from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import pytest

from conjectures_contribution.model import Contribution, Digest, SchemaError, TargetSlug
from conjectures_contribution.payout import (
    EVENT_VERSION,
    Destination,
    FormalSolve,
    PayoutEvent,
    SolveMode,
    allocate,
    build_payout,
    validate_payout,
)
from conjectures_contribution.recognition import (
    CONTRACT_VERSION,
    Decision,
    GateResult,
    Gates,
    ReviewId,
    ReviewPayload,
    ReviewRecord,
    Score,
    sign_review,
)
from conjectures_contribution.signing import SigningKey

from .conftest import Repo

GATES = Gates(
    direct_relevance=GateResult.PASS,
    verified_value=GateResult.PASS,
    material_progress=GateResult.PASS,
    novelty=GateResult.PASS,
    reusable_handoff=GateResult.PASS,
    provenance=GateResult.PASS,
)


def _review(repo: Repo, directory: Path, weight: int) -> tuple[Contribution, ReviewRecord]:
    contribution = repo.read(directory)
    reviewer = SigningKey.generate()
    score = Score(weight, 0, 0, 0)
    payload = ReviewPayload(
        contract_version=CONTRACT_VERSION,
        contribution_id=str(contribution.contribution_id),
        target=contribution.payload.target,
        decision=Decision.RECOGNIZED,
        gates=GATES,
        score=score,
        weight=weight,
        reviewers=(reviewer.public_key,),
        reason="This checked delta is reusable by the next solver.",
        reviewed_at="2026-08-31T16:00:00Z",
    )
    return contribution, sign_review(payload, (reviewer,))


def _event(
    operator: SigningKey,
    review_ids: tuple[ReviewId, ...],
    budget: int = 10,
) -> PayoutEvent:
    return PayoutEvent(
        event_version=EVENT_VERSION,
        contract_version=CONTRACT_VERSION,
        name="launch-2026-08-31",
        asset="TAO",
        unit="rao",
        network="finney",
        budget=budget,
        destination=Destination.COLDKEY,
        period_start="2026-08-31T00:00:00Z",
        period_end="2026-08-31T23:59:59Z",
        targets=(TargetSlug("demo-1"),),
        formal_solves=(
            FormalSolve(
                target=TargetSlug("demo-1"),
                mode=SolveMode.FORMALIZED,
                result_id="11111111-1111-1111-1111-111111111111",
                proof_sha256=Digest("a" * 64),
                accepted_at="2026-08-31T23:59:59Z",
            ),
        ),
        review_ids=tuple(sorted(review_ids)),
        created_at="2026-09-01T00:00:00Z",
        payment_due_at="2026-09-02T00:00:00Z",
        operator=operator.public_key,
    )


def test_largest_remainder_allocation_is_exact_and_deterministic() -> None:
    assert allocate(10, (("b", 2), ("a", 1))) == {"a": 3, "b": 7}
    assert allocate(1, (("b", 1), ("a", 1))) == {"a": 1, "b": 0}


def test_payout_events_accept_only_coldkey_destinations() -> None:
    operator = SigningKey.generate()
    event = _event(operator, (ReviewId("0" * 64),))
    raw = event.to_json() | {"destination": "hotkey"}

    with pytest.raises(SchemaError, match="expected coldkey"):
        PayoutEvent.parse(raw)


def test_payout_event_requires_one_prior_formal_solve_per_target() -> None:
    operator = SigningKey.generate()
    event = _event(operator, (ReviewId("0" * 64),))

    with pytest.raises(SchemaError, match="exactly one accepted formal solve"):
        PayoutEvent.parse(event.to_json() | {"formal_solves": []})

    later = replace(event.formal_solves[0], accepted_at="2026-09-01T00:00:01Z")
    with pytest.raises(SchemaError, match="accepted_at must not be after created_at"):
        replace(event, formal_solves=(later,))


def test_a_payout_event_binds_reviews_destinations_and_integer_amounts(repo: Repo) -> None:
    first_dir = repo.promote(repo.draft(title="First recognized delta"))
    second_dir = repo.promote(
        repo.draft(
            title="Second recognized delta",
            files={
                "sources.md": "# Sources\n\n- Original second delta.\n",
                "script.lean": "theorem second_delta : True := trivial\n",
            },
        )
    )
    first, first_review = _review(repo, first_dir, 1)
    second, second_review = _review(repo, second_dir, 2)
    operator = SigningKey.generate()
    event = _event(operator, (first_review.review_id, second_review.review_id))

    record = build_payout(
        event,
        (first_review, second_review),
        {str(first.contribution_id): first, str(second.contribution_id): second},
        operator,
    )

    assert {allocation.weight: allocation.amount for allocation in record.allocations} == {
        1: 3,
        2: 7,
    }
    assert {str(allocation.destination) for allocation in record.allocations} == {
        str(repo.reward.reward.coldkey)
    }
    validate_payout(record)


def test_payout_refuses_an_unsigned_reward_destination(repo: Repo) -> None:
    directory = repo.promote(reward=False)
    contribution, review = _review(repo, directory, 1)
    operator = SigningKey.generate()

    with pytest.raises(SchemaError, match="no reward destination"):
        build_payout(
            _event(operator, (review.review_id,)),
            (review,),
            {str(contribution.contribution_id): contribution},
            operator,
        )


def test_payout_signature_detects_changed_amounts(repo: Repo) -> None:
    contribution, review = _review(repo, repo.promote(), 1)
    operator = SigningKey.generate()
    record = build_payout(
        _event(operator, (review.review_id,)),
        (review,),
        {str(contribution.contribution_id): contribution},
        operator,
    )
    allocation = replace(record.allocations[0], amount=record.allocations[0].amount - 1)

    with pytest.raises(SchemaError, match="sum"):
        validate_payout(replace(record, allocations=(allocation,)))
