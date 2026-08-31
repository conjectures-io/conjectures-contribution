from __future__ import annotations

from dataclasses import replace
from typing import Any

import pytest

from conjectures_contribution.model import SchemaError
from conjectures_contribution.recognition import (
    CONTRACT_VERSION,
    Decision,
    GateResult,
    Gates,
    ReviewPayload,
    Score,
    active_reviews,
    sign_review,
    validate_for_contribution,
    validate_record,
)
from conjectures_contribution.signing import SigningKey

from .conftest import Repo

PASSING_GATES = Gates(
    direct_relevance=GateResult.PASS,
    verified_value=GateResult.PASS,
    material_progress=GateResult.PASS,
    novelty=GateResult.PASS,
    reusable_handoff=GateResult.PASS,
    provenance=GateResult.PASS,
)


def _payload(repo: Repo, reviewers: tuple[SigningKey, ...], **changes: Any) -> ReviewPayload:
    contribution = repo.read(repo.promote())
    base = ReviewPayload(
        contract_version=CONTRACT_VERSION,
        contribution_id=str(contribution.contribution_id),
        target=contribution.payload.target,
        decision=Decision.RECOGNIZED,
        gates=PASSING_GATES,
        score=Score(1, 0, 0, 0),
        weight=1,
        reviewers=tuple(sorted(key.public_key for key in reviewers)),
        reason="The named declaration removes the target's first checked obligation.",
        reviewed_at="2026-08-31T16:00:00Z",
    )
    return replace(base, **changes)


def test_an_independent_signed_review_validates_against_the_contribution(repo: Repo) -> None:
    reviewer = SigningKey.generate()
    payload = _payload(repo, (reviewer,))
    contribution = repo.read(repo.contributions / str(payload.target) / payload.contribution_id)

    record = sign_review(payload, (reviewer,))

    validate_for_contribution(record, contribution)


def test_a_contribution_author_cannot_review_their_own_work(repo: Repo) -> None:
    payload = _payload(repo, (repo.key,))
    contribution = repo.read(repo.contributions / str(payload.target) / payload.contribution_id)
    record = sign_review(payload, (repo.key,))

    with pytest.raises(SchemaError, match="cannot review"):
        validate_for_contribution(record, contribution)


def test_high_weight_requires_two_independent_signatures(repo: Repo) -> None:
    reviewer = SigningKey.generate()
    low = _payload(repo, (reviewer,))
    score = Score(4, 2, 1, 1)

    with pytest.raises(SchemaError, match="requires two reviewers"):
        replace(low, score=score, weight=score.total)

    second = SigningKey.generate()
    payload = replace(
        low,
        score=score,
        weight=score.total,
        reviewers=tuple(sorted((reviewer.public_key, second.public_key))),
    )
    assert len(sign_review(payload, (reviewer, second)).signatures) == 2


def test_non_recognition_has_zero_weight_and_names_a_failed_gate(repo: Repo) -> None:
    reviewer = SigningKey.generate()
    gates = replace(PASSING_GATES, novelty=GateResult.FAIL)
    payload = _payload(
        repo,
        (reviewer,),
        decision=Decision.ADMISSIBLE_ONLY,
        gates=gates,
        score=Score(0, 0, 0, 0),
        weight=0,
    )
    assert sign_review(payload, (reviewer,)).payload.weight == 0


def test_supersession_leaves_exactly_one_active_review(repo: Repo) -> None:
    first_reviewer = SigningKey.generate()
    second_reviewer = SigningKey.generate()
    first = sign_review(_payload(repo, (first_reviewer,)), (first_reviewer,))
    second_payload = replace(
        first.payload,
        reviewed_at="2026-08-31T17:00:00Z",
        reason="New evidence confirms a broader reusable use site.",
        reviewers=(second_reviewer.public_key,),
        supersedes=first.review_id,
    )
    second = sign_review(second_payload, (second_reviewer,))

    assert active_reviews((first, second)) == (second,)


def test_a_reviewer_cannot_decide_their_own_appeal(repo: Repo) -> None:
    reviewer = SigningKey.generate()
    first = sign_review(_payload(repo, (reviewer,)), (reviewer,))
    second = sign_review(
        replace(
            first.payload,
            reviewed_at="2026-08-31T17:00:00Z",
            reason="The same reviewer attempts to revise the prior decision.",
            supersedes=first.review_id,
        ),
        (reviewer,),
    )

    with pytest.raises(SchemaError, match="different reviewer"):
        active_reviews((first, second))


def test_a_review_signature_cannot_be_reused_after_payload_changes(repo: Repo) -> None:
    reviewer = SigningKey.generate()
    record = sign_review(_payload(repo, (reviewer,)), (reviewer,))
    tampered = replace(record, payload=replace(record.payload, reason="A different rationale."))

    with pytest.raises(SchemaError, match="review_id"):
        validate_record(tampered)
