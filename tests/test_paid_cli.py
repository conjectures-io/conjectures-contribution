from __future__ import annotations

from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.canonical import canonical_bytes
from conjectures_contribution.cli.admin import app
from conjectures_contribution.payout import EVENT_VERSION, Destination, PayoutEvent
from conjectures_contribution.recognition import CONTRACT_VERSION, iter_reviews
from conjectures_contribution.signing import SigningKey

from .conftest import Repo

runner = CliRunner()


def _save_key(path: Path) -> SigningKey:
    key = SigningKey.generate()
    key.save(path)
    return key


def test_review_payout_and_audit_commands_form_one_deterministic_pipeline(
    repo: Repo, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(repo.root)
    contribution = repo.promote()
    reviewer_path = tmp_path / "reviewer.key"
    _save_key(reviewer_path)
    review = runner.invoke(
        app,
        [
            "review",
            str(contribution),
            "--decision",
            "recognized",
            "--direct-relevance",
            "pass",
            "--verified-value",
            "pass",
            "--material-progress",
            "pass",
            "--novelty",
            "pass",
            "--reusable-handoff",
            "pass",
            "--provenance",
            "pass",
            "--target-impact",
            "1",
            "--reason",
            "The checked declaration removes one concrete target obligation.",
            "--reviewed-at",
            "2026-08-31T16:00:00Z",
            "--reviewer-key",
            str(reviewer_path),
        ],
    )
    assert review.exit_code == 0, review.output
    records = iter_reviews(repo.root)

    operator_path = tmp_path / "operator.key"
    operator = _save_key(operator_path)
    event = PayoutEvent(
        event_version=EVENT_VERSION,
        contract_version=CONTRACT_VERSION,
        name="launch-canary",
        asset="TAO",
        unit="rao",
        network="finney",
        budget=10,
        destination=Destination.HOTKEY,
        period_start="2026-08-31T00:00:00Z",
        period_end="2026-08-31T23:59:59Z",
        targets=(repo.read(contribution).payload.target,),
        review_ids=(records[0].review_id,),
        created_at="2026-09-01T00:00:00Z",
        payment_due_at="2026-09-02T00:00:00Z",
        operator=operator.public_key,
    )
    event_path = tmp_path / "event.json"
    event_path.write_bytes(canonical_bytes(event.to_json()))

    payout = runner.invoke(app, ["payout", str(event_path), "--operator-key", str(operator_path)])
    assert payout.exit_code == 0, payout.output

    audit = runner.invoke(app, ["audit-rewards"])
    assert audit.exit_code == 0, audit.output
    assert "1 review record(s), 1 active, 1 payout event(s): valid" in audit.output
