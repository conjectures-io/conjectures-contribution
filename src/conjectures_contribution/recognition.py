from __future__ import annotations

import hashlib
import json
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
from enum import StrEnum
from pathlib import Path
from typing import Any, Self, cast

from .canonical import canonical_bytes
from .model import Contribution, Digest, PublicKey, SchemaError, Signature, TargetSlug
from .signing import SigningKey, verify

CONTRACT_VERSION = "1.0"
REVIEW_DOMAIN = b"conjectures-recognition-v1\0"
REVIEW_ROOT = "reviews"
MAX_REASON_CHARS = 4000
MAX_WEIGHT = 10
HIGH_WEIGHT_MIN = 8
SECOND_REVIEWER_COUNT = 2


class ReviewId(Digest):
    __slots__ = ()


class Decision(StrEnum):
    RECOGNIZED = "recognized"
    ADMISSIBLE_ONLY = "admissible-only"
    DEFERRED = "deferred"
    REJECTED = "rejected"
    WITHDRAWN = "withdrawn"


class GateResult(StrEnum):
    PASS = "pass"  # noqa: S105 - review outcome, not a password
    FAIL = "fail"
    UNCERTAIN = "uncertain"


def _object(value: Any, where: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise SchemaError(f"{where}: expected an object")
    return cast("Mapping[str, Any]", value)


def _array(value: Any, where: str) -> Sequence[Any]:
    if not isinstance(value, list):
        raise SchemaError(f"{where}: expected an array")
    return cast("Sequence[Any]", value)


def _text(value: Any, where: str) -> str:
    if not isinstance(value, str):
        raise SchemaError(f"{where}: expected a string")
    return value


def _integer(value: Any, where: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise SchemaError(f"{where}: expected an integer")
    return value


def _keys(value: Mapping[str, Any], expected: frozenset[str], where: str) -> None:
    found = frozenset(value)
    if found != expected:
        missing = sorted(expected - found)
        extra = sorted(found - expected)
        details = [
            *(f"missing {name}" for name in missing),
            *(f"unexpected {name}" for name in extra),
        ]
        raise SchemaError(f"{where}: {', '.join(details)}")


def _enum(enum: type[StrEnum], value: Any, where: str) -> Any:
    text = _text(value, where)
    try:
        return enum(text)
    except ValueError:
        allowed = ", ".join(item.value for item in enum)
        raise SchemaError(f"{where}: expected one of {allowed}, got {text!r}") from None


def _utc_timestamp(value: Any, where: str) -> str:
    text = _text(value, where)
    try:
        parsed = datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=UTC)
    except ValueError:
        raise SchemaError(f"{where}: expected a UTC timestamp like 2026-08-31T16:00:00Z") from None
    if parsed.strftime("%Y-%m-%dT%H:%M:%SZ") != text:
        raise SchemaError(f"{where}: timestamp is not canonical")
    return text


@dataclass(frozen=True, slots=True)
class Gates:
    direct_relevance: GateResult
    verified_value: GateResult
    material_progress: GateResult
    novelty: GateResult
    reusable_handoff: GateResult
    provenance: GateResult

    @classmethod
    def parse(cls, raw: Any, where: str = "gates") -> Self:
        value = _object(raw, where)
        expected = frozenset(
            {
                "direct_relevance",
                "verified_value",
                "material_progress",
                "novelty",
                "reusable_handoff",
                "provenance",
            }
        )
        _keys(value, expected, where)
        return cls(
            **{name: _enum(GateResult, value[name], f"{where}.{name}") for name in sorted(expected)}
        )

    def values(self) -> tuple[GateResult, ...]:
        return (
            self.direct_relevance,
            self.verified_value,
            self.material_progress,
            self.novelty,
            self.reusable_handoff,
            self.provenance,
        )

    def to_json(self) -> dict[str, str]:
        return {
            "direct_relevance": self.direct_relevance.value,
            "material_progress": self.material_progress.value,
            "novelty": self.novelty.value,
            "provenance": self.provenance.value,
            "reusable_handoff": self.reusable_handoff.value,
            "verified_value": self.verified_value.value,
        }


@dataclass(frozen=True, slots=True)
class Score:
    target_impact: int
    generality_reuse: int
    originality_delta: int
    verification_handoff: int

    def __post_init__(self) -> None:
        ranges = {
            "target_impact": (0, 4),
            "generality_reuse": (0, 2),
            "originality_delta": (0, 2),
            "verification_handoff": (0, 2),
        }
        for name, (low, high) in ranges.items():
            value = getattr(self, name)
            if not low <= value <= high:
                raise SchemaError(f"score.{name}: expected {low}..{high}, got {value}")

    @classmethod
    def parse(cls, raw: Any, where: str = "score") -> Self:
        value = _object(raw, where)
        expected = frozenset(
            {"target_impact", "generality_reuse", "originality_delta", "verification_handoff"}
        )
        _keys(value, expected, where)
        return cls(**{name: _integer(value[name], f"{where}.{name}") for name in expected})

    @property
    def total(self) -> int:
        return (
            self.target_impact
            + self.generality_reuse
            + self.originality_delta
            + self.verification_handoff
        )

    def to_json(self) -> dict[str, int]:
        return {
            "generality_reuse": self.generality_reuse,
            "originality_delta": self.originality_delta,
            "target_impact": self.target_impact,
            "verification_handoff": self.verification_handoff,
        }


@dataclass(frozen=True, slots=True)
class ReviewPayload:
    contract_version: str
    contribution_id: str
    target: TargetSlug
    decision: Decision
    gates: Gates
    score: Score
    weight: int
    reviewers: tuple[PublicKey, ...]
    reason: str
    reviewed_at: str
    conflicts: tuple[str, ...] = ()
    supersedes: ReviewId | None = None

    def __post_init__(self) -> None:
        _validate_review_common(self)
        _validate_review_decision(self)
        _validate_review_independence(self)

    @classmethod
    def parse(cls, raw: Any, where: str = "payload") -> Self:
        value = _object(raw, where)
        expected = frozenset(
            {
                "contract_version",
                "contribution_id",
                "target",
                "decision",
                "gates",
                "score",
                "weight",
                "reviewers",
                "reason",
                "reviewed_at",
                "conflicts",
                "supersedes",
            }
        )
        _keys(value, expected, where)
        reviewers = _array(value["reviewers"], f"{where}.reviewers")
        conflicts = _array(value["conflicts"], f"{where}.conflicts")
        supersedes = value["supersedes"]
        return cls(
            contract_version=_text(value["contract_version"], f"{where}.contract_version"),
            contribution_id=_text(value["contribution_id"], f"{where}.contribution_id"),
            target=TargetSlug.parse(value["target"], f"{where}.target"),
            decision=_enum(Decision, value["decision"], f"{where}.decision"),
            gates=Gates.parse(value["gates"], f"{where}.gates"),
            score=Score.parse(value["score"], f"{where}.score"),
            weight=_integer(value["weight"], f"{where}.weight"),
            reviewers=tuple(
                PublicKey.parse(item, f"{where}.reviewers[{index}]")
                for index, item in enumerate(reviewers)
            ),
            reason=_text(value["reason"], f"{where}.reason"),
            reviewed_at=_utc_timestamp(value["reviewed_at"], f"{where}.reviewed_at"),
            conflicts=tuple(
                _text(item, f"{where}.conflicts[{index}]") for index, item in enumerate(conflicts)
            ),
            supersedes=(
                None if supersedes is None else ReviewId.parse(supersedes, f"{where}.supersedes")
            ),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "conflicts": list(self.conflicts),
            "contract_version": self.contract_version,
            "contribution_id": self.contribution_id,
            "decision": self.decision.value,
            "gates": self.gates.to_json(),
            "reason": self.reason,
            "reviewed_at": self.reviewed_at,
            "reviewers": [str(reviewer) for reviewer in self.reviewers],
            "score": self.score.to_json(),
            "supersedes": None if self.supersedes is None else str(self.supersedes),
            "target": str(self.target),
            "weight": self.weight,
        }


def _validate_review_common(payload: ReviewPayload) -> None:
    if payload.contract_version != CONTRACT_VERSION:
        raise SchemaError(
            f"contract_version: expected {CONTRACT_VERSION}, got {payload.contract_version!r}"
        )
    ReviewId(payload.contribution_id)
    _utc_timestamp(payload.reviewed_at, "reviewed_at")
    if not payload.reason.strip() or payload.reason != payload.reason.strip():
        raise SchemaError("reason: must be substantive and not padded with whitespace")
    if len(payload.reason) > MAX_REASON_CHARS:
        raise SchemaError(f"reason: longer than {MAX_REASON_CHARS} characters")
    if not payload.reviewers or tuple(sorted(set(payload.reviewers))) != payload.reviewers:
        raise SchemaError("reviewers: must be sorted, unique, and non-empty")
    if tuple(sorted(set(payload.conflicts))) != payload.conflicts:
        raise SchemaError("conflicts: must be sorted and free of duplicates")
    if any(not item.strip() or item != item.strip() for item in payload.conflicts):
        raise SchemaError("conflicts: entries must be non-empty and not padded")


def _validate_review_decision(payload: ReviewPayload) -> None:
    if payload.decision is Decision.RECOGNIZED:
        if any(value is not GateResult.PASS for value in payload.gates.values()):
            raise SchemaError("recognized: every gate must pass")
        if payload.score.target_impact < 1:
            raise SchemaError("recognized: target_impact must be at least 1")
        if payload.weight != payload.score.total or not 1 <= payload.weight <= MAX_WEIGHT:
            raise SchemaError("recognized: weight must be the 1..10 score component sum")
        return
    if payload.weight != 0 or payload.score.total != 0:
        raise SchemaError("non-recognized decisions must have zero score and weight")
    if payload.decision in {Decision.ADMISSIBLE_ONLY, Decision.REJECTED} and all(
        value is not GateResult.FAIL for value in payload.gates.values()
    ):
        raise SchemaError(f"{payload.decision.value}: at least one gate must fail")
    if payload.decision is Decision.DEFERRED and all(
        value is not GateResult.UNCERTAIN for value in payload.gates.values()
    ):
        raise SchemaError("deferred: at least one gate must be uncertain")


def _validate_review_independence(payload: ReviewPayload) -> None:
    requires_second = payload.weight >= HIGH_WEIGHT_MIN or bool(payload.conflicts)
    if requires_second and len(payload.reviewers) < SECOND_REVIEWER_COUNT:
        raise SchemaError("a high-weight or conflicted review requires two reviewers")


@dataclass(frozen=True, slots=True, order=True)
class ReviewSignature:
    reviewer: PublicKey
    signature: Signature

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        value = _object(raw, where)
        _keys(value, frozenset({"reviewer", "signature"}), where)
        return cls(
            reviewer=PublicKey.parse(value["reviewer"], f"{where}.reviewer"),
            signature=Signature.parse(value["signature"], f"{where}.signature"),
        )

    def to_json(self) -> dict[str, str]:
        return {"reviewer": str(self.reviewer), "signature": str(self.signature)}


@dataclass(frozen=True, slots=True)
class ReviewRecord:
    payload: ReviewPayload
    review_id: ReviewId
    signatures: tuple[ReviewSignature, ...]

    @classmethod
    def parse(cls, raw: Any, where: str = "review") -> Self:
        value = _object(raw, where)
        _keys(value, frozenset({"payload", "review_id", "signatures"}), where)
        signatures = _array(value["signatures"], f"{where}.signatures")
        record = cls(
            payload=ReviewPayload.parse(value["payload"], f"{where}.payload"),
            review_id=ReviewId.parse(value["review_id"], f"{where}.review_id"),
            signatures=tuple(
                ReviewSignature.parse(item, f"{where}.signatures[{index}]")
                for index, item in enumerate(signatures)
            ),
        )
        validate_record(record)
        return record

    def to_json(self) -> dict[str, Any]:
        return {
            "payload": self.payload.to_json(),
            "review_id": str(self.review_id),
            "signatures": [signature.to_json() for signature in self.signatures],
        }


def payload_bytes(payload: ReviewPayload) -> bytes:
    return canonical_bytes(payload.to_json())


def derive_review_id(payload: ReviewPayload) -> ReviewId:
    return ReviewId.of(payload_bytes(payload))


def review_message(payload: ReviewPayload) -> bytes:
    return hashlib.sha256(REVIEW_DOMAIN + payload_bytes(payload)).digest()


def sign_review(payload: ReviewPayload, keys: Iterable[SigningKey]) -> ReviewRecord:
    ordered = tuple(sorted(keys, key=lambda key: key.public_key))
    public_keys = tuple(key.public_key for key in ordered)
    if public_keys != payload.reviewers:
        raise SchemaError("the supplied signing keys must exactly match payload.reviewers")
    message = review_message(payload)
    record = ReviewRecord(
        payload=payload,
        review_id=derive_review_id(payload),
        signatures=tuple(
            ReviewSignature(reviewer=key.public_key, signature=key.sign(message)) for key in ordered
        ),
    )
    validate_record(record)
    return record


def validate_record(record: ReviewRecord) -> None:
    if record.review_id != derive_review_id(record.payload):
        raise SchemaError("review_id does not match the canonical payload")
    if tuple(sorted(record.signatures)) != record.signatures:
        raise SchemaError("signatures must be sorted by reviewer")
    signers = tuple(signature.reviewer for signature in record.signatures)
    if signers != record.payload.reviewers:
        raise SchemaError("signatures must exactly match payload.reviewers")
    message = review_message(record.payload)
    if any(not verify(message, item.reviewer, item.signature) for item in record.signatures):
        raise SchemaError("review signature verification failed")


def validate_for_contribution(record: ReviewRecord, contribution: Contribution) -> None:
    validate_record(record)
    if record.payload.contribution_id != str(contribution.contribution_id):
        raise SchemaError("review contribution_id does not match metadata.json")
    if record.payload.target != contribution.payload.target:
        raise SchemaError("review target does not match metadata.json")
    if contribution.payload.author in record.payload.reviewers:
        raise SchemaError("a contribution author cannot review their own contribution")


def load_review(path: Path) -> ReviewRecord:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SchemaError(f"{path}: invalid review JSON: {exc}") from None
    return ReviewRecord.parse(raw, str(path))


def write_review(root: Path, record: ReviewRecord) -> Path:
    validate_record(record)
    directory = root / REVIEW_ROOT / str(record.payload.target) / record.payload.contribution_id
    destination = directory / f"{record.review_id}.json"
    if destination.exists():
        existing = load_review(destination)
        if existing == record:
            return destination
        raise SchemaError(f"{destination}: refusing to overwrite a different review")
    directory.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(canonical_bytes(record.to_json()))
    return destination


def iter_reviews(root: Path) -> tuple[ReviewRecord, ...]:
    review_root = root / REVIEW_ROOT
    if not review_root.is_dir():
        return ()
    return tuple(load_review(path) for path in sorted(review_root.glob("*/*/*.json")))


def active_reviews(records: Iterable[ReviewRecord]) -> tuple[ReviewRecord, ...]:
    ordered = tuple(records)
    by_id = {record.review_id: record for record in ordered}
    if len(by_id) != len(ordered):
        raise SchemaError("duplicate review_id")
    superseded: set[ReviewId] = set()
    for record in ordered:
        previous_id = record.payload.supersedes
        if previous_id is None:
            continue
        previous = by_id.get(previous_id)
        if previous is None:
            raise SchemaError(f"review {record.review_id} supersedes an unknown review")
        if previous.payload.contribution_id != record.payload.contribution_id:
            raise SchemaError("a review can supersede only the same contribution")
        if previous_id in superseded:
            raise SchemaError(f"review {previous_id} is superseded more than once")
        if _utc_datetime(record.payload.reviewed_at) <= _utc_datetime(previous.payload.reviewed_at):
            raise SchemaError("a superseding review must have a later reviewed_at timestamp")
        if set(record.payload.reviewers) & set(previous.payload.reviewers):
            raise SchemaError("a superseding review requires different reviewer keys")
        superseded.add(previous_id)
    active = tuple(record for record in ordered if record.review_id not in superseded)
    contribution_ids = [record.payload.contribution_id for record in active]
    if len(set(contribution_ids)) != len(contribution_ids):
        raise SchemaError("each contribution must have exactly one active review")
    return tuple(sorted(active, key=lambda record: record.payload.contribution_id))


def _utc_datetime(value: str) -> datetime:
    return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=UTC)
