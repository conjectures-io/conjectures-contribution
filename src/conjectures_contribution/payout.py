from __future__ import annotations

import hashlib
import json
import re
import uuid
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
from enum import StrEnum
from pathlib import Path
from typing import Any, Self, cast

from . import reward as reward_module
from .canonical import canonical_bytes
from .model import Contribution, Digest, PublicKey, SchemaError, Signature, Ss58Address, TargetSlug
from .recognition import (
    CONTRACT_VERSION,
    Decision,
    ReviewId,
    ReviewRecord,
    active_reviews,
    validate_for_contribution,
)
from .signing import SigningKey, verify

EVENT_VERSION = 1
PAYOUT_DOMAIN = b"conjectures-payout-v1\0"
PAYOUT_ROOT = "payouts"
_NAME = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
_ASSET = re.compile(r"[A-Z0-9][A-Z0-9-]{0,31}")
_UNIT = re.compile(r"[a-z0-9][a-z0-9-]{0,31}")


class EventId(Digest):
    __slots__ = ()


class Destination(StrEnum):
    COLDKEY = "coldkey"


class SolveMode(StrEnum):
    FORMALIZED = "formalized"
    COUNTEREXAMPLE = "counterexample"


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
    if frozenset(value) != expected:
        raise SchemaError(f"{where}: fields must be exactly {', '.join(sorted(expected))}")


def _timestamp(value: Any, where: str) -> str:
    text = _text(value, where)
    try:
        parsed = datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=UTC)
    except ValueError:
        raise SchemaError(f"{where}: expected a canonical UTC timestamp") from None
    if parsed.strftime("%Y-%m-%dT%H:%M:%SZ") != text:
        raise SchemaError(f"{where}: timestamp is not canonical")
    return text


def _uuid(value: Any, where: str) -> str:
    text = _text(value, where)
    try:
        parsed = uuid.UUID(text)
    except ValueError:
        raise SchemaError(f"{where}: expected a canonical UUID") from None
    if str(parsed) != text:
        raise SchemaError(f"{where}: UUID is not canonical")
    return text


def _datetime(value: str) -> datetime:
    return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=UTC)


def _validate_terms(  # noqa: PLR0913 - each signed financial term is an explicit input
    *,
    contract_version: str,
    name: str,
    asset: str,
    unit: str,
    network: str,
    budget: int,
    period_start: str,
    period_end: str,
    targets: tuple[TargetSlug, ...],
    payment_due_at: str,
) -> None:
    if contract_version != CONTRACT_VERSION:
        raise SchemaError(f"contract_version: expected {CONTRACT_VERSION}")
    if _NAME.fullmatch(name) is None:
        raise SchemaError("name: expected a lowercase slug")
    if _ASSET.fullmatch(asset) is None:
        raise SchemaError("asset: expected an uppercase asset symbol")
    if _UNIT.fullmatch(unit) is None:
        raise SchemaError("unit: expected a lowercase integer-unit name")
    if _NAME.fullmatch(network) is None:
        raise SchemaError("network: expected a lowercase network slug")
    if budget <= 0:
        raise SchemaError("budget: expected a positive integer in the declared unit")
    _timestamp(period_start, "period_start")
    _timestamp(period_end, "period_end")
    _timestamp(payment_due_at, "payment_due_at")
    if _datetime(period_start) > _datetime(period_end):
        raise SchemaError("period_start must not be after period_end")
    if _datetime(payment_due_at) < _datetime(period_end):
        raise SchemaError("payment_due_at must not be before period_end")
    if not targets or tuple(sorted(set(targets))) != targets:
        raise SchemaError("targets: must be sorted, unique, and non-empty")


@dataclass(frozen=True, slots=True)
class FormalSolve:
    target: TargetSlug
    mode: SolveMode
    result_id: str
    proof_sha256: Digest
    accepted_at: str

    def __post_init__(self) -> None:
        _uuid(self.result_id, "formal_solve.result_id")
        _timestamp(self.accepted_at, "formal_solve.accepted_at")

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        value = _object(raw, where)
        _keys(
            value,
            frozenset({"target", "mode", "result_id", "proof_sha256", "accepted_at"}),
            where,
        )
        try:
            mode = SolveMode(_text(value["mode"], f"{where}.mode"))
        except ValueError:
            raise SchemaError(f"{where}.mode: expected formalized or counterexample") from None
        return cls(
            target=TargetSlug.parse(value["target"], f"{where}.target"),
            mode=mode,
            result_id=_uuid(value["result_id"], f"{where}.result_id"),
            proof_sha256=Digest.parse(value["proof_sha256"], f"{where}.proof_sha256"),
            accepted_at=_timestamp(value["accepted_at"], f"{where}.accepted_at"),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "accepted_at": self.accepted_at,
            "mode": self.mode.value,
            "proof_sha256": str(self.proof_sha256),
            "result_id": self.result_id,
            "target": str(self.target),
        }


@dataclass(frozen=True, slots=True)
class PayoutEvent:
    event_version: int
    contract_version: str
    name: str
    asset: str
    unit: str
    network: str
    budget: int
    destination: Destination
    period_start: str
    period_end: str
    targets: tuple[TargetSlug, ...]
    formal_solves: tuple[FormalSolve, ...]
    review_ids: tuple[ReviewId, ...]
    created_at: str
    payment_due_at: str
    operator: PublicKey

    def __post_init__(self) -> None:
        if self.event_version != EVENT_VERSION:
            raise SchemaError(f"event_version: expected {EVENT_VERSION}")
        if self.destination is not Destination.COLDKEY:
            raise SchemaError("destination: payouts must use the submitted coldkey")
        _validate_terms(
            contract_version=self.contract_version,
            name=self.name,
            asset=self.asset,
            unit=self.unit,
            network=self.network,
            budget=self.budget,
            period_start=self.period_start,
            period_end=self.period_end,
            targets=self.targets,
            payment_due_at=self.payment_due_at,
        )
        _timestamp(self.created_at, "created_at")
        if _datetime(self.created_at) < _datetime(self.period_end):
            raise SchemaError("created_at must not be before period_end")
        if _datetime(self.payment_due_at) < _datetime(self.created_at):
            raise SchemaError("payment_due_at must not be before created_at")
        solve_targets = tuple(solve.target for solve in self.formal_solves)
        if solve_targets != self.targets:
            raise SchemaError(
                "formal_solves: must contain exactly one accepted formal solve for every target"
            )
        if any(
            _datetime(solve.accepted_at) > _datetime(self.created_at)
            for solve in self.formal_solves
        ):
            raise SchemaError("formal_solves: accepted_at must not be after created_at")
        if not self.review_ids or tuple(sorted(set(self.review_ids))) != self.review_ids:
            raise SchemaError("review_ids: must be sorted, unique, and non-empty")

    @classmethod
    def parse(cls, raw: Any, where: str = "event") -> Self:
        value = _object(raw, where)
        expected = frozenset(
            {
                "event_version",
                "contract_version",
                "name",
                "asset",
                "unit",
                "network",
                "budget",
                "destination",
                "period_start",
                "period_end",
                "targets",
                "formal_solves",
                "review_ids",
                "created_at",
                "payment_due_at",
                "operator",
            }
        )
        _keys(value, expected, where)
        targets = _array(value["targets"], f"{where}.targets")
        formal_solves = _array(value["formal_solves"], f"{where}.formal_solves")
        review_ids = _array(value["review_ids"], f"{where}.review_ids")
        try:
            destination = Destination(_text(value["destination"], f"{where}.destination"))
        except ValueError:
            raise SchemaError(f"{where}.destination: expected coldkey") from None
        return cls(
            event_version=_integer(value["event_version"], f"{where}.event_version"),
            contract_version=_text(value["contract_version"], f"{where}.contract_version"),
            name=_text(value["name"], f"{where}.name"),
            asset=_text(value["asset"], f"{where}.asset"),
            unit=_text(value["unit"], f"{where}.unit"),
            network=_text(value["network"], f"{where}.network"),
            budget=_integer(value["budget"], f"{where}.budget"),
            destination=destination,
            period_start=_timestamp(value["period_start"], f"{where}.period_start"),
            period_end=_timestamp(value["period_end"], f"{where}.period_end"),
            targets=tuple(
                TargetSlug.parse(item, f"{where}.targets[{index}]")
                for index, item in enumerate(targets)
            ),
            formal_solves=tuple(
                FormalSolve.parse(item, f"{where}.formal_solves[{index}]")
                for index, item in enumerate(formal_solves)
            ),
            review_ids=tuple(
                ReviewId.parse(item, f"{where}.review_ids[{index}]")
                for index, item in enumerate(review_ids)
            ),
            created_at=_timestamp(value["created_at"], f"{where}.created_at"),
            payment_due_at=_timestamp(value["payment_due_at"], f"{where}.payment_due_at"),
            operator=PublicKey.parse(value["operator"], f"{where}.operator"),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "asset": self.asset,
            "budget": self.budget,
            "contract_version": self.contract_version,
            "created_at": self.created_at,
            "destination": self.destination.value,
            "event_version": self.event_version,
            "formal_solves": [solve.to_json() for solve in self.formal_solves],
            "name": self.name,
            "network": self.network,
            "operator": str(self.operator),
            "payment_due_at": self.payment_due_at,
            "period_end": self.period_end,
            "period_start": self.period_start,
            "review_ids": [str(review_id) for review_id in self.review_ids],
            "targets": [str(target) for target in self.targets],
            "unit": self.unit,
        }


@dataclass(frozen=True, slots=True, order=True)
class Allocation:
    contribution_id: str
    review_id: ReviewId
    target: TargetSlug
    weight: int
    destination: Ss58Address
    amount: int

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        value = _object(raw, where)
        expected = frozenset(
            {"contribution_id", "review_id", "target", "weight", "destination", "amount"}
        )
        _keys(value, expected, where)
        return cls(
            contribution_id=str(ReviewId(_text(value["contribution_id"], where))),
            review_id=ReviewId.parse(value["review_id"], f"{where}.review_id"),
            target=TargetSlug.parse(value["target"], f"{where}.target"),
            weight=_integer(value["weight"], f"{where}.weight"),
            destination=Ss58Address.parse(value["destination"], f"{where}.destination"),
            amount=_integer(value["amount"], f"{where}.amount"),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "amount": self.amount,
            "contribution_id": self.contribution_id,
            "destination": str(self.destination),
            "review_id": str(self.review_id),
            "target": str(self.target),
            "weight": self.weight,
        }


@dataclass(frozen=True, slots=True)
class PayoutRecord:
    event: PayoutEvent
    allocations: tuple[Allocation, ...]
    event_id: EventId
    signature: Signature

    @classmethod
    def parse(cls, raw: Any, where: str = "payout") -> Self:
        value = _object(raw, where)
        _keys(value, frozenset({"event", "allocations", "event_id", "signature"}), where)
        allocations = _array(value["allocations"], f"{where}.allocations")
        return cls(
            event=PayoutEvent.parse(value["event"], f"{where}.event"),
            allocations=tuple(
                Allocation.parse(item, f"{where}.allocations[{index}]")
                for index, item in enumerate(allocations)
            ),
            event_id=EventId.parse(value["event_id"], f"{where}.event_id"),
            signature=Signature.parse(value["signature"], f"{where}.signature"),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "allocations": [allocation.to_json() for allocation in self.allocations],
            "event": self.event.to_json(),
            "event_id": str(self.event_id),
            "signature": str(self.signature),
        }


def unsigned_bytes(event: PayoutEvent, allocations: tuple[Allocation, ...]) -> bytes:
    return canonical_bytes(
        {
            "allocations": [allocation.to_json() for allocation in allocations],
            "event": event.to_json(),
        }
    )


def derive_event_id(event: PayoutEvent, allocations: tuple[Allocation, ...]) -> EventId:
    return EventId.of(unsigned_bytes(event, allocations))


def payout_message(event: PayoutEvent, allocations: tuple[Allocation, ...]) -> bytes:
    return hashlib.sha256(PAYOUT_DOMAIN + unsigned_bytes(event, allocations)).digest()


def allocate(budget: int, weighted_ids: Iterable[tuple[str, int]]) -> dict[str, int]:
    weighted = tuple(sorted(weighted_ids))
    if budget <= 0:
        raise SchemaError("budget must be positive")
    if not weighted or len({item[0] for item in weighted}) != len(weighted):
        raise SchemaError("weighted ids must be unique and non-empty")
    if any(weight <= 0 for _, weight in weighted):
        raise SchemaError("allocation weights must be positive")
    total = sum(weight for _, weight in weighted)
    floors: dict[str, int] = {}
    remainders: list[tuple[int, str]] = []
    for contribution_id, weight in weighted:
        amount, remainder = divmod(budget * weight, total)
        floors[contribution_id] = amount
        remainders.append((remainder, contribution_id))
    left = budget - sum(floors.values())
    for _, contribution_id in sorted(remainders, key=lambda item: (-item[0], item[1]))[:left]:
        floors[contribution_id] += 1
    return floors


def build_payout(
    event: PayoutEvent,
    reviews: Iterable[ReviewRecord],
    contributions: Mapping[str, Contribution],
    operator_key: SigningKey,
) -> PayoutRecord:
    if operator_key.public_key != event.operator:
        raise SchemaError("operator signing key does not match event.operator")
    allocations = payout_allocations(event, reviews, contributions)
    record = PayoutRecord(
        event=event,
        allocations=allocations,
        event_id=derive_event_id(event, allocations),
        signature=operator_key.sign(payout_message(event, allocations)),
    )
    validate_payout(record)
    return record


def payout_allocations(
    event: PayoutEvent,
    reviews: Iterable[ReviewRecord],
    contributions: Mapping[str, Contribution],
) -> tuple[Allocation, ...]:
    all_reviews = tuple(reviews)
    current = {record.review_id: record for record in active_reviews(all_reviews)}
    missing = set(event.review_ids) - set(current)
    if missing:
        missing_text = ", ".join(map(str, sorted(missing)))
        raise SchemaError(f"event names unknown or superseded review(s): {missing_text}")
    selected = tuple(current[review_id] for review_id in event.review_ids)
    by_id: dict[str, tuple[ReviewRecord, Contribution]] = {}
    for review in selected:
        payload = review.payload
        if payload.decision is not Decision.RECOGNIZED:
            raise SchemaError(f"review {review.review_id} is not recognized")
        if payload.target not in event.targets:
            raise SchemaError(f"review {review.review_id} is outside the event targets")
        reviewed_at = _datetime(payload.reviewed_at)
        if not _datetime(event.period_start) <= reviewed_at <= _datetime(event.period_end):
            raise SchemaError(f"review {review.review_id} is outside the event period")
        contribution = contributions.get(payload.contribution_id)
        if contribution is None:
            raise SchemaError(f"contribution {payload.contribution_id} is missing")
        validate_for_contribution(review, contribution)
        reward = contribution.payload.reward
        signature = contribution.reward_signature
        if reward is None or signature is None:
            raise SchemaError(f"contribution {payload.contribution_id} has no reward destination")
        if not reward_module.verify(contribution.contribution_id, reward.hotkey, signature):
            raise SchemaError(
                f"contribution {payload.contribution_id} has an invalid reward signature"
            )
        if payload.contribution_id in by_id:
            raise SchemaError(f"contribution {payload.contribution_id} appears more than once")
        by_id[payload.contribution_id] = (review, contribution)
    amounts = allocate(
        event.budget,
        (
            (contribution_id, review.payload.weight)
            for contribution_id, (review, _) in by_id.items()
        ),
    )
    return tuple(
        Allocation(
            contribution_id=contribution_id,
            review_id=review.review_id,
            target=review.payload.target,
            weight=review.payload.weight,
            destination=contribution.payload.reward.coldkey,
            amount=amounts[contribution_id],
        )
        for contribution_id, (review, contribution) in sorted(by_id.items())
        if contribution.payload.reward is not None
    )


def validate_payout(record: PayoutRecord) -> None:
    if tuple(sorted(record.allocations)) != record.allocations:
        raise SchemaError("allocations must be sorted by contribution_id")
    if not record.allocations:
        raise SchemaError("allocations must not be empty")
    if sum(allocation.amount for allocation in record.allocations) != record.event.budget:
        raise SchemaError("allocation amounts do not sum to the event budget")
    if any(allocation.amount < 0 for allocation in record.allocations):
        raise SchemaError("allocation amounts must not be negative")
    if record.event_id != derive_event_id(record.event, record.allocations):
        raise SchemaError("event_id does not match the canonical event and allocations")
    if not verify(
        payout_message(record.event, record.allocations), record.event.operator, record.signature
    ):
        raise SchemaError("payout operator signature verification failed")


def validate_payout_context(
    record: PayoutRecord,
    reviews: Iterable[ReviewRecord],
    contributions: Mapping[str, Contribution],
) -> None:
    validate_payout(record)
    expected = payout_allocations(record.event, reviews, contributions)
    if record.allocations != expected:
        raise SchemaError("payout allocations do not match the named reviews and contributions")


def load_event(path: Path) -> PayoutEvent:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SchemaError(f"{path}: invalid event JSON: {exc}") from None
    return PayoutEvent.parse(raw, str(path))


def load_payout(path: Path) -> PayoutRecord:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SchemaError(f"{path}: invalid payout JSON: {exc}") from None
    record = PayoutRecord.parse(raw, str(path))
    validate_payout(record)
    return record


def write_payout(root: Path, record: PayoutRecord) -> Path:
    validate_payout(record)
    directory = root / PAYOUT_ROOT
    destination = directory / f"{record.event_id}.json"
    if destination.exists():
        existing = load_payout(destination)
        if existing == record:
            return destination
        raise SchemaError(f"{destination}: refusing to overwrite a different payout")
    directory.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(canonical_bytes(record.to_json()))
    return destination
