from __future__ import annotations

import hashlib
import re
import unicodedata
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Any, ClassVar, Final, Self, cast


class SchemaError(ValueError):
    pass


SCHEMA_VERSION: Final = 1
METADATA_FILENAME: Final = "metadata.json"
DRAFT_FILENAME: Final = "draft.json"
REQUIRED_ARTIFACTS: Final = frozenset({"sources.md"})

MAX_ARTIFACTS: Final = 32
MAX_ARTIFACT_BYTES: Final = 1 << 20
MAX_TOTAL_BYTES: Final = 4 << 20
MAX_TITLE_CHARS: Final = 120

_HEX = re.compile(r"[0-9a-f]*")
_SLUG = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
_ARTIFACT_NAME = re.compile(r"[a-z0-9][a-z0-9._-]{0,63}")
_COMMIT = re.compile(r"[0-9a-f]{40}")


def _as_mapping(value: Any, where: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise SchemaError(f"{where}: expected an object")
    return cast("Mapping[str, Any]", value)


def _as_sequence(value: Any, where: str) -> Sequence[Any]:
    if not isinstance(value, list):
        raise SchemaError(f"{where}: expected an array")
    return cast("Sequence[Any]", value)


def _as_str(value: Any, where: str) -> str:
    if not isinstance(value, str):
        raise SchemaError(f"{where}: expected a string")
    return value


def _as_int(value: Any, where: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise SchemaError(f"{where}: expected an integer")
    return value


def _field(obj: Mapping[str, Any], key: str, where: str) -> Any:
    if key not in obj:
        raise SchemaError(f"{where}: missing field '{key}'")
    return obj[key]


# Unknown keys change the hashed bytes but would escape every rule below, so the
# only safe reading of an unrecognised field is to reject the document.
def _exact_keys(obj: Mapping[str, Any], allowed: frozenset[str], where: str) -> None:
    unexpected = sorted(set(obj) - allowed)
    if unexpected:
        raise SchemaError(f"{where}: unexpected field(s) {', '.join(unexpected)}")


class ChangeKind(StrEnum):
    ADDED = "added"
    MODIFIED = "modified"
    DELETED = "deleted"


@dataclass(frozen=True, slots=True, order=True)
class Change:
    path: Path
    kind: ChangeKind


@dataclass(frozen=True, slots=True, order=True)
class Hex:
    WIDTH: ClassVar[int] = 0

    value: str

    def __post_init__(self) -> None:
        if len(self.value) != self.WIDTH or _HEX.fullmatch(self.value) is None:
            raise SchemaError(f"expected {self.WIDTH} lowercase hex characters, got {self.value!r}")

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        try:
            return cls(_as_str(raw, where))
        except SchemaError as exc:
            raise SchemaError(f"{where}: {exc}") from None

    def __str__(self) -> str:
        return self.value


class Digest(Hex):
    __slots__ = ()
    WIDTH: ClassVar[int] = 64

    @classmethod
    def of(cls, data: bytes) -> Self:
        return cls(hashlib.sha256(data).hexdigest())


class Sha256(Digest):
    __slots__ = ()


class ContributionId(Digest):
    __slots__ = ()


class PublicKey(Hex):
    __slots__ = ()
    WIDTH: ClassVar[int] = 64


class Signature(Hex):
    __slots__ = ()
    WIDTH: ClassVar[int] = 128


@dataclass(frozen=True, slots=True, order=True)
class TargetSlug:
    value: str

    def __post_init__(self) -> None:
        if _SLUG.fullmatch(self.value) is None:
            raise SchemaError(f"not a target slug: {self.value!r}")

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        try:
            return cls(_as_str(raw, where))
        except SchemaError as exc:
            raise SchemaError(f"{where}: {exc}") from None

    def __str__(self) -> str:
        return self.value


@dataclass(frozen=True, slots=True, order=True)
class ArtifactName:
    value: str

    def __post_init__(self) -> None:
        if _ARTIFACT_NAME.fullmatch(self.value) is None:
            raise SchemaError(f"unsafe artifact name: {self.value!r}")
        if self.value in {METADATA_FILENAME, DRAFT_FILENAME}:
            raise SchemaError(f"reserved artifact name: {self.value!r}")

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        try:
            return cls(_as_str(raw, where))
        except SchemaError as exc:
            raise SchemaError(f"{where}: {exc}") from None

    def __str__(self) -> str:
        return self.value


class _ParsedEnum(StrEnum):
    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        text = _as_str(raw, where)
        try:
            return cls(text)
        except ValueError:
            allowed = ", ".join(m.value for m in cls)
            raise SchemaError(f"{where}: expected one of {allowed}, got {text!r}") from None


class Kind(_ParsedEnum):
    IDEA = "idea"
    LEMMA = "lemma"
    PARTIAL_PROOF = "partial-proof"
    REFUTATION = "refutation"


class Mode(_ParsedEnum):
    FORMALIZED = "formalized"
    COUNTEREXAMPLE = "counterexample"
    EITHER = "either"


@dataclass(frozen=True, slots=True, order=True)
class ArtifactRef:
    name: ArtifactName
    digest: Sha256
    size: int

    def __post_init__(self) -> None:
        if self.size < 0:
            raise SchemaError(f"{self.name}: negative size")

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        obj = _as_mapping(raw, where)
        _exact_keys(obj, frozenset({"name", "sha256", "size"}), where)
        return cls(
            name=ArtifactName.parse(_field(obj, "name", where), f"{where}.name"),
            digest=Sha256.parse(_field(obj, "sha256", where), f"{where}.sha256"),
            size=_as_int(_field(obj, "size", where), f"{where}.size"),
        )

    def to_json(self) -> dict[str, Any]:
        return {"name": str(self.name), "sha256": str(self.digest), "size": self.size}


def _validate_title(title: str) -> None:
    if not title or title != title.strip():
        raise SchemaError("title: must be non-empty and not padded with whitespace")
    if len(title) > MAX_TITLE_CHARS:
        raise SchemaError(f"title: longer than {MAX_TITLE_CHARS} characters")
    if "\n" in title:
        raise SchemaError("title: must be a single line")
    # Cf covers the bidi overrides and zero-width joiners a title could use to render
    # as something other than what the reviewed bytes say.
    if any(unicodedata.category(ch) in {"Cc", "Cf"} for ch in title):
        raise SchemaError("title: must not contain control or formatting characters")


def _validate_commit(commit: str) -> None:
    if _COMMIT.fullmatch(commit) is None:
        raise SchemaError("tasks_commit: expected a 40-character commit sha")


_PAYLOAD_KEYS: Final = frozenset(
    {
        "artifacts",
        "author",
        "kind",
        "mode",
        "parents",
        "reward_target_id",
        "schema_version",
        "target",
        "tasks_commit",
        "title",
    }
)


@dataclass(frozen=True, slots=True)
class Payload:
    schema_version: int
    target: TargetSlug
    reward_target_id: str
    tasks_commit: str
    mode: Mode
    kind: Kind
    title: str
    author: PublicKey
    parents: tuple[ContributionId, ...]
    artifacts: tuple[ArtifactRef, ...]

    # Ordering is part of the hashed identity: the same content in two orders would
    # otherwise be two distinct contributions.
    def __post_init__(self) -> None:
        _validate_title(self.title)
        _validate_commit(self.tasks_commit)
        if self.schema_version != SCHEMA_VERSION:
            raise SchemaError(
                f"schema_version: expected {SCHEMA_VERSION}, got {self.schema_version}"
            )
        if list(self.parents) != sorted(set(self.parents)):
            raise SchemaError("parents: must be sorted and free of duplicates")
        names = [a.name for a in self.artifacts]
        if names != sorted(set(names)):
            raise SchemaError("artifacts: must be sorted by name and free of duplicates")
        if not self.artifacts:
            raise SchemaError("artifacts: at least one artifact is required")

    @classmethod
    def parse(cls, raw: Any, where: str = "payload") -> Self:
        obj = _as_mapping(raw, where)
        _exact_keys(obj, _PAYLOAD_KEYS, where)
        artifacts = _as_sequence(_field(obj, "artifacts", where), f"{where}.artifacts")
        parents = _as_sequence(_field(obj, "parents", where), f"{where}.parents")
        return cls(
            schema_version=_as_int(_field(obj, "schema_version", where), f"{where}.schema_version"),
            target=TargetSlug.parse(_field(obj, "target", where), f"{where}.target"),
            reward_target_id=_as_str(
                _field(obj, "reward_target_id", where), f"{where}.reward_target_id"
            ),
            tasks_commit=_as_str(_field(obj, "tasks_commit", where), f"{where}.tasks_commit"),
            mode=Mode.parse(_field(obj, "mode", where), f"{where}.mode"),
            kind=Kind.parse(_field(obj, "kind", where), f"{where}.kind"),
            title=_as_str(_field(obj, "title", where), f"{where}.title"),
            author=PublicKey.parse(_field(obj, "author", where), f"{where}.author"),
            parents=tuple(
                ContributionId.parse(p, f"{where}.parents[{i}]") for i, p in enumerate(parents)
            ),
            artifacts=tuple(
                ArtifactRef.parse(a, f"{where}.artifacts[{i}]") for i, a in enumerate(artifacts)
            ),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "artifacts": [a.to_json() for a in self.artifacts],
            "author": str(self.author),
            "kind": str(self.kind),
            "mode": str(self.mode),
            "parents": [str(p) for p in self.parents],
            "reward_target_id": self.reward_target_id,
            "schema_version": self.schema_version,
            "target": str(self.target),
            "tasks_commit": self.tasks_commit,
            "title": self.title,
        }


@dataclass(frozen=True, slots=True)
class Contribution:
    payload: Payload
    contribution_id: ContributionId
    signature: Signature

    # Structural only. That the id matches the payload and the signature verifies are
    # checks (C004, C006), so a malformed record must still be representable to be reported.
    @classmethod
    def parse(cls, raw: Any, where: str = "metadata") -> Self:
        obj = _as_mapping(raw, where)
        _exact_keys(obj, frozenset({"payload", "contribution_id", "signature"}), where)
        return cls(
            payload=Payload.parse(_field(obj, "payload", where), f"{where}.payload"),
            contribution_id=ContributionId.parse(
                _field(obj, "contribution_id", where), f"{where}.contribution_id"
            ),
            signature=Signature.parse(_field(obj, "signature", where), f"{where}.signature"),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "contribution_id": str(self.contribution_id),
            "payload": self.payload.to_json(),
            "signature": str(self.signature),
        }


@dataclass(frozen=True, slots=True)
class Draft:
    target: TargetSlug
    title: str
    kind: Kind
    mode: Mode
    parents: tuple[ContributionId, ...]

    def __post_init__(self) -> None:
        _validate_title(self.title)

    @classmethod
    def parse(cls, raw: Any, where: str = "draft") -> Self:
        obj = _as_mapping(raw, where)
        _exact_keys(obj, frozenset({"target", "title", "kind", "mode", "parents"}), where)
        parents = _as_sequence(_field(obj, "parents", where), f"{where}.parents")
        return cls(
            target=TargetSlug.parse(_field(obj, "target", where), f"{where}.target"),
            title=_as_str(_field(obj, "title", where), f"{where}.title"),
            kind=Kind.parse(_field(obj, "kind", where), f"{where}.kind"),
            mode=Mode.parse(_field(obj, "mode", where), f"{where}.mode"),
            parents=tuple(
                sorted(
                    {
                        ContributionId.parse(p, f"{where}.parents[{i}]")
                        for i, p in enumerate(parents)
                    }
                )
            ),
        )

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": str(self.kind),
            "mode": str(self.mode),
            "parents": [str(p) for p in self.parents],
            "target": str(self.target),
            "title": self.title,
        }
