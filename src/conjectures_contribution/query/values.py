"""Value types for the query path, and the one representation that makes it total.

Every field the corpus parses is a `Field[T]`: either the value, or an `Unavailable`
naming why it is missing. A document that fails to parse a field still yields a row —
the hole is carried, never guessed at, and never rendered as `0` or `false`.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from datetime import date, timedelta
from enum import StrEnum
from typing import Any, Self, TypeAlias, TypeVar

from ..model import PublicKey, SchemaError

_ISO_LENGTH = 10
_HEX = re.compile(r"[0-9a-f]{40}")
_RELATIVE = re.compile(r"([0-9]+)([dwmy])")
# Calendar months vary; a browsing window does not need them to. `--since 6m` is
# "about half a year back", and the resolved day is echoed so nobody has to guess.
_UNIT_DAYS = {"d": 1, "w": 7, "m": 30, "y": 365}


@dataclass(frozen=True, slots=True)
class Unavailable:
    reason: str


_T = TypeVar("_T")
_U = TypeVar("_U")

Field: TypeAlias = _T | Unavailable

# Two identities live in the corpus: the ed25519 key that signed a contribution, and the
# ss58 addresses money goes to. `--mine` is authorship, so it resolves to this one.
AuthorKey: TypeAlias = PublicKey


class Source(StrEnum):
    TREE = "tree"
    POOL = "pool"


@dataclass(frozen=True, slots=True, order=True)
class Date:
    value: str

    def __post_init__(self) -> None:
        if len(self.value) != _ISO_LENGTH:
            raise SchemaError(f"not an ISO date: {self.value!r}")
        try:
            date.fromisoformat(self.value)
        except ValueError:
            raise SchemaError(f"not an ISO date: {self.value!r}") from None

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        if not isinstance(raw, str):
            raise SchemaError(f"{where}: expected a string")
        try:
            return cls(raw)
        except SchemaError as exc:
            raise SchemaError(f"{where}: {exc}") from None

    # Relative forms resolve here, at the boundary, so the pipeline below only ever sees
    # an absolute day and a rerun means what the run meant.
    @classmethod
    def resolve(cls, text: str, today: date) -> Self:
        match = _RELATIVE.fullmatch(text)
        if match is None:
            return cls.parse(text, "date")
        return cls(
            (today - timedelta(days=int(match.group(1)) * _UNIT_DAYS[match.group(2)])).isoformat()
        )

    def __str__(self) -> str:
        return self.value


@dataclass(frozen=True, slots=True, order=True)
class Commit:
    value: str

    def __post_init__(self) -> None:
        if _HEX.fullmatch(self.value) is None:
            raise SchemaError(f"not a commit sha: {self.value!r}")

    @classmethod
    def parse(cls, raw: Any, where: str) -> Self:
        if not isinstance(raw, str):
            raise SchemaError(f"{where}: expected a string")
        try:
            return cls(raw)
        except SchemaError as exc:
            raise SchemaError(f"{where}: {exc}") from None

    def __str__(self) -> str:
        return self.value


def mapped(value: Field[_T | None], fn: Callable[[_T], _U]) -> Field[_U | None]:
    if value is None or isinstance(value, Unavailable):
        return value
    return fn(value)
