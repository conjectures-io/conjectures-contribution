from __future__ import annotations

import functools
from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Any, Protocol

from ..model import Change, Contribution
from ..pool import Pool
from ..store import Published, contribution_directory


class Severity(StrEnum):
    ERROR = "error"
    WARNING = "warning"
    SKIPPED = "skipped"


@dataclass(frozen=True, slots=True)
class Finding:
    check_id: str
    severity: Severity
    message: str
    path: str | None = None

    def to_json(self) -> dict[str, Any]:
        return {
            "check_id": self.check_id,
            "severity": str(self.severity),
            "message": self.message,
            "path": self.path,
        }


@dataclass(frozen=True, slots=True)
class CheckContext:
    directory: Path
    contributions_root: Path
    pool: Pool
    published: Published
    raw: Any | None
    raw_bytes: bytes | None
    contribution: Contribution | None
    parse_error: str | None


@dataclass(frozen=True, slots=True)
class ChangesetContext:
    repo_root: Path
    contributions_root: Path
    changes: tuple[Change, ...]

    def contribution_of(self, path: Path) -> Path | None:
        return contribution_directory(self.contributions_root, path)


class Check(Protocol):
    id: str
    title: str

    def __call__(self, ctx: CheckContext) -> Iterable[Finding]: ...


class ChangesetCheck(Protocol):
    id: str
    title: str

    def __call__(self, ctx: ChangesetContext) -> Iterable[Finding]: ...


CheckFn = Callable[[CheckContext], Iterable[Finding]]
ChangesetFn = Callable[[ChangesetContext], Iterable[Finding]]
ContributionFn = Callable[[CheckContext, Contribution], Iterable[Finding]]


# A rule that reads the record cannot also be the rule that reports it unreadable;
# C001 owns that, and everything downstream stays silent rather than piling on.
def needs_contribution(fn: ContributionFn) -> CheckFn:
    @functools.wraps(fn)
    def wrapper(ctx: CheckContext) -> Iterator[Finding]:
        if ctx.contribution is None:
            return
        yield from fn(ctx, ctx.contribution)

    return wrapper
