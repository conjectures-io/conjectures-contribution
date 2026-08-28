from __future__ import annotations

from collections.abc import Callable
from typing import cast

from .base import (
    ChangesetCheck,
    ChangesetContext,
    ChangesetFn,
    Check,
    CheckContext,
    CheckFn,
    Finding,
)

_CHECKS: list[Check] = []
_CHANGESET_CHECKS: list[ChangesetCheck] = []


def _claim(check_id: str) -> None:
    taken = [c.id for c in _CHECKS] + [c.id for c in _CHANGESET_CHECKS]
    if check_id in taken:
        raise RuntimeError(f"duplicate check id: {check_id}")


def register(check_id: str, title: str) -> Callable[[CheckFn], Check]:
    def decorate(fn: CheckFn) -> Check:
        _claim(check_id)
        check = cast("Check", fn)
        check.id, check.title = check_id, title
        _CHECKS.append(check)
        return check

    return decorate


def register_changeset(check_id: str, title: str) -> Callable[[ChangesetFn], ChangesetCheck]:
    def decorate(fn: ChangesetFn) -> ChangesetCheck:
        _claim(check_id)
        check = cast("ChangesetCheck", fn)
        check.id, check.title = check_id, title
        _CHANGESET_CHECKS.append(check)
        return check

    return decorate


# Registration order follows imports; reports read in rule order.
def checks() -> tuple[Check, ...]:
    return tuple(sorted(_CHECKS, key=lambda check: check.id))


def changeset_checks() -> tuple[ChangesetCheck, ...]:
    return tuple(sorted(_CHANGESET_CHECKS, key=lambda check: check.id))


def run_all(ctx: CheckContext) -> tuple[Finding, ...]:
    return tuple(finding for check in checks() for finding in check(ctx))


def run_changeset(ctx: ChangesetContext) -> tuple[Finding, ...]:
    return tuple(finding for check in changeset_checks() for finding in check(ctx))
