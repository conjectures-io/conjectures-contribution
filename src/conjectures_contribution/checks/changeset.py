from __future__ import annotations

from collections.abc import Iterator
from pathlib import Path

from ..model import ChangeKind
from .base import ChangesetContext, Finding, Severity
from .registry import register_changeset

MAX_REPORTED = 10


@register_changeset("C011", "the change is confined to one new contribution")
def confined_to_one_contribution(ctx: ChangesetContext) -> Iterator[Finding]:
    if not ctx.changes:
        return

    outside = sorted(c for c in ctx.changes if ctx.contribution_of(c.path) is None)
    for change in outside[:MAX_REPORTED]:
        yield Finding("C011", Severity.ERROR, "outside any contribution", _show(ctx, change.path))
    if len(outside) > MAX_REPORTED:
        yield Finding(
            "C011", Severity.ERROR, f"and {len(outside) - MAX_REPORTED} further paths outside"
        )

    touched = {ctx.contribution_of(c.path) for c in ctx.changes} - {None}
    if len(touched) > 1:
        names = ", ".join(sorted(_show(ctx, d) for d in touched if d is not None))
        yield Finding("C011", Severity.ERROR, f"touches {len(touched)} contributions: {names}")
    elif not touched and not outside:
        yield Finding("C011", Severity.ERROR, "no contribution directory in the change set")


@register_changeset("C012", "published contributions are never modified or removed")
def append_only(ctx: ChangesetContext) -> Iterator[Finding]:
    edited = sorted(c for c in ctx.changes if c.kind is not ChangeKind.ADDED)
    for change in edited[:MAX_REPORTED]:
        yield Finding(
            "C012", Severity.ERROR, f"{change.kind} an existing path", _show(ctx, change.path)
        )
    if len(edited) > MAX_REPORTED:
        yield Finding(
            "C012", Severity.ERROR, f"and {len(edited) - MAX_REPORTED} further existing paths"
        )


def _show(ctx: ChangesetContext, path: Path) -> str:
    try:
        return str(path.relative_to(ctx.repo_root))
    except ValueError:
        return str(path)
