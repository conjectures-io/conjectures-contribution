from __future__ import annotations

from collections.abc import Iterator

from ..canonical import derive_id
from ..model import Contribution
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register


@register("C004", "contribution id matches its payload and its location")
@needs_contribution
def id_matches_payload(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    derived = derive_id(contribution.payload)
    if derived != contribution.contribution_id:
        yield Finding(
            "C004",
            Severity.ERROR,
            f"contribution_id is {contribution.contribution_id}, payload hashes to {derived}",
        )

    # The target directory is the addressable index of a conjecture; a bundle filed under
    # the wrong one would be invisible where it belongs and unattributed where it sits.
    expected = (
        ctx.contributions_root
        / str(contribution.payload.target)
        / str(contribution.contribution_id)
    )
    if ctx.directory.resolve() != expected.resolve():
        yield Finding("C004", Severity.ERROR, f"expected to live at {expected}")


@register("C005", "contribution id is new")
@needs_contribution
def id_is_new(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    here = ctx.directory.resolve()
    for other in ctx.published.by_id.get(str(contribution.contribution_id), ()):
        if other.resolve() != here:
            yield Finding("C005", Severity.ERROR, f"contribution id already published at {other}")


# Identical artifacts under a new author key is what re-signing someone else's work
# looks like; a genuine follow-up cites it in parents instead.
@register("C015", "content is not a copy of a published contribution")
@needs_contribution
def content_is_new(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    fingerprint = frozenset(str(a.digest) for a in contribution.payload.artifacts)
    here = ctx.directory.resolve()
    for other in ctx.published.by_content.get(fingerprint, ()):
        if other.resolve() != here:
            yield Finding(
                "C015", Severity.ERROR, f"identical artifacts already published at {other}"
            )
