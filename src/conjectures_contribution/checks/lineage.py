from __future__ import annotations

from collections.abc import Iterator

from ..model import Contribution
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register


@register("C010", "parent contributions exist")
@needs_contribution
def parents_exist(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    for parent in contribution.payload.parents:
        if str(parent) not in ctx.published.by_id:
            yield Finding("C010", Severity.ERROR, f"unknown parent contribution {parent}")
