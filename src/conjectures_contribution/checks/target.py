from __future__ import annotations

from collections.abc import Iterator

from ..model import Contribution
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register


@register("C002", "target exists in the pinned pool and is open")
@needs_contribution
def target_known(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    payload = contribution.payload
    target = ctx.pool.targets.get(payload.target)
    if target is None:
        yield Finding("C002", Severity.ERROR, f"unknown target '{payload.target}'")
        return
    if payload.reward_target_id != target.reward_target_id:
        yield Finding(
            "C002",
            Severity.ERROR,
            f"reward_target_id is '{payload.reward_target_id}', "
            f"pool publishes '{target.reward_target_id}'",
        )
    retired = sorted(set(target.theorems) & ctx.pool.retired_theorems)
    if retired:
        yield Finding("C002", Severity.ERROR, f"target is retired: {', '.join(retired)}")


@register("C003", "tasks commit matches the pinned submodule")
@needs_contribution
def tasks_commit_pinned(ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    declared = contribution.payload.tasks_commit
    if declared != ctx.pool.tasks_commit:
        yield Finding(
            "C003",
            Severity.ERROR,
            f"tasks_commit is {declared}, pinned pool is at {ctx.pool.tasks_commit}",
        )
