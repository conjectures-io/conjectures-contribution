from __future__ import annotations

import json
from collections import defaultdict
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Self

from .model import Mode, TargetSlug

DEFAULT_TIER = "tier-1"


class PoolError(RuntimeError):
    pass


@dataclass(frozen=True, slots=True)
class Target:
    slug: TargetSlug
    problem_id: str
    reward_target_id: str
    theorems: tuple[str, ...]
    bundles: Mapping[Mode, str]


@dataclass(frozen=True, slots=True)
class Pool:
    tier: str
    tasks_commit: str
    targets: Mapping[TargetSlug, Target]
    retired_theorems: frozenset[str]

    @classmethod
    def load(cls, root: Path, tier: str = DEFAULT_TIER) -> Self:
        allowlist = _read_json(root / "allowlist.json")
        by_task_id = {
            _require(entry, "task_id"): entry
            for entry in allowlist["allowed_task_bundles"]
            if entry["tier"] == tier
        }

        groups: dict[str, list[tuple[str, dict[str, Any]]]] = defaultdict(list)
        seen: set[str] = set()
        for directory in sorted(p for p in (root / "pool" / tier).iterdir() if p.is_dir()):
            manifest = directory / "manifest.json"
            if not manifest.is_file():
                raise PoolError(f"{directory}: missing manifest.json")
            task_id = _require(_read_json(manifest), "task_id")
            entry = by_task_id.get(task_id)
            if entry is None:
                raise PoolError(f"{directory.name}: task_id {task_id} is not in the allowlist")
            seen.add(task_id)
            groups[entry["problem_id"]].append((directory.name, entry))

        orphaned = sorted(set(by_task_id) - seen)
        if orphaned:
            raise PoolError(f"allowlist entries with no bundle directory: {', '.join(orphaned)}")

        targets = {t.slug: t for t in (_build_target(p, g) for p, g in groups.items())}
        return cls(
            tier=tier,
            tasks_commit=allowlist["repository_commit"],
            targets=MappingProxyType(targets),
            retired_theorems=frozenset(
                _read_json(root / "tiers" / tier / "retired-source-theorems.json")[
                    "source_theorems"
                ]
            ),
        )


def _build_target(problem_id: str, group: list[tuple[str, dict[str, Any]]]) -> Target:
    bundles: dict[Mode, str] = {}
    slugs: set[str] = set()
    rewards: set[str] = set()
    theorems: set[str] = set()

    for directory_name, entry in group:
        mode = Mode(entry["mode"])
        suffix = f"-{mode}"
        if not directory_name.endswith(suffix):
            raise PoolError(f"{directory_name}: does not end with its mode {suffix!r}")
        if mode in bundles:
            raise PoolError(f"{problem_id}: duplicate {mode} bundle")
        bundles[mode] = directory_name
        slugs.add(directory_name[: -len(suffix)])
        rewards.add(entry["reward_target_id"])
        theorems.update(entry["theorems"])

    if len(slugs) != 1:
        raise PoolError(f"{problem_id}: bundles disagree on slug: {sorted(slugs)}")
    if len(rewards) != 1:
        raise PoolError(f"{problem_id}: bundles disagree on reward_target_id: {sorted(rewards)}")
    if set(bundles) != {Mode.FORMALIZED, Mode.COUNTEREXAMPLE}:
        raise PoolError(f"{problem_id}: expected both modes, got {sorted(str(m) for m in bundles)}")

    return Target(
        slug=TargetSlug(slugs.pop()),
        problem_id=problem_id,
        reward_target_id=rewards.pop(),
        theorems=tuple(sorted(theorems)),
        bundles=MappingProxyType(bundles),
    )


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise PoolError(f"{path}: not found — is the conjectures submodule checked out?") from None
    except json.JSONDecodeError as exc:
        raise PoolError(f"{path}: invalid JSON ({exc})") from None


def _require(obj: Mapping[str, Any], key: str) -> Any:
    if key not in obj:
        raise PoolError(f"missing field '{key}'")
    return obj[key]
