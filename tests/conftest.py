from __future__ import annotations

import json
from collections.abc import Callable, Sequence
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any

import pytest
from bittensor_core import Keypair

from conjectures_contribution.build import Built
from conjectures_contribution.canonical import canonical_bytes, derive_id, payload_bytes
from conjectures_contribution.checks import (
    Change,
    ChangesetContext,
    Severity,
    run_all,
    run_changeset,
)
from conjectures_contribution.loader import load_context
from conjectures_contribution.model import (
    DRAFT_FILENAME,
    METADATA_FILENAME,
    Contribution,
    Draft,
    Kind,
    Mode,
    Reward,
    Ss58Address,
    TargetSlug,
)
from conjectures_contribution.pool import Pool
from conjectures_contribution.signing import SigningKey
from conjectures_contribution.store import Published
from conjectures_contribution.wallet import RewardSigner

COMMIT = "0" * 40
SLUG = "demo-1"
THEOREM = "Demo.demo"
REWARD_ID = f"fc-target:{THEOREM}"

# Development keypairs: deterministic, well known, and needing no wallet on disk.
HOTKEY_URI = "//Alice"
COLDKEY_URI = "//Bob"


def reward_signer(uri: str = HOTKEY_URI) -> RewardSigner:
    keypair = Keypair.create_from_uri(uri)
    return RewardSigner(
        reward=Reward(
            coldkey=Ss58Address(str(Keypair.create_from_uri(COLDKEY_URI).ss58_address)),
            hotkey=Ss58Address(str(keypair.ss58_address)),
        ),
        keypair=keypair,
    )


def _write_pool(root: Path, retired: Sequence[str], slugs: Sequence[str] = (SLUG,)) -> None:
    bundles = [
        {
            "task_id": f"task-{slug}-{mode}",
            "tier": "tier-1",
            "mode": mode,
            "problem_id": f"problem-{slug}",
            "reward_target_id": REWARD_ID,
            "theorems": [THEOREM],
            "slug": slug,
        }
        for slug in slugs
        for mode in ("formalized", "counterexample")
    ]
    (root / "allowlist.json").write_bytes(
        canonical_bytes(
            {
                "repository_commit": COMMIT,
                # `slug` is ours, not an allowlist field: the real pool derives it from the
                # bundle directory name, which is what Pool.load reads.
                "allowed_task_bundles": [
                    {k: v for k, v in bundle.items() if k != "slug"} for bundle in bundles
                ],
            }
        )
    )
    for bundle in bundles:
        directory = root / "pool" / "tier-1" / f"{bundle['slug']}-{bundle['mode']}"
        directory.mkdir(parents=True)
        (directory / "manifest.json").write_bytes(canonical_bytes({"task_id": bundle["task_id"]}))
    tiers = root / "tiers" / "tier-1"
    tiers.mkdir(parents=True)
    (tiers / "retired-source-theorems.json").write_bytes(
        canonical_bytes({"source_theorems": list(retired)})
    )


@dataclass(frozen=True, slots=True)
class Repo:
    root: Path
    pool: Pool
    key: SigningKey
    reward: RewardSigner

    @property
    def contributions(self) -> Path:
        return self.root / "contributions"

    @property
    def drafts(self) -> Path:
        return self.root / "drafts"

    def draft(self, *, files: dict[str, str | bytes] | None = None, **overrides: Any) -> Path:
        directory = self.drafts / SLUG
        directory.mkdir(parents=True, exist_ok=True)
        draft = Draft(
            target=TargetSlug(SLUG),
            title="A partial reduction",
            kind=Kind.IDEA,
            mode=Mode.EITHER,
            parents=(),
        )
        (directory / DRAFT_FILENAME).write_bytes(
            canonical_bytes(replace(draft, **overrides).to_json())
        )
        for name, body in (files or {"sources.md": "# Sources\n"}).items():
            if isinstance(body, bytes):
                (directory / name).write_bytes(body)
            else:
                (directory / name).write_text(body, encoding="utf-8")
        return directory

    def promote(
        self,
        directory: Path | None = None,
        *,
        reward: bool = True,
        signer: RewardSigner | None = None,
    ) -> Path:
        source = directory if directory is not None else self.draft()
        draft = Draft.parse(json.loads((source / DRAFT_FILENAME).read_text()))
        chosen = (signer or self.reward) if reward else None
        return Built.from_draft(draft, source, self.pool, self.key, chosen).write(
            self.contributions
        )

    def errors(self, directory: Path) -> tuple[str, ...]:
        context = load_context(
            directory,
            contributions_root=self.contributions,
            pool=self.pool,
            published=Published.scan(self.contributions),
        )
        return tuple(f.check_id for f in run_all(context) if f.severity is Severity.ERROR)

    def changeset_errors(self, *changes: Change) -> tuple[str, ...]:
        context = ChangesetContext(
            repo_root=self.root,
            contributions_root=self.contributions,
            changes=tuple(changes),
        )
        return tuple(f.check_id for f in run_changeset(context) if f.severity is Severity.ERROR)

    def read(self, directory: Path) -> Contribution:
        return Contribution.parse(json.loads((directory / METADATA_FILENAME).read_text()))

    # Re-signing keeps a payload mutation from also tripping C004 and C006, so each
    # rule can be tested in isolation.
    def resign(self, directory: Path, **changes: Any) -> Path:
        payload = replace(self.read(directory).payload, **changes)
        contribution_id = derive_id(payload)
        contribution = Contribution(
            payload=payload,
            contribution_id=contribution_id,
            signature=self.key.sign(payload_bytes(payload)),
            reward_signature=(
                None if payload.reward is None else self.reward.sign(contribution_id)
            ),
        )
        (directory / METADATA_FILENAME).write_bytes(canonical_bytes(contribution.to_json()))
        moved = self.contributions / str(payload.target) / str(contribution.contribution_id)
        if moved != directory:
            moved.parent.mkdir(parents=True, exist_ok=True)
            directory.rename(moved)
        return moved

    def rewrite_raw(
        self, directory: Path, mutate: Callable[[dict[str, Any]], dict[str, Any]]
    ) -> None:
        raw: dict[str, Any] = json.loads((directory / METADATA_FILENAME).read_text())
        (directory / METADATA_FILENAME).write_bytes(canonical_bytes(mutate(raw)))


def make_repo(tmp_path: Path, retired: Sequence[str] = (), slugs: Sequence[str] = (SLUG,)) -> Repo:
    pool_root = tmp_path / "conjectures"
    pool_root.mkdir()
    _write_pool(pool_root, retired, slugs)
    return Repo(
        root=tmp_path,
        pool=Pool.load(pool_root),
        key=SigningKey.generate(),
        reward=reward_signer(),
    )


@pytest.fixture
def repo(tmp_path: Path) -> Repo:
    return make_repo(tmp_path)


@pytest.fixture
def published(repo: Repo) -> Path:
    return repo.promote()
