from __future__ import annotations

import json
import re
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

# Rich renders an option name as several separately styled spans, so once colour is on
# the bytes read "\x1b[1;36m-\x1b[0m\x1b[1;36m-install\x1b[0m…" and a plain substring
# search for "--install-completion" finds nothing. CI runs with colour forced on and a
# local pipe does not, which is why help assertions pass here and fail there. Assert
# against the visible text instead.
_ANSI = re.compile(r"\x1b\[[0-9;]*m")


def plain(text: str) -> str:
    return _ANSI.sub("", text)


COMMIT = "0" * 40
SOURCES = "# Sources\n\n- Original work.\n"
# C007 requires a Lean artifact and C024 rejects the scaffold, so the default draft
# carries a small real one rather than leaving every test to supply it.
SCRIPT = (
    "namespace Contribution.Demo\n"
    "theorem le_succ (n : Nat) : n \u2264 n + 1 := Nat.le_succ n\n"
    "end Contribution.Demo\n"
)
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
        default: dict[str, str | bytes] = {"sources.md": SOURCES, "script.lean": SCRIPT}
        for name, body in (files or default).items():
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

    def reviews(self, directory: Path) -> tuple[str, ...]:
        context = load_context(
            directory,
            contributions_root=self.contributions,
            pool=self.pool,
            published=Published.scan(self.contributions),
        )
        return tuple(f.check_id for f in run_all(context) if f.severity is Severity.REVIEW)

    # Most Lean rules need only one file to fire; this keeps each test to its subject.
    def with_lean(self, source: str, name: str = "script.lean") -> Path:
        return self.promote(self.draft(files={"sources.md": SOURCES, name: source}))

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


# The corpus the query tests read: five targets, a shared coldkey, an orphan, one unindexed
# directory, one hole. Written by hand rather than promoted, so a date or a malformed field is
# what the test says it is and no assertion depends on the 209 real targets.
QUERY_POOL_SLUGS = ("demo-1", "demo-2", "demo-3", "demo-4")
DRIFTED_SLUG = "demo-5"
AUTHOR_A = "a" * 64
AUTHOR_B = "b" * 64
AUTHOR_C = "c" * 64
COLDKEY_SHARED = "5" + "C" * 47
COLDKEY_OTHER = "5" + "D" * 47
HOTKEY_A = "5" + "E" * 47
HOTKEY_B = "5" + "F" * 47
STALE_COMMIT = "1" * 40
C1, C2, C3, C4, C5, UNINDEXED = (str(n) * 64 for n in range(1, 7))
D1 = "Contribution.Demo.le_succ"
D2 = "Contribution.Demo.card_le"
D3 = "Contribution.Other.distinctDistances_mono"
INDEX_FILENAME = "index.json"


def query_entry(identifier: str, added: str, **overrides: Any) -> dict[str, Any]:
    entry: dict[str, Any] = {
        "added": added,
        "artifacts": ["script.lean", "sources.md"],
        "author": AUTHOR_A,
        "coldkey": COLDKEY_SHARED,
        "contribution_id": identifier,
        "declarations": [],
        "hotkey": HOTKEY_A,
        "kind": "lemma",
        "mode": "either",
        "parents": [],
        "path": f"{identifier}/",
        "tasks_commit": COMMIT,
        "title": "A partial reduction",
    }
    entry.update(overrides)
    return entry


def write_index(
    contributions: Path,
    slug: str,
    entries: Sequence[dict[str, Any]],
    *,
    schema: int = 2,
    count: int | None = None,
) -> Path:
    directory = contributions / slug
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / INDEX_FILENAME
    path.write_text(
        json.dumps(
            {
                "schema_version": schema,
                "target": slug,
                "problem_id": f"problem-{slug}",
                "reward_target_id": REWARD_ID,
                "open": True,
                "contribution_count": len(entries) if count is None else count,
                "contributions": list(entries),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return path


def write_bundle(contributions: Path, slug: str, identifier: str, **overrides: Any) -> Path:
    payload: dict[str, Any] = {
        "artifacts": [
            {"name": "script.lean", "sha256": "0" * 64, "size": 12},
            {"name": "sources.md", "sha256": "1" * 64, "size": 12},
        ],
        "author": AUTHOR_B,
        "kind": "lemma",
        "mode": "either",
        "parents": [],
        "reward": {"coldkey": COLDKEY_OTHER, "hotkey": HOTKEY_B},
        "reward_target_id": REWARD_ID,
        "schema_version": 1,
        "target": slug,
        "tasks_commit": COMMIT,
        "title": "Straight from the working tree",
    }
    payload.update(overrides)
    directory = contributions / slug / identifier
    directory.mkdir(parents=True, exist_ok=True)
    (directory / METADATA_FILENAME).write_text(
        json.dumps(
            {
                "contribution_id": identifier,
                "payload": payload,
                "reward_signature": "0" * 128,
                "signature": "0" * 128,
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    return directory


@dataclass(frozen=True, slots=True)
class QueryRepo:
    root: Path

    @property
    def contributions(self) -> Path:
        return self.root / "contributions"

    @property
    def pool_root(self) -> Path:
        return self.root / "conjectures"

    def pool(self) -> Pool:
        return Pool.load(self.pool_root)

    def index(self, slug: str) -> Path:
        return self.contributions / slug / INDEX_FILENAME


def make_query_repo(tmp_path: Path) -> QueryRepo:
    pool_root = tmp_path / "conjectures"
    pool_root.mkdir()
    _write_pool(pool_root, (), QUERY_POOL_SLUGS)
    contributions = tmp_path / "contributions"
    contributions.mkdir()

    write_index(
        contributions,
        "demo-1",
        [
            query_entry(C1, "2026-08-01", declarations=[D1]),
            query_entry(
                C2,
                "2026-08-10",
                author=AUTHOR_B,
                coldkey=COLDKEY_OTHER,
                hotkey=HOTKEY_B,
                parents=[C1],
                declarations=[D2],
                tasks_commit=STALE_COMMIT,
                title="Building on the reduction",
            ),
        ],
    )
    write_index(contributions, "demo-2", [query_entry(C3, "2026-07-01", declarations=[D3])])
    # demo-3 has no directory at all: an empty target is the pool's row, not the tree's.
    write_index(
        contributions,
        "demo-4",
        [query_entry(C4, "2026-06-01", author=AUTHOR_C, hotkey="not-an-address")],
    )
    write_index(
        contributions,
        DRIFTED_SLUG,
        [query_entry(C5, "2026-05-01", author=AUTHOR_B, coldkey=None, hotkey=None)],
    )
    write_bundle(contributions, DRIFTED_SLUG, C5)
    write_bundle(contributions, DRIFTED_SLUG, UNINDEXED)
    return QueryRepo(root=tmp_path)


@pytest.fixture
def query_repo(tmp_path: Path) -> QueryRepo:
    return make_query_repo(tmp_path)
