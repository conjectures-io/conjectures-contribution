from __future__ import annotations

import json

import pytest

from conjectures_contribution.index import (
    INDEX_JSON,
    INDEX_MD,
    SCHEMA_VERSION,
    TASKS_REPOSITORY,
    build,
)

from .conftest import SLUG, Repo

LEAN = (
    "import Mathlib\n"
    "namespace Contribution.Demo\n"
    "theorem card_le (n : ℕ) : n ≤ n + 1 := Nat.le_succ n\n"
    "end Contribution.Demo\n"
)


def _build(repo: Repo, *, check: bool = False) -> tuple[str, ...]:
    return build(repo.root, repo.contributions, repo.root / "conjectures", repo.pool, check=check)


def _target_md(repo: Repo) -> str:
    return (repo.contributions / SLUG / INDEX_MD).read_text(encoding="utf-8")


@pytest.mark.usefixtures("published")
def test_indexes_are_written_then_stable(repo: Repo) -> None:
    assert _build(repo) != ()
    assert _build(repo) == ()
    assert _build(repo, check=True) == ()


@pytest.mark.usefixtures("published")
def test_a_stale_index_is_detected(repo: Repo) -> None:
    _build(repo)
    (repo.contributions / SLUG / INDEX_MD).write_text("tampered\n", encoding="utf-8")
    assert _build(repo, check=True) == (f"contributions/{SLUG}/{INDEX_MD}",)


def test_the_target_index_lists_the_contribution(repo: Repo) -> None:
    directory = repo.with_lean(LEAN)
    _build(repo)
    text = _target_md(repo)
    assert directory.name[:12] in text
    assert "Contribution.Demo.card_le" in text
    assert "A partial reduction" in text


def test_the_machine_readable_index_matches(repo: Repo) -> None:
    directory = repo.with_lean(LEAN)
    _build(repo)
    payload = json.loads((repo.contributions / SLUG / INDEX_JSON).read_text(encoding="utf-8"))
    assert payload["contribution_count"] == 1
    assert payload["open"] is True
    entry = payload["contributions"][0]
    assert entry["contribution_id"] == directory.name
    assert entry["declarations"] == ["Contribution.Demo.card_le"]
    assert entry["artifacts"] == ["script.lean", "sources.md"]


def test_the_index_entry_carries_the_author_and_the_pin(repo: Repo) -> None:
    directory = repo.with_lean(LEAN)
    _build(repo)
    payload = json.loads((repo.contributions / SLUG / INDEX_JSON).read_text(encoding="utf-8"))
    assert payload["schema_version"] == SCHEMA_VERSION == 2
    entry = payload["contributions"][0]
    assert entry["author"] == str(repo.key.public_key)
    assert entry["tasks_commit"] == repo.read(directory).payload.tasks_commit


@pytest.mark.usefixtures("published")
def test_problems_link_to_our_own_pool_not_upstream(repo: Repo) -> None:
    _build(repo)
    text = _target_md(repo)
    assert f"{TASKS_REPOSITORY}/tree/" in text
    assert f"pool/tier-1/{SLUG}-formalized" in text
    assert f"pool/tier-1/{SLUG}-counterexample" in text
    assert "google-deepmind" not in text


def test_an_empty_target_gets_a_stub(repo: Repo) -> None:
    _build(repo)
    text = _target_md(repo)
    assert "## Contributions (0)" in text
    assert "None yet" in text


@pytest.mark.usefixtures("published")
def test_the_root_index_counts_targets(repo: Repo) -> None:
    _build(repo)
    text = (repo.contributions / INDEX_MD).read_text(encoding="utf-8")
    assert "1 contribution(s) across 1 of 1 targets." in text


def test_a_pipe_in_a_title_does_not_break_the_table(repo: Repo) -> None:
    repo.promote(repo.draft(title="Bounds where a | b divides"))
    _build(repo)
    assert "a \\| b" in _target_md(repo)


@pytest.mark.usefixtures("published")
def test_a_target_that_left_the_pool_keeps_its_index(repo: Repo) -> None:
    stray = repo.contributions / "erdos-retired"
    stray.mkdir()
    _build(repo)
    text = (stray / INDEX_MD).read_text(encoding="utf-8")
    assert "no longer in the pinned pool" in text
