from __future__ import annotations

from pathlib import Path

import pytest

from conjectures_contribution.cli import complete, config
from conjectures_contribution.cli.repo import ROOT_ENV
from conjectures_contribution.model import DRAFT_FILENAME

from .conftest import make_repo

SLUGS = ("erdos-100", "erdos-1060-parts-ii", "green-open-problem-3")


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv(ROOT_ENV, raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "home" / "contribution.toml"))


@pytest.fixture
def root(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = tmp_path / "repo"
    directory.mkdir()
    found = make_repo(directory, slugs=SLUGS).root
    monkeypatch.chdir(found)
    return found


@pytest.fixture
def outside(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = tmp_path / "elsewhere"
    directory.mkdir()
    monkeypatch.chdir(directory)
    return directory


@pytest.mark.usefixtures("outside")
def test_targets_outside_a_repository_are_empty() -> None:
    assert complete.targets("") == []


@pytest.mark.usefixtures("root")
def test_targets_strips_mode_suffixes_and_dedupes() -> None:
    assert complete.targets("") == sorted(SLUGS)


@pytest.mark.usefixtures("root")
def test_targets_matches_by_prefix() -> None:
    assert complete.targets("erdos-10") == ["erdos-100", "erdos-1060-parts-ii"]


# A prefix nobody types is more useful as a substring search than as no answer at all.
@pytest.mark.usefixtures("root")
def test_targets_falls_back_to_substring_when_no_prefix_matches() -> None:
    assert complete.targets("1060") == ["erdos-1060-parts-ii"]


@pytest.mark.usefixtures("root")
def test_targets_prefers_prefix_matches_over_substring_matches() -> None:
    assert complete.targets("green") == ["green-open-problem-3"]


def test_a_missing_pool_directory_yields_nothing_rather_than_raising(root: Path) -> None:
    for entry in sorted((root / "conjectures" / "pool" / "tier-1").iterdir()):
        for child in entry.iterdir():
            child.unlink()
        entry.rmdir()
    (root / "conjectures" / "pool" / "tier-1").rmdir()
    assert complete.targets("") == []


def test_drafts_offers_only_directories_holding_a_draft(root: Path) -> None:
    drafts = root / "drafts"
    (drafts / "erdos-100").mkdir(parents=True)
    (drafts / "erdos-100" / DRAFT_FILENAME).write_text("{}", encoding="utf-8")
    (drafts / "half-started").mkdir()
    (drafts / "README.md").write_text("notes", encoding="utf-8")
    assert complete.drafts("") == ["erdos-100"]


@pytest.mark.usefixtures("root")
def test_drafts_with_no_drafts_directory_is_empty() -> None:
    assert complete.drafts("") == []


def test_wallets_lists_wallet_directories(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    wallets = tmp_path / "wallets"
    for name in ("alpha", "beta"):
        (wallets / name).mkdir(parents=True)
    (wallets / "loose.txt").write_text("x", encoding="utf-8")
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_PATH", str(wallets))
    assert complete.wallets("") == ["alpha", "beta"]


def test_hotkeys_filters_out_public_keyfiles(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    hotkeys = tmp_path / "wallets" / "alpha" / "hotkeys"
    hotkeys.mkdir(parents=True)
    for name in ("miner", "minerpub.txt", "validator"):
        (hotkeys / name).write_text("{}", encoding="utf-8")
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_PATH", str(tmp_path / "wallets"))
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_NAME", "alpha")
    assert complete.hotkeys("") == ["miner", "validator"]


def test_hotkeys_for_a_wallet_that_does_not_exist_is_empty(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_PATH", str(tmp_path / "wallets"))
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_NAME", "missing")
    assert complete.hotkeys("") == []


# The narrow OSError handling below covers what actually goes wrong, but "never raises" has to
# be a property of the callback rather than an argument about its call graph.
@pytest.mark.parametrize("name", ["targets", "drafts", "wallets", "hotkeys"])
def test_no_callback_can_raise(name: str, monkeypatch: pytest.MonkeyPatch) -> None:
    def explode() -> list[str]:
        raise RuntimeError("the pool is on fire")

    for source in ("_slugs", "_draft_names", "_wallet_names", "_hotkey_names"):
        monkeypatch.setattr(complete, source, explode)
    assert getattr(complete, name)("") == []
