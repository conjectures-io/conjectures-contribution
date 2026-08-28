from __future__ import annotations

from importlib.metadata import version
from pathlib import Path
from typing import Any

import pytest
from typer.main import get_command
from typer.testing import CliRunner

from conjectures_contribution.cli import config
from conjectures_contribution.cli.main import app
from conjectures_contribution.cli.repo import ROOT_ENV
from conjectures_contribution.model import DRAFT_FILENAME

from .conftest import make_repo, plain

runner = CliRunner()


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv(ROOT_ENV, raising=False)
    for name in ("WALLET_NAME", "WALLET_HOTKEY", "WALLET_PATH"):
        monkeypatch.delenv(f"{config.ENV_PREFIX}{name}", raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "home" / "contribution.toml"))


@pytest.fixture
def root(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = tmp_path / "repo"
    directory.mkdir()
    found = make_repo(directory).root
    monkeypatch.chdir(found)
    return found


@pytest.fixture
def outside(tmp_path: Path) -> Path:
    directory = tmp_path / "elsewhere"
    directory.mkdir()
    return directory


def test_repo_pin_with_no_argument_pins_the_discovered_root(root: Path) -> None:
    result = runner.invoke(app, ["repo", "pin"])
    assert result.exit_code == 0
    assert config.pinned_repo() == str(root)


@pytest.mark.usefixtures("root")
def test_repo_pin_refuses_a_directory_that_is_not_a_repository(outside: Path) -> None:
    result = runner.invoke(app, ["repo", "pin", str(outside)])
    assert result.exit_code == 2
    assert config.pinned_repo() is None


@pytest.mark.usefixtures("root")
def test_repo_unpin_on_an_absent_pin_is_not_an_error() -> None:
    assert runner.invoke(app, ["repo", "unpin"]).exit_code == 0


@pytest.mark.usefixtures("root")
def test_repo_unpin_removes_the_pin() -> None:
    runner.invoke(app, ["repo", "pin"])
    assert runner.invoke(app, ["repo", "unpin"]).exit_code == 0
    assert config.pinned_repo() is None


def test_repo_show_names_the_root_and_its_source(root: Path) -> None:
    result = runner.invoke(app, ["repo", "show"])
    assert result.exit_code == 0
    assert str(root) in result.output
    assert "walk-up" in result.output


def test_repo_show_outside_any_repository_fails_cleanly(
    outside: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(outside)
    result = runner.invoke(app, ["repo", "show"])
    assert result.exit_code == 2
    assert "contrib repo pin" in result.output


@pytest.mark.usefixtures("root")
def test_config_set_then_show() -> None:
    assert runner.invoke(app, ["config", "set", "wallet_name", "mine"]).exit_code == 0
    result = runner.invoke(app, ["config", "show"])
    assert "mine" in result.output
    assert "file" in result.output


@pytest.mark.usefixtures("root")
def test_config_set_rejects_a_key_we_do_not_own() -> None:
    result = runner.invoke(app, ["config", "set", "api_base_url", "x"])
    assert result.exit_code == 2


@pytest.mark.usefixtures("root")
def test_config_unset_returns_to_the_default() -> None:
    runner.invoke(app, ["config", "set", "wallet_name", "mine"])
    assert runner.invoke(app, ["config", "unset", "wallet_name"]).exit_code == 0
    assert config.resolve().name.source is config.Source.DEFAULT


@pytest.mark.usefixtures("root")
def test_config_show_reports_the_file_it_reads() -> None:
    result = runner.invoke(app, ["config", "show"])
    assert str(config.config_file()) in result.output


# click's parameter objects are what actually carry the completion callbacks, and typer does
# not re-export their types; Any keeps the walk honest rather than papering it with ignores.
def _completions(path: tuple[str, ...], param: str, incomplete: str) -> list[str]:
    command: Any = get_command(app)
    for name in path:
        command = command.commands[name]
    found: Any = next(p for p in command.params if p.name == param)
    return [str(item.value) for item in found.shell_complete(None, incomplete)]


def test_the_root_app_offers_to_install_completion() -> None:
    assert "--install-completion" in plain(runner.invoke(app, ["--help"]).output)


@pytest.mark.usefixtures("root")
def test_new_completes_target_slugs_from_the_pool() -> None:
    assert _completions(("new",), "target", "") == ["demo-1"]


def test_promote_completes_drafts_not_pool_targets(root: Path) -> None:
    drafts = root / "drafts" / "demo-1"
    drafts.mkdir(parents=True)
    (drafts / DRAFT_FILENAME).write_text("{}", encoding="utf-8")
    (root / "drafts" / "not-a-draft").mkdir()
    assert _completions(("promote",), "target", "") == ["demo-1"]


@pytest.mark.usefixtures("root")
def test_promote_completes_nothing_when_there_are_no_drafts() -> None:
    assert _completions(("promote",), "target", "") == []


def test_wallet_names_complete(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    (tmp_path / "wallets" / "alpha").mkdir(parents=True)
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_PATH", str(tmp_path / "wallets"))
    for path in (("promote",), ("wallet", "show")):
        assert _completions(path, "wallet", "") == ["alpha"]


def test_hotkey_names_complete(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    (tmp_path / "wallets" / "alpha" / "hotkeys").mkdir(parents=True)
    (tmp_path / "wallets" / "alpha" / "hotkeys" / "miner").write_text("{}", encoding="utf-8")
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_PATH", str(tmp_path / "wallets"))
    monkeypatch.setenv(f"{config.ENV_PREFIX}WALLET_NAME", "alpha")
    for path in (("promote",), ("wallet", "show")):
        assert _completions(path, "hotkey", "") == ["miner"]


def test_version_names_the_distribution_and_its_version() -> None:
    result = runner.invoke(app, ["--version"])
    assert result.exit_code == 0
    expected = f"conjectures-contribution {version('conjectures-contribution')}"
    assert result.output.strip() == expected


def test_repo_flag_overrides_discovery_from_outside(
    root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(outside)
    result = runner.invoke(app, ["--repo", str(root), "check"])
    assert result.exit_code == 0


def test_repo_flag_applies_to_repo_show(
    root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(outside)
    result = runner.invoke(app, ["--repo", str(root), "repo", "show"])
    assert result.exit_code == 0
    assert f"{root}  (flag)" in result.output


def test_repo_flag_can_be_pinned(
    root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.chdir(outside)
    result = runner.invoke(app, ["--repo", str(root), "repo", "pin"])
    assert result.exit_code == 0
    assert config.pinned_repo() == str(root)


@pytest.mark.usefixtures("root")
def test_repo_flag_must_name_a_repository(outside: Path) -> None:
    result = runner.invoke(app, ["--repo", str(outside), "check"])
    assert result.exit_code == 2
    assert "allowlist.json" in result.output
