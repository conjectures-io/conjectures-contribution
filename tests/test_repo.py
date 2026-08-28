from __future__ import annotations

from pathlib import Path

import pytest

from conjectures_contribution.cli import config
from conjectures_contribution.cli.repo import (
    ROOT_ENV,
    Workspace,
    WorkspaceError,
    open_workspace,
)

from .conftest import make_repo

MARKER = "allowlist.json"


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv(ROOT_ENV, raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "home" / "contribution.toml"))


@pytest.fixture
def root(tmp_path: Path) -> Path:
    directory = tmp_path / "repo"
    directory.mkdir()
    return make_repo(directory).root


@pytest.fixture
def outside(tmp_path: Path) -> Path:
    directory = tmp_path / "elsewhere"
    directory.mkdir()
    return directory


def test_the_walk_up_finds_the_root(root: Path) -> None:
    assert Workspace.discover(root).root == root
    assert Workspace.discover(root).source is config.Source.WALK


def test_the_walk_up_works_from_a_subdirectory(root: Path) -> None:
    nested = root / "contributions" / "demo-1"
    nested.mkdir(parents=True)
    assert Workspace.discover(nested).root == root


def test_no_repository_anywhere_names_the_marker_and_the_fix(outside: Path) -> None:
    with pytest.raises(WorkspaceError, match=MARKER) as caught:
        Workspace.discover(outside)
    assert "contrib repo pin" in str(caught.value)


def test_the_flag_wins(root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    other = make_repo(outside).root
    monkeypatch.setenv(ROOT_ENV, str(other))
    found = Workspace.discover(root, override=root)
    assert (found.root, found.source) == (root, config.Source.FLAG)


# Today any override at all is accepted and fails much later inside Pool.load, with a message
# about the pool rather than about the path the user actually got wrong.
def test_the_flag_must_name_a_repository(root: Path, outside: Path) -> None:
    with pytest.raises(WorkspaceError, match=MARKER):
        Workspace.discover(root, override=outside)


def test_the_env_override_must_name_a_repository(
    root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv(ROOT_ENV, str(outside))
    with pytest.raises(WorkspaceError, match=MARKER):
        Workspace.discover(root)


def test_env_beats_the_walk_up(root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    other = make_repo(outside).root
    monkeypatch.setenv(ROOT_ENV, str(other))
    found = Workspace.discover(root)
    assert (found.root, found.source) == (other, config.Source.ENV)


# The mv case: a checkout that moved is still found by anyone working inside it, whatever a
# stale pin says.
def test_the_walk_up_beats_the_pin(root: Path, outside: Path) -> None:
    other = make_repo(outside).root
    config.write(config.ConfigKey.REPO_PATH, str(other))
    found = Workspace.discover(root)
    assert (found.root, found.source) == (root, config.Source.WALK)


def test_the_pin_is_used_outside_any_repository(root: Path, outside: Path) -> None:
    config.write(config.ConfigKey.REPO_PATH, str(root))
    found = Workspace.discover(outside)
    assert (found.root, found.source) == (root, config.Source.PIN)


def test_a_stale_pin_says_how_to_re_pin(outside: Path, tmp_path: Path) -> None:
    config.write(config.ConfigKey.REPO_PATH, str(tmp_path / "moved-away"))
    with pytest.raises(WorkspaceError, match="pinned repository") as caught:
        Workspace.discover(outside)
    assert "contrib repo pin" in str(caught.value)


def test_discover_quietly_returns_none_instead_of_raising(outside: Path) -> None:
    assert Workspace.discover_quietly(outside) is None


def test_discover_quietly_finds_a_root(root: Path) -> None:
    found = Workspace.discover_quietly(root)
    assert found is not None
    assert found.root == root


def test_working_inside_the_tree_says_nothing(
    root: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.chdir(root)
    assert open_workspace().root == root
    assert capsys.readouterr() == ("", "")


def test_a_subdirectory_is_still_inside_the_tree(
    root: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    nested = root / "drafts"
    nested.mkdir()
    monkeypatch.chdir(nested)
    open_workspace()
    assert capsys.readouterr().err == ""


def test_working_outside_the_tree_names_the_repository_on_stderr(
    root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    config.write(config.ConfigKey.REPO_PATH, str(root))
    monkeypatch.chdir(outside)
    assert open_workspace().root == root
    captured = capsys.readouterr()
    # stdout stays machine-readable, so `contrib check --json` is unaffected by the note.
    assert captured.out == ""
    assert str(root) in captured.err
    assert captured.err.startswith("note: using repository at ")


def test_the_note_names_the_source(
    root: Path, outside: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    config.write(config.ConfigKey.REPO_PATH, str(root))
    monkeypatch.chdir(outside)
    open_workspace()
    assert "pinned" in capsys.readouterr().err
