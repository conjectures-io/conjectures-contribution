from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.cli import config
from conjectures_contribution.cli.main import app
from conjectures_contribution.cli.repo import ROOT_ENV
from conjectures_contribution.index import build

from .conftest import DRIFTED_SLUG, QueryRepo, Repo, make_query_repo, make_repo, plain
from .test_index import LEAN

runner = CliRunner()


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv(ROOT_ENV, raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "home" / "contribution.toml"))


@pytest.fixture
def here(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> QueryRepo:
    directory = tmp_path / "repo"
    directory.mkdir()
    found = make_query_repo(directory)
    monkeypatch.chdir(found.root)
    return found


@pytest.fixture
def indexed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Repo:
    root = tmp_path / "repo"
    root.mkdir()
    repo = make_repo(root)
    repo.with_lean(LEAN)
    subprocess.run(["git", "init", "--quiet"], cwd=root, check=True)  # noqa: S607
    subprocess.run(["git", "add", "."], cwd=root, check=True)  # noqa: S607
    subprocess.run(
        ["git", "-c", "user.name=T", "-c", "user.email=t@x.invalid", "commit", "-qm", "in"],  # noqa: S607
        cwd=root,
        check=True,
    )
    build(root, repo.contributions, root / "conjectures", repo.pool)
    monkeypatch.chdir(root)
    return repo


@pytest.mark.skipif(shutil.which("git") is None, reason="git is not installed")
@pytest.mark.usefixtures("indexed")
def test_a_freshly_indexed_corpus_is_clean() -> None:
    result = runner.invoke(app, ["doctor"])
    assert result.exit_code == 0, plain(result.output)
    assert "ok" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_a_stale_index_is_named_with_its_remedy() -> None:
    result = runner.invoke(app, ["doctor"])
    assert result.exit_code == 3
    assert "contrib-admin index" in plain(result.output)


def test_a_corrupt_index_is_named(here: QueryRepo) -> None:
    here.index("demo-2").write_text("{ not json", encoding="utf-8")
    result = runner.invoke(app, ["doctor"])
    assert result.exit_code == 3
    assert "contributions/demo-2/index.json" in plain(result.output)


def test_a_disagreeing_contribution_count_is_reported(here: QueryRepo) -> None:
    raw = json.loads(here.index("demo-1").read_text(encoding="utf-8"))
    raw["contribution_count"] = 99
    here.index("demo-1").write_text(json.dumps(raw), encoding="utf-8")
    result = runner.invoke(app, ["doctor"])
    assert result.exit_code == 3
    assert "99" in plain(result.output)
    assert "demo-1" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_a_target_outside_the_pool_is_reported() -> None:
    result = runner.invoke(app, ["doctor"])
    assert DRIFTED_SLUG in plain(result.output)


@pytest.mark.usefixtures("here")
def test_an_unindexed_contribution_is_reported() -> None:
    text = plain(runner.invoke(app, ["doctor"]).output)
    assert "not in any index" in text


@pytest.mark.usefixtures("here")
def test_a_field_hole_ls_would_have_hidden_is_named() -> None:
    text = plain(runner.invoke(app, ["doctor"]).output)
    assert "hotkey" in text


# Scoping is the whole design: `ls` stays quiet, `doctor` says it.
def test_what_ls_scopes_away_doctor_still_reports(here: QueryRepo) -> None:
    here.index("demo-2").write_text("{ not json", encoding="utf-8")
    quiet = runner.invoke(app, ["ls", "contributions", "--target", "demo-1"])
    assert quiet.exit_code == 0
    assert "demo-2" not in plain(quiet.output)
    assert "demo-2" in plain(runner.invoke(app, ["doctor"]).output)


def test_every_finding_kind_is_reported_in_one_run(here: QueryRepo) -> None:
    here.index("demo-2").write_text("{ not json", encoding="utf-8")
    text = plain(runner.invoke(app, ["doctor"]).output)
    for headline in ("indexes:", "sources:", "tree:", "fields:"):
        assert headline in text
