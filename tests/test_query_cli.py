from __future__ import annotations

import json
from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.cli import config
from conjectures_contribution.cli.main import app
from conjectures_contribution.cli.repo import ROOT_ENV

from .conftest import AUTHOR_A, C1, QueryRepo, make_query_repo, plain, write_index

runner = CliRunner()


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv(ROOT_ENV, raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "home" / "contribution.toml"))
    monkeypatch.setenv("CONJECTURES_KEY", str(tmp_path / "home" / "ed25519.key"))


@pytest.fixture
def here(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> QueryRepo:
    directory = tmp_path / "repo"
    directory.mkdir()
    found = make_query_repo(directory)
    monkeypatch.chdir(found.root)
    return found


@pytest.mark.usefixtures("here")
def test_ls_defaults_to_the_targets_table() -> None:
    result = runner.invoke(app, ["ls"])
    assert result.exit_code == 0
    assert "demo-1" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_an_unknown_grain_is_refused() -> None:
    result = runner.invoke(app, ["ls", "declarations"])
    assert result.exit_code == 2
    assert "contributions" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_a_filter_on_a_grain_that_lacks_it_names_the_grains_that_have_it() -> None:
    result = runner.invoke(app, ["ls", "targets", "--kind", "lemma"])
    assert result.exit_code == 2
    assert "contributions" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_an_unknown_boolean_is_refused_with_the_real_ones() -> None:
    result = runner.invoke(app, ["ls", "targets", "--is", "open"])
    assert result.exit_code == 2
    assert "in_pool" in plain(result.output)


def test_an_unreadable_source_answers_and_says_so(here: QueryRepo) -> None:
    here.index("demo-2").write_text("{ not json", encoding="utf-8")
    result = runner.invoke(app, ["ls"])
    assert result.exit_code == 3
    assert "demo-1" in plain(result.output)
    assert "contrib doctor" in plain(result.output)


def test_an_unreadable_source_is_silent_when_the_query_excludes_it(here: QueryRepo) -> None:
    here.index("demo-2").write_text("{ not json", encoding="utf-8")
    result = runner.invoke(app, ["ls", "contributions", "--target", "demo-1"])
    assert result.exit_code == 0
    assert "contrib doctor" not in plain(result.output)


@pytest.mark.usefixtures("here")
def test_zero_rows_is_exit_zero_and_an_empty_array() -> None:
    result = runner.invoke(app, ["ls", "contributions", "--target", "nothing", "--json"])
    assert result.exit_code == 0
    assert json.loads(plain(result.stdout)) == []


@pytest.mark.usefixtures("here")
def test_a_decline_is_reported_without_failing() -> None:
    result = runner.invoke(app, ["ls", "contributions", "--declares", "*le_succ*"])
    assert result.exit_code == 0
    assert "--declares" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_a_resolved_window_is_echoed() -> None:
    result = runner.invoke(app, ["ls", "contributions", "--since", "30d"])
    assert result.exit_code == 0
    assert "window" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_mine_without_a_cached_key_names_the_command_that_fixes_it() -> None:
    result = runner.invoke(app, ["ls", "contributions", "--mine"])
    assert result.exit_code == 2
    assert "contrib key" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_mine_reads_the_cached_key_and_never_the_private_one() -> None:
    config.write(config.ConfigKey.AUTHOR_KEY, AUTHOR_A)
    result = runner.invoke(app, ["ls", "contributions", "--mine", "--json"])
    assert result.exit_code == 0
    assert {row["author"] for row in json.loads(plain(result.stdout))} == {AUTHOR_A}


@pytest.mark.usefixtures("here")
def test_key_show_caches_the_public_half_for_mine() -> None:
    generated = runner.invoke(app, ["key", "generate"])
    assert generated.exit_code == 0
    assert config.author_key() == plain(generated.stdout).splitlines()[1]


@pytest.mark.usefixtures("here")
def test_key_show_with_an_explicit_path_does_not_repoint_mine(tmp_path: Path) -> None:
    runner.invoke(app, ["key", "generate"])
    cached = config.author_key()
    other = tmp_path / "other.key"
    assert runner.invoke(app, ["key", "generate", "--path", str(other)]).exit_code == 0
    assert config.author_key() == cached


@pytest.mark.usefixtures("here")
def test_limit_truncates_and_all_does_not() -> None:
    limited = runner.invoke(app, ["ls", "contributions", "--limit", "1", "--json"])
    assert len(json.loads(plain(limited.stdout))) == 1
    every = runner.invoke(app, ["ls", "contributions", "--all", "--json"])
    assert len(json.loads(plain(every.stdout))) == 6


@pytest.mark.usefixtures("here")
def test_limit_zero_points_at_all() -> None:
    result = runner.invoke(app, ["ls", "--limit", "0"])
    assert result.exit_code == 2
    assert "--all" in plain(result.output)


@pytest.mark.usefixtures("here")
def test_a_json_pipe_is_never_polluted_by_diagnostics() -> None:
    result = runner.invoke(app, ["ls", "contributions", "--declares", "*le_succ*", "--json"])
    assert [row["id"] for row in json.loads(plain(result.stdout))] == [C1]


@pytest.mark.usefixtures("here")
def test_help_names_every_filter() -> None:
    text = plain(runner.invoke(app, ["ls", "--help"]).output)
    for flag in ("--target", "--author", "--mine", "--coldkey", "--hotkey", "--kind", "--mode"):
        assert flag in text
    for flag in ("--since", "--until", "--match", "--declares", "--is", "--not"):
        assert flag in text
    for flag in ("--sort", "--desc", "--limit", "--all", "--json"):
        assert flag in text


def test_every_target_unreadable_is_a_refusal(here: QueryRepo) -> None:
    for slug in ("demo-1", "demo-2", "demo-4", "demo-5"):
        here.index(slug).write_text("{ not json", encoding="utf-8")
    write_index(here.contributions, "demo-3", [])
    here.index("demo-3").write_text("{ not json", encoding="utf-8")
    result = runner.invoke(app, ["ls", "contributions"])
    assert result.exit_code == 2
    assert "contrib doctor" in plain(result.output)


def test_an_index_written_before_the_schema_bump_degrades_rather_than_vanishing(
    here: QueryRepo,
) -> None:
    raw = json.loads(here.index("demo-1").read_text(encoding="utf-8"))
    raw["schema_version"] = 1
    for entry in raw["contributions"]:
        del entry["author"]
    here.index("demo-1").write_text(json.dumps(raw), encoding="utf-8")

    result = runner.invoke(app, ["ls", "contributions", "--target", "demo-1"])
    assert result.exit_code == 3
    assert "contrib-admin index" in plain(result.output)
    assert "could not be read" not in plain(result.output)
    assert runner.invoke(app, ["ls", "authors"]).exit_code == 3
