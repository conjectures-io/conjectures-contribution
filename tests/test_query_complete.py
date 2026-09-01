from __future__ import annotations

import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast

import pytest
import typer

from conjectures_contribution.cli import complete, config
from conjectures_contribution.cli.repo import ROOT_ENV

from .conftest import AUTHOR_A, COLDKEY_SHARED, D1, QueryRepo, make_query_repo


@dataclass(frozen=True, slots=True)
class _Context:
    params: dict[str, Any]
    args: tuple[str, ...] = ()


def _ctx(grain: str | None, typed: tuple[str, ...] = ()) -> typer.Context:
    return cast("typer.Context", _Context({"grain": grain}, typed))


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
def outside(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = tmp_path / "elsewhere"
    directory.mkdir()
    monkeypatch.chdir(directory)
    return directory


def test_grains_complete_from_the_table() -> None:
    assert complete.grains("") == ["authors", "contributions", "targets"]


def test_sort_offers_the_typed_grains_columns() -> None:
    assert "children" in complete.sort_columns(_ctx(None, ("contributions",)), "")
    assert "children" in complete.sort_columns(_ctx("contributions"), "")
    assert "children" not in complete.sort_columns(_ctx("targets"), "")
    assert "in_pool" in complete.sort_columns(_ctx("targets"), "")


# `contrib ls --sort <TAB>` puts the flag before the grain, so a superset beats silence.
def test_sort_falls_back_to_every_column_when_the_grain_is_not_typed_yet() -> None:
    offered = complete.sort_columns(_ctx(None), "")
    assert "children" in offered
    assert "in_pool" in offered


def test_sort_survives_a_grain_that_does_not_exist() -> None:
    assert complete.sort_columns(_ctx("declarations"), "in_") == ["in_pool"]


def test_is_offers_only_boolean_columns() -> None:
    offered = complete.boolean_columns(_ctx("contributions"), "")
    assert "orphan" in offered
    assert "title" not in offered


def test_windows_offers_relative_forms() -> None:
    assert "30d" in complete.windows("")
    assert complete.windows("6") == ["6m"]


@pytest.mark.usefixtures("here")
def test_declarations_come_from_the_corpus() -> None:
    assert complete.declarations("le_succ") == [D1]


@pytest.mark.usefixtures("here")
def test_keys_come_from_the_corpus() -> None:
    assert AUTHOR_A in complete.corpus_authors("")
    assert COLDKEY_SHARED in complete.corpus_coldkeys("")


# `complete.hotkeys` is a wallet hotkey name; the corpus one is a reward address.
def test_the_corpus_key_callbacks_do_not_shadow_the_wallet_ones() -> None:
    assert complete.hotkeys is not complete.corpus_hotkeys


@pytest.mark.usefixtures("outside")
@pytest.mark.parametrize(
    "name", ["declarations", "corpus_authors", "corpus_coldkeys", "corpus_hotkeys"]
)
def test_no_callback_raises_outside_a_repository(name: str) -> None:
    callback: Any = getattr(complete, name)
    assert callback("") == []


# Click reports the default grain during value completion, so the typed word has to come
# from the leftover args or `--sort` would offer another grain's columns outright.
def test_the_typed_grain_wins_over_the_default_in_the_context() -> None:
    assert "children" not in complete.sort_columns(_ctx("targets", ("targets",)), "")


def test_the_shell_protocol_answers_with_the_grains_columns(here: QueryRepo) -> None:
    environment = {
        **os.environ,
        "_CONTRIB_COMPLETE": "complete_bash",
        "COMP_WORDS": "contrib ls contributions --sort ",
        "COMP_CWORD": "4",
    }
    result = subprocess.run(  # noqa: S603
        [str(Path(sys.executable).parent / "contrib")],
        cwd=here.root,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert "children" in result.stdout
