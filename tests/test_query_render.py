from __future__ import annotations

import json
from datetime import date
from pathlib import Path
from typing import Any

import pytest

from conjectures_contribution.query import GRAINS
from conjectures_contribution.query.corpus import read_corpus
from conjectures_contribution.query.query import Query, Request, run
from conjectures_contribution.query.render import render
from conjectures_contribution.query.values import Source

from .conftest import C4, UNINDEXED, QueryRepo

TODAY = date(2026, 9, 1)
GOLDEN = Path(__file__).parent / "golden" / "query-columns.json"


def _rendered(repo: QueryRepo, **overrides: Any) -> str:
    query = Query.build(Request(today=TODAY, **overrides))
    corpus = read_corpus(repo.root, repo.contributions, repo.pool, query.sources)
    return render(run(corpus, query).rows, query)


def _json(repo: QueryRepo, **overrides: Any) -> list[dict[str, Any]]:
    parsed: list[dict[str, Any]] = json.loads(_rendered(repo, as_json=True, **overrides))
    return parsed


def test_the_json_field_names_and_types_are_the_compatibility_promise() -> None:
    declared = {
        name: {column.name: str(column.type) for column in grain.columns}
        for name, grain in GRAINS.items()
    }
    promised = json.loads(GOLDEN.read_text(encoding="utf-8"))
    assert declared == promised, (
        "--json fields are added, never renamed or retyped. Regenerating this snapshot is "
        "the moment to ask whether the promise is being broken."
    )


def test_json_of_zero_rows_is_an_empty_array(query_repo: QueryRepo) -> None:
    assert _rendered(query_repo, as_json=True, target=("nothing-here",)) == "[]"


def test_a_table_of_zero_rows_is_empty(query_repo: QueryRepo) -> None:
    assert _rendered(query_repo, target=("nothing-here",)) == ""


def test_json_carries_full_ids_and_the_table_shortens_them(query_repo: QueryRepo) -> None:
    rows = _json(query_repo, grain="contributions")
    assert any(len(str(row["id"])) == 64 for row in rows)
    table = _rendered(query_repo, grain="contributions")
    assert UNINDEXED not in table
    assert UNINDEXED[:12] in table


def test_a_hole_renders_as_a_question_mark_and_as_null(query_repo: QueryRepo) -> None:
    assert _json(query_repo, grain="contributions", target=("demo-4",))[0]["hotkey"] is None
    # demo-5 holds the unindexed directory, whose date and declarations await a reindex.
    assert "?" in _rendered(query_repo, grain="contributions", target=("demo-5",))


def test_an_absent_value_renders_as_a_dash_and_as_null(query_repo: QueryRepo) -> None:
    empty = _json(query_repo, grain="targets", target=("demo-3",))[0]
    assert empty["first_added"] is None
    drifted = _json(query_repo, grain="targets", target=("demo-5",))[0]
    assert drifted["modes"] is None
    assert "—" in _rendered(query_repo, grain="targets", target=("demo-3",))
    assert "—" in _rendered(query_repo, grain="targets", target=("demo-5",))


def test_a_set_is_a_count_in_the_table_and_a_list_in_json(query_repo: QueryRepo) -> None:
    rows = _json(query_repo, grain="targets", target=("demo-1",))
    assert rows[0]["declarations"] == [
        "Contribution.Demo.card_le",
        "Contribution.Demo.le_succ",
    ]
    lines = _rendered(query_repo, grain="targets", target=("demo-1",)).splitlines()
    assert lines[1].split()[4] == "2"


def test_a_date_renders_as_its_iso_day(query_repo: QueryRepo) -> None:
    assert _json(query_repo, grain="contributions", target=("demo-4",))[0]["added"] == "2026-06-01"


def test_a_boolean_reads_as_yes_or_no(query_repo: QueryRepo) -> None:
    table = _rendered(query_repo, grain="contributions", target=("demo-5",))
    assert "yes" in table
    assert "no" in table


def test_the_table_columns_align(query_repo: QueryRepo) -> None:
    lines = _rendered(query_repo, grain="targets").splitlines()
    starts = {line.index("demo-") for line in lines[1:]}
    assert starts == {0}
    assert len({len(line.rstrip()) for line in lines}) > 0
    header = lines[0].split()
    assert header[0] == "target"


def test_the_output_is_byte_identical_across_runs(query_repo: QueryRepo) -> None:
    first = _rendered(query_repo, grain="contributions", as_json=True, limit=None)
    second = _rendered(query_repo, grain="contributions", as_json=True, limit=None)
    assert first == second


@pytest.mark.parametrize("grain", sorted(GRAINS))
def test_every_grain_renders_both_ways(query_repo: QueryRepo, grain: str) -> None:
    assert _rendered(query_repo, grain=grain).strip() != ""
    assert json.loads(_rendered(query_repo, grain=grain, as_json=True)) != []


def test_json_holds_exactly_the_declared_columns(query_repo: QueryRepo) -> None:
    for name, grain in GRAINS.items():
        for row in _json(query_repo, grain=name):
            assert list(row) == list(grain.names())


def test_the_sources_a_render_needs_do_not_depend_on_the_rows(query_repo: QueryRepo) -> None:
    query = Query.build(Request(today=TODAY, grain="contributions", as_json=True))
    assert Source.POOL in query.sources
    assert C4 in _rendered(query_repo, grain="contributions", as_json=True)


def test_an_aggregate_nobody_can_read_shows_as_unknown_not_as_zero(
    query_repo: QueryRepo,
) -> None:
    rows = _json(query_repo, grain="targets", target=("demo-5",))
    assert rows[0]["declarations"] is None
    table = _rendered(query_repo, grain="targets", target=("demo-5",))
    assert "?" in table
