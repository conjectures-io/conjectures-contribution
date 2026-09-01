from __future__ import annotations

import random
from datetime import date

import pytest

from conjectures_contribution.model import PublicKey
from conjectures_contribution.query.corpus import Corpus, read_corpus
from conjectures_contribution.query.query import Query, QueryError, Request, run
from conjectures_contribution.query.values import Date, Source

from .conftest import (
    AUTHOR_A,
    AUTHOR_B,
    C1,
    C2,
    C3,
    C4,
    C5,
    DRIFTED_SLUG,
    HOTKEY_A,
    UNINDEXED,
    QueryRepo,
)

TODAY = date(2026, 9, 1)
EVERY_SOURCE = frozenset(Source)
TREE_ONLY = frozenset({Source.TREE})


def _request(**overrides: object) -> Request:
    return Request(today=TODAY, **overrides)  # type: ignore[arg-type]


def _corpus(repo: QueryRepo, sources: frozenset[Source] = EVERY_SOURCE) -> Corpus:
    return read_corpus(repo.root, repo.contributions, repo.pool, sources)


def _ids(repo: QueryRepo, **overrides: object) -> tuple[str, ...]:
    query = Query.build(_request(**overrides))
    result = run(_corpus(repo, query.sources), query)
    identity = query.grain.column(query.grain.identity)
    assert identity is not None
    return tuple(str(identity.get(row)) for row in result.rows)


def test_a_filter_binds_to_a_column_and_names_the_grains_that_have_it() -> None:
    with pytest.raises(QueryError) as caught:
        Query.build(_request(grain="targets", kind=("lemma",)))
    assert "--kind" in str(caught.value)
    assert "contributions" in str(caught.value)


def test_an_unknown_grain_lists_the_real_ones() -> None:
    with pytest.raises(QueryError) as caught:
        Query.build(_request(grain="declarations"))
    assert "contributions" in str(caught.value)


def test_an_unknown_sort_column_lists_the_alternatives() -> None:
    with pytest.raises(QueryError) as caught:
        Query.build(_request(grain="targets", sort="children"))
    assert "--sort" in str(caught.value)
    assert "contributions" in str(caught.value)


def test_is_refuses_a_column_that_is_not_boolean() -> None:
    with pytest.raises(QueryError) as caught:
        Query.build(_request(grain="contributions", is_=("title",)))
    assert "orphan" in str(caught.value)


def test_limit_zero_is_refused_and_points_at_all() -> None:
    with pytest.raises(QueryError) as caught:
        Query.build(_request(limit=0))
    assert "--all" in str(caught.value)


def test_a_date_that_is_neither_iso_nor_relative_is_refused() -> None:
    with pytest.raises(QueryError) as caught:
        Query.build(_request(grain="contributions", since="last tuesday"))
    assert "--since" in str(caught.value)


def test_filters_and_together(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="contributions", target=("demo-1",), author=(AUTHOR_B,)) == (C2,)


def test_repeated_values_of_one_flag_are_ored(query_repo: QueryRepo) -> None:
    found = _ids(query_repo, grain="contributions", target=("demo-2", DRIFTED_SLUG))
    assert set(found) == {C3, C5, UNINDEXED}


def test_a_filter_never_matches_a_hole_and_reports_the_decline(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="contributions", hotkey=(HOTKEY_A,)))
    result = run(_corpus(query_repo, query.sources), query)
    assert {str(row.id) for row in result.rows} == {C1, C3}
    assert result.declined == {"--hotkey": 1}


def test_an_absent_value_is_not_a_decline(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="contributions", is_=("rewarded",)))
    result = run(_corpus(query_repo, query.sources), query)
    assert C5 not in {str(row.id) for row in result.rows}
    assert result.declined == {}


def test_a_predicate_on_an_unloaded_source_declines_every_row(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="contributions", is_=("stale",)))
    result = run(_corpus(query_repo, TREE_ONLY), query)
    assert result.rows == ()
    assert result.declined == {"--is stale": 6}


def test_a_filter_is_membership_on_a_set_column(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="targets", author=(AUTHOR_A,)) == ("demo-1", "demo-2")


def test_an_author_prefix_is_enough(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="authors", author=(AUTHOR_B[:8],)) == (AUTHOR_B,)


def test_declares_globs_across_every_grain(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="contributions", declares=("*distinctDistances*",)) == (C3,)
    assert _ids(query_repo, grain="targets", declares=("*distinctDistances*",)) == ("demo-2",)


def test_match_tests_the_grains_name_column(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="contributions", match=("Building*",)) == (C2,)
    assert _ids(query_repo, grain="targets", match=("demo-4",)) == ("demo-4",)


def test_since_and_until_bind_to_the_time_column(query_repo: QueryRepo) -> None:
    found = _ids(query_repo, grain="contributions", since="2026-07-01", until="2026-08-01")
    assert set(found) == {C1, C3}


def test_a_relative_window_resolves_against_today(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="contributions", since="30d"))
    assert query.window == (Date("2026-08-02"), None)
    result = run(_corpus(query_repo, query.sources), query)
    assert {str(row.id) for row in result.rows} == {C2}


def test_mine_matches_on_authorship(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="contributions", mine=PublicKey(AUTHOR_A)) == (C1, C3)


def test_each_grain_sorts_by_its_own_default(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="targets")[0] == "demo-1"
    assert _ids(query_repo, grain="contributions")[:2] == (C2, C1)
    assert _ids(query_repo, grain="authors")[0] == AUTHOR_B


def test_holes_sort_last_in_both_directions(query_repo: QueryRepo) -> None:
    ascending = _ids(query_repo, grain="contributions", sort="added")
    descending = _ids(query_repo, grain="contributions", sort="added", descending=True)
    assert ascending[-1] == UNINDEXED
    assert descending[-1] == UNINDEXED


def test_the_order_is_total_under_a_shuffled_input(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="contributions", sort="kind"))
    corpus = _corpus(query_repo, query.sources)
    shuffled = list(corpus.contributions)
    random.Random(7).shuffle(shuffled)  # noqa: S311
    other = Corpus(
        targets=corpus.targets,
        contributions=tuple(shuffled),
        authors=corpus.authors,
        notes=corpus.notes,
    )
    assert [r.id for r in run(corpus, query).rows] == [r.id for r in run(other, query).rows]


def test_a_set_column_sorts_by_size(query_repo: QueryRepo) -> None:
    assert _ids(query_repo, grain="targets", sort="declarations", descending=True)[0] == "demo-1"


def test_limit_truncates_and_all_does_not(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="contributions", limit=2))
    result = run(_corpus(query_repo, query.sources), query)
    assert len(result.rows) == 2
    assert result.total == 6
    assert len(_ids(query_repo, grain="contributions", limit=None)) == 6


def test_the_pool_is_in_the_sources_only_when_a_column_needs_it() -> None:
    assert Source.POOL not in Query.build(_request(grain="contributions")).sources
    assert Source.POOL in Query.build(_request(grain="contributions", is_=("stale",))).sources
    assert Source.POOL in Query.build(_request(grain="targets")).sources
    assert Source.POOL in Query.build(_request(grain="contributions", as_json=True)).sources


def test_the_declines_name_the_flag_that_declined(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="contributions", declares=("*le_succ*",)))
    result = run(_corpus(query_repo, query.sources), query)
    assert result.declined == {"--declares": 1}
    assert [str(row.id) for row in result.rows] == [C1]


def test_a_query_with_no_filters_declines_nothing(query_repo: QueryRepo) -> None:
    query = Query.build(_request(grain="targets"))
    assert run(_corpus(query_repo, query.sources), query).declined == {}


@pytest.mark.parametrize("column", ["orphan", "unindexed"])
def test_is_and_not_are_complementary_on_a_total_column(query_repo: QueryRepo, column: str) -> None:
    yes = set(_ids(query_repo, grain="contributions", is_=(column,)))
    no = set(_ids(query_repo, grain="contributions", not_=(column,)))
    assert yes.isdisjoint(no)
    assert yes | no == {C1, C2, C3, C4, C5, UNINDEXED}
