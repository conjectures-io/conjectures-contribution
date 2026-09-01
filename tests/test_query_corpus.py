from __future__ import annotations

import json
from dataclasses import fields

import pytest

from conjectures_contribution.index import build
from conjectures_contribution.model import Kind, Mode, PublicKey
from conjectures_contribution.pool import Pool
from conjectures_contribution.query.corpus import Corpus, read_corpus
from conjectures_contribution.query.rows import AuthorRow, ContributionRow, TargetRow
from conjectures_contribution.query.values import Commit, Date, Source, Unavailable

from .conftest import (
    AUTHOR_A,
    AUTHOR_B,
    AUTHOR_C,
    C1,
    C2,
    C4,
    C5,
    COLDKEY_OTHER,
    COLDKEY_SHARED,
    COMMIT,
    D1,
    DRIFTED_SLUG,
    UNINDEXED,
    QueryRepo,
    Repo,
    query_entry,
    write_index,
)
from .test_index import LEAN

EVERY_SOURCE = frozenset(Source)
TREE_ONLY = frozenset({Source.TREE})


def _corpus(repo: QueryRepo, sources: frozenset[Source] = EVERY_SOURCE) -> Corpus:
    return read_corpus(repo.root, repo.contributions, repo.pool, sources)


def _contributions(corpus: Corpus) -> dict[str, ContributionRow]:
    return {str(row.id): row for row in corpus.contributions}


def _targets(corpus: Corpus) -> dict[str, TargetRow]:
    return {str(row.target): row for row in corpus.targets}


def _authors(corpus: Corpus) -> dict[str, AuthorRow]:
    return {str(row.author): row for row in corpus.authors}


def _holes(row: AuthorRow | ContributionRow | TargetRow) -> set[str]:
    return {f.name for f in fields(row) if isinstance(getattr(row, f.name), Unavailable)}


def test_an_empty_target_is_a_row_and_not_a_note(query_repo: QueryRepo) -> None:
    corpus = _corpus(query_repo)
    assert corpus.notes == ()
    assert _targets(corpus)["demo-3"].contributions == 0


def test_targets_are_the_union_of_the_pool_and_the_tree(query_repo: QueryRepo) -> None:
    targets = _targets(_corpus(query_repo))
    assert set(targets) == {"demo-1", "demo-2", "demo-3", "demo-4", DRIFTED_SLUG}
    assert targets["demo-1"].in_pool is True
    assert targets[DRIFTED_SLUG].in_pool is False


def test_an_index_that_is_not_utf8_costs_its_row_and_warns(query_repo: QueryRepo) -> None:
    query_repo.index("demo-2").write_bytes(b"\xff\xfe not utf-8")
    corpus = _corpus(query_repo)
    assert "demo-2" not in _targets(corpus)
    (note,) = corpus.notes
    assert note.slug == "demo-2"
    assert "UTF-8" in note.message


def test_invalid_json_costs_its_row_and_warns(query_repo: QueryRepo) -> None:
    query_repo.index("demo-2").write_text("{ not json", encoding="utf-8")
    corpus = _corpus(query_repo)
    assert "demo-2" not in _targets(corpus)
    (note,) = corpus.notes
    assert note.source.endswith("demo-2/index.json")


def test_a_newer_schema_costs_its_row_and_names_the_version(query_repo: QueryRepo) -> None:
    write_index(query_repo.contributions, "demo-2", [], schema=99)
    corpus = _corpus(query_repo)
    assert "demo-2" not in _targets(corpus)
    (note,) = corpus.notes
    assert "99" in note.message


def test_an_older_schema_degrades_the_fields_it_lacks(query_repo: QueryRepo) -> None:
    entry = query_entry(C1, "2026-08-01", declarations=[D1])
    del entry["author"]
    del entry["tasks_commit"]
    write_index(query_repo.contributions, "demo-1", [entry], schema=1)
    corpus = _corpus(query_repo)
    row = _contributions(corpus)[C1]
    assert _holes(row) == {"author", "tasks_commit", "stale"}
    assert row.title == "A partial reduction"
    (note,) = corpus.notes
    assert "contrib-admin index" in note.message


def test_an_unindexed_directory_yields_a_row_with_exactly_two_holes(
    query_repo: QueryRepo,
) -> None:
    row = _contributions(_corpus(query_repo))[UNINDEXED]
    assert row.unindexed is True
    assert _holes(row) == {"declarations", "added"}
    assert row.title == "Straight from the working tree"


def test_an_indexed_directory_on_disk_is_not_unindexed(query_repo: QueryRepo) -> None:
    assert _contributions(_corpus(query_repo))[C5].unindexed is False


def test_children_invert_declared_parents(query_repo: QueryRepo) -> None:
    rows = _contributions(_corpus(query_repo))
    assert rows[C1].children == 1
    assert rows[C2].children == 0


def test_stale_compares_the_pin_against_the_pool(query_repo: QueryRepo) -> None:
    rows = _contributions(_corpus(query_repo))
    assert rows[C1].stale is False
    assert rows[C2].stale is True


def test_a_malformed_field_is_a_hole_and_keeps_its_row(query_repo: QueryRepo) -> None:
    row = _contributions(_corpus(query_repo))[C4]
    assert _holes(row) == {"hotkey"}
    assert row.kind is Kind.LEMMA
    assert row.mode is Mode.EITHER


def test_an_absent_reward_is_not_a_hole(query_repo: QueryRepo) -> None:
    row = _contributions(_corpus(query_repo))[C5]
    assert row.coldkey is None
    assert _holes(row) == set()


def test_the_pool_is_never_read_when_no_column_needs_it(query_repo: QueryRepo) -> None:
    def refuse() -> Pool:
        raise AssertionError("the pool was loaded for a query that does not need it")

    corpus = read_corpus(query_repo.root, query_repo.contributions, refuse, TREE_ONLY)
    row = _contributions(corpus)[C1]
    assert isinstance(row.stale, Unavailable)
    assert _targets(corpus)["demo-1"].in_pool == Unavailable("pool: not loaded")


def test_shared_coldkeys_are_flagged_on_every_author_sharing_one(query_repo: QueryRepo) -> None:
    authors = _authors(_corpus(query_repo))
    shared = authors[AUTHOR_A].coldkeys
    assert not isinstance(shared, Unavailable)
    assert tuple(str(key) for key in shared) == (COLDKEY_SHARED,)
    assert authors[AUTHOR_A].shared_coldkey is True
    assert authors[AUTHOR_C].shared_coldkey is True
    assert authors[AUTHOR_B].shared_coldkey is False


def test_authors_aggregate_across_targets(query_repo: QueryRepo) -> None:
    row = _authors(_corpus(query_repo))[AUTHOR_A]
    assert row.contributions == 2
    assert tuple(str(t) for t in row.targets) == ("demo-1", "demo-2")
    assert row.children == 1
    assert row.first_seen == Date("2026-07-01")
    assert row.last_seen == Date("2026-08-01")


def test_target_aggregates_come_from_the_rows_not_the_stored_count(
    query_repo: QueryRepo,
) -> None:
    write_index(
        query_repo.contributions,
        "demo-2",
        [query_entry(C1, "2026-07-01", declarations=[D1])],
        count=99,
    )
    row = _targets(_corpus(query_repo))["demo-2"]
    assert row.contributions == 1
    assert row.declarations == (D1,)
    assert row.last_added == Date("2026-07-01")


def test_the_writer_and_the_reader_agree(repo: Repo) -> None:
    directory = repo.with_lean(LEAN)
    build(repo.root, repo.contributions, repo.root / "conjectures", repo.pool)
    corpus = read_corpus(repo.root, repo.contributions, lambda: repo.pool, EVERY_SOURCE)
    row = _contributions(corpus)[directory.name]
    published = repo.read(directory).payload
    assert corpus.notes == ()
    assert row.title == published.title
    assert row.author == published.author
    assert row.tasks_commit == Commit(published.tasks_commit)
    assert row.declarations == ("Contribution.Demo.card_le",)


@pytest.mark.parametrize("slug", ["demo-1", "demo-4"])
def test_every_index_the_fixture_writes_parses(query_repo: QueryRepo, slug: str) -> None:
    raw = json.loads(query_repo.index(slug).read_text(encoding="utf-8"))
    assert raw["schema_version"] == 2


# The count of a set aggregate is a claim. Building it out of the readable rows only would
# understate it silently, which is the failure the hole machinery exists to prevent.
def test_an_unreadable_author_holes_the_target_aggregate_instead_of_counting_zero(
    query_repo: QueryRepo,
) -> None:
    entry = query_entry(C1, "2026-08-01", declarations=[D1])
    del entry["author"]
    write_index(query_repo.contributions, "demo-1", [entry], schema=1)
    row = _targets(_corpus(query_repo))["demo-1"]
    assert isinstance(row.authors, Unavailable)
    assert row.contributions == 1


def test_one_unreadable_author_among_several_still_holes_the_aggregate(
    query_repo: QueryRepo,
) -> None:
    broken = query_entry(C2, "2026-08-10", author="not-a-key")
    write_index(
        query_repo.contributions,
        "demo-1",
        [query_entry(C1, "2026-08-01"), broken],
    )
    assert isinstance(_targets(_corpus(query_repo))["demo-1"].authors, Unavailable)


def test_an_unindexed_contribution_holes_the_declaration_aggregate(
    query_repo: QueryRepo,
) -> None:
    row = _targets(_corpus(query_repo))[DRIFTED_SLUG]
    assert isinstance(row.declarations, Unavailable)


def test_an_opted_out_reward_does_not_hole_the_coldkey_aggregate(query_repo: QueryRepo) -> None:
    # AUTHOR_B has one contribution with no reward at all; the rest still aggregate.
    coldkeys = _authors(_corpus(query_repo))[AUTHOR_B].coldkeys
    assert not isinstance(coldkeys, Unavailable)
    assert tuple(str(key) for key in coldkeys) == (COLDKEY_OTHER,)


# The index is a summary of the signed records, so a field it predates is not lost — it is
# one directory down. Recovering it costs a read only while the index is behind.
def test_a_behind_schema_index_recovers_missing_fields_from_the_signed_record(
    query_repo: QueryRepo,
) -> None:
    entry = query_entry(C5, "2026-05-01", coldkey=None, hotkey=None)
    del entry["author"]
    del entry["tasks_commit"]
    write_index(query_repo.contributions, DRIFTED_SLUG, [entry], schema=1)
    corpus = _corpus(query_repo)
    row = _contributions(corpus)[C5]
    assert row.author == PublicKey(AUTHOR_B)
    assert row.tasks_commit == Commit(COMMIT)
    assert _holes(row) == set()
    assert corpus.notes == ()


def test_the_index_wins_over_the_bundle_for_a_field_it_does_carry(
    query_repo: QueryRepo,
) -> None:
    entry = query_entry(C5, "2026-05-01", coldkey=None, hotkey=None)
    del entry["author"]
    write_index(query_repo.contributions, DRIFTED_SLUG, [entry], schema=1)
    # write_bundle gives C5 a reward; the index says it opted out, and the index is the
    # summary of record for the keys it actually carries.
    assert _contributions(_corpus(query_repo))[C5].coldkey is None


def test_a_malformed_index_field_is_not_repaired_from_the_bundle(query_repo: QueryRepo) -> None:
    entry = query_entry(C5, "2026-05-01", hotkey="not-an-address")
    del entry["author"]
    write_index(query_repo.contributions, DRIFTED_SLUG, [entry], schema=1)
    assert _holes(_contributions(_corpus(query_repo))[C5]) == {"hotkey"}


def test_a_behind_schema_index_with_no_signed_record_still_holes_and_says_so(
    query_repo: QueryRepo,
) -> None:
    entry = query_entry(C1, "2026-08-01")
    del entry["author"]
    write_index(query_repo.contributions, "demo-1", [entry], schema=1)
    corpus = _corpus(query_repo)
    assert isinstance(_contributions(corpus)[C1].author, Unavailable)
    (note,) = corpus.notes
    assert "contrib-admin index" in note.message


def test_a_target_carries_the_reward_destinations_of_its_contributions(
    query_repo: QueryRepo,
) -> None:
    row = _targets(_corpus(query_repo))["demo-1"]
    assert not isinstance(row.coldkeys, Unavailable)
    assert tuple(str(key) for key in row.coldkeys) == (COLDKEY_SHARED, COLDKEY_OTHER)
