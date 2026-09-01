from __future__ import annotations

from collections import defaultdict
from typing import cast

import pytest

from conjectures_contribution.model import (
    ContributionId,
    Kind,
    Mode,
    PublicKey,
    Ss58Address,
    TargetSlug,
)
from conjectures_contribution.query import GRAINS
from conjectures_contribution.query.columns import ColumnType
from conjectures_contribution.query.corpus import Corpus
from conjectures_contribution.query.rows import AuthorRow, ContributionRow, TargetRow
from conjectures_contribution.query.values import Commit, Date, Unavailable

AUTHOR = PublicKey("a" * 64)
COLDKEY = Ss58Address("5" + "C" * 47)
HOTKEY = Ss58Address("5" + "D" * 47)
IDENTIFIER = ContributionId("b" * 64)


def _corpus() -> Corpus:
    contribution = ContributionRow(
        id=IDENTIFIER,
        target=TargetSlug("demo-1"),
        title="A partial reduction",
        author=AUTHOR,
        coldkey=COLDKEY,
        hotkey=Unavailable("hotkey: not an ss58 address"),
        kind=Kind.LEMMA,
        mode=Mode.EITHER,
        added=Date("2026-08-01"),
        declarations=("Contribution.Demo.le_succ",),
        parents=(),
        artifacts=("script.lean", "sources.md"),
        tasks_commit=Commit("0" * 40),
        children=0,
        stale=False,
        unindexed=False,
    )
    target = TargetRow(
        target=TargetSlug("demo-1"),
        in_pool=True,
        modes=(Mode.FORMALIZED, Mode.COUNTEREXAMPLE),
        contributions=1,
        authors=(AUTHOR,),
        coldkeys=(COLDKEY,),
        declarations=("Contribution.Demo.le_succ",),
        first_added=Date("2026-08-01"),
        last_added=Date("2026-08-01"),
    )
    author = AuthorRow(
        author=AUTHOR,
        contributions=1,
        targets=(TargetSlug("demo-1"),),
        declarations=("Contribution.Demo.le_succ",),
        coldkeys=(COLDKEY,),
        hotkeys=(HOTKEY,),
        children=0,
        first_seen=Date("2026-08-01"),
        last_seen=Date("2026-08-01"),
        shared_coldkey=False,
    )
    return Corpus(targets=(target,), contributions=(contribution,), authors=(author,), notes=())


def test_a_grain_never_declares_a_column_name_twice() -> None:
    for grain in GRAINS.values():
        names = [column.name for column in grain.columns]
        assert len(names) == len(set(names)), grain.name


def test_a_column_name_carries_one_type_across_every_grain() -> None:
    types: defaultdict[str, set[ColumnType]] = defaultdict(set)
    for grain in GRAINS.values():
        for column in grain.columns:
            types[column.name].add(column.type)
    disagreeing = {name: kinds for name, kinds in types.items() if len(kinds) > 1}
    assert disagreeing == {}


def test_the_three_named_columns_exist_and_are_typed() -> None:
    for grain in GRAINS.values():
        declared = {column.name: column.type for column in grain.columns}
        assert grain.default_sort in declared, grain.name
        assert grain.identity in declared, grain.name
        assert declared[grain.name_column] is ColumnType.STR, grain.name
        assert declared[grain.time_column] is ColumnType.DATE, grain.name


def test_the_table_projection_names_real_columns() -> None:
    for grain in GRAINS.values():
        assert set(grain.table) <= set(grain.names()), grain.name
        assert grain.identity in grain.table, grain.name


def test_the_is_vocabulary_is_exactly_the_boolean_columns() -> None:
    for grain in GRAINS.values():
        booleans = {c.name for c in grain.columns if c.type is ColumnType.BOOL}
        assert set(grain.booleans()) == booleans, grain.name


@pytest.mark.parametrize("name", sorted(GRAINS))
def test_every_column_computes_a_value_of_its_declared_type(name: str) -> None:
    grain = GRAINS[name]
    expected = {
        ColumnType.STR: str,
        ColumnType.INT: int,
        ColumnType.DATE: Date,
        ColumnType.BOOL: bool,
        ColumnType.SET: tuple,
    }
    for row in grain.load(_corpus()):
        for column in grain.columns:
            value = column.get(row)
            if value is None or isinstance(value, Unavailable):
                continue
            assert isinstance(value, expected[column.type]), f"{grain.name}.{column.name}"
            if column.type is ColumnType.SET:
                elements = cast("tuple[object, ...]", value)
                assert all(isinstance(item, str) for item in elements)


def test_every_grain_loads_the_rows_it_names() -> None:
    corpus = _corpus()
    assert len(GRAINS["targets"].load(corpus)) == 1
    assert len(GRAINS["contributions"].load(corpus)) == 1
    assert len(GRAINS["authors"].load(corpus)) == 1
