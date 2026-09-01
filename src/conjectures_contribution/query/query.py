"""Turning a request into a query, and a query into rows.

`Query.build` is where every refusal lives: an unknown grain, a filter on a grain that
lacks the column it binds to, a `--sort` nobody can compute, an unparseable date. Past it
an invalid query is unrepresentable, so `select` and `order` are total and their tests
need no error cases.

A filter binds to a **column**, and therefore applies to exactly the grains that have it.
The flag-by-grain matrix is derived here, never maintained.
"""

from __future__ import annotations

import fnmatch
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import date
from enum import StrEnum
from typing import Any, Self, assert_never, cast

from ..model import SchemaError
from .columns import Column, ColumnType
from .corpus import Corpus
from .grains import DEFAULT_GRAIN, GRAINS, Grain
from .notes import Note
from .values import AuthorKey, Date, Source, Unavailable

DEFAULT_LIMIT = 20


class QueryError(RuntimeError):
    pass


class Test(StrEnum):
    EXACT = "exact"
    PREFIX = "prefix"
    GLOB = "glob"
    SINCE = "since"
    UNTIL = "until"
    TRUE = "true"
    FALSE = "false"


class Bind(StrEnum):
    NAMED = "named"
    NAME_COLUMN = "name"
    TIME_COLUMN = "time"


@dataclass(frozen=True, slots=True, kw_only=True)
class Request:
    """Raw strings off the command line. Nothing here has been validated yet."""

    today: date
    grain: str = DEFAULT_GRAIN
    target: tuple[str, ...] = ()
    author: tuple[str, ...] = ()
    coldkey: tuple[str, ...] = ()
    hotkey: tuple[str, ...] = ()
    kind: tuple[str, ...] = ()
    mode: tuple[str, ...] = ()
    match: tuple[str, ...] = ()
    declares: tuple[str, ...] = ()
    since: str | None = None
    until: str | None = None
    is_: tuple[str, ...] = ()
    not_: tuple[str, ...] = ()
    mine: AuthorKey | None = None
    sort: str | None = None
    descending: bool = False
    limit: int | None = DEFAULT_LIMIT
    as_json: bool = False


@dataclass(frozen=True, slots=True)
class FilterSpec:
    flag: str
    bind: Bind
    columns: tuple[str, ...]
    test: Test
    read: Callable[[Request], tuple[str, ...]]


# A plural column is the aggregate of the singular one on another grain, so binding to
# both is what makes `--author` mean "signed it" on contributions and "is active here" on
# targets without either being a special case.
FILTERS: tuple[FilterSpec, ...] = (
    FilterSpec("--target", Bind.NAMED, ("target", "targets"), Test.EXACT, lambda r: r.target),
    FilterSpec("--author", Bind.NAMED, ("author", "authors"), Test.PREFIX, lambda r: r.author),
    FilterSpec(
        "--mine",
        Bind.NAMED,
        ("author", "authors"),
        Test.EXACT,
        lambda r: () if r.mine is None else (str(r.mine),),
    ),
    FilterSpec("--coldkey", Bind.NAMED, ("coldkey", "coldkeys"), Test.PREFIX, lambda r: r.coldkey),
    FilterSpec("--hotkey", Bind.NAMED, ("hotkey", "hotkeys"), Test.PREFIX, lambda r: r.hotkey),
    FilterSpec("--kind", Bind.NAMED, ("kind",), Test.EXACT, lambda r: r.kind),
    FilterSpec("--mode", Bind.NAMED, ("mode", "modes"), Test.EXACT, lambda r: r.mode),
    FilterSpec("--declares", Bind.NAMED, ("declarations",), Test.GLOB, lambda r: r.declares),
    FilterSpec("--match", Bind.NAME_COLUMN, (), Test.GLOB, lambda r: r.match),
    FilterSpec(
        "--since",
        Bind.TIME_COLUMN,
        (),
        Test.SINCE,
        lambda r: () if r.since is None else (r.since,),
    ),
    FilterSpec(
        "--until",
        Bind.TIME_COLUMN,
        (),
        Test.UNTIL,
        lambda r: () if r.until is None else (r.until,),
    ),
)


@dataclass(frozen=True, slots=True)
class Predicate:
    label: str
    column: Column[Any]
    test: Callable[[object], bool | None]


@dataclass(frozen=True, slots=True)
class Query:
    grain: Grain[Any]
    predicates: tuple[Predicate, ...]
    projection: tuple[Column[Any], ...]
    sort: Column[Any]
    identity: Column[Any]
    descending: bool
    limit: int | None
    window: tuple[Date | None, Date | None]
    as_json: bool
    sources: frozenset[Source] = field(default=frozenset())

    @classmethod
    def build(cls, request: Request) -> Self:
        grain = GRAINS.get(request.grain)
        if grain is None:
            raise QueryError(f"unknown grain {request.grain!r}; try {_listed(tuple(GRAINS))}")

        predicates = [*_value_predicates(grain, request), *_boolean_predicates(grain, request)]
        sort = _sort_column(grain, request)
        projection = _projection(grain, request)
        limit = _limit(request)

        identity = grain.column(grain.identity)
        if identity is None:  # pragma: no cover - the grain invariants forbid it
            raise QueryError(f"{grain.name}: identity column {grain.identity!r} is missing")

        return cls(
            grain=grain,
            predicates=tuple(predicates),
            projection=projection,
            sort=sort,
            identity=identity,
            descending=request.descending or (request.sort is None and grain.descending),
            limit=limit,
            window=(
                _window(request.since, "--since", request),
                _window(request.until, "--until", request),
            ),
            as_json=request.as_json,
            sources=frozenset(
                {
                    *grain.sources,
                    *(c.source for c in projection),
                    *(p.column.source for p in predicates),
                    sort.source,
                }
            ),
        )


@dataclass(frozen=True, slots=True)
class Result:
    rows: tuple[Any, ...]
    total: int
    # Rows a filter could neither accept nor reject, by flag. Reported, never silent: an
    # empty table read as "nothing is stale" is the failure this whole design guards.
    declined: Mapping[str, int]


def run(corpus: Corpus, query: Query) -> Result:
    kept, declined = _select(query.grain.load(corpus), query.predicates)
    ordered = _order(kept, query)
    return Result(
        rows=ordered if query.limit is None else ordered[: query.limit],
        total=len(ordered),
        declined=declined,
    )


def _select(
    rows: Sequence[Any], predicates: Sequence[Predicate]
) -> tuple[tuple[Any, ...], Mapping[str, int]]:
    declined: dict[str, int] = {}
    kept: list[Any] = []
    for row in rows:
        verdicts = [(p, p.test(p.column.get(row))) for p in predicates]
        if any(verdict is False for _, verdict in verdicts):
            continue
        unknown = [p for p, verdict in verdicts if verdict is None]
        if unknown:
            for predicate in unknown:
                declined[predicate.label] = declined.get(predicate.label, 0) + 1
            continue
        kept.append(row)
    return tuple(kept), declined


# Total in both directions: identity first so ties are stable, then holes to the end
# whichever way the visible values run.
def _order(rows: Sequence[Any], query: Query) -> tuple[Any, ...]:
    present: list[tuple[str | int, Any]] = []
    absent: list[Any] = []
    for row in sorted(rows, key=lambda r: str(query.identity.get(r))):
        key = _sortable(query.sort, row)
        if key is None:
            absent.append(row)
        else:
            present.append((key, row))
    present.sort(key=lambda pair: pair[0], reverse=query.descending)
    return tuple([row for _, row in present] + absent)


def _sortable(column: Column[Any], row: Any) -> str | int | None:
    value = column.get(row)
    if value is None or isinstance(value, Unavailable):
        return None
    if column.type is ColumnType.STR:
        return cast("str", value)
    if column.type is ColumnType.INT:
        return cast("int", value)
    if column.type is ColumnType.DATE:
        return str(cast("Date", value))
    if column.type is ColumnType.BOOL:
        return int(cast("bool", value))
    if column.type is ColumnType.SET:
        return len(cast("tuple[object, ...]", value))
    assert_never(column.type)


def _value_predicates(grain: Grain[Any], request: Request) -> list[Predicate]:
    built: list[Predicate] = []
    for spec in FILTERS:
        operands = spec.read(request)
        if not operands:
            continue
        column = _bound(grain, spec)
        if column is None:
            raise QueryError(
                f"{spec.flag} does not apply to {grain.name}; "
                f"it filters {_listed(_grains_with(spec.columns))}"
            )
        built.append(_predicate(spec, column, operands, request))
    return built


def _boolean_predicates(grain: Grain[Any], request: Request) -> list[Predicate]:
    built: list[Predicate] = []
    for flag, names, expected in (("--is", request.is_, True), ("--not", request.not_, False)):
        for name in names:
            column = grain.column(name)
            if column is None or column.type is not ColumnType.BOOL:
                raise QueryError(
                    f"{flag}: {name!r} is not a boolean column on {grain.name}; "
                    f"try {_listed(grain.booleans())}"
                )
            built.append(
                Predicate(
                    label=f"{flag} {name}",
                    column=column,
                    test=_boolean_test(expected),
                )
            )
    return built


def _bound(grain: Grain[Any], spec: FilterSpec) -> Column[Any] | None:
    if spec.bind is Bind.NAME_COLUMN:
        return grain.column(grain.name_column)
    if spec.bind is Bind.TIME_COLUMN:
        return grain.column(grain.time_column)
    if spec.bind is Bind.NAMED:
        return next((c for c in map(grain.column, spec.columns) if c is not None), None)
    assert_never(spec.bind)


def _predicate(
    spec: FilterSpec, column: Column[Any], operands: tuple[str, ...], request: Request
) -> Predicate:
    if spec.test in {Test.SINCE, Test.UNTIL}:
        boundary = _resolve(operands[0], spec.flag, request.today)
        return Predicate(spec.flag, column, _date_test(spec.test, boundary))
    return Predicate(spec.flag, column, _text_test(column.type, spec.test, operands))


# A hole matches nothing and is reported; an absent value matches nothing and is not. The
# difference is the whole point of carrying both.
def _text_test(
    kind: ColumnType, test: Test, operands: tuple[str, ...]
) -> Callable[[object], bool | None]:
    def evaluate(value: object) -> bool | None:
        if isinstance(value, Unavailable):
            return None
        if value is None:
            return False
        return any(
            _compare(test, candidate, o) for candidate in _candidates(kind, value) for o in operands
        )

    return evaluate


def _date_test(test: Test, boundary: Date) -> Callable[[object], bool | None]:
    def evaluate(value: object) -> bool | None:
        if isinstance(value, Unavailable):
            return None
        if value is None:
            return False
        moment = cast("Date", value)
        return moment >= boundary if test is Test.SINCE else moment <= boundary

    return evaluate


def _boolean_test(expected: bool) -> Callable[[object], bool | None]:
    def evaluate(value: object) -> bool | None:
        if isinstance(value, Unavailable):
            return None
        if value is None:
            return False
        return bool(value) is expected

    return evaluate


def _candidates(kind: ColumnType, value: object) -> tuple[str, ...]:
    if kind is ColumnType.SET:
        return tuple(str(item) for item in cast("tuple[object, ...]", value))
    return (str(value),)


def _compare(test: Test, candidate: str, operand: str) -> bool:
    if test is Test.EXACT:
        return candidate == operand
    if test is Test.PREFIX:
        return candidate.startswith(operand)
    if test is Test.GLOB:
        return fnmatch.fnmatchcase(candidate, operand)
    raise QueryError(f"{test}: not a text comparison")


def _sort_column(grain: Grain[Any], request: Request) -> Column[Any]:
    name = request.sort or grain.default_sort
    column = grain.column(name)
    if column is None:
        raise QueryError(
            f"--sort: no column {name!r} on {grain.name}; "
            f"{grain.name} has {_listed(grain.names())}"
            + (
                f", and {name!r} is on {_listed(_grains_with((name,)))}"
                if _grains_with((name,))
                else ""
            )
        )
    return column


def _projection(grain: Grain[Any], request: Request) -> tuple[Column[Any], ...]:
    if request.as_json:
        return grain.columns
    shown = [grain.column(name) for name in grain.table]
    return tuple(c for c in shown if c is not None)


def _limit(request: Request) -> int | None:
    if request.limit is None:
        return None
    if request.limit < 1:
        raise QueryError("--limit must be at least 1; use --all for every row")
    return request.limit


def _window(text: str | None, flag: str, request: Request) -> Date | None:
    return None if text is None else _resolve(text, flag, request.today)


def _resolve(text: str, flag: str, today: date) -> Date:
    try:
        return Date.resolve(text, today)
    except SchemaError as exc:
        raise QueryError(f"{flag}: {exc}; expected 2026-08-01 or a window like 30d") from None


def _grains_with(names: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(
        grain.name
        for grain in GRAINS.values()
        if any(grain.column(name) is not None for name in names)
    )


def _listed(names: Sequence[str]) -> str:
    return ", ".join(names)


# A row we failed to build only matters if it could have appeared in this answer. Where the
# query filters on something the failure hid from us, assume it was relevant: claiming a
# complete answer we cannot verify is the one direction that lies.
def relevant(notes: Sequence[Note], query: Query) -> tuple[Note, ...]:
    return tuple(note for note in notes if note.slug is None or admits(query, note.slug))


def admits(query: Query, slug: str) -> bool:
    for predicate in query.predicates:
        if predicate.column.name not in {"target", "targets"}:
            continue
        value: object = slug if predicate.column.type is ColumnType.STR else (slug,)
        if predicate.test(value) is not True:
            return False
    return True
