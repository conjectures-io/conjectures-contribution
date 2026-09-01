"""The three grains, and the only module that knows all three row types.

A grain composes: it holds a loader, a column tuple, and the names of the columns that
answer "what is this row called", "when did it happen", and "which one is it". Adding a
fourth grain adds a value here, not a class anywhere.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Generic, TypeVar

from .columns import Column, ColumnType, R
from .corpus import Corpus
from .rows import AuthorRow, ContributionRow, TargetRow
from .values import Field, Source, Unavailable, mapped

_KEY_WIDTH = 12


@dataclass(frozen=True, slots=True)
class Grain(Generic[R]):
    name: str
    columns: tuple[Column[R], ...]
    default_sort: str
    descending: bool
    name_column: str
    time_column: str
    identity: str
    # What the aligned table shows. `--json` emits every column; a terminal cannot.
    table: tuple[str, ...]
    # Loaded whatever the query projects: the rows themselves cannot be built without them.
    sources: frozenset[Source]
    load: Callable[[Corpus], tuple[R, ...]]

    def column(self, name: str) -> Column[R] | None:
        return next((c for c in self.columns if c.name == name), None)

    def names(self) -> tuple[str, ...]:
        return tuple(c.name for c in self.columns)

    def booleans(self) -> tuple[str, ...]:
        return tuple(c.name for c in self.columns if c.type is ColumnType.BOOL)


_T = TypeVar("_T")


def _text(value: Field[_T | None]) -> Field[str | None]:
    return mapped(value, str)


def _elements(value: Field[tuple[Any, ...] | None]) -> Field[tuple[str, ...] | None]:
    return mapped(value, lambda items: tuple(str(item) for item in items))


# A contribution with no reward opted out; one whose reward would not parse is a hole.
def _rewarded(row: ContributionRow) -> Field[bool]:
    if isinstance(row.coldkey, Unavailable):
        return row.coldkey
    return row.coldkey is not None


TARGET_COLUMNS: tuple[Column[TargetRow], ...] = (
    Column(
        name="target",
        type=ColumnType.STR,
        get=lambda r: str(r.target),
        help="Target slug.",
    ),
    Column(
        name="in_pool",
        type=ColumnType.BOOL,
        get=lambda r: r.in_pool,
        help="The slug is still in the pinned pool. Not the same as accepting work.",
        source=Source.POOL,
    ),
    Column(
        name="empty",
        type=ColumnType.BOOL,
        get=lambda r: r.contributions == 0,
        help="Nothing has been contributed here.",
    ),
    Column(
        name="modes",
        type=ColumnType.SET,
        get=lambda r: _elements(r.modes),
        help="Task bundles the pool offers for this target.",
        source=Source.POOL,
    ),
    Column(
        name="contributions",
        type=ColumnType.INT,
        get=lambda r: r.contributions,
        help="Contributions on this target, counted, never read from contribution_count.",
    ),
    Column(
        name="authors",
        type=ColumnType.SET,
        get=lambda r: _elements(r.authors),
        help="Author keys active on this target.",
    ),
    Column(
        name="coldkeys",
        type=ColumnType.SET,
        get=lambda r: _elements(r.coldkeys),
        help="Reward coldkeys the contributions here name.",
    ),
    Column(
        name="declarations",
        type=ColumnType.SET,
        get=lambda r: _elements(r.declarations),
        help="Lean declarations contributed here.",
    ),
    Column(
        name="first_added",
        type=ColumnType.DATE,
        get=lambda r: r.first_added,
        help="Date of the earliest contribution.",
    ),
    Column(
        name="last_added",
        type=ColumnType.DATE,
        get=lambda r: r.last_added,
        help="Date of the most recent contribution.",
    ),
)


CONTRIBUTION_COLUMNS: tuple[Column[ContributionRow], ...] = (
    Column(
        name="id",
        type=ColumnType.STR,
        get=lambda r: str(r.id),
        help="Contribution id.",
        width=_KEY_WIDTH,
    ),
    Column(
        name="target",
        type=ColumnType.STR,
        get=lambda r: str(r.target),
        help="Target slug.",
    ),
    Column(name="title", type=ColumnType.STR, get=lambda r: r.title, help="Declared title."),
    Column(
        name="author",
        type=ColumnType.STR,
        get=lambda r: _text(r.author),
        help="Ed25519 key that signed the contribution.",
        width=_KEY_WIDTH,
    ),
    Column(
        name="coldkey",
        type=ColumnType.STR,
        get=lambda r: _text(r.coldkey),
        help="Reward coldkey, or absent when the contributor opted out.",
        width=_KEY_WIDTH,
    ),
    Column(
        name="hotkey",
        type=ColumnType.STR,
        get=lambda r: _text(r.hotkey),
        help="Reward hotkey, or absent when the contributor opted out.",
        width=_KEY_WIDTH,
    ),
    Column(name="kind", type=ColumnType.STR, get=lambda r: _text(r.kind), help="Declared kind."),
    Column(name="mode", type=ColumnType.STR, get=lambda r: _text(r.mode), help="Declared mode."),
    Column(
        name="added",
        type=ColumnType.DATE,
        get=lambda r: r.added,
        help="Date the directory first appeared in git.",
    ),
    Column(
        name="declarations",
        type=ColumnType.SET,
        get=lambda r: _elements(r.declarations),
        help="Lean declarations this contribution provides.",
    ),
    Column(
        name="parents",
        type=ColumnType.INT,
        get=lambda r: mapped(r.parents, len),
        help="Declared parents. Declared, not derived.",
    ),
    Column(
        name="children",
        type=ColumnType.INT,
        get=lambda r: r.children,
        help="Contributions declaring this one as a parent. Declared, not derived.",
    ),
    Column(
        name="artifacts",
        type=ColumnType.INT,
        get=lambda r: mapped(r.artifacts, len),
        help="Files in the contribution.",
    ),
    Column(
        name="tasks_commit",
        type=ColumnType.STR,
        get=lambda r: _text(r.tasks_commit),
        help="Pool commit the contribution was built against.",
        width=_KEY_WIDTH,
    ),
    Column(
        name="orphan",
        type=ColumnType.BOOL,
        get=lambda r: r.children == 0,
        help="Nobody has declared this contribution as a parent.",
    ),
    Column(
        name="stale",
        type=ColumnType.BOOL,
        get=lambda r: r.stale,
        help="Pinned to a commit other than the pool's.",
        source=Source.POOL,
    ),
    Column(
        name="rewarded",
        type=ColumnType.BOOL,
        get=_rewarded,
        help="Carries a reward destination.",
    ),
    Column(
        name="unindexed",
        type=ColumnType.BOOL,
        get=lambda r: r.unindexed,
        help="On disk but absent from the target index; run contrib-admin index.",
    ),
)


AUTHOR_COLUMNS: tuple[Column[AuthorRow], ...] = (
    Column(
        name="author",
        type=ColumnType.STR,
        get=lambda r: str(r.author),
        help="Ed25519 public key.",
        width=_KEY_WIDTH,
    ),
    Column(
        name="contributions",
        type=ColumnType.INT,
        get=lambda r: r.contributions,
        help="Contributions signed by this key.",
    ),
    Column(
        name="targets",
        type=ColumnType.SET,
        get=lambda r: _elements(r.targets),
        help="Targets this key is active on.",
    ),
    Column(
        name="declarations",
        type=ColumnType.SET,
        get=lambda r: _elements(r.declarations),
        help="Lean declarations contributed by this key.",
    ),
    Column(
        name="coldkeys",
        type=ColumnType.SET,
        get=lambda r: _elements(r.coldkeys),
        help="Distinct reward coldkeys this key has used.",
    ),
    Column(
        name="hotkeys",
        type=ColumnType.SET,
        get=lambda r: _elements(r.hotkeys),
        help="Distinct reward hotkeys this key has used.",
    ),
    Column(
        name="children",
        type=ColumnType.INT,
        get=lambda r: r.children,
        help="Times this key's work was declared as a parent.",
    ),
    Column(
        name="first_seen",
        type=ColumnType.DATE,
        get=lambda r: r.first_seen,
        help="Date of this key's earliest contribution.",
    ),
    Column(
        name="last_seen",
        type=ColumnType.DATE,
        get=lambda r: r.last_seen,
        help="Date of this key's most recent contribution.",
    ),
    Column(
        name="shared_coldkey",
        type=ColumnType.BOOL,
        get=lambda r: r.shared_coldkey,
        help="Another author key pays into one of the same coldkeys.",
    ),
)


TARGETS: Grain[TargetRow] = Grain(
    name="targets",
    columns=TARGET_COLUMNS,
    default_sort="target",
    descending=False,
    name_column="target",
    time_column="last_added",
    identity="target",
    table=(
        "target",
        "in_pool",
        "contributions",
        "authors",
        "coldkeys",
        "declarations",
        "modes",
        "first_added",
        "last_added",
    ),
    # The pool is the authoritative target list; the tree only adds drift and counts.
    sources=frozenset({Source.POOL, Source.TREE}),
    load=lambda c: c.targets,
)

CONTRIBUTIONS: Grain[ContributionRow] = Grain(
    name="contributions",
    columns=CONTRIBUTION_COLUMNS,
    default_sort="added",
    descending=True,
    name_column="title",
    time_column="added",
    identity="id",
    table=(
        "id",
        "added",
        "target",
        "title",
        "kind",
        "mode",
        "author",
        "declarations",
        "children",
        "unindexed",
    ),
    sources=frozenset({Source.TREE}),
    load=lambda c: c.contributions,
)

AUTHORS: Grain[AuthorRow] = Grain(
    name="authors",
    columns=AUTHOR_COLUMNS,
    default_sort="contributions",
    descending=True,
    name_column="author",
    time_column="last_seen",
    identity="author",
    table=(
        "author",
        "contributions",
        "targets",
        "declarations",
        "coldkeys",
        "hotkeys",
        "children",
        "last_seen",
        "shared_coldkey",
    ),
    sources=frozenset({Source.TREE}),
    load=lambda c: c.authors,
)

GRAINS: Mapping[str, Grain[Any]] = MappingProxyType(
    {g.name: g for g in (TARGETS, CONTRIBUTIONS, AUTHORS)}
)

DEFAULT_GRAIN = TARGETS.name
