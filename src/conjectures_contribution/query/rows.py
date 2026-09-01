"""One frozen record per grain. Rows are values; no stage may mutate what an earlier one built.

Fields that come from a document are `Field[T]`, because the document may be wrong about
one of them and still be worth a row. Fields derived across the corpus — `children`,
`shared_coldkey` — cannot be unavailable once the corpus loaded at all, so they are not.
"""

from __future__ import annotations

from dataclasses import dataclass, fields

from ..model import ContributionId, Kind, Mode, PublicKey, Ss58Address, TargetSlug
from .values import Commit, Date, Field, Unavailable


@dataclass(frozen=True, slots=True)
class ContributionRow:
    id: ContributionId
    target: TargetSlug
    title: Field[str]
    author: Field[PublicKey]
    # A null reward is an opt-out, not a parse failure: absent (None) and unreadable
    # (Unavailable) are different answers and only the second is a hole.
    coldkey: Field[Ss58Address | None]
    hotkey: Field[Ss58Address | None]
    kind: Field[Kind]
    mode: Field[Mode]
    added: Field[Date]
    declarations: Field[tuple[str, ...]]
    parents: Field[tuple[ContributionId, ...]]
    artifacts: Field[tuple[str, ...]]
    tasks_commit: Field[Commit]
    children: int
    stale: Field[bool]
    unindexed: bool


@dataclass(frozen=True, slots=True)
class TargetRow:
    target: TargetSlug
    in_pool: Field[bool]
    modes: Field[tuple[Mode, ...] | None]
    contributions: int
    # A set aggregate is a claim about every contributing row. One unreadable field makes
    # the whole set a hole rather than a short list: an understated count reads as fact.
    authors: Field[tuple[PublicKey, ...]]
    # Who would be paid if this target settled. Authorship is the identity; a reward
    # destination is a mutable, optional choice, so they are different columns.
    coldkeys: Field[tuple[Ss58Address, ...]]
    declarations: Field[tuple[str, ...]]
    first_added: Field[Date | None]
    last_added: Field[Date | None]


@dataclass(frozen=True, slots=True)
class AuthorRow:
    author: PublicKey
    contributions: int
    targets: tuple[TargetSlug, ...]
    declarations: Field[tuple[str, ...]]
    coldkeys: Field[tuple[Ss58Address, ...]]
    hotkeys: Field[tuple[Ss58Address, ...]]
    children: int
    first_seen: Field[Date | None]
    last_seen: Field[Date | None]
    shared_coldkey: Field[bool]


Row = TargetRow | ContributionRow | AuthorRow


def holes(row: Row) -> tuple[str, ...]:
    return tuple(f.name for f in fields(row) if isinstance(getattr(row, f.name), Unavailable))
