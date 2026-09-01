"""Reading the corpus: one pass over `contributions/`, degrading rather than raising.

Two tiers of failure, and they behave differently. A **structural** failure — unreadable
bytes, invalid JSON, a schema version we cannot interpret — costs the whole target its
row and is always noted. A **field** failure costs one field, which becomes a hole; the
row survives, and nothing is said unless a query actually reads that column.

Sources load per query: the pool is opened only when a column that needs it is projected
or filtered, which is why `ls contributions --mine` never pays for `Pool.load`.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field, replace
from pathlib import Path
from types import MappingProxyType
from typing import Any, TypeVar, cast

from ..index import INDEX_JSON, SCHEMA_VERSION
from ..model import (
    METADATA_FILENAME,
    Contribution,
    ContributionId,
    Kind,
    Mode,
    PublicKey,
    SchemaError,
    Ss58Address,
    TargetSlug,
)
from ..pool import Pool
from .notes import Level, Note
from .rows import AuthorRow, ContributionRow, TargetRow
from .values import Commit, Date, Field, Source, Unavailable

REINDEX = "contrib-admin index"
_NOT_LOADED = "pool: not loaded"
_NOT_INDEXED = "not in the index yet; run contrib-admin index"

_T = TypeVar("_T")


@dataclass(frozen=True, slots=True)
class Corpus:
    targets: tuple[TargetRow, ...]
    contributions: tuple[ContributionRow, ...]
    authors: tuple[AuthorRow, ...]
    notes: tuple[Note, ...]
    # What each index claims about itself. `ls` derives its counts and never reads this;
    # `contrib doctor` compares the two, which is the only reason it is carried.
    stored: Mapping[str, int] = field(default_factory=lambda: MappingProxyType({}))


def read_corpus(
    root: Path,
    contributions_root: Path,
    pool: Callable[[], Pool],
    sources: frozenset[Source],
) -> Corpus:
    notes: list[Note] = []
    loaded = pool() if Source.POOL in sources else None
    pinned = _pinned(loaded, notes)
    pool_slugs: set[str] = {str(s) for s in loaded.targets} if loaded is not None else set()

    by_slug: dict[str, tuple[ContributionRow, ...]] = {}
    stored: dict[str, int] = {}
    for name in sorted(_subdirectories(contributions_root) | pool_slugs):
        directory = contributions_root / name
        try:
            slug = TargetSlug(name)
        except SchemaError as exc:
            notes.append(_note(root, directory, str(exc), slug=name))
            continue
        read = _read_index(root, directory, slug, notes)
        if read is None:
            continue
        indexed, claimed = read
        if claimed is not None:
            stored[name] = claimed
        known = {str(row.id) for row in indexed}
        by_slug[name] = indexed + _unindexed(root, directory, slug, known, notes)

    every = tuple(row for name in sorted(by_slug) for row in by_slug[name])
    children = _children(
        root, every, complete=len(by_slug) == len(set(by_slug) | pool_slugs), notes=notes
    )
    resolved = tuple(
        replace(row, children=children[str(row.id)], stale=_stale(row, pinned)) for row in every
    )
    grouped = {name: tuple(r for r in resolved if str(r.target) == name) for name in by_slug}

    return Corpus(
        targets=tuple(
            _target_row(name, rows, loaded=loaded, in_pool=name in pool_slugs)
            for name, rows in sorted(grouped.items())
        ),
        contributions=resolved,
        authors=_author_rows(resolved),
        notes=tuple(sorted(notes, key=lambda n: (n.source, n.message))),
        stored=MappingProxyType(dict(sorted(stored.items()))),
    )


def _subdirectories(root: Path) -> set[str]:
    if not root.is_dir():
        return set()
    return {p.name for p in root.iterdir() if p.is_dir()}


def _pinned(pool: Pool | None, notes: list[Note]) -> Commit | None:
    if pool is None:
        return None
    try:
        return Commit(pool.tasks_commit)
    except SchemaError as exc:
        notes.append(Note(Level.WARNING, "conjectures/allowlist.json", str(exc)))
        return None


def _note(
    root: Path, path: Path, message: str, *, slug: str | None, level: Level = Level.WARNING
) -> Note:
    try:
        source = path.relative_to(root).as_posix()
    except ValueError:
        source = path.as_posix()
    return Note(level, source, message, slug)


# None means the target is gone: no field of it is obtainable, so the row would be a guess.
def _read_index(
    root: Path, directory: Path, slug: TargetSlug, notes: list[Note]
) -> tuple[tuple[ContributionRow, ...], int | None] | None:
    path = directory / INDEX_JSON
    name = str(slug)

    try:
        raw_bytes = path.read_bytes()
    except (FileNotFoundError, NotADirectoryError):
        return (), None
    except OSError as exc:
        notes.append(_note(root, path, f"unreadable: {exc}", slug=name))
        return None

    try:
        raw = json.loads(raw_bytes.decode("utf-8"))
    except UnicodeDecodeError:
        notes.append(_note(root, path, "is not valid UTF-8", slug=name))
        return None
    except json.JSONDecodeError as exc:
        notes.append(_note(root, path, f"invalid JSON: {exc}", slug=name))
        return None

    if not isinstance(raw, dict):
        notes.append(_note(root, path, "expected an object", slug=name))
        return None
    document = cast("Mapping[str, Any]", raw)

    version = document.get("schema_version")
    if not isinstance(version, int) or isinstance(version, bool):
        notes.append(_note(root, path, "schema_version: expected an integer", slug=name))
        return None
    if version > SCHEMA_VERSION:
        notes.append(
            _note(
                root,
                path,
                f"schema_version {version} is newer than this tool reads ({SCHEMA_VERSION}); "
                "upgrade conjectures-contribution",
                slug=name,
            )
        )
        return None
    entries = document.get("contributions")
    if not isinstance(entries, list):
        notes.append(_note(root, path, "contributions: expected an array", slug=name))
        return None

    rows, unrecovered, unreadable = _entry_rows(
        directory, slug, cast("Sequence[Any]", entries), behind=version < SCHEMA_VERSION
    )
    notes.extend(
        _note(root, path, f"entry {position} has no readable contribution_id", slug=name)
        for position in unreadable
    )

    # Nothing is said when every gap was closed from the signed records: the answer is
    # complete, and that the index wants rebuilding is `contrib doctor`'s business.
    if unrecovered:
        notes.append(
            _note(
                root,
                path,
                f"written at schema_version {version}, and {unrecovered} of its entries have "
                f"no readable {METADATA_FILENAME}, so fields added since read as unavailable "
                f"— rerun `{REINDEX}`",
                slug=name,
                level=Level.NOTICE,
            )
        )
    claimed = document.get("contribution_count")
    return tuple(rows), claimed if isinstance(claimed, int) and not isinstance(
        claimed, bool
    ) else None


# The id is the row's identity: without it there is nothing to hang the holes on.
def _entry_row(slug: TargetSlug, raw: Any, where: str) -> ContributionRow | None:
    if not isinstance(raw, dict):
        return None
    entry = cast("Mapping[str, Any]", raw)
    try:
        identifier = ContributionId.parse(entry["contribution_id"], where)
    except (KeyError, SchemaError):
        return None
    return ContributionRow(
        id=identifier,
        target=slug,
        title=_one(entry, "title", _text, where),
        author=_one(entry, "author", PublicKey.parse, where),
        coldkey=_maybe(entry, "coldkey", Ss58Address.parse, where),
        hotkey=_maybe(entry, "hotkey", Ss58Address.parse, where),
        kind=_one(entry, "kind", Kind.parse, where),
        mode=_one(entry, "mode", Mode.parse, where),
        added=_one(entry, "added", Date.parse, where),
        declarations=_many(entry, "declarations", _text, where),
        parents=_many(entry, "parents", ContributionId.parse, where),
        artifacts=_many(entry, "artifacts", _text, where),
        tasks_commit=_one(entry, "tasks_commit", Commit.parse, where),
        children=0,
        stale=Unavailable(_NOT_LOADED),
        unindexed=False,
    )


def _entry_rows(
    directory: Path, slug: TargetSlug, entries: Sequence[Any], *, behind: bool
) -> tuple[tuple[ContributionRow, ...], int, tuple[int, ...]]:
    rows: list[ContributionRow] = []
    unreadable: list[int] = []
    unrecovered = 0
    for position, entry in enumerate(entries):
        merged = entry
        if behind and isinstance(entry, dict):
            supplied = _from_bundle(directory, cast("Mapping[str, Any]", entry))
            if supplied is None:
                unrecovered += 1
            else:
                # The entry wins for every key it carries: the index is the summary of
                # record, and a field it gets wrong is corruption, not a gap to paper over.
                merged = {**supplied, **cast("Mapping[str, Any]", entry)}
        row = _entry_row(slug, merged, f"{slug}[{position}]")
        if row is None:
            unreadable.append(position)
            continue
        rows.append(row)
    return tuple(rows), unrecovered, tuple(unreadable)


# What an index older than this reader lacks is not lost: `metadata.json` is the signed
# record the index summarises. Only fields the payload actually carries are recoverable —
# the git date and the Lean declarations are not among them.
def _from_bundle(directory: Path, entry: Mapping[str, Any]) -> Mapping[str, Any] | None:
    identifier = entry.get("contribution_id")
    if not isinstance(identifier, str):
        return None
    try:
        raw = json.loads((directory / identifier / METADATA_FILENAME).read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(raw, dict):
        return None
    payload = cast("Mapping[str, Any]", raw).get("payload")
    if not isinstance(payload, dict):
        return None

    signed = cast("Mapping[str, Any]", payload)
    supplied: dict[str, Any] = {
        key: signed[key]
        for key in ("author", "kind", "mode", "parents", "tasks_commit", "title")
        if key in signed
    }
    if "reward" in signed:
        reward = signed["reward"]
        paid: Mapping[str, Any] = (
            cast("Mapping[str, Any]", reward) if isinstance(reward, dict) else {}
        )
        supplied["coldkey"] = paid.get("coldkey")
        supplied["hotkey"] = paid.get("hotkey")
    artifacts = signed.get("artifacts")
    if isinstance(artifacts, list):
        supplied["artifacts"] = [
            a["name"]
            for a in cast("Sequence[Any]", artifacts)
            if isinstance(a, dict) and "name" in a
        ]
    return supplied


# A contributor who just ran `contrib promote` must see their own work, so the tree is
# reconciled against the index rather than trusted to it. Two fields cost a rebuild —
# the git date and the Lean declarations — and arrive as holes until then.
def _unindexed(
    root: Path, directory: Path, slug: TargetSlug, known: set[str], notes: list[Note]
) -> tuple[ContributionRow, ...]:
    if not directory.is_dir():
        return ()
    rows: list[ContributionRow] = []
    for candidate in sorted(p for p in directory.iterdir() if p.is_dir()):
        metadata = candidate / METADATA_FILENAME
        if candidate.name in known or not metadata.is_file():
            continue
        try:
            contribution = Contribution.parse(json.loads(metadata.read_text(encoding="utf-8")))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError, SchemaError) as exc:
            notes.append(_note(root, metadata, str(exc), slug=str(slug)))
            continue
        payload = contribution.payload
        reward = payload.reward
        rows.append(
            ContributionRow(
                id=contribution.contribution_id,
                target=slug,
                title=payload.title,
                author=payload.author,
                coldkey=None if reward is None else reward.coldkey,
                hotkey=None if reward is None else reward.hotkey,
                kind=payload.kind,
                mode=payload.mode,
                added=Unavailable(f"added: {_NOT_INDEXED}"),
                declarations=Unavailable(f"declarations: {_NOT_INDEXED}"),
                parents=payload.parents,
                artifacts=tuple(str(a.name) for a in payload.artifacts),
                tasks_commit=Commit(payload.tasks_commit),
                children=0,
                stale=Unavailable(_NOT_LOADED),
                unindexed=True,
            )
        )
    return tuple(rows)


# Lineage is declared, never derived: this counts claims, and the columns say so.
def _children(
    root: Path, rows: tuple[ContributionRow, ...], *, complete: bool, notes: list[Note]
) -> Counter[str]:
    counts: Counter[str] = Counter()
    known = {str(row.id) for row in rows}
    for row in rows:
        if isinstance(row.parents, Unavailable):
            continue
        for parent in row.parents:
            counts[str(parent)] += 1
            # A target we could not read took its contributions with it, so every parent
            # under it would look dangling. Only claim an edge is broken when it can be.
            if complete and str(parent) not in known:
                notes.append(
                    _note(
                        root,
                        Path("contributions") / str(row.target) / str(row.id),
                        f"declares parent {parent} which is in no index",
                        slug=str(row.target),
                    )
                )
    return counts


def _stale(row: ContributionRow, pinned: Commit | None) -> Field[bool]:
    if pinned is None:
        return Unavailable(_NOT_LOADED)
    if isinstance(row.tasks_commit, Unavailable):
        return row.tasks_commit
    return row.tasks_commit != pinned


def _target_row(
    name: str, rows: tuple[ContributionRow, ...], *, loaded: Pool | None, in_pool: bool
) -> TargetRow:
    slug = TargetSlug(name)
    target = loaded.targets.get(slug) if loaded is not None else None
    first, last = _window(row.added for row in rows)
    return TargetRow(
        target=slug,
        in_pool=Unavailable(_NOT_LOADED) if loaded is None else in_pool,
        modes=(
            Unavailable(_NOT_LOADED)
            if loaded is None
            else (None if target is None else tuple(sorted(target.bundles)))
        ),
        contributions=len(rows),
        authors=_authors(rows),
        coldkeys=_addresses(rows, lambda r: r.coldkey),
        declarations=_declarations(rows),
        first_added=first,
        last_added=last,
    )


def _author_rows(rows: tuple[ContributionRow, ...]) -> tuple[AuthorRow, ...]:
    grouped: defaultdict[PublicKey, list[ContributionRow]] = defaultdict(list)
    for row in rows:
        if isinstance(row.author, PublicKey):
            grouped[row.author].append(row)

    owners: defaultdict[Ss58Address, set[PublicKey]] = defaultdict(set)
    for author, group in grouped.items():
        for coldkey in _known(_addresses(group, lambda r: r.coldkey)):
            owners[coldkey].add(author)

    built: list[AuthorRow] = []
    for author in sorted(grouped):
        group = grouped[author]
        coldkeys = _addresses(group, lambda r: r.coldkey)
        first, last = _window(row.added for row in group)
        built.append(
            AuthorRow(
                author=author,
                contributions=len(group),
                targets=tuple(sorted({row.target for row in group})),
                declarations=_declarations(tuple(group)),
                coldkeys=coldkeys,
                hotkeys=_addresses(group, lambda r: r.hotkey),
                children=sum(row.children for row in group),
                first_seen=first,
                last_seen=last,
                # Best effort over the coldkeys that read. An author whose own are
                # unreadable cannot be said to share or not share one.
                shared_coldkey=(
                    coldkeys
                    if isinstance(coldkeys, Unavailable)
                    else any(len(owners[c]) > 1 for c in coldkeys)
                ),
            )
        )
    return tuple(built)


# An opted-out reward contributes no address and is not a hole; an unreadable one is.
def _addresses(
    rows: Sequence[ContributionRow], pick: Callable[[ContributionRow], Field[Ss58Address | None]]
) -> Field[tuple[Ss58Address, ...]]:
    found: set[Ss58Address] = set()
    for row in rows:
        value = pick(row)
        if isinstance(value, Unavailable):
            return value
        if value is not None:
            found.add(value)
    return tuple(sorted(found))


def _authors(rows: Sequence[ContributionRow]) -> Field[tuple[PublicKey, ...]]:
    found: set[PublicKey] = set()
    for row in rows:
        if isinstance(row.author, Unavailable):
            return row.author
        found.add(row.author)
    return tuple(sorted(found))


def _declarations(rows: Sequence[ContributionRow]) -> Field[tuple[str, ...]]:
    found: set[str] = set()
    for row in rows:
        if isinstance(row.declarations, Unavailable):
            return row.declarations
        found.update(row.declarations)
    return tuple(sorted(found))


# No contributions means no dates, which is an absence. Contributions whose dates all failed
# to parse is a hole, and the two must not render the same.
def _window(dates: Any) -> tuple[Field[Date | None], Field[Date | None]]:
    seen = list(dates)
    available = sorted(d for d in seen if isinstance(d, Date))
    if available:
        return available[0], available[-1]
    if any(isinstance(d, Unavailable) for d in seen):
        hole = Unavailable("added: unavailable on every contribution")
        return hole, hole
    return None, None


def _text(raw: Any, where: str) -> str:
    if not isinstance(raw, str):
        raise SchemaError(f"{where}: expected a string")
    return raw


def _one(
    entry: Mapping[str, Any], key: str, parse: Callable[[Any, str], _T], where: str
) -> Field[_T]:
    if key not in entry:
        return Unavailable(f"{key}: absent")
    try:
        return parse(entry[key], f"{where}.{key}")
    except SchemaError as exc:
        return Unavailable(str(exc))


def _maybe(
    entry: Mapping[str, Any], key: str, parse: Callable[[Any, str], _T], where: str
) -> Field[_T | None]:
    if key not in entry:
        return Unavailable(f"{key}: absent")
    if entry[key] is None:
        return None
    try:
        return parse(entry[key], f"{where}.{key}")
    except SchemaError as exc:
        return Unavailable(str(exc))


def _many(
    entry: Mapping[str, Any], key: str, parse: Callable[[Any, str], _T], where: str
) -> Field[tuple[_T, ...]]:
    if key not in entry:
        return Unavailable(f"{key}: absent")
    value = entry[key]
    if not isinstance(value, list):
        return Unavailable(f"{key}: expected an array")
    try:
        return tuple(
            parse(item, f"{where}.{key}[{position}]")
            for position, item in enumerate(cast("Sequence[Any]", value))
        )
    except SchemaError as exc:
        return Unavailable(str(exc))


def _known(addresses: Field[tuple[Ss58Address, ...]]) -> tuple[Ss58Address, ...]:
    return () if isinstance(addresses, Unavailable) else addresses
