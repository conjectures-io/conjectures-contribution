"""`contrib doctor` — the same corpus pipeline with the scoping switched off.

`ls` answers a question and says one line when the answer might be short. This says what
is actually wrong and which command fixes it, which is what keeps that one line tolerable.
Staleness is not re-derived here: `index.build(check=True)` already returns the paths that
differ, and a second implementation of it would be a second thing to keep true.
"""

from dataclasses import dataclass

import typer

from .. import index
from ..query.corpus import Corpus, read_corpus
from ..query.notes import Note
from ..query.rows import ContributionRow, holes
from ..query.values import Source, Unavailable
from .errors import guard
from .repo import open_workspace

REINDEX = "rerun `contrib-admin index`"
ID_SHOWN = 12


@dataclass(frozen=True, slots=True)
class Section:
    headline: str
    details: tuple[str, ...]


@guard
def doctor(ctx: typer.Context) -> None:
    workspace = open_workspace(ctx)
    pool = workspace.pool()
    corpus = read_corpus(workspace.root, workspace.contributions, lambda: pool, frozenset(Source))
    stale = index.build(
        workspace.root, workspace.contributions, workspace.pool_root, pool, check=True
    )

    sections = [
        section
        for section in (
            _stale(stale),
            _unreadable(corpus.notes),
            _counts(corpus),
            _drift(corpus),
            _pending(corpus),
            _fields(corpus),
        )
        if section is not None
    ]

    for section in sections:
        typer.secho(section.headline, fg=typer.colors.YELLOW)
        for detail in section.details:
            typer.echo(f"  {detail}")
    if not sections:
        typer.secho("ok: every index is current and every source parsed.", fg=typer.colors.GREEN)
    raise typer.Exit(code=3 if sections else 0)


def _stale(paths: tuple[str, ...]) -> Section | None:
    if not paths:
        return None
    return Section(f"indexes: {len(paths)} out of date — {REINDEX}", paths)


def _unreadable(notes: tuple[Note, ...]) -> Section | None:
    if not notes:
        return None
    return Section(
        f"sources: {len(notes)} did not read as written",
        tuple(f"{note.source}: {note.message}" for note in notes),
    )


# The reader derives every count it shows. This is the only place the stored one is read,
# and it is read to be checked, never to be believed.
def _counts(corpus: Corpus) -> Section | None:
    disagreeing = tuple(
        f"{slug}: the index says {claimed}, it lists {_listed(corpus, slug)}"
        for slug, claimed in corpus.stored.items()
        if claimed != _listed(corpus, slug)
    )
    if not disagreeing:
        return None
    return Section(
        f"counts: {len(disagreeing)} index(es) disagree with what they list — {REINDEX}",
        disagreeing,
    )


def _listed(corpus: Corpus, slug: str) -> int:
    return sum(1 for row in corpus.contributions if str(row.target) == slug and not row.unindexed)


def _drift(corpus: Corpus) -> Section | None:
    outside = tuple(str(row.target) for row in corpus.targets if row.in_pool is False)
    if not outside:
        return None
    return Section(
        f"tree: {len(outside)} target(s) left the pinned pool; their contributions are kept "
        "for the record",
        outside,
    )


def _pending(corpus: Corpus) -> Section | None:
    pending = tuple(_named(row) for row in corpus.contributions if row.unindexed)
    if not pending:
        return None
    return Section(f"tree: {len(pending)} contribution(s) not in any index — {REINDEX}", pending)


# Holes on an unindexed row are expected and reported above as pending. These are the ones
# an index claims to describe and does not.
def _fields(corpus: Corpus) -> Section | None:
    found = tuple(
        f"{_named(row)}: {', '.join(_unreadable_fields(row))}"
        for row in corpus.contributions
        if not row.unindexed and _unreadable_fields(row)
    )
    if not found:
        return None
    return Section(f"fields: {len(found)} indexed row(s) carry unreadable fields", found)


def _named(row: ContributionRow) -> str:
    return f"{row.target}/{str(row.id)[:ID_SHOWN]}"


# `stale` is derived from `tasks_commit`, so naming both would report one problem twice.
def _unreadable_fields(row: ContributionRow) -> tuple[str, ...]:
    hidden: set[str] = {"stale"} if isinstance(row.tasks_commit, Unavailable) else set()
    return tuple(name for name in holes(row) if name not in hidden)
