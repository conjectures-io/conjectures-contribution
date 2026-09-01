"""The `contrib ls` surface. Typer owns tokenisation and `--help`; nothing else.

Validation cannot live in Click here, because almost every option's valid values depend
on the grain, which is another argument in the same invocation. So the flags are collected
into a `Request` and `Query.build` refuses or returns — which is what lets every assertion
about filtering, ordering and rendering be made without a `CliRunner`.
"""

from datetime import UTC, datetime
from typing import Annotated

import typer

from ..model import Kind, Mode, PublicKey, SchemaError
from ..query.corpus import read_corpus
from ..query.grains import DEFAULT_GRAIN
from ..query.notes import Level, Note
from ..query.query import DEFAULT_LIMIT, Query, QueryError, Request, Result, relevant, run
from ..query.render import render
from . import complete, config
from .errors import guard
from .repo import open_workspace

KEY_HINT = "run `contrib key generate` once, or `contrib key show` if you already have one"


@guard
def ls(
    ctx: typer.Context,
    grain: Annotated[
        str,
        typer.Argument(help="targets, contributions, or authors.", autocompletion=complete.grains),
    ] = DEFAULT_GRAIN,
    target: Annotated[
        list[str] | None,
        typer.Option("--target", help="Target slug; repeatable.", autocompletion=complete.targets),
    ] = None,
    author: Annotated[
        list[str] | None,
        typer.Option(
            "--author",
            help="Author key, or a prefix of one; repeatable.",
            autocompletion=complete.corpus_authors,
        ),
    ] = None,
    mine: Annotated[bool, typer.Option("--mine", help="Rows belonging to my author key.")] = False,
    coldkey: Annotated[
        list[str] | None,
        typer.Option(
            "--coldkey",
            help="Reward coldkey, or a prefix.",
            autocompletion=complete.corpus_coldkeys,
        ),
    ] = None,
    hotkey: Annotated[
        list[str] | None,
        typer.Option(
            "--hotkey",
            help="Reward hotkey, or a prefix.",
            autocompletion=complete.corpus_hotkeys,
        ),
    ] = None,
    kind: Annotated[Kind | None, typer.Option("--kind", help="Declared kind.")] = None,
    mode: Annotated[Mode | None, typer.Option("--mode", help="Declared mode.")] = None,
    since: Annotated[
        str | None,
        typer.Option(
            "--since",
            help="ISO date, or a window like 30d or 6m.",
            autocompletion=complete.windows,
        ),
    ] = None,
    until: Annotated[
        str | None,
        typer.Option("--until", help="ISO date, or a window.", autocompletion=complete.windows),
    ] = None,
    match: Annotated[
        str | None, typer.Option("--match", help="Glob against the grain's name column.")
    ] = None,
    declares: Annotated[
        str | None,
        typer.Option(
            "--declares",
            help="Glob against Lean declaration names.",
            autocompletion=complete.declarations,
        ),
    ] = None,
    is_: Annotated[
        list[str] | None,
        typer.Option(
            "--is",
            help="Boolean column that must hold; repeatable.",
            autocompletion=complete.boolean_columns,
        ),
    ] = None,
    not_: Annotated[
        list[str] | None,
        typer.Option(
            "--not",
            help="Boolean column that must not hold; repeatable.",
            autocompletion=complete.boolean_columns,
        ),
    ] = None,
    sort: Annotated[
        str | None,
        typer.Option("--sort", help="Column to order by.", autocompletion=complete.sort_columns),
    ] = None,
    desc: Annotated[bool, typer.Option("--desc", help="Reverse the order.")] = False,
    limit: Annotated[int, typer.Option("--limit", help="Rows to show.")] = DEFAULT_LIMIT,
    every: Annotated[bool, typer.Option("--all", help="Show every row.")] = False,
    as_json: Annotated[bool, typer.Option("--json", help="Emit the joined rows as JSON.")] = False,
) -> None:
    workspace = open_workspace(ctx)
    query = Query.build(
        Request(
            today=datetime.now(UTC).date(),
            grain=grain,
            target=tuple(target or ()),
            author=tuple(author or ()),
            coldkey=tuple(coldkey or ()),
            hotkey=tuple(hotkey or ()),
            kind=() if kind is None else (str(kind),),
            mode=() if mode is None else (str(mode),),
            match=() if match is None else (match,),
            declares=() if declares is None else (declares,),
            since=since,
            until=until,
            is_=tuple(is_ or ()),
            not_=tuple(not_ or ()),
            mine=_cached_author_key() if mine else None,
            sort=sort,
            descending=desc,
            limit=None if every else limit,
            as_json=as_json,
        )
    )
    corpus = read_corpus(workspace.root, workspace.contributions, workspace.pool, query.sources)
    if not query.grain.load(corpus) and any(n.level is Level.WARNING for n in corpus.notes):
        raise QueryError(f"nothing readable to list as {grain}; run `contrib doctor`")

    result = run(corpus, query)
    rendered = render(result.rows, query)
    if rendered:
        typer.echo(rendered)

    notes = relevant(corpus.notes, query)
    _report(query, result, notes)
    raise typer.Exit(code=3 if notes else 0)


# Reading the private key to learn its public half would make a read-only listing fail on
# every machine that does not hold it. The public half is cached in the config instead.
def _cached_author_key() -> PublicKey:
    cached = config.author_key()
    if cached is None:
        raise QueryError(f"--mine: no author key is cached — {KEY_HINT}")
    try:
        return PublicKey(cached)
    except SchemaError as exc:
        raise QueryError(
            f"--mine: the cached author key is unusable ({exc}) — {KEY_HINT}"
        ) from None


# Everything here goes to stderr: a --json pipe must carry rows and nothing else.
def _report(query: Query, result: Result, notes: tuple[Note, ...]) -> None:
    since, until = query.window
    if since is not None or until is not None:
        typer.secho(
            f"note: window {since or '(open)'} to {until or '(open)'}",
            fg=typer.colors.CYAN,
            err=True,
        )
    for label, count in sorted(result.declined.items()):
        typer.secho(
            f"note: {label} could not be decided for {count} row(s); they are not listed.",
            fg=typer.colors.YELLOW,
            err=True,
        )
    if not result.rows:
        typer.secho("note: no rows.", fg=typer.colors.CYAN, err=True)
    elif result.total > len(result.rows):
        typer.secho(
            f"note: showing {len(result.rows)} of {result.total}; --all for every row.",
            fg=typer.colors.CYAN,
            err=True,
        )
    lost = [n for n in notes if n.level is not Level.NOTICE]
    behind = [n for n in notes if n.level is Level.NOTICE]
    if lost:
        typer.secho(
            f"warning: {len(lost)} source(s) could not be read; rows may be missing. "
            "`contrib doctor` for details.",
            fg=typer.colors.RED,
            err=True,
        )
    if behind:
        typer.secho(
            f"warning: {len(behind)} index(es) predate this tool; some fields read as "
            "unavailable. Rerun `contrib-admin index`.",
            fg=typer.colors.YELLOW,
            err=True,
        )
