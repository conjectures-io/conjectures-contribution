from pathlib import Path
from typing import Annotated

import typer

from .. import report, store
from ..checks import ChangesetContext, run_all, run_changeset
from ..loader import load_context
from ..model import Change
from ..store import Published
from .errors import guard
from .git import changes
from .repo import Workspace


@guard
def check(
    paths: Annotated[
        list[Path] | None, typer.Argument(help="Contribution directories; default is all.")
    ] = None,
    base: Annotated[str | None, typer.Option(help="Base ref; enables the changeset rules.")] = None,
    as_json: Annotated[bool, typer.Option("--json", help="Machine-readable findings.")] = False,
) -> None:
    workspace = Workspace.discover()
    pool = workspace.pool()
    published = Published.scan(workspace.contributions)
    changeset = changes(workspace.root, base) if base is not None else None

    findings = (
        run_changeset(
            ChangesetContext(
                repo_root=workspace.root,
                contributions_root=workspace.contributions,
                changes=changeset,
            )
        )
        if changeset is not None
        else ()
    )

    results = [
        (
            directory,
            run_all(
                load_context(
                    directory,
                    contributions_root=workspace.contributions,
                    pool=pool,
                    published=published,
                )
            ),
        )
        for directory in _select(workspace, paths, changeset)
    ]

    rendered = report.build(workspace.root, results, findings)
    typer.echo(rendered.to_json() if as_json else rendered.to_text())
    raise typer.Exit(code=0 if rendered.ok else 1)


def _select(
    workspace: Workspace, paths: list[Path] | None, changeset: tuple[Change, ...] | None
) -> list[Path]:
    if paths:
        return [p.resolve() for p in paths]
    if changeset is None:
        return sorted(store.iter_contributions(workspace.contributions))
    return list(store.touched(workspace.contributions, changeset))
