from pathlib import Path
from typing import Annotated

import typer

from ..canonical import canonical_bytes
from ..model import DRAFT_FILENAME, ContributionId, Draft, Kind, Mode, TargetSlug
from ..templates import (
    SCRIPT_FILENAME,
    SCRIPT_TEMPLATE,
    SOURCES_FILENAME,
    SOURCES_TEMPLATE,
    namespace_for,
)
from . import complete
from .errors import guard
from .repo import Workspace, open_workspace


@guard
def new(
    ctx: typer.Context,
    target: Annotated[
        str,
        typer.Argument(help="Target slug, e.g. erdos-100.", autocompletion=complete.targets),
    ],
    title: Annotated[str, typer.Option(help="One-line summary.")] = "Untitled contribution",
    kind: Annotated[Kind, typer.Option(help="What this contribution is.")] = Kind.IDEA,
    mode: Annotated[
        Mode, typer.Option(help="Which side of the target it addresses.")
    ] = Mode.EITHER,
    parent: Annotated[
        list[str] | None, typer.Option(help="Parent contribution id; repeatable.")
    ] = None,
) -> None:
    workspace = open_workspace(ctx)
    pool = workspace.pool()

    slug = TargetSlug.parse(target, "target")
    if slug not in pool.targets:
        raise typer.BadParameter(f"'{slug}' is not a target in the pinned pool")

    draft = Draft(
        target=slug,
        title=title,
        kind=kind,
        mode=mode,
        parents=tuple(sorted({ContributionId.parse(p, "parent") for p in parent or []})),
    )

    directory = workspace.drafts / str(slug)
    if directory.exists():
        raise typer.BadParameter(f"{_show(workspace, directory)} already exists")
    directory.mkdir(parents=True)
    (directory / DRAFT_FILENAME).write_bytes(canonical_bytes(draft.to_json()))
    (directory / SOURCES_FILENAME).write_text(SOURCES_TEMPLATE, encoding="utf-8")
    (directory / SCRIPT_FILENAME).write_text(
        SCRIPT_TEMPLATE.format(slug=slug, namespace=namespace_for(str(slug))),
        encoding="utf-8",
    )

    typer.echo(f"{_show(workspace, directory)}")
    typer.echo(f"edit the files, then: contrib promote {slug}")
    typer.echo("both files are scaffolding; a draft promoted unedited is rejected (C024)")


def _show(workspace: Workspace, path: Path) -> str:
    return str(path.relative_to(workspace.root))
