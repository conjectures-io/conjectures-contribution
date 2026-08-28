from typing import Annotated

import typer

from .errors import guard
from .repo import Workspace

app = typer.Typer(
    add_completion=False, no_args_is_help=True, help="Maintainer tooling for the contribution repo."
)

INDEX_FILENAME = "index.md"


# Without a callback Typer collapses a single-command app, and `contrib-admin sync`
# would become `contrib-admin`.
@app.callback()
def _root() -> None:  # pyright: ignore[reportUnusedFunction]
    pass


@app.command("sync")
@guard
def sync(
    dry_run: Annotated[bool, typer.Option(help="Report what would change, write nothing.")] = False,
) -> None:
    workspace = Workspace.discover()
    pool = workspace.pool()
    workspace.contributions.mkdir(parents=True, exist_ok=True)
    present = {p.name for p in workspace.contributions.iterdir() if p.is_dir()}

    verb = "would create" if dry_run else "created"
    created = 0
    for slug in sorted(str(s) for s in pool.targets):
        directory = workspace.contributions / slug
        index = directory / INDEX_FILENAME
        if slug not in present:
            typer.echo(f"{verb} {slug}")
            created += 1
            if not dry_run:
                directory.mkdir()
        if not index.exists() and not dry_run:
            index.write_text(f"# {slug}\n", encoding="utf-8")

    for stale in sorted(present - {str(s) for s in pool.targets}):
        typer.secho(
            f"stale (not in pinned pool, left in place): {stale}", fg=typer.colors.YELLOW, err=True
        )

    typer.echo(f"{len(pool.targets)} open targets, {created} {'missing' if dry_run else 'created'}")
