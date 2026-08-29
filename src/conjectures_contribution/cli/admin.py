from pathlib import Path
from typing import Annotated

import typer

from .. import index as index_module
from . import repo as repo_module
from .errors import guard
from .repo import open_workspace

app = typer.Typer(
    add_completion=False, no_args_is_help=True, help="Maintainer tooling for the contribution repo."
)


# Without a callback Typer collapses a single-command app, and `contrib-admin sync`
# would become `contrib-admin`.
@app.callback()
def _root(  # pyright: ignore[reportUnusedFunction]
    ctx: typer.Context,
    repo: Annotated[
        Path | None, typer.Option(help="Repository to act on; default is the one you are in.")
    ] = None,
    pool: Annotated[
        Path | None,
        typer.Option(help="Trusted conjecture pool to use instead of <repository>/conjectures."),
    ] = None,
) -> None:
    ctx.obj = repo_module.RootOptions(repo=repo, pool=pool)


@app.command("sync")
@guard
def sync(
    ctx: typer.Context,
    dry_run: Annotated[bool, typer.Option(help="Report what would change, write nothing.")] = False,
) -> None:
    workspace = open_workspace(ctx)
    pool = workspace.pool()
    workspace.contributions.mkdir(parents=True, exist_ok=True)
    present = {p.name for p in workspace.contributions.iterdir() if p.is_dir()}

    verb = "would create" if dry_run else "created"
    created = 0
    for slug in sorted(str(s) for s in pool.targets):
        if slug not in present:
            typer.echo(f"{verb} {slug}")
            created += 1
            if not dry_run:
                (workspace.contributions / slug).mkdir()

    # Index files come from the same generator CI runs, so a freshly synced target
    # and a merged contribution produce byte-identical output.
    if not dry_run:
        for path in index_module.build(
            workspace.root, workspace.contributions, workspace.pool_root, pool
        ):
            typer.echo(f"wrote {path}")

    for stale in sorted(present - {str(s) for s in pool.targets}):
        typer.secho(
            f"stale (not in pinned pool, left in place): {stale}", fg=typer.colors.YELLOW, err=True
        )

    typer.echo(f"{len(pool.targets)} open targets, {created} {'missing' if dry_run else 'created'}")


@app.command("index")
@guard
def index(
    ctx: typer.Context,
    check: Annotated[
        bool, typer.Option(help="Fail instead of writing when an index is stale.")
    ] = False,
) -> None:
    """Rebuild `contributions/**/index.md` and `index.json`."""
    workspace = open_workspace(ctx)
    stale = index_module.build(
        workspace.root,
        workspace.contributions,
        workspace.pool_root,
        workspace.pool(),
        check=check,
    )
    if not stale:
        typer.echo("indexes are up to date")
        return
    for path in stale:
        typer.echo(f"{'stale' if check else 'wrote'} {path}")
    if check:
        typer.secho(
            "run `contrib-admin index` and commit the result", fg=typer.colors.RED, err=True
        )
        raise typer.Exit(code=1)
