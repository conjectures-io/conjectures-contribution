from pathlib import Path
from typing import Annotated

import typer

from .. import elaborate as elaborate_module
from .. import report
from .errors import guard
from .repo import open_workspace


@guard
def elaborate(
    ctx: typer.Context,
    contribution: Annotated[Path, typer.Argument(help="Published contribution directory.")],
    workspace: Annotated[
        Path,
        typer.Option(
            envvar="CONTRIB_LEAN_WORKSPACE",
            help="Lake project to elaborate against; scripts/lean_workspace.sh prepares one.",
        ),
    ],
    timeout_seconds: Annotated[
        int, typer.Option(envvar="CONTRIB_LEAN_TIMEOUT", help="Wall clock per file.")
    ] = elaborate_module.DEFAULT_TIMEOUT_SECONDS,
    memory_mb: Annotated[
        int, typer.Option(envvar="CONTRIB_LEAN_MEMORY_MB", help="Memory cap per file.")
    ] = elaborate_module.DEFAULT_MEMORY_MB,
    sandbox_runner: Annotated[
        Path | None,
        typer.Option(
            envvar="CONTRIB_LEAN_SANDBOX",
            help="Trusted executable that isolates each Lean invocation; required in CI.",
        ),
    ] = None,
    as_json: Annotated[bool, typer.Option("--json", help="Machine-readable findings.")] = False,
) -> None:
    """Elaborate the contribution's Lean sources in a sandboxed workspace."""
    workspace_root = open_workspace(ctx)
    directory = contribution.resolve()
    findings = elaborate_module.elaborate(
        directory,
        workspace.resolve(),
        sandbox_runner=sandbox_runner.resolve() if sandbox_runner is not None else None,
        timeout_seconds=timeout_seconds,
        memory_mb=memory_mb,
    )
    rendered = report.build(workspace_root.root, [(directory, findings)])
    typer.echo(rendered.to_json() if as_json else rendered.to_text())
    raise typer.Exit(code=0 if rendered.ok else 1)
