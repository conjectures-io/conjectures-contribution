import json
import shutil
from pathlib import Path
from typing import Annotated

import typer

from .. import report
from ..build import Built
from ..checks import run_all
from ..loader import load_context
from ..model import DRAFT_FILENAME, Draft
from ..signing import SigningKey
from ..store import Published
from .errors import guard
from .repo import Workspace, key_path


@guard
def promote(
    target: Annotated[str | None, typer.Argument(help="Target slug of the draft.")] = None,
    source: Annotated[
        Path | None, typer.Option("--from", help="Draft directory; default is drafts/<target>.")
    ] = None,
    key: Annotated[Path | None, typer.Option(help="Signing key file.")] = None,
) -> None:
    workspace = Workspace.discover()
    directory = _resolve_draft(workspace, target, source)
    draft = Draft.parse(json.loads((directory / DRAFT_FILENAME).read_text(encoding="utf-8")))
    if target is not None and str(draft.target) != target:
        raise typer.BadParameter(f"draft declares target '{draft.target}', not '{target}'")

    pool = workspace.pool()
    signing_key = SigningKey.load(key_path(key))
    built = Built.from_draft(draft, directory, pool, signing_key)
    destination = built.write(workspace.contributions)

    findings = run_all(
        load_context(
            destination,
            contributions_root=workspace.contributions,
            pool=pool,
            published=Published.scan(workspace.contributions),
        )
    )
    rendered = report.build(workspace.root, [(destination, findings)])
    if not rendered.ok:
        shutil.rmtree(destination)
        typer.echo(rendered.to_text(), err=True)
        raise typer.Exit(code=1)

    typer.echo(str(destination.relative_to(workspace.root)))


def _resolve_draft(workspace: Workspace, target: str | None, source: Path | None) -> Path:
    if source is not None:
        directory = source.resolve()
    elif target is not None:
        directory = workspace.drafts / target
    else:
        candidates = [
            p for p in sorted(workspace.drafts.glob("*")) if (p / DRAFT_FILENAME).is_file()
        ]
        if len(candidates) != 1:
            raise typer.BadParameter(f"expected one draft in drafts/, found {len(candidates)}")
        directory = candidates[0]
    if not (directory / DRAFT_FILENAME).is_file():
        raise typer.BadParameter(f"{directory}: no {DRAFT_FILENAME}")
    return directory
