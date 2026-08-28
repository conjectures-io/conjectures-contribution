"""Create a contribution directory for every open task bundle in the pinned pool."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Annotated

import typer

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_POOL_ROOT = REPO_ROOT / "conjectures"
DEFAULT_CONTRIBUTION_ROOT = REPO_ROOT / "contribution"
INDEX_FILENAME = "index.txt"

app = typer.Typer(add_completion=False)


def load_open_bundles(tier_dir: Path) -> dict[str, str]:
    """Map bundle directory name -> task_id for every bundle in the tier."""
    if not tier_dir.is_dir():
        raise typer.BadParameter(f"tier directory not found: {tier_dir}")

    bundles: dict[str, str] = {}
    for path in sorted(p for p in tier_dir.iterdir() if p.is_dir()):
        manifest = path / "manifest.json"
        if not manifest.is_file():
            typer.echo(f"skip (no manifest.json): {path.name}", err=True)
            continue
        bundles[path.name] = json.loads(manifest.read_text())["task_id"]
    return bundles


def verify_against_allowlist(allowlist_path: Path, bundles: dict[str, str], tier: str) -> list[str]:
    """Return human-readable drift between the pinned pool and the allowlist."""
    allowlist = json.loads(allowlist_path.read_text())
    allowed = {
        entry["task_id"]
        for entry in allowlist["allowed_task_bundles"]
        if entry["tier"] == tier
    }

    problems = [
        f"pool bundle not in allowlist: {name} ({task_id})"
        for name, task_id in sorted(bundles.items())
        if task_id not in allowed
    ]
    orphaned = allowed - set(bundles.values())
    problems.extend(f"allowlist entry has no pool bundle: {task_id}" for task_id in sorted(orphaned))
    return problems


@app.command()
def main(
    tier: Annotated[str, typer.Option(help="Pool tier to mirror.")] = "tier-1",
    pool_root: Annotated[
        Path, typer.Option(help="Checkout of the pinned conjectures-tasks submodule.")
    ] = DEFAULT_POOL_ROOT,
    contribution_root: Annotated[
        Path, typer.Option(help="Directory that mirrors the open task bundles.")
    ] = DEFAULT_CONTRIBUTION_ROOT,
    verify_allowlist: Annotated[
        bool, typer.Option(help="Fail if the pinned pool and allowlist.json disagree.")
    ] = True,
    dry_run: Annotated[bool, typer.Option(help="Report what would change, write nothing.")] = False,
) -> None:
    """Create an `index.txt`-seeded directory for each open task missing from contribution/."""
    tier_dir = pool_root / "pool" / tier
    bundles = load_open_bundles(tier_dir)
    if not bundles:
        raise typer.BadParameter(f"no task bundles found under {tier_dir}")

    if verify_allowlist:
        problems = verify_against_allowlist(pool_root / "allowlist.json", bundles, tier)
        if problems:
            for problem in problems:
                typer.echo(problem, err=True)
            raise typer.Exit(code=1)

    contribution_root.mkdir(parents=True, exist_ok=True)
    existing = {p.name for p in contribution_root.iterdir() if p.is_dir()}

    verb = "would create" if dry_run else "created"
    created: list[str] = []
    seeded: list[str] = []
    for name in sorted(bundles):
        target = contribution_root / name
        is_new = name not in existing
        if is_new:
            created.append(name)
            typer.echo(f"{verb} {name}")
            if not dry_run:
                target.mkdir()
        index = target / INDEX_FILENAME
        if not index.exists():
            seeded.append(name)
            if not is_new:
                typer.echo(f"{verb} {name}/{INDEX_FILENAME}")
            if not dry_run:
                index.touch()

    for name in sorted(existing - set(bundles)):
        typer.echo(f"stale (not in pinned pool, left in place): {name}", err=True)

    typer.echo(
        f"{len(bundles)} open tasks, {len(created)} directories and "
        f"{len(seeded)} {INDEX_FILENAME} {'missing' if dry_run else 'created'}"
    )


if __name__ == "__main__":
    app()
