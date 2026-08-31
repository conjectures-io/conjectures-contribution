import json
from pathlib import Path
from typing import Annotated

import typer

from .. import index as index_module
from ..model import METADATA_FILENAME, Contribution, SchemaError
from ..payout import (
    build_funding,
    build_payout,
    load_event,
    load_funding,
    load_payout,
    load_round,
    validate_payout_context,
    write_funding,
    write_payout,
)
from ..recognition import (
    CONTRACT_VERSION,
    Decision,
    GateResult,
    Gates,
    ReviewId,
    ReviewPayload,
    Score,
    active_reviews,
    iter_reviews,
    sign_review,
    validate_for_contribution,
    write_review,
)
from ..signing import SigningKey
from ..store import iter_contributions
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


def _contribution(path: Path) -> Contribution:
    metadata = path.resolve() / METADATA_FILENAME
    try:
        return Contribution.parse(json.loads(metadata.read_text(encoding="utf-8")), str(metadata))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SchemaError(f"{metadata}: invalid contribution metadata: {exc}") from None


def _published(root: Path) -> dict[str, Contribution]:
    return {
        str(contribution.contribution_id): contribution
        for directory in iter_contributions(root / "contributions")
        for contribution in (_contribution(directory),)
    }


@app.command("review")
@guard
def review(
    ctx: typer.Context,
    contribution: Annotated[Path, typer.Argument(help="Published contribution directory.")],
    decision: Annotated[Decision, typer.Option(help="Recognition decision.")],
    direct_relevance: Annotated[GateResult, typer.Option()],
    verified_value: Annotated[GateResult, typer.Option()],
    material_progress: Annotated[GateResult, typer.Option()],
    novelty: Annotated[GateResult, typer.Option()],
    reusable_handoff: Annotated[GateResult, typer.Option()],
    provenance: Annotated[GateResult, typer.Option()],
    target_impact: Annotated[int, typer.Option(min=0, max=4)] = 0,
    generality_reuse: Annotated[int, typer.Option(min=0, max=2)] = 0,
    originality_delta: Annotated[int, typer.Option(min=0, max=2)] = 0,
    verification_handoff: Annotated[int, typer.Option(min=0, max=2)] = 0,
    reason: Annotated[str, typer.Option(help="Evidence-based decision rationale.")] = "",
    reviewed_at: Annotated[
        str, typer.Option(help="Canonical UTC time, for example 2026-08-31T16:00:00Z.")
    ] = "",
    reviewer_key: Annotated[
        list[Path] | None,
        typer.Option("--reviewer-key", help="Ed25519 reviewer key; repeat for two reviewers."),
    ] = None,
    conflict: Annotated[
        list[str] | None, typer.Option("--conflict", help="Disclosed conflict; repeat as needed.")
    ] = None,
    supersedes: Annotated[
        str | None, typer.Option(help="Prior review id replaced by this one.")
    ] = None,
) -> None:
    """Create and sign an immutable recognition decision."""
    workspace = open_workspace(ctx)
    keys = tuple(SigningKey.load(path.expanduser()) for path in (reviewer_key or []))
    if not keys:
        raise SchemaError("at least one --reviewer-key is required")
    published = _contribution(contribution)
    score = Score(
        target_impact=target_impact,
        generality_reuse=generality_reuse,
        originality_delta=originality_delta,
        verification_handoff=verification_handoff,
    )
    payload = ReviewPayload(
        contract_version=CONTRACT_VERSION,
        contribution_id=str(published.contribution_id),
        target=published.payload.target,
        decision=decision,
        gates=Gates(
            direct_relevance=direct_relevance,
            verified_value=verified_value,
            material_progress=material_progress,
            novelty=novelty,
            reusable_handoff=reusable_handoff,
            provenance=provenance,
        ),
        score=score,
        weight=score.total if decision is Decision.RECOGNIZED else 0,
        reviewers=tuple(sorted(key.public_key for key in keys)),
        reason=reason,
        reviewed_at=reviewed_at,
        conflicts=tuple(sorted(conflict or [])),
        supersedes=None if supersedes is None else ReviewId(supersedes),
    )
    record = sign_review(payload, keys)
    validate_for_contribution(record, published)
    typer.echo(write_review(workspace.root, record))


@app.command("payout")
@guard
def payout(
    ctx: typer.Context,
    event_file: Annotated[Path, typer.Argument(help="Explicit funded payout-event JSON.")],
    funding_file: Annotated[Path, typer.Option(help="Previously published funding record.")],
    operator_key: Annotated[Path, typer.Option(help="Ed25519 operator signing key.")],
) -> None:
    """Build and sign an exact integer payout allocation."""
    workspace = open_workspace(ctx)
    event = load_event(event_file)
    record = build_payout(
        event,
        load_funding(funding_file),
        iter_reviews(workspace.root),
        _published(workspace.root),
        SigningKey.load(operator_key.expanduser()),
    )
    typer.echo(write_payout(workspace.root, record))


@app.command("fund")
@guard
def fund(
    ctx: typer.Context,
    round_file: Annotated[Path, typer.Argument(help="Explicit pre-launch funding-round JSON.")],
    operator_key: Annotated[Path, typer.Option(help="Ed25519 operator signing key.")],
) -> None:
    """Sign and publish a budget commitment before its earning window."""
    workspace = open_workspace(ctx)
    record = build_funding(load_round(round_file), SigningKey.load(operator_key.expanduser()))
    typer.echo(write_funding(workspace.root, record))


@app.command("audit-rewards")
@guard
def audit_rewards(ctx: typer.Context) -> None:
    """Verify every review, supersession, and signed payout record."""
    workspace = open_workspace(ctx)
    contributions = _published(workspace.root)
    reviews = iter_reviews(workspace.root)
    for record in reviews:
        contribution = contributions.get(record.payload.contribution_id)
        if contribution is None:
            raise SchemaError(f"review {record.review_id}: contribution is missing")
        validate_for_contribution(record, contribution)
    current = active_reviews(reviews)
    funding_paths = sorted((workspace.root / "funding").glob("*.json"))
    funding = {
        record.round_id: record for path in funding_paths for record in (load_funding(path),)
    }
    payout_paths = sorted((workspace.root / "payouts").glob("*.json"))
    for path in payout_paths:
        payout_record = load_payout(path)
        funding_record = funding.get(payout_record.event.round_id)
        if funding_record is None:
            raise SchemaError(f"payout {payout_record.event_id}: funding round is missing")
        validate_payout_context(payout_record, funding_record, reviews, contributions)
    typer.echo(
        f"{len(reviews)} review record(s), {len(current)} active, "
        f"{len(funding_paths)} funding round(s), {len(payout_paths)} payout event(s): valid"
    )
