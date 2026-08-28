from __future__ import annotations

from collections.abc import Iterator

from .. import reward
from ..model import METADATA_FILENAME, Contribution
from .base import CheckContext, Finding, Severity, needs_contribution
from .registry import register


@register("C016", "reward block is well-formed")
@needs_contribution
def reward_well_formed(_ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    block = contribution.payload.reward
    signature = contribution.reward_signature

    # A destination with no proof of control, or a proof with nothing to pay, is a
    # hand-edited record either way: neither half means anything without the other.
    if (block is None) != (signature is None):
        present, missing = (
            ("reward", "reward_signature") if block else ("reward_signature", "reward")
        )
        yield Finding(
            "C016",
            Severity.ERROR,
            f"{present} is set but {missing} is null; both or neither",
            METADATA_FILENAME,
        )
    if block is None:
        return

    for role, address in (("coldkey", block.coldkey), ("hotkey", block.hotkey)):
        if not reward.is_canonical(address):
            yield Finding(
                "C016",
                Severity.ERROR,
                f"{role} {address} is not a Bittensor ss58 address (format {reward.SS58_FORMAT})",
                METADATA_FILENAME,
            )


@register("C017", "reward signature verifies under the declared hotkey")
@needs_contribution
def reward_signature_valid(_ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    block = contribution.payload.reward
    signature = contribution.reward_signature
    if block is None or signature is None:
        return
    # C016 owns malformed addresses; verifying under one would only repeat its finding.
    if not reward.is_canonical(block.hotkey):
        return
    if not reward.verify(contribution.contribution_id, block.hotkey, signature):
        yield Finding(
            "C017",
            Severity.ERROR,
            f"reward signature does not verify under hotkey {block.hotkey}",
            METADATA_FILENAME,
        )


@register("C018", "contribution declares a reward destination")
@needs_contribution
def reward_declared(_ctx: CheckContext, contribution: Contribution) -> Iterator[Finding]:
    if contribution.payload.reward is None:
        yield Finding(
            "C018",
            Severity.WARNING,
            "no reward destination; this contribution is not eligible for a reward",
            METADATA_FILENAME,
        )
