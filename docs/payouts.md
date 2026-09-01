# Paid contribution operation

Technical acceptance, recognition, and payment remain separate. A green contribution pipeline
proves admissibility; it does not assign a weight or spend funds.

An independent maintainer creates a signed recognition record with `contrib-admin review`. The
command requires explicit six-gate results, a reason, a canonical UTC review time, and one or two
reviewer key files. Recognized work receives the 1–10 component score defined by the contract.
High-weight or conflicted decisions require two signatures, and an author key cannot review its
own contribution.

Recognition records conditional credit; they do not trigger payment. A contribution payout is
blocked until the target has been formally settled by an accepted validator proof or refutation.
The payout event must bind that accepted result's id and published proof hash for every target it
covers. Payouts always use the coldkey that the contributor signed into the immutable contribution
metadata. No separate address collection or pre-launch funding record is required.

After the review window closes **and the target has been formally solved**, create a payout event
with the actual budget, scope, and accepted-result evidence:

```json
{
  "asset": "TAO",
  "budget": 1000000000,
  "contract_version": "1.0",
  "created_at": "2026-09-08T00:00:00Z",
  "destination": "coldkey",
  "event_version": 1,
  "formal_solves": [
    {
      "accepted_at": "2026-09-07T20:00:00Z",
      "mode": "formalized",
      "proof_sha256": "<64-character published proof digest>",
      "result_id": "<canonical validator result UUID>",
      "target": "<funded target slug>"
    }
  ],
  "name": "launch-week-one",
  "network": "finney",
  "operator": "<64-character Ed25519 public key>",
  "payment_due_at": "2026-09-09T00:00:00Z",
  "period_end": "2026-09-07T23:59:59Z",
  "period_start": "2026-09-01T00:00:00Z",
  "review_ids": ["<eligible signed review id>"],
  "targets": ["<funded target slug>"],
  "unit": "rao"
}
```

The numbers and dates above demonstrate the schema only. Sign and publish the exact allocation
with:

```sh
uv run contrib-admin payout /path/to/event.json \
  --operator-key /secure/operator.key
uv run contrib-admin audit-rewards
```

`payouts/<event-id>.json` binds the accepted formal solve, exact eligible reviews, coldkey
destinations, financial terms, and integer allocations. Publish the payout snapshot before
executing transfers, then publish the resulting chain transaction ids.

