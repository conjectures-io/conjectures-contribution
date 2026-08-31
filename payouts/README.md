# Funded payout events

This directory contains immutable, operator-signed allocation snapshots under
[`contribution-contract.md`](../contribution-contract.md).

`contrib-admin payout EVENT.json --operator-key KEY` writes one canonical record as
`payouts/<event-id>.json`. The event input must explicitly name its asset, integer unit, positive
budget, network, `coldkey` destination, UTC review window, targets, eligible review ids, payment
deadline, and operator public key. There are no inferred or floating-point financial values, and
each destination comes from the contributor's signed metadata.

Before executing transfers, publish the committed record. After execution, publish the chain
transaction identifiers alongside the launch announcement or in a follow-up audit record.

Run `contrib-admin audit-rewards` to recheck all review and payout signatures and bindings.
