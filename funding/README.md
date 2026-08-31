# Funding rounds

This directory contains immutable, operator-signed budget commitments published before their
earning windows open.

`contrib-admin fund ROUND.json --operator-key KEY` writes one canonical record as
`funding/<round-id>.json`. It binds the network, asset and integer unit, positive budget,
destination policy, UTC window, funded targets, payment deadline, and operator key. Payout events
must reference one of these records and repeat its terms exactly.

Funding JSON records are append-only. Changing terms requires a new round, not an edit.
