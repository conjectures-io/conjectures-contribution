# Recognition records

This directory contains immutable, maintainer-signed decisions under
[`contribution-contract.md`](../contribution-contract.md).

Records are written only by `contrib-admin review`:

```text
reviews/<target>/<contribution-id>/<review-id>.json
```

The id hashes the canonical decision payload. Every listed reviewer signs that payload with an
Ed25519 key. Corrections create a new record whose `supersedes` field names the old id; existing
records are never edited or deleted.

Run `contrib-admin audit-rewards` before publishing a payout event.
