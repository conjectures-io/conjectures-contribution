# Two identities: the author key and the reward wallet

A contribution carries two unrelated identities, and confusing them is the easiest mistake to
make when reading `contrib ls` output or the contract.

```
author   111d9b187e4b1a2213e2c0c625e000fee87245ac72bde74aac143e67c7ccebb7
coldkey  5G1G2f93eezKQ48jFFmynqGdTYsK8yk6ecTSDb8uU22111ht
hotkey   5GeGrYFpMrNSh3Nwcx987zWz4cME9A9NbCkEbjBvv4uLUScV
```

Different cryptosystems, different files, different jobs.

## The author key — who made it

An ed25519 public key, 64 hex characters. Its private half lives in
`~/.config/conjectures/ed25519.key`, created by `contrib key generate`. It exists on no
blockchain and nothing outside this tool knows about it.

It signs the canonical bytes of the payload. That signature — `signature` in `metadata.json`,
verified by `C006` — is what says *this key-holder produced this exact contribution*.

The author key is inside the payload that is hashed into the contribution id, so it is
**immutable**: changing it produces a different contribution at a different address.

## The reward wallet — where payment goes

A Bittensor ss58 address, 48 base58 characters, from your `btcli` wallet. This is a real on-chain
account that can hold funds.

The **coldkey** is the destination. The **hotkey** is the operational key beside it, and it is
the one that signs: `reward_signature` is the hotkey signing the contribution id, which is the
wallet saying *I accept being the destination for this exact contribution*.

The private coldkey is never opened by this tool. `wallet.py` reads only `coldkeypub.txt`, and a
test named `test_nothing_opens_the_private_coldkey` keeps it that way. Nothing here ever prompts
for a passphrase; an encrypted hotkey is refused with an explanation rather than a prompt.

A reward destination is a **choice, per contribution**. You can point the next one elsewhere, and
`contrib promote --no-reward` writes `null` — a contribution with an author and no coldkey at all
is valid and permanent, because the choice is part of the hashed id.

## Why they are separate

- **Different jobs.** One answers "who made this", the other "where does payment go".
- **Different lifetimes.** Authorship is fixed forever by the id; a destination is a per-
  contribution decision.
- **Different risk.** A key that holds funds should not be signing arbitrary documents, and an
  identity you can regenerate freely should not be your wallet.
- **One is optional.** Opting out of a reward is supported; being anonymous about authorship is
  not, because the signature is what makes a contribution attributable at all.

## What follows for the columns

`contrib ls` reports both, and neither count implies the other:

- `authors 3, coldkeys 1` on a target — three identities paying into one wallet. The cheapest
  sybil signal there is, and `contrib ls authors --is shared_coldkey` finds it directly.
- `authors 1, coldkeys 3` — one contributor rotating destinations between submissions.

`--mine` matches on **authorship**, never on the reward destination, because authorship is the
stable identity. It reads the public half of your key from
`~/.config/conjectures/contribution.toml`, cached there by `contrib key generate` and
`contrib key show`, so a read-only listing never has to open the private key and never fails on a
machine that does not hold it.

## What the signature does *not* prove

`C006` proves that the holder of the author key produced that payload. It does not prove they
wrote the Lean. `C015` rejects byte-identical artifacts resubmitted under a new key; a paraphrase
escapes it. Treat an author key as a stable pseudonym — two contributions under one key are
provably by the same key-holder, and that is the whole claim.

One person may hold many author keys, and nothing detects that directly. `shared_coldkey` catches
the case where they all pay into one wallet.
