# Sources and scope

## Target

- Erdős Problem 364: https://www.erdosproblems.com/364
- The exact Formal Conjectures source used by the bound contribution court is unchanged in
  `ErdosProblems/364.lean` from the audited upstream base:
  https://github.com/google-deepmind/formal-conjectures/blob/7d1a8c9912747679d0093f6d1216420c33ee5ffa/FormalConjectures/ErdosProblems/364.lean
- Bound contribution corpus:
  https://github.com/conjectures-io/conjectures-contribution/blob/bce521fd688c82ec2b45cbd640cf8fbdafb7431a/contributions/erdos-364/index.md

## Exact candidate provenance

The five fixed starting values are source-bound candidates selected from the project-held
A076445 outer-pair candidate table after applying the already-published mod-36 necessary
condition. Background sequence: https://oeis.org/A076445.

The exact starts used here are the rows with source indices 19, 20, 26, 29, and 33. This is a
finite parametrized candidate set. The source explicitly does **not** establish that these rows
are consecutive in the global ordering, so these theorems must not be reported as a contiguous
integer-search frontier.

For the five middle terms `m = n + 1`, the supplied exact certificates are:

| source index | prime | exact middle certificate |
| ---: | ---: | --- |
| 19 | 19 | `19 ∣ m` and `19^2 ∤ m` |
| 20 | 29 | `29 ∣ m` and `29^2 ∤ m` |
| 26 | 7 | `7 ∣ m` and `7^2 ∤ m` |
| 29 | 29 | `29 ∣ m` and `29^2 ∤ m` |
| 33 | 19 | `19 ∣ m` and `19^2 ∤ m` |

`script.lean` rechecks those finite arithmetic facts directly with `norm_num`; it does not rely
on a new generic mathematical lemma.

## Collision and prior-art boundary

The bound corpus already contains the generic exact-once obstruction
`Contribution.Erdos364Congruence.not_powerful_of_dvd_of_not_sq_dvd` here:
https://github.com/conjectures-io/conjectures-contribution/blob/bce521fd688c82ec2b45cbd640cf8fbdafb7431a/contributions/erdos-364/c03f9833c590b6a8994f9b396b3846dddeeb002096199112c54dab8c667852df/script.lean

That generic obstruction is prior work and is not claimed as new. The proposed delta is only the
five exact candidate-specific exclusions. A bounded collision check at the bound corpus revision
found none of the five exact middle numerals already present. Rebind this check before any external
submission action.

## Claim ceiling

The artifact establishes only that these five exact source-bound starting values do not yield a
consecutive powerful triple. It does not solve Erdős 364, establish a global search frontier, or
claim contribution recognition, reward, payment, or external acceptance.
