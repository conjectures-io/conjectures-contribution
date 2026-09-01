# Querying the corpus: `contrib ls` and `contrib doctor`

`contrib ls` reads every `contributions/<target>/index.json`, reconciles it against the
directories on disk and the pinned pool, and prints rows. One command, three nouns, generic
flags:

```
contrib ls [targets|contributions|authors] [FILTERS] [PRESENTATION]
```

Everything is local — no network, no GitHub, no Lean build. A whole-corpus query costs about
half a second including interpreter start.

`contrib doctor` answers the other question: not "what is there" but "what is wrong with what
is there".

## Questions, and the command that answers each

| Question | Command |
|---|---|
| Which targets have nothing on them? | `contrib ls targets --is empty` |
| Which are crowded? | `contrib ls targets --sort contributions --desc` |
| Which have only one or two? | `contrib ls targets --not empty --sort contributions` |
| Which started, then stalled? | `contrib ls targets --not empty --until 6m --sort last_added` |
| Which are offered in counterexample mode? | `contrib ls targets --mode counterexample` |
| What arrived recently? | `contrib ls contributions --since 30d` |
| Does this declaration already exist? | `contrib ls contributions --declares '*distinctDistances*'` |
| Which targets already have declarations like it? | `contrib ls targets --declares '*Sidon*'` |
| Everything on one target | `contrib ls contributions --target erdos-100` |
| Which contributions are load-bearing? | `contrib ls contributions --sort children --desc` |
| Which has nobody built on? | `contrib ls contributions --is orphan` |
| What have I contributed? | `contrib ls contributions --mine` |
| Has anyone built on mine? | `contrib ls contributions --mine --not orphan` |
| Which contributions name no reward destination? | `contrib ls contributions --not rewarded` |
| Which are pinned to a stale pool commit? | `contrib ls contributions --is stale` |
| Which are on disk but not yet indexed? | `contrib ls contributions --is unindexed` |
| Contributions in a window | `contrib ls contributions --since 2026-08-01 --until 2026-08-31` |
| Who is behind this coldkey? | `contrib ls authors --coldkey 5CfjeQ` |
| One author, many hotkeys? | `contrib ls authors --sort hotkeys --desc` |
| Distinct authors sharing a coldkey? | `contrib ls authors --is shared_coldkey` |
| Is the corpus healthy? | `contrib doctor` |

## The three grains

`targets ⊃ contributions`, with `authors` as the cross-cut. `targets` is the default.

A **set** column shows its size in the table and its elements in `--json`; a filter tests it by
membership and `--sort` orders it by size. The **shown** column below marks what the aligned
table prints — `--json` always emits every column, and `--sort` reaches every column whether the
table shows it or not.

### `targets`

One row per slug in the pinned pool, plus any directory under `contributions/` that has left it.
Default sort `target`.

| column | type | shown | meaning |
|---|---|---|---|
| `target` | str | yes | Target slug. |
| `in_pool` | bool | yes | The slug is still in the pinned pool. **Not** the same as accepting work — retirement is per theorem and does not touch it. |
| `empty` | bool | no | Nothing has been contributed here. |
| `modes` | set | yes | Task bundles the pool offers: `formalized`, `counterexample`. |
| `contributions` | int | yes | Counted from the rows, never read from the stored `contribution_count`. |
| `authors` | set | yes | Author keys active here. |
| `coldkeys` | set | yes | Reward destinations the contributions here name. |
| `declarations` | set | yes | Lean declarations contributed here. |
| `first_added` | date | yes | Earliest contribution. |
| `last_added` | date | yes | Most recent contribution. `--since`/`--until` test this one. |

### `contributions`

One row per contribution. Default sort `added`, descending.

| column | type | shown | meaning |
|---|---|---|---|
| `id` | str | yes | Contribution id. Truncated to 12 in the table, full in `--json`. |
| `target` | str | yes | Target slug. |
| `title` | str | yes | Declared title. `--match` tests this one. |
| `author` | str | yes | Ed25519 key that signed it. See [identity.md](identity.md). |
| `coldkey` | str | no | Reward coldkey, or absent when the contributor opted out. |
| `hotkey` | str | no | Reward hotkey, or absent when the contributor opted out. |
| `kind` | str | yes | `idea`, `lemma`, `partial-proof`, `refutation`. |
| `mode` | str | yes | `formalized`, `counterexample`, `either`. |
| `added` | date | yes | Date the directory first appeared in git. `--since`/`--until` test this one. |
| `declarations` | set | yes | Lean declarations this contribution provides. |
| `parents` | int | no | Declared parents. Declared, not derived. |
| `children` | int | yes | Contributions declaring this one as a parent. Declared, not derived. |
| `artifacts` | int | no | Files in the contribution. |
| `tasks_commit` | str | no | Pool commit it was built against. |
| `orphan` | bool | no | Nobody has declared it as a parent. |
| `stale` | bool | no | Pinned to a commit other than the pool's. |
| `rewarded` | bool | no | Carries a reward destination. |
| `unindexed` | bool | yes | On disk but absent from the target index — CI has not reindexed since it was promoted. |

### `authors`

One row per author key. Default sort `contributions`, descending.

| column | type | shown | meaning |
|---|---|---|---|
| `author` | str | yes | Ed25519 public key. |
| `contributions` | int | yes | Contributions signed by this key. |
| `targets` | set | yes | Targets this key is active on. |
| `declarations` | set | yes | Lean declarations contributed by this key. |
| `coldkeys` | set | yes | Distinct reward coldkeys this key has used. |
| `hotkeys` | set | yes | Distinct reward hotkeys this key has used. |
| `children` | int | yes | Times this key's work was declared as a parent. |
| `first_seen` | date | no | Earliest contribution. |
| `last_seen` | date | yes | Most recent contribution. `--since`/`--until` test this one. |
| `shared_coldkey` | bool | yes | Another author key pays into one of the same coldkeys. |

## Filters

All AND-ed; repeating one flag ORs its values. **A filter binds to a column, so it applies to
exactly the grains that have that column** — there is no matrix to memorise, and applying one
where it does not fit exits 2 naming the grains that do.

| flag | binds to | test |
|---|---|---|
| `--target SLUG` | `target`, `targets` | exact; repeatable |
| `--author KEY` | `author`, `authors` | prefix; repeatable |
| `--mine` | `author`, `authors` | exact, against your configured key |
| `--coldkey ADDR` | `coldkey`, `coldkeys` | prefix; repeatable |
| `--hotkey ADDR` | `hotkey`, `hotkeys` | prefix; repeatable |
| `--kind KIND` | `kind` | exact |
| `--mode MODE` | `mode`, `modes` | exact |
| `--declares GLOB` | `declarations` | glob against any element |
| `--match GLOB` | the grain's name column | glob |
| `--since DATE` / `--until DATE` | the grain's time column | inclusive; ISO `2026-08-01` or a window like `30d`, `6m`, `1y` |
| `--is COLUMN` / `--not COLUMN` | any boolean column | repeatable |

`--is`/`--not` is the whole predicate vocabulary: there is no `--where` and no expression
grammar. Every predicate is a column you can also see in the output. What a `--where` would
genuinely add — `contributions <= 2` — is covered by `--sort contributions` and reading from the
top.

The booleans are `in_pool` and `empty` on targets; `orphan`, `stale`, `rewarded` and `unindexed`
on contributions; `shared_coldkey` on authors.

A relative window resolves against today at the moment you run it, and the resolved days are
echoed on stderr so a `--json` consumer can tell what `30d` meant.

## Presentation

| flag | default |
|---|---|
| `--sort COLUMN` | the grain's default sort; any column, shown or not |
| `--desc` | off, except the grain defaults above |
| `--limit N` | 20 |
| `--all` | show every row |
| `--json` | off |

## Reading the output correctly

**Zero rows is exit 0**, and `--json` still emits `[]`. Never read "no rows" as failure.

**Exit 3 means the answer may be incomplete** — some source did not parse. The rows printed are
still true; `contrib doctor` says what is wrong. **Exit 2 means the question was refused**, and
the message names the fix. Diagnostics go to stderr, so a `--json` pipe is never polluted.

**`?` is unreadable and `—` is absent.** They are different facts. `—` means the value is
legitimately not there — a contribution that opted out of a reward, a target with no
contributions yet. `?` means we could not read it. Both are `null` in `--json`, and neither is
ever rendered as `0`, `false`, or `""`.

**A filter never matches an unreadable value**, and says on stderr how many rows it declined for
that reason. An empty table is not evidence of absence when the line below it says three rows
could not be decided.

**A set aggregate is a hole if any contributing row is.** `authors ?` on a target means we could
not read some author, not that nobody contributed. Understating a count would read as fact.

**`parents`, `children` and `orphan` are *declared* lineage.** Nothing verifies that the Lean
actually uses a declared parent, and nothing detects reuse with no parent declared. "Nobody built
on this" is a claim about declarations, not about the mathematics.

**`in_pool` does not mean "accepting work".** It means the slug is still in the pinned pool.

## Beyond the flags: one pipe

`--json` emits the joined rows with full ids and stable field names, ties broken by id, so
repeated runs diff cleanly. Fields are added over time, never renamed or retyped.

```sh
# contributions per kind
contrib ls contributions --all --json | jq -r 'group_by(.kind)[] | "\(.[0].kind)\t\(length)"'

# contributions per month
contrib ls contributions --all --json | jq -r 'group_by(.added[:7])[] | "\(.[0].added[:7])\t\(length)"'

# every declaration name in the repository, sorted
contrib ls contributions --all --json | jq -r '.[].declarations[]' | sort -u
```

Grouping, aggregation and cross-tabulation stop at that boundary deliberately. The moment the
tool grows a query grammar, `jq` is the better tool — already installed, already documented.

## `contrib doctor`

The same pipeline with the relevance scoping switched off: parse everything, filter nothing,
report all of it. It reports stale indexes, sources that did not parse, an index whose stored
`contribution_count` disagrees with what it lists, targets that have left the pool,
contributions on disk that no index mentions, and indexed rows carrying unreadable fields — each
with the command that fixes it.

Exit 0 clean, 3 with findings, 2 if the checkout is unreadable.

Run it when `ls` exits 3, or before trusting a listing you are about to act on.

## Notes for coding agents

- `--json` with `--all` is the path to use; parse stdout, ignore stderr.
- Check the exit code. 0 and 3 both carry rows; 3 means "and something was missing".
- Do not report `null` as zero. See the `?` / `—` rule above.
- Do not report `orphan` as "nobody used this work". It means nobody *declared* it.
- `reviews/` and `payouts/` are empty today, so nothing here reports weight or payment. Those
  columns do not exist yet, and their absence must not be reported as zero.
- For "what is already proven on this target", read `contributions/<target>/index.md` instead:
  one file, and it gives the statements alongside the declaration names.

`ls` lists. It does not verify signatures, compute payouts, or reach GitHub — so it cannot tell
you whether somebody else is working on a target right now.
