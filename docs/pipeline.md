# The contribution pipeline

How a pull request becomes a merged contribution, and what the repository must be configured to allow.

| Workflow | Trigger | What it does |
| --- | --- | --- |
| `contribution-pr` | PR adding a contribution directory | unprivileged static feedback and index preview on GitHub-hosted runners |
| `contribution-verify` | `contribution-pr` completed | resolves the PR from its head SHA, repeats every trusted rule, then runs sandboxed Lean on `Default` |
| `contribution-merge` | `contribution-verify` finished green | confirms the verified head and base, labels the PR, rebase-merges |
| `contribution-index` | push to `main` | regenerates the indexes and commits them |
| `ci-selfcheck` | changes to the tooling | ruff, mypy, pyright, pytest, index drift, actionlint, zizmor, shellcheck |

The pull request can rewrite its own `contribution-pr` workflow, so that workflow is only fast
feedback. `contribution-verify` is loaded from the default branch through `workflow_run`. It
uses GitHub's API to bind the triggering head SHA to exactly one open PR, checks out the
validator and pool from the tip of the default branch — never from the pull request's base
commit — and independently repeats every rule. Its
sandbox job has no repository token permissions.

Elaborating Lean is arbitrary code execution. Each source therefore runs in a read-only
container with no network, dropped capabilities, process and memory limits, and no mount of
the runner's home. Only the trusted verifier publishes merge metadata, and the job holding the
write token never checks the contribution out.

Indexes are rebuilt on `main` after the merge, never inside a PR: if every contribution edited
an index, every contribution PR would conflict with every other one.

GitHub label names are capped at 50 characters. The merge workflow keeps `target:<slug>` for
targets that fit; for longer slugs it uses a readable prefix plus a 12-character SHA-256 suffix.
The signed metadata and generated indexes always retain the full target slug.

## Maintainer pull requests

`contribution-pr` triggers on `contributions/*/*/**` — four segments deep, so it fires only on
files inside a contribution directory. A PR that changes tooling, workflows, or the generated
`contributions/index.md` and `contributions/<target>/index.md` never reaches it; those get
`ci-selfcheck` instead.

For the case the path filter cannot see — a PR that legitimately adds a contribution directory
*and* something else — label it **`meta`** and the pipeline skips. Only users with write access
can label a pull request, so an outside contributor cannot apply it to their own submission.

## Repository settings this expects

* **Allow rebase merging** must be on; enable **automatically delete head branches**.
* An environment named `contribution-runner` gates the self-hosted job. Configure at least one
  required reviewer. That maintainer should approve the pull request before authorizing the
  environment job, so the one-review branch rule is already satisfied when the checked commit
  reaches the merge workflow.
* Give this repository access to the `Default` runner group. Its Linux runner needs `git`, `jq`,
  `curl`, `elan`, and Docker. The workflow pulls a digest-pinned Debian image before elaboration.
* Protect `main` from direct pushes and require pull requests. Keep the existing one-review rule
  for maintainer changes; the contribution merge workflow additionally refuses to merge if
  either the checked head or checked base commit has moved.

## The merge identity

`contribution-merge` acts as a GitHub App, not as `github-actions[bot]`. A push made with
`GITHUB_TOKEN` never triggers another workflow, so merging with it left `contribution-index`
unrun and every generated index quietly stale — the same rule the index workflow relies on to
avoid looping is the rule that stopped it from being reached at all.

The app is installed on this repository only and holds **Contents: read and write**,
**Pull requests: read and write** and **Issues: read and write**. It is deliberately not
granted **Actions**, so the one step that reads the verifier's artifact keeps `GITHUB_TOKEN`.
Its credentials live in the repository variable `CONTRIB_APP_ID` and the secret
`CONTRIB_APP_PRIVATE_KEY`. If required approvals or required status checks are ever turned on,
add the app to the ruleset's bypass list, or merging stops.

## Repository variables

| Variable | Default | Meaning |
| --- | --- | --- |
| `CONTRIB_LEAN_WORKSPACE` | unset | Path on the `DEV`-group runner to a clean prebuilt Lake project at the exact commit pinned by the pool. |
| `CONTRIB_LEAN_BOOTSTRAP` | `false` | If no workspace is configured, let CI clone and build Formal Conjectures at the commit the pool pins. Slow once, then cached per commit. |
| `CONTRIB_LEAN_CACHE` | `$RUNNER_TOOL_CACHE/formal-conjectures` | Where bootstrapped workspaces are cached. |
| `CONTRIB_LEAN_TIMEOUT` | `900` | Wall-clock seconds per Lean file. |
| `CONTRIB_LEAN_PIDS_LIMIT` | `1024` | Process ceiling inside the sandbox. Lean takes a thread per elaboration task, so this scales with the size of a contribution, not with the core count. |
| `CONTRIB_LEAN_MEMORY_MB` | `16384` | Memory cap per Lean file. |
| `CONTRIB_AUTOMERGE` | on | Set to `false` to label and leave the PR for a human. |
| `CONTRIB_TAG_CONTRIBUTIONS` | `false` | Also push a `contrib/<target>/<id>` tag per contribution. Off on purpose: labels and `index.json` already carry the provenance without adding a ref per contribution. |

One of `CONTRIB_LEAN_WORKSPACE` or `CONTRIB_LEAN_BOOTSTRAP=true` must be set, or the Lean
stage fails with instructions rather than silently skipping.

Either way the runner account needs `elan` on its own `PATH` — `lean_sandbox.sh` asks `lake`
which toolchain the workspace pins before it can mount that toolchain into the container, so
`elan` is required even when the workspace is prebuilt and no bootstrap happens.

## Maintenance

```sh
# after bumping the pinned pool
git submodule update --remote conjectures
uv run contrib-admin sync

uv run contrib-admin index            # rebuild indexes (CI does this on main)
uv run contrib-admin index --check    # fail if anything is stale
```
