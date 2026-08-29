<!--
One pull request adds exactly one contribution directory. Everything below is
checked automatically; this template is here so you can catch problems before CI
does. Technical rules: guidelines.md. Recognition policy: contribution-contract.md.
-->

## What this gives the next miner

<!-- One or two sentences. The short version goes in the payload `title`. -->

## Target obstacle and use site

<!-- Name the target obligation this reduces and the declaration(s) a later solver will use. -->

## Novelty and lineage

<!-- Compare with Mathlib and the target's index.json. Name every parent contribution and delta. -->

## Checklist

- [ ] Adds exactly one directory under `contributions/<target>/<contribution-id>/`
- [ ] `<contribution-id>` came from `contrib promote`, not chosen by hand
- [ ] `sources.md` says where this came from (or "original work")
- [ ] `contrib check` passes locally
- [ ] No `sorry`, no `#eval`, no `axiom`; every `.lean` file stands alone
- [ ] This is not a solution to the target, and does not duplicate an existing
      contribution in `contributions/<target>/index.json`
- [ ] The pull request explains a concrete use, the novel delta, and all parent contributions
