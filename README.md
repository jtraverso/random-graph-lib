# RandomGraphLib: random graphs and finite product probability in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

The single source for the random-graph infrastructure of the author's Lean formalizations. New
developments should copy these files unchanged (or depend on this repository at a pinned commit)
instead of keeping private variants. Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, module system.

## Contents

| Path | What it provides | Origin |
|---|---|---|
| `PseudorandomLib/FiniteProb.lean` | Finite product probability spaces: weights, expectation, probability, union bound, Markov, cylinders, complements, transport along equivalences | Ehard–Glock–Joos formalization (PALOMAR-2026-10-17-000004), byte-identical |
| `PseudorandomLib/RandomGraphs/` | `G(n, p)` on `Fin n` (`Pairs`, `coin`, `graphOf`, `gnpProb`), monotone coupling in `p`, expansion, Pósa rotations, boosters, two-round exposure, isolated vertices (second moment), connectivity threshold, Pósa's theorem (`posa`, `posa_eighty`) | jtraverso/random-graph-thresholds @ 86325fa, byte-identical |
| `GirthLib/ErdosGirthAux.lean` | The edge-set weighting `ErdosGirth.wt` of the Erdős girth–chromatic formalization | jtraverso/erdos-girth-chromatic @ 05407c1 (PALOMAR-2026-10-17-000009), byte-identical |
| `RandomGraphLib/Mathlib.lean` | **Bridge to Mathlib**: `gnpProb n p Q = (SimpleGraph.binomialRandom (Fin n) p).real {G \| Q G}` (`gnpProb_eq_binomialRandom`), via the explicit graph weights `p ^ e(G) (1 - p) ^ (C(n, 2) - e(G))` | new |
| `RandomGraphLib/Girth.lean` | The Erdős edge-set sums are `gnpProb` (`sum_wt_eq_gnpProb`), hence Mathlib's `G(Fin n, p)` | new |

## Why the bridge matters

Mathlib defines the binomial random graph as a measure `G(V, p)` on `SimpleGraph V`
(`Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`) but proves no threshold
results about it. The proofs here work in the finite product model, where every probability is an
explicit finite sum; `gnpProb_eq_binomialRandom` transfers each result to Mathlib's measure, so
statements can be written in Mathlib's language.

## Building

```
lake build
```
