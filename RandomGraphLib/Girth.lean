/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.Mathlib
public import GirthLib.ErdosGirthAux

/-!
# The edge-set model of the Erdős girth formalization is `G(n, p)`

The formalization of Erdős' girth–chromatic theorem (`GirthLib`, namespace `ErdosGirth`) weighs an
edge set `S ⊆ pairs m` by `wt m p S = p ^ |S| (1 - p) ^ (|pairs m| - |S|)` and sums over
`(pairs m).powerset`. `sum_wt_eq_gnpProb` identifies these sums with `gnpProb`, hence (by
`gnpProb_eq_binomialRandom`) with Mathlib's `G(Fin m, p)`.
-/

@[expose] public section

open Finset

namespace RandomGraphLib

open Pseudorandom.RandomGraphs ErdosGirth

variable {m : ℕ}

theorem edgeFinset_subset_pairs (G : SimpleGraph (Fin m)) [Fintype G.edgeSet] :
    G.edgeFinset ⊆ pairs m := by
  intro e he
  simp only [pairs, mem_filter, mem_univ, true_and]
  exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he)

theorem edgeSet_gr {S : Finset (Sym2 (Fin m))} (hS : S ⊆ pairs m) :
    (gr S).edgeSet = S := by
  rw [gr, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, mem_coe, and_iff_left_iff_imp]
  intro he
  have := hS he
  simp only [pairs, mem_filter, mem_univ, true_and] at this
  exact this

theorem card_pairs_eq (m : ℕ) : #(pairs m) = m.choose 2 := by
  rw [← card_pairs m, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun e => by simp [pairs])

theorem wt_eq_graphWeight (p : ℝ) {S : Finset (Sym2 (Fin m))} (hS : S ⊆ pairs m) :
    wt m p S = graphWeight p (gr S) := by
  have hn : numEdges (gr S) = #S := by
    rw [numEdges, edgeSet_gr hS, Set.ncard_coe_finset]
  rw [wt, graphWeight, hn, prod_const, prod_const, card_sdiff_of_subset hS, card_pairs_eq]

/-- Sums of `ErdosGirth.wt` over edge sets are probabilities in `G(m, p)`. -/
theorem sum_wt_eq_gnpProb (p : ℝ) (Q : SimpleGraph (Fin m) → Prop) [DecidablePred Q] :
    ∑ S ∈ (pairs m).powerset.filter (fun S => Q (gr S)), wt m p S = gnpProb m p Q := by
  classical
  rw [gnpProb_eq_sum]
  refine Finset.sum_nbij' gr (fun G => G.edgeFinset) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    simpa using hS.2
  · intro G hG
    simp only [mem_filter, mem_univ, true_and] at hG
    simp only [mem_filter, mem_powerset]
    refine ⟨edgeFinset_subset_pairs G, ?_⟩
    rwa [gr, SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    ext e
    rw [SimpleGraph.mem_edgeFinset, edgeSet_gr hS.1, mem_coe]
  · intro G _
    rw [gr, SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    exact wt_eq_graphWeight p hS.1

end RandomGraphLib
