/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Defs

/-!
# The finite product model of `G(n, p)` agrees with Mathlib's `binomialRandom`

`Pseudorandom.RandomGraphs.gnpProb n p Q` is the probability that `G(n, p)` has property `Q` in
the finite product model (one independent `Bernoulli(p)` coin per pair of distinct vertices of
`Fin n`). Mathlib defines the binomial random graph as a probability measure
`SimpleGraph.binomialRandom V p` (notation `G(V, p)`) on `SimpleGraph V`.

* `graphEquiv`: coin outcomes and graphs on `Fin n` are in bijection (`ω ↦ graphOf ω`);
* `gnpProb_eq_sum`: `gnpProb n p Q = ∑_{G ⊨ Q} p ^ e(G) (1 - p) ^ (C(n, 2) - e(G))`;
* `binomialRandom_real_eq_sum`: the same sum computes `G(Fin n, p)` of the event;
* `gnpProb_eq_binomialRandom`: hence `gnpProb n p Q = G(Fin n, p).real {G | Q G}` for
  `0 ≤ p ≤ 1`. Every statement about `gnpProb` is a statement about Mathlib's random graph.
-/

@[expose] public section

open Finset MeasureTheory unitInterval
open scoped SimpleGraph

namespace RandomGraphLib

open Pseudorandom Pseudorandom.RandomGraphs

variable {n : ℕ}

/-- The number of edges of a graph on `Fin n`. -/
noncomputable def numEdges (G : SimpleGraph (Fin n)) : ℕ := G.edgeSet.ncard

/-- The probability weight of one graph in `G(n, p)`. -/
noncomputable def graphWeight (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  p ^ numEdges G * (1 - p) ^ (n.choose 2 - numEdges G)

theorem mem_edgeSet_graphOf (ω : Pairs n → Bool) (e : Pairs n) :
    e.1 ∈ (graphOf ω).edgeSet ↔ ω e = true := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v => exact graphOf_adj_iff ω ⟨s(u, v), he⟩ u v rfl

/-- Coin outcomes and graphs on `Fin n` are in bijection. -/
noncomputable def graphEquiv (n : ℕ) : (Pairs n → Bool) ≃ SimpleGraph (Fin n) where
  toFun := graphOf
  invFun G e := @decide (e.1 ∈ G.edgeSet) (Classical.dec _)
  left_inv ω := by
    funext e
    have := mem_edgeSet_graphOf ω e
    by_cases h : ω e = true <;> simp_all
  right_inv G := by
    ext u v
    rw [graphOf_adj]
    constructor
    · rintro ⟨_, h⟩
      simpa using h
    · intro h
      exact ⟨G.ne_of_adj h, by simpa using h⟩

@[simp] theorem graphEquiv_apply (ω : Pairs n → Bool) : graphEquiv n ω = graphOf ω := rfl

theorem edgeSet_graphOf (ω : Pairs n → Bool) :
    (graphOf ω).edgeSet = Subtype.val '' {e : Pairs n | ω e = true} := by
  ext e
  constructor
  · intro h
    have hd : ¬ e.IsDiag := (graphOf ω).not_isDiag_of_mem_edgeSet h
    exact ⟨⟨e, hd⟩, (mem_edgeSet_graphOf ω ⟨e, hd⟩).1 h, rfl⟩
  · rintro ⟨e', he', rfl⟩
    exact (mem_edgeSet_graphOf ω e').2 he'

theorem numEdges_graphOf (ω : Pairs n → Bool) :
    numEdges (graphOf ω) = #(univ.filter fun e => ω e = true) := by
  rw [numEdges, edgeSet_graphOf, Set.ncard_image_of_injective _ Subtype.val_injective,
    ← Set.ncard_coe_finset]
  simp

theorem card_pairs (n : ℕ) : Fintype.card (Pairs n) = n.choose 2 := by
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin]

theorem pw_coin (p : ℝ) (ω : Pairs n → Bool) : pw (coin p n) ω = graphWeight p (graphOf ω) := by
  classical
  rw [pw, graphWeight, numEdges_graphOf]
  simp only [coin]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := univ) (fun e : Pairs n => ω e = true)
  rw [card_univ, card_pairs] at this
  omega

/-- `P(G(n, p) ⊨ Q)` as a sum of graph weights. -/
theorem gnpProb_eq_sum (p : ℝ) (Q : SimpleGraph (Fin n) → Prop) [DecidablePred Q] :
    gnpProb n p Q = ∑ G ∈ univ.filter Q, graphWeight p G := by
  classical
  rw [gnpProb, pProb, pE, Finset.sum_filter, ← (graphEquiv n).sum_comp]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [pw_coin, graphEquiv_apply]
  split_ifs <;> simp

/-- Singletons of `SimpleGraph V` are measurable when `V` is countable. -/
instance measurableSingletonClass_simpleGraph {V : Type*} [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) := by
  refine ⟨fun G => ?_⟩
  have h : ({G} : Set (SimpleGraph V)) = SimpleGraph.Adj ⁻¹' {G.Adj} :=
    Set.ext fun H => ⟨fun h => by rw [Set.mem_singleton_iff.1 h]; rfl,
      fun h => Set.mem_singleton_iff.2 (SimpleGraph.ext h)⟩
  rw [h]
  exact SimpleGraph.measurable_adj (measurableSet_singleton _)

/-- Mathlib's `G(Fin n, p)` of an event, as a sum of graph weights. -/
theorem binomialRandom_real_eq_sum (p : I) (S : Set (SimpleGraph (Fin n))) [DecidablePred (· ∈ S)] :
    (SimpleGraph.binomialRandom (Fin n) p).real S =
      ∑ G ∈ univ.filter (· ∈ S), graphWeight (p : ℝ) G := by
  have hS : (SimpleGraph.binomialRandom (Fin n) p).real S =
      (SimpleGraph.binomialRandom (Fin n) p).real ↑(univ.filter (· ∈ S)) := by
    congr 1; ext; simp
  rw [hS, measureReal_def, ← MeasureTheory.sum_measure_singleton, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun G _ => ?_
    rw [SimpleGraph.binomialRandom_singleton, graphWeight, numEdges, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    simp [unitInterval.coe_symm_eq]
  · exact fun G _ => measure_ne_top _ _

/-- **The bridge.** For `0 ≤ p ≤ 1`, the finite product model and Mathlib's binomial random graph
give every property the same probability. -/
theorem gnpProb_eq_binomialRandom {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (Q : SimpleGraph (Fin n) → Prop) :
    gnpProb n p Q = (SimpleGraph.binomialRandom (Fin n) ⟨p, h0, h1⟩).real {G | Q G} := by
  classical
  rw [gnpProb_eq_sum, binomialRandom_real_eq_sum]
  rfl

end RandomGraphLib
