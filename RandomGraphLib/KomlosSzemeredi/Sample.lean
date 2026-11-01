/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.KomlosSzemeredi.Far
public import RandomGraphLib.KomlosSzemeredi.Dense
public import RandomGraphLib.KomlosSzemeredi.SparseUnion
public import PseudorandomLib.RandomGraphs.Coupling

/-!
# Komlós–Szemerédi, upper side: the sparse expander

Given `G` and an auxiliary graph `A ≤ G`, every vertex picks `min(deg v, D)` of its neighbours;
`Γ₀` is `A` together with the picked edges. It has at most `e(A) + n D` edges, small vertices keep
all their edges and the others at least `D`. If `G` has minimum degree two, its small vertices
are far apart and on no short cycle, its small sets are sparse, and the large sets of `A` expand,
then `Γ₀` is a connected expander (`exists_sparse_expander`). `G(n, p q)` is the intersection of
independent `G(n, p)` and `G(n, q)` (`pProb_coinPair_and`).
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Pseudorandom Pseudorandom.RandomGraphs

variable {n : ℕ}

/-- `G(n, p q)` is the intersection of independent `G(n, p)` and `G(n, q)`. -/
theorem pProb_coinPair_and (p q : ℝ) (n : ℕ) (S : (Pairs n → Bool) → Prop) :
    pProb (coinPair p q n) (fun ω => S (fun e => (ω e).1 && (ω e).2)) =
      pProb (coin (p * q) n) S := by
  refine pProb_map (coin (p * q) n) (coinPair p q n) (fun x => x.1 && x.2)
    (fun e a => ?_) S
  cases a
  · simp [coinPair, coin, Fintype.sum_prod_type]
    ring
  · simp [coinPair, coin, Fintype.sum_prod_type]

/-- `D` of the neighbours of `v`, or all of them if there are fewer. -/
noncomputable def pick (G : SimpleGraph (Fin n)) (D : ℕ) (v : Fin n) : Finset (Fin n) :=
  Classical.choose (exists_subset_card_eq (min_le_left (nbrs G v).card D))

theorem pick_subset (G : SimpleGraph (Fin n)) (D : ℕ) (v : Fin n) : pick G D v ⊆ nbrs G v :=
  (Classical.choose_spec (exists_subset_card_eq (min_le_left (nbrs G v).card D))).1

theorem card_pick (G : SimpleGraph (Fin n)) (D : ℕ) (v : Fin n) :
    (pick G D v).card = min (nbrs G v).card D :=
  (Classical.choose_spec (exists_subset_card_eq (min_le_left (nbrs G v).card D))).2

/-- The picked edges. -/
def pickGraph (G : SimpleGraph (Fin n)) (D : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun v w => w ∈ pick G D v

theorem pickGraph_le (G : SimpleGraph (Fin n)) (D : ℕ) : pickGraph G D ≤ G := by
  intro v w h
  rw [pickGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact mem_nbrs.1 (pick_subset G D v h)
  · exact (mem_nbrs.1 (pick_subset G D w h)).symm

open Classical in
/-- The pairs of a graph. -/
noncomputable def pairsOf (Γ : SimpleGraph (Fin n)) : Finset (Pairs n) :=
  univ.filter fun e => e.1 ∈ Γ.edgeSet

theorem mem_pairsOf {Γ : SimpleGraph (Fin n)} {e : Pairs n} : e ∈ pairsOf Γ ↔ e.1 ∈ Γ.edgeSet := by
  classical
  simp [pairsOf]

theorem setGraph_pairsOf (Γ : SimpleGraph (Fin n)) : setGraph (pairsOf Γ) = Γ := by
  classical
  ext u v
  simp only [setGraph, graphOf_adj, pairsOf, mem_filter, mem_univ, true_and, decide_eq_true_eq,
    SimpleGraph.mem_edgeSet]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Γ.ne_of_adj h, h⟩⟩

theorem card_pairsOf_sup (Γ Γ' : SimpleGraph (Fin n)) :
    (pairsOf (Γ ⊔ Γ')).card ≤ (pairsOf Γ).card + (pairsOf Γ').card := by
  classical
  refine (card_le_card fun e he => ?_).trans (card_union_le _ _)
  simp only [pairsOf, mem_filter, mem_univ, true_and, SimpleGraph.edgeSet_sup, Set.mem_union,
    mem_union] at he ⊢
  exact he

theorem pairsOf_graphOf (ω : Pairs n → Bool) :
    pairsOf (graphOf ω) = univ.filter fun e => ω e = true := by
  ext e
  obtain ⟨u, v, huv⟩ := exists_eq_sym2_mk e.1
  simp only [pairsOf, mem_filter, mem_univ, true_and, huv, SimpleGraph.mem_edgeSet]
  exact graphOf_adj_iff ω e u v huv

theorem card_pairsOf_pickGraph (G : SimpleGraph (Fin n)) (D : ℕ) :
    (pairsOf (pickGraph G D)).card ≤ n * D := by
  classical
  calc (pairsOf (pickGraph G D)).card ≤ (univ.sigma (pick G D)).card := by
        refine card_le_card_of_forall_subsingleton (fun e x => e.1 = s(x.1, x.2))
          (fun e he => ?_) ?_
        · obtain ⟨a, b, hab⟩ := exists_eq_sym2_mk e.1
          have h := mem_pairsOf.1 he
          rw [hab, SimpleGraph.mem_edgeSet, pickGraph, SimpleGraph.fromRel_adj] at h
          rcases h.2 with h' | h'
          · exact ⟨⟨a, b⟩, mem_sigma.2 ⟨mem_univ _, h'⟩, hab⟩
          · exact ⟨⟨b, a⟩, mem_sigma.2 ⟨mem_univ _, h'⟩, hab.trans Sym2.eq_swap⟩
        · intro x _ e he e' he'
          exact Subtype.ext (he.2.trans he'.2.symm)
    _ = ∑ v, (pick G D v).card := card_sigma _ _
    _ ≤ ∑ _v : Fin n, D := sum_le_sum fun v _ => (card_pick G D v).trans_le (min_le_right _ _)
    _ = n * D := by simp

/-- **The sparse expander.** -/
theorem exists_sparse_expander (ω ωA : Pairs n → Bool) (hA : ∀ e, ωA e = true → ω e = true)
    (h8 : 8 ≤ n) {D s₀ u₀ mA : ℕ} (hD : 1 ≤ D) (h4 : 4 * s₀ ≤ u₀)
    (hdeg : ∀ v, ¬ IsSmall (graphOf ω) 2 v) (hnear : ¬ NearSmall (graphOf ω) D)
    (hcyc : ¬ CycleSmall (graphOf ω) D)
    (hdense : ¬ ∃ U : Finset (Fin n), U.card ≤ u₀ ∧ D * U.card < 6 * eIn (graphOf ω) U)
    (hlarge : ¬ ∃ S : Finset (Fin n), s₀ ≤ S.card ∧ S.card ≤ n / 4 ∧
      (nbhd (graphOf ωA) S \ S).card < 2 * S.card)
    (hmany : ¬ mA ≤ (univ.filter fun e => ωA e = true).card) :
    ∃ F : Finset (Pairs n), F.card ≤ mA + n * D ∧ (∀ e ∈ F, ω e = true) ∧
      (setGraph F).Connected ∧ IsExpander (setGraph F) (n / 4) := by
  classical
  set G := graphOf ω with hG
  set A := graphOf ωA with hAdef
  set Γ := A ⊔ pickGraph G D with hΓ
  have hAG : A ≤ G := graphOf_mono hA
  have hΓG : Γ ≤ G := sup_le hAG (pickGraph_le G D)
  have hAΓ : A ≤ Γ := le_sup_left
  have hexp : IsExpander Γ (n / 4) := by
    refine isExpander_of_small hΓG (s₀ := s₀) (u₀ := u₀) hD (fun v => ?_) (fun v hv w hvw => ?_)
      (fun v hv => ?_) (fun x y hx hy hxy w => ?_) (fun x a b hx hl hbx => ?_)
      (fun x a b c hx hl hcx => ?_) (fun U hU => ?_) (fun S hS1 hS2 => ?_) h4
    · have := hdeg v
      unfold IsSmall at this
      omega
    · have hpick : pick G D v = nbrs G v := by
        refine eq_of_subset_of_card_le (pick_subset G D v) ?_
        rw [card_pick]
        unfold IsSmall at hv
        omega
      refine (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr ?_)
      rw [pickGraph, SimpleGraph.fromRel_adj]
      exact ⟨G.ne_of_adj hvw, Or.inl (hpick ▸ mem_nbrs.2 hvw)⟩
    · have hsub : pick G D v ⊆ nbrs Γ v := by
        intro w hw
        have hvw : G.Adj v w := mem_nbrs.1 (pick_subset G D v hw)
        refine mem_nbrs.2 ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr ?_))
        rw [pickGraph, SimpleGraph.fromRel_adj]
        exact ⟨G.ne_of_adj hvw, Or.inl hw⟩
      have := card_le_card hsub
      rw [card_pick] at this
      unfold IsSmall at hv
      omega
    · by_contra hlt
      exact hnear ⟨x, y, hx, hy, hxy, w, by omega⟩
    · exact hcyc ⟨x, hx, Or.inl ⟨a, b, hl, hbx⟩⟩
    · exact hcyc ⟨x, hx, Or.inr ⟨a, b, c, hl, hcx⟩⟩
    · by_contra hlt
      exact hdense ⟨U, hU, by omega⟩
    · by_contra hlt
      push Not at hlt
      refine hlarge ⟨S, hS1, hS2, lt_of_le_of_lt ?_ hlt⟩
      exact card_le_card (sdiff_subset_sdiff (fun y hy => by
        obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 hy
        exact mem_nbhd.2 ⟨x, hx, hAΓ hxy⟩) (subset_refl _))
  refine ⟨pairsOf Γ, ?_, fun e he => ?_, ?_, ?_⟩
  · refine (card_pairsOf_sup A (pickGraph G D)).trans ?_
    have h1 := card_pairsOf_pickGraph G D
    have h2 : (pairsOf A).card < mA := by
      rw [hAdef, pairsOf_graphOf]
      exact Nat.lt_of_not_le hmany
    omega
  · have h := mem_pairsOf.1 he
    obtain ⟨u, v, huv⟩ := exists_eq_sym2_mk e.1
    rw [huv, SimpleGraph.mem_edgeSet] at h
    exact (graphOf_adj_iff ω e u v huv).1 (hΓG h)
  · rw [setGraph_pairsOf]
    exact connected_of_isExpander (by simpa using h8) (by simpa using hexp)
  · rw [setGraph_pairsOf]
    exact hexp

end RandomGraphLib
