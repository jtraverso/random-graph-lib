/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Rotation

/-!
# Komlós–Szemerédi, upper side: expansion of a sparse subgraph

Let `Γ ≤ G`. Call a vertex *small* if it has fewer than `D` neighbours in `G`. Suppose that every
vertex of `G` has at least two neighbours, that small vertices keep all their edges in `Γ` and the
other vertices keep at least `D`, that two small vertices are at distance at least five in `G`,
that no small vertex lies on a cycle of length three or four, that every set `U` of at most `u₀`
vertices spans at most `D |U| / 12` edges of `G`, and that every set of between `s₀ ≥ u₀ / 4`
and `k` vertices expands by a factor two in `Γ`. Then every set of at most `k` vertices expands by
a factor two in `Γ` (`isExpander_of_small`). A graph on at least eight vertices in which every set
of at most a quarter of the vertices expands by a factor two is connected
(`connected_of_isExpander`).
-/

@[expose] public section

namespace RandomGraphLib

open Finset Pseudorandom.RandomGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

open Classical in
/-- The neighbours of `v`. -/
noncomputable def nbrs (G : SimpleGraph V) (v : V) : Finset V := univ.filter (G.Adj v)

open Classical in
/-- The ordered pairs of adjacent vertices of `U`. -/
noncomputable def eIn (G : SimpleGraph V) (U : Finset V) : ℕ :=
  ((U ×ˢ U).filter fun x => G.Adj x.1 x.2).card

/-- `v` has fewer than `D` neighbours. -/
def IsSmall (G : SimpleGraph V) (D : ℕ) (v : V) : Prop := (nbrs G v).card < D

theorem mem_nbrs {G : SimpleGraph V} {v w : V} : w ∈ nbrs G v ↔ G.Adj v w := by
  classical
  simp [nbrs]

theorem mem_nbhd {G : SimpleGraph V} {S : Finset V} {y : V} :
    y ∈ nbhd G S ↔ ∃ x ∈ S, G.Adj x y := by
  classical
  simp [nbhd]

theorem nbhd_subset_of_subset {G : SimpleGraph V} {S T : Finset V} (h : S ⊆ T) :
    nbhd G S ⊆ nbhd G T := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 hy
  exact mem_nbhd.2 ⟨x, h hx, hxy⟩

theorem eIn_mono {G H : SimpleGraph V} (h : G ≤ H) (U : Finset V) : eIn G U ≤ eIn H U := by
  classical
  unfold eIn
  refine card_le_card fun x hx => ?_
  simp only [mem_filter] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

theorem exists_walk_le_one {G : SimpleGraph V} {y z : V} (h : y = z ∨ G.Adj y z) :
    ∃ w : G.Walk y z, w.length ≤ 1 := by
  rcases h with rfl | h
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · exact ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil, by simp⟩

/-- Neighbours of the vertices of `S` inside a set `U ⊇ S ∪ N(S)`, counted with order. -/
theorem sum_card_nbrs_le_eIn {G : SimpleGraph V} {S U : Finset V} (hS : S ⊆ U)
    (hN : nbhd G S ⊆ U) : ∑ v ∈ S, (nbrs G v).card ≤ eIn G U := by
  classical
  rw [← card_sigma]
  unfold eIn
  refine card_le_card_of_injOn (fun x => (x.1, x.2)) (fun x hx => ?_) ?_
  · simp only [mem_coe, mem_sigma, mem_nbrs] at hx
    simp only [mem_coe, mem_filter, mem_product]
    exact ⟨⟨hS hx.1, hN (mem_nbhd.2 ⟨x.1, hx.1, hx.2⟩)⟩, hx.2⟩
  · rintro ⟨a, b⟩ - ⟨a', b'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- **Expansion of the sparse subgraph.** -/
theorem isExpander_of_small {G Γ : SimpleGraph V} (hΓ : Γ ≤ G) {D k s₀ u₀ : ℕ} (hD : 1 ≤ D)
    (hdeg : ∀ v, 2 ≤ (nbrs G v).card)
    (hsm : ∀ v, IsSmall G D v → ∀ w, G.Adj v w → Γ.Adj v w)
    (hbig : ∀ v, ¬ IsSmall G D v → D ≤ (nbrs Γ v).card)
    (hfar : ∀ x y, IsSmall G D x → IsSmall G D y → x ≠ y → ∀ w : G.Walk x y, 5 ≤ w.length)
    (hcyc3 : ∀ x a b, IsSmall G D x → IsPathList G [x, a, b] → ¬ G.Adj b x)
    (hcyc4 : ∀ x a b c, IsSmall G D x → IsPathList G [x, a, b, c] → ¬ G.Adj c x)
    (hsparse : ∀ U : Finset V, U.card ≤ u₀ → 6 * eIn G U ≤ D * U.card)
    (hlarge : ∀ S : Finset V, s₀ ≤ S.card → S.card ≤ k → 2 * S.card ≤ (nbhd Γ S \ S).card)
    (h4 : 4 * s₀ ≤ u₀) : IsExpander Γ k := by
  classical
  intro S hSk
  by_cases hs : s₀ ≤ S.card
  · exact hlarge S hs hSk
  push Not at hs
  have hSu : 4 * S.card ≤ u₀ := by omega
  -- two small vertices are not adjacent and have no common neighbour
  have hnadj : ∀ x y, IsSmall G D x → IsSmall G D y → ¬ G.Adj x y := by
    intro x y hx hy hxy
    have := hfar x y hx hy (G.ne_of_adj hxy) (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil)
    simp at this
  have hcommon : ∀ x x' y, IsSmall G D x → IsSmall G D x' → G.Adj x y → G.Adj x' y → x = x' := by
    intro x x' y hx hx' hxy hx'y
    by_contra hne
    have := hfar x x' hx hx' hne
      (SimpleGraph.Walk.cons hxy (SimpleGraph.Walk.cons hx'y.symm SimpleGraph.Walk.nil))
    simp at this
  set S1 := S.filter (IsSmall G D) with hS1
  set S2 := S.filter (fun v => ¬ IsSmall G D v) with hS2
  have hS : S1.card + S2.card = S.card := card_filter_add_card_filter_not _
  have hS1S : S1 ⊆ S := filter_subset _ _
  have hS2S : S2 ⊆ S := filter_subset _ _
  have hmem1 : ∀ x ∈ S1, IsSmall G D x := fun x hx => (mem_filter.1 hx).2
  have hmem2 : ∀ x ∈ S2, ¬ IsSmall G D x := fun x hx => (mem_filter.1 hx).2
  have hsplit : ∀ x ∈ S, IsSmall G D x → x ∈ S1 := fun x hx h => mem_filter.2 ⟨hx, h⟩
  have hsplit' : ∀ x ∈ S, ¬ IsSmall G D x → x ∈ S2 := fun x hx h => mem_filter.2 ⟨hx, h⟩
  set U2 := S2 ∪ nbhd Γ S2 with hU2
  -- (A) the closed neighbourhood of the big vertices of `S` is large
  have hA : 6 * S2.card ≤ U2.card ∨ u₀ < U2.card := by
    by_cases hU : U2.card ≤ u₀
    · left
      have h1 : D * S2.card ≤ eIn Γ U2 := by
        calc D * S2.card = ∑ _v ∈ S2, D := by rw [sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ v ∈ S2, (nbrs Γ v).card := sum_le_sum fun v hv => hbig v (hmem2 v hv)
          _ ≤ eIn Γ U2 := sum_card_nbrs_le_eIn subset_union_left subset_union_right
      have h2 := eIn_mono hΓ U2
      have h3 := hsparse U2 hU
      have : D * (6 * S2.card) ≤ D * U2.card := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (by omega)
    · right; omega
  -- (B) the part `Z = U2 \ S` of `N(S) \ S`
  have hB1 : U2 ∩ S ⊆ S2 ∪ (nbhd Γ S2 ∩ S1) := by
    intro y hy
    obtain ⟨hyU, hyS⟩ := mem_inter.1 hy
    by_cases hsy : IsSmall G D y
    · rcases mem_union.1 hyU with h | h
      · exact absurd hsy (hmem2 y h)
      · exact mem_union_right _ (mem_inter.2 ⟨h, hsplit y hyS hsy⟩)
    · exact mem_union_left _ (hsplit' y hyS hsy)
  have hB2 : (nbhd Γ S2 ∩ S1).card ≤ S2.card := by
    refine card_le_card_of_forall_subsingleton (fun x z => Γ.Adj z x) (fun x hx => ?_) ?_
    · obtain ⟨z, hz, hzx⟩ := mem_nbhd.1 (mem_inter.1 hx).1
      exact ⟨z, hz, hzx⟩
    · intro z hz x hx x' hx'
      have h1 := mem_inter.1 (mem_coe.1 hx.1)
      have h1' := mem_inter.1 (mem_coe.1 hx'.1)
      exact hcommon x x' z (hmem1 x h1.2) (hmem1 x' h1'.2) (hΓ hx.2).symm (hΓ hx'.2).symm
  have hZ : U2.card ≤ (U2 \ S).card + 2 * S2.card := by
    have h1 := card_sdiff_add_card_inter U2 S
    have h2 := (card_le_card hB1).trans (card_union_le _ _)
    omega
  -- (C) the part `Y = N(S1) \ U2`
  have hC1 : 2 * S1.card ≤ (nbhd Γ S1).card := by
    have hsub : S1.biUnion (nbrs G) ⊆ nbhd Γ S1 := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_biUnion.1 hy
      exact mem_nbhd.2 ⟨x, hx, hsm x (hmem1 x hx) y (mem_nbrs.1 hxy)⟩
    have hdisj : (S1 : Set V).PairwiseDisjoint (nbrs G) := by
      intro x hx x' hx' hne
      rw [Function.onFun, disjoint_left]
      intro y hy hy'
      exact hne (hcommon x x' y (hmem1 x hx) (hmem1 x' hx') (mem_nbrs.1 hy) (mem_nbrs.1 hy'))
    calc 2 * S1.card = ∑ _x ∈ S1, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ S1, (nbrs G x).card := sum_le_sum fun x _ => hdeg x
      _ = (S1.biUnion (nbrs G)).card := (card_biUnion hdisj).symm
      _ ≤ (nbhd Γ S1).card := card_le_card hsub
  have hC2 : (nbhd Γ S1 ∩ U2).card ≤ S2.card := by
    refine card_le_card_of_forall_subsingleton (fun y z => y = z ∨ Γ.Adj z y)
      (fun y hy => ?_) ?_
    · rcases mem_union.1 (mem_inter.1 hy).2 with h | h
      · exact ⟨y, h, Or.inl rfl⟩
      · obtain ⟨z, hz, hzy⟩ := mem_nbhd.1 h
        exact ⟨z, hz, Or.inr hzy⟩
    · intro z hz y hy y' hy'
      have hy1 := (mem_inter.1 (mem_coe.1 hy.1)).1
      have hy1' := (mem_inter.1 (mem_coe.1 hy'.1)).1
      have hyz : y = z ∨ Γ.Adj z y := hy.2
      have hyz' : y' = z ∨ Γ.Adj z y' := hy'.2
      obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 hy1
      obtain ⟨x', hx', hxy'⟩ := mem_nbhd.1 hy1'
      have hsx := hmem1 x hx
      have hsx' := hmem1 x' hx'
      have hbz := hmem2 z hz
      have hxz : x ≠ z := fun h => hbz (h ▸ hsx)
      by_contra hne
      by_cases hxx : x = x'
      · subst hxx
        have hGxy := hΓ hxy
        have hGxy' := hΓ hxy'
        rcases hyz with rfl | hzy <;> rcases hyz' with rfl | hzy'
        · exact hne rfl
        · refine hcyc3 x y y' hsx ⟨?_, ?_⟩ hGxy'.symm
          · simp [G.ne_of_adj hGxy, G.ne_of_adj hGxy', hne]
          · simp [List.isChain_cons_cons, hGxy, hΓ hzy']
        · refine hcyc3 x y' y hsx ⟨?_, ?_⟩ hGxy.symm
          · simp [G.ne_of_adj hGxy, G.ne_of_adj hGxy', Ne.symm hne]
          · simp [List.isChain_cons_cons, hGxy', hΓ hzy]
        · have hGzy := hΓ hzy
          have hGzy' := hΓ hzy'
          refine hcyc4 x y z y' hsx ⟨?_, ?_⟩ hGxy'.symm
          · simp [G.ne_of_adj hGxy, G.ne_of_adj hGxy', hne, hxz, (G.ne_of_adj hGzy).symm,
              G.ne_of_adj hGzy']
          · simp [List.isChain_cons_cons, hGxy, hGzy.symm, hGzy']
      · obtain ⟨w1, hw1⟩ := exists_walk_le_one (G := G)
          (hyz.imp id fun h => (hΓ h).symm)
        obtain ⟨w2, hw2⟩ := exists_walk_le_one (G := G)
          (hyz'.imp id fun h => (hΓ h).symm)
        have := hfar x x' hsx hsx' hxx (SimpleGraph.Walk.cons (hΓ hxy) (w1.append
          (w2.reverse.append (SimpleGraph.Walk.cons (hΓ hxy').symm SimpleGraph.Walk.nil))))
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append,
          SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_nil] at this
        omega
  have hY : (nbhd Γ S1).card ≤ (nbhd Γ S1 \ U2).card + S2.card := by
    have := card_sdiff_add_card_inter (nbhd Γ S1) U2
    omega
  -- (D) `Y` and `Z` are disjoint parts of `N(S) \ S`
  have hYsub : nbhd Γ S1 \ U2 ⊆ nbhd Γ S \ S := by
    intro y hy
    obtain ⟨hy1, hyU⟩ := mem_sdiff.1 hy
    refine mem_sdiff.2 ⟨nbhd_subset_of_subset hS1S hy1, fun hyS => ?_⟩
    obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 hy1
    by_cases hsy : IsSmall G D y
    · exact hnadj x y (hmem1 x hx) hsy (hΓ hxy)
    · exact hyU (mem_union_left _ (hsplit' y hyS hsy))
  have hZsub : U2 \ S ⊆ nbhd Γ S \ S := by
    intro z hz
    obtain ⟨hzU, hzS⟩ := mem_sdiff.1 hz
    refine mem_sdiff.2 ⟨?_, hzS⟩
    rcases mem_union.1 hzU with h | h
    · exact absurd (hS2S h) hzS
    · exact nbhd_subset_of_subset hS2S h
  have hYZ : Disjoint (nbhd Γ S1 \ U2) (U2 \ S) := by
    rw [disjoint_left]
    intro y hy hy'
    exact (mem_sdiff.1 hy).2 (mem_sdiff.1 hy').1
  have hfin : (nbhd Γ S1 \ U2).card + (U2 \ S).card ≤ (nbhd Γ S \ S).card := by
    rw [← card_union_of_disjoint hYZ]
    exact card_le_card (union_subset hYsub hZsub)
  rcases hA with hA | hA <;> omega

/-- A graph on at least eight vertices in which every set of at most a quarter of the vertices
expands by a factor two is connected. -/
theorem connected_of_isExpander {Γ : SimpleGraph V} (h8 : 8 ≤ Fintype.card V)
    (h : IsExpander Γ (Fintype.card V / 4)) : Γ.Connected := by
  classical
  set k := Fintype.card V / 4 with hk
  have hcomp : ∀ u, 3 * k ≤ (univ.filter (Γ.Reachable u)).card := by
    intro u
    set C := univ.filter (Γ.Reachable u) with hC
    have hclosed : nbhd Γ C ⊆ C := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 hy
      simp only [hC, mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.trans hxy.reachable
    have huC : u ∈ C := by simp [hC]
    have hCk : k < C.card := by
      by_contra hle
      push Not at hle
      have := h C hle
      rw [sdiff_eq_empty_iff_subset.2 hclosed, card_empty] at this
      have : C.card = 0 := by omega
      exact absurd (card_eq_zero.1 this ▸ huC) (by simp)
    obtain ⟨S, hSC, hScard⟩ := exists_subset_card_eq hCk.le
    have h2 := h S hScard.le
    have hsub : nbhd Γ S \ S ⊆ C \ S :=
      sdiff_subset_sdiff ((nbhd_subset_of_subset hSC).trans hclosed) (subset_refl _)
    have := card_le_card hsub
    rw [card_sdiff_of_subset hSC] at this
    omega
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  refine (SimpleGraph.connected_iff_exists_forall_reachable Γ).2 ⟨v, fun w => ?_⟩
  by_contra hvw
  have hdisj : Disjoint (univ.filter (Γ.Reachable v)) (univ.filter (Γ.Reachable w)) := by
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_filter, mem_univ, true_and] at hx hx'
    exact hvw (hx.trans hx'.symm)
  have := card_union_of_disjoint hdisj
  have hle := card_le_univ (univ.filter (Γ.Reachable v) ∪ univ.filter (Γ.Reachable w))
  have h1 := hcomp v
  have h2 := hcomp w
  omega

end RandomGraphLib
