/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.KomlosSzemeredi.Expand
public import PseudorandomLib.RandomGraphs.Crossing
public import PseudorandomLib.RandomGraphs.Connectivity
public import PseudorandomLib.RandomGraphs.Round

/-!
# Komlós–Szemerédi, upper side: dense small sets and the auxiliary sample

* `pProb_dense_le`: the probability that some set `U` of at most `u₀` vertices of `G(n, p)` has
  `6 eIn(U) > D |U|` (more than `D |U| / 12` edges) is at most
  `∑_{u=1}^{u₀} C(n, u) C(u², ⌊D u / 12⌋ + 1) p^{⌊D u / 12⌋ + 1}`.
* `pProb_large_le`: the probability that some set `S` with `s₀ ≤ |S| ≤ n / 4` has fewer than
  `2 |S|` neighbours outside `S` is at most `∑_{s=s₀}^{n/4} C(n, s) C(n, 2 s) (1 - q)^{s (n - 3 s)}`.
* `pProb_many_le`: at least `m` pairs are present with probability at most `C(N, m) q^m`.
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Pseudorandom Pseudorandom.RandomGraphs

variable {n : ℕ}

/-- The pairs inside `U`. -/
def inPairs (U : Finset (Fin n)) : Finset (Pairs n) := univ.filter fun e => ∀ v ∈ e.1, v ∈ U

theorem card_inPairs_le (U : Finset (Fin n)) : (inPairs U).card ≤ U.card ^ 2 := by
  rw [sq, ← card_product]
  refine card_le_card_of_forall_subsingleton (fun e x => e.1 = s(x.1, x.2)) (fun e he => ?_) ?_
  · obtain ⟨a, b, hab⟩ := exists_eq_sym2_mk e.1
    have h := (mem_filter.1 he).2
    exact ⟨(a, b), mem_product.2 ⟨h a (by rw [hab]; exact Sym2.mem_mk_left _ _),
      h b (by rw [hab]; exact Sym2.mem_mk_right _ _)⟩, hab⟩
  · intro x _ e he e' he'
    exact Subtype.ext (he.2.trans he'.2.symm)

/-- Ordered adjacent pairs inside `U` are twice the present pairs inside `U`. -/
theorem eIn_graphOf_le (ω : Pairs n → Bool) (U : Finset (Fin n)) :
    eIn (graphOf ω) U ≤ 2 * ((inPairs U).filter fun e => ω e = true).card := by
  classical
  unfold eIn
  set P := (inPairs U).filter fun e => ω e = true with hP
  have h1 : ((U ×ˢ U).filter fun x => x.1 < x.2 ∧ (graphOf ω).Adj x.1 x.2).card ≤ P.card := by
    refine card_le_card_of_forall_subsingleton (fun x e => e.1 = s(x.1, x.2))
      (fun x hx => ?_) ?_
    · simp only [mem_filter, mem_product] at hx
      obtain ⟨⟨ha, hb⟩, -, hadj⟩ := hx
      obtain ⟨hne, hω⟩ := (graphOf_adj _ _ _).1 hadj
      refine ⟨⟨s(x.1, x.2), by simpa using hne⟩, ?_, rfl⟩
      simp only [hP, inPairs, mem_filter, mem_univ, true_and, Sym2.mem_iff]
      exact ⟨by rintro v (rfl | rfl) <;> assumption, hω⟩
    · intro e _ x hx y hy
      have l1 : x.1 < x.2 := (mem_filter.1 (mem_coe.1 hx.1)).2.1
      have l2 : y.1 < y.2 := (mem_filter.1 (mem_coe.1 hy.1)).2.1
      have he : s(x.1, x.2) = s(y.1, y.2) := hx.2.symm.trans hy.2
      rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext e1 e2
      · exact absurd l1 (by rw [e1, e2]; exact lt_asymm l2)
  have hsub : (U ×ˢ U).filter (fun x => (graphOf ω).Adj x.1 x.2) ⊆
      (U ×ˢ U).filter (fun x => x.1 < x.2 ∧ (graphOf ω).Adj x.1 x.2) ∪
        (U ×ˢ U).filter (fun x => x.2 < x.1 ∧ (graphOf ω).Adj x.1 x.2) := by
    intro x hx
    simp only [mem_filter, mem_union] at hx ⊢
    rcases lt_or_gt_of_ne ((graphOf ω).ne_of_adj hx.2) with h | h
    · exact Or.inl ⟨hx.1, h, hx.2⟩
    · exact Or.inr ⟨hx.1, h, hx.2⟩
  have h2 : ((U ×ˢ U).filter fun x => x.2 < x.1 ∧ (graphOf ω).Adj x.1 x.2).card ≤ P.card := by
    have : ((U ×ˢ U).filter fun x => x.2 < x.1 ∧ (graphOf ω).Adj x.1 x.2) =
        ((U ×ˢ U).filter fun x => x.1 < x.2 ∧ (graphOf ω).Adj x.1 x.2).map
          (Equiv.prodComm _ _).toEmbedding := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_map_equiv, Equiv.prodComm_symm,
        Equiv.prodComm_apply, Prod.swap_prod_mk]
      constructor
      · rintro ⟨⟨ha, hb⟩, h, hadj⟩; exact ⟨⟨hb, ha⟩, h, hadj.symm⟩
      · rintro ⟨⟨hb, ha⟩, h, hadj⟩; exact ⟨⟨ha, hb⟩, h, hadj.symm⟩
    rw [this, card_map]
    exact h1
  have := (card_le_card hsub).trans (card_union_le _ _)
  omega

/-- **Dense small sets.** -/
theorem pProb_dense_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u₀ D : ℕ) :
    gnpProb n p (fun G => ∃ U : Finset (Fin n), U.card ≤ u₀ ∧ D * U.card < 6 * eIn G U) ≤
      ∑ u ∈ Icc 1 u₀, (n.choose u : ℝ) *
        (((u ^ 2).choose (D * u / 12 + 1) : ℝ) * p ^ (D * u / 12 + 1)) := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  unfold gnpProb
  refine (pProb_mono hP (T := fun ω => ∃ u ∈ Icc 1 u₀,
      ∃ U ∈ powersetCard u (univ : Finset (Fin n)),
      ∃ J ∈ powersetCard (D * u / 12 + 1) (inPairs U), ∀ e ∈ J, ω e = true)
      fun ω h => ?_).trans ?_
  · obtain ⟨U, hU, hd⟩ := h
    have hb := eIn_graphOf_le ω U
    have hu1 : 1 ≤ U.card := by
      rcases Nat.eq_zero_or_pos U.card with h0 | h0
      · rw [h0] at hd
        simp at hd
        have : U = ∅ := card_eq_zero.1 h0
        subst this
        simp [eIn] at hd
      · exact h0
    have hm : D * U.card / 12 + 1 ≤ ((inPairs U).filter fun e => ω e = true).card := by omega
    obtain ⟨J, hJ, hJc⟩ := exists_subset_card_eq hm
    refine ⟨U.card, mem_Icc.2 ⟨hu1, hU⟩, U, mem_powersetCard.2 ⟨subset_univ _, rfl⟩, J,
      mem_powersetCard.2 ⟨hJ.trans (filter_subset _ _), hJc⟩, fun e he => ?_⟩
    exact (mem_filter.1 (hJ he)).2
  · refine (pProb_exists_le hP _ _).trans (sum_le_sum fun u hu => ?_)
    refine (pProb_exists_le hP _ _).trans ?_
    calc ∑ U ∈ powersetCard u (univ : Finset (Fin n)), pProb (coin p n) (fun ω =>
          ∃ J ∈ powersetCard (D * u / 12 + 1) (inPairs U), ∀ e ∈ J, ω e = true)
        ≤ ∑ _U ∈ powersetCard u (univ : Finset (Fin n)),
            ((u ^ 2).choose (D * u / 12 + 1) : ℝ) * p ^ (D * u / 12 + 1) := by
          refine sum_le_sum fun U hU => ?_
          have hUc := (mem_powersetCard.1 hU).2
          refine (pProb_exists_le hP _ _).trans ?_
          calc ∑ J ∈ powersetCard (D * u / 12 + 1) (inPairs U),
                pProb (coin p n) (fun ω => ∀ e ∈ J, ω e = true)
              = ∑ _J ∈ powersetCard (D * u / 12 + 1) (inPairs U),
                  p ^ (D * u / 12 + 1) := by
                refine sum_congr rfl fun J hJ => ?_
                have := pProb_coin_present_absent hp0 hp1 J ∅ (disjoint_empty_right _)
                simp only [card_empty, pow_zero, mul_one, notMem_empty, false_imp_iff,
                  imp_true_iff, and_true] at this
                rw [this, (mem_powersetCard.1 hJ).2]
            _ ≤ ((u ^ 2).choose (D * u / 12 + 1) : ℝ) * p ^ (D * u / 12 + 1) := by
                rw [sum_const, card_powersetCard, nsmul_eq_mul]
                refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hp0 _)
                exact_mod_cast Nat.choose_le_choose _ (hUc ▸ card_inPairs_le U)
      _ = (n.choose u : ℝ) * (((u ^ 2).choose (D * u / 12 + 1) : ℝ) * p ^ (D * u / 12 + 1)) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Large sets expand.** -/
theorem pProb_large_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s₀ : ℕ) :
    gnpProb n q (fun G => ∃ S : Finset (Fin n), s₀ ≤ S.card ∧ S.card ≤ n / 4 ∧
        (nbhd G S \ S).card < 2 * S.card) ≤
      ∑ s ∈ Icc s₀ (n / 4), (n.choose s : ℝ) * ((n.choose (2 * s) : ℝ) *
        (1 - q) ^ (s * (n - 3 * s))) := by
  classical
  have hP := coin_isPMF hq0 hq1 n
  unfold gnpProb
  refine (pProb_mono hP (T := fun ω => ∃ s ∈ Icc s₀ (n / 4),
      ∃ S ∈ powersetCard s (univ : Finset (Fin n)), ∃ T ∈ powersetCard (2 * s) (univ \ S),
        ∀ a ∈ S, ∀ b ∈ univ \ (S ∪ T), ¬ (graphOf ω).Adj a b) fun ω h => ?_).trans ?_
  · obtain ⟨S, hs0, hs4, hlt⟩ := h
    have h4 : 4 * S.card ≤ n := by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).1 hs4; omega
    have hcardc : (univ \ S).card = n - S.card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    obtain ⟨T, hNT, hT, hTcard⟩ := exists_subsuperset_card_eq
      (sdiff_subset_sdiff (subset_univ (nbhd (graphOf ω) S)) (subset_refl S)) hlt.le
      (by rw [hcardc]; omega)
    refine ⟨S.card, mem_Icc.2 ⟨hs0, hs4⟩, S, mem_powersetCard.2 ⟨subset_univ _, rfl⟩, T,
      mem_powersetCard.2 ⟨hT, hTcard⟩, fun a ha b hb hab => ?_⟩
    have hb' := (mem_sdiff.1 hb).2
    rw [mem_union, not_or] at hb'
    have : b ∈ nbhd (graphOf ω) S \ S := mem_sdiff.2 ⟨mem_nbhd.2 ⟨a, ha, hab⟩, hb'.1⟩
    exact hb'.2 (hNT this)
  · refine (pProb_exists_le hP _ _).trans (sum_le_sum fun s hs => ?_)
    have hs := mem_Icc.1 hs
    have h4 : 4 * s ≤ n := by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).1 hs.2; omega
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun S _ => pProb_exists_le hP _ _).trans ?_
    have hterm : ∀ S ∈ powersetCard s (univ : Finset (Fin n)),
        ∀ T ∈ powersetCard (2 * s) (univ \ S),
        pProb (coin q n) (fun ω => ∀ a ∈ S, ∀ b ∈ univ \ (S ∪ T), ¬ (graphOf ω).Adj a b) =
          (1 - q) ^ (s * (n - 3 * s)) := by
      intro S hS T hT
      have hS := mem_powersetCard.1 hS
      have hT := mem_powersetCard.1 hT
      have hdisj : Disjoint S T := by
        rw [disjoint_left]
        intro a haS haT
        exact (mem_sdiff.1 (hT.1 haT)).2 haS
      have h := gnpProb_noCross hq0 hq1 (disjoint_left.2 fun a (ha : a ∈ S) hb =>
        (mem_sdiff.1 hb).2 (mem_union_left _ ha) : Disjoint S (univ \ (S ∪ T)))
      unfold gnpProb at h
      rw [h, card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hdisj, card_univ,
        Fintype.card_fin, hS.2, hT.2]
      congr 2
      omega
    calc ∑ S ∈ powersetCard s (univ : Finset (Fin n)), ∑ T ∈ powersetCard (2 * s) (univ \ S),
          pProb (coin q n) (fun ω => ∀ a ∈ S, ∀ b ∈ univ \ (S ∪ T), ¬ (graphOf ω).Adj a b)
        = ∑ S ∈ powersetCard s (univ : Finset (Fin n)), ∑ _T ∈ powersetCard (2 * s) (univ \ S),
            (1 - q) ^ (s * (n - 3 * s)) :=
          sum_congr rfl fun S hS => sum_congr rfl fun T hT => hterm S hS T hT
      _ ≤ ∑ _S ∈ powersetCard s (univ : Finset (Fin n)), (n.choose (2 * s) : ℝ) *
            (1 - q) ^ (s * (n - 3 * s)) := by
          refine sum_le_sum fun S hS => ?_
          rw [sum_const, card_powersetCard, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) _)
          have hc : (univ \ S).card ≤ n := by
            have := card_le_univ (univ \ S); simpa using this
          exact_mod_cast Nat.choose_le_choose _ hc
      _ = (n.choose s : ℝ) * ((n.choose (2 * s) : ℝ) * (1 - q) ^ (s * (n - 3 * s))) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Many present pairs.** -/
theorem pProb_many_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    pProb (coin q n) (fun ω => m ≤ (univ.filter fun e => ω e = true).card) ≤
      ((Fintype.card (Pairs n)).choose m : ℝ) * q ^ m := by
  classical
  have hP := coin_isPMF hq0 hq1 n
  refine (pProb_mono hP (T := fun ω => ∃ J ∈ powersetCard m (univ : Finset (Pairs n)),
      ∀ e ∈ J, ω e = true) fun ω h => ?_).trans ?_
  · obtain ⟨J, hJ, hJc⟩ := exists_subset_card_eq h
    exact ⟨J, mem_powersetCard.2 ⟨subset_univ _, hJc⟩, fun e he => (mem_filter.1 (hJ he)).2⟩
  · refine (pProb_exists_le hP _ _).trans (le_of_eq ?_)
    rw [sum_congr rfl fun J hJ => by
      have := pProb_coin_present_absent hq0 hq1 J ∅ (disjoint_empty_right _)
      simp only [card_empty, pow_zero, mul_one, notMem_empty, false_imp_iff,
        imp_true_iff, and_true] at this
      rw [this, (mem_powersetCard.1 hJ).2]]
    rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul]

end RandomGraphLib
