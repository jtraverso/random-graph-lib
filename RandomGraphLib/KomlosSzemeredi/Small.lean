/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.KomlosSzemeredi.Lower
public import RandomGraphLib.KomlosSzemeredi.Indep
public import RandomGraphLib.KomlosSzemeredi.Expand

/-!
# Komlós–Szemerédi, upper side: vertices of small degree

A vertex of `G(n, p)` is *small* if it has fewer than `D` neighbours. The number of present pairs
in a set `R` of pairs is binomial, so it is below `D` with probability `tailSum |R| p D`
(`pProb_count_lt_le`), at most `(e n p / D)^D (1 - p)^{n - c - D}` when `n - c ≤ |R| ≤ n`
(`tailSum_le`). If a set `F₀` of pairs is present and the vertices of `X` are small, then the
pairs at the vertices of `X` outside `F₀` and outside `X` are disjoint sets of size at least
`n - |F₀| - |X|`, independent of `F₀`; this gives `pProb_config`.
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Pseudorandom Pseudorandom.RandomGraphs MoserTardos

variable {n : ℕ}

/-- The pairs at `x`. -/
def starP (x : Fin n) : Finset (Pairs n) := univ.filter fun e => x ∈ e.1

theorem card_starP (x : Fin n) : (starP x).card = n - 1 := card_pairs_at x

theorem card_filter_le_nbrs {ω : Pairs n → Bool} {x : Fin n} {R : Finset (Pairs n)}
    (hR : R ⊆ starP x) : (R.filter fun e => ω e = true).card ≤ (nbrs (graphOf ω) x).card := by
  refine card_le_card_of_forall_subsingleton (fun e w => e.1 = s(x, w)) (fun e he => ?_) ?_
  · obtain ⟨heR, hω⟩ := mem_filter.1 he
    have hx : x ∈ e.1 := (mem_filter.1 (hR heR)).2
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hx
    exact ⟨w, mem_nbrs.2 ((graphOf_adj_iff ω e x w hw).2 hω), hw⟩
  · intro w _ e he e' he'
    exact Subtype.ext (he.2.trans he'.2.symm)

/-- `P(Bin(r, p) < D)`. -/
noncomputable def tailSum (r : ℕ) (p : ℝ) (D : ℕ) : ℝ :=
  ∑ j ∈ range D, (r.choose j : ℝ) * (p ^ j * (1 - p) ^ (r - j))

theorem tailSum_nonneg (r : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (D : ℕ) :
    0 ≤ tailSum r p D :=
  sum_nonneg fun _ _ => mul_nonneg (by positivity)
    (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _))

/-- Fewer than `D` present pairs in `R`. -/
theorem pProb_count_lt_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : Finset (Pairs n)) (D : ℕ) :
    pProb (coin p n) (fun ω => (R.filter fun e => ω e = true).card < D) ≤
      tailSum R.card p D := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  refine (pProb_mono hP (T := fun ω => ∃ J ∈ R.powerset.filter (fun J => J.card < D),
      (∀ e ∈ J, ω e = true) ∧ ∀ e ∈ R \ J, ω e = false)
      fun ω h => ⟨R.filter fun e => ω e = true, ?_, ?_, ?_⟩).trans ?_
  · exact mem_filter.2 ⟨mem_powerset.2 (filter_subset _ _), h⟩
  · intro e he; exact (mem_filter.1 he).2
  · intro e he
    obtain ⟨heR, hne⟩ := mem_sdiff.1 he
    simpa [heR] using hne
  refine (pProb_exists_le hP _ _).trans (le_of_eq ?_)
  calc ∑ J ∈ R.powerset.filter (fun J => J.card < D), pProb (coin p n)
        (fun ω => (∀ e ∈ J, ω e = true) ∧ ∀ e ∈ R \ J, ω e = false)
      = ∑ J ∈ R.powerset.filter (fun J => J.card < D), p ^ J.card * (1 - p) ^ (R.card - J.card) :=
        sum_congr rfl fun J hJ => by
          rw [pProb_coin_present_absent hp0 hp1 _ _ disjoint_sdiff,
            card_sdiff_of_subset (mem_powerset.1 (mem_filter.1 hJ).1)]
    _ = tailSum R.card p D := by
        rw [sum_filter, sum_powerset_apply_card
          (fun m => if m < D then p ^ m * (1 - p) ^ (R.card - m) else 0)]
        unfold tailSum
        set g : ℕ → ℝ := fun m => (R.card.choose m : ℝ) *
          (if m < D then p ^ m * (1 - p) ^ (R.card - m) else 0) with hg
        have h1 : ∑ m ∈ range (R.card + 1), R.card.choose m •
            (if m < D then p ^ m * (1 - p) ^ (R.card - m) else 0) =
            ∑ m ∈ range (R.card + 1) ∪ range D, g m := by
          rw [← sum_subset subset_union_left]
          · exact sum_congr rfl fun m _ => by rw [nsmul_eq_mul]
          · intro m hm hm'
            have : R.card < m := by simp only [mem_union, mem_range] at hm hm'; omega
            simp [hg, Nat.choose_eq_zero_of_lt this]
        have h2 : ∑ j ∈ range D, (R.card.choose j : ℝ) * (p ^ j * (1 - p) ^ (R.card - j)) =
            ∑ m ∈ range (R.card + 1) ∪ range D, g m := by
          rw [← sum_subset subset_union_right]
          · exact sum_congr rfl fun m hm => by simp [hg, mem_range.1 hm]
          · intro m hm hm'
            have : D ≤ m := by simpa using hm'
            simp [hg, show ¬ m < D by omega]
        rw [h1, h2]

/-- `∑_{j < D} x^j / j! ≤ (e x / D)^D` for `x ≥ D ≥ 1`. -/
theorem sum_pow_div_factorial_le {x : ℝ} {D : ℕ} (hD : 1 ≤ D) (hx : (D : ℝ) ≤ x) :
    ∑ j ∈ range D, x ^ j / j.factorial ≤ (exp 1 * x / D) ^ D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hxD : 1 ≤ x / D := (one_le_div hD0).2 hx
  calc ∑ j ∈ range D, x ^ j / j.factorial
      = ∑ j ∈ range D, (x / D) ^ j * ((D : ℝ) ^ j / j.factorial) :=
        sum_congr rfl fun j _ => by rw [div_pow]; field_simp
    _ ≤ ∑ j ∈ range D, (x / D) ^ D * ((D : ℝ) ^ j / j.factorial) :=
        sum_le_sum fun j hj => mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hxD (mem_range.1 hj).le) (by positivity)
    _ = (x / D) ^ D * ∑ j ∈ range D, (D : ℝ) ^ j / j.factorial := by rw [mul_sum]
    _ ≤ (x / D) ^ D * exp D :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hD0.le D) (by positivity)
    _ = (exp 1 * x / D) ^ D := by
        rw [show (D : ℝ) = D * 1 by ring, Real.exp_nat_mul, mul_one, mul_div_assoc, mul_pow,
          mul_comm]

/-- The binomial tail bound. -/
theorem tailSum_le {r c D : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : n ≤ r + c)
    (hr2 : r ≤ n) (hD : 1 ≤ D) (hnp : (D : ℝ) ≤ n * p) :
    tailSum r p D ≤ (exp 1 * (n * p) / D) ^ D * (1 - p) ^ (n - c - D) := by
  unfold tailSum
  calc ∑ j ∈ range D, (r.choose j : ℝ) * (p ^ j * (1 - p) ^ (r - j))
      ≤ ∑ j ∈ range D, ((n * p) ^ j / j.factorial) * (1 - p) ^ (n - c - D) := by
        refine sum_le_sum fun j hj => ?_
        have hj := mem_range.1 hj
        have h1 : (r.choose j : ℝ) ≤ (n : ℝ) ^ j / j.factorial :=
          (Nat.choose_le_pow_div j r).trans (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hr2) _) (by positivity))
        have h2 : (1 - p) ^ (r - j) ≤ (1 - p) ^ (n - c - D) :=
          pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
        calc (r.choose j : ℝ) * (p ^ j * (1 - p) ^ (r - j))
            ≤ ((n : ℝ) ^ j / j.factorial) * (p ^ j * (1 - p) ^ (n - c - D)) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (pow_nonneg hp0 _))
                (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)) (by positivity)
          _ = ((n * p) ^ j / j.factorial) * (1 - p) ^ (n - c - D) := by ring
    _ = (∑ j ∈ range D, (n * p) ^ j / j.factorial) * (1 - p) ^ (n - c - D) := by rw [sum_mul]
    _ ≤ (exp 1 * (n * p) / D) ^ D * (1 - p) ^ (n - c - D) :=
        mul_le_mul_of_nonneg_right (sum_pow_div_factorial_le hD hnp) (pow_nonneg (by linarith) _)

/-- **Configurations around small vertices.** If the pairs of `F₀` are present, the vertices of
`X` are small with probability at most `T` each, independently. -/
theorem pProb_config {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F₀ : Finset (Pairs n))
    (X : Finset (Fin n)) (D : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ r : ℕ, n ≤ r + (F₀.card + X.card) → r ≤ n → tailSum r p D ≤ T) :
    pProb (coin p n) (fun ω => (∀ e ∈ F₀, ω e = true) ∧ ∀ x ∈ X, IsSmall (graphOf ω) D x) ≤
      p ^ F₀.card * T ^ X.card := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  set inX : Finset (Pairs n) := univ.filter fun e => ∀ v ∈ e.1, v ∈ X with hinX
  set R : Fin n → Finset (Pairs n) := fun x => (starP x \ F₀) \ inX with hR
  set C : Option (Fin n) → Finset (Pairs n) := fun i => i.elim F₀ R with hC
  set A : Option (Fin n) → (Pairs n → Bool) → Prop := fun i ω => i.elim
    (∀ e ∈ F₀, ω e = true) (fun x => ((R x).filter fun e => ω e = true).card < D) with hA
  set S : Finset (Option (Fin n)) := insert none (X.map Function.Embedding.some) with hS
  have hnone : none ∉ X.map Function.Embedding.some := by simp
  have hRsub : ∀ x, R x ⊆ starP x := fun x => (sdiff_subset.trans sdiff_subset)
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (C i) (C j) := by
    have hFR : ∀ x, Disjoint F₀ (R x) := fun x => by
      rw [disjoint_left]; intro e he he'
      simp only [hR, mem_sdiff] at he'
      exact he'.1.2 he
    have hRR : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint (R x) (R y) := by
      intro x hx y hy hxy
      rw [disjoint_left]
      intro e he he'
      simp only [hR, mem_sdiff, starP, mem_filter, mem_univ, true_and] at he he'
      apply he.2
      have he1 : e.1 = s(x, y) := (Sym2.mem_and_mem_iff hxy).1 ⟨he.1.1, he'.1.1⟩
      simp only [hinX, mem_filter, mem_univ, true_and, he1, Sym2.mem_iff]
      rintro v (rfl | rfl) <;> assumption
    intro i hi j hj hij
    simp only [hS, mem_insert, mem_map, Function.Embedding.some_apply] at hi hj
    rcases hi with rfl | ⟨x, hx, rfl⟩ <;> rcases hj with rfl | ⟨y, hy, rfl⟩
    · exact absurd rfl hij
    · exact hFR y
    · exact (hFR x).symm
    · exact hRR x hx y hy fun h => hij (h ▸ rfl)
  have hdep : ∀ i ω ω', (∀ e ∈ C i, ω e = ω' e) → (A i ω ↔ A i ω') := by
    intro i ω ω' h
    cases i with
    | none =>
      simp only [hA, hC, Option.elim] at h ⊢
      exact forall₂_congr fun e he => by rw [h e he]
    | some x =>
      simp only [hA, hC, Option.elim] at h ⊢
      rw [filter_congr fun e he => by rw [h e he]]
  have hev : ∀ ω, ((∀ e ∈ F₀, ω e = true) ∧ ∀ x ∈ X, IsSmall (graphOf ω) D x) →
      ∀ i ∈ S, A i ω := by
    rintro ω ⟨h1, h2⟩ i hi
    simp only [hS, mem_insert, mem_map, Function.Embedding.some_apply] at hi
    rcases hi with rfl | ⟨x, hx, rfl⟩
    · exact h1
    · exact lt_of_le_of_lt (card_filter_le_nbrs (hRsub x)) (h2 x hx)
  refine (pProb_mono hP hev).trans ?_
  rw [pProb_forall_of_disjoint hP S C hdisj A hdep, hS, prod_insert hnone, prod_map]
  have hF : pProb (coin p n) (A none) = p ^ F₀.card := by
    have := pProb_coin_present_absent hp0 hp1 F₀ ∅ (disjoint_empty_right _)
    simp only [card_empty, pow_zero, mul_one, notMem_empty, false_imp_iff, imp_true_iff,
      and_true] at this
    simpa [hA] using this
  rw [hF]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hp0 _)
  calc ∏ x ∈ X, pProb (coin p n) (A (Function.Embedding.some x)) ≤ ∏ _x ∈ X, T := by
        refine Finset.prod_le_prod₀ (fun x _ => pProb_nonneg hP _) fun x hx => ?_
        refine (pProb_count_lt_le hp0 hp1 (R x) D).trans (hT _ ?_ ?_)
        · -- `|R x| ≥ n - |F₀| - |X|`
          have hcover : starP x ⊆ R x ∪ F₀ ∪ (starP x ∩ inX) := by
            intro e he
            by_cases h1 : e ∈ F₀
            · exact mem_union_left _ (mem_union_right _ h1)
            · by_cases h2 : e ∈ inX
              · exact mem_union_right _ (mem_inter.2 ⟨he, h2⟩)
              · exact mem_union_left _ (mem_union_left _ (by simp [hR, he, h1, h2]))
          have hin : (starP x ∩ inX).card ≤ (X.erase x).card := by
            refine card_le_card_of_forall_subsingleton (fun e y => e.1 = s(x, y))
              (fun e he => ?_) ?_
            · obtain ⟨he1, he2⟩ := mem_inter.1 he
              have hx : x ∈ e.1 := (mem_filter.1 he1).2
              obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.1 hx
              have hyX : y ∈ X := (mem_filter.1 he2).2 y (by rw [hy]; exact Sym2.mem_mk_right _ _)
              have hxy : y ≠ x := by
                rintro rfl
                exact e.2 (by rw [hy]; exact Sym2.mk_isDiag_iff.2 rfl)
              exact ⟨y, mem_erase.2 ⟨hxy, hyX⟩, hy⟩
            · intro y _ e he e' he'
              exact Subtype.ext (he.2.trans he'.2.symm)
          have h1 := card_le_card hcover
          have h2 := card_union_le (R x ∪ F₀) (starP x ∩ inX)
          have h3 := card_union_le (R x) F₀
          have h4 := card_erase_of_mem hx
          have h5 := card_starP x
          have h6 : 1 ≤ X.card := card_pos.2 ⟨x, hx⟩
          omega
        · have := card_le_card (hRsub x)
          rw [card_starP] at this
          omega
    _ = T ^ X.card := by rw [prod_const]

end RandomGraphLib
