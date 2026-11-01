/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.KomlosSzemeredi.Small

/-!
# Komlós–Szemerédi, upper side: small vertices are far apart

A walk of length at most four between two distinct small vertices contains a path of length
`m ∈ [1, 4]`, i.e. `m + 1` distinct vertices with the `m` pairs between consecutive ones present
and small ends; a small vertex on a cycle of length three or four gives `m + 1` distinct vertices
(`m ∈ {2, 3}`) with `m + 1` present pairs. By `pProb_config` and the union bound
(`pProb_near_le`, `pProb_cycle_le`):

* `P(two small vertices at distance ≤ 4) ≤ ∑_{m=1}^{4} n^{m+1} p^m T²`,
* `P(a small vertex on a cycle of length 3 or 4) ≤ ∑_{m=2}^{3} n^{m+1} p^{m+1} T`,

where `T` bounds the probability that a vertex has fewer than `D` neighbours among at least
`n - 6` pairs.
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Pseudorandom Pseudorandom.RandomGraphs

variable {n : ℕ}

/-- The pair `{t i, t (i + 1)}`. -/
def stepPair {m : ℕ} (t : Fin (m + 1) → Fin n) (ht : Function.Injective t) (i : Fin m) :
    Pairs n :=
  ⟨s(t i.castSucc, t i.succ), by simpa using ht.ne (Fin.castSucc_lt_succ (i := i)).ne⟩

/-- The pairs along a tuple of distinct vertices. -/
def pathPairs {m : ℕ} (t : Fin (m + 1) → Fin n) (ht : Function.Injective t) :
    Finset (Pairs n) :=
  univ.image (stepPair t ht)

theorem card_pathPairs {m : ℕ} (t : Fin (m + 1) → Fin n) (ht : Function.Injective t) :
    (pathPairs t ht).card = m := by
  rw [pathPairs, card_image_of_injective _ ?_, card_univ, Fintype.card_fin]
  intro i j hij
  simp only [stepPair, Subtype.mk.injEq, Sym2.eq_iff] at hij
  rcases hij with ⟨h1, -⟩ | ⟨h1, h2⟩
  · have := ht h1
    exact Fin.ext (by simpa [Fin.ext_iff] using this)
  · have e1 := congrArg Fin.val (ht h1)
    have e2 := congrArg Fin.val (ht h2)
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
    omega

/-- The closing pair `{t m, t 0}` of a tuple with at least three vertices. -/
def closePair {m : ℕ} (t : Fin (m + 1) → Fin n) (ht : Function.Injective t) (hm : 1 ≤ m) :
    Pairs n :=
  ⟨s(t (Fin.last m), t 0), by
    have h : Fin.last m ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    simpa using ht.ne h⟩

theorem closePair_not_mem {m : ℕ} (t : Fin (m + 1) → Fin n) (ht : Function.Injective t)
    (hm : 2 ≤ m) : closePair t ht (by omega) ∉ pathPairs t ht := by
  intro h
  obtain ⟨i, -, hi⟩ := mem_image.1 h
  simp only [stepPair, closePair, Subtype.mk.injEq, Sym2.eq_iff] at hi
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := congrArg Fin.val (ht h1)
    have e2 := congrArg Fin.val (ht h2)
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at e1 e2
    omega
  · have e1 := congrArg Fin.val (ht h1)
    have e2 := congrArg Fin.val (ht h2)
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at e1 e2
    omega

theorem card_tuples (m : ℕ) :
    Fintype.card {t : Fin (m + 1) → Fin n // Function.Injective t} ≤ n ^ (m + 1) := by
  classical
  refine (Fintype.card_subtype_le _).trans ?_
  simp

/-- Two distinct small vertices at distance at most four. -/
def NearSmall (G : SimpleGraph (Fin n)) (D : ℕ) : Prop :=
  ∃ x y, IsSmall G D x ∧ IsSmall G D y ∧ x ≠ y ∧ ∃ w : G.Walk x y, w.length ≤ 4

/-- A small vertex on a cycle of length three or four. -/
def CycleSmall (G : SimpleGraph (Fin n)) (D : ℕ) : Prop :=
  ∃ x, IsSmall G D x ∧ ((∃ a b, IsPathList G [x, a, b] ∧ G.Adj b x) ∨
    ∃ a b c, IsPathList G [x, a, b, c] ∧ G.Adj c x)

theorem pProb_near_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (D : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ r : ℕ, n ≤ r + 6 → r ≤ n → tailSum r p D ≤ T) :
    gnpProb n p (fun G => NearSmall G D) ≤ ∑ m ∈ Icc 1 4, (n : ℝ) ^ (m + 1) * (p ^ m * T ^ 2) := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  unfold gnpProb
  refine (pProb_mono hP (T := fun ω => ∃ m ∈ Icc 1 4,
      ∃ t ∈ (univ : Finset {t : Fin (m + 1) → Fin n // Function.Injective t}),
      (∀ e ∈ pathPairs t.1 t.2, ω e = true) ∧
        ∀ x ∈ ({t.1 0, t.1 (Fin.last m)} : Finset (Fin n)), IsSmall (graphOf ω) D x)
      fun ω h => ?_).trans ?_
  · obtain ⟨x, y, hx, hy, hxy, w, hw⟩ := h
    set q := w.bypass with hq
    have hqp : q.IsPath := w.bypass_isPath
    have hql : q.length ≤ 4 := (w.length_bypass_le_length).trans hw
    have hq1 : 1 ≤ q.length := by
      rcases Nat.eq_zero_or_pos q.length with h0 | h0
      · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hxy
      · exact h0
    have hinj : Function.Injective fun i : Fin (q.length + 1) => q.getVert i := by
      intro i j hij
      exact Fin.ext (hqp.getVert_injOn (show (i : ℕ) ≤ q.length from Nat.lt_succ_iff.1 i.isLt)
        (show (j : ℕ) ≤ q.length from Nat.lt_succ_iff.1 j.isLt) hij)
    refine ⟨q.length, mem_Icc.2 ⟨hq1, hql⟩, ⟨_, hinj⟩, mem_univ _, ?_, ?_⟩
    · intro e he
      obtain ⟨i, -, rfl⟩ := mem_image.1 he
      have hadj := q.adj_getVert_succ (i := i) i.2
      exact (graphOf_adj_iff ω _ _ _ rfl).1 (by simpa [Fin.val_succ] using hadj)
    · intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · simpa using hx
      · simpa [SimpleGraph.Walk.getVert_length] using hy
  · refine (pProb_exists_le hP _ _).trans (sum_le_sum fun m hm => ?_)
    have hm := mem_Icc.1 hm
    refine (pProb_exists_le hP _ _).trans ?_
    calc ∑ t ∈ (univ : Finset {t : Fin (m + 1) → Fin n // Function.Injective t}),
          pProb (coin p n) (fun ω => (∀ e ∈ pathPairs t.1 t.2, ω e = true) ∧
            ∀ x ∈ ({t.1 0, t.1 (Fin.last m)} : Finset (Fin n)), IsSmall (graphOf ω) D x)
        ≤ ∑ _t ∈ (univ : Finset {t : Fin (m + 1) → Fin n // Function.Injective t}),
            p ^ m * T ^ 2 := by
          refine sum_le_sum fun t _ => ?_
          have h0m : t.1 0 ≠ t.1 (Fin.last m) := t.2.ne fun h => by
            have := congrArg Fin.val h
            simp at this
            omega
          have hX : ({t.1 0, t.1 (Fin.last m)} : Finset (Fin n)).card = 2 := card_pair h0m
          have := pProb_config hp0 hp1 (pathPairs t.1 t.2) {t.1 0, t.1 (Fin.last m)} D hT0
            (fun r hr hrn => hT r (by rw [card_pathPairs, hX] at hr; omega) hrn)
          rwa [card_pathPairs, hX] at this
      _ ≤ (n : ℝ) ^ (m + 1) * (p ^ m * T ^ 2) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_tuples m) (by positivity)

theorem pProb_cycle_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (D : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ r : ℕ, n ≤ r + 6 → r ≤ n → tailSum r p D ≤ T) :
    gnpProb n p (fun G => CycleSmall G D) ≤
      ∑ k ∈ range 2, (n : ℝ) ^ (k + 3) * (p ^ (k + 3) * T) := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  unfold gnpProb
  refine (pProb_mono hP (T := fun ω => ∃ k ∈ range 2,
      ∃ t ∈ (univ : Finset {t : Fin (k + 2 + 1) → Fin n // Function.Injective t}),
      (∀ e ∈ insert (closePair t.1 t.2 (by omega)) (pathPairs t.1 t.2), ω e = true) ∧
        ∀ x ∈ ({t.1 0} : Finset (Fin n)), IsSmall (graphOf ω) D x)
      fun ω h => ?_).trans ?_
  · obtain ⟨x, hx, ⟨a, b, hl, hbx⟩ | ⟨a, b, c, hl, hcx⟩⟩ := h
    · have hnd := hl.1
      have hc := hl.2
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
        List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true] at hnd
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
      have hinj : Function.Injective (![x, a, b] : Fin 3 → Fin n) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      refine ⟨0, by simp, ⟨![x, a, b], hinj⟩, mem_univ _, ?_, ?_⟩
      · intro e he
        rcases mem_insert.1 he with rfl | he
        · exact (graphOf_adj_iff ω _ b x rfl).1 hbx
        · obtain ⟨i, -, rfl⟩ := mem_image.1 he
          fin_cases i
          · exact (graphOf_adj_iff ω _ x a rfl).1 hc.1
          · exact (graphOf_adj_iff ω _ a b rfl).1 hc.2
      · intro v hv
        rw [mem_singleton] at hv
        subst hv
        simpa using hx
    · have hnd := hl.1
      have hc := hl.2
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
        List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true] at hnd
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
      have hinj : Function.Injective (![x, a, b, c] : Fin 4 → Fin n) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      refine ⟨1, by simp, ⟨![x, a, b, c], hinj⟩, mem_univ _, ?_, ?_⟩
      · intro e he
        rcases mem_insert.1 he with rfl | he
        · exact (graphOf_adj_iff ω _ c x rfl).1 hcx
        · obtain ⟨i, -, rfl⟩ := mem_image.1 he
          fin_cases i
          · exact (graphOf_adj_iff ω _ x a rfl).1 hc.1
          · exact (graphOf_adj_iff ω _ a b rfl).1 hc.2.1
          · exact (graphOf_adj_iff ω _ b c rfl).1 hc.2.2
      · intro v hv
        rw [mem_singleton] at hv
        subst hv
        simpa using hx
  · refine (pProb_exists_le hP _ _).trans (sum_le_sum fun k hk => ?_)
    have hk2 : k < 2 := mem_range.1 hk
    refine (pProb_exists_le hP _ _).trans ?_
    calc ∑ t ∈ (univ : Finset {t : Fin (k + 2 + 1) → Fin n // Function.Injective t}),
          pProb (coin p n) (fun ω =>
            (∀ e ∈ insert (closePair t.1 t.2 (by omega)) (pathPairs t.1 t.2), ω e = true) ∧
            ∀ x ∈ ({t.1 0} : Finset (Fin n)), IsSmall (graphOf ω) D x)
        ≤ ∑ _t ∈ (univ : Finset {t : Fin (k + 2 + 1) → Fin n // Function.Injective t}),
            p ^ (k + 3) * T := by
          refine sum_le_sum fun t _ => ?_
          have hc : (insert (closePair t.1 t.2 (by omega)) (pathPairs t.1 t.2)).card = k + 3 := by
            rw [card_insert_of_notMem (closePair_not_mem t.1 t.2 (by omega)), card_pathPairs]
          have := pProb_config hp0 hp1 _ {t.1 0} D hT0
            (fun r hr hrn => hT r (by rw [hc, card_singleton] at hr; omega) hrn)
          rwa [hc, card_singleton, pow_one] at this
      _ ≤ (n : ℝ) ^ (k + 3) * (p ^ (k + 3) * T) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_tuples (k + 2)) (by positivity)

end RandomGraphLib
