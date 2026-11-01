/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.KomlosSzemeredi.Sample

/-!
# Komlós–Szemerédi, upper side: the bound for fixed `n`

`P(G(n, p) has no Hamiltonian cycle)` is at most the sum of
* the probability that `G(n, p)` has no sparse connected expander, bounded through an
  independent auxiliary `G(n, ε)` (`A = G ∩ G(n, ε)` is a `G(n, p ε)`) by the failure
  probabilities of the hypotheses of `exists_sparse_expander`;
* the union bound over sparse expanders (`sparse_bound`, `sum_sets_card_le`).
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Pseudorandom Pseudorandom.RandomGraphs

variable {n : ℕ}

/-- Fewer than two neighbours: `tailSum` with `D = 2`. -/
theorem tailSum_two_le {r : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : n ≤ r + 1)
    (hr2 : r ≤ n) (h2 : 2 ≤ n) : tailSum r p 2 ≤ (1 + n * p) * (1 - p) ^ (n - 2) := by
  unfold tailSum
  rw [sum_range_succ, sum_range_one]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.choose_one_right,
    pow_one, Nat.sub_zero]
  have hq0 : 0 ≤ 1 - p := by linarith
  have h1 : (1 - p) ^ r ≤ (1 - p) ^ (n - 2) := pow_le_pow_of_le_one hq0 (by linarith) (by omega)
  have h2' : (1 - p) ^ (r - 1) ≤ (1 - p) ^ (n - 2) :=
    pow_le_pow_of_le_one hq0 (by linarith) (by omega)
  have h3 : (r : ℝ) * p ≤ n * p := mul_le_mul_of_nonneg_right (by exact_mod_cast hr2) hp0
  have h4 : 0 ≤ (1 - p) ^ (n - 2) := pow_nonneg hq0 _
  have h5 : 0 ≤ (r : ℝ) * p := by positivity
  calc (1 - p) ^ r + (r : ℝ) * (p * (1 - p) ^ (r - 1))
      = (1 - p) ^ r + ((r : ℝ) * p) * (1 - p) ^ (r - 1) := by ring
    _ ≤ (1 - p) ^ (n - 2) + (n * p) * (1 - p) ^ (n - 2) := by
        gcongr
    _ = (1 + n * p) * (1 - p) ^ (n - 2) := by ring

/-- **The bound for fixed `n`.** -/
theorem gnpProb_not_hamCycle_le (h8 : 8 ≤ n) {p ε κ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {D s₀ u₀ mA : ℕ} (hD : 1 ≤ D)
    (h4 : 4 * s₀ ≤ u₀) {T₂ T : ℝ} (hT₂0 : 0 ≤ T₂)
    (hT₂ : ∀ r : ℕ, n ≤ r + 1 → r ≤ n → tailSum r p 2 ≤ T₂) (hT0 : 0 ≤ T)
    (hT : ∀ r : ℕ, n ≤ r + 6 → r ≤ n → tailSum r p D ≤ T) :
    gnpProb n p (fun G => ¬ HasHamCycle G) ≤
      n * T₂ + ∑ m ∈ Icc 1 4, (n : ℝ) ^ (m + 1) * (p ^ m * T ^ 2) +
        ∑ k ∈ range 2, (n : ℝ) ^ (k + 3) * (p ^ (k + 3) * T) +
        ∑ u ∈ Icc 1 u₀, (n.choose u : ℝ) *
          (((u ^ 2).choose (D * u / 12 + 1) : ℝ) * p ^ (D * u / 12 + 1)) +
        ∑ s ∈ Icc s₀ (n / 4), (n.choose s : ℝ) * ((n.choose (2 * s) : ℝ) *
          (1 - p * ε) ^ (s * (n - 3 * s))) +
        ((Fintype.card (Pairs n)).choose mA : ℝ) * (p * ε) ^ mA +
        κ⁻¹ ^ (mA + n * D + n) * exp (κ * p * Fintype.card (Pairs n)) *
          (1 - p) ^ ((n / 4 + 1) ^ 2 / 2) := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  have hpε0 : 0 ≤ p * ε := mul_nonneg hp0 hε0
  have hpε1 : p * ε ≤ 1 := by nlinarith
  have hPP := coinPair_isPMF hp0 hp1 hε0 hε1 n
  have hk : 1 ≤ n / 4 := by omega
  set M := mA + n * D with hM
  set Good : (Pairs n → Bool) → Prop := fun ω => ∃ F : Finset (Pairs n), F.card ≤ M ∧
    (∀ e ∈ F, ω e = true) ∧ (setGraph F).Connected ∧ IsExpander (setGraph F) (n / 4) with hGood
  -- the bad events
  set B1 : SimpleGraph (Fin n) → Prop := fun G => ∃ v, IsSmall G 2 v with hB1
  set B4 : SimpleGraph (Fin n) → Prop := fun G =>
    ∃ U : Finset (Fin n), U.card ≤ u₀ ∧ D * U.card < 6 * eIn G U with hB4
  set B5 : SimpleGraph (Fin n) → Prop := fun G => ∃ S : Finset (Fin n), s₀ ≤ S.card ∧
    S.card ≤ n / 4 ∧ (nbhd G S \ S).card < 2 * S.card with hB5
  set B6 : (Pairs n → Bool) → Prop := fun ω => mA ≤ (univ.filter fun e => ω e = true).card
    with hB6
  have hnotGood : pProb (coin p n) (fun ω => ¬ Good ω) ≤
      gnpProb n p B1 + gnpProb n p (fun G => NearSmall G D) +
        gnpProb n p (fun G => CycleSmall G D) + gnpProb n p B4 +
        gnpProb n (p * ε) B5 + pProb (coin (p * ε) n) B6 := by
    have h0 : pProb (coin p n) (fun ω => ¬ Good ω) =
        pProb (coinPair p ε n) (fun ω => ¬ Good (fun e => (ω e).1)) :=
      (pProb_coinPair_fst p ε n (fun ω => ¬ Good ω)).symm
    have hsub : ∀ ω : Pairs n → Bool × Bool, ¬ Good (fun e => (ω e).1) →
        (((((B1 (graphOf fun e => (ω e).1) ∨ NearSmall (graphOf fun e => (ω e).1) D) ∨
          CycleSmall (graphOf fun e => (ω e).1) D) ∨ B4 (graphOf fun e => (ω e).1)) ∨
          B5 (graphOf fun e => (ω e).1 && (ω e).2)) ∨ B6 (fun e => (ω e).1 && (ω e).2)) := by
      intro ω hng
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4'⟩, h5⟩, h6⟩ := hcon
      refine hng (exists_sparse_expander (fun e => (ω e).1) (fun e => (ω e).1 && (ω e).2)
        (fun e he => by simp at he; exact he.1) h8 hD h4 (fun v hv => h1 ⟨v, hv⟩) h2 h3 h4' h5 h6)
    have hor : pProb (coinPair p ε n) (fun ω =>
        (((((B1 (graphOf fun e => (ω e).1) ∨ NearSmall (graphOf fun e => (ω e).1) D) ∨
          CycleSmall (graphOf fun e => (ω e).1) D) ∨ B4 (graphOf fun e => (ω e).1)) ∨
          B5 (graphOf fun e => (ω e).1 && (ω e).2)) ∨ B6 (fun e => (ω e).1 && (ω e).2))) ≤
        pProb (coinPair p ε n) (fun ω => B1 (graphOf fun e => (ω e).1)) +
        pProb (coinPair p ε n) (fun ω => NearSmall (graphOf fun e => (ω e).1) D) +
        pProb (coinPair p ε n) (fun ω => CycleSmall (graphOf fun e => (ω e).1) D) +
        pProb (coinPair p ε n) (fun ω => B4 (graphOf fun e => (ω e).1)) +
        pProb (coinPair p ε n) (fun ω => B5 (graphOf fun e => (ω e).1 && (ω e).2)) +
        pProb (coinPair p ε n) (fun ω => B6 (fun e => (ω e).1 && (ω e).2)) :=
      (pProb_or_le hPP _ _).trans (add_le_add ((pProb_or_le hPP _ _).trans
        (add_le_add ((pProb_or_le hPP _ _).trans (add_le_add
          ((pProb_or_le hPP _ _).trans (add_le_add (pProb_or_le hPP _ _) le_rfl)) le_rfl))
            le_rfl)) le_rfl)
    have q1 : pProb (coinPair p ε n) (fun ω => B1 (graphOf fun e => (ω e).1)) = gnpProb n p B1 :=
      pProb_coinPair_fst p ε n (fun ω => B1 (graphOf ω))
    have q2 : pProb (coinPair p ε n) (fun ω => NearSmall (graphOf fun e => (ω e).1) D) =
        gnpProb n p (fun G => NearSmall G D) :=
      pProb_coinPair_fst p ε n (fun ω => NearSmall (graphOf ω) D)
    have q3 : pProb (coinPair p ε n) (fun ω => CycleSmall (graphOf fun e => (ω e).1) D) =
        gnpProb n p (fun G => CycleSmall G D) :=
      pProb_coinPair_fst p ε n (fun ω => CycleSmall (graphOf ω) D)
    have q4 : pProb (coinPair p ε n) (fun ω => B4 (graphOf fun e => (ω e).1)) = gnpProb n p B4 :=
      pProb_coinPair_fst p ε n (fun ω => B4 (graphOf ω))
    have q5 : pProb (coinPair p ε n) (fun ω => B5 (graphOf fun e => (ω e).1 && (ω e).2)) =
        gnpProb n (p * ε) B5 :=
      pProb_coinPair_and p ε n (fun ω => B5 (graphOf ω))
    have q6 : pProb (coinPair p ε n) (fun ω => B6 (fun e => (ω e).1 && (ω e).2)) =
        pProb (coin (p * ε) n) B6 :=
      pProb_coinPair_and p ε n B6
    rw [h0]
    refine (pProb_mono hPP hsub).trans (hor.trans (le_of_eq ?_))
    rw [q1, q2, q3, q4, q5, q6]
  have hB1 : gnpProb n p B1 ≤ n * T₂ := by
    unfold gnpProb
    refine (pProb_mono hP (T := fun ω => ∃ v ∈ (univ : Finset (Fin n)),
      (∀ e ∈ (∅ : Finset (Pairs n)), ω e = true) ∧
        ∀ x ∈ ({v} : Finset (Fin n)), IsSmall (graphOf ω) 2 x)
      fun ω ⟨v, hv⟩ => ⟨v, mem_univ _, by simp, by simpa using hv⟩).trans ?_
    refine (pProb_exists_le hP _ _).trans ?_
    calc ∑ v ∈ (univ : Finset (Fin n)), pProb (coin p n) (fun ω =>
          (∀ e ∈ (∅ : Finset (Pairs n)), ω e = true) ∧
            ∀ x ∈ ({v} : Finset (Fin n)), IsSmall (graphOf ω) 2 x)
        ≤ ∑ _v ∈ (univ : Finset (Fin n)), T₂ := by
          refine sum_le_sum fun v _ => ?_
          have := pProb_config hp0 hp1 ∅ {v} 2 hT₂0
            (fun r hr hrn => hT₂ r (by simpa using hr) hrn)
          simpa using this
      _ = n * T₂ := by simp
  have hgood : pProb (coin p n) (fun ω => ¬ HasHamCycle (graphOf ω) ∧ Good ω) ≤
      κ⁻¹ ^ (M + n) * exp (κ * p * Fintype.card (Pairs n)) *
        (1 - p) ^ ((n / 4 + 1) ^ 2 / 2) := by
    refine (sparse_bound hk M hp0 hp1).trans ?_
    rw [← sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) _)
    exact sum_sets_card_le (M + n) hp0 hκ0 hκ1
  unfold gnpProb
  refine (pProb_mono hP (T := fun ω => (¬ HasHamCycle (graphOf ω) ∧ Good ω) ∨ ¬ Good ω)
    fun ω h => by by_cases hg : Good ω <;> simp [hg, h]).trans ?_
  refine (pProb_or_le hP _ _).trans ?_
  have hN := pProb_near_le hp0 hp1 D hT0 hT
  have hC := pProb_cycle_le hp0 hp1 D hT0 hT
  have hDn : gnpProb n p B4 ≤ _ := pProb_dense_le hp0 hp1 u₀ D
  have hL : gnpProb n (p * ε) B5 ≤ _ := pProb_large_le hpε0 hpε1 s₀
  have hMa : pProb (coin (p * ε) n) B6 ≤ _ := pProb_many_le hpε0 hpε1 mA
  linarith

end RandomGraphLib
