/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.KomlosSzemeredi.Bound
public import RandomGraphLib.KomlosSzemeredi.Estimates
public import RandomGraphLib.Mathlib
public import PseudorandomLib.RandomGraphs.HamCycle

/-!
# Komlós–Szemerédi, upper side

`isHamiltonian_of_log_add_loglog_add`: if `ω(n) → ∞`, then
`G(n, (log n + log log n + ω(n)) / n)` (edge probability clipped above at `1`) is Hamiltonian
with probability tending to `1`.

For large `n` we apply `gnpProb_not_hamCycle_le` with `w = min(ω, log log n)`,
`D = ⌊log n / 1000⌋`, an auxiliary `G(n, 1/4000)`, sets of size at least `n^{1 - 1/96000}` for the
expansion of the auxiliary sample, `mA = ⌈e² C(n, 2) p / 4000⌉` and `κ = 1/200`; every error term
is bounded by `ksErr (log n) w` (`gnpProb_not_hamCycle_le_ksErr`), which tends to `0`.
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Filter Pseudorandom Pseudorandom.RandomGraphs

/-- The total error. -/
noncomputable def ksErr (L w : ℝ) : ℝ :=
  3 * exp 1 * exp (-w) + 64 * exp 2 * (L ^ 4 * exp (-(98 / 100 * L))) +
    32 * exp 1 * (L ^ 4 * exp (-(99 / 100 * L))) + 2 * exp (-L) +
    2 * (exp 3 * exp (-(L / 32000))) + exp (-L) + exp (1 - L)

theorem exp_neg_le_half {x : ℝ} (hx : 1 ≤ x) : exp (-x) ≤ 1 / 2 := by
  have h1 : exp (-x) ≤ exp (-1) := exp_le_exp.2 (by linarith)
  have h2 : exp (-1) * exp 1 = 1 := by rw [← Real.exp_add]; simp
  have := exp_one_gt_27
  nlinarith [exp_pos (-1)]

set_option maxHeartbeats 1000000 in
/-- **The bound for large `n`.** -/
theorem gnpProb_not_hamCycle_le_ksErr {n : ℕ} {p L w : ℝ} (hn : 8001 ≤ n) (hLn : exp L = n)
    (hL : 10 ^ 10 ≤ L) (hnp : n * p = L + Real.log L + w) (hw0 : 0 ≤ w)
    (hwL : w ≤ Real.log L) (h2L : 2 * Real.log L ≤ L) (h4L : 4 * L ≤ n)
    (hsq : 2 * L * (6 + L) ≤ n) :
    gnpProb n p (fun G => ¬ HasHamCycle G) ≤ ksErr L w := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn8001 : (8001 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hnp1 : L ≤ n * p := by linarith
  have hnp2 : n * p ≤ 2 * L := by linarith
  have hp0 : 0 ≤ p := by
    by_contra h; push Not at h; nlinarith
  have hp_le : p ≤ 2 * L / n := by rw [le_div_iff₀ hn0]; linarith
  have hp1 : p ≤ 1 := hp_le.trans (by rw [div_le_iff₀ hn0]; linarith)
  have hp2 : 2 * p ≤ 1 := by
    have := hp_le
    rw [le_div_iff₀ hn0] at this
    nlinarith
  -- the parameters
  set D : ℕ := ⌊L / 1000⌋₊ with hDdef
  have hD2 : (D : ℝ) ≤ L / 1000 := Nat.floor_le (by positivity)
  have hD3 : L / 1000 - 1 < D := Nat.sub_one_lt_floor _
  have hD1 : L / 2000 ≤ D := by linarith
  have hD : 1 ≤ D := by
    have : (1 : ℝ) < D := by linarith
    exact_mod_cast this.le
  set s₀ : ℕ := ⌈exp ((1 - 1 / 96000) * L)⌉₊ with hs₀def
  have hs₀ : exp ((1 - 1 / 96000) * L) ≤ s₀ := Nat.le_ceil _
  have hs₀1 : 1 ≤ s₀ := Nat.one_le_iff_ne_zero.2 (by
    rw [hs₀def, Ne, Nat.ceil_eq_zero, not_le]; exact exp_pos _)
  have hexp1 : 1 ≤ exp ((1 - 1 / 96000) * L) := Real.one_le_exp (by positivity)
  have hs₀2 : (s₀ : ℝ) ≤ 2 * exp ((1 - 1 / 96000) * L) := by
    have := Nat.ceil_lt_add_one (exp_pos ((1 - 1 / 96000) * L)).le
    rw [← hs₀def] at this
    linarith
  set u₀ : ℕ := 4 * s₀ with hu₀def
  set N : ℕ := Fintype.card (Pairs n) with hNdef
  have hN : N = n.choose 2 := card_pairs n
  have hNR : (N : ℝ) = n * (n - 1) / 2 := by rw [hN, Nat.cast_choose_two]
  set mA : ℕ := ⌈exp 2 * N * (p * (1 / 4000))⌉₊ with hmAdef
  have hmA : exp 2 * N * (p * (1 / 4000)) ≤ mA := Nat.le_ceil _
  have hmA2 : (mA : ℝ) < exp 2 * N * (p * (1 / 4000)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hpN : L * (n - 1) / 2 ≤ p * N := by
    rw [hNR]
    have : (0 : ℝ) ≤ n - 1 := by linarith
    nlinarith
  have hmAL : L ≤ mA := by
    refine le_trans ?_ hmA
    have he2 : (1 : ℝ) ≤ exp 2 := Real.one_le_exp (by norm_num)
    have : L ≤ p * N * (1 / 4000) := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hp0 (Nat.cast_nonneg N)) (by norm_num : (0 : ℝ) ≤ 1 / 4000)]
  have hmA1 : 1 ≤ mA := by
    have : (1 : ℝ) ≤ mA := by linarith
    exact_mod_cast this
  -- the tails
  set T₂ : ℝ := (1 + n * p) * (1 - p) ^ (n - 2) with hT₂def
  set T : ℝ := (exp 1 * (n * p) / D) ^ D * (1 - p) ^ (n - 6 - D) with hTdef
  have hT₂0 : 0 ≤ T₂ := mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  have hT₂ : ∀ r : ℕ, n ≤ r + 1 → r ≤ n → tailSum r p 2 ≤ T₂ :=
    fun r hr1 hr2 => tailSum_two_le hp0 hp1 hr1 hr2 (by omega)
  have hDnp : (D : ℝ) ≤ n * p := by linarith
  have hT : ∀ r : ℕ, n ≤ r + 6 → r ≤ n → tailSum r p D ≤ T :=
    fun r hr1 hr2 => tailSum_le hp0 hp1 hr1 hr2 hD hDnp
  have hD6 : 6 + D ≤ n := by
    have : (6 : ℝ) + D ≤ n := by nlinarith
    exact_mod_cast this
  have hsmall : p * (6 + D) ≤ 1 := by
    have h1 : p * (6 + D) ≤ 2 * L / n * (6 + L) := by
      gcongr
      linarith
    refine h1.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
    linarith
  have hTle := tailT_le hLn hnp1 hnp2 hD1 hD2 hD hp1 hsmall hD6
  -- the main bound
  have hmain := gnpProb_not_hamCycle_le (n := n) (p := p) (ε := 1 / 4000) (κ := 1 / 200)
    (D := D) (s₀ := s₀) (u₀ := u₀) (mA := mA) (by omega) hp0 hp1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hD (le_refl _) hT₂0 hT₂ hT0 hT
  refine hmain.trans ?_
  unfold ksErr
  -- each term
  have e1 : (n : ℝ) * T₂ ≤ 3 * exp 1 * exp (-w) :=
    degTerm_le (by omega) hLn (by linarith) hnp hnp2 hp0 hp2
  have e2 := nearTerm_le hLn (by linarith) hnp2 hT0 hTle
  have e3 := cycleTerm_le (n := n) (by linarith) hnp2 hT0 hTle
  -- dense sets
  set ρ : ℝ := 384000 * exp 1 * exp (-(L / 96000)) with hρdef
  have hρ : 12 * exp 1 * u₀ * p / D ≤ ρ := by
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
    rw [div_le_iff₀ hD0]
    have hu : (u₀ : ℝ) ≤ 8 * exp ((1 - 1 / 96000) * L) := by
      rw [hu₀def]; push_cast; linarith
    have hpexp : p * exp L ≤ 2 * L := by rw [hLn]; linarith
    have hsplit : exp ((1 - 1 / 96000) * L) = exp (-(L / 96000)) * exp L := by
      rw [← Real.exp_add]; ring_nf
    calc 12 * exp 1 * u₀ * p ≤ 12 * exp 1 * (8 * exp ((1 - 1 / 96000) * L)) * p := by gcongr
      _ = 96 * exp 1 * exp (-(L / 96000)) * (p * exp L) := by rw [hsplit]; ring
      _ ≤ 96 * exp 1 * exp (-(L / 96000)) * (2 * L) := by gcongr
      _ = ρ * (L / 2000) := by rw [hρdef]; ring
      _ ≤ ρ * D := by gcongr
  have hbigexp : 384000 * exp 1 ≤ exp (L / 192000) := by
    have h := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ L / 192000)
    have h1 := exp_one_lt_28
    have hx : (52000 : ℝ) ≤ L / 192000 := by linarith
    have hx2 : (52000 : ℝ) ^ 2 ≤ (L / 192000) ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
    linarith
  have hρhalf : ρ ≤ exp (-(L / 192000)) := by
    rw [hρdef]
    calc 384000 * exp 1 * exp (-(L / 96000)) ≤ exp (L / 192000) * exp (-(L / 96000)) := by
          gcongr
      _ = exp (-(L / 192000)) := by rw [← Real.exp_add]; ring_nf
  have hρ1 : ρ ≤ 1 := hρhalf.trans (Real.exp_le_one_iff.2 (by linarith))
  have hρ0 : 0 ≤ ρ := by positivity
  have hD12 : L / 24000 - 1 ≤ ((D / 12 : ℕ) : ℝ) := by
    have h1 : D ≤ 12 * (D / 12) + 11 := by omega
    have h2 : (D : ℝ) ≤ 12 * ((D / 12 : ℕ) : ℝ) + 11 := by exact_mod_cast h1
    linarith
  have hr4 : (n : ℝ) * ρ ^ (D / 12) ≤ exp (-L) := by
    calc (n : ℝ) * ρ ^ (D / 12) ≤ exp L * exp (-(L / 192000)) ^ (D / 12) := by
          rw [hLn]; gcongr
      _ = exp (L - L / 192000 * ((D / 12 : ℕ) : ℝ)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      _ ≤ exp (-L) := by
          refine exp_le_exp.2 ?_
          have : L / 192000 * (L / 24000 - 1) ≤ L / 192000 * ((D / 12 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hD12 (by positivity)
          nlinarith
  have e4 := denseTerm_le (n := n) (u₀ := u₀) hp0 hD hρ hρ1
    (hr4.trans (exp_neg_le_half (by linarith)))
  -- large sets of the auxiliary sample
  have hr5 : exp 3 * exp (-(L / 32000)) ≤ 1 / 2 := by
    rw [← Real.exp_add]
    exact (exp_le_exp.2 (by linarith : 3 + -(L / 32000) ≤ -1)).trans (exp_neg_le_half le_rfl)
  have e5 := largeTerm_le (n := n) (s₀ := s₀) (q := p * (1 / 4000)) hLn hs₀ hs₀1
    (by positivity) (by linarith) (by nlinarith) hr5
  -- many pairs in the auxiliary sample
  have e6 := manyTerm_le (N := N) (mA := mA) (x := p * (1 / 4000)) (by positivity) hmA hmA1 hmAL
  -- sparse expanders
  have hM : ((mA + n * D + n : ℕ) : ℝ) ≤ 1 / 200 * p * (n.choose 2 : ℕ) := by
    rw [← hN]
    push_cast
    have he2 := exp_two_le
    have hnD : (n : ℝ) * D ≤ n * (L / 1000) := by gcongr
    have hmA3 : (mA : ℝ) ≤ 7.84 * (p * N) / 4000 + 1 := by
      have : exp 2 * N * (p * (1 / 4000)) ≤ 7.84 * (p * N) / 4000 := by
        have : 0 ≤ p * N := by positivity
        nlinarith
      linarith
    nlinarith
  have e7 := sparseTerm_le (n := n) (M' := mA + n * D + n) (by omega) hp0 hp1 hnp1 hL0.le hM
  rw [← hN] at e7
  have e4' : ∑ u ∈ Icc 1 u₀, (n.choose u : ℝ) *
      (((u ^ 2).choose (D * u / 12 + 1) : ℝ) * p ^ (D * u / 12 + 1)) ≤ 2 * exp (-L) :=
    e4.trans (by linarith [hr4])
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) e4')
    e5) e6) e7

/-- **Komlós–Szemerédi (1983), upper side.** If `ω(n) → ∞`, then
`G(n, (log n + log log n + ω(n)) / n)` (edge probability clipped above at `1`) is Hamiltonian
with probability tending to `1`. -/
theorem isHamiltonian_of_log_add_loglog_add (ω : ℕ → ℝ) (hω : Tendsto ω atTop atTop) :
    Tendsto (fun n : ℕ => gnpProb n (min 1 ((Real.log n + Real.log (Real.log n) + ω n) / n))
      (fun G => G.IsHamiltonian)) atTop (nhds 1) := by
  set L : ℕ → ℝ := fun n => Real.log n with hLdef
  set w : ℕ → ℝ := fun n => min (ω n) (Real.log (L n)) with hwdef
  set q : ℕ → ℝ := fun n => (L n + Real.log (L n) + w n) / n with hqdef
  have hlogn : Tendsto L atTop atTop := tendsto_log_nat
  have hloglog : Tendsto (fun n => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogn
  have hw : Tendsto w atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hω.eventually_ge_atTop b, hloglog.eventually_ge_atTop b] with n h1 h2
    exact le_min h1 h2
  -- `L^2 / n → 0`
  have hL2 : Tendsto (fun n : ℕ => L n ^ 2 / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, hLdef] using h
  have hLn : Tendsto (fun n : ℕ => L n / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, hLdef] using h
  -- `2 log L ≤ L` for `L ≥ 0`
  have h2log : ∀ x : ℝ, 0 < x → 2 * Real.log x ≤ x := by
    intro x hx
    have h := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ x / 2)
    have : x ≤ exp (x / 2) := by nlinarith
    have := (Real.log_le_log hx this)
    rw [Real.log_exp] at this
    linarith
  have hev : ∀ᶠ n : ℕ in atTop, 8001 ≤ n ∧ 10 ^ 10 ≤ L n ∧ 0 ≤ w n ∧
      4 * L n ≤ n ∧ 2 * L n * (6 + L n) ≤ n := by
    filter_upwards [eventually_ge_atTop 8001, hlogn.eventually_ge_atTop (10 ^ 10),
      hw.eventually_ge_atTop 0, hL2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
      hLn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
      eventually_gt_atTop 0] with n h1 h2 h3 h4 h5 h6
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h6
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [div_lt_iff₀ hn0] at h5; linarith
    · rw [div_lt_iff₀ hn0] at h4 h5
      nlinarith
  have hbound : ∀ᶠ n : ℕ in atTop,
      1 - ksErr (L n) (w n) ≤ gnpProb n (min 1 ((Real.log n + Real.log (Real.log n) + ω n) / n))
        (fun G => G.IsHamiltonian) := by
    filter_upwards [hev] with n ⟨h1, h2, h3, h4, h5⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hL0 : 0 < L n := by linarith
    have hLn' : exp (L n) = n := Real.exp_log hn0
    have hwL : w n ≤ Real.log (L n) := min_le_right _ _
    have h2L := h2log (L n) hL0
    have hnq : (n : ℝ) * q n = L n + Real.log (L n) + w n := by
      rw [hqdef]; field_simp
    have hlog0 : 0 ≤ Real.log (L n) := Real.log_nonneg (by linarith)
    have hq0 : 0 ≤ q n := by
      rw [hqdef]; positivity
    have hq1 : q n ≤ 1 := by
      rw [hqdef, div_le_one hn0]; linarith
    have key := gnpProb_not_hamCycle_le_ksErr h1 hLn' h2 hnq h3 hwL h2L h4 h5
    -- from `¬ HasHamCycle` to `IsHamiltonian`
    have hP := coin_isPMF hq0 hq1 n
    have hham : 1 - ksErr (L n) (w n) ≤ gnpProb n (q n) (fun G => G.IsHamiltonian) := by
      have hnot : gnpProb n (q n) (fun G => ¬ HasHamCycle G) =
          1 - gnpProb n (q n) (fun G => HasHamCycle G) := by
        unfold gnpProb; exact pProb_not hP _
      have hmono : gnpProb n (q n) (fun G => HasHamCycle G) ≤
          gnpProb n (q n) (fun G => G.IsHamiltonian) := by
        unfold gnpProb
        exact pProb_mono hP fun ω h => HasHamCycle.isHamiltonian h (by simp; omega)
      linarith
    refine hham.trans (gnpProb_isHamiltonian_mono hq0 ?_ ?_)
    · refine le_min hq1 ?_
      show (Real.log n + Real.log (Real.log n) + w n) / n ≤ _
      gcongr
      exact min_le_left _ _
    · exact min_le_left _ _
  have hupper : ∀ᶠ n : ℕ in atTop,
      gnpProb n (min 1 ((Real.log n + Real.log (Real.log n) + ω n) / n))
        (fun G => G.IsHamiltonian) ≤ 1 := by
    filter_upwards [hev, hω.eventually_ge_atTop 0] with n hn hω0
    obtain ⟨h1, h2, -⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog0 : 0 ≤ Real.log (Real.log n) := Real.log_nonneg (by simp only [hLdef] at h2; linarith)
    have hlogn0 : 0 ≤ Real.log n := by simp only [hLdef] at h2; linarith
    have h0 : 0 ≤ min 1 ((Real.log n + Real.log (Real.log n) + ω n) / n) :=
      le_min zero_le_one (by positivity)
    exact pProb_le_one (coin_isPMF h0 (min_le_left _ _) n) _
  have herr : Tendsto (fun n => ksErr (L n) (w n)) atTop (nhds 0) := by
    have t1 : Tendsto (fun n => exp (-w n)) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hw
    have t2 : Tendsto (fun n => L n ^ 4 * exp (-(98 / 100 * L n))) atTop (nhds 0) :=
      (tendsto_pow_mul_exp_neg 4 (by norm_num)).comp hlogn
    have t3 : Tendsto (fun n => L n ^ 4 * exp (-(99 / 100 * L n))) atTop (nhds 0) :=
      (tendsto_pow_mul_exp_neg 4 (by norm_num)).comp hlogn
    have t4 : Tendsto (fun n => exp (-L n)) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlogn
    have t5 : Tendsto (fun n => exp (-(L n / 32000))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hlogn.atTop_div_const (by norm_num))
    have t6 : Tendsto (fun n => exp (1 - L n)) atTop (nhds 0) := by
      have := t4.const_mul (exp 1)
      rw [mul_zero] at this
      refine this.congr' (Eventually.of_forall fun n => ?_)
      simp only
      rw [← Real.exp_add]; ring_nf
    have := ((((((t1.const_mul (3 * exp 1)).add (t2.const_mul (64 * exp 2))).add
      (t3.const_mul (32 * exp 1))).add (t4.const_mul 2)).add
      ((t5.const_mul (exp 3)).const_mul 2)).add t4).add t6
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun n => ?_)
    simp only [ksErr]
  have hlow : Tendsto (fun n => 1 - ksErr (L n) (w n)) atTop (nhds 1) := by
    have := herr.const_sub 1
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds hbound hupper

end RandomGraphLib
