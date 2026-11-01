/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RandomGraphLib.KomlosSzemeredi.Asymp

/-!
# Komlós–Szemerédi, upper side: the error terms

Each error term of `gnpProb_not_hamCycle_le` is bounded by an explicit function of
`L = log n` (and of `ω`), under inequalities that hold for large `n`.
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real

/-- The degree term: `n (1 + n p) (1 - p)^{n - 2} ≤ 3 e e^{-w}` when `n p = L + log L + w`. -/
theorem degTerm_le {n : ℕ} {p L w : ℝ} (hn : 2 ≤ n) (hLn : exp L = n) (hL1 : 1 ≤ L)
    (hnp : n * p = L + Real.log L + w) (hnp2 : n * p ≤ 2 * L) (hp0 : 0 ≤ p) (hp2 : 2 * p ≤ 1) :
    n * ((1 + n * p) * (1 - p) ^ (n - 2)) ≤ 3 * exp 1 * exp (-w) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 < L := by linarith
  have h1 : (1 - p) ^ (n - 2) ≤ exp (-(n * p)) * exp 1 := by
    refine (one_sub_pow_le_exp (by linarith) _).trans ?_
    rw [← Real.exp_add]
    refine exp_le_exp.2 ?_
    have : ((n - 2 : ℕ) : ℝ) = n - 2 := by rw [Nat.cast_sub hn]; push_cast; ring
    rw [this]
    nlinarith
  have h2 : exp (-(n * p)) = exp (-w) / (n * L) := by
    rw [hnp, show -(L + Real.log L + w) = -w - (L + Real.log L) by ring, Real.exp_sub,
      Real.exp_add, hLn, Real.exp_log hL0]
  calc n * ((1 + n * p) * (1 - p) ^ (n - 2))
      ≤ n * ((1 + n * p) * (exp (-(n * p)) * exp 1)) := by
        gcongr
    _ = exp 1 * exp (-w) * ((1 + n * p) / L) := by
        rw [h2]; field_simp
    _ ≤ exp 1 * exp (-w) * 3 := by
        gcongr
        rw [div_le_iff₀ hL0]
        linarith
    _ = 3 * exp 1 * exp (-w) := by ring

/-- The small-degree tail: `T ≤ e^{1 - 99 L / 100}`. -/
theorem tailT_le {n D : ℕ} {p L : ℝ} (hLn : exp L = n) (hnp1 : L ≤ n * p)
    (hnp2 : n * p ≤ 2 * L) (hD1 : L / 2000 ≤ D) (hD2 : (D : ℝ) ≤ L / 1000) (hD : 1 ≤ D)
    (hp1 : p ≤ 1) (hsmall : p * (6 + D) ≤ 1) (hn : 6 + D ≤ n) :
    (exp 1 * (n * p) / D) ^ D * (1 - p) ^ (n - 6 - D) ≤ exp (1 - 99 / 100 * L) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hL0 : 0 < L := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have ha0 : 0 ≤ exp 1 * (n * p) / D := by
    have : 0 ≤ n * p := by linarith
    positivity
  have ha : exp 1 * (n * p) / D ≤ exp 10 := by
    rw [div_le_iff₀ hD0]
    have := four_thousand_e_le
    have h1 : exp 1 * (n * p) ≤ exp 1 * (2 * L) := by gcongr
    have h2 : exp 1 * (2 * L) ≤ 4000 * exp 1 * (L / 2000) := by ring_nf; rfl
    calc exp 1 * (n * p) ≤ 4000 * exp 1 * (L / 2000) := h1.trans h2
      _ ≤ exp 10 * D := by gcongr
  have h1 : (exp 1 * (n * p) / D) ^ D ≤ exp (L / 100) := by
    calc (exp 1 * (n * p) / D) ^ D ≤ exp 10 ^ D := pow_le_pow_left₀ ha0 ha D
      _ = exp (10 * D) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ exp (L / 100) := exp_le_exp.2 (by linarith)
  have h2 : (1 - p) ^ (n - 6 - D) ≤ exp (1 - L) := by
    refine (one_sub_pow_le_exp hp1 _).trans (exp_le_exp.2 ?_)
    have : ((n - 6 - D : ℕ) : ℝ) = n - 6 - D := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]
    nlinarith
  calc (exp 1 * (n * p) / D) ^ D * (1 - p) ^ (n - 6 - D) ≤ exp (L / 100) * exp (1 - L) :=
        mul_le_mul h1 h2 (pow_nonneg (by linarith) _) (exp_pos _).le
    _ = exp (1 - 99 / 100 * L) := by rw [← Real.exp_add]; ring_nf

/-- The near-pairs term. -/
theorem nearTerm_le {n : ℕ} {p L T : ℝ} (hLn : exp L = n) (hnp1 : 1 ≤ n * p)
    (hnp2 : n * p ≤ 2 * L) (hT0 : 0 ≤ T) (hT : T ≤ exp (1 - 99 / 100 * L)) :
    ∑ m ∈ Icc 1 4, (n : ℝ) ^ (m + 1) * (p ^ m * T ^ 2) ≤
      64 * exp 2 * (L ^ 4 * exp (-(98 / 100 * L))) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hL0 : 0 ≤ L := by linarith
  have hT2 : T ^ 2 ≤ exp (2 - 198 / 100 * L) := by
    calc T ^ 2 ≤ exp (1 - 99 / 100 * L) ^ 2 := pow_le_pow_left₀ hT0 hT 2
      _ = exp (2 - 198 / 100 * L) := by rw [← Real.exp_nat_mul]; ring_nf
  have hterm : ∀ m ∈ Icc 1 4, (n : ℝ) ^ (m + 1) * (p ^ m * T ^ 2) ≤
      n * ((2 * L) ^ 4 * exp (2 - 198 / 100 * L)) := by
    intro m hm
    have hm := mem_Icc.1 hm
    have h1 : (n * p) ^ m ≤ (2 * L) ^ 4 :=
      (pow_le_pow_right₀ hnp1 hm.2).trans (pow_le_pow_left₀ (by linarith) hnp2 4)
    calc (n : ℝ) ^ (m + 1) * (p ^ m * T ^ 2) = n * ((n * p) ^ m * T ^ 2) := by ring
      _ ≤ n * ((2 * L) ^ 4 * exp (2 - 198 / 100 * L)) := by gcongr
  calc ∑ m ∈ Icc 1 4, (n : ℝ) ^ (m + 1) * (p ^ m * T ^ 2)
      ≤ ∑ _m ∈ Icc 1 4, (n : ℝ) * ((2 * L) ^ 4 * exp (2 - 198 / 100 * L)) := sum_le_sum hterm
    _ = 4 * (n * ((2 * L) ^ 4 * exp (2 - 198 / 100 * L))) := by simp
    _ = 64 * exp 2 * (L ^ 4 * exp (-(98 / 100 * L))) := by
        rw [← hLn]
        have : exp L * exp (2 - 198 / 100 * L) = exp 2 * exp (-(98 / 100 * L)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        calc 4 * (exp L * ((2 * L) ^ 4 * exp (2 - 198 / 100 * L)))
            = 64 * L ^ 4 * (exp L * exp (2 - 198 / 100 * L)) := by ring
          _ = 64 * exp 2 * (L ^ 4 * exp (-(98 / 100 * L))) := by rw [this]; ring

/-- The short-cycle term. -/
theorem cycleTerm_le {n : ℕ} {p L T : ℝ} (hnp1 : 1 ≤ n * p) (hnp2 : n * p ≤ 2 * L)
    (hT0 : 0 ≤ T) (hT : T ≤ exp (1 - 99 / 100 * L)) :
    ∑ k ∈ range 2, (n : ℝ) ^ (k + 3) * (p ^ (k + 3) * T) ≤
      32 * exp 1 * (L ^ 4 * exp (-(99 / 100 * L))) := by
  have hL0 : 0 ≤ L := by linarith
  have hterm : ∀ k ∈ range 2, (n : ℝ) ^ (k + 3) * (p ^ (k + 3) * T) ≤
      (2 * L) ^ 4 * exp (1 - 99 / 100 * L) := by
    intro k hk
    have hk := mem_range.1 hk
    have h1 : (n * p) ^ (k + 3) ≤ (2 * L) ^ 4 :=
      (pow_le_pow_right₀ hnp1 (by omega)).trans (pow_le_pow_left₀ (by linarith) hnp2 4)
    calc (n : ℝ) ^ (k + 3) * (p ^ (k + 3) * T) = (n * p) ^ (k + 3) * T := by ring
      _ ≤ (2 * L) ^ 4 * exp (1 - 99 / 100 * L) := mul_le_mul h1 hT hT0 (by positivity)
  calc ∑ k ∈ range 2, (n : ℝ) ^ (k + 3) * (p ^ (k + 3) * T)
      ≤ ∑ _k ∈ range 2, (2 * L) ^ 4 * exp (1 - 99 / 100 * L) := sum_le_sum hterm
    _ = 32 * exp 1 * (L ^ 4 * exp (-(99 / 100 * L))) := by
        rw [sum_const, card_range, show (1 : ℝ) - 99 / 100 * L = 1 + -(99 / 100 * L) by ring,
          Real.exp_add]
        simp only [nsmul_eq_mul]
        push_cast
        ring

/-- The dense-sets term. -/
theorem denseTerm_le {n u₀ D : ℕ} {p ρ : ℝ} (hp0 : 0 ≤ p) (hD : 1 ≤ D)
    (hρ : 12 * exp 1 * u₀ * p / D ≤ ρ) (hρ1 : ρ ≤ 1)
    (hr : (n : ℝ) * ρ ^ (D / 12) ≤ 1 / 2) :
    ∑ u ∈ Icc 1 u₀, (n.choose u : ℝ) *
        (((u ^ 2).choose (D * u / 12 + 1) : ℝ) * p ^ (D * u / 12 + 1)) ≤
      2 * ((n : ℝ) * ρ ^ (D / 12)) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  refine le_trans (sum_le_sum fun u hu => ?_) (sum_Icc_pow_le (by positivity) hr le_rfl)
  have hu := mem_Icc.1 hu
  set m := D * u / 12 + 1 with hm
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu.1
  have hm1 : 1 ≤ m := by omega
  have hmR : (D : ℝ) * u / 12 ≤ m := by
    have : D * u ≤ 12 * m := by omega
    rw [div_le_iff₀ (by norm_num)]
    exact_mod_cast (by linarith : (D * u : ℕ) ≤ m * 12)
  have hbase : exp 1 * ((u ^ 2 : ℕ) : ℝ) * p / m ≤ ρ := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    calc exp 1 * ((u ^ 2 : ℕ) : ℝ) * p / m ≤ exp 1 * ((u ^ 2 : ℕ) : ℝ) * p / (D * u / 12) := by
          gcongr
      _ = 12 * exp 1 * u * p / D := by push_cast; field_simp
      _ ≤ 12 * exp 1 * u₀ * p / D := by
          gcongr
          exact_mod_cast hu.2
      _ ≤ ρ := hρ
  have hexp : u * (D / 12) ≤ m := by
    have : u * (D / 12) ≤ D * u / 12 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      calc u * (D / 12) * 12 = u * (D / 12 * 12) := by ring
        _ ≤ u * D := Nat.mul_le_mul_left _ (Nat.div_mul_le_self D 12)
        _ = D * u := by ring
    omega
  calc (n.choose u : ℝ) * (((u ^ 2).choose m : ℝ) * p ^ m)
      ≤ (n : ℝ) ^ u * ρ ^ m := by
        refine mul_le_mul (by exact_mod_cast Nat.choose_le_pow n u) ?_ (by positivity)
          (by positivity)
        refine (choose_mul_pow_le _ m hm1 hp0).trans ?_
        exact pow_le_pow_left₀ (by positivity) hbase m
    _ ≤ (n : ℝ) ^ u * ρ ^ (u * (D / 12)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 hexp) (by positivity)
    _ = ((n : ℝ) * ρ ^ (D / 12)) ^ u := by rw [mul_pow, ← pow_mul, Nat.mul_comm (D / 12) u]

/-- The large-sets term. -/
theorem largeTerm_le {n s₀ : ℕ} {q L : ℝ} (hLn : exp L = n) (hs₀ : exp ((1 - 1 / 96000) * L) ≤ s₀)
    (hs₀1 : 1 ≤ s₀) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqn : L / 4000 ≤ q * n)
    (hr : exp 3 * exp (-(L / 32000)) ≤ 1 / 2) :
    ∑ s ∈ Icc s₀ (n / 4), (n.choose s : ℝ) * ((n.choose (2 * s) : ℝ) *
      (1 - q) ^ (s * (n - 3 * s))) ≤ 2 * (exp 3 * exp (-(L / 32000))) := by
  refine le_trans (sum_le_sum fun s hs => ?_) (sum_Icc_pow_le (by positivity) hr hs₀1)
  have hs := mem_Icc.1 hs
  have h4 : 4 * s ≤ n := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).1 hs.2; omega
  have hs1 : 1 ≤ s := hs₀1.trans hs.1
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsR : exp ((1 - 1 / 96000) * L) ≤ s := hs₀.trans (by exact_mod_cast hs.1)
  -- `e n / s ≤ e^{1 + L / 96000}`
  have hbase : exp 1 * n / s ≤ exp (1 + L / 96000) := by
    rw [div_le_iff₀ hs0, ← hLn]
    calc exp 1 * exp L = exp (1 + L / 96000) * exp ((1 - 1 / 96000) * L) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ exp (1 + L / 96000) * s := by gcongr
  have hb0 : 0 ≤ exp 1 * n / s := by positivity
  have h1 : (n.choose s : ℝ) ≤ exp (1 + L / 96000) ^ s :=
    (choose_le_exp_div_pow n s hs1).trans (pow_le_pow_left₀ hb0 hbase s)
  have h2 : (n.choose (2 * s) : ℝ) ≤ exp (1 + L / 96000) ^ (2 * s) := by
    refine (choose_le_exp_div_pow n (2 * s) (by omega)).trans
      (pow_le_pow_left₀ (by positivity) (le_trans ?_ hbase) _)
    gcongr
    · exact_mod_cast (by omega : s ≤ 2 * s)
  have h3 : (1 - q) ^ (s * (n - 3 * s)) ≤ exp (-(q * n / 4)) ^ s := by
    refine (one_sub_pow_le_exp hq1 _).trans ?_
    rw [← Real.exp_nat_mul]
    refine exp_le_exp.2 ?_
    have hc : ((s * (n - 3 * s) : ℕ) : ℝ) = s * (n - 3 * s) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc]
    have h4' : (4 : ℝ) * s ≤ n := by exact_mod_cast h4
    nlinarith [mul_nonneg (mul_nonneg hq0 hs0.le) (sub_nonneg.2 h4')]
  calc (n.choose s : ℝ) * ((n.choose (2 * s) : ℝ) * (1 - q) ^ (s * (n - 3 * s)))
      ≤ exp (1 + L / 96000) ^ s * (exp (1 + L / 96000) ^ (2 * s) * exp (-(q * n / 4)) ^ s) := by
        gcongr
    _ = (exp (3 * (1 + L / 96000)) * exp (-(q * n / 4))) ^ s := by
        have ha3 : exp (3 * (1 + L / 96000)) = exp (1 + L / 96000) ^ 3 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [mul_pow, ha3, ← pow_mul]
        ring
    _ ≤ (exp 3 * exp (-(L / 32000))) ^ s := by
        refine pow_le_pow_left₀ (by positivity) ?_ s
        rw [← Real.exp_add, ← Real.exp_add]
        refine exp_le_exp.2 ?_
        linarith

/-- The many-pairs term. -/
theorem manyTerm_le {N mA : ℕ} {x L : ℝ} (hx : 0 ≤ x) (hmA : exp 2 * N * x ≤ mA)
    (hmA1 : 1 ≤ mA) (hL : L ≤ mA) :
    (N.choose mA : ℝ) * x ^ mA ≤ exp (-L) := by
  have hm0 : (0 : ℝ) < mA := by exact_mod_cast hmA1
  refine (choose_mul_pow_le N mA hmA1 hx).trans ?_
  have hb : exp 1 * N * x / mA ≤ exp (-1) := by
    rw [div_le_iff₀ hm0]
    have h12 : exp 1 = exp 2 * exp (-1) := by rw [← Real.exp_add]; norm_num
    calc exp 1 * N * x = exp (-1) * (exp 2 * N * x) := by rw [h12]; ring
      _ ≤ exp (-1) * mA := by gcongr
  calc (exp 1 * N * x / mA) ^ mA ≤ exp (-1) ^ mA := pow_le_pow_left₀ (by positivity) hb _
    _ = exp (-(mA : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ exp (-L) := exp_le_exp.2 (by linarith)

/-- The sparse-expanders term. -/
theorem sparseTerm_le {n M' : ℕ} {p L : ℝ} (hn : 73 ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hnp : L ≤ n * p) (hL : 0 ≤ L) (hM : (M' : ℝ) ≤ 1 / 200 * p * (n.choose 2 : ℕ)) :
    (1 / 200 : ℝ)⁻¹ ^ M' * exp (1 / 200 * p * (n.choose 2 : ℕ)) *
      (1 - p) ^ ((n / 4 + 1) ^ 2 / 2) ≤ exp (1 - L) := by
  have hN : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hk : (n : ℝ) ^ 2 / 32 - 1 ≤ ((n / 4 + 1) ^ 2 / 2 : ℕ) := by
    have h1 : (n : ℝ) / 4 ≤ ((n / 4 + 1 : ℕ) : ℝ) := by
      have : n < (n / 4 + 1) * 4 := by omega
      have : (n : ℝ) < ((n / 4 + 1 : ℕ) : ℝ) * 4 := by exact_mod_cast this
      linarith
    have h2 : (n : ℝ) ^ 2 / 16 ≤ (((n / 4 + 1) ^ 2 : ℕ) : ℝ) := by
      push_cast at h1 ⊢
      have : (0 : ℝ) ≤ n / 4 := by positivity
      nlinarith
    have h3 : (((n / 4 + 1) ^ 2 : ℕ) : ℝ) ≤ 2 * (((n / 4 + 1) ^ 2 / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.lt_succ_iff.1 (Nat.lt_div_mul_add (a := (n / 4 + 1) ^ 2) (by norm_num : 0 < 2))
      have : (n / 4 + 1) ^ 2 ≤ 2 * ((n / 4 + 1) ^ 2 / 2) + 1 := by omega
      exact_mod_cast this
    linarith
  have h200 : (1 / 200 : ℝ)⁻¹ ^ M' ≤ exp (6 * (1 / 200 * p * (n.choose 2 : ℕ))) := by
    rw [show (1 / 200 : ℝ)⁻¹ = 200 by norm_num]
    calc (200 : ℝ) ^ M' ≤ exp 6 ^ M' := pow_le_pow_left₀ (by norm_num) two_hundred_le _
      _ = exp (6 * M') := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ exp (6 * (1 / 200 * p * (n.choose 2 : ℕ))) := exp_le_exp.2 (by linarith)
  have hq : (1 - p) ^ ((n / 4 + 1) ^ 2 / 2) ≤ exp (-(p * ((n : ℝ) ^ 2 / 32 - 1))) := by
    refine (one_sub_pow_le_exp hp1 _).trans (exp_le_exp.2 ?_)
    nlinarith
  calc (1 / 200 : ℝ)⁻¹ ^ M' * exp (1 / 200 * p * (n.choose 2 : ℕ)) *
        (1 - p) ^ ((n / 4 + 1) ^ 2 / 2)
      ≤ exp (6 * (1 / 200 * p * (n.choose 2 : ℕ))) * exp (1 / 200 * p * (n.choose 2 : ℕ)) *
          exp (-(p * ((n : ℝ) ^ 2 / 32 - 1))) := by gcongr
    _ = exp (7 / 200 * p * (n.choose 2 : ℕ) - p * ((n : ℝ) ^ 2 / 32 - 1)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ exp (1 - L) := by
        refine exp_le_exp.2 ?_
        have h73 : (73 : ℝ) ≤ n := by exact_mod_cast hn
        have hpn : 0 ≤ p * n := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hN hp0]

end RandomGraphLib
