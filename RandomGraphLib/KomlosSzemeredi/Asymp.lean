/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Komlós–Szemerédi, upper side: elementary estimates

Numerical facts and the elementary inequalities used to show that the error terms of
`gnpProb_not_hamCycle_le` tend to `0`.
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real

theorem exp_one_gt_27 : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9

theorem exp_one_lt_28 : exp 1 < 2.8 := lt_trans Real.exp_one_lt_d9 (by norm_num)

theorem exp_nat_ge (k : ℕ) : (2.7 : ℝ) ^ k ≤ exp k := by
  rw [show (k : ℝ) = k * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) exp_one_gt_27.le k

theorem four_thousand_e_le : 4000 * exp 1 ≤ exp 10 := by
  have h9 := exp_nat_ge 9
  have : exp 10 = exp 9 * exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  push_cast at h9
  have : (4000 : ℝ) ≤ exp 9 := le_trans (by norm_num) h9
  nlinarith [exp_pos 1]

theorem two_hundred_le : (200 : ℝ) ≤ exp 6 := by
  have h6 := exp_nat_ge 6
  push_cast at h6
  exact le_trans (by norm_num) h6

theorem exp_two_le : exp 2 ≤ 7.84 := by
  have : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have := exp_one_lt_28
  nlinarith [exp_pos 1]

/-- `(1 - p)^k ≤ e^{-p k}`. -/
theorem one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (k : ℕ) : (1 - p) ^ k ≤ exp (-(p * k)) := by
  calc (1 - p) ^ k ≤ exp (-p) ^ k :=
        pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-p)]) k
    _ = exp (-(p * k)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- `∑_{u ∈ [a, b]} r^u ≤ 2 r` for `0 ≤ r ≤ 1/2` and `a ≥ 1`. -/
theorem sum_Icc_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) {a b : ℕ} (ha : 1 ≤ a) :
    ∑ u ∈ Icc a b, r ^ u ≤ 2 * r := by
  calc ∑ u ∈ Icc a b, r ^ u ≤ ∑ u ∈ Ico 1 (b + 1), r ^ u := by
        refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) (fun _ _ _ => by positivity)
        simp only [mem_Icc, mem_Ico] at hu ⊢
        omega
    _ ≤ r ^ 1 / (1 - r) := geom_sum_Ico_le_of_lt_one hr0 (by linarith)
    _ ≤ 2 * r := by
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith

/-- `C(n, s) ≤ (e n / s)^s`. -/
theorem choose_le_exp_div_pow (n s : ℕ) (hs : 1 ≤ s) :
    (n.choose s : ℝ) ≤ (exp 1 * n / s) ^ s := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 := Nat.choose_le_pow_div (α := ℝ) s n
  have h2 := Real.pow_div_factorial_le_exp (s : ℝ) hspos.le s
  have hf : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  calc (n.choose s : ℝ) ≤ (n : ℝ) ^ s / s.factorial := h1
    _ ≤ (n : ℝ) ^ s * (exp 1 ^ s / (s : ℝ) ^ s) := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.exp_nat_mul, mul_one, inv_le_comm₀ hf (by positivity), inv_div,
          div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hf] at h2
        linarith
    _ = (exp 1 * n / s) ^ s := by rw [div_pow, mul_pow]; ring

/-- `C(N, m) x^m ≤ (e N x / m)^m`. -/
theorem choose_mul_pow_le (N m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    (N.choose m : ℝ) * x ^ m ≤ (exp 1 * N * x / m) ^ m := by
  calc (N.choose m : ℝ) * x ^ m ≤ (exp 1 * N / m) ^ m * x ^ m :=
        mul_le_mul_of_nonneg_right (choose_le_exp_div_pow N m hm) (pow_nonneg hx _)
    _ = (exp 1 * N * x / m) ^ m := by rw [← mul_pow]; ring_nf

/-- The logarithm and `log log` limits. -/
theorem tendsto_log_nat : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `x^k e^{-c x} → 0`. -/
theorem tendsto_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun x : ℝ => x ^ k * exp (-(c * x))) Filter.atTop (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (Filter.tendsto_id.const_mul_atTop hc)
  have h2 := h.const_mul (c⁻¹ ^ k)
  rw [mul_zero] at h2
  refine h2.congr' (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, id]
  have hc1 : c⁻¹ ^ k * c ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc.ne', one_pow]
  rw [mul_pow]
  calc c⁻¹ ^ k * (c ^ k * x ^ k * exp (-(c * x))) = (c⁻¹ ^ k * c ^ k) * x ^ k * exp (-(c * x)) := by
        ring
    _ = x ^ k * exp (-(c * x)) := by rw [hc1, one_mul]

end RandomGraphLib
