/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Round

/-!
# Komlós–Szemerédi, upper side: the union bound over sparse expanders

If `G = G(n, p)` has no Hamiltonian cycle but contains a connected graph `H` on at most `M` pairs
in which every set of at most `n / 4` vertices expands by a factor two, then adding at most `n`
edges of `G` to `H` (`exists_boost_closure`) gives a graph `H'` on at most `M + n` pairs, contained
in `G`, without Hamiltonian cycle and with at least `(n / 4 + 1)² / 2` boosters (`booster_count`),
none of which is an edge of `G`. The union bound over `H'` gives `sparse_bound`; the weighted
number of sets of at most `M` pairs is at most `κ^{-M} e^{κ x N}` (`sum_sets_card_le`).
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Pseudorandom Pseudorandom.RandomGraphs

variable {n : ℕ}

theorem setGraph_le_graphOf {ω : Pairs n → Bool} {F : Finset (Pairs n)}
    (h : ∀ e ∈ F, ω e = true) : setGraph F ≤ graphOf ω :=
  graphOf_mono fun e he => h e (of_decide_eq_true he)

theorem setGraph_union (F F' : Finset (Pairs n)) :
    setGraph (F ∪ F') = setGraph F ⊔ setGraph F' := by
  classical
  rw [setGraph, setGraph, setGraph, ← graphOf_or]
  congr 1
  funext e
  simp [mem_union]

theorem disjoint_boostPairs_setGraph (F : Finset (Pairs n)) :
    Disjoint F (boostPairs (setGraph F)) := by
  classical
  rw [disjoint_left]
  intro e heF heB
  simp only [boostPairs, boosterSet, mem_filter, mem_univ, true_and] at heB
  obtain ⟨u, v, he, hb⟩ := heB
  apply hb.1
  rw [setGraph, graphOf_adj_iff _ e u v he]
  simpa using heF

/-- **The union bound over sparse expanders.** -/
theorem sparse_bound (hk : 1 ≤ n / 4) (M : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    pProb (coin p n) (fun ω => ¬ HasHamCycle (graphOf ω) ∧ ∃ F : Finset (Pairs n), F.card ≤ M ∧
        (∀ e ∈ F, ω e = true) ∧ (setGraph F).Connected ∧ IsExpander (setGraph F) (n / 4)) ≤
      ∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ M + n),
        p ^ F.card * (1 - p) ^ ((n / 4 + 1) ^ 2 / 2) := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  set Good : Finset (Pairs n) → Prop := fun F =>
    (setGraph F).Connected ∧ IsExpander (setGraph F) (n / 4) ∧ ¬ HasHamCycle (setGraph F)
    with hGood
  have hwit : ∀ ω : Pairs n → Bool, (¬ HasHamCycle (graphOf ω) ∧ ∃ F : Finset (Pairs n),
      F.card ≤ M ∧ (∀ e ∈ F, ω e = true) ∧ (setGraph F).Connected ∧
        IsExpander (setGraph F) (n / 4)) →
      ∃ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ M + n),
        Good F ∧ ((∀ e ∈ F, ω e = true) ∧ ∀ e ∈ boostPairs (setGraph F), ω e = false) := by
    rintro ω ⟨hH, F, hFM, hFω, hconn, hexp⟩
    have hle := setGraph_le_graphOf hFω
    have hsup : setGraph F ⊔ graphOf ω = graphOf ω := sup_eq_right.2 hle
    obtain ⟨F₀, hcard, hsub, hham, hboost⟩ :=
      exists_boost_closure (setGraph F) (graphOf ω) (by rwa [hsup])
    set F₁ : Finset (Pairs n) := univ.filter fun e => e.1 ∈ F₀ with hF₁def
    have hgraph : setGraph F₁ = SimpleGraph.fromEdgeSet ↑F₀ := by
      ext u v
      simp only [setGraph, graphOf_adj, hF₁def, mem_filter, mem_univ, true_and,
        decide_eq_true_eq, SimpleGraph.fromEdgeSet_adj, mem_coe]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨h', h⟩
      · rintro ⟨h', h⟩; exact ⟨h, h'⟩
    have hU : setGraph (F ∪ F₁) = setGraph F ⊔ SimpleGraph.fromEdgeSet ↑F₀ := by
      rw [setGraph_union, hgraph]
    have hleU : setGraph F ≤ setGraph (F ∪ F₁) := by rw [hU]; exact le_sup_left
    have hF₁card : F₁.card ≤ n := by
      refine le_trans ?_ (hcard.trans_eq (Fintype.card_fin n))
      refine card_le_card_of_injOn Subtype.val (fun e he => ?_) Subtype.val_injective.injOn
      simpa [hF₁def] using he
    refine ⟨F ∪ F₁, mem_filter.2 ⟨mem_powerset.2 (subset_univ _), ?_⟩,
      ⟨hconn.mono hleU, hexp.mono hleU, hU ▸ hham⟩, ?_, ?_⟩
    · exact (card_union_le _ _).trans (by omega)
    · intro e he
      rcases mem_union.1 he with he | he
      · exact hFω e he
      · have he' : e.1 ∈ F₀ := by simpa [hF₁def] using he
        obtain ⟨u, v, huv⟩ := exists_eq_sym2_mk e.1
        have := hsub _ he'
        rw [huv, SimpleGraph.mem_edgeSet] at this
        exact (graphOf_adj_iff ω e u v huv).1 this
    · intro e he
      simp only [boostPairs, boosterSet, mem_filter, mem_univ, true_and] at he
      obtain ⟨u, v, huv, hb⟩ := he
      rw [hU] at hb
      have := hboost u v hb
      rw [graphOf_adj_iff ω e u v huv] at this
      simpa using this
  refine (pProb_mono hP fun ω h => hwit ω h).trans ?_
  refine (pProb_exists_le hP _ _).trans (sum_le_sum fun F hF => ?_)
  by_cases hg : Good F
  · rw [pProb_congr (T := fun ω => (∀ e ∈ F, ω e = true) ∧ ∀ e ∈ boostPairs (setGraph F),
        ω e = false) (fun ω => ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩),
      pProb_coin_present_absent hp0 hp1 _ _ (disjoint_boostPairs_setGraph F)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hp0 _)
    refine pow_le_pow_of_le_one (by linarith) (by linarith) ?_
    have hcount := booster_count hk hg.2.1 hg.1 hg.2.2
    have := card_boosterSet_le (setGraph F)
    exact Nat.div_le_of_le_mul (by omega)
  · rw [pProb_congr (T := fun _ => False) (fun ω => ⟨fun h => hg h.1, False.elim⟩),
      pProb_false]
    positivity

/-- The weighted number of sets of at most `M` pairs. -/
theorem sum_sets_card_le (M : ℕ) {x κ : ℝ} (hx : 0 ≤ x) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ M), x ^ F.card ≤
      κ⁻¹ ^ M * exp (κ * x * Fintype.card (Pairs n)) := by
  classical
  have hterm : ∀ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ M),
      x ^ F.card ≤ κ⁻¹ ^ M * (κ * x) ^ F.card := by
    intro F hF
    have hFM := (mem_filter.1 hF).2
    have h1 : κ ^ M ≤ κ ^ F.card := pow_le_pow_of_le_one hκ0.le hκ1 hFM
    calc x ^ F.card = κ⁻¹ ^ M * (κ ^ M * x ^ F.card) := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hκ0.ne', one_pow, one_mul]
      _ ≤ κ⁻¹ ^ M * (κ ^ F.card * x ^ F.card) := by gcongr
      _ = κ⁻¹ ^ M * (κ * x) ^ F.card := by rw [mul_pow]
  have hκx : 0 ≤ κ * x := mul_nonneg hκ0.le hx
  calc ∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ M), x ^ F.card
      ≤ ∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ M),
          κ⁻¹ ^ M * (κ * x) ^ F.card := sum_le_sum hterm
    _ ≤ ∑ F ∈ (univ : Finset (Pairs n)).powerset, κ⁻¹ ^ M * (κ * x) ^ F.card :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = κ⁻¹ ^ M * (κ * x + 1) ^ Fintype.card (Pairs n) := by
        rw [← mul_sum, ← card_univ, ← sum_pow_mul_eq_add_pow]
        simp
    _ ≤ κ⁻¹ ^ M * exp (κ * x * Fintype.card (Pairs n)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (κ * x + 1) ^ Fintype.card (Pairs n) ≤ exp (κ * x) ^ Fintype.card (Pairs n) :=
              pow_le_pow_left₀ (by positivity) (add_one_le_exp _) _
          _ = exp (κ * x * Fintype.card (Pairs n)) := by rw [← Real.exp_nat_mul]; ring_nf

end RandomGraphLib
