/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Isolated
public import PseudorandomLib.RandomGraphs.Crossing
public import PseudorandomLib.RandomGraphs.Round

/-!
# Komlós–Szemerédi, lower side: pendant vertices below `(log n + log log n - ω) / n`

A vertex of degree one lies on no Hamiltonian cycle. We count the ordered pairs `(v, w)` such
that `w` is the only neighbour of `v` (`IsPendant`). Each is a cylinder event of probability
`p (1 - p)^{n - 2}`, and two of them are either incompatible, the same edge seen from both ends,
or nearly independent. The second moment method gives

`P(G(n, p) Hamiltonian) ≤ 1 / μ + (1 / (1 - p) - 1) + 1 / (n (n - 1) p)`,
`μ = n (n - 1) p (1 - p)^{n - 2}` (`gnpProb_isHamiltonian_le`),

and `not_isHamiltonian_of_log_add_loglog_sub`: for `p = (log n + log log n - ω(n)) / n` with
`ω → ∞`, `G(n, p)` is Hamiltonian with probability tending to `0`.
-/

@[expose] public section

namespace RandomGraphLib

open Finset Real Filter Pseudorandom Pseudorandom.RandomGraphs

variable {n : ℕ}

/-- `w` is the only neighbour of `v`. -/
def IsPendant (G : SimpleGraph (Fin n)) (v w : Fin n) : Prop :=
  G.Adj v w ∧ ∀ x, G.Adj v x → x = w

/-- A Hamiltonian graph on at least three vertices has no vertex of degree one. -/
theorem not_isPendant_of_isHamiltonian {G : SimpleGraph (Fin n)} (hn : 3 ≤ n)
    (hG : G.IsHamiltonian) (v w : Fin n) : ¬ IsPendant G v w := by
  rintro ⟨-, hw⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨c, hc⟩ := hG.exists_isHamiltonianCycle v
  have hnil : ¬ c.Nil := hc.isCycle.not_nil
  have h1 := hw _ (c.adj_snd hnil)
  have h2 := hw _ (c.adj_penultimate hnil).symm
  exact hc.isCycle.snd_ne_penultimate (h1.trans h2.symm)

/-- The pair `{v, w}`. -/
def edgePairs (v w : Fin n) : Finset (Pairs n) := univ.filter fun e => e.1 = s(v, w)

/-- The pairs at `v` other than `{v, w}`. -/
def starPairs (v w : Fin n) : Finset (Pairs n) := univ.filter fun e => v ∈ e.1 ∧ e.1 ≠ s(v, w)

theorem card_edgePairs {v w : Fin n} (h : v ≠ w) : (edgePairs v w).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨s(v, w), by simpa using h⟩, ?_⟩
  ext e
  simp only [edgePairs, mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun he => Subtype.ext he, fun he => by rw [he]⟩

/-- The pairs at `v` correspond to the other vertices. -/
theorem card_pairs_at (v : Fin n) : (univ.filter fun e : Pairs n => v ∈ e.1).card = n - 1 := by
  have : (univ.filter fun e : Pairs n => v ∈ e.1) =
      (univ.erase v).attach.image fun x => (⟨s(v, x.1), by
        simpa [eq_comm] using (mem_erase.1 x.2).1⟩ : Pairs n) := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_attach]
    constructor
    · intro he
      obtain ⟨e, hd⟩ := e
      obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 he
      have hx : x ≠ v := fun h => hd (by rw [h]; exact Sym2.mk_isDiag_iff.2 rfl)
      exact ⟨⟨x, mem_erase.2 ⟨hx, mem_univ _⟩⟩, Subtype.ext rfl⟩
    · rintro ⟨x, -, rfl⟩
      exact Sym2.mem_mk_left _ _
  rw [this, card_image_of_injective _ (fun x y hxy => by
      simp only [Subtype.mk.injEq, Sym2.eq_iff, true_and] at hxy
      rcases hxy with h | ⟨h1, h2⟩
      · exact Subtype.ext h
      · exact Subtype.ext (h2.trans h1)),
    card_attach, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

theorem card_starPairs {v w : Fin n} (h : v ≠ w) : (starPairs v w).card = n - 2 := by
  have hsub : starPairs v w = (univ.filter fun e : Pairs n => v ∈ e.1) \ edgePairs v w := by
    ext e
    simp [starPairs, edgePairs]
  have hle : edgePairs v w ⊆ univ.filter fun e : Pairs n => v ∈ e.1 := by
    intro e he
    simp only [edgePairs, mem_filter, mem_univ, true_and] at he ⊢
    rw [he]
    exact Sym2.mem_mk_left _ _
  rw [hsub, card_sdiff_of_subset hle, card_pairs_at, card_edgePairs h]
  omega

theorem isPendant_graphOf_iff {ω : Pairs n → Bool} {v w : Fin n} (h : v ≠ w) :
    IsPendant (graphOf ω) v w ↔
      (∀ e ∈ edgePairs v w, ω e = true) ∧ ∀ e ∈ starPairs v w, ω e = false := by
  constructor
  · rintro ⟨hvw, hw⟩
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · simp only [edgePairs, mem_filter, mem_univ, true_and] at he
      exact (graphOf_adj_iff ω e v w he).1 hvw
    · simp only [starPairs, mem_filter, mem_univ, true_and] at he
      obtain ⟨hv, hne⟩ := he
      obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 hv
      by_contra hω
      have hadj : (graphOf ω).Adj v x := (graphOf_adj_iff ω e v x hx).2 (by simpa using hω)
      exact hne (by rw [hx, hw x hadj])
  · rintro ⟨h1, h2⟩
    have hvw : (graphOf ω).Adj v w :=
      (graphOf_adj_iff ω ⟨s(v, w), by simpa using h⟩ v w rfl).2
        (h1 _ (by simp [edgePairs]))
    refine ⟨hvw, fun x hx => ?_⟩
    by_contra hxw
    have hvx : v ≠ x := (graphOf ω).ne_of_adj hx
    have := (graphOf_adj_iff ω ⟨s(v, x), by simpa using hvx⟩ v x rfl).1 hx
    have hmem : (⟨s(v, x), by simpa using hvx⟩ : Pairs n) ∈ starPairs v w := by
      simp only [starPairs, mem_filter, mem_univ, true_and, Sym2.mem_mk_left]
      intro he
      apply hxw
      rcases Sym2.eq_iff.1 he with ⟨-, h'⟩ | ⟨h', -⟩
      · exact h'
      · exact absurd h' h
    rw [h2 _ hmem] at this
    exact Bool.false_ne_true this

theorem disjoint_edgePairs_starPairs (v w : Fin n) : Disjoint (edgePairs v w) (starPairs v w) := by
  rw [disjoint_left]
  intro e he he'
  simp only [edgePairs, starPairs, mem_filter, mem_univ, true_and] at he he'
  exact he'.2 he

theorem gnpProb_isPendant {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {v w : Fin n} (h : v ≠ w) :
    gnpProb n p (fun G => IsPendant G v w) = p * (1 - p) ^ (n - 2) := by
  unfold gnpProb
  rw [pProb_congr fun ω => isPendant_graphOf_iff h,
    pProb_coin_present_absent hp0 hp1 _ _ (disjoint_edgePairs_starPairs v w),
    card_edgePairs h, card_starPairs h, pow_one]

/-- Two pendant pairs with different first vertex, neither pointing at the other: the event is
contained in a cylinder with two present and `2n - 5` absent pairs. -/
theorem gnpProb_isPendant_pair_generic {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 3 ≤ n)
    {v w v' w' : Fin n} (hvw : v ≠ w) (hvw' : v' ≠ w') (hvv : v ≠ v') (hwv : w ≠ v')
    (hwv' : w' ≠ v) :
    gnpProb n p (fun G => IsPendant G v w ∧ IsPendant G v' w') ≤
      p ^ 2 * (1 - p) ^ (2 * n - 5) := by
  classical
  set F := edgePairs v w ∪ edgePairs v' w' with hF
  set B := starPairs v w ∪ ((starPairs v' w').filter fun e => v ∉ e.1) with hB
  have hFB : Disjoint F B := by
    rw [disjoint_left]
    intro e he he'
    simp only [hF, hB, edgePairs, starPairs, mem_union, mem_filter, mem_univ, true_and] at he he'
    rcases he with he | he <;> rcases he' with ⟨hv, hne⟩ | ⟨⟨hv, hne⟩, hnv⟩
    · exact hne he
    · exact hnv (by rw [he]; exact Sym2.mem_mk_left _ _)
    · rw [he] at hv
      rcases Sym2.mem_iff.1 hv with h' | h'
      · exact hvv h'
      · exact hwv' h'.symm
    · exact hne he
  have hFc : F.card = 2 := by
    rw [hF, card_union_of_disjoint, card_edgePairs hvw, card_edgePairs hvw']
    rw [disjoint_left]
    intro e he he'
    simp only [edgePairs, mem_filter, mem_univ, true_and] at he he'
    have : v ∈ e.1 := by rw [he]; exact Sym2.mem_mk_left _ _
    rw [he'] at this
    rcases Sym2.mem_iff.1 this with h' | h'
    · exact hvv h'
    · exact hwv' h'.symm
  have hBc : 2 * n - 5 ≤ B.card := by
    have hdisj : Disjoint (starPairs v w) ((starPairs v' w').filter fun e => v ∉ e.1) := by
      rw [disjoint_left]
      intro e he he'
      simp only [starPairs, mem_filter, mem_univ, true_and] at he he'
      exact he'.2 he.1
    have hsub : (starPairs v' w').erase ⟨s(v', v), by simpa using hvv.symm⟩ ⊆
        (starPairs v' w').filter fun e => v ∉ e.1 := by
      intro e he
      obtain ⟨hne, he⟩ := mem_erase.1 he
      refine mem_filter.2 ⟨he, fun hv => hne (Subtype.ext ?_)⟩
      simp only [starPairs, mem_filter, mem_univ, true_and] at he
      obtain ⟨hv', -⟩ := he
      obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 hv'
      rw [hx] at hv
      refine hx.trans ?_
      rcases Sym2.mem_iff.1 hv with h' | h'
      · exact absurd h' hvv
      · subst h'
        rfl
    have h1 := card_le_card hsub
    have h2 := pred_card_le_card_erase (s := starPairs v' w') (a := ⟨s(v', v), by
      simpa using hvv.symm⟩)
    rw [hB, card_union_of_disjoint hdisj, card_starPairs hvw]
    rw [card_starPairs hvw'] at h2
    omega
  calc gnpProb n p (fun G => IsPendant G v w ∧ IsPendant G v' w')
      ≤ pProb (coin p n) (fun ω => (∀ e ∈ F, ω e = true) ∧ ∀ e ∈ B, ω e = false) := by
        refine pProb_mono (coin_isPMF hp0 hp1 n) fun ω hω => ?_
        have hω : IsPendant (graphOf ω) v w ∧ IsPendant (graphOf ω) v' w' := hω
        rw [isPendant_graphOf_iff hvw, isPendant_graphOf_iff hvw'] at hω
        refine ⟨fun e he => ?_, fun e he => ?_⟩
        · rcases mem_union.1 he with he | he
          · exact hω.1.1 e he
          · exact hω.2.1 e he
        · rcases mem_union.1 he with he | he
          · exact hω.1.2 e he
          · exact hω.2.2 e (mem_filter.1 he).1
    _ = p ^ 2 * (1 - p) ^ B.card := by rw [pProb_coin_present_absent hp0 hp1 _ _ hFB, hFc]
    _ ≤ p ^ 2 * (1 - p) ^ (2 * n - 5) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by linarith) (by linarith) hBc)
          (by positivity)

/-- The same edge seen from both ends: both endpoints have degree one. -/
theorem gnpProb_isPendant_pair_swap {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {v w : Fin n}
    (hvw : v ≠ w) :
    gnpProb n p (fun G => IsPendant G v w ∧ IsPendant G w v) ≤ p * (1 - p) ^ (2 * (n - 2)) := by
  classical
  set B := starPairs v w ∪ starPairs w v with hB
  have hdisj : Disjoint (starPairs v w) (starPairs w v) := by
    rw [disjoint_left]
    intro e he he'
    simp only [starPairs, mem_filter, mem_univ, true_and] at he he'
    obtain ⟨hv, hne⟩ := he
    obtain ⟨hw, -⟩ := he'
    obtain ⟨d, hd⟩ := e
    refine hne ?_
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hv
    rcases Sym2.mem_iff.1 hw with h' | h'
    · exact absurd h'.symm hvw
    · rw [h']
  have hFB : Disjoint (edgePairs v w) B := by
    rw [hB, disjoint_union_right]
    refine ⟨disjoint_edgePairs_starPairs v w, ?_⟩
    have := disjoint_edgePairs_starPairs w v
    rwa [show edgePairs w v = edgePairs v w by simp [edgePairs, Sym2.eq_swap]] at this
  calc gnpProb n p (fun G => IsPendant G v w ∧ IsPendant G w v)
      ≤ pProb (coin p n) (fun ω => (∀ e ∈ edgePairs v w, ω e = true) ∧ ∀ e ∈ B, ω e = false) := by
        refine pProb_mono (coin_isPMF hp0 hp1 n) fun ω hω => ?_
        have hω : IsPendant (graphOf ω) v w ∧ IsPendant (graphOf ω) w v := hω
        rw [isPendant_graphOf_iff hvw, isPendant_graphOf_iff hvw.symm] at hω
        refine ⟨hω.1.1, fun e he => ?_⟩
        rcases mem_union.1 he with he | he
        · exact hω.1.2 e he
        · exact hω.2.2 e he
    _ = p * (1 - p) ^ (2 * (n - 2)) := by
        rw [pProb_coin_present_absent hp0 hp1 _ _ hFB, card_edgePairs hvw, pow_one, hB,
          card_union_of_disjoint hdisj, card_starPairs hvw, card_starPairs hvw.symm, two_mul]

/-- Two pendant pairs that cannot hold together. -/
theorem not_isPendant_pair {G : SimpleGraph (Fin n)} {v w v' w' : Fin n}
    (h : (v = v' ∧ w ≠ w') ∨ (v ≠ v' ∧ w = v' ∧ w' ≠ v) ∨ (v ≠ v' ∧ w' = v ∧ w ≠ v')) :
    ¬ (IsPendant G v w ∧ IsPendant G v' w') := by
  rintro ⟨⟨hvw, hw⟩, ⟨hvw', hw'⟩⟩
  rcases h with ⟨rfl, hne⟩ | ⟨-, rfl, hne⟩ | ⟨-, rfl, hne⟩
  · exact hne (hw _ hvw').symm
  · exact hne (hw' _ hvw.symm).symm
  · exact hne (hw _ hvw'.symm).symm

/-- Off-diagonal pairs of `Fin n`. -/
theorem card_offDiag_univ : ((univ : Finset (Fin n × Fin n)).filter fun a => a.1 ≠ a.2).card =
    n * (n - 1) := by
  have : ((univ : Finset (Fin n × Fin n)).filter fun a => a.1 ≠ a.2) =
      (univ : Finset (Fin n)).offDiag := by
    ext a
    simp [mem_offDiag]
  rw [this, offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub_one]

/-- **Second moment bound.** For `n ≥ 3` and `0 < p < 1`,
`P(G(n, p) Hamiltonian) ≤ 1 / μ + (1 / (1 - p) - 1) + 1 / (n (n - 1) p)` with
`μ = n (n - 1) p (1 - p)^{n - 2}` the expected number of pendant pairs. -/
theorem gnpProb_isHamiltonian_le (hn : 3 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    gnpProb n p (fun G => G.IsHamiltonian) ≤
      1 / (n * (n - 1) * p * (1 - p) ^ (n - 2)) + (1 / (1 - p) - 1) + 1 / (n * (n - 1) * p) := by
  classical
  have hP := coin_isPMF hp0.le hp1.le n
  have h1p : 0 < 1 - p := by linarith
  have hn1 : (1 : ℝ) ≤ n - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set N : ℝ := n * (n - 1) with hN
  have hNpos : 0 < N := by rw [hN]; nlinarith
  set a₁ : ℝ := p * (1 - p) ^ (n - 2) with ha₁
  set μ : ℝ := N * a₁ with hμ
  have hμpos : 0 < μ := mul_pos hNpos (mul_pos hp0 (pow_pos h1p _))
  set gen : ℝ := p ^ 2 * (1 - p) ^ (2 * n - 5) with hgen
  set sw : ℝ := p * (1 - p) ^ (2 * (n - 2)) with hsw
  have hgen0 : 0 ≤ gen := by positivity
  have hsw0 : 0 ≤ sw := by positivity
  set I : Fin n × Fin n → (Pairs n → Bool) → ℝ :=
    fun a ω => if a.1 ≠ a.2 ∧ IsPendant (graphOf ω) a.1 a.2 then 1 else 0 with hI
  set Z : (Pairs n → Bool) → ℝ := fun ω => ∑ a, I a ω with hZ
  have hEI : ∀ a : Fin n × Fin n, pE (coin p n) (I a) = if a.1 ≠ a.2 then a₁ else 0 := by
    intro a
    by_cases h : a.1 ≠ a.2
    · rw [if_pos h, ha₁, ← gnpProb_isPendant hp0.le hp1.le h]
      unfold gnpProb
      exact (pProb_eq_pE _ _ (fun ω hω => by simp [hI, h, hω])
        (fun ω hω => by simp [hI, h, hω])).symm
    · rw [if_neg h]
      have : I a = fun _ => 0 := by funext ω; simp [hI, h]
      rw [this, pE_const hP]
  have hsum_off : ∀ c : ℝ, ∑ a : Fin n × Fin n, (if a.1 ≠ a.2 then c else 0) = N * c := by
    intro c
    rw [← sum_filter, sum_const, card_offDiag_univ, nsmul_eq_mul, hN]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hEZ : pE (coin p n) Z = μ := by
    rw [hZ, pE_sum]
    simp_rw [hEI]
    rw [hsum_off]
  have hII : ∀ a b ω, I a ω * I b ω =
      if (a.1 ≠ a.2 ∧ IsPendant (graphOf ω) a.1 a.2) ∧ (b.1 ≠ b.2 ∧ IsPendant (graphOf ω) b.1 b.2)
      then 1 else 0 := by
    intro a b ω
    simp only [hI]
    split_ifs <;> simp_all
  -- pairwise bound
  have hEII : ∀ a b : Fin n × Fin n, pE (coin p n) (fun ω => I a ω * I b ω) ≤
      (if a = b then (if a.1 ≠ a.2 then a₁ else 0) else 0) +
        (if a.1 ≠ a.2 ∧ b.1 ≠ b.2 then gen else 0) +
        (if a.1 ≠ a.2 ∧ b = (a.2, a.1) then sw else 0) := by
    intro a b
    have hpe : pE (coin p n) (fun ω => I a ω * I b ω) =
        pProb (coin p n) (fun ω => (a.1 ≠ a.2 ∧ IsPendant (graphOf ω) a.1 a.2) ∧
          (b.1 ≠ b.2 ∧ IsPendant (graphOf ω) b.1 b.2)) :=
      (pProb_eq_pE _ _ (fun ω h => by rw [hII]; simp [h]) (fun ω h => by rw [hII]; simp [h])).symm
    have hnn : 0 ≤ (if a = b then (if a.1 ≠ a.2 then a₁ else 0) else 0) := by
      split_ifs <;> positivity
    have hnn2 : 0 ≤ (if a.1 ≠ a.2 ∧ b.1 ≠ b.2 then gen else 0) := by split_ifs <;> positivity
    have hnn3 : 0 ≤ (if a.1 ≠ a.2 ∧ b = (a.2, a.1) then sw else 0) := by
      split_ifs <;> positivity
    rw [hpe]
    obtain ⟨v, w⟩ := a
    obtain ⟨v', w'⟩ := b
    simp only at *
    by_cases hvw : v = w
    · rw [pProb_congr (T := fun _ => False) (fun ω => ⟨fun h => h.1.1 hvw, False.elim⟩),
        pProb_false]
      linarith
    by_cases hvw' : v' = w'
    · rw [pProb_congr (T := fun _ => False) (fun ω => ⟨fun h => h.2.1 hvw', False.elim⟩),
        pProb_false]
      linarith
    by_cases hab : (v, w) = (v', w')
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hab
      rw [if_pos rfl, if_pos hvw]
      have : pProb (coin p n) (fun ω => (v ≠ w ∧ IsPendant (graphOf ω) v w) ∧
          (v ≠ w ∧ IsPendant (graphOf ω) v w)) = a₁ := by
        rw [pProb_congr (T := fun ω => IsPendant (graphOf ω) v w) (fun ω => by tauto), ha₁]
        exact gnpProb_isPendant hp0.le hp1.le hvw
      linarith
    rw [if_neg hab]
    by_cases hswap : v' = w ∧ w' = v
    · obtain ⟨h1, h2⟩ := hswap
      rw [if_pos (show v ≠ w ∧ (v', w') = (w, v) from ⟨hvw, Prod.ext h1 h2⟩)]
      have : pProb (coin p n) (fun ω => (v ≠ w ∧ IsPendant (graphOf ω) v w) ∧
          (v' ≠ w' ∧ IsPendant (graphOf ω) v' w')) ≤ sw := by
        rw [pProb_congr (T := fun ω => IsPendant (graphOf ω) v w ∧ IsPendant (graphOf ω) w v)
          (fun ω => by rw [h1, h2]; tauto)]
        exact gnpProb_isPendant_pair_swap hp0.le hp1.le hvw
      linarith
    have hbad : (v = v' ∧ w ≠ w') ∨ (v ≠ v' ∧ w = v' ∧ w' ≠ v) ∨ (v ≠ v' ∧ w' = v ∧ w ≠ v') ∨
        (v ≠ v' ∧ w ≠ v' ∧ w' ≠ v) := by
      by_cases h1 : v = v'
      · subst h1
        exact Or.inl ⟨rfl, fun h => hab (by rw [h])⟩
      · by_cases h2 : w = v'
        · exact Or.inr (Or.inl ⟨h1, h2, fun h => hswap ⟨h2.symm, h⟩⟩)
        · by_cases h3 : w' = v
          · exact Or.inr (Or.inr (Or.inl ⟨h1, h3, h2⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
    rcases hbad with h | h | h | ⟨h1, h2, h3⟩
    · rw [pProb_congr (T := fun _ => False) (fun ω => ⟨fun hω =>
        not_isPendant_pair (Or.inl h) ⟨hω.1.2, hω.2.2⟩, False.elim⟩), pProb_false]
      linarith
    · rw [pProb_congr (T := fun _ => False) (fun ω => ⟨fun hω =>
        not_isPendant_pair (Or.inr (Or.inl h)) ⟨hω.1.2, hω.2.2⟩, False.elim⟩), pProb_false]
      linarith
    · rw [pProb_congr (T := fun _ => False) (fun ω => ⟨fun hω =>
        not_isPendant_pair (Or.inr (Or.inr h)) ⟨hω.1.2, hω.2.2⟩, False.elim⟩), pProb_false]
      linarith
    · rw [if_pos ⟨hvw, hvw'⟩]
      have : pProb (coin p n) (fun ω => (v ≠ w ∧ IsPendant (graphOf ω) v w) ∧
          (v' ≠ w' ∧ IsPendant (graphOf ω) v' w')) ≤ gen := by
        rw [pProb_congr (T := fun ω => IsPendant (graphOf ω) v w ∧ IsPendant (graphOf ω) v' w')
          (fun ω => by tauto)]
        exact gnpProb_isPendant_pair_generic hp0.le hp1.le hn hvw hvw' h1 h2 h3
      linarith
  -- second moment
  have hEZ2 : pE (coin p n) (fun ω => Z ω ^ 2) ≤ μ + N ^ 2 * gen + N * sw := by
    have hsq : (fun ω => Z ω ^ 2) = fun ω => ∑ a, ∑ b, I a ω * I b ω := by
      funext ω; rw [hZ, sq, Finset.sum_mul_sum]
    rw [hsq, pE_sum]
    simp_rw [pE_sum]
    refine (sum_le_sum fun a _ => sum_le_sum fun b _ => hEII a b).trans (le_of_eq ?_)
    simp only [sum_add_distrib]
    have e1 : ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
        (if a = b then (if a.1 ≠ a.2 then a₁ else 0) else 0) = μ := by
      simp_rw [sum_ite_eq, mem_univ, if_true]
      rw [hsum_off, hμ]
    have e2 : ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
        (if a.1 ≠ a.2 ∧ b.1 ≠ b.2 then gen else 0) = N ^ 2 * gen := by
      calc ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
            (if a.1 ≠ a.2 ∧ b.1 ≠ b.2 then gen else 0)
          = ∑ a : Fin n × Fin n, (if a.1 ≠ a.2 then N * gen else 0) := by
            refine sum_congr rfl fun a _ => ?_
            by_cases ha : a.1 ≠ a.2
            · rw [if_pos ha, ← hsum_off]
              exact sum_congr rfl fun b _ => by simp [ha]
            · rw [if_neg ha]
              exact sum_eq_zero fun b _ => by simp [ha]
        _ = N ^ 2 * gen := by rw [hsum_off]; ring
    have e3 : ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
        (if a.1 ≠ a.2 ∧ b = (a.2, a.1) then sw else 0) = N * sw := by
      calc ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
            (if a.1 ≠ a.2 ∧ b = (a.2, a.1) then sw else 0)
          = ∑ a : Fin n × Fin n, (if a.1 ≠ a.2 then sw else 0) := by
            refine sum_congr rfl fun a _ => ?_
            by_cases ha : a.1 ≠ a.2
            · rw [if_pos ha]
              simp [ha]
            · rw [if_neg ha]
              exact sum_eq_zero fun b _ => by simp [ha]
        _ = N * sw := hsum_off sw
    rw [e1, e2, e3]
  have hVar : pE (coin p n) (fun ω => (Z ω - μ) ^ 2) =
      pE (coin p n) (fun ω => Z ω ^ 2) - μ ^ 2 := by
    have : (fun ω => (Z ω - μ) ^ 2) = fun ω => (Z ω ^ 2 + (-2 * μ) * Z ω) + μ ^ 2 := by
      funext ω; ring
    rw [this, pE_add, pE_add, pE_const_mul, pE_const hP, hEZ]
    ring
  have hham : ∀ ω, (graphOf ω).IsHamiltonian → μ ^ 2 ≤ (Z ω - μ) ^ 2 := by
    intro ω hω
    have : Z ω = 0 := by
      rw [hZ]
      refine sum_eq_zero fun a _ => ?_
      simp only [hI]
      rw [if_neg]
      exact fun h => not_isPendant_of_isHamiltonian hn hω a.1 a.2 h.2
    rw [this]; nlinarith
  have hmarkov := pProb_ge_le_markov hP (f := fun ω => (Z ω - μ) ^ 2) (fun ω => sq_nonneg _)
    (pow_pos hμpos 2)
  -- the algebra
  have hpow : (1 - p) ^ (2 * (n - 2)) = (1 - p) ^ (2 * n - 5) * (1 - p) := by
    rw [← pow_succ]; congr 1; omega
  have hμ2 : μ ^ 2 = N ^ 2 * p ^ 2 * (1 - p) ^ (2 * (n - 2)) := by
    rw [hμ, ha₁]
    ring
  have hgenμ : N ^ 2 * gen = μ ^ 2 / (1 - p) := by
    rw [hμ2, hpow, hgen]
    field_simp
  have hswμ : N * sw = μ ^ 2 / (N * p) := by
    rw [hμ2, hsw]
    field_simp
  calc gnpProb n p (fun G => G.IsHamiltonian)
      ≤ pProb (coin p n) (fun ω => μ ^ 2 ≤ (Z ω - μ) ^ 2) :=
        pProb_mono hP fun ω h => hham ω h
    _ ≤ pE (coin p n) (fun ω => (Z ω - μ) ^ 2) / μ ^ 2 := hmarkov
    _ ≤ (μ + μ ^ 2 / (1 - p) + μ ^ 2 / (N * p) - μ ^ 2) / μ ^ 2 := by
        rw [hVar, ← hgenμ, ← hswμ]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / μ + (1 / (1 - p) - 1) + 1 / (N * p) := by
        field_simp
        ring
    _ = 1 / (n * (n - 1) * p * (1 - p) ^ (n - 2)) + (1 / (1 - p) - 1) +
          1 / (n * (n - 1) * p) := by
        rw [hμ, ha₁, hN]
        ring_nf

/-- Hamiltonicity is a monotone property. -/
theorem gnpProb_isHamiltonian_mono {p q : ℝ} (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    gnpProb n p (fun G => G.IsHamiltonian) ≤ gnpProb n q (fun G => G.IsHamiltonian) :=
  gnpProb_mono (fun _ _ hGH hG => hG.mono hGH) hp0 hpq hq1

/-- **Komlós–Szemerédi (1983), lower side.** If `ω(n) → ∞`, then
`G(n, (log n + log log n - ω(n)) / n)` (edge probability clipped below at `0`) is Hamiltonian
with probability tending to `0`. -/
theorem not_isHamiltonian_of_log_add_loglog_sub (ω : ℕ → ℝ) (hω : Tendsto ω atTop atTop) :
    Tendsto (fun n : ℕ => gnpProb n (max 0 ((Real.log n + Real.log (Real.log n) - ω n) / n))
      (fun G => G.IsHamiltonian)) atTop (nhds 0) := by
  set L : ℕ → ℝ := fun n => Real.log n with hLdef
  set LL : ℕ → ℝ := fun n => Real.log (Real.log n) with hLLdef
  have hlogn : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto LL atTop atTop := Real.tendsto_log_atTop.comp hlogn
  -- a slower `ω'` and the comparison probability `q`
  set ω' : ℕ → ℝ := fun n => min (ω n) (LL n / 2) with hω'def
  have hω' : Tendsto ω' atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hω.eventually_ge_atTop b, (hloglog.atTop_div_const (by norm_num :
      (0 : ℝ) < 2)).eventually_ge_atTop b] with n h1 h2
    exact le_min h1 h2
  set q : ℕ → ℝ := fun n => (L n + LL n - ω' n) / n with hqdef
  have hL1 : Tendsto (fun n : ℕ => Real.log n / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hL2 : Tendsto (fun n : ℕ => Real.log n ^ 2 / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  -- basic eventual facts: `log n ≥ 1`, `0 ≤ log log n ≤ log n`, `ω' ≤ log log n / 2`
  have hbase : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ 1 ≤ L n ∧ 0 ≤ LL n ∧ LL n ≤ L n ∧
      ω' n ≤ LL n / 2 ∧ 0 ≤ ω' n := by
    filter_upwards [eventually_ge_atTop 3, hlogn.eventually_ge_atTop 1,
      hω'.eventually_ge_atTop 0] with n hn h1 h3
    refine ⟨hn, h1, Real.log_nonneg h1, ?_, min_le_right _ _, h3⟩
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  -- `log n / n ≤ q n ≤ 2 log n / n`
  have hq_bounds : ∀ᶠ n : ℕ in atTop, L n / n ≤ q n ∧ q n ≤ 2 * (L n / n) := by
    filter_upwards [hbase] with n hb
    obtain ⟨hn, h1, h2, h3, h4, h5⟩ := hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    refine ⟨div_le_div_of_nonneg_right (by linarith) hnpos.le, ?_⟩
    rw [hqdef, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hnpos.le
  have hq0 : Tendsto q atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hL1.const_mul 2) ?_ ?_
    · filter_upwards [hq_bounds, hbase] with n h hb
      exact le_trans (div_nonneg (by linarith [hb.2.1]) (Nat.cast_nonneg _)) h.1
    · filter_upwards [hq_bounds] with n h using h.2
  have hqpos : ∀ᶠ n : ℕ in atTop, 0 < q n := by
    filter_upwards [hq_bounds, hbase] with n h hb
    obtain ⟨hn, h1, -⟩ := hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact lt_of_lt_of_le (div_pos (by linarith) hnpos) h.1
  have hqhalf : ∀ᶠ n : ℕ in atTop, q n ≤ 1 / 2 := hq0.eventually (ge_mem_nhds (by norm_num))
  -- comparison: the clipped probability is at most `q n`
  have hcomp : ∀ᶠ n : ℕ in atTop,
      gnpProb n (max 0 ((Real.log n + Real.log (Real.log n) - ω n) / n))
        (fun G => G.IsHamiltonian) ≤ gnpProb n (q n) (fun G => G.IsHamiltonian) := by
    filter_upwards [hqpos, hqhalf, hbase] with n hq hq2 hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by have := hb.1; omega : 0 < n)
    refine gnpProb_isHamiltonian_mono (le_max_left _ _) (max_le hq.le ?_) (by linarith)
    refine div_le_div_of_nonneg_right ?_ hnpos.le
    have : ω' n ≤ ω n := min_le_left _ _
    simp only [hLdef, hLLdef] at this ⊢
    linarith
  -- the second moment bound at `q n` tends to `0`
  set N : ℕ → ℝ := fun n => (n : ℝ) * (n - 1) with hNdef
  set μ : ℕ → ℝ := fun n => N n * q n * (1 - q n) ^ (n - 2) with hμdef
  have hNq : Tendsto (fun n => N n * q n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (hlogn.atTop_mul_atTop₀
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))))
    filter_upwards [hq_bounds, hbase] with n h hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by have := hb.1; omega : 0 < n)
    have hn1 : (0 : ℝ) ≤ n - 1 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hb.1
      linarith
    calc L n * ((n : ℝ) + -1) = N n * (L n / n) := by
          simp only [hNdef]; field_simp; ring
      _ ≤ N n * q n := mul_le_mul_of_nonneg_left h.1 (mul_nonneg hnpos.le hn1)
  -- lower bound on the mean
  set E : ℕ → ℝ := fun n => ω' n - 8 * (L n ^ 2 / n) with hEdef
  have hE : Tendsto E atTop atTop := by
    have h2 : Tendsto (fun n : ℕ => 8 * (L n ^ 2 / n)) atTop (nhds 0) := by
      simpa using hL2.const_mul 8
    exact hω'.atTop_add (by simpa using h2.neg) |>.congr fun n => by
      simp [hEdef, sub_eq_add_neg]
  have hμ : Tendsto μ atTop atTop := by
    have hhalf : Tendsto (fun n => (1 / 2 : ℝ) * Real.exp (E n)) atTop atTop :=
      (Real.tendsto_exp_atTop.comp hE).const_mul_atTop (by norm_num)
    refine tendsto_atTop_mono' atTop ?_ hhalf
    filter_upwards [hq_bounds, hqpos, hqhalf, hbase] with n h hq hq2 hb
    obtain ⟨hn, hL1n, hLL0, hLLL, hω'1, hω'0⟩ := hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hmean := exp_le_isolated_mean (by omega : 1 ≤ n) hq.le hq2
    have hpow : (1 - q n) ^ (n - 1) ≤ (1 - q n) ^ (n - 2) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    -- `exp (log n - n q - 2 n q²) = exp (ω' - 2 n q²) / log n`
    have hnq : (n : ℝ) * q n = L n + LL n - ω' n := by
      simp only [hqdef]; field_simp
    have hLpos : 0 < L n := by linarith
    have hexpLL : Real.exp (LL n) = L n := by
      simp only [hLLdef, hLdef]; exact Real.exp_log hLpos
    have hkey : Real.exp (Real.log n - n * q n - 2 * n * q n ^ 2) =
        Real.exp (ω' n - 2 * n * q n ^ 2) / L n := by
      rw [show Real.log n - n * q n - 2 * n * q n ^ 2 = (ω' n - 2 * n * q n ^ 2) - LL n by
        rw [hnq]; simp only [hLdef]; ring, Real.exp_sub, hexpLL]
    have hsq : 2 * n * q n ^ 2 ≤ 8 * (L n ^ 2 / n) := by
      have : q n ^ 2 ≤ (2 * (L n / n)) ^ 2 := pow_le_pow_left₀ hq.le h.2 2
      rw [show 8 * (L n ^ 2 / n) = 2 * n * (2 * (L n / n)) ^ 2 by field_simp; ring]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hexpE : Real.exp (E n) ≤ Real.exp (ω' n - 2 * n * q n ^ 2) :=
      Real.exp_le_exp.2 (by simp only [hEdef]; linarith)
    -- assemble
    have h1 : Real.exp (E n) / L n ≤ n * (1 - q n) ^ (n - 2) := by
      calc Real.exp (E n) / L n ≤ Real.exp (ω' n - 2 * n * q n ^ 2) / L n :=
            div_le_div_of_nonneg_right hexpE hLpos.le
        _ = Real.exp (Real.log n - n * q n - 2 * n * q n ^ 2) := hkey.symm
        _ ≤ n * (1 - q n) ^ (n - 1) := hmean
        _ ≤ n * (1 - q n) ^ (n - 2) := mul_le_mul_of_nonneg_left hpow hnpos.le
    have h2 : (n - 1 : ℝ) * q n * (Real.exp (E n) / L n) ≤ μ n := by
      calc (n - 1 : ℝ) * q n * (Real.exp (E n) / L n)
          ≤ (n - 1 : ℝ) * q n * (n * (1 - q n) ^ (n - 2)) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith) hq.le)
        _ = μ n := by simp only [hμdef, hNdef]; ring
    have h3 : (1 / 2 : ℝ) * Real.exp (E n) ≤ (n - 1 : ℝ) * q n * (Real.exp (E n) / L n) := by
      have hqL : L n / n ≤ q n := h.1
      have hexp0 : 0 < Real.exp (E n) := Real.exp_pos _
      have : (1 / 2 : ℝ) ≤ (n - 1 : ℝ) * (L n / n) / L n := by
        rw [show (n - 1 : ℝ) * (L n / n) / L n = (n - 1) / n by field_simp]
        rw [le_div_iff₀ hnpos]
        linarith
      calc (1 / 2 : ℝ) * Real.exp (E n) ≤ (n - 1 : ℝ) * (L n / n) / L n * Real.exp (E n) :=
            mul_le_mul_of_nonneg_right this hexp0.le
        _ ≤ (n - 1 : ℝ) * q n / L n * Real.exp (E n) := by
            refine mul_le_mul_of_nonneg_right ?_ hexp0.le
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hqL (by linarith)) hLpos.le
        _ = (n - 1 : ℝ) * q n * (Real.exp (E n) / L n) := by ring
    exact h3.trans h2
  have hbound : Tendsto (fun n => 1 / (n * (n - 1) * q n * (1 - q n) ^ (n - 2)) +
      (1 / (1 - q n) - 1) + 1 / (n * (n - 1) * q n)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => 1 / μ n) atTop (nhds 0) := by
      simpa [Pi.inv_def] using hμ.inv_tendsto_atTop
    have h2 : Tendsto (fun n => 1 / (1 - q n) - 1) atTop (nhds 0) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hq0
      have h' := (tendsto_const_nhds (x := (1 : ℝ))).div h (by norm_num)
      simpa using h'.sub_const 1
    have h3 : Tendsto (fun n => 1 / (N n * q n)) atTop (nhds 0) := by
      simpa [Pi.inv_def] using hNq.inv_tendsto_atTop
    have := (h1.add h2).add h3
    simpa [hμdef, hNdef, mul_assoc] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · filter_upwards [hqpos, hqhalf, hbase] with n hq hq2 hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by have := hb.1; omega : 0 < n)
    have hle : max 0 ((Real.log n + Real.log (Real.log n) - ω n) / n) ≤ q n := by
      refine max_le hq.le (div_le_div_of_nonneg_right ?_ hnpos.le)
      have : ω' n ≤ ω n := min_le_left _ _
      simp only [hLdef, hLLdef] at this ⊢
      linarith
    exact pProb_nonneg (coin_isPMF (le_max_left _ _) (by linarith) n) _
  · filter_upwards [hcomp, hqpos, hqhalf, hbase] with n hc hq hq2 hb
    exact hc.trans (gnpProb_isHamiltonian_le hb.1 hq (by linarith))

end RandomGraphLib
