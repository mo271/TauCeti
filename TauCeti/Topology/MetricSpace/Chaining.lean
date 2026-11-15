/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Topology.MetricSpace.CoveringNumbers
import TauCeti.Topology.MetricSpace.Holder

/-!
# Sparse star-bridge covers and multiscale Hölder chaining

To deduce Hölder continuity on a metric parameter set `S` of covering dimension `d` from
increment bounds along a countable family of edges, naive all-pairs neighbor graphs at scale
`r ^ n` have `O(r ^ (-2 d n))` edges, losing a factor of two in the dimension threshold, while
tree-only parent pointers miss nearby points separated by net cell boundaries.

We resolve both issues in two steps:

1. **Sparse star-bridge covers (`TauCeti.exists_finset_edist_le_card_le_rpow`).**
   For any finite subset `F` of a pseudo-emetric space, threshold `δ`, and shell count `K ≥ 1`,
   concentric ball-doubling selects `O(|F| ^ (1 + 1 / K))` directed edges of length at most
   `2 K δ` such that every pair of points in `F` within distance `2 δ` shares a common star
   center in `F`. Taking `K` large makes the cardinality exponent arbitrarily close to `1`.

2. **Multiscale deterministic chaining
   (`TauCeti.exists_edges_and_holderOnWith_of_coveringNumber_le`).**
   When `S` has finite diameter at most `D` and internal covering numbers bounded by
   `C ε ^ (-d)` for `0 < ε ≤ 1`, combining cumulative minimal covers at scales `r ^ n` with
   parent edges, sparse star-bridge edges, and a level-zero global star produces a countable
   dense-in-`S` subset `U ⊆ S` and edge families of size `O((r ^ (-d')) ^ n)` (for any `d' > d`)
   and length `O(r ^ n)`. Any map into a pseudo-emetric space satisfying a `γ`-Hölder bound along
   these edges is `γ`-Hölder on `U`.

## References

* B. Awerbuch, D. Peleg, *Sparse partitions*, 31st IEEE Symposium on Foundations of Computer
  Science, 1990, 503–513 (concentric neighborhood clustering).
* V. Krätschmer, M. Urusov, *A general Kolmogorov–Chentsov type theorem on general metric spaces*,
  arXiv:2107.13837v2, Theorem 1.1.
-/

public section

open Filter Metric Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section StarBridge

/-- By pigeonhole over `K` concentric shells around `z ∈ U ⊆ F`, some shell grows by a factor of at
most `|F| ^ (1 / K)`. -/
private lemma exists_shell_card_le {T : Type*} {F U : Finset T} {z : T} (hUF : U ⊆ F)
    (hzU : z ∈ U) {K : ℕ} (hK : 0 < K) (B : ℕ → Finset T)
    (hzB0 : z ∈ B 0) (hB_sub : ∀ j, B j ⊆ U) :
    ∃ j < K, ((B (j + 1)).card : ℝ≥0) ≤ (F.card : ℝ≥0) ^ (K : ℝ)⁻¹ * ((B j).card : ℝ≥0) := by
  set α : ℝ≥0 := (F.card : ℝ≥0) ^ (K : ℝ)⁻¹
  have hF_pos : (0 : ℝ≥0) < F.card := by exact_mod_cast Finset.card_pos.2 ⟨z, hUF hzU⟩
  have hα_pos : 0 < α := NNReal.rpow_pos hF_pos
  by_contra! hgt
  have hpow : ∀ m, 0 < m → m ≤ K → α ^ m * ((B 0).card : ℝ≥0) < ((B m).card : ℝ≥0) := by
    intro m hm hmK
    induction m with
    | zero => omega
    | succ m ihm =>
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · simpa using hgt 0 hK
      · exact ((mul_lt_mul_of_pos_left (ihm hm' (by omega)) hα_pos).trans_eq'
          (by rw [pow_succ', mul_assoc])).trans (hgt m hmK)
  have hαK : α ^ K = (F.card : ℝ≥0) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), NNReal.rpow_one]
  have hB0 : (1 : ℝ≥0) ≤ (B 0).card := by exact_mod_cast Finset.card_pos.2 ⟨z, hzB0⟩
  have hBK : ((B K).card : ℝ≥0) ≤ F.card := by
    exact_mod_cast Finset.card_le_card ((hB_sub K).trans hUF)
  exact ((mul_one (F.card : ℝ≥0)).symm.trans_le
    (hαK ▸ mul_le_mul_of_nonneg_left hB0 zero_le) |>.trans_lt (hpow K hK le_rfl) |>.trans_le
    hBK).false

variable {T : Type*} [PseudoEMetricSpace T]

/-- Auxiliary induction on subsets `U ⊆ F` for `exists_finset_edist_le_card_le_rpow`. -/
private lemma exists_star_bridge_subset (F : Finset T) (δ : ℝ≥0∞) {K : ℕ} (hK : 0 < K) :
    ∀ n : ℕ, ∀ U : Finset T, U.card = n → U ⊆ F →
      ∃ E : Finset (T × T),
        (E : Set (T × T)) ⊆ (U : Set T) ×ˢ (U : Set T) ∧
        (∀ p ∈ E, edist p.1 p.2 ≤ (2 * K : ℕ) * δ) ∧
        (E.card : ℝ≥0) ≤ (F.card : ℝ≥0) ^ (K : ℝ)⁻¹ * (U.card : ℝ≥0) ∧
        ∀ u ∈ U, ∀ v ∈ U, edist u v ≤ 2 * δ → ∃ z ∈ U, (u, z) ∈ E ∧ (v, z) ∈ E := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U hcard hUF
    rcases U.eq_empty_or_nonempty with rfl | ⟨z, hzU⟩
    · exact ⟨∅, by simp, by simp, by simp, by simp⟩
    set α : ℝ≥0 := (F.card : ℝ≥0) ^ (K : ℝ)⁻¹
    let B : ℕ → Finset T := fun j ↦ U.filter fun w ↦ edist w z ≤ (2 * j : ℕ) * δ
    have hzB0 : z ∈ B 0 := by simp [B, hzU]
    have hB_sub : ∀ j, B j ⊆ U := fun j ↦ Finset.filter_subset _ U
    have hB_mono : Monotone B := fun i j hij w hw ↦ by
      simp only [B, Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, hw.2.trans (by gcongr)⟩
    have hB_step : ∀ {j u v}, u ∈ B j → v ∈ U → edist u v ≤ 2 * δ → v ∈ B (j + 1) := by
      intro j u v hu hv huv
      simp only [B, Finset.mem_filter] at hu ⊢
      refine ⟨hv, (edist_triangle v u z).trans ?_⟩
      rw [edist_comm v u]
      exact (add_le_add huv hu.2).trans_eq (by push_cast; ring)
    obtain ⟨j, hjK, hj_card⟩ := exists_shell_card_le hUF hzU hK B hzB0 hB_sub
    let U' : Finset T := U \ B j
    have hU'_lt : U'.card < n := hcard ▸
      Finset.card_lt_card (Finset.sdiff_ssubset (hB_sub j) ⟨z, hB_mono (Nat.zero_le j) hzB0⟩)
    obtain ⟨E', hE'_sub, hE'_len, hE'_card, hE'_bridge⟩ :=
      ih U'.card hU'_lt U' rfl (Finset.sdiff_subset.trans hUF)
    let Sz : Finset (T × T) := (B (j + 1)).image fun w ↦ (w, z)
    refine ⟨Sz ∪ E', fun p hp ↦ ?_, fun p hp ↦ ?_, ?_, fun u hu v hv huv ↦ ?_⟩
    · rcases Finset.mem_union.1 (Finset.mem_coe.1 hp) with hpS | hpE'
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hpS
        exact ⟨hB_sub (j + 1) hw, hzU⟩
      · exact Set.prod_mono Finset.sdiff_subset Finset.sdiff_subset (hE'_sub hpE')
    · rcases Finset.mem_union.1 hp with hpS | hpE'
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hpS
        have hjK' : 2 * (j + 1) ≤ 2 * K := by omega
        exact (Finset.mem_filter.1 hw).2.trans
          (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hjK') zero_le)
      · exact hE'_len p hpE'
    · have hSz : (Sz.card : ℝ≥0) ≤ (B (j + 1)).card := Nat.cast_le.2 Finset.card_image_le
      have hpart := Finset.card_sdiff_add_card_eq_card (hB_sub j)
      have hunion : ((Sz ∪ E').card : ℝ≥0) ≤ Sz.card + E'.card := by
        exact_mod_cast Finset.card_union_le Sz E'
      refine hunion.trans ((add_le_add (hSz.trans hj_card) hE'_card).trans_eq ?_)
      rw [← hpart]; push_cast; ring
    · by_cases huj : u ∈ B j
      · exact ⟨z, hzU, Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (hB_mono (Nat.le_succ j) huj)),
          Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hB_step huj hv huv))⟩
      · by_cases hvj : v ∈ B j
        · exact ⟨z, hzU, Finset.mem_union_left _ (Finset.mem_image_of_mem _
            (hB_step hvj hu (edist_comm u v ▸ huv))),
            Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hB_mono (Nat.le_succ j) hvj))⟩
        · obtain ⟨z', hz', huz', hvz'⟩ :=
            hE'_bridge u (Finset.mem_sdiff.2 ⟨hu, huj⟩) v (Finset.mem_sdiff.2 ⟨hv, hvj⟩) huv
          exact ⟨z', Finset.sdiff_subset hz', Finset.mem_union_right _ huz',
            Finset.mem_union_right _ hvz'⟩

/-- **Sparse star-bridge cover.** Every finite set `F` in a pseudo-emetric space admits at most
`|F| ^ (1 + 1 / K)` directed edges of length at most `2 K δ` in `F × F` such that any two points
of `F` within distance `2 δ` connect to a common center in `F`. -/
theorem exists_finset_edist_le_card_le_rpow (F : Finset T) (δ : ℝ≥0∞) {K : ℕ} (hK : 0 < K) :
    ∃ E : Finset (T × T),
      (E : Set (T × T)) ⊆ (F : Set T) ×ˢ (F : Set T) ∧
      (∀ p ∈ E, edist p.1 p.2 ≤ (2 * K : ℕ) * δ) ∧
      (E.card : ℝ≥0) ≤ (F.card : ℝ≥0) ^ (1 + (K : ℝ)⁻¹) ∧
      ∀ u ∈ F, ∀ v ∈ F, edist u v ≤ 2 * δ → ∃ z ∈ F, (u, z) ∈ E ∧ (v, z) ∈ E := by
  obtain ⟨E, hsub, hlen, hcard, hbridge⟩ := exists_star_bridge_subset F δ hK F.card F rfl subset_rfl
  refine ⟨E, hsub, hlen, hcard.trans ?_, hbridge⟩
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [NNReal.zero_rpow (by positivity : (1 : ℝ) + (K : ℝ)⁻¹ ≠ 0)]
  · have hF_pos : (0 : ℝ≥0) < F.card := by exact_mod_cast Finset.card_pos.2 hF
    rw [add_comm, NNReal.rpow_add hF_pos.ne', NNReal.rpow_one]

end StarBridge

section MultiscaleChaining

variable {T E : Type*}

/-- Recursive ancestor descent along scale pointers `parent n` from level `N` down to `m`. -/
private def descend (parent : ℕ → T → T) : ℕ → ℕ → T → T
  | 0, _, x => x
  | N + 1, m, x => if m = N + 1 then x else descend parent N m (parent N x)

private lemma descend_self (parent : ℕ → T → T) (N : ℕ) (x : T) : descend parent N N x = x := by
  cases N <;> simp [descend]

private lemma descend_succ_of_le (parent : ℕ → T → T) {N m : ℕ} (hm : m ≤ N) (x : T) :
    descend parent (N + 1) m x = descend parent N m (parent N x) := by
  simp [descend, Nat.ne_of_lt (Nat.lt_succ_of_le hm)]

private lemma descend_eq_parent (parent : ℕ → T → T) :
    ∀ {N k : ℕ}, k < N → ∀ x : T, descend parent N k x = parent k (descend parent N (k + 1) x)
  | 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | N + 1, k, hk, x => by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hk'
    · rw [descend_succ_of_le parent le_rfl, descend_self, descend_self]
    · rw [descend_succ_of_le parent (le_of_lt hk'), descend_eq_parent parent hk' (parent N x),
        descend_succ_of_le parent (Nat.succ_le_of_lt hk')]

private lemma edist_le_sum_Ico_descend [PseudoEMetricSpace E] (parent : ℕ → T → T) (f : T → E)
    {m N : ℕ} (hmN : m ≤ N) (x : T) : edist (f x) (f (descend parent N m x)) ≤
      ∑ k ∈ Finset.Ico m N, edist (f (descend parent N (k + 1) x)) (f (descend parent N k x)) := by
  induction N generalizing x with
  | zero =>
    obtain rfl := Nat.eq_zero_of_le_zero hmN
    simp [descend_self]
  | succ N ih =>
    rcases eq_or_lt_of_le hmN with rfl | hmN'
    · simp [descend_self]
    have hmN_le : m ≤ N := Nat.le_of_lt_succ hmN'
    have hstep : ∑ k ∈ Finset.Ico m N,
        edist (f (descend parent N (k + 1) (parent N x))) (f (descend parent N k (parent N x))) =
        ∑ k ∈ Finset.Ico m N,
          edist (f (descend parent (N + 1) (k + 1) x)) (f (descend parent (N + 1) k x)) :=
      Finset.sum_congr rfl fun k hk ↦ by
        have hkN : k < N := (Finset.mem_Ico.1 hk).2
        rw [descend_succ_of_le parent (Nat.succ_le_of_lt hkN),
          descend_succ_of_le parent (le_of_lt hkN)]
    rw [Finset.sum_Ico_succ_top hmN_le, add_comm (∑ _ ∈ _, _), descend_succ_of_le parent hmN_le]
    refine (edist_triangle _ (f (parent N x)) _).trans ?_
    rw [descend_self, descend_succ_of_le parent le_rfl, descend_self, ← hstep]
    gcongr
    exact ih hmN_le (parent N x)

/-- Geometric-series bound for ancestor descent under `K * q ^ k` single-step bounds (`q < 1`). -/
private lemma edist_descend_le_mul_pow [PseudoEMetricSpace E] (parent : ℕ → T → T) (f : T → E)
    {K q : ℝ≥0} (hq : q < 1) {m N : ℕ} (hmN : m ≤ N) (x : T) (hstep : ∀ k ∈ Finset.Ico m N,
      edist (f (descend parent N (k + 1) x)) (f (descend parent N k x)) ≤
        (K : ℝ≥0∞) * (q : ℝ≥0∞) ^ k) :
    edist (f x) (f (descend parent N m x)) ≤ (((1 - q)⁻¹ * K : ℝ≥0) : ℝ≥0∞) * (q : ℝ≥0∞) ^ m := by
  have h1mq : 0 < 1 - q := tsub_pos_iff_lt.2 hq
  refine (edist_le_sum_Ico_descend parent f hmN x).trans ((Finset.sum_le_sum hstep).trans ?_)
  rw [Finset.sum_Ico_eq_sum_range]
  have hgeom : ∑ j ∈ Finset.range (N - m), (K : ℝ≥0∞) * (q : ℝ≥0∞) ^ (m + j) =
      ∑ j ∈ Finset.range (N - m), ((K : ℝ≥0∞) * (q : ℝ≥0∞) ^ m) * (q : ℝ≥0∞) ^ j :=
    Finset.sum_congr rfl fun j _ ↦ by rw [pow_add, mul_assoc]
  refine (hgeom.trans_le (sum_le_tsum (Finset.range (N - m)))).trans_eq ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.coe_mul, ENNReal.coe_inv h1mq.ne',
    ENNReal.coe_sub, ENNReal.coe_one]
  ring

/-- Ancestor descent along `parent` keeps elements of `M N` inside `M m` (`m ≤ N`). -/
private lemma descend_mem {S : Set T} {M : ℕ → Finset T} (hM_sub : ∀ n, (M n : Set T) ⊆ S)
    {parent : ℕ → T → T} (hparent_mem : ∀ n {w}, w ∈ S → parent n w ∈ M n) :
    ∀ {N m : ℕ} {x : T}, m ≤ N → x ∈ M N → descend parent N m x ∈ M m
  | 0, m, _, hm, hx => by
    obtain rfl := Nat.eq_zero_of_le_zero hm
    simpa [descend_self] using hx
  | N + 1, m, x, hm, hx => by
    rcases eq_or_lt_of_le hm with rfl | hm'
    · simpa [descend_self] using hx
    · rw [descend_succ_of_le parent (Nat.le_of_lt_succ hm')]
      exact descend_mem hM_sub hparent_mem (Nat.le_of_lt_succ hm')
        (hparent_mem N (hM_sub (N + 1) hx))

/-- Parameter-space displacement along ancestor descent is bounded by `(1 - r)⁻¹ * r ^ m`. -/
private lemma edist_descend_le [PseudoEMetricSpace T] {S : Set T} {M : ℕ → Finset T}
    (hM_sub : ∀ n, (M n : Set T) ⊆ S) {parent : ℕ → T → T} {r : ℝ≥0} (hr1 : r < 1)
    (hparent_mem : ∀ n {w}, w ∈ S → parent n w ∈ M n)
    (hparent_edist : ∀ n {w}, w ∈ S → edist w (parent n w) ≤ (r : ℝ≥0∞) ^ n)
    {N m : ℕ} {x : T} (hmN : m ≤ N) (hx : x ∈ M N) :
    edist x (descend parent N m x) ≤ ((1 - r)⁻¹ : ℝ≥0) * (r : ℝ≥0∞) ^ m := by
  simpa using edist_descend_le_mul_pow parent id (K := 1) hr1 hmN x fun k hk ↦ by
    have hkN : k < N := (Finset.mem_Ico.1 hk).2
    rw [id, id, descend_eq_parent parent hkN, ENNReal.coe_one, one_mul]
    exact hparent_edist k
      (hM_sub (k + 1) (descend_mem hM_sub hparent_mem (Nat.succ_le_of_lt hkN) hx))

/-- Value-space oscillation of `f` along ancestor descent is bounded by
`(1 - r ^ γ)⁻¹ * K_f * (r ^ m) ^ γ`. -/
private lemma edist_apply_descend_le [PseudoEMetricSpace E] {S : Set T} {M : ℕ → Finset T}
    (hM_sub : ∀ n, (M n : Set T) ⊆ S) {parent : ℕ → T → T} {r K_f γ : ℝ≥0}
    (hr0 : 0 < r) (hr1 : r < 1) (hγ : 0 < γ) (hparent_mem : ∀ n {w}, w ∈ S → parent n w ∈ M n)
    (f : T → E) (hf_parent : ∀ k {w}, w ∈ M (k + 1) →
      edist (f w) (f (parent k w)) ≤ (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ k) ^ (γ : ℝ))
    {N m : ℕ} {x : T} (hmN : m ≤ N) (hx : x ∈ M N) :
    edist (f x) (f (descend parent N m x)) ≤
      (((1 - r ^ (γ : ℝ))⁻¹ * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
  have hrγ_lt : r ^ (γ : ℝ) < 1 := NNReal.rpow_lt_one hr1 (by exact_mod_cast hγ)
  simpa [ENNReal.coe_rpow_of_ne_zero hr0.ne', ENNReal.pow_rpow_comm] using
    edist_descend_le_mul_pow parent f (K := K_f) hrγ_lt hmN x fun k hk ↦ by
      have hkN : k < N := (Finset.mem_Ico.1 hk).2
      rw [descend_eq_parent parent hkN]
      simpa [ENNReal.coe_rpow_of_ne_zero hr0.ne', ENNReal.pow_rpow_comm] using
        hf_parent k (descend_mem hM_sub hparent_mem (Nat.succ_le_of_lt hkN) hx)

/-- Cumulative minimal covers `M n = ⋃_{j ≤ n} N j` at geometric scales `r ^ n` with polynomial
union growth absorbed into `r ^ (-d₁)` for `d < d₁`. -/
private lemma exists_monotone_finset_isCover_of_coveringNumber_le [PseudoEMetricSpace T]
    {S : Set T} (hS : S.Nonempty) {C r : ℝ≥0} {d d₁ : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hd : 0 ≤ d) (hdd₁ : d < d₁) (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε S : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d)) :
    ∃ (M : ℕ → Finset T) (C₁ : ℝ≥0), Monotone M ∧ (M 0).Nonempty ∧ (∀ n, (M n : Set T) ⊆ S) ∧
      (∀ n, IsCover (r ^ n) S (M n)) ∧ ∀ n, ((M n).card : ℝ≥0) ≤ C₁ * (r ^ (-d₁)) ^ n := by
  classical
  have hcov_ne_top : ∀ n : ℕ, coveringNumber (r ^ n) S ≠ ⊤ := fun n ↦ by
    rw [← ENat.toENNReal_ne_top]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (by exact_mod_cast (pow_pos hr0 n).ne') ENNReal.coe_ne_top))
      (hcov (r ^ n) (pow_pos hr0 n) (pow_le_one₀ zero_le hr1.le))
  let N : ℕ → Finset T := fun n ↦ (finite_minimalCover (ε := r ^ n) (A := S)).toFinset
  have hN_sub : ∀ j, (N j : Set T) ⊆ S := fun j ↦ by
    simpa [N] using minimalCover_subset (ε := r ^ j) (A := S)
  have hN_card : ∀ n, ((N n).card : ℝ≥0) ≤ C * (r ^ (-d)) ^ n := fun n ↦ by
    have henc : ((N n).card : ℝ≥0∞) = (coveringNumber (r ^ n) S : ℝ≥0∞) := by
      exact_mod_cast (finite_minimalCover (ε := r ^ n) (A := S)).encard_eq_coe_toFinset_card.symm
        |>.trans (encard_minimalCover (hcov_ne_top n))
    have hle := henc.trans_le (hcov (r ^ n) (pow_pos hr0 n) (pow_le_one₀ zero_le hr1.le))
    rw [ENNReal.coe_pow, ENNReal.pow_rpow_comm, ← ENNReal.coe_rpow_of_ne_zero hr0.ne',
      ← ENNReal.coe_pow, ← ENNReal.coe_mul] at hle
    exact_mod_cast hle
  let M : ℕ → Finset T := fun n ↦ (Finset.range (n + 1)).biUnion N
  have hM_cover : ∀ n, IsCover (r ^ n) S (M n) := fun n x hx ↦ by
    obtain ⟨y, hy, hxy⟩ := (by simpa [N] using isCover_minimalCover (hcov_ne_top n) :
      IsCover (r ^ n) S (N n)) hx
    exact ⟨y, Finset.mem_coe.2 (Finset.subset_biUnion_of_mem N
      (Finset.mem_range.2 (Nat.lt_succ_self n)) (Finset.mem_coe.1 hy)), hxy⟩
  obtain ⟨x₀, hx₀⟩ := hS
  obtain ⟨w₀, hw₀, -⟩ := hM_cover 0 hx₀
  let α : ℝ≥0 := r ^ (d - d₁)
  have hα_gt : 1 < α := by
    simpa using NNReal.rpow_lt_rpow_of_exponent_gt hr0 hr1 (y := 0) (by linarith)
  let δ : ℝ≥0 := α - 1
  have hδ_pos : 0 < δ := tsub_pos_iff_lt.2 hα_gt
  refine ⟨M, (1 + δ⁻¹) * C, fun m n hmn ↦ Finset.biUnion_subset_biUnion_of_subset_left N
      (Finset.range_mono (Nat.add_le_add_right hmn 1)), ⟨w₀, Finset.mem_coe.1 hw₀⟩,
    fun n x hx ↦ let ⟨j, _, hxj⟩ := Finset.mem_biUnion.1 hx; hN_sub j hxj, hM_cover, fun n ↦ ?_⟩
  have h1_le_rd : 1 ≤ r ^ (-d) := by
    simpa using NNReal.rpow_le_rpow_of_exponent_ge hr0 hr1.le (y := 0) (neg_nonpos.2 hd)
  have hsum : ((M n).card : ℝ≥0) ≤ (n + 1 : ℝ≥0) * C * (r ^ (-d)) ^ n := calc
    ((M n).card : ℝ≥0) ≤ ∑ j ∈ Finset.range (n + 1), ((N j).card : ℝ≥0) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (n + 1), C * (r ^ (-d)) ^ n := Finset.sum_le_sum fun j hj ↦
      (hN_card j).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h1_le_rd (Nat.le_of_lt_succ (Finset.mem_range.1 hj))) zero_le)
    _ = (n + 1 : ℝ≥0) * C * (r ^ (-d)) ^ n := by simp [mul_assoc]
  have hbern : (n + 1 : ℝ≥0) ≤ (1 + δ⁻¹) * α ^ n := by
    rw [← NNReal.coe_le_coe]
    have hpow : 1 + (n : ℝ) * (δ : ℝ) ≤ (α : ℝ) ^ n := by
      rw [← add_tsub_cancel_of_le hα_gt.le]
      simpa using one_add_mul_le_pow (by linarith [δ.coe_nonneg] : (-2 : ℝ) ≤ δ) n
    have hinv : (δ : ℝ)⁻¹ * δ = 1 := inv_mul_cancel₀ (by exact_mod_cast hδ_pos.ne')
    have hlin : (n + 1 : ℝ) ≤ (1 + (δ : ℝ)⁻¹) * (1 + (n : ℝ) * δ) := by
      have hid : (1 + (δ : ℝ)⁻¹) * (1 + (n : ℝ) * δ) = n + 1 + ((n : ℝ) * δ + (δ : ℝ)⁻¹) := by
        linear_combination (n : ℝ) * hinv
      linarith [show (0 : ℝ) ≤ (n : ℝ) * δ + (δ : ℝ)⁻¹ by positivity]
    exact hlin.trans (by push_cast; gcongr)
  have hmul : α * r ^ (-d) = r ^ (-d₁) := by rw [← NNReal.rpow_add hr0.ne']; congr 1; ring
  exact hsum.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbern zero_le) zero_le).trans_eq (by rw [← hmul]; ring))

/-- Constructs the combined parent, star-bridge, and level-zero global-star edge families `E_all n`
over monotone covers `M n`, along with their endpoint membership, length, and cardinality bounds. -/
private lemma exists_scale_edge_finsets [PseudoEMetricSpace T] {S : Set T} {D C₁ r : ℝ≥0}
    {d₁ d' : ℝ} {K : ℕ} (hdiam : ediam S ≤ D) (hr0 : 0 < r) (hr1 : r < 1) (hdd' : d₁ < d')
    (hK_pos : 0 < K) (hd₁K_le : d₁ * (1 + (K : ℝ)⁻¹) ≤ d') {M : ℕ → Finset T} {w₀ : T}
    (hw₀M0 : w₀ ∈ M 0) (hM_sub : ∀ n, (M n : Set T) ⊆ S)
    (hM_card : ∀ n, ((M n).card : ℝ≥0) ≤ C₁ * (r ^ (-d₁)) ^ n) {parent : ℕ → T → T}
    (hparent_mem : ∀ n {w}, w ∈ S → parent n w ∈ M n)
    (hparent_edist : ∀ n {w}, w ∈ S → edist w (parent n w) ≤ (r : ℝ≥0∞) ^ n) :
    ∃ (E_all : ℕ → Finset (T × T)) (C_edge A : ℝ≥0),
      (∀ n {p : T × T}, p ∈ E_all n → p.1 ∈ (⋃ m, (M m : Set T)) ∧ p.2 ∈ (⋃ m, (M m : Set T))) ∧
      (∀ n {p : T × T}, p ∈ E_all n → edist p.1 p.2 ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) ∧
      (∀ n, ((E_all n).card : ℝ≥0) ≤ C_edge * (r ^ (-d')) ^ n) ∧
      (∀ n {w}, w ∈ M (n + 1) → (w, parent n w) ∈ E_all n) ∧
      (∀ n {u v}, u ∈ M n → v ∈ M n →
        edist u v ≤ 2 * ((((1 - r)⁻¹ + 1 : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) →
        ∃ z ∈ M n, (u, z) ∈ E_all n ∧ (v, z) ∈ E_all n) ∧
      ∀ {w}, w ∈ M 0 → (w, w₀) ∈ E_all 0 := by
  classical
  let c_δ : ℝ≥0 := (1 - r)⁻¹ + 1
  let bridge := fun n : ℕ ↦
    exists_finset_edist_le_card_le_rpow (M n) ((c_δ : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) hK_pos
  let E_parent : ℕ → Finset (T × T) := fun n ↦ (M (n + 1)).image fun w ↦ (w, parent n w)
  let E_bridge : ℕ → Finset (T × T) := fun n ↦ (bridge n).choose
  let E_global : ℕ → Finset (T × T) := fun n ↦ if n = 0 then (M 0).image (·, w₀) else ∅
  let E_all : ℕ → Finset (T × T) := fun n ↦ E_parent n ∪ E_bridge n ∪ E_global n
  let A : ℝ≥0 := max 1 (max ((2 * K : ℕ) * c_δ) D)
  let C_edge : ℝ≥0 := C₁ * r ^ (-d₁) + C₁ ^ (1 + (K : ℝ)⁻¹) + C₁
  refine ⟨E_all, C_edge, A, fun n {p} hp ↦ ?_, fun n {p} hp ↦ ?_, fun n ↦ ?_,
    fun n {w} hw ↦ Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw)),
    fun n {u v} hu hv huv ↦ ?_, fun {w} hw ↦ Finset.mem_union_right _
      (by simpa only [E_global, ↓reduceIte] using Finset.mem_image_of_mem (·, w₀) hw)⟩
  · rcases Finset.mem_union.1 hp with hp12 | hp3
    · rcases Finset.mem_union.1 hp12 with hp1 | hp2
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hp1
        exact ⟨mem_iUnion.2 ⟨n + 1, hw⟩, mem_iUnion.2 ⟨n, hparent_mem n (hM_sub (n + 1) hw)⟩⟩
      · have h := (bridge n).choose_spec.1 (Finset.mem_coe.2 hp2)
        exact ⟨mem_iUnion.2 ⟨n, h.1⟩, mem_iUnion.2 ⟨n, h.2⟩⟩
    · rcases eq_or_ne n 0 with rfl | hn0
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (by simpa [E_global] using hp3)
        exact ⟨mem_iUnion.2 ⟨0, hw⟩, mem_iUnion.2 ⟨0, hw₀M0⟩⟩
      · simp [E_global, hn0] at hp3
  · rcases Finset.mem_union.1 hp with hp12 | hp3
    · rcases Finset.mem_union.1 hp12 with hp1 | hp2
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hp1
        have h1A : (1 : ℝ≥0∞) ≤ A := ENNReal.coe_le_coe.2 (le_max_left 1 _)
        exact (hparent_edist n (hM_sub (n + 1) hw)).trans
          (by simpa using mul_le_mul_of_nonneg_right h1A zero_le)
      · have hbA : (((2 * K : ℕ) * c_δ : ℝ≥0) : ℝ≥0∞) ≤ A :=
          ENNReal.coe_le_coe.2 ((le_max_left _ D).trans (le_max_right 1 _))
        refine ((bridge n).choose_spec.2.1 p hp2).trans ?_
        rw [← mul_assoc]
        push_cast at hbA ⊢
        exact mul_le_mul_of_nonneg_right hbA zero_le
    · rcases eq_or_ne n 0 with rfl | hn0
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (by simpa [E_global] using hp3)
        have hDA : (D : ℝ≥0∞) ≤ A :=
          ENNReal.coe_le_coe.2 ((le_max_right _ D).trans (le_max_right 1 _))
        exact (edist_le_ediam_of_mem (hM_sub 0 hw) (hM_sub 0 hw₀M0)).trans
          (hdiam.trans (by simpa using hDA))
      · simp [E_global, hn0] at hp3
  · have hp_c : ((E_parent n).card : ℝ≥0) ≤ (C₁ * r ^ (-d₁)) * (r ^ (-d')) ^ n :=
      (Nat.cast_le.2 Finset.card_image_le).trans <| (hM_card (n + 1)).trans <|
        (by ring : C₁ * (r ^ (-d₁)) ^ (n + 1) = (C₁ * r ^ (-d₁)) * (r ^ (-d₁)) ^ n).trans_le <|
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left' (NNReal.rpow_le_rpow_of_exponent_ge hr0 hr1.le (neg_le_neg hdd'.le)) n)
          zero_le
    have hb_c : ((E_bridge n).card : ℝ≥0) ≤ C₁ ^ (1 + (K : ℝ)⁻¹) * (r ^ (-d')) ^ n := by
      refine ((bridge n).choose_spec.2.2.1).trans
        ((NNReal.rpow_le_rpow (hM_card n) (by positivity)).trans ?_)
      rw [NNReal.mul_rpow, ← NNReal.rpow_natCast_mul, mul_comm (n : ℝ), NNReal.rpow_mul_natCast]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left' ?_ n) zero_le
      rw [← NNReal.rpow_mul, neg_mul]
      exact NNReal.rpow_le_rpow_of_exponent_ge hr0 hr1.le (neg_le_neg hd₁K_le)
    have hg_c : ((E_global n).card : ℝ≥0) ≤ C₁ * (r ^ (-d')) ^ n := by
      rcases eq_or_ne n 0 with rfl | hn0
      · simpa [E_global] using (Nat.cast_le.2 Finset.card_image_le).trans (by simpa using hM_card 0)
      · simp [E_global, hn0]
    have hunion : ((E_all n).card : ℝ≥0) ≤
        ((E_parent n).card : ℝ≥0) + ((E_bridge n).card : ℝ≥0) + ((E_global n).card : ℝ≥0) := by
      exact_mod_cast (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    exact hunion.trans ((add_le_add (add_le_add hp_c hb_c) hg_c).trans_eq (by dsimp [C_edge]; ring))
  · obtain ⟨z, hz, huz, hvz⟩ := (bridge n).choose_spec.2.2.2 u hu v hv huv
    exact ⟨z, hz, Finset.mem_union_left _ (Finset.mem_union_right _ huz),
      Finset.mem_union_left _ (Finset.mem_union_right _ hvz)⟩

/-- Combines ancestor descent with scale-`m` star-bridge edges at small distances and level-zero
global-star edges at arbitrary distances to deduce `HolderOnWith` on `⋃ n, M n`. -/
private lemma holderOnWith_iUnion_of_scale_edges [PseudoEMetricSpace T] [PseudoEMetricSpace E]
    {S : Set T} {M : ℕ → Finset T} (hM_mono : Monotone M) {w₀ : T} (hM_sub : ∀ n, (M n : Set T) ⊆ S)
    {parent : ℕ → T → T} {r K_f γ : ℝ≥0} (hparent_mem : ∀ n {w}, w ∈ S → parent n w ∈ M n)
    (hparent_edist : ∀ n {w}, w ∈ S → edist w (parent n w) ≤ (r : ℝ≥0∞) ^ n)
    (hr0 : 0 < r) (hr1 : r < 1) (hγ : 0 < γ) {E_all : ℕ → Finset (T × T)}
    (hE_parent : ∀ n {w}, w ∈ M (n + 1) → (w, parent n w) ∈ E_all n)
    (hE_bridge : ∀ n {u v}, u ∈ M n → v ∈ M n →
      edist u v ≤ 2 * ((((1 - r)⁻¹ + 1 : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) →
      ∃ z ∈ M n, (u, z) ∈ E_all n ∧ (v, z) ∈ E_all n)
    (hE_global : ∀ {w}, w ∈ M 0 → (w, w₀) ∈ E_all 0) (f : T → E)
    (hf_edge : ∀ n {p : T × T}, p ∈ E_all n →
      edist (f p.1) (f p.2) ≤ (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ (γ : ℝ)) :
    HolderOnWith (((2 * (1 - r ^ (γ : ℝ))⁻¹ + 2) * r⁻¹ ^ (γ : ℝ)) * K_f) γ f
      (⋃ n, (M n : Set T)) := by
  let c_chain : ℝ≥0 := 2 * (1 - r ^ (γ : ℝ))⁻¹ + 2
  have hf_parent : ∀ k {w}, w ∈ M (k + 1) →
      edist (f w) (f (parent k w)) ≤ (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ k) ^ (γ : ℝ) :=
    fun k {w} hw ↦ hf_edge k (hE_parent k hw)
  rw [mul_right_comm]
  refine holderOnWith_of_forall_pow_le hr0 hr1 hγ
    (fun {x y} hx hy m hxy ↦ ?_) (fun {x y} hx hy ↦ ?_)
  · -- Small-scale case (`edist x y ≤ r ^ m`): descend both points to `M m` and cross a star bridge.
    obtain ⟨Nx, hNx⟩ := mem_iUnion.1 hx
    obtain ⟨Ny, hNy⟩ := mem_iUnion.1 hy
    let N := max m (max Nx Ny)
    have hmN : m ≤ N := le_max_left _ _
    have hxN : x ∈ M N :=
      hM_mono ((le_max_left Nx Ny).trans (le_max_right m _)) (Finset.mem_coe.1 hNx)
    have hyN : y ∈ M N :=
      hM_mono ((le_max_right Nx Ny).trans (le_max_right m _)) (Finset.mem_coe.1 hNy)
    let u := descend parent N m x
    let v := descend parent N m y
    have huv : edist u v ≤ 2 * ((((1 - r)⁻¹ + 1 : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ m) := by
      refine (edist_triangle4 u x y v).trans ?_
      rw [edist_comm u x]
      refine (add_le_add
        (add_le_add (edist_descend_le hM_sub hr1 hparent_mem hparent_edist hmN hxN) hxy)
        (edist_descend_le hM_sub hr1 hparent_mem hparent_edist hmN hyN)).trans ?_
      refine ((by ring : _ = (2 * (((1 - r)⁻¹ : ℝ≥0) : ℝ≥0∞) + 1) * (r : ℝ≥0∞) ^ m).trans_le
        (by gcongr; norm_num : _ ≤ (2 * (((1 - r)⁻¹ : ℝ≥0) : ℝ≥0∞) + 2) * (r : ℝ≥0∞) ^ m)).trans_eq
        (by push_cast; ring)
    obtain ⟨z, -, huz, hvz⟩ := hE_bridge m
      (descend_mem hM_sub hparent_mem hmN hxN) (descend_mem hM_sub hparent_mem hmN hyN) huv
    have hf_uv : edist (f u) (f v) ≤ 2 * ((K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ)) := by
      rw [two_mul]
      exact (edist_triangle _ (f z) _).trans
        (edist_comm (f z) (f v) ▸ add_le_add (hf_edge m huz) (hf_edge m hvz))
    refine (edist_triangle4 (f x) (f u) (f v) (f y)).trans ?_
    rw [edist_comm (f v) (f y)]
    exact (add_le_add
      (add_le_add (edist_apply_descend_le hM_sub hr0 hr1 hγ hparent_mem f hf_parent hmN hxN) hf_uv)
      (edist_apply_descend_le hM_sub hr0 hr1 hγ hparent_mem f hf_parent hmN hyN)).trans_eq
      (by dsimp [c_chain]; ring)
  · -- Global diameter case: descend both points to `M 0` and connect via the basepoint `w₀`.
    obtain ⟨Nx, hNx⟩ := mem_iUnion.1 hx
    obtain ⟨Ny, hNy⟩ := mem_iUnion.1 hy
    let N := max Nx Ny
    have hxN : x ∈ M N := hM_mono (le_max_left Nx Ny) (Finset.mem_coe.1 hNx)
    have hyN : y ∈ M N := hM_mono (le_max_right Nx Ny) (Finset.mem_coe.1 hNy)
    let u := descend parent N 0 x
    let v := descend parent N 0 y
    have hu0 := hE_global (descend_mem hM_sub hparent_mem (Nat.zero_le N) hxN)
    have hv0 := hE_global (descend_mem hM_sub hparent_mem (Nat.zero_le N) hyN)
    have hf_uv : edist (f u) (f v) ≤ 2 * (K_f : ℝ≥0∞) := by
      rw [two_mul]
      exact (edist_triangle _ (f w₀) _).trans (edist_comm (f w₀) (f v) ▸
        add_le_add (by simpa using hf_edge 0 hu0) (by simpa using hf_edge 0 hv0))
    refine (edist_triangle4 (f x) (f u) (f v) (f y)).trans ?_
    rw [edist_comm (f v) (f y)]
    have hxu := by
      simpa using
        edist_apply_descend_le hM_sub hr0 hr1 hγ hparent_mem f hf_parent (Nat.zero_le N) hxN
    have hyv := by
      simpa using
        edist_apply_descend_le hM_sub hr0 hr1 hγ hparent_mem f hf_parent (Nat.zero_le N) hyN
    exact (add_le_add (add_le_add hxu hf_uv) hyv).trans_eq (by dsimp [c_chain]; ring)

/-- **Multiscale deterministic Hölder chaining.** Let `S` be a subset of a pseudo-emetric space
with extended diameter at most `D` and covering numbers bounded by `C ε ^ (-d)` for `0 < ε ≤ 1`.
For any `r ∈ (0, 1)` and any `d' > d`, there exist a countable subset `U ⊆ S` whose closure
contains `S` and edge families `(s n, t n)` in `U` at each scale `n` with at most
`C_edge (r ^ (-d')) ^ n` edges of length at most `A r ^ n`, such that any map `f` into a
pseudo-emetric space obeying a `γ`-Hölder bound (`γ > 0`) along those edges is `γ`-Hölder on `U`
with a deterministic multiple of the edge constant. -/
theorem exists_edges_and_holderOnWith_of_coveringNumber_le [PseudoEMetricSpace T]
    {S : Set T} {D C r : ℝ≥0} {d d' : ℝ} (hdiam : ediam S ≤ D) (hr0 : 0 < r) (hr1 : r < 1)
    (hdd' : d < d') (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε S : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d)) :
    ∃ (U : Set T) (k : ℕ → ℕ) (s t : (n : ℕ) → Fin (k n) → T) (C_edge A : ℝ≥0),
      U.Countable ∧ U ⊆ S ∧ S ⊆ closure U ∧ (∀ n i, s n i ∈ U ∧ t n i ∈ U) ∧
      (∀ n, (k n : ℝ≥0) ≤ C_edge * (r ^ (-d')) ^ n) ∧
      (∀ n i, edist (s n i) (t n i) ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) ∧
      ∀ {γ : ℝ≥0}, 0 < γ → ∃ C_H : ℝ≥0,
        ∀ {E : Type*} [PseudoEMetricSpace E] (f : T → E) (K_f : ℝ≥0),
          (∀ n i, edist (f (s n i)) (f (t n i)) ≤ (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ (γ : ℝ)) →
          HolderOnWith (C_H * K_f) γ f U := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨∅, fun _ ↦ 0, fun _ ↦ Fin.elim0, fun _ ↦ Fin.elim0, 0, 0, countable_empty, subset_rfl,
      subset_closure, fun _ i ↦ i.elim0, fun _ ↦ by simp, fun _ i ↦ i.elim0,
      fun _ ↦ ⟨0, fun _ _ _ ↦ by simp [HolderOnWith]⟩⟩
  -- Phase 1: split `(d, d')` at `d₁ = (d + d') / 2` and choose `K ≥ 1` so `d₁ * (1 + 1 / K) ≤ d'`.
  have hd : 0 ≤ d := nonneg_of_coveringNumber_le hS hcov
  let d₁ : ℝ := (d + d') / 2
  have hd_lt_d₁ : d < d₁ := by dsimp [d₁]; linarith
  have hd₁_lt_d' : d₁ < d' := by dsimp [d₁]; linarith
  have hd₁_pos : 0 < d₁ := hd.trans_lt hd_lt_d₁
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (d₁ / (d' - d₁))
  let K : ℕ := max 1 K₀
  have hK_pos : 0 < K := by positivity
  have hd₁K_le : d₁ * (1 + (K : ℝ)⁻¹) ≤ d' := by
    have hK_gt : d₁ / (d' - d₁) < K := hK₀.trans_le (by exact_mod_cast le_max_right 1 K₀)
    have hinv : (K : ℝ)⁻¹ ≤ (d' - d₁) / d₁ := by
      rw [inv_le_iff_one_le_mul₀ (by exact_mod_cast hK_pos), div_mul_eq_mul_div,
        one_le_div hd₁_pos]
      linarith [(div_lt_iff₀ (sub_pos.2 hd₁_lt_d')).1 hK_gt]
    exact (mul_le_mul_of_nonneg_left (add_le_add_right hinv 1) hd₁_pos.le).trans_eq
      (by field_simp; ring)
  -- Phase 2: construct cumulative minimal covers `M n` and parent pointers `parent n`.
  obtain ⟨M, C₁, hM_mono, ⟨w₀, hw₀M0⟩, hM_sub, hM_cover, hM_card⟩ :=
    exists_monotone_finset_isCover_of_coveringNumber_le hS hr0 hr1 hd hd_lt_d₁ hcov
  let U : Set T := ⋃ n, (M n : Set T)
  have hS_closure : S ⊆ closure U := fun x hx ↦ EMetric.mem_closure_iff.2 fun ε hε ↦ by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.coe_lt_one_iff.2 hr1))).2 ε hε).exists
    obtain ⟨y, hy, hxy⟩ := hM_cover n hx
    exact ⟨y, mem_iUnion.2 ⟨n, hy⟩, hxy.trans_lt (by simpa [ENNReal.coe_pow] using hn)⟩
  let parent : ℕ → T → T := fun n w ↦ if hw : w ∈ S then (hM_cover n hw).choose else w₀
  have hparent_mem : ∀ n {w}, w ∈ S → parent n w ∈ M n := fun n {w} hw ↦ by
    simpa only [parent, hw, ↓reduceDIte] using Finset.mem_coe.1 (hM_cover n hw).choose_spec.1
  have hparent_edist : ∀ n {w}, w ∈ S → edist w (parent n w) ≤ (r : ℝ≥0∞) ^ n := fun n {w} hw ↦ by
    simpa [parent, hw, ENNReal.coe_pow] using (hM_cover n hw).choose_spec.2
  -- Phase 3: assemble parent, star-bridge, and global-star edges and index them by `Fin`.
  obtain ⟨E_all, C_edge, A, hE_U, hE_len, hk_card, hE_parent, hE_bridge, hE_global⟩ :=
    exists_scale_edge_finsets hdiam hr0 hr1 hd₁_lt_d' hK_pos hd₁K_le hw₀M0 hM_sub hM_card
      hparent_mem hparent_edist
  let eFin := fun n ↦ (E_all n).equivFin
  let s : (n : ℕ) → Fin (E_all n).card → T := fun n i ↦ ((eFin n).symm i).1.1
  let t : (n : ℕ) → Fin (E_all n).card → T := fun n i ↦ ((eFin n).symm i).1.2
  -- Phase 4: conclude `HolderOnWith` on `U` for any map controlled along `(s n, t n)`.
  refine ⟨U, fun n ↦ (E_all n).card, s, t, C_edge, A,
    countable_iUnion fun n ↦ (M n).countable_toSet,
    iUnion_subset hM_sub, hS_closure, fun n i ↦ hE_U n ((eFin n).symm i).2, hk_card,
    fun n i ↦ hE_len n ((eFin n).symm i).2, fun {γ} hγ ↦ ?_⟩
  refine ⟨(2 * (1 - r ^ (γ : ℝ))⁻¹ + 2) * r⁻¹ ^ (γ : ℝ), fun f K_f hf ↦
    holderOnWith_iUnion_of_scale_edges hM_mono hM_sub hparent_mem hparent_edist hr0 hr1 hγ
      hE_parent hE_bridge hE_global f fun n {p} hp ↦ ?_⟩
  simpa [s, t] using hf n (eFin n ⟨p, hp⟩)

end MultiscaleChaining

end TauCeti
