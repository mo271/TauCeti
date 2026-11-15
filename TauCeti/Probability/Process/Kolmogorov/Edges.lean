/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Geometric edge estimates for Kolmogorov processes

A moment bound on increments controls all edges in a sequence of finite nets at once.
At level `n`, allow at most `C * a^n` edges of length at most `r^n`, and normalize
their increments by `c^n`. For `c > 0`, if `a * r^q / c^p < 1`, the supremum of the normalized
`p`th powers has a finite moment, bounded by a geometric series. Consequently one
finite random constant bounds every edge at every level, outside one common null set.

These estimates are the probabilistic input to chaining: they do not assume that the
edges form nets, and do not by themselves assert continuity of a modification.
Neither independence nor probability normalization is needed. The value space may be
an extended pseudometric space, and the estimates also apply to almost-everywhere
modifications of native Kolmogorov processes.

The argument is the weighted edge-sum estimate underlying Kolmogorov--Chentsov
continuity proofs; see Krätschmer--Urusov, *A general Kolmogorov--Chentsov type theorem
on general metric spaces*, arXiv:2107.13837v2, Theorem 1.1. We use Mathlib's
`IsAEKolmogorovProcess`, nonnegative Tonelli theorem and geometric-series formula.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.IsAEKolmogorovProcess

variable {T Ω E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
  {p q : ℝ} {M : ℝ≥0} {k : ℕ → ℕ}
  {s t : (n : ℕ) → Fin (k n) → T}

/-- The supremum over geometrically sized edge families has a geometric moment bound.
The edge count is allowed to be zero, and endpoints and edges may repeat. -/
theorem lintegral_iSup_edist_div_pow_rpow_le (hX : IsAEKolmogorovProcess X P p q M)
    {C a r c : ℝ≥0} (hcard : ∀ n, (k n : ℝ≥0) ≤ C * a ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (r : ℝ≥0∞) ^ n) :
    ∫⁻ ω, ⨆ n, ⨆ i, (edist (X (s n i) ω) (X (t n i) ω) /
      (c : ℝ≥0∞) ^ n) ^ p ∂P ≤
        (C : ℝ≥0∞) * M * (1 - (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q /
          (c : ℝ≥0∞) ^ p)⁻¹ := by
  -- Dominate the maximum by the total edge energy and apply nonnegative Tonelli.
  calc
    _ ≤ ∫⁻ ω, ∑' n, ∑ i, (edist (X (s n i) ω) (X (t n i) ω) /
          (c : ℝ≥0∞) ^ n) ^ p ∂P := by
      apply lintegral_mono
      intro ω
      refine iSup_le fun n ↦ iSup_le fun i ↦ ?_
      exact (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ i)).trans
        (le_tsum (fun n ↦ ∑ i, (edist (X (s n i) ω) (X (t n i) ω) /
          (c : ℝ≥0∞) ^ n) ^ p) n)
    _ = ∑' n, ∫⁻ ω, ∑ i, (edist (X (s n i) ω) (X (t n i) ω) /
          (c : ℝ≥0∞) ^ n) ^ p ∂P := by
      apply lintegral_tsum
      intro n
      exact Finset.aemeasurable_fun_sum _ fun i _ ↦
        (hX.aemeasurable_edist.div_const _).pow_const p
    _ ≤ ∑' n, (C : ℝ≥0∞) * M *
          ((a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p) ^ n := by
      -- At each level, combine the increment moment, edge length and edge count bounds.
      apply tsum_le_tsum
      intro n
      calc
        _ ≤ (M : ℝ≥0∞) * (∑ i, edist (s n i) (t n i) ^ q) /
            ((c : ℝ≥0∞) ^ n) ^ p := by
          simp_rw [ENNReal.div_rpow_of_nonneg _ _ hX.p_pos.le, div_eq_mul_inv]
          rw [lintegral_finsetSum' _ (fun i _ ↦
            (hX.aemeasurable_edist.pow_const p).mul_const _)]
          simp_rw [lintegral_mul_const'' _ (hX.aemeasurable_edist.pow_const p)]
          rw [← Finset.sum_mul, Finset.mul_sum]
          gcongr
          exact hX.kolmogorovCondition _ _
        _ ≤ (M : ℝ≥0∞) * ((k n : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ q) /
            ((c : ℝ≥0∞) ^ n) ^ p := by
          gcongr
          exact (Finset.sum_le_sum fun i _ ↦
            ENNReal.rpow_le_rpow (hedge n i) hX.q_pos.le).trans_eq (by simp)
        _ ≤ (M : ℝ≥0∞) * (((C : ℝ≥0∞) * (a : ℝ≥0∞) ^ n) *
            ((r : ℝ≥0∞) ^ n) ^ q) / ((c : ℝ≥0∞) ^ n) ^ p := by
          gcongr
          exact_mod_cast hcard n
        _ = _ := by
          simp only [ENNReal.pow_rpow_comm, mul_pow, div_eq_mul_inv, ENNReal.inv_pow]
          ring
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- When the geometric ratio is less than one, a single finite constant bounds all
normalized edges, simultaneously at every level. -/
theorem ae_exists_edist_le_mul_pow (hX : IsAEKolmogorovProcess X P p q M)
    {C a r c : ℝ≥0} (hc : c ≠ 0)
    (hcard : ∀ n, (k n : ℝ≥0) ≤ C * a ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (r : ℝ≥0∞) ^ n)
    (hratio : a * r ^ q / c ^ p < 1) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, ∀ n i,
      edist (X (s n i) ω) (X (t n i) ω) ≤ (K : ℝ≥0∞) * (c : ℝ≥0∞) ^ n := by
  let Z : Ω → ℝ≥0∞ := fun ω ↦ ⨆ n, ⨆ i,
    (edist (X (s n i) ω) (X (t n i) ω) / (c : ℝ≥0∞) ^ n) ^ p
  have hZ : AEMeasurable Z P := AEMeasurable.iSup fun n ↦ AEMeasurable.iSup fun i ↦
    (hX.aemeasurable_edist.div_const _).pow_const p
  have hratio' : (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p < 1 := by
    rw [← ENNReal.coe_rpow_of_nonneg _ hX.q_pos.le,
      ← ENNReal.coe_rpow_of_nonneg _ hX.p_pos.le, ← ENNReal.coe_mul,
      ← ENNReal.coe_div (NNReal.rpow_pos (pos_iff_ne_zero.mpr hc)).ne']
    exact_mod_cast hratio
  have hfinite : (C : ℝ≥0∞) * M *
      (1 - (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p)⁻¹ ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
      (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hratio')))
  have hZfinite : ∫⁻ ω, Z ω ∂P ≠ ⊤ := ne_top_of_le_ne_top hfinite
    (hX.lintegral_iSup_edist_div_pow_rpow_le hcard hedge)
  filter_upwards [ae_lt_top' hZ hZfinite] with ω hω
  refine ⟨(Z ω).toNNReal ^ p⁻¹, fun n i ↦ ?_⟩
  have hi : (edist (X (s n i) ω) (X (t n i) ω) /
      (c : ℝ≥0∞) ^ n) ^ p ≤ Z ω := le_iSup_of_le n (le_iSup_of_le i le_rfl)
  have hroot := (ENNReal.le_rpow_inv_iff hX.p_pos).mpr hi
  rw [← ENNReal.coe_toNNReal hω.ne, ← ENNReal.coe_rpow_of_nonneg _
    (inv_pos.mpr hX.p_pos).le] at hroot
  exact (ENNReal.div_le_iff (pow_ne_zero _ (by exact_mod_cast hc)) (by simp)).mp hroot

/-- Entropy growth of dimension `d` permits every edge exponent `γ` with
`d + p * γ < q`, giving a Hölder bound when `γ > 0`.
This is a bound on the supplied edges, not yet on arbitrary pairs
of parameter points. No topology or completeness assumption beyond the native
Kolmogorov condition is required. -/
theorem ae_exists_edist_le_mul_pow_rpow (hX : IsAEKolmogorovProcess X P p q M)
    {C r : ℝ≥0} {d γ : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hcard : ∀ n, (k n : ℝ≥0) ≤ C * (r ^ (-d)) ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (r : ℝ≥0∞) ^ n)
    (hγ : d + p * γ < q) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, ∀ n i,
      edist (X (s n i) ω) (X (t n i) ω) ≤
        (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
  have hratio : r ^ (-d) * r ^ q / (r ^ γ) ^ p < 1 := by
    rw [← NNReal.rpow_mul, ← NNReal.rpow_add hr.ne', ← NNReal.rpow_sub hr.ne']
    exact NNReal.rpow_lt_one hr₁ (by linarith)
  filter_upwards [hX.ae_exists_edist_le_mul_pow (NNReal.rpow_pos hr).ne'
    hcard hedge hratio] with ω hω
  obtain ⟨K, hK⟩ := hω
  refine ⟨K, fun n i ↦ ?_⟩
  simpa only [ENNReal.coe_rpow_of_ne_zero hr.ne', ENNReal.pow_rpow_comm] using hK n i

/-- Between parameter points at finite extended distance, increments of an `IsAEKolmogorovProcess`
are almost everywhere finite. -/
theorem ae_edist_lt_top (hX : IsAEKolmogorovProcess X P p q M) {s' t' : T}
    (hst : edist s' t' ≠ ⊤) :
    ∀ᵐ ω ∂P, edist (X s' ω) (X t' ω) < ⊤ := by
  have hlt : ∫⁻ ω, edist (X s' ω) (X t' ω) ^ p ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hX.q_pos.le hst)) (hX.kolmogorovCondition s' t')
  filter_upwards [ae_lt_top' (hX.aemeasurable_edist.pow_const p) hlt] with ω hω
  exact lt_top_iff_ne_top.2 fun htop ↦ by simp [htop, hX.p_pos] at hω

/-- Extending `ae_exists_edist_le_mul_pow_rpow` to edge lengths bounded by `A * r ^ n` for an
arbitrary constant `A : ℝ≥0`. -/
theorem ae_exists_edist_le_mul_pow_rpow_of_le_mul (hX : IsAEKolmogorovProcess X P p q M)
    {C A r : ℝ≥0} {d γ : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hcard : ∀ n, (k n : ℝ≥0) ≤ C * (r ^ (-d)) ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n)
    (hγ : d + p * γ < q) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, ∀ n i,
      edist (X (s n i) ω) (X (t n i) ω) ≤ (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
  -- Shift levels by `m₀` so `A * r ^ m₀ < 1`, absorbing `A` into the geometric tail.
  have htend : Tendsto (fun m : ℕ ↦ A * r ^ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hr₁).const_mul A
  obtain ⟨m₀, hm₀⟩ := ((tendsto_order.1 htend).2 1 zero_lt_one).exists
  have hcard_shift : ∀ n, (k (n + m₀) : ℝ≥0) ≤ (C * (r ^ (-d)) ^ m₀) * (r ^ (-d)) ^ n :=
    fun n ↦ (hcard (n + m₀)).trans_eq (by rw [pow_add]; ring)
  have hedge_shift : ∀ n i, edist (s (n + m₀) i) (t (n + m₀) i) ≤ (r : ℝ≥0∞) ^ n := fun n i ↦ by
    have hm₀' : ((A * r ^ m₀ : ℝ≥0) : ℝ≥0∞) ≤ 1 := ENNReal.coe_le_coe.2 hm₀.le
    calc
      edist (s (n + m₀) i) (t (n + m₀) i) ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ (n + m₀) :=
        hedge (n + m₀) i
      _ = ((A * r ^ m₀ : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_mul, ENNReal.coe_pow, pow_add]; ring
      _ ≤ 1 * (r : ℝ≥0∞) ^ n := mul_le_mul_of_nonneg_right hm₀' zero_le
      _ = (r : ℝ≥0∞) ^ n := one_mul _
  -- Control the finitely many head levels `n < m₀` via `ae_edist_lt_top`.
  have hhead : ∀ n ∈ Finset.range m₀, ∀ᵐ ω ∂P, ∀ i : Fin (k n),
      edist (X (s n i) ω) (X (t n i) ω) < ⊤ := fun n _ ↦ ae_all_iff.2 fun i ↦
    hX.ae_edist_lt_top <| ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)) (hedge n i)
  filter_upwards [hX.ae_exists_edist_le_mul_pow_rpow hr hr₁ hcard_shift hedge_shift hγ,
    (ae_ball_iff (Finset.countable_toSet _)).2 hhead] with ω ⟨K₁, hK₁⟩ hω_head
  let S_head : Finset ℝ≥0 := (Finset.range m₀).biUnion fun n ↦ Finset.univ.image fun i : Fin (k n) ↦
    (edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n
  let K : ℝ≥0 := max (K₁ * (r ^ (-γ)) ^ m₀) (S_head.sup id)
  refine ⟨K, fun n i ↦ ?_⟩
  rcases lt_or_ge n m₀ with hnm | hnm
  · have hfin : edist (X (s n i) ω) (X (t n i) ω) ≠ ⊤ := (hω_head n (Finset.mem_range.2 hnm) i).ne
    have hle_K : (edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n ≤ K :=
      (Finset.le_sup (f := id) (Finset.mem_biUnion.2
        ⟨n, Finset.mem_range.2 hnm, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)).trans
        (le_max_right _ _)
    calc
      edist (X (s n i) ω) (X (t n i) ω) =
          (((edist (X (s n i) ω) (X (t n i) ω)).toNNReal * (r ^ (-γ)) ^ n : ℝ≥0) : ℝ≥0∞) *
            ((r ^ γ : ℝ≥0) : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hfin, mul_assoc, ← ENNReal.coe_pow,
          ← ENNReal.coe_mul, NNReal.rpow_neg_pow_mul_rpow_pow hr.ne', ENNReal.coe_one, mul_one]
      _ ≤ (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
        rw [ENNReal.coe_rpow_of_ne_zero hr.ne', ENNReal.pow_rpow_comm]; gcongr
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hnm
    refine (hK₁ n' i).trans ?_
    have heq : (K₁ : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n') ^ γ =
        ((K₁ * (r ^ (-γ)) ^ m₀ : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ (n' + m₀)) ^ γ := by
      rw [ENNReal.pow_rpow_comm, ENNReal.pow_rpow_comm, ← ENNReal.coe_rpow_of_ne_zero hr.ne',
        ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      congr 1
      rw [pow_add, mul_assoc, mul_left_comm ((r ^ (-γ)) ^ m₀),
        NNReal.rpow_neg_pow_mul_rpow_pow hr.ne', mul_one]
    exact heq.trans_le (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.2 (le_max_left _ _)) zero_le)

end ProbabilityTheory.IsAEKolmogorovProcess
