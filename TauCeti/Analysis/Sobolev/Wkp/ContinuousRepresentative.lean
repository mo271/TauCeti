/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import TauCeti.Analysis.Sobolev.Morrey.StarConvex
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Exponent

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Analysis.Sobolev.Wkp.StarConvex
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Continuous representatives, point evaluation, and boundary continuity on star-shaped domains

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space `E` of dimension
`n` that is star-convex with respect to every point of an open ball `ball x₀ ρ` of positive radius
`ρ`, with `diam Ω ≤ γ * ρ`. Let `1 ≤ p ≤ ∞` and `k : ℕ` satisfy the supercritical condition
`n < k * p` or `p = 1 ∧ n ≤ k`. This file proves that every `u ∈ W^{k,p}(Ω)` admits a unique
representative continuous on `closure Ω` (hence uniformly continuous on `Ω`), satisfying the
diameter-weighted supremum estimate

`sup_{closure Ω} |u| ≤ C(n, k, p, γ, μ(B(0, 1))) * ∑_{j ≤ k} (diam Ω) ^ (j - n / p) * |u|_{j,p}`,

where `n / ∞ = 0`. In particular, point evaluation at every `x ∈ closure Ω` is a bounded linear
functional on `W^{k,p}(Ω)`. Moreover, for `j + 1 ≤ k` with `(k - (j + 1)) * p > n` (or `p = 1` and
`n ≤ k - (j + 1)`) and any direction `v : E`, the directional derivative component
`x ↦ (D^{j+1} u)(x)⟨v⟩^{j+1}` also admits a representative continuous on `closure Ω` and uniformly
continuous on `Ω`.

## Method

For `W^{k,p}(Ω)` with `p < ∞`, smooth-up-to-the-boundary approximants from
`TauCeti.Wkp.dense_contDiff_representatives_of_forall_starConvex` are controlled in the supremum
norm on `closure Ω` by the classical estimate
`TauCeti.enorm_le_sum_eLpNorm_of_contDiffOn_of_forall_starConvex`. Passing to a Cauchy sequence in
the Banach space `closure Ω →ᵇ ℝ` produces the unique continuous representative up to the boundary.
For `p = ∞` (`k ≥ 1`), lowering the exponent to `n + 1` via `TauCeti.Wkp.ofExponentLEL` transfers
both continuity up to the boundary and the diameter-weighted estimate, with the powers of `diam Ω`
from the volume bound `μ(Ω) ≤ μ(B(0, 1)) * (diam Ω) ^ n` cancelling identically. For directional
derivative components, iterating `TauCeti.Wkp.lineDerivL` places `x ↦ (D^{j+1} u)(x)⟨v⟩^{j+1}` in
`W^{k - (j + 1), p}(Ω)`, to which the embedding applies.

## Main declarations

* `TauCeti.Wkp.scaledNormSum`: the diameter-weighted Sobolev sum
  `∑_{j ≤ k} D ^ (j - n / p) * |u|_{j,p}`.
* `TauCeti.Wkp.continuousRepresentativeL`: the bounded linear embedding
  `W^{k,p}(Ω) →L[ℝ] (closure Ω →ᵇ ℝ)`.
* `TauCeti.Wkp.norm_continuousRepresentativeL_apply_le`: the diameter-weighted supremum bound with
  constant depending only on `dim E, k, p, γ`, and `μ(B(0, 1))`.
* `TauCeti.Wkp.evalClosureL`, `TauCeti.Wkp.evalL`: bounded point evaluation functionals on
  `closure Ω` and on `Ω`, with explicit bounds `abs_evalClosureL_le` and `abs_evalL_le`.
* `TauCeti.Wkp.exists_continuousOn_closure_ae_eq_of_forall_starConvex`: existential form of the
  embedding and diameter-weighted bound.
* `TauCeti.Wkp.exists_value_ae_eq_fullContractL_iteratedGradient`,
  `TauCeti.Wkp.exists_continuousRepresentative_fullContractL_of_forall_starConvex`,
  `TauCeti.Wkp.exists_continuousOn_closure_fullContractL_of_forall_starConvex`: Sobolev membership
  and continuity up to the boundary for directional derivative components.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Chapter 4, Lemmas 4.3.1 and 4.3.4.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12.
-/

public section

noncomputable section

open Bornology Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-! ### Diameter-weighted Sobolev sum -/

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diameter-weighted Sobolev sum `∑_{j ≤ k} D ^ (j - n / p) * |u|_{j,p}` on `W^{k,p}(Ω)`,
defined recursively via `TauCeti.Wkp.lowerOrder` and `TauCeti.Wkp.iteratedGradient`.
At `p = ∞`, `p.toReal = 0`, so `n / p.toReal = 0` and the weight at order `j` is `D ^ j`. -/
def scaledNormSum (D : ℝ) : (k : ℕ) → Wkp mu Omega p k → ℝ
  | 0, u => D ^ (-(finrank ℝ E : ℝ) / p.toReal) * ‖value 0 u‖
  | k + 1, u =>
      scaledNormSum D k (lowerOrder k u) +
        D ^ (((k + 1 : ℕ) : ℝ) - finrank ℝ E / p.toReal) * ‖iteratedGradient k u‖

@[simp]
theorem scaledNormSum_zero (D : ℝ) (u : Wkp mu Omega p 0) :
    scaledNormSum D 0 u = D ^ (-(finrank ℝ E : ℝ) / p.toReal) * ‖value 0 u‖ :=
  (rfl)

@[simp]
theorem scaledNormSum_succ (D : ℝ) (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    scaledNormSum D (k + 1) u =
      scaledNormSum D k (lowerOrder k u) +
        D ^ (((k + 1 : ℕ) : ℝ) - finrank ℝ E / p.toReal) * ‖iteratedGradient k u‖ :=
  (rfl)

/-- The diameter-weighted Sobolev sum is nonnegative whenever `0 ≤ D`. -/
theorem scaledNormSum_nonneg {D : ℝ} (hD : 0 ≤ D) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k), 0 ≤ scaledNormSum D k u
  | 0, u => mul_nonneg (Real.rpow_nonneg hD _) (norm_nonneg (value 0 u))
  | k + 1, u => add_nonneg (scaledNormSum_nonneg hD k (lowerOrder k u))
      (mul_nonneg (Real.rpow_nonneg hD _) (norm_nonneg (iteratedGradient k u)))

@[simp]
theorem scaledNormSum_zero_apply (D : ℝ) :
    ∀ k : ℕ, scaledNormSum (mu := mu) (Omega := Omega) (p := p) D k 0 = 0
  | 0 => by simp [scaledNormSum_zero]
  | k + 1 => by
      rw [scaledNormSum_succ, ← lowerOrderL_apply, ← iteratedGradientL_apply, map_zero, map_zero,
        scaledNormSum_zero_apply D k, norm_zero, mul_zero, add_zero]

/-- Subadditivity of `TauCeti.Wkp.scaledNormSum`. -/
theorem scaledNormSum_add_le {D : ℝ} (hD : 0 ≤ D) :
    ∀ (k : ℕ) (u v : Wkp mu Omega p k),
      scaledNormSum D k (u + v) ≤ scaledNormSum D k u + scaledNormSum D k v
  | 0, u, v => by
      rw [scaledNormSum_zero, scaledNormSum_zero, scaledNormSum_zero, value_add, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.rpow_nonneg hD _)
  | k + 1, u, v => by
      rw [scaledNormSum_succ, scaledNormSum_succ, scaledNormSum_succ,
        ← lowerOrderL_apply k (u + v), ← iteratedGradientL_apply k (u + v),
        map_add, map_add, lowerOrderL_apply, lowerOrderL_apply,
        iteratedGradientL_apply, iteratedGradientL_apply]
      have h1 := scaledNormSum_add_le hD k (lowerOrder k u) (lowerOrder k v)
      have h2 := mul_le_mul_of_nonneg_left (norm_add_le (iteratedGradient k u)
        (iteratedGradient k v)) (Real.rpow_nonneg hD (((k + 1 : ℕ) : ℝ) - finrank ℝ E / p.toReal))
      linarith

/-- Positive homogeneity of `TauCeti.Wkp.scaledNormSum`. -/
theorem scaledNormSum_smul (D : ℝ) (c : ℝ) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k), scaledNormSum D k (c • u) = |c| * scaledNormSum D k u
  | 0, u => by
      rw [scaledNormSum_zero, scaledNormSum_zero, value_smul, norm_smul, Real.norm_eq_abs]
      ring
  | k + 1, u => by
      rw [scaledNormSum_succ, scaledNormSum_succ, ← lowerOrderL_apply, ← iteratedGradientL_apply,
        map_smul, map_smul, lowerOrderL_apply, iteratedGradientL_apply, scaledNormSum_smul D c k,
        norm_smul, Real.norm_eq_abs]
      ring

/-- Continuity of `TauCeti.Wkp.scaledNormSum` on `W^{k,p}(Ω)`. -/
theorem continuous_scaledNormSum (D : ℝ) :
    ∀ k : ℕ, Continuous (scaledNormSum (mu := mu) (Omega := Omega) (p := p) D k)
  | 0 => by
      have heq : scaledNormSum (mu := mu) (Omega := Omega) (p := p) D 0 =
          fun u => D ^ (-(finrank ℝ E : ℝ) / p.toReal) * ‖valueL 0 u‖ := by
        ext u; rw [scaledNormSum_zero, valueL_apply]
      rw [heq]
      exact continuous_const.mul ((valueL (mu := mu) (Omega := Omega) (p := p) 0).continuous.norm)
  | k + 1 => by
      have heq : scaledNormSum (mu := mu) (Omega := Omega) (p := p) D (k + 1) =
          fun u => scaledNormSum D k (lowerOrderL k u) +
            D ^ (((k + 1 : ℕ) : ℝ) - finrank ℝ E / p.toReal) * ‖iteratedGradientL k u‖ := by
        ext u; rw [scaledNormSum_succ, lowerOrderL_apply, iteratedGradientL_apply]
      rw [heq]
      exact ((continuous_scaledNormSum D k).comp
          (lowerOrderL (mu := mu) (Omega := Omega) (p := p) k).continuous).add
        (continuous_const.mul
          ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) k).continuous.norm))

/-- `TauCeti.Wkp.scaledNormSum` is controlled by a constant multiple of the `W^{k,p}` norm. -/
theorem scaledNormSum_le_sum_mul_norm {D : ℝ} (hD : 0 ≤ D) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k),
      scaledNormSum D k u ≤
        (∑ j ∈ Finset.range (k + 1), D ^ ((j : ℝ) - finrank ℝ E / p.toReal)) * ‖u‖
  | 0, u => by
      rw [scaledNormSum_zero, Finset.sum_range_one, value_zero]
      simp only [Nat.cast_zero, zero_sub, neg_div, le_refl]
  | k + 1, u => by
      rw [scaledNormSum_succ, Finset.sum_range_succ, add_mul]
      refine add_le_add ?_ ?_
      · exact (scaledNormSum_le_sum_mul_norm hD k (lowerOrder k u)).trans
          (mul_le_mul_of_nonneg_left (norm_lowerOrder_le k u)
            (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg hD _))
      · exact mul_le_mul_of_nonneg_left (norm_iteratedGradient_le k u) (Real.rpow_nonneg hD _)

/-- On a `Cᵏ` representative, `TauCeti.Wkp.scaledNormSum` is the sum of the weighted classical
`Lᵖ` derivative seminorms. -/
theorem scaledNormSum_eq_sum_lpNorm_of_contDiffOn (D : ℝ) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k) {f : E → ℝ}, ContDiffOn ℝ k f Omega →
      (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f →
      scaledNormSum D k u = ∑ j ∈ Finset.range (k + 1),
        D ^ ((j : ℝ) - finrank ℝ E / p.toReal) * lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)
  | 0, u, f, hf, hu => by
      rw [scaledNormSum_zero, Finset.sum_range_one]
      simp only [Nat.cast_zero, zero_sub, neg_div]
      congr 1
      rw [Lp.norm_def, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen (by simp)).aestronglyMeasurable
          Omega.isOpen.measurableSet) ?_
      filter_upwards [hu] with x hx
      rw [hx, norm_iteratedFDeriv_zero]
  | k + 1, u, f, hf, hu => by
      rw [scaledNormSum_succ, Finset.sum_range_succ,
        scaledNormSum_eq_sum_lpNorm_of_contDiffOn D k (lowerOrder k u)
          (hf.of_le (by exact_mod_cast Nat.le_succ k)) (by simpa only [value_succ] using hu),
        norm_iteratedGradient_eq_lpNorm_of_contDiffOn k u hf hu]

/-- In dimension zero (`Subsingleton E`), `scaledNormSum 0 k u` bounds `‖value k u‖`. -/
private theorem norm_value_le_scaledNormSum_zero [Subsingleton E] :
    ∀ (k : ℕ) (u : Wkp mu Omega p k), ‖value k u‖ ≤ scaledNormSum 0 k u
  | 0, u => by
      simp [scaledNormSum_zero, finrank_zero_of_subsingleton]
  | k + 1, u => by
      rw [scaledNormSum_succ, value_succ]
      exact (norm_value_le_scaledNormSum_zero k (lowerOrder k u)).trans
        (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg le_rfl _) (norm_nonneg _)))

omit [BorelSpace E] in
/-- Single-term diameter-cancellation bound when lowering the `Lᵖ` exponent from `q` to `r` on a
domain with `μ(Ω) ≤ μ(B(0, 1)) * D ^ n`. -/
private theorem rpow_mul_norm_ofExponentLEL_le [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {r q : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ q)]
    (hrq : r ≤ q) {D : ℝ} (hD : 0 < D)
    (hmu : mu Omega ≤ ENNReal.ofReal (mu.real (ball (0 : E) 1) * D ^ finrank ℝ E))
    (j : ℝ) (f : Lp F q (mu.restrict Omega)) :
    D ^ (j - finrank ℝ E / r.toReal) * ‖Lp.ofExponentLEL ℝ F hrq f‖ ≤
      mu.real (ball (0 : E) 1) ^ (1 / r.toReal - 1 / q.toReal) *
        (D ^ (j - finrank ℝ E / q.toReal) * ‖f‖) := by
  set vB := mu.real (ball (0 : E) 1)
  set n := finrank ℝ E
  set δ := 1 / r.toReal - 1 / q.toReal
  have hvB : 0 < vB := Metric.measureReal_ball_pos mu 0 one_pos
  have hδ : 0 ≤ δ := by
    rcases eq_or_ne q ⊤ with rfl | hq
    · simp [δ]
    · have hr : r ≠ ⊤ := (lt_of_le_of_lt hrq (lt_top_iff_ne_top.2 hq)).ne
      have hr_pos : 0 < r.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hr
      exact sub_nonneg.2 (one_div_le_one_div_of_le hr_pos (ENNReal.toReal_mono hq hrq))
  have hvol : (mu Omega ^ δ).toReal ≤ vB ^ δ * D ^ ((n : ℝ) * δ) := by
    have h1 : mu Omega ^ δ ≤ ENNReal.ofReal (vB * D ^ n) ^ δ := ENNReal.rpow_le_rpow hmu hδ
    have h2 := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hδ ENNReal.ofReal_ne_top) h1
    rw [ENNReal.ofReal_rpow_of_pos (mul_pos hvB (pow_pos hD _)),
      ENNReal.toReal_ofReal (by positivity), Real.mul_rpow hvB.le (pow_nonneg hD.le _),
      ← Real.rpow_natCast D n, ← Real.rpow_mul hD.le] at h2
    exact h2
  have hLp := Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hrq f
  rw [Measure.restrict_apply_univ] at hLp
  calc D ^ (j - n / r.toReal) * ‖Lp.ofExponentLEL ℝ F hrq f‖
      ≤ D ^ (j - n / r.toReal) * ((mu Omega ^ δ).toReal * ‖f‖) :=
        mul_le_mul_of_nonneg_left hLp (Real.rpow_nonneg hD.le _)
    _ ≤ D ^ (j - n / r.toReal) * (vB ^ δ * D ^ ((n : ℝ) * δ) * ‖f‖) := by gcongr
    _ = vB ^ δ * (D ^ (j - n / r.toReal) * D ^ ((n : ℝ) * δ)) * ‖f‖ := by ring
    _ = vB ^ δ * (D ^ (j - n / q.toReal) * ‖f‖) := by
        rw [← Real.rpow_add hD, mul_assoc]
        congr 3
        simp only [δ]
        ring

/-- Lowering the integrability exponent on a domain with `μ(Ω) ≤ μ(B(0, 1)) * D ^ n` multiplies
`TauCeti.Wkp.scaledNormSum D` by at most `μ(B(0, 1)) ^ (1 / r - 1 / q)`, with the powers of `D`
cancelling identically. -/
theorem scaledNormSum_ofExponentLEL_le [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    {r q : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ q)] (hrq : r ≤ q) {D : ℝ} (hD : 0 < D)
    (hmu : mu Omega ≤ ENNReal.ofReal (mu.real (ball (0 : E) 1) * D ^ finrank ℝ E)) :
    ∀ (k : ℕ) (u : Wkp mu Omega q k),
      scaledNormSum D k (ofExponentLEL hrq k u) ≤
        mu.real (ball (0 : E) 1) ^ (1 / r.toReal - 1 / q.toReal) * scaledNormSum D k u
  | 0, u => by
      rw [scaledNormSum_zero, scaledNormSum_zero, value_ofExponentLEL]
      simpa only [zero_sub, neg_div] using rpow_mul_norm_ofExponentLEL_le hrq hD hmu 0 (value 0 u)
  | k + 1, u => by
      rw [scaledNormSum_succ, scaledNormSum_succ, lowerOrder_ofExponentLEL,
        iteratedGradient_ofExponentLEL, mul_add]
      exact add_le_add (scaledNormSum_ofExponentLEL_le hrq hD hmu k (lowerOrder k u))
        (rpow_mul_norm_ofExponentLEL_le hrq hD hmu ((k + 1 : ℕ) : ℝ) (iteratedGradient k u))

/-! ### Continuous representatives up to the boundary on star-shaped domains -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Extend a bounded continuous function on `closure Ω` by zero off `closure Ω`, preserving
continuity on `closure Ω` and uniform continuity on `Ω`. -/
private theorem exists_extend_of_boundedContinuousFunction (hΩ : IsBounded (Omega : Set E))
    (g : closure (Omega : Set E) →ᵇ ℝ) :
    ∃ f : E → ℝ, ContinuousOn f (closure (Omega : Set E)) ∧ UniformContinuousOn f Omega ∧
      ∀ x (hx : x ∈ closure (Omega : Set E)), f x = g ⟨x, hx⟩ := by
  classical
  let f : E → ℝ := fun x => if hx : x ∈ closure (Omega : Set E) then g ⟨x, hx⟩ else 0
  have hfeq : ∀ x (hx : x ∈ closure (Omega : Set E)), f x = g ⟨x, hx⟩ := fun x hx =>
    dite_eq_left hx
  have hf_cont : ContinuousOn f (closure (Omega : Set E)) :=
    continuousOn_iff_continuous_domRestrict.2 (g.continuous.congr fun x => (hfeq x.1 x.2).symm)
  exact ⟨f, hf_cont, (hΩ.isCompact_closure.uniformContinuousOn_of_continuous hf_cont).mono
    subset_closure, hfeq⟩

/-- For a globally smooth representative of `u ∈ W^{k,p}(Ω)` (`p < ∞`), restriction to `closure Ω`
satisfies the diameter-weighted supremum bound. -/
private theorem norm_mkOfCompact_le_of_contDiff (hΩ : IsBounded (Omega : Set E)) {x₀ : E}
    {ρ γ : ℝ} (hρ : 0 < ρ) (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hγ : diam (Omega : Set E) ≤ γ * ρ) (hp : p ≠ ⊤) {k : ℕ}
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    have : CompactSpace (closure (Omega : Set E)) :=
      isCompact_iff_compactSpace.1 hΩ.isCompact_closure
    ‖BoundedContinuousFunction.mkOfCompact
        ⟨fun x : closure (Omega : Set E) => f x, hf.continuous.comp continuous_subtype_val⟩‖ ≤
      starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u := by
  have : CompactSpace (closure (Omega : Set E)) :=
    isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  set C := starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1))
  have hC : 0 ≤ C := starConvexSupConst_nonneg _ _ _ _ measureReal_nonneg
  have hS : 0 ≤ scaledNormSum (diam (Omega : Set E)) k u := scaledNormSum_nonneg diam_nonneg k u
  have hbound_Ω : ∀ x ∈ (Omega : Set E), |f x| ≤ C * scaledNormSum (diam (Omega : Set E)) k u := by
    intro x hx
    have hf' : ContDiffOn ℝ k f Omega := (hf.of_le (by simp)).contDiffOn
    have hmem := memLp_iteratedFDeriv_of_contDiffOn k u hf' hu
    have he := enorm_le_sum_eLpNorm_of_contDiffOn_of_forall_starConvex (μ := mu) Omega.isOpen hΩ
      hρ hstar hγ hp hkp hf' hx
    have hfin : ENNReal.ofReal C * ∑ j ∈ Finset.range (k + 1),
        ENNReal.ofReal (diam (Omega : Set E) ^ ((j : ℝ) - finrank ℝ E / p.toReal)) *
          eLpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun j hj => ?_)
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (hmem j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).eLpNorm_ne_top
    have hreal := ENNReal.toReal_mono hfin he
    rw [toReal_eNorm, Real.norm_eq_abs, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ENNReal.toReal_sum fun j hj => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (hmem j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).eLpNorm_ne_top] at hreal
    refine hreal.trans_eq ?_
    rw [scaledNormSum_eq_sum_lpNorm_of_contDiffOn (diam (Omega : Set E)) k u hf' hu]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg diam_nonneg _), lpNorm]
  have hbound_cl : ∀ x ∈ closure (Omega : Set E),
      |f x| ≤ C * scaledNormSum (diam (Omega : Set E)) k u :=
    closure_minimal (s := (Omega : Set E))
      (t := {x | |f x| ≤ C * scaledNormSum (diam (Omega : Set E)) k u})
      hbound_Ω (isClosed_le hf.continuous.abs continuous_const)
  exact (BoundedContinuousFunction.norm_le (mul_nonneg hC hS)).2 fun x =>
    by simpa only [Real.norm_eq_abs, BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk] using hbound_cl x.1 x.2

/-- If `seq m → u` in `W^{k,p}(Ω)` and continuous representatives `fseq m` of `seq m` converge
uniformly on `closure Ω` to `g`, then `g` agrees almost everywhere on `Ω` with `value k u`. -/
private theorem ae_eq_value_of_tendsto_contDiff (hΩ : IsBounded (Omega : Set E)) {k : ℕ}
    {u : Wkp mu Omega p k} {seq : ℕ → Wkp mu Omega p k} (hseq : Tendsto seq atTop (𝓝 u))
    {fseq : ℕ → E → ℝ} (hfseq : ∀ m, Continuous (fseq m))
    (hvseq : ∀ m, (value k (seq m) : E → ℝ) =ᵐ[mu.restrict Omega] fseq m)
    {g : closure (Omega : Set E) →ᵇ ℝ}
    (hg : Tendsto (fun m =>
      have : CompactSpace (closure (Omega : Set E)) :=
        isCompact_iff_compactSpace.1 hΩ.isCompact_closure
      BoundedContinuousFunction.mkOfCompact
        ⟨fun x : closure (Omega : Set E) => fseq m x, (hfseq m).comp continuous_subtype_val⟩)
      atTop (𝓝 g)) :
    ∀ᵐ x ∂mu, ∀ hx : x ∈ Omega, g ⟨x, subset_closure hx⟩ = value k u x := by
  have : CompactSpace (closure (Omega : Set E)) :=
    isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  let gseq : ℕ → closure (Omega : Set E) →ᵇ ℝ := fun m =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x : closure (Omega : Set E) => fseq m x, (hfseq m).comp continuous_subtype_val⟩
  obtain ⟨g', hg'_cont, _, hg'_eq⟩ := exists_extend_of_boundedContinuousFunction hΩ g
  have hg'_meas : AEStronglyMeasurable g' (mu.restrict Omega) :=
    (hg'_cont.mono subset_closure).aestronglyMeasurable Omega.isOpen.measurableSet
  have hmu_fin : mu Omega ≠ ⊤ := by
    obtain ⟨R, hR⟩ := hΩ.subset_closedBall (0 : E)
    exact ((measure_mono hR).trans_lt measure_closedBall_lt_top).ne
  have hlp_zero : eLpNorm (g' - (value k u : E → ℝ)) p (mu.restrict Omega) = 0 := by
    refine le_antisymm ?_ zero_le
    have hbound : ∀ m, eLpNorm (g' - (value k u : E → ℝ)) p (mu.restrict Omega) ≤
        ENNReal.ofReal ‖gseq m - g‖ * mu Omega ^ (1 / p.toReal) +
          eLpNorm (fseq m - (value k u : E → ℝ)) p (mu.restrict Omega) := by
      intro m
      have hsplit : g' - (value k u : E → ℝ) = (g' - fseq m) + (fseq m - (value k u : E → ℝ)) := by
        ext x; simp
      have hae : ∀ᵐ x ∂mu.restrict Omega, ‖(g' - fseq m) x‖ ≤ ‖gseq m - g‖ := by
        filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hxΩ
        rw [Pi.sub_apply, hg'_eq x (subset_closure hxΩ), norm_sub_rev]
        exact (gseq m - g).norm_coe_le_norm ⟨x, subset_closure hxΩ⟩
      have h1 : eLpNorm (g' - fseq m) p (mu.restrict Omega) ≤
          ENNReal.ofReal ‖gseq m - g‖ * mu Omega ^ (1 / p.toReal) := by
        refine (eLpNorm_le_of_ae_bound
          (hg'_meas.sub (hfseq m).aestronglyMeasurable) hae).trans_eq ?_
        rw [Measure.restrict_apply_univ, mul_comm, one_div]
      rw [hsplit]
      exact (eLpNorm_add_le Fact.out).trans (by gcongr)
    have ht1 : Tendsto (fun m => ENNReal.ofReal ‖gseq m - g‖ * mu Omega ^ (1 / p.toReal))
        atTop (𝓝 0) := by
      have hgn : Tendsto (fun m => ENNReal.ofReal ‖gseq m - g‖) atTop (𝓝 0) := by
        simpa [dist_eq_norm] using ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.1 hg)
      simpa using ENNReal.Tendsto.mul_const hgn
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity) hmu_fin))
    have ht := ht1.add (tendsto_eLpNorm_sub_of_tendsto hseq hvseq .rfl)
    rw [add_zero] at ht
    exact ge_of_tendsto ht (Eventually.of_forall hbound)
  have hae_sub : (g' - (value k u : E → ℝ)) =ᵐ[mu.restrict Omega] 0 :=
    (eLpNorm_eq_zero_iff (zero_lt_one.trans_le Fact.out).ne').1 hlp_zero
  rw [EventuallyEq, ae_restrict_iff' Omega.isOpen.measurableSet] at hae_sub
  filter_upwards [hae_sub] with x hx hxΩ
  rw [← hg'_eq x (subset_closure hxΩ)]
  exact sub_eq_zero.1 (hx hxΩ)

/-- Existence of a bounded continuous representative on `closure Ω` satisfying the diameter-weighted
supremum bound, for finite exponents `1 ≤ p < ∞`. -/
private theorem exists_continuousRepresentative_le_of_ne_top (hΩ : IsBounded (Omega : Set E))
    {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hγ : diam (Omega : Set E) ≤ γ * ρ) (hp : p ≠ ⊤) {k : ℕ}
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (u : Wkp mu Omega p k) :
    ∃ g : closure (Omega : Set E) →ᵇ ℝ,
      (∀ᵐ x ∂mu, ∀ hx : x ∈ Omega, g ⟨x, subset_closure hx⟩ = value k u x) ∧
      ‖g‖ ≤ starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u := by
  have : CompactSpace (closure (Omega : Set E)) :=
    isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  set C := starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1))
  have hC : 0 ≤ C := starConvexSupConst_nonneg _ _ _ _ measureReal_nonneg
  -- Approximate `u` in `W^{k,p}(Ω)` by globally smooth functions on `E`.
  have hdense := dense_contDiff_representatives_of_forall_starConvex (mu := mu) (Omega := Omega)
    hp k hρ hstar
  have hex : ∀ m : ℕ, ∃ v : Wkp mu Omega p k, ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
      (value k v : E → ℝ) =ᵐ[mu.restrict Omega] f ∧ dist v u < 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨v, ⟨f, hf, hvf⟩, hdist⟩ := Metric.mem_closure_iff.1 (hdense u) (1 / ((m : ℝ) + 1))
      (by positivity)
    exact ⟨v, f, hf, hvf, by rwa [dist_comm]⟩
  choose seq fseq hfseq hvseq hdist using hex
  have hseq_tendsto : Tendsto seq atTop (𝓝 u) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun m => (hdist m).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  -- The classical supremum estimate makes the smooth approximants Cauchy in `closure Ω →ᵇ ℝ`.
  let gseq : ℕ → closure (Omega : Set E) →ᵇ ℝ := fun m =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x : closure (Omega : Set E) => fseq m x,
        (hfseq m).continuous.comp continuous_subtype_val⟩
  have hg_bound : ∀ m, ‖gseq m‖ ≤ C * scaledNormSum (diam (Omega : Set E)) k (seq m) := fun m =>
    norm_mkOfCompact_le_of_contDiff hΩ hρ hstar hγ hp hkp (seq m) (hfseq m) (hvseq m)
  have hg_sub : ∀ m l, ‖gseq m - gseq l‖ ≤
      C * (∑ j ∈ Finset.range (k + 1),
        diam (Omega : Set E) ^ ((j : ℝ) - finrank ℝ E / p.toReal)) * ‖seq m - seq l‖ := by
    intro m l
    have hrep : (value k (seq m - seq l) : E → ℝ) =ᵐ[mu.restrict Omega] fseq m - fseq l := by
      rw [value_sub]
      filter_upwards [Lp.coeFn_sub (value k (seq m)) (value k (seq l)), hvseq m, hvseq l]
        with x h1 h2 h3
      simp only [h1, Pi.sub_apply, h2, h3]
    refine (norm_mkOfCompact_le_of_contDiff hΩ hρ hstar hγ hp hkp (seq m - seq l)
      ((hfseq m).sub (hfseq l)) hrep).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (scaledNormSum_le_sum_mul_norm diam_nonneg k _) hC
  have hcauchy : CauchySeq gseq := by
    set M := C * ∑ j ∈ Finset.range (k + 1),
      diam (Omega : Set E) ^ ((j : ℝ) - finrank ℝ E / p.toReal)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hseq_tendsto.cauchySeq (ε / (M + 1)) (by positivity)
    refine ⟨N, fun m hm l hl => ?_⟩
    rw [dist_eq_norm]
    calc ‖gseq m - gseq l‖ ≤ M * ‖seq m - seq l‖ := hg_sub m l
      _ ≤ (M + 1) * dist (seq m) (seq l) := by
          rw [dist_eq_norm]
          exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left (hN m hm l hl) (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  -- Pass to the uniform limit `g` and transfer both a.e. equality and the supremum bound.
  obtain ⟨g, hg_tendsto⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨g, ae_eq_value_of_tendsto_contDiff hΩ hseq_tendsto (fun m => (hfseq m).continuous)
    hvseq hg_tendsto, ?_⟩
  exact le_of_tendsto_of_tendsto hg_tendsto.norm
    (((continuous_scaledNormSum (diam (Omega : Set E)) k).tendsto u |>.comp
      hseq_tendsto).const_mul C) (Eventually.of_forall hg_bound)

/-- Zero-dimensional case of `exists_continuousRepresentative_le_top`. -/
private theorem exists_continuousRepresentative_le_top_subsingleton [Subsingleton E]
    (hΩne : (Omega : Set E).Nonempty) (γ : ℝ) (k : ℕ) (u : Wkp mu Omega ⊤ k) :
    ∃ g : closure (Omega : Set E) →ᵇ ℝ,
      (∀ᵐ x ∂mu, ∀ hx : x ∈ Omega, g ⟨x, subset_closure hx⟩ = value k u x) ∧
      ‖g‖ ≤ starConvexSupConst (finrank ℝ E) k ⊤ γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u := by
  refine ⟨BoundedContinuousFunction.const _ ((value k u : E → ℝ) 0),
    .of_forall fun x _ => by simp [Subsingleton.elim x 0], ?_⟩
  have hC : starConvexSupConst (finrank ℝ E) k ⊤ γ (mu.real (ball 0 1)) = 1 := by
    rw [finrank_zero_of_subsingleton, starConvexSupConst_zero_top]
  have hD : diam (Omega : Set E) = 0 := diam_subsingleton Set.subsingleton_of_subsingleton
  rw [hC, one_mul, hD]
  have hμ0 : mu.restrict (Omega : Set E) ≠ 0 := by
    intro h0
    have hpos : 0 < mu Omega := Omega.isOpen.measure_pos mu hΩne
    have : mu Omega = 0 := by
      rw [← Measure.restrict_apply_univ, h0, FunLike.coe_zero, Pi.zero_apply]
    exact hpos.ne' this
  have hval : |(value k u : E → ℝ) 0| = ‖value k u‖ := by
    rw [Lp.norm_def, eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        aestronglyMeasurable_const (.of_forall fun y => by rw [Subsingleton.elim y 0]),
      eLpNorm_const ((value k u : E → ℝ) 0) ENNReal.top_ne_zero hμ0]
    simp [Real.norm_eq_abs]
  refine (BoundedContinuousFunction.norm_const_le _).trans ?_
  rw [Real.norm_eq_abs, hval]
  exact norm_value_le_scaledNormSum_zero k u

/-- Existence of a bounded continuous representative on `closure Ω` satisfying the diameter-weighted
supremum bound, for `p = ∞`. -/
private theorem exists_continuousRepresentative_le_top (hΩ : IsBounded (Omega : Set E))
    {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hγ : diam (Omega : Set E) ≤ γ * ρ) {k : ℕ}
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * (⊤ : ℝ≥0∞) ∨ ((⊤ : ℝ≥0∞) = 1 ∧ finrank ℝ E ≤ k))
    (u : Wkp mu Omega ⊤ k) :
    ∃ g : closure (Omega : Set E) →ᵇ ℝ,
      (∀ᵐ x ∂mu, ∀ hx : x ∈ Omega, g ⟨x, subset_closure hx⟩ = value k u x) ∧
      ‖g‖ ≤ starConvexSupConst (finrank ℝ E) k ⊤ γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u := by
  rcases (Omega : Set E).eq_empty_or_nonempty with hempty | ⟨x₁, hx₁⟩
  · refine ⟨0, .of_forall fun _ hx => False.elim (hempty.subset hx), ?_⟩
    rw [norm_zero]
    exact mul_nonneg (starConvexSupConst_nonneg _ _ _ _ measureReal_nonneg)
      (scaledNormSum_nonneg diam_nonneg k u)
  rcases subsingleton_or_nontrivial E with _ | _
  · exact exists_continuousRepresentative_le_top_subsingleton ⟨x₁, hx₁⟩ γ k u
  -- In positive dimension, lower the exponent from `∞` to `r = n + 1` so `k * r > n`.
  set n := finrank ℝ E
  have hn0 : n ≠ 0 := finrank_pos.ne'
  have hk : 1 ≤ k := by
    rcases hkp with h | ⟨h1, _⟩
    · by_contra hk0
      have : k = 0 := by omega
      simp [this] at h
    · exact absurd h1 ENNReal.top_ne_one
  have hΩD : (Omega : Set E) ⊆ closedBall x₁ (diam (Omega : Set E)) := fun z hz =>
    mem_closedBall.2 (dist_le_diam_of_mem hΩ hz hx₁)
  have hBΩ : ball x₀ ρ ⊆ (Omega : Set E) := fun _ hy => (hstar _ hy).mem ⟨x₁, hx₁⟩
  have hD : 0 < diam (Omega : Set E) :=
    lt_of_lt_of_le (by linarith : 0 < 2 * ρ) (Metric.diam_ball_eq x₀ hρ.le ▸ diam_mono hBΩ hΩ)
  have hmu : mu Omega ≤ ENNReal.ofReal (mu.real (ball (0 : E) 1) * diam (Omega : Set E) ^ n) := by
    refine (measure_mono hΩD).trans_eq ?_
    rw [Measure.addHaar_closedBall mu x₁ hD.le, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ENNReal.ofReal_mul (pow_nonneg hD.le _), mul_comm]
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) :=
    isFiniteMeasure_restrict.2 (hmu.trans_lt ENNReal.ofReal_lt_top).ne
  let r : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)
  have : Fact (1 ≤ r) := ⟨by dsimp only [r]; exact_mod_cast Nat.succ_pos n⟩
  have hr_top : r ≠ ⊤ := ENNReal.natCast_ne_top _
  have hkr : (n : ℝ≥0∞) < k * r := by
    have hlt : n < k * (n + 1) := lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_mul_of_pos_left _ hk)
    dsimp only [r]
    exact_mod_cast hlt
  let v := ofExponentLEL (le_top : r ≤ ⊤) k u
  obtain ⟨g, hgv, hg_norm⟩ := exists_continuousRepresentative_le_of_ne_top hΩ hρ hstar hγ hr_top
    (Or.inl hkr) v
  refine ⟨g, ?_, ?_⟩
  · have hv_ae := (ae_restrict_iff' Omega.isOpen.measurableSet).1
      (value_ofExponentLEL_ae (le_top : r ≤ ⊤) k u)
    filter_upwards [hgv, hv_ae] with x h1 h2 hx
    exact (h1 hx).trans (h2 hx)
  · have hscale := scaledNormSum_ofExponentLEL_le (le_top : r ≤ ⊤) hD hmu k u
    have hC_nn : 0 ≤ starConvexSupConst n k r γ (mu.real (ball 0 1)) :=
      starConvexSupConst_nonneg _ _ _ _ measureReal_nonneg
    calc ‖g‖ ≤ starConvexSupConst n k r γ (mu.real (ball 0 1)) *
          scaledNormSum (diam (Omega : Set E)) k v := hg_norm
      _ ≤ starConvexSupConst n k r γ (mu.real (ball 0 1)) *
          (mu.real (ball (0 : E) 1) ^ (1 / r.toReal - 1 / (⊤ : ℝ≥0∞).toReal) *
            scaledNormSum (diam (Omega : Set E)) k u) :=
          mul_le_mul_of_nonneg_left hscale hC_nn
      _ = starConvexSupConst n k ⊤ γ (mu.real (ball 0 1)) *
          scaledNormSum (diam (Omega : Set E)) k u := by
          rw [starConvexSupConst_top_of_ne_zero hn0]
          simp only [r, ENNReal.toReal_natCast, ENNReal.toReal_top, div_zero, sub_zero]
          ring

/-- Existence of a bounded continuous representative on `closure Ω` satisfying the diameter-weighted
supremum bound, for all exponents `1 ≤ p ≤ ∞`. -/
private theorem exists_continuousRepresentative_le (hΩ : IsBounded (Omega : Set E))
    {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hγ : diam (Omega : Set E) ≤ γ * ρ) {k : ℕ}
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (u : Wkp mu Omega p k) :
    ∃ g : closure (Omega : Set E) →ᵇ ℝ,
      (∀ᵐ x ∂mu, ∀ hx : x ∈ Omega, g ⟨x, subset_closure hx⟩ = value k u x) ∧
      ‖g‖ ≤ starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u := by
  by_cases hp : p = ⊤
  · subst hp
    exact exists_continuousRepresentative_le_top hΩ hρ hstar hγ hkp u
  · exact exists_continuousRepresentative_le_of_ne_top hΩ hρ hstar hγ hp hkp u

section ContinuousRepresentative

variable {k : ℕ}

/-- **Continuous representative operator on a bounded star-shaped domain.** Under the supercritical
condition `dim E < k * p` or `p = 1 ∧ dim E ≤ k`, every `u ∈ W^{k,p}(Ω)` admits a unique bounded
continuous representative on `closure Ω`, depending linearly and continuously on `u`. -/
def continuousRepresentativeL (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k)) :
    Wkp mu Omega p k →L[ℝ] (closure (Omega : Set E) →ᵇ ℝ) :=
  have hγ : diam (Omega : Set E) ≤
      (diam (Omega : Set E) / hstar.choose_spec.choose) * hstar.choose_spec.choose := by
    rw [div_mul_cancel₀ _ hstar.choose_spec.choose_spec.1.ne']
  let rep : Wkp mu Omega p k → (closure (Omega : Set E) →ᵇ ℝ) := fun u =>
    (exists_continuousRepresentative_le hΩ hstar.choose_spec.choose_spec.1
      hstar.choose_spec.choose_spec.2 hγ hkp u).choose
  have hrep_ae : ∀ u, ∀ᵐ x ∂mu, ∀ hx : x ∈ Omega,
      rep u ⟨x, subset_closure hx⟩ = value k u x := fun u =>
    (exists_continuousRepresentative_le hΩ hstar.choose_spec.choose_spec.1
      hstar.choose_spec.choose_spec.2 hγ hkp u).choose_spec.1
  have hrep_norm : ∀ u, ‖rep u‖ ≤
      starConvexSupConst (finrank ℝ E) k p (diam (Omega : Set E) / hstar.choose_spec.choose)
        (mu.real (ball 0 1)) * scaledNormSum (diam (Omega : Set E)) k u := fun u =>
    (exists_continuousRepresentative_le hΩ hstar.choose_spec.choose_spec.1
      hstar.choose_spec.choose_spec.2 hγ hkp u).choose_spec.2
  LinearMap.mkContinuousOfExistsBound
    { toFun := rep
      map_add' := fun u v => by
        refine BoundedContinuousFunction.ext (congrFun (Omega.isOpen.ext_closure_of_ae_eq (μ := mu)
          (rep (u + v)).continuous (rep u + rep v).continuous ?_))
        have hadd := (ae_restrict_iff' Omega.isOpen.measurableSet).1
          (Lp.coeFn_add (value k u) (value k v))
        filter_upwards [hrep_ae (u + v), hrep_ae u, hrep_ae v, hadd] with x h1 h2 h3 h4 hx
        rw [h1 hx, value_add, h4 hx, Pi.add_apply, add_apply, h2 hx, h3 hx]
      map_smul' := fun c u => by
        refine BoundedContinuousFunction.ext (congrFun (Omega.isOpen.ext_closure_of_ae_eq (μ := mu)
          (rep (c • u)).continuous (c • rep u).continuous ?_))
        have hsmul := (ae_restrict_iff' Omega.isOpen.measurableSet).1
          (Lp.coeFn_smul c (value k u))
        filter_upwards [hrep_ae (c • u), hrep_ae u, hsmul] with x h1 h2 h3 hx
        rw [h1 hx, value_smul, h3 hx, Pi.smul_apply, RingHom.id_apply, smul_apply, h2 hx] }
    ⟨starConvexSupConst (finrank ℝ E) k p (diam (Omega : Set E) / hstar.choose_spec.choose)
        (mu.real (ball 0 1)) *
      ∑ j ∈ Finset.range (k + 1),
        diam (Omega : Set E) ^ ((j : ℝ) - finrank ℝ E / p.toReal), fun u =>
      (hrep_norm u).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (scaledNormSum_le_sum_mul_norm diam_nonneg k u)
          (starConvexSupConst_nonneg _ _ _ _ measureReal_nonneg))⟩

/-- Almost everywhere on `Ω`, `TauCeti.Wkp.continuousRepresentativeL` agrees with
`TauCeti.Wkp.value`. -/
theorem continuousRepresentativeL_ae (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (u : Wkp mu Omega p k) :
    ∀ᵐ x ∂mu, ∀ hx : x ∈ Omega,
      continuousRepresentativeL hΩ hstar hkp u ⟨x, subset_closure hx⟩ = value k u x := by
  have hγ : diam (Omega : Set E) ≤
      (diam (Omega : Set E) / hstar.choose_spec.choose) * hstar.choose_spec.choose := by
    rw [div_mul_cancel₀ _ hstar.choose_spec.choose_spec.1.ne']
  dsimp only [continuousRepresentativeL]
  rw [LinearMap.mkContinuousOfExistsBound_apply]
  exact (exists_continuousRepresentative_le hΩ hstar.choose_spec.choose_spec.1
    hstar.choose_spec.choose_spec.2 hγ hkp u).choose_spec.1

/-- Any bounded continuous function on `closure Ω` that agrees almost everywhere on `Ω` with
`value k u` equals `TauCeti.Wkp.continuousRepresentativeL`. -/
theorem continuousRepresentativeL_eq_of_ae_eq (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    {u : Wkp mu Omega p k} {g : closure (Omega : Set E) →ᵇ ℝ}
    (hg : ∀ᵐ x ∂mu, ∀ hx : x ∈ Omega, g ⟨x, subset_closure hx⟩ = value k u x) :
    continuousRepresentativeL hΩ hstar hkp u = g := by
  refine BoundedContinuousFunction.ext (congrFun (Omega.isOpen.ext_closure_of_ae_eq (μ := mu)
    (continuousRepresentativeL hΩ hstar hkp u).continuous g.continuous ?_))
  filter_upwards [continuousRepresentativeL_ae hΩ hstar hkp u, hg] with x h1 h2 hx
  exact (h1 hx).trans (h2 hx).symm

/-- If `f : E → ℝ` is continuous on `closure Ω` and agrees almost everywhere on `Ω` with
`value k u`, then `TauCeti.Wkp.continuousRepresentativeL` agrees with `f` at every point of
`closure Ω`. -/
theorem continuousRepresentativeL_apply_of_continuousOn_closure (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    {u : Wkp mu Omega p k} {f : E → ℝ} (hf : ContinuousOn f (closure (Omega : Set E)))
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) (x : closure (Omega : Set E)) :
    continuousRepresentativeL hΩ hstar hkp u x = f x := by
  have : CompactSpace (closure (Omega : Set E)) :=
    isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  let g : closure (Omega : Set E) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun y => f y,
      continuousOn_iff_continuous_domRestrict.1 hf⟩
  have hg : continuousRepresentativeL hΩ hstar hkp u = g := by
    refine continuousRepresentativeL_eq_of_ae_eq hΩ hstar hkp ?_
    have hu' := (ae_restrict_iff' Omega.isOpen.measurableSet).1 hu
    filter_upwards [hu'] with y hy hyΩ
    exact (hy hyΩ).symm
  rw [hg]
  rfl

/-- **Diameter-weighted supremum bound for `W^{k,p}(Ω)` on bounded star-shaped domains.**
The constant `TauCeti.starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1))` depends only on
the dimension, order, exponent, chunkiness bound `γ`, and unit-ball measure. -/
theorem norm_continuousRepresentativeL_apply_le (hΩ : IsBounded (Omega : Set E)) {x₀ : E}
    {ρ γ : ℝ} (hρ : 0 < ρ) (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hγ : diam (Omega : Set E) ≤ γ * ρ)
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (u : Wkp mu Omega p k) :
    ‖continuousRepresentativeL hΩ ⟨x₀, ρ, hρ, hstar⟩ hkp u‖ ≤
      starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u := by
  obtain ⟨g, hg_ae, hg_norm⟩ := exists_continuousRepresentative_le hΩ hρ hstar hγ hkp u
  rwa [continuousRepresentativeL_eq_of_ae_eq hΩ ⟨x₀, ρ, hρ, hstar⟩ hkp hg_ae]

/-- The continuous representative on `closure Ω` is uniformly continuous on `closure Ω`. -/
theorem uniformContinuous_continuousRepresentativeL (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (u : Wkp mu Omega p k) :
    UniformContinuous (continuousRepresentativeL hΩ hstar hkp u) := by
  have : CompactSpace (closure (Omega : Set E)) :=
    isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  exact CompactSpace.uniformContinuous_of_continuous
    (continuousRepresentativeL hΩ hstar hkp u).continuous

/-- **Bounded point evaluation on `closure Ω`.** Evaluating the continuous representative of
`u ∈ W^{k,p}(Ω)` at any point `x ∈ closure Ω` is a continuous linear functional. -/
def evalClosureL (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (x : closure (Omega : Set E)) : Wkp mu Omega p k →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp (continuousRepresentativeL hΩ hstar hkp)

@[simp]
theorem evalClosureL_apply (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (x : closure (Omega : Set E)) (u : Wkp mu Omega p k) :
    evalClosureL hΩ hstar hkp x u = continuousRepresentativeL hΩ hstar hkp u x :=
  (rfl)

/-- Point evaluation at `x ∈ closure Ω` satisfies the diameter-weighted supremum bound. -/
theorem abs_evalClosureL_le (hΩ : IsBounded (Omega : Set E)) {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hγ : diam (Omega : Set E) ≤ γ * ρ)
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    (x : closure (Omega : Set E)) (u : Wkp mu Omega p k) :
    |evalClosureL hΩ ⟨x₀, ρ, hρ, hstar⟩ hkp x u| ≤
      starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u := by
  rw [evalClosureL_apply, ← Real.norm_eq_abs]
  exact ((continuousRepresentativeL hΩ ⟨x₀, ρ, hρ, hstar⟩ hkp u).norm_coe_le_norm x).trans
    (norm_continuousRepresentativeL_apply_le hΩ hρ hstar hγ hkp u)

/-- **Bounded point evaluation on `Ω`.** Evaluating the continuous representative of
`u ∈ W^{k,p}(Ω)` at an interior point `x ∈ Ω` is a continuous linear functional. -/
def evalL (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    {x : E} (hx : x ∈ Omega) : Wkp mu Omega p k →L[ℝ] ℝ :=
  evalClosureL hΩ hstar hkp ⟨x, subset_closure hx⟩

@[simp]
theorem evalL_apply (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    {x : E} (hx : x ∈ Omega) (u : Wkp mu Omega p k) :
    evalL hΩ hstar hkp hx u = continuousRepresentativeL hΩ hstar hkp u ⟨x, subset_closure hx⟩ :=
  (rfl)

/-- Point evaluation at an interior point `x ∈ Ω` satisfies the diameter-weighted supremum bound. -/
theorem abs_evalL_le (hΩ : IsBounded (Omega : Set E)) {x₀ : E} {ρ γ : ℝ} (hρ : 0 < ρ)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    (hγ : diam (Omega : Set E) ≤ γ * ρ)
    (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k))
    {x : E} (hx : x ∈ Omega) (u : Wkp mu Omega p k) :
    |evalL hΩ ⟨x₀, ρ, hρ, hstar⟩ hkp hx u| ≤
      starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1)) *
        scaledNormSum (diam (Omega : Set E)) k u :=
  abs_evalClosureL_le hΩ hρ hstar hγ hkp ⟨x, subset_closure hx⟩ u

end ContinuousRepresentative

/-- **`W^{k,p} ⊆ C⁰` on bounded star-shaped domains.** For `dim E < k * p` or `p = 1 ∧ dim E ≤ k`,
there is a nonnegative constant `C` depending only on `dim E, k, p, γ`, and `μ(B(0, 1))` such that
on every bounded open `Ω` star-convex with respect to `ball x₀ ρ` (`0 < ρ`, `diam Ω ≤ γ * ρ`),
every `u ∈ W^{k,p}(Ω)` has a representative continuous on `closure Ω`, uniformly continuous on `Ω`,
and bounded on `closure Ω` by `C * scaledNormSum (diam Ω) k u`. -/
theorem exists_continuousOn_closure_ae_eq_of_forall_starConvex (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (γ : ℝ) (hkp : (finrank ℝ E : ℝ≥0∞) < k * p ∨ (p = 1 ∧ finrank ℝ E ≤ k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Omega : Opens E) (x₀ : E) (ρ : ℝ),
      IsBounded (Omega : Set E) → 0 < ρ →
      (∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E)) →
      diam (Omega : Set E) ≤ γ * ρ →
      ∀ u : Wkp mu Omega p k, ∃ f : E → ℝ,
        ContinuousOn f (closure (Omega : Set E)) ∧
        UniformContinuousOn f (Omega : Set E) ∧
        (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f ∧
        ∀ x ∈ closure (Omega : Set E),
          |f x| ≤ C * scaledNormSum (diam (Omega : Set E)) k u := by
  refine ⟨starConvexSupConst (finrank ℝ E) k p γ (mu.real (ball 0 1)),
    starConvexSupConst_nonneg _ _ _ _ measureReal_nonneg,
    fun Omega x₀ ρ hΩ hρ hstar hγ u => ?_⟩
  let g := continuousRepresentativeL hΩ ⟨x₀, ρ, hρ, hstar⟩ hkp u
  obtain ⟨f, hf_cont, hf_uc, hfeq⟩ := exists_extend_of_boundedContinuousFunction hΩ g
  refine ⟨f, hf_cont, hf_uc, ?_, fun x hx => ?_⟩
  · rw [EventuallyEq, ae_restrict_iff' Omega.isOpen.measurableSet]
    filter_upwards [continuousRepresentativeL_ae hΩ ⟨x₀, ρ, hρ, hstar⟩ hkp u] with x hx hxΩ
    rw [hfeq x (subset_closure hxΩ), hx hxΩ]
  · rw [hfeq x hx]
    exact abs_evalClosureL_le hΩ hρ hstar hγ hkp ⟨x, hx⟩ u

/-! ### Boundary continuity of directional derivative components -/

private theorem exists_value_ae_eq_fullContractL_iteratedGradient_aux (v : E) :
    ∀ (j : ℕ) {m k : ℕ} (_ : k = m + j + 1) (u : Wkp mu Omega p k) (w : Wkp mu Omega p (j + 1)),
      value (j + 1) w = value k u →
      ∃ d : Wkp mu Omega p m, (value m d : E → ℝ) =ᵐ[mu.restrict Omega]
        fun x => IteratedGradient.fullContractL j v (iteratedGradient j w x)
  | 0, m, k, hk, u, w, huw => by
      subst hk
      refine ⟨lineDerivL v m u, ?_⟩
      have h1 := hasWeakLineDerivOn_lineDerivL v m u
      have h2 : HasWeakLineDerivOn mu Omega (value 1 w)
          (fun x => IteratedGradient.fullContractL 0 v (iteratedGradient 0 w x)) v := by
        simpa only [IteratedGradient.fullContractL_zero, innerSL_apply_apply,
          real_inner_comm v] using (hasWeakFDerivOn_value w).hasWeakLineDerivOn v
      exact h1.ae_eq (huw ▸ h2)
  | j + 1, m, k, hk, u, w, huw => by
      obtain ⟨d₁, hd₁⟩ := exists_value_ae_eq_fullContractL_iteratedGradient_aux v j (m := m + 1)
        (k := k) (by omega) u (lowerOrder (j + 1) w) (by rw [← value_succ, huw])
      refine ⟨lineDerivL v m d₁, ?_⟩
      have h1 := hasWeakLineDerivOn_lineDerivL v m d₁
      have h2 : HasWeakLineDerivOn mu Omega
          (fun x => IteratedGradient.fullContractL j v
            (iteratedGradient j (lowerOrder (j + 1) w) x))
          (fun x => IteratedGradient.fullContractL (j + 1) v
            (iteratedGradient (j + 1) w x)) v := by
        have hcomp := ((hasWeakFDerivOn_iteratedGradient j w).clm_comp
          (IteratedGradient.fullContractL j v)).hasWeakLineDerivOn v
        have hfun : (fun x => IteratedGradient.fullContractL j v
              ((iteratedGradient (j + 1) w x) v)) =
            fun x => IteratedGradient.fullContractL (j + 1) v (iteratedGradient (j + 1) w x) :=
          funext fun x => by
            rw [IteratedGradient.fullContractL_succ, ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.apply_apply]
        exact hfun ▸ hcomp
      exact h1.ae_eq (h2.congr_ae hd₁.symm)

/-- **Sobolev regularity of directional derivative components.** If `u ∈ W^{k,p}(Ω)` and
`w ∈ W^{j+1,p}(Ω)` share the same underlying value (`j + 1 ≤ k`), then for every direction `v`,
the component `x ↦ (D^{j+1} w)(x)⟨v⟩^{j+1}` represents an element of `W^{k - (j + 1), p}(Ω)`. -/
theorem exists_value_ae_eq_fullContractL_iteratedGradient {j k : ℕ} (hjk : j + 1 ≤ k) (v : E)
    (u : Wkp mu Omega p k) (w : Wkp mu Omega p (j + 1)) (huw : value (j + 1) w = value k u) :
    ∃ d : Wkp mu Omega p (k - (j + 1)),
      (value (k - (j + 1)) d : E → ℝ) =ᵐ[mu.restrict Omega]
        fun x => IteratedGradient.fullContractL j v (iteratedGradient j w x) :=
  exists_value_ae_eq_fullContractL_iteratedGradient_aux v j (by omega) u w huw

/-- **Boundary continuity of directional derivative components (bundled form).** On a bounded open
set `Ω` star-convex with respect to an open ball of positive radius, if `u ∈ W^{k,p}(Ω)` and
`w ∈ W^{j+1,p}(Ω)` share the same underlying value (`j + 1 ≤ k`) and
`dim E < (k - (j + 1)) * p` or `p = 1 ∧ dim E ≤ k - (j + 1)`, then for every direction `v`,
`x ↦ (D^{j+1} w)(x)⟨v⟩^{j+1}` admits a bounded continuous representative on `closure Ω`. -/
theorem exists_continuousRepresentative_fullContractL_of_forall_starConvex
    (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    {j k : ℕ} (hjk : j + 1 ≤ k)
    (hkp : (finrank ℝ E : ℝ≥0∞) < ((k - (j + 1) : ℕ) : ℝ≥0∞) * p ∨
      (p = 1 ∧ finrank ℝ E ≤ k - (j + 1)))
    (v : E) (u : Wkp mu Omega p k) (w : Wkp mu Omega p (j + 1))
    (huw : value (j + 1) w = value k u) :
    ∃ g : closure (Omega : Set E) →ᵇ ℝ,
      ∀ᵐ x ∂mu, ∀ hx : x ∈ Omega,
        g ⟨x, subset_closure hx⟩ = IteratedGradient.fullContractL j v (iteratedGradient j w x) := by
  obtain ⟨d, hd⟩ := exists_value_ae_eq_fullContractL_iteratedGradient hjk v u w huw
  refine ⟨continuousRepresentativeL hΩ hstar hkp d, ?_⟩
  have hd' := (ae_restrict_iff' Omega.isOpen.measurableSet).1 hd
  filter_upwards [continuousRepresentativeL_ae hΩ hstar hkp d, hd'] with x h1 h2 hx
  exact (h1 hx).trans (h2 hx)

/-- **Boundary continuity of directional derivative components.** Under the hypotheses of
`TauCeti.Wkp.exists_continuousRepresentative_fullContractL_of_forall_starConvex`, the directional
derivative component `x ↦ (D^{j+1} w)(x)⟨v⟩^{j+1}` agrees almost everywhere on `Ω` with a function
continuous on `closure Ω` and uniformly continuous on `Ω`. -/
theorem exists_continuousOn_closure_fullContractL_of_forall_starConvex
    (hΩ : IsBounded (Omega : Set E))
    (hstar : ∃ (x₀ : E) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Omega : Set E))
    {j k : ℕ} (hjk : j + 1 ≤ k)
    (hkp : (finrank ℝ E : ℝ≥0∞) < ((k - (j + 1) : ℕ) : ℝ≥0∞) * p ∨
      (p = 1 ∧ finrank ℝ E ≤ k - (j + 1)))
    (v : E) (u : Wkp mu Omega p k) (w : Wkp mu Omega p (j + 1))
    (huw : value (j + 1) w = value k u) :
    ∃ f : E → ℝ, ContinuousOn f (closure (Omega : Set E)) ∧ UniformContinuousOn f Omega ∧
      (fun x => IteratedGradient.fullContractL j v (iteratedGradient j w x)) =ᵐ[mu.restrict Omega]
        f := by
  obtain ⟨g, hg⟩ :=
    exists_continuousRepresentative_fullContractL_of_forall_starConvex hΩ hstar hjk hkp v u w huw
  obtain ⟨f, hf_cont, hf_uc, hfeq⟩ := exists_extend_of_boundedContinuousFunction hΩ g
  refine ⟨f, hf_cont, hf_uc, ?_⟩
  rw [EventuallyEq, ae_restrict_iff' Omega.isOpen.measurableSet]
  filter_upwards [hg] with x hx hxΩ
  rw [hfeq x (subset_closure hxΩ), hx hxΩ]

/-! ### Concrete checks -/

section Examples

-- `u = x` on `(-1, 1)` in `W^{1,1}` (`k = n = p = 1`): point evaluation recovers `x`.
example :
    let Ω : Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩
    let hΩ : IsBounded (Ω : Set ℝ) := isBounded_Ioo (-1) 1
    let hstar : ∃ (x₀ : ℝ) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Ω : Set ℝ) :=
      ⟨0, 1, zero_lt_one, fun _ hy =>
        (convex_Ioo (-1 : ℝ) 1).starConvex (by simpa [Real.ball_eq_Ioo] using hy)⟩
    let hkp : (finrank ℝ ℝ : ℝ≥0∞) < ((1 : ℕ) : ℝ≥0∞) * (1 : ℝ≥0∞) ∨
        ((1 : ℝ≥0∞) = 1 ∧ finrank ℝ ℝ ≤ 1) := Or.inr ⟨rfl, by simp⟩
    ∃ u : Wkp volume Ω 1 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict Ω] id ∧
      ∀ x (hx : x ∈ closure (Ω : Set ℝ)), evalClosureL hΩ hstar hkp ⟨x, hx⟩ u = x := by
  intro Ω hΩ hstar hkp
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := 1) 1 isOpen_univ contDiff_id.contDiffOn isCompact_Icc Ioo_subset_Icc_self
    (subset_univ _)
  exact ⟨u, hu, fun x hx =>
    continuousRepresentativeL_apply_of_continuousOn_closure hΩ hstar hkp continuousOn_id hu
      ⟨x, hx⟩⟩

-- `u = x` on `(0, 1)` in `W^{1,2}`: point evaluation at `1/2` gives `1/2`.
example :
    let Ω : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩
    let hΩ : IsBounded (Ω : Set ℝ) := isBounded_Ioo 0 1
    let hstar : ∃ (x₀ : ℝ) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Ω : Set ℝ) :=
      ⟨1 / 2, 1 / 2, by norm_num, fun _ hy => (convex_Ioo (0 : ℝ) 1).starConvex (by
        rw [Real.ball_eq_Ioo] at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)⟩
    let hkp : (finrank ℝ ℝ : ℝ≥0∞) < ((1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞) ∨
        ((2 : ℝ≥0∞) = 1 ∧ finrank ℝ ℝ ≤ 1) := Or.inl (by norm_num)
    ∃ u : Wkp volume Ω 2 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict Ω] id ∧
      evalL hΩ hstar hkp (by norm_num [Ω] : (1 / 2 : ℝ) ∈ Ω) u = 1 / 2 := by
  intro Ω hΩ hstar hkp
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := 2) 1 isOpen_univ contDiff_id.contDiffOn isCompact_Icc Ioo_subset_Icc_self
    (subset_univ _)
  exact ⟨u, hu,
    continuousRepresentativeL_apply_of_continuousOn_closure hΩ hstar hkp continuousOn_id hu
      ⟨1 / 2, subset_closure (by norm_num [Ω])⟩⟩

-- `u = x²` on `(0, 1)` in `W^{2,2}`: continuous representative with boundary value `1` at `x = 1`,
-- and directional derivative in direction `v = 3` with boundary value `6` at `x = 1`.
example :
    let Ω : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩
    let hΩ : IsBounded (Ω : Set ℝ) := isBounded_Ioo 0 1
    let hstar : ∃ (x₀ : ℝ) (ρ : ℝ), 0 < ρ ∧ ∀ y ∈ ball x₀ ρ, StarConvex ℝ y (Ω : Set ℝ) :=
      ⟨1 / 2, 1 / 2, by norm_num, fun _ hy => (convex_Ioo (0 : ℝ) 1).starConvex (by
        rw [Real.ball_eq_Ioo] at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)⟩
    let hkp₂ : (finrank ℝ ℝ : ℝ≥0∞) < ((2 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞) ∨
        ((2 : ℝ≥0∞) = 1 ∧ finrank ℝ ℝ ≤ 2) := Or.inl (by norm_num)
    ∃ u : Wkp volume Ω 2 2,
      (value 2 u : ℝ → ℝ) =ᵐ[volume.restrict Ω] (fun x => x ^ 2) ∧
      evalClosureL hΩ hstar hkp₂ ⟨1, by simp [Ω, closure_Ioo zero_ne_one]⟩ u = 1 ∧
      ∃ f : ℝ → ℝ, ContinuousOn f (closure (Ω : Set ℝ)) ∧ UniformContinuousOn f Ω ∧
        (fun x => IteratedGradient.fullContractL 0 (3 : ℝ)
          (iteratedGradient 0 (lowerOrder 1 u) x)) =ᵐ[volume.restrict Ω] f ∧ f 1 = 6 := by
  intro Ω hΩ hstar hkp₂
  have hkp₁ : (finrank ℝ ℝ : ℝ≥0∞) < ((2 - 1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞) ∨
      ((2 : ℝ≥0∞) = 1 ∧ finrank ℝ ℝ ≤ 2 - 1) := Or.inl (by norm_num)
  have hf_smooth : ContDiff ℝ 2 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := 2) 2 isOpen_univ hf_smooth.contDiffOn isCompact_Icc Ioo_subset_Icc_self (subset_univ _)
  obtain ⟨f, hf_cont, hf_uc, hf_ae⟩ :=
    exists_continuousOn_closure_fullContractL_of_forall_starConvex hΩ hstar (j := 0) (k := 2)
      (by omega) hkp₁ (3 : ℝ) u (lowerOrder 1 u) (value_succ 1 u).symm
  have h1mem : (1 : ℝ) ∈ closure (Ω : Set ℝ) := by simp [Ω, closure_Ioo zero_ne_one]
  refine ⟨u, hu, ?_, f, hf_cont, hf_uc, hf_ae, ?_⟩
  · rw [evalClosureL_apply]
    simpa using continuousRepresentativeL_apply_of_continuousOn_closure hΩ hstar hkp₂
      (continuous_pow 2).continuousOn hu ⟨1, h1mem⟩
  · have hgrad := iteratedGradient_ae_eq_of_contDiffOn 0 (lowerOrder 1 u)
      (hf_smooth.of_le (by norm_num)).contDiffOn (by simpa only [value_succ] using hu)
    have h6x : (fun x : ℝ => 6 * x) =ᵐ[volume.restrict Ω] f := by
      filter_upwards [hgrad, hf_ae] with x hgx hfx
      rw [← hfx, hgx, iteratedGradientChain_zero, IteratedGradient.fullContractL_zero,
        innerSL_apply_apply, RCLike.inner_apply, conj_trivial]
      have hderiv : gradient (fun t : ℝ => t ^ 2) x = 2 * x := by
        rw [gradient_eq_deriv', (hasDerivAt_pow 2 x).deriv]
        ring
      rw [hderiv]
      ring
    have heq : (fun y : closure (Ω : Set ℝ) => (6 : ℝ) * y) = fun y : closure (Ω : Set ℝ) => f y :=
      Ω.isOpen.ext_closure_of_ae_eq (μ := volume) (continuous_const.mul continuous_subtype_val)
        (continuousOn_iff_continuous_domRestrict.1 hf_cont)
        ((ae_restrict_iff' Ω.isOpen.measurableSet).1 h6x |>.mono fun x hx hxΩ => hx hxΩ)
    simpa using (congrFun heq ⟨1, h1mem⟩).symm

end Examples

end Wkp

end TauCeti

end
