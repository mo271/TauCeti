/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

import Mathlib.Analysis.RCLike.Lemmas

/-!
# Compact form pairs

A *compact form pair* `CompactFormPair 𝕜 E H` packages the variational data for a semibounded
quadratic form on a form domain `E` compactly and densely embedded into an inner-product space `H`:

* an injective, dense-range, compact continuous linear map `inclusion : E →L[𝕜] H`, which need not
  be a topological embedding;
* a bounded Hermitian sesquilinear form `form : E →L⋆[𝕜] E →L[𝕜] 𝕜` satisfying
  `form u v = star (form v u)`;
* an existential lower-bound condition witnessing constants `0 < c` and `ω : ℝ` such that
  `c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2` for all `u : E`.

Keeping `c` and `ω` existential makes `CompactFormPair` extensional in `(inclusion, form)`, while
`CompactFormPair.HasShiftedLowerBound` and `CompactFormPair.ofShiftedLowerBound` track explicit
quantitative constants through every construction:

* `CompactFormPair.shiftForm`: shifts `form` by `α • ⟨inclusion ·, inclusion ·⟩`, translating the
  shift witness from `ω` to `ω - α` and making the shifted energy coercive when `ω ≤ α`;
* `CompactFormPair.restrict`: restricts a pair to a submodule `V₁ ≤ E`, replacing `H` by the
  topological closure of `V₁.map inclusion` so density is preserved;
* `CompactFormPair.congrH`: transports `H` along a linear isometric equivalence;
* `CompactFormPair.congrE`: transports `E` along a continuous linear equivalence (in particular, a
  change to an equivalent norm on the form domain);
* `CompactFormPair.restrictScalars`: restricts scalars from `𝕜` to `ℝ`, taking the real part of
  both the form and the `H`-inner product with unchanged constants `(c, ω)`;
* `CompactFormPair.ofFiniteDimensionalId`: builds the canonical pair on a finite-dimensional
  inner-product space `H` with `inclusion = id`, `c = 1` and `ω = ‖a‖ + 1`.

## References

* V. Ivrii, *Partial Differential Equations*, §13.1, Theorems 1–4.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.8 and §4.10.
-/

public section

noncomputable section

namespace TauCeti

/-- A compact form pair over `𝕜` (`ℝ` or `ℂ`): a normed form domain `E`, an inner-product space
`H`, an injective, dense, compact linear map `inclusion : E →L[𝕜] H`, and a bounded Hermitian
sesquilinear form `form` on `E` admitting a quantitative shifted lower bound
`c * ‖u‖ ^ 2 ≤ Re (form u u) + ω * ‖inclusion u‖ ^ 2` with `0 < c`.

The constants `c` and `ω` are stored existentially so that a compact form pair is determined
extensionally by `(inclusion, form)`. Quantitative bounds for specific constants are expressed via
`CompactFormPair.HasShiftedLowerBound`. -/
structure CompactFormPair (𝕜 E H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  /-- The continuous linear form-domain map `j : E →L[𝕜] H`. -/
  inclusion : E →L[𝕜] H
  /-- Injectivity of `inclusion`. -/
  injective : Function.Injective inclusion
  /-- Density of `Set.range inclusion` in `H`. -/
  dense : DenseRange inclusion
  /-- Compactness of `inclusion` from the norm topology of `E` to `H`. -/
  compact : IsCompactOperator inclusion
  /-- The bounded sesquilinear form `a : E →L⋆[𝕜] E →L[𝕜] 𝕜`, conjugate-linear in its first slot. -/
  form : E →L⋆[𝕜] E →L[𝕜] 𝕜
  /-- The Hermitian symmetry law `a u v = star (a v u)`. -/
  hermitian : ∀ u v, form u v = star (form v u)
  /-- Existence of a coercivity constant `c > 0` and real shift `ω` bounding `c * ‖u‖ ^ 2` by
  `Re (form u u) + ω * ‖inclusion u‖ ^ 2`. -/
  exists_shifted_lower_bound : ∃ c ω : ℝ, 0 < c ∧
    ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2

namespace CompactFormPair

section Basic

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Two compact form pairs with the same inclusion map and sesquilinear form are equal. -/
@[ext]
theorem ext {P Q : CompactFormPair 𝕜 E H}
    (hincl : P.inclusion = Q.inclusion) (hform : P.form = Q.form) : P = Q := by
  cases P
  cases Q
  congr

/-- The real quadratic energy `q(u) = Re (form u u)` of a compact form pair. -/
def energy (P : CompactFormPair 𝕜 E H) (u : E) : ℝ :=
  RCLike.re (P.form u u)

/-- Unfolded formula for `CompactFormPair.energy`. -/
theorem energy_def (P : CompactFormPair 𝕜 E H) (u : E) :
    P.energy u = RCLike.re (P.form u u) :=
  (rfl)

/-- By injectivity, `P.inclusion u = 0` holds if and only if `u = 0`. -/
@[simp]
theorem inclusion_eq_zero_iff (P : CompactFormPair 𝕜 E H) {u : E} :
    P.inclusion u = 0 ↔ u = 0 :=
  map_eq_zero_iff P.inclusion P.injective

/-- The imaginary part of `P.form u u` vanishes by Hermitian symmetry. -/
@[simp]
theorem im_form_self (P : CompactFormPair 𝕜 E H) (u : E) :
    RCLike.im (P.form u u) = 0 := by
  have h := congrArg RCLike.im (P.hermitian u u)
  rw [RCLike.star_def, RCLike.conj_im] at h
  linarith

/-- The diagonal value `P.form u u` equals `(P.energy u : 𝕜)`. -/
theorem form_self_eq_energy (P : CompactFormPair 𝕜 E H) (u : E) :
    P.form u u = (P.energy u : 𝕜) := by
  apply RCLike.ext
  · simp [energy_def]
  · simp

/-- The quadratic energy vanishes at `0`. -/
@[simp]
theorem energy_zero (P : CompactFormPair 𝕜 E H) : P.energy 0 = 0 := by
  simp [energy_def]

/-- The quadratic energy is even. -/
@[simp]
theorem energy_neg (P : CompactFormPair 𝕜 E H) (u : E) : P.energy (-u) = P.energy u := by
  simp [energy_def]

/-- Scaling `u` by `z : 𝕜` scales `P.energy u` by `‖z‖ ^ 2`. -/
theorem energy_smul (P : CompactFormPair 𝕜 E H) (z : 𝕜) (u : E) :
    P.energy (z • u) = ‖z‖ ^ 2 * P.energy u := by
  simp only [energy_def, map_smulₛₗ, FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
    ← mul_assoc]
  rw [RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

/-- Scaling `u` by `(t : 𝕜)` for `t : ℝ` scales `P.energy u` by `t ^ 2`. -/
theorem energy_ofReal_smul (P : CompactFormPair 𝕜 E H) (t : ℝ) (u : E) :
    P.energy ((t : 𝕜) • u) = t ^ 2 * P.energy u := by
  rw [P.energy_smul, RCLike.norm_ofReal, sq_abs]

/-- Real-part symmetry `Re (P.form v u) = Re (P.form u v)` from the Hermitian law. -/
theorem re_form_symm (P : CompactFormPair 𝕜 E H) (u v : E) :
    RCLike.re (P.form v u) = RCLike.re (P.form u v) := by
  rw [P.hermitian v u, RCLike.star_def, RCLike.conj_re]

/-- Exact quadratic expansion of `P.energy (u + v)`. -/
theorem energy_add (P : CompactFormPair 𝕜 E H) (u v : E) :
    P.energy (u + v) = P.energy u + 2 * RCLike.re (P.form u v) + P.energy v := by
  simp only [energy_def, map_add, FunLike.coe_add, Pi.add_apply, P.re_form_symm u v]
  ring

/-- Exact quadratic expansion of `P.energy (u - v)`. -/
theorem energy_sub (P : CompactFormPair 𝕜 E H) (u v : E) :
    P.energy (u - v) = P.energy u - 2 * RCLike.re (P.form u v) + P.energy v := by
  simpa [sub_eq_add_neg, mul_neg] using P.energy_add u (-v)

/-- Pointwise operator-norm bound `|P.energy u| ≤ ‖P.form‖ * ‖u‖ ^ 2`. -/
theorem abs_energy_le (P : CompactFormPair 𝕜 E H) (u : E) :
    |P.energy u| ≤ ‖P.form‖ * ‖u‖ ^ 2 := by
  calc
    |P.energy u| = |RCLike.re (P.form u u)| := rfl
    _ ≤ ‖P.form u u‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖P.form‖ * ‖u‖ * ‖u‖ := P.form.le_opNorm₂ u u
    _ = ‖P.form‖ * ‖u‖ ^ 2 := by ring

/-- The quadratic energy of a compact form pair is norm-continuous on `E`. -/
@[fun_prop]
theorem continuous_energy (P : CompactFormPair 𝕜 E H) : Continuous P.energy :=
  RCLike.continuous_re.comp (P.form.continuous.clm_apply continuous_id)

/-! ### Quantitative shifted lower bounds -/

/-- `P.HasShiftedLowerBound c ω` records that `0 < c` and
`c * ‖u‖ ^ 2 ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2` for every `u : E`. -/
def HasShiftedLowerBound (P : CompactFormPair 𝕜 E H) (c ω : ℝ) : Prop :=
  0 < c ∧ ∀ u, c * ‖u‖ ^ 2 ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2

/-- Characterization of `CompactFormPair.HasShiftedLowerBound`. -/
theorem hasShiftedLowerBound_iff {P : CompactFormPair 𝕜 E H} {c ω : ℝ} :
    P.HasShiftedLowerBound c ω ↔
      0 < c ∧ ∀ u, c * ‖u‖ ^ 2 ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2 :=
  Iff.rfl

/-- Positivity of the coercivity constant in `HasShiftedLowerBound`. -/
theorem HasShiftedLowerBound.pos {P : CompactFormPair 𝕜 E H} {c ω : ℝ}
    (h : P.HasShiftedLowerBound c ω) : 0 < c :=
  h.1

/-- Pointwise shifted lower bound from `HasShiftedLowerBound`. -/
theorem HasShiftedLowerBound.bound {P : CompactFormPair 𝕜 E H} {c ω : ℝ}
    (h : P.HasShiftedLowerBound c ω) (u : E) :
    c * ‖u‖ ^ 2 ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2 :=
  h.2 u

/-- Decreasing `c > 0` and increasing `ω` preserves `HasShiftedLowerBound`. -/
theorem HasShiftedLowerBound.mono {P : CompactFormPair 𝕜 E H} {c c' ω ω' : ℝ}
    (h : P.HasShiftedLowerBound c ω) (hc' : 0 < c') (hcc : c' ≤ c) (hω : ω ≤ ω') :
    P.HasShiftedLowerBound c' ω' := by
  refine ⟨hc', fun u => ?_⟩
  calc
    c' * ‖u‖ ^ 2 ≤ c * ‖u‖ ^ 2 := by gcongr
    _ ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2 := h.bound u
    _ ≤ P.energy u + ω' * ‖P.inclusion u‖ ^ 2 := by gcongr

/-- Construct a `CompactFormPair` from explicit shifted-lower-bound constants `c` and `ω`. -/
def ofShiftedLowerBound (inclusion : E →L[𝕜] H)
    (injective : Function.Injective inclusion) (dense : DenseRange inclusion)
    (compact : IsCompactOperator inclusion) (form : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (hermitian : ∀ u v, form u v = star (form v u)) (c ω : ℝ)
    (hc : 0 < c)
    (hbound : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2) :
    CompactFormPair 𝕜 E H where
  inclusion := inclusion
  injective := injective
  dense := dense
  compact := compact
  form := form
  hermitian := hermitian
  exists_shifted_lower_bound := ⟨c, ω, hc, hbound⟩

/-- Inclusion map of `CompactFormPair.ofShiftedLowerBound`. -/
@[simp]
theorem inclusion_ofShiftedLowerBound (inclusion : E →L[𝕜] H)
    (injective : Function.Injective inclusion) (dense : DenseRange inclusion)
    (compact : IsCompactOperator inclusion) (form : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (hermitian : ∀ u v, form u v = star (form v u)) (c ω : ℝ)
    (hc : 0 < c)
    (hbound : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2) :
    (ofShiftedLowerBound inclusion injective dense compact form hermitian c ω hc hbound).inclusion =
      inclusion :=
  (rfl)

/-- Sesquilinear form of `CompactFormPair.ofShiftedLowerBound`. -/
@[simp]
theorem form_ofShiftedLowerBound (inclusion : E →L[𝕜] H)
    (injective : Function.Injective inclusion) (dense : DenseRange inclusion)
    (compact : IsCompactOperator inclusion) (form : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (hermitian : ∀ u v, form u v = star (form v u)) (c ω : ℝ)
    (hc : 0 < c)
    (hbound : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2) :
    (ofShiftedLowerBound inclusion injective dense compact form hermitian c ω hc hbound).form =
      form :=
  (rfl)

/-- Quadratic energy of `CompactFormPair.ofShiftedLowerBound`. -/
theorem energy_ofShiftedLowerBound (inclusion : E →L[𝕜] H)
    (injective : Function.Injective inclusion) (dense : DenseRange inclusion)
    (compact : IsCompactOperator inclusion) (form : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (hermitian : ∀ u v, form u v = star (form v u)) (c ω : ℝ)
    (hc : 0 < c)
    (hbound : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2) (u : E) :
    (ofShiftedLowerBound inclusion injective dense compact form hermitian c ω hc hbound).energy u =
      RCLike.re (form u u) :=
  (rfl)

/-- `CompactFormPair.ofShiftedLowerBound` satisfies `HasShiftedLowerBound` with the supplied
constants `(c, ω)`. -/
theorem hasShiftedLowerBound_ofShiftedLowerBound (inclusion : E →L[𝕜] H)
    (injective : Function.Injective inclusion) (dense : DenseRange inclusion)
    (compact : IsCompactOperator inclusion) (form : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (hermitian : ∀ u v, form u v = star (form v u)) (c ω : ℝ)
    (hc : 0 < c)
    (hbound : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2) :
    (ofShiftedLowerBound inclusion injective dense compact form hermitian c ω hc
      hbound).HasShiftedLowerBound c ω :=
  ⟨hc, hbound⟩

/-- Chosen coercivity constant `c > 0` witnessing `P.exists_shifted_lower_bound`. -/
def coercivityConstant (P : CompactFormPair 𝕜 E H) : ℝ :=
  P.exists_shifted_lower_bound.choose

/-- Chosen real shift `ω` paired with `P.coercivityConstant`. -/
def shift (P : CompactFormPair 𝕜 E H) : ℝ :=
  P.exists_shifted_lower_bound.choose_spec.choose

/-- `P.coercivityConstant` and `P.shift` satisfy `HasShiftedLowerBound`. -/
theorem hasShiftedLowerBound_coercivityConstant_shift (P : CompactFormPair 𝕜 E H) :
    P.HasShiftedLowerBound P.coercivityConstant P.shift :=
  P.exists_shifted_lower_bound.choose_spec.choose_spec

/-- Strict positivity of `P.coercivityConstant`. -/
theorem coercivityConstant_pos (P : CompactFormPair 𝕜 E H) : 0 < P.coercivityConstant :=
  P.hasShiftedLowerBound_coercivityConstant_shift.pos

/-- Pointwise shifted lower bound for `P.coercivityConstant` and `P.shift`. -/
theorem shifted_lower_bound (P : CompactFormPair 𝕜 E H) (u : E) :
    P.coercivityConstant * ‖u‖ ^ 2 ≤ P.energy u + P.shift * ‖P.inclusion u‖ ^ 2 :=
  P.hasShiftedLowerBound_coercivityConstant_shift.bound u

/-! ### Semibounded shifts -/

/-- Shift the form of `P` by `α • ⟨P.inclusion ·, P.inclusion ·⟩` for `α : ℝ`. -/
def shiftForm (P : CompactFormPair 𝕜 E H) (α : ℝ) : CompactFormPair 𝕜 E H where
  inclusion := P.inclusion
  injective := P.injective
  dense := P.dense
  compact := P.compact
  form := P.form + (α : 𝕜) • (innerSL 𝕜).bilinearComp P.inclusion P.inclusion
  hermitian u v := by
    simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply, smul_eq_mul,
      map_add, map_mul, RCLike.star_def, RCLike.conj_ofReal, inner_conj_symm]
    rw [P.hermitian u v, RCLike.star_def]
  exists_shifted_lower_bound := by
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    refine ⟨c, ω - α, hc, fun u => ?_⟩
    have hre :
        RCLike.re ((P.form + (α : 𝕜) • (innerSL 𝕜).bilinearComp P.inclusion P.inclusion) u u) =
          RCLike.re (P.form u u) + α * ‖P.inclusion u‖ ^ 2 := by
      simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
        Pi.smul_apply, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply, smul_eq_mul,
        map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]
    linarith [hbound u]

/-- Shifting the form leaves `inclusion` unchanged. -/
@[simp]
theorem inclusion_shiftForm (P : CompactFormPair 𝕜 E H) (α : ℝ) :
    (P.shiftForm α).inclusion = P.inclusion :=
  (rfl)

/-- Evaluation formula for `(P.shiftForm α).form`. -/
@[simp]
theorem form_shiftForm_apply (P : CompactFormPair 𝕜 E H) (α : ℝ) (u v : E) :
    (P.shiftForm α).form u v = P.form u v + (α : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v) :=
  (rfl)

/-- Shifting by `α` adds `α * ‖P.inclusion u‖ ^ 2` to the quadratic energy. -/
@[simp]
theorem energy_shiftForm (P : CompactFormPair 𝕜 E H) (α : ℝ) (u : E) :
    (P.shiftForm α).energy u = P.energy u + α * ‖P.inclusion u‖ ^ 2 := by
  simp only [energy_def, form_shiftForm_apply, map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]

/-- Shifting by `0` leaves a compact form pair unchanged. -/
@[simp]
theorem shiftForm_zero (P : CompactFormPair 𝕜 E H) : P.shiftForm 0 = P := by
  ext u v
  · rfl
  · simp

/-- Successive shifts add their real shift parameters. -/
@[simp]
theorem shiftForm_shiftForm (P : CompactFormPair 𝕜 E H) (α β : ℝ) :
    (P.shiftForm α).shiftForm β = P.shiftForm (α + β) := by
  ext u v
  · rfl
  · simp [add_mul, add_assoc]

/-- Recovering `P.form` from `(P.shiftForm α).form` by subtracting the `H`-inner product term. -/
theorem form_eq_form_shiftForm_sub (P : CompactFormPair 𝕜 E H) (α : ℝ) (u v : E) :
    P.form u v = (P.shiftForm α).form u v - (α : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v) :=
  eq_sub_of_add_eq (P.form_shiftForm_apply α u v).symm

/-- Shifting by `α` translates the shift constant `ω` to `ω - α` with the same `c`. -/
theorem HasShiftedLowerBound.shiftForm {P : CompactFormPair 𝕜 E H} {c ω : ℝ}
    (h : P.HasShiftedLowerBound c ω) (α : ℝ) :
    (P.shiftForm α).HasShiftedLowerBound c (ω - α) := by
  refine ⟨h.pos, fun u => ?_⟩
  rw [energy_shiftForm, inclusion_shiftForm]
  linarith [h.bound u]

/-- Equivalence of `HasShiftedLowerBound` before and after shifting by `α`. -/
@[simp]
theorem hasShiftedLowerBound_shiftForm_iff (P : CompactFormPair 𝕜 E H) (c ω α : ℝ) :
    (P.shiftForm α).HasShiftedLowerBound c (ω - α) ↔ P.HasShiftedLowerBound c ω := by
  refine ⟨fun h => ?_, fun h => h.shiftForm α⟩
  simpa [sub_neg_eq_add] using h.shiftForm (-α)

/-- Every shift `α ≥ ω` makes `(P.shiftForm α).energy` coercive on `E` with the same constant
`c`. -/
theorem HasShiftedLowerBound.mul_norm_sq_le_energy_shiftForm {P : CompactFormPair 𝕜 E H}
    {c ω α : ℝ} (h : P.HasShiftedLowerBound c ω) (hωα : ω ≤ α) (u : E) :
    c * ‖u‖ ^ 2 ≤ (P.shiftForm α).energy u := by
  have hsub : 0 ≤ (α - ω) * ‖P.inclusion u‖ ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hωα) (sq_nonneg _)
  rw [energy_shiftForm]
  linarith [h.bound u]

/-- Coercivity of `(P.shiftForm α).energy` whenever `P.shift ≤ α`. -/
theorem mul_norm_sq_le_energy_shiftForm (P : CompactFormPair 𝕜 E H) {α : ℝ}
    (hα : P.shift ≤ α) (u : E) :
    P.coercivityConstant * ‖u‖ ^ 2 ≤ (P.shiftForm α).energy u :=
  P.hasShiftedLowerBound_coercivityConstant_shift.mul_norm_sq_le_energy_shiftForm hα u

/-- Upper bound `(P.shiftForm α).energy u ≤ (‖P.form‖ + |α| * ‖P.inclusion‖ ^ 2) * ‖u‖ ^ 2`,
giving two-sided norm equivalence with `E` when combined with coercivity for `α ≥ ω`. -/
theorem energy_shiftForm_le (P : CompactFormPair 𝕜 E H) (α : ℝ) (u : E) :
    (P.shiftForm α).energy u ≤ (‖P.form‖ + |α| * ‖P.inclusion‖ ^ 2) * ‖u‖ ^ 2 := by
  rw [energy_shiftForm]
  have h1 : P.energy u ≤ ‖P.form‖ * ‖u‖ ^ 2 := (le_abs_self _).trans (P.abs_energy_le u)
  have h2 : α * ‖P.inclusion u‖ ^ 2 ≤ |α| * (‖P.inclusion‖ * ‖u‖) ^ 2 := by
    calc
      α * ‖P.inclusion u‖ ^ 2 ≤ |α| * ‖P.inclusion u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self α) (sq_nonneg _)
      _ ≤ |α| * (‖P.inclusion‖ * ‖u‖) ^ 2 := by
        gcongr
        exact P.inclusion.le_opNorm u
  linarith

/-! ### Restriction to a submodule -/

/-- Restrict a compact form pair `P` to a submodule `V₁ ≤ E`, replacing `H` by the topological
closure of `V₁.map P.inclusion` so that the restricted inclusion retains dense range. -/
def restrict (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) :
    CompactFormPair 𝕜 V₁ (V₁.map P.inclusion.toLinearMap).topologicalClosure where
  inclusion := (P.inclusion.comp V₁.subtypeL).codRestrict
    (V₁.map P.inclusion.toLinearMap).topologicalClosure fun u =>
      (V₁.map P.inclusion.toLinearMap).le_topologicalClosure ⟨u, u.2, rfl⟩
  injective u v huv := Subtype.ext <| P.injective <| congrArg Subtype.val huv
  dense := by
    rw [denseRange_iff_closure_range]
    apply Set.Subset.antisymm (Set.subset_univ _)
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ closure (P.inclusion '' (V₁ : Set E)) := hx
    rw [Metric.mem_closure_iff] at hx' ⊢
    intro ε hε
    obtain ⟨_, ⟨u, hu, rfl⟩, hdist⟩ := hx' ε hε
    exact ⟨_, ⟨⟨u, hu⟩, rfl⟩, hdist⟩
  compact := (P.compact.comp_clm V₁.subtypeL).codRestrict
    (fun u => (V₁.map P.inclusion.toLinearMap).le_topologicalClosure ⟨u, u.2, rfl⟩)
    (V₁.map P.inclusion.toLinearMap).isClosed_topologicalClosure
  form := P.form.bilinearComp V₁.subtypeL V₁.subtypeL
  hermitian u v := P.hermitian u v
  exists_shifted_lower_bound := by
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    exact ⟨c, ω, hc, fun u => hbound u⟩

/-- Ambient coercion of `(P.restrict V₁).inclusion u` agrees with `P.inclusion u`. -/
@[simp]
theorem coe_inclusion_restrict (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) (u : V₁) :
    ((P.restrict V₁).inclusion u : H) = P.inclusion u :=
  (rfl)

/-- Evaluation of `(P.restrict V₁).form` agrees with `P.form` on `V₁`. -/
@[simp]
theorem form_restrict_apply (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) (u v : V₁) :
    (P.restrict V₁).form u v = P.form u v :=
  (rfl)

/-- Quadratic energy of `P.restrict V₁` agrees with `P.energy` on `V₁`. -/
@[simp]
theorem energy_restrict (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) (u : V₁) :
    (P.restrict V₁).energy u = P.energy u :=
  (rfl)

/-- Restriction to a submodule preserves any `HasShiftedLowerBound c ω` witness. -/
theorem HasShiftedLowerBound.restrict {P : CompactFormPair 𝕜 E H} {c ω : ℝ}
    (h : P.HasShiftedLowerBound c ω) (V₁ : Submodule 𝕜 E) :
    (P.restrict V₁).HasShiftedLowerBound c ω :=
  ⟨h.pos, fun u => h.bound u⟩

/-! ### Unitary transport in `H` -/

/-- Transport a compact form pair along a linear isometric equivalence `U : H ≃ₗᵢ[𝕜] H'`. -/
def congrH (P : CompactFormPair 𝕜 E H) {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] (U : H ≃ₗᵢ[𝕜] H') :
    CompactFormPair 𝕜 E H' where
  inclusion := U.toLinearIsometry.toContinuousLinearMap.comp P.inclusion
  injective := U.injective.comp P.injective
  dense := U.surjective.denseRange.comp P.dense U.continuous
  compact := P.compact.clm_comp U.toLinearIsometry.toContinuousLinearMap
  form := P.form
  hermitian := P.hermitian
  exists_shifted_lower_bound := by
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    refine ⟨c, ω, hc, fun u => ?_⟩
    simpa [U.norm_map] using hbound u

/-- Inclusion map of `P.congrH U`. -/
@[simp]
theorem inclusion_congrH (P : CompactFormPair 𝕜 E H) {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] (U : H ≃ₗᵢ[𝕜] H') :
    (P.congrH U).inclusion = U.toLinearIsometry.toContinuousLinearMap.comp P.inclusion :=
  (rfl)

/-- Unitary transport in `H` leaves `form` unchanged. -/
@[simp]
theorem form_congrH (P : CompactFormPair 𝕜 E H) {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] (U : H ≃ₗᵢ[𝕜] H') :
    (P.congrH U).form = P.form :=
  (rfl)

/-- Unitary transport in `H` leaves `energy` unchanged. -/
@[simp]
theorem energy_congrH (P : CompactFormPair 𝕜 E H) {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] (U : H ≃ₗᵢ[𝕜] H') (u : E) :
    (P.congrH U).energy u = P.energy u :=
  (rfl)

/-- Unitary transport along `LinearIsometryEquiv.refl` is the identity. -/
@[simp]
theorem congrH_refl (P : CompactFormPair 𝕜 E H) : P.congrH (LinearIsometryEquiv.refl 𝕜 H) = P := by
  ext <;> rfl

/-- Composing unitary transports in `H`. -/
theorem congrH_trans (P : CompactFormPair 𝕜 E H) {H' H'' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    [NormedAddCommGroup H''] [InnerProductSpace 𝕜 H'']
    (U : H ≃ₗᵢ[𝕜] H') (V : H' ≃ₗᵢ[𝕜] H'') :
    (P.congrH U).congrH V = P.congrH (U.trans V) := by
  ext <;> rfl

/-- Unitary transport in `H` preserves `HasShiftedLowerBound c ω` iff it held originally. -/
@[simp]
theorem hasShiftedLowerBound_congrH_iff (P : CompactFormPair 𝕜 E H) {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] (U : H ≃ₗᵢ[𝕜] H') (c ω : ℝ) :
    (P.congrH U).HasShiftedLowerBound c ω ↔ P.HasShiftedLowerBound c ω := by
  simp [HasShiftedLowerBound, U.norm_map]

/-! ### Continuous linear equivalence on `E` (change to an equivalent norm) -/

private theorem congrE_bound_aux {P : CompactFormPair 𝕜 E H} {c ω : ℝ}
    (hc : 0 < c) (hbound : ∀ v : E, c * ‖v‖ ^ 2 ≤ RCLike.re (P.form v v) + ω * ‖P.inclusion v‖ ^ 2)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (e : E' ≃L[𝕜] E) :
    let M : ℝ := max 1 (‖(e.symm : E →L[𝕜] E')‖ ^ 2)
    0 < c / M ∧ ∀ u : E',
      c / M * ‖u‖ ^ 2 ≤ RCLike.re (P.form (e u) (e u)) + ω * ‖P.inclusion (e u)‖ ^ 2 := by
  intro M
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨div_pos hc hMpos, fun u => ?_⟩
  have hu : ‖u‖ ^ 2 ≤ M * ‖e u‖ ^ 2 := by
    calc
      ‖u‖ ^ 2 = ‖e.symm (e u)‖ ^ 2 := by rw [e.symm_apply_apply]
      _ ≤ (‖(e.symm : E →L[𝕜] E')‖ * ‖e u‖) ^ 2 := by
        gcongr
        exact (e.symm : E →L[𝕜] E').le_opNorm (e u)
      _ = ‖(e.symm : E →L[𝕜] E')‖ ^ 2 * ‖e u‖ ^ 2 := by ring
      _ ≤ M * ‖e u‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  calc
    c / M * ‖u‖ ^ 2 ≤ c / M * (M * ‖e u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hu (div_pos hc hMpos).le
    _ = c * ‖e u‖ ^ 2 := by field_simp [hMpos.ne']
    _ ≤ RCLike.re (P.form (e u) (e u)) + ω * ‖P.inclusion (e u)‖ ^ 2 := hbound (e u)

/-- Pull back a compact form pair along a continuous linear equivalence `e : E' ≃L[𝕜] E`, modeling
in particular a change to an equivalent norm on the form domain. -/
def congrE (P : CompactFormPair 𝕜 E H) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (e : E' ≃L[𝕜] E) :
    CompactFormPair 𝕜 E' H where
  inclusion := P.inclusion.comp (e : E' →L[𝕜] E)
  injective := P.injective.comp e.injective
  dense := P.dense.comp e.surjective.denseRange P.inclusion.continuous
  compact := P.compact.comp_clm (e : E' →L[𝕜] E)
  form := P.form.bilinearComp (e : E' →L[𝕜] E) (e : E' →L[𝕜] E)
  hermitian u v := P.hermitian (e u) (e v)
  exists_shifted_lower_bound := by
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    obtain ⟨hc', hbound'⟩ := P.congrE_bound_aux hc hbound e
    exact ⟨_, ω, hc', hbound'⟩

/-- Inclusion map of `P.congrE e`. -/
@[simp]
theorem inclusion_congrE (P : CompactFormPair 𝕜 E H) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (e : E' ≃L[𝕜] E) :
    (P.congrE e).inclusion = P.inclusion.comp (e : E' →L[𝕜] E) :=
  (rfl)

/-- Pointwise evaluation of `(P.congrE e).form`. -/
@[simp]
theorem form_congrE_apply (P : CompactFormPair 𝕜 E H) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (e : E' ≃L[𝕜] E) (u v : E') :
    (P.congrE e).form u v = P.form (e u) (e v) :=
  (rfl)

/-- Quadratic energy of `P.congrE e` pulls back `P.energy` along `e`. -/
@[simp]
theorem energy_congrE (P : CompactFormPair 𝕜 E H) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (e : E' ≃L[𝕜] E) (u : E') :
    (P.congrE e).energy u = P.energy (e u) :=
  (rfl)

/-- Pulling back along `ContinuousLinearEquiv.refl` is the identity. -/
@[simp]
theorem congrE_refl (P : CompactFormPair 𝕜 E H) :
    P.congrE (ContinuousLinearEquiv.refl 𝕜 E) = P := by
  ext <;> rfl

/-- Composing continuous linear equivalences on the form domain. -/
theorem congrE_trans (P : CompactFormPair 𝕜 E H) {E' E'' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    (e₁ : E'' ≃L[𝕜] E') (e₂ : E' ≃L[𝕜] E) :
    (P.congrE e₂).congrE e₁ = P.congrE (e₁.trans e₂) := by
  ext <;> rfl

/-- Quantitative `HasShiftedLowerBound` transport along `e : E' ≃L[𝕜] E` when `a * ‖u‖ ≤ ‖e u‖`
with `0 < a`. -/
theorem HasShiftedLowerBound.congrE_of_norm_le {P : CompactFormPair 𝕜 E H} {c ω : ℝ}
    (h : P.HasShiftedLowerBound c ω) {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (e : E' ≃L[𝕜] E) {a : ℝ} (ha : 0 < a) (hnorm : ∀ u : E', a * ‖u‖ ≤ ‖e u‖) :
    (P.congrE e).HasShiftedLowerBound (c * a ^ 2) ω := by
  refine ⟨mul_pos h.pos (sq_pos_of_pos ha), fun u => ?_⟩
  have hsq : (a * ‖u‖) ^ 2 ≤ ‖e u‖ ^ 2 :=
    sq_le_sq₀ (mul_nonneg ha.le (norm_nonneg u)) (norm_nonneg (e u)) |>.mpr (hnorm u)
  calc
    c * a ^ 2 * ‖u‖ ^ 2 = c * (a * ‖u‖) ^ 2 := by ring
    _ ≤ c * ‖e u‖ ^ 2 := mul_le_mul_of_nonneg_left hsq h.pos.le
    _ ≤ P.energy (e u) + ω * ‖P.inclusion (e u)‖ ^ 2 := h.bound (e u)

/-- Unconditional quantitative `HasShiftedLowerBound` transport along `e : E' ≃L[𝕜] E`. -/
theorem HasShiftedLowerBound.congrE {P : CompactFormPair 𝕜 E H} {c ω : ℝ}
    (h : P.HasShiftedLowerBound c ω) {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (e : E' ≃L[𝕜] E) :
    (P.congrE e).HasShiftedLowerBound (c / max 1 (‖(e.symm : E →L[𝕜] E')‖ ^ 2)) ω :=
  P.congrE_bound_aux h.pos h.bound e

/-! ### Restriction of scalars to `ℝ` -/

private def restrictScalarsForm (P : CompactFormPair 𝕜 E H) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    E →L[ℝ] E →L[ℝ] ℝ :=
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  LinearMap.mkContinuous₂
    { toFun u := (RCLike.reCLM.comp ((P.form u).restrictScalars ℝ)).toLinearMap
      map_add' u₁ u₂ := by
        ext v
        simp
      map_smul' r u := by
        ext v
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_restrictScalars', RCLike.reCLM_apply, RingHom.id_apply,
          LinearMap.smul_apply, smul_eq_mul]
        have h : P.form (r • u) = P.form ((r : 𝕜) • u) := rfl
        rw [h, map_smulₛₗ, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, RCLike.conj_ofReal,
          RCLike.re_ofReal_mul] }
    ‖P.form‖ fun u v => by
      calc
        ‖RCLike.re (P.form u v)‖ = |RCLike.re (P.form u v)| := Real.norm_eq_abs _
        _ ≤ ‖P.form u v‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖P.form‖ * ‖u‖ * ‖v‖ := P.form.le_opNorm₂ u v

/-- Restrict a `𝕜`-compact form pair to a real compact form pair on the same underlying spaces
equipped with `NormedSpace.restrictScalars ℝ 𝕜 E` and `InnerProductSpace.rclikeToReal 𝕜 H`,
replacing `form` by `Re ∘ form` and keeping the exact same lower-bound constants `(c, ω)`. -/
def restrictScalars (P : CompactFormPair 𝕜 E H) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    letI := InnerProductSpace.rclikeToReal 𝕜 H
    CompactFormPair ℝ E H :=
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  letI := InnerProductSpace.rclikeToReal 𝕜 H
  { inclusion := P.inclusion.restrictScalars ℝ
    injective := P.injective
    dense := P.dense
    compact := P.compact
    form := P.restrictScalarsForm
    hermitian u v := by
      simp [restrictScalarsForm, LinearMap.mkContinuous₂_apply, P.re_form_symm u v]
    exists_shifted_lower_bound := by
      obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
      exact ⟨c, ω, hc, fun u => hbound u⟩ }

/-- Inclusion map of `P.restrictScalars`. -/
@[simp]
theorem inclusion_restrictScalars (P : CompactFormPair 𝕜 E H) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    letI := InnerProductSpace.rclikeToReal 𝕜 H
    P.restrictScalars.inclusion = P.inclusion.restrictScalars ℝ :=
  (rfl)

/-- Pointwise evaluation of `P.restrictScalars.form` is the real part of `P.form`. -/
@[simp]
theorem form_restrictScalars_apply (P : CompactFormPair 𝕜 E H) (u v : E) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    letI := InnerProductSpace.rclikeToReal 𝕜 H
    P.restrictScalars.form u v = RCLike.re (P.form u v) :=
  (rfl)

/-- Scalar restriction to `ℝ` leaves `energy` unchanged. -/
@[simp]
theorem energy_restrictScalars (P : CompactFormPair 𝕜 E H) (u : E) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    letI := InnerProductSpace.rclikeToReal 𝕜 H
    P.restrictScalars.energy u = P.energy u :=
  (rfl)

/-- Real scalar restriction preserves `HasShiftedLowerBound c ω` with identical constants. -/
@[simp]
theorem hasShiftedLowerBound_restrictScalars_iff (P : CompactFormPair 𝕜 E H) (c ω : ℝ) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    letI := InnerProductSpace.rclikeToReal 𝕜 H
    P.restrictScalars.HasShiftedLowerBound c ω ↔ P.HasShiftedLowerBound c ω :=
  Iff.rfl

end Basic

/-! ### Canonical finite-dimensional pair -/

section FiniteDimensional

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem ofFiniteDimensionalId_bound (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (u : H) :
    1 * ‖u‖ ^ 2 ≤ RCLike.re (a u u) + (‖a‖ + 1) * ‖ContinuousLinearMap.id 𝕜 H u‖ ^ 2 := by
  have hre : -‖a‖ * ‖u‖ ^ 2 ≤ RCLike.re (a u u) := by
    have habs : |RCLike.re (a u u)| ≤ ‖a‖ * ‖u‖ ^ 2 :=
      (RCLike.abs_re_le_norm _).trans (by simpa [sq, mul_assoc] using a.le_opNorm₂ u u)
    linarith [neg_abs_le (RCLike.re (a u u))]
  simp only [ContinuousLinearMap.id_apply]
  linarith

variable [FiniteDimensional 𝕜 H]

/-- Every bounded Hermitian form `a` on a finite-dimensional inner-product space `H` forms a
compact form pair with `inclusion = ContinuousLinearMap.id 𝕜 H`, coercivity constant `1`, and shift
`‖a‖ + 1`. -/
def ofFiniteDimensionalId (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ha : ∀ u v, a u v = star (a v u)) : CompactFormPair 𝕜 H H :=
  haveI := FiniteDimensional.proper_rclike 𝕜 H
  ofShiftedLowerBound (ContinuousLinearMap.id 𝕜 H) Function.injective_id
    Function.surjective_id.denseRange (isCompactOperator_id (E := H)) a ha 1 (‖a‖ + 1)
    zero_lt_one (ofFiniteDimensionalId_bound a)

/-- Inclusion map of `CompactFormPair.ofFiniteDimensionalId` is the identity. -/
@[simp]
theorem inclusion_ofFiniteDimensionalId (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ha : ∀ u v, a u v = star (a v u)) :
    (ofFiniteDimensionalId a ha).inclusion = ContinuousLinearMap.id 𝕜 H :=
  (rfl)

/-- Sesquilinear form of `CompactFormPair.ofFiniteDimensionalId` is `a`. -/
@[simp]
theorem form_ofFiniteDimensionalId (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ha : ∀ u v, a u v = star (a v u)) :
    (ofFiniteDimensionalId a ha).form = a :=
  (rfl)

/-- Quadratic energy of `CompactFormPair.ofFiniteDimensionalId` is `Re (a u u)`. -/
theorem energy_ofFiniteDimensionalId (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ha : ∀ u v, a u v = star (a v u)) (u : H) :
    (ofFiniteDimensionalId a ha).energy u = RCLike.re (a u u) :=
  (rfl)

/-- `ofFiniteDimensionalId a ha` satisfies `HasShiftedLowerBound 1 (‖a‖ + 1)`. -/
theorem hasShiftedLowerBound_ofFiniteDimensionalId
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ha : ∀ u v, a u v = star (a v u)) :
    (ofFiniteDimensionalId a ha).HasShiftedLowerBound 1 (‖a‖ + 1) :=
  hasShiftedLowerBound_ofShiftedLowerBound _ _ _ _ _ _ _ _ zero_lt_one
    (ofFiniteDimensionalId_bound a)

end FiniteDimensional

end CompactFormPair

end TauCeti

end
