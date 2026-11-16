/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Variational.CompactFormPair.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Constrained spheres, Rayleigh minima, and the restricted Euler–Lagrange equation

For a compact form pair `P : CompactFormPair 𝕜 E H` and a submodule `W : Submodule 𝕜 H`, the
admissible constrained sphere is

`P.unitConstraint W = {u : E | P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1}`.

This module develops the variational theory of `P.energy` on `P.unitConstraint W`:

* **Constrained spheres and Rayleigh quotients**: witness independence, behavior under shifts,
  submodule restriction, unitary/norm transport, scalar restriction, phase invariance, the sharp
  nonemptiness criterion `∃ u, P.inclusion u ∈ W ∧ P.inclusion u ≠ 0`, equivalence of sphere
  minimization with minimizing the Rayleigh quotient `P.energy v / ‖P.inclusion v‖ ^ 2`, and the
  lower bound `-ω ≤ P.energy u`.
* **Bounded sublevels**: `CompactFormPair.hasBoundedSublevelsOn_energy_unitConstraint` shows that
  every energy sublevel on `P.unitConstraint W` is norm bounded via `‖u‖ ^ 2 ≤ (b + ω) / c`, so
  the set of sphere minimizers is bounded.
* **Existence of constrained minima and coercive comparison**: on any complete form domain `E` and
  norm-closed submodule `W` containing a nonzero image of `P.inclusion`,
  `CompactFormPair.exists_minimum_on_unitConstraint` proves that `P.energy` attains its minimum on
  `P.unitConstraint W` without requiring an inner product on `E` or completeness of `H`. Over `ℝ`
  on a complete inner-product form domain, `CompactFormPair.isLeast_energy_unitConstraint_top_real`
  identifies the unconstrained sphere minimum with `‖hB.formSolutionOperator P.inclusion‖⁻¹ - α`.
* **Restricted Euler–Lagrange equation**: `CompactFormPair.equation_of_isLocalExtrOn_unitConstraint`
  and `CompactFormPair.equation_of_constrained_minimum` prove that any local extremum (in
  particular, any global minimizer) `u ∈ P.unitConstraint W` satisfies
  `P.form u v = (P.energy u : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v)` for every `v : E` with
  `P.inclusion v ∈ W`, without requiring completeness or closedness of `W`.

## References

* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 4.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.8 and §4.10.
* See `IsCoercive.isLeast_rayleighQuotient` for the coercive real Hilbert-space Rayleigh minimum,
  and Mathlib's `IsSelfAdjoint.eq_smul_self_of_isLocalExtrOn` for the bounded-operator
  Euler–Lagrange analogue on a single inner-product space.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti.CompactFormPair

section UnitConstraint

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The constrained sphere `S_W = {u : E | P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1}` associated to
a submodule `W` of `H`. -/
def unitConstraint (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) : Set E :=
  {u : E | P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1}

/-- Membership in `P.unitConstraint W` means `P.inclusion u ∈ W` and `‖P.inclusion u‖ = 1`. -/
@[simp]
theorem mem_unitConstraint_iff {P : CompactFormPair 𝕜 E H} {W : Submodule 𝕜 H} {u : E} :
    u ∈ P.unitConstraint W ↔ P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1 :=
  Iff.rfl

/-- Every vector in `P.unitConstraint W` has `inner 𝕜 (P.inclusion u) (P.inclusion u) = 1`. -/
theorem inner_inclusion_self_of_mem_unitConstraint {P : CompactFormPair 𝕜 E H}
    {W : Submodule 𝕜 H} {u : E} (hu : u ∈ P.unitConstraint W) :
    inner 𝕜 (P.inclusion u) (P.inclusion u) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu.2, RCLike.ofReal_one, one_pow]

/-- Every vector in `P.unitConstraint W` has `P.inclusion u ≠ 0`. -/
theorem inclusion_ne_zero_of_mem_unitConstraint {P : CompactFormPair 𝕜 E H} {W : Submodule 𝕜 H}
    {u : E} (hu : u ∈ P.unitConstraint W) : P.inclusion u ≠ 0 :=
  norm_ne_zero_iff.mp (hu.2.trans_ne one_ne_zero)

/-- Every vector in `P.unitConstraint W` is nonzero in `E`. -/
theorem ne_zero_of_mem_unitConstraint {P : CompactFormPair 𝕜 E H} {W : Submodule 𝕜 H}
    {u : E} (hu : u ∈ P.unitConstraint W) : u ≠ 0 := by
  rintro rfl
  exact P.inclusion_ne_zero_of_mem_unitConstraint hu (map_zero _)

/-- Monotonicity of `CompactFormPair.unitConstraint` in the constraining submodule `W`. -/
@[gcongr]
theorem unitConstraint_mono (P : CompactFormPair 𝕜 E H) {W₁ W₂ : Submodule 𝕜 H}
    (hW : W₁ ≤ W₂) : P.unitConstraint W₁ ⊆ P.unitConstraint W₂ :=
  fun _ hu => ⟨hW hu.1, hu.2⟩

/-- The constrained sphere of the zero submodule is empty. -/
@[simp]
theorem unitConstraint_bot (P : CompactFormPair 𝕜 E H) : P.unitConstraint ⊥ = ∅ := by
  ext u
  simp only [unitConstraint, mem_ofPred_eq, Submodule.mem_bot, mem_empty_iff_false, iff_false,
    not_and]
  intro h0
  rw [h0, norm_zero]
  exact zero_ne_one

/-- The constrained sphere of `⊤` is the full `H`-unit sphere `{u : E | ‖P.inclusion u‖ = 1}`. -/
@[simp]
theorem unitConstraint_top (P : CompactFormPair 𝕜 E H) :
    P.unitConstraint ⊤ = {u : E | ‖P.inclusion u‖ = 1} := by
  ext u
  simp [unitConstraint]

/-! ### Witness independence and transport of constrained spheres -/

/-- `CompactFormPair.unitConstraint` depends only on `inclusion`, not on the lower-bound witnesses
`(c, ω)`. -/
@[simp]
theorem unitConstraint_ofShiftedLowerBound (inclusion : E →L[𝕜] H)
    (injective : Function.Injective inclusion) (dense : DenseRange inclusion)
    (compact : IsCompactOperator inclusion) (form : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (hermitian : ∀ u v, form u v = star (form v u)) (c ω : ℝ)
    (hc : 0 < c)
    (hbound : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2)
    (W : Submodule 𝕜 H) :
    (ofShiftedLowerBound inclusion injective dense compact form hermitian c ω hc
      hbound).unitConstraint W = {u : E | inclusion u ∈ W ∧ ‖inclusion u‖ = 1} := by
  ext u
  simp [unitConstraint]

/-- Shifting a compact form pair leaves `unitConstraint W` unchanged. -/
@[simp]
theorem unitConstraint_shiftForm (P : CompactFormPair 𝕜 E H) (α : ℝ) (W : Submodule 𝕜 H) :
    (P.shiftForm α).unitConstraint W = P.unitConstraint W := by
  ext u
  simp [unitConstraint]

/-- On `P.unitConstraint W`, shifting by `α` adds the constant `α` to `P.energy`. -/
theorem energy_shiftForm_on_unitConstraint (P : CompactFormPair 𝕜 E H) (α : ℝ)
    {W : Submodule 𝕜 H} {u : E} (hu : u ∈ P.unitConstraint W) :
    (P.shiftForm α).energy u = P.energy u + α := by
  rw [energy_shiftForm, hu.2, one_pow, mul_one]

/-- At an admissible point `u ∈ P.unitConstraint W`, minimizing `(P.shiftForm α).energy` on
`P.unitConstraint W` is equivalent to minimizing `P.energy`. -/
theorem isMinOn_energy_shiftForm_unitConstraint_iff (P : CompactFormPair 𝕜 E H) (α : ℝ)
    {W : Submodule 𝕜 H} {u : E} (hu : u ∈ P.unitConstraint W) :
    IsMinOn (P.shiftForm α).energy (P.unitConstraint W) u ↔
      IsMinOn P.energy (P.unitConstraint W) u := by
  rw [isMinOn_iff, isMinOn_iff]
  refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · have hle := h v hv
    rw [P.energy_shiftForm_on_unitConstraint α hu, P.energy_shiftForm_on_unitConstraint α hv] at hle
    linarith
  · rw [P.energy_shiftForm_on_unitConstraint α hu, P.energy_shiftForm_on_unitConstraint α hv]
    linarith [h v hv]

/-- Unitary transport in `H` pulls back constrained spheres along `U`. -/
@[simp]
theorem unitConstraint_congrH (P : CompactFormPair 𝕜 E H) {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] (U : H ≃ₗᵢ[𝕜] H')
    (W : Submodule 𝕜 H') :
    (P.congrH U).unitConstraint W = P.unitConstraint (W.comap U.toLinearEquiv.toLinearMap) := by
  ext u
  simp [unitConstraint, U.norm_map]

/-- Continuous linear equivalence on `E` pulls back constrained spheres by preimage. -/
@[simp]
theorem unitConstraint_congrE (P : CompactFormPair 𝕜 E H) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (e : E' ≃L[𝕜] E) (W : Submodule 𝕜 H) :
    (P.congrE e).unitConstraint W = e ⁻¹' P.unitConstraint W := by
  ext u
  simp [unitConstraint]

/-- Scalar restriction to `ℝ` preserves `unitConstraint` when `W` is viewed as a real submodule. -/
@[simp]
theorem unitConstraint_restrictScalars (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    letI := InnerProductSpace.rclikeToReal 𝕜 H
    P.restrictScalars.unitConstraint (W.restrictScalars ℝ) = P.unitConstraint W := by
  ext u
  simp [unitConstraint]

/-! ### Normalization, nonemptiness, phase invariance, and Rayleigh quotients -/

/-- Normalizing a vector `v` with `P.inclusion v ∈ W` and `P.inclusion v ≠ 0` places it on
`P.unitConstraint W`. -/
theorem inv_norm_inclusion_smul_mem_unitConstraint {P : CompactFormPair 𝕜 E H}
    {W : Submodule 𝕜 H} {v : E} (hvW : P.inclusion v ∈ W) (hv0 : P.inclusion v ≠ 0) :
    ((‖P.inclusion v‖⁻¹ : ℝ) : 𝕜) • v ∈ P.unitConstraint W := by
  refine ⟨by simpa only [map_smul] using W.smul_mem _ hvW, ?_⟩
  rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]

/-- Energy of the `H`-normalized vector `((‖P.inclusion v‖⁻¹ : ℝ) : 𝕜) • v` equals the Rayleigh
quotient `P.energy v / ‖P.inclusion v‖ ^ 2`. -/
theorem energy_inv_norm_inclusion_smul (P : CompactFormPair 𝕜 E H) (v : E) :
    P.energy (((‖P.inclusion v‖⁻¹ : ℝ) : 𝕜) • v) = P.energy v / ‖P.inclusion v‖ ^ 2 := by
  rw [P.energy_ofReal_smul, inv_pow, div_eq_inv_mul]

/-- `P.unitConstraint W` is nonempty if and only if `W` contains a nonzero vector in the range of
`P.inclusion`. Note that `W ≠ ⊥` alone does not suffice when `W ∩ Set.range P.inclusion = {0}`. -/
theorem unitConstraint_nonempty_iff (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) :
    (P.unitConstraint W).Nonempty ↔ ∃ u : E, P.inclusion u ∈ W ∧ P.inclusion u ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu.1, P.inclusion_ne_zero_of_mem_unitConstraint hu⟩
  · rintro ⟨v, hvW, hv0⟩
    exact ⟨_, P.inv_norm_inclusion_smul_mem_unitConstraint hvW hv0⟩

/-- When `H` is nontrivial, the unconstrained sphere `P.unitConstraint ⊤` is nonempty by density of
`P.inclusion`. -/
theorem unitConstraint_top_nonempty [Nontrivial H] (P : CompactFormPair 𝕜 E H) :
    (P.unitConstraint ⊤).Nonempty := by
  rw [P.unitConstraint_nonempty_iff]
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  by_contra! hzero
  have hmem : x ∈ closure (Set.range P.inclusion) := P.dense x
  have hrange : Set.range P.inclusion ⊆ ({0} : Set H) := by
    rintro _ ⟨u, rfl⟩
    exact hzero u Submodule.mem_top
  exact hx <| Set.mem_singleton_iff.mp <|
    (closure_mono hrange).trans_eq isClosed_singleton.closure_eq hmem

/-- Phase invariance of `P.unitConstraint W`: scaling by a unit scalar `z : 𝕜` (`‖z‖ = 1`)
preserves membership in `P.unitConstraint W`. -/
theorem smul_mem_unitConstraint {P : CompactFormPair 𝕜 E H} {W : Submodule 𝕜 H}
    {z : 𝕜} {u : E} (hz : ‖z‖ = 1) (hu : u ∈ P.unitConstraint W) :
    z • u ∈ P.unitConstraint W := by
  refine ⟨by simpa only [map_smul] using W.smul_mem z hu.1, ?_⟩
  rw [map_smul, norm_smul, hz, one_mul, hu.2]

/-- Phase invariance of `P.energy`: scaling by `z : 𝕜` with `‖z‖ = 1` leaves `P.energy`
unchanged. -/
theorem energy_smul_of_norm_eq_one (P : CompactFormPair 𝕜 E H) {z : 𝕜} (hz : ‖z‖ = 1) (u : E) :
    P.energy (z • u) = P.energy u := by
  rw [P.energy_smul, hz, one_pow, one_mul]

/-- Minimizing `P.energy` on `P.unitConstraint W` at `u` is equivalent to `P.energy u` bounding the
Rayleigh quotient `P.energy v / ‖P.inclusion v‖ ^ 2` from below for all `v` with
`P.inclusion v ∈ W` and `P.inclusion v ≠ 0`. -/
theorem isMinOn_unitConstraint_iff_le_div {P : CompactFormPair 𝕜 E H} {W : Submodule 𝕜 H}
    {u : E} :
    IsMinOn P.energy (P.unitConstraint W) u ↔
      ∀ v : E, P.inclusion v ∈ W → P.inclusion v ≠ 0 →
        P.energy u ≤ P.energy v / ‖P.inclusion v‖ ^ 2 := by
  rw [isMinOn_iff]
  refine ⟨fun hmin v hvW hv0 => ?_, fun hle w hw => ?_⟩
  · rw [← P.energy_inv_norm_inclusion_smul v]
    exact hmin _ (P.inv_norm_inclusion_smul_mem_unitConstraint hvW hv0)
  · have h := hle w hw.1 (P.inclusion_ne_zero_of_mem_unitConstraint hw)
    rwa [hw.2, one_pow, div_one] at h

/-- Homogeneous form of sphere minimization: `IsMinOn P.energy (P.unitConstraint W) u` holds if and
only if `P.energy u * ‖P.inclusion v‖ ^ 2 ≤ P.energy v` for every `v : E` with
`P.inclusion v ∈ W`. -/
theorem isMinOn_unitConstraint_iff_mul_norm_sq_le {P : CompactFormPair 𝕜 E H}
    {W : Submodule 𝕜 H} {u : E} :
    IsMinOn P.energy (P.unitConstraint W) u ↔
      ∀ v : E, P.inclusion v ∈ W → P.energy u * ‖P.inclusion v‖ ^ 2 ≤ P.energy v := by
  rw [isMinOn_unitConstraint_iff_le_div]
  refine ⟨fun h v hvW => ?_, fun h v hvW hv0 => ?_⟩
  · rcases eq_or_ne (P.inclusion v) 0 with hv0 | hv0
    · have hv : v = 0 := P.inclusion_eq_zero_iff.mp hv0
      subst hv
      simp
    · exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv0))).mp (h v hvW hv0)
  · exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv0))).mpr (h v hvW)

/-- At a sphere minimizer `u ∈ P.unitConstraint W`, `P.energy u` is the least value of the Rayleigh
quotient `P.energy v / ‖P.inclusion v‖ ^ 2` over `{v | P.inclusion v ∈ W ∧ P.inclusion v ≠ 0}`. -/
theorem isLeast_rayleighQuotient_of_isMinOn_unitConstraint {P : CompactFormPair 𝕜 E H}
    {W : Submodule 𝕜 H} {u : E} (hu : u ∈ P.unitConstraint W)
    (hmin : IsMinOn P.energy (P.unitConstraint W) u) :
    IsLeast {r : ℝ | ∃ v : E, P.inclusion v ∈ W ∧ P.inclusion v ≠ 0 ∧
      P.energy v / ‖P.inclusion v‖ ^ 2 = r} (P.energy u) := by
  refine ⟨⟨u, hu.1, P.inclusion_ne_zero_of_mem_unitConstraint hu, by simp [hu.2]⟩, ?_⟩
  rintro _ ⟨v, hvW, hv0, rfl⟩
  exact isMinOn_unitConstraint_iff_le_div.mp hmin v hvW hv0

/-! ### Energy lower bounds, closedness, and bounded sublevels -/

/-- Rearranged shifted lower bound `-ω * ‖P.inclusion u‖ ^ 2 + c * ‖u‖ ^ 2 ≤ P.energy u`. -/
theorem HasShiftedLowerBound.neg_mul_norm_sq_add_le_energy {P : CompactFormPair 𝕜 E H}
    {c ω : ℝ} (h : P.HasShiftedLowerBound c ω) (u : E) :
    -ω * ‖P.inclusion u‖ ^ 2 + c * ‖u‖ ^ 2 ≤ P.energy u := by
  linarith [h.bound u]

/-- On `P.unitConstraint W`, any witness `P.HasShiftedLowerBound c ω` bounds `P.energy u` below by
`-ω`. -/
theorem HasShiftedLowerBound.neg_le_energy_of_mem_unitConstraint {P : CompactFormPair 𝕜 E H}
    {c ω : ℝ} (h : P.HasShiftedLowerBound c ω) {W : Submodule 𝕜 H} {u : E}
    (hu : u ∈ P.unitConstraint W) : -ω ≤ P.energy u := by
  have hc : 0 ≤ c * ‖u‖ ^ 2 := mul_nonneg h.pos.le (sq_nonneg _)
  have hb := h.bound u
  rw [hu.2, one_pow, mul_one] at hb
  linarith

/-- On `P.unitConstraint W`, `P.energy` is bounded below by `-P.shift`. -/
theorem neg_shift_le_energy_of_mem_unitConstraint (P : CompactFormPair 𝕜 E H)
    {W : Submodule 𝕜 H} {u : E} (hu : u ∈ P.unitConstraint W) :
    -P.shift ≤ P.energy u :=
  P.hasShiftedLowerBound_coercivityConstant_shift.neg_le_energy_of_mem_unitConstraint hu

/-- The energy values of `P` on `P.unitConstraint W` are bounded below. -/
theorem bddBelow_image_energy_unitConstraint (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) :
    BddBelow (P.energy '' P.unitConstraint W) :=
  ⟨-P.shift, by rintro _ ⟨u, hu, rfl⟩; exact P.neg_shift_le_energy_of_mem_unitConstraint hu⟩

/-- Norm-closedness of `W` in `H` makes `P.unitConstraint W` norm-closed in `E`. -/
theorem isClosed_unitConstraint (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H}
    (hW : IsClosed (W : Set H)) : IsClosed (P.unitConstraint W) :=
  (hW.preimage P.inclusion.continuous).inter
    (isClosed_eq (continuous_norm.comp P.inclusion.continuous) continuous_const)

/-- Quantitative sublevel norm estimate on `P.unitConstraint W`: if `P.HasShiftedLowerBound c ω` and
`P.energy u ≤ b` for `u ∈ P.unitConstraint W`, then `‖u‖ ^ 2 ≤ (b + ω) / c`. -/
theorem HasShiftedLowerBound.norm_sq_le_of_mem_unitConstraint_of_energy_le
    {P : CompactFormPair 𝕜 E H} {c ω b : ℝ} (h : P.HasShiftedLowerBound c ω)
    {W : Submodule 𝕜 H} {u : E} (hu : u ∈ P.unitConstraint W) (hb : P.energy u ≤ b) :
    ‖u‖ ^ 2 ≤ (b + ω) / c := by
  rw [le_div_iff₀ h.pos, mul_comm]
  have hbound := h.bound u
  rw [hu.2, one_pow, mul_one] at hbound
  linarith

/-- Every energy sublevel `{u ∈ P.unitConstraint W | P.energy u ≤ b}` is norm bounded in `E`. -/
theorem hasBoundedSublevelsOn_energy_unitConstraint (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) : HasBoundedSublevelsOn P.energy (P.unitConstraint W) := by
  rw [hasBoundedSublevelsOn_iff]
  intro b
  let R : ℝ := Real.sqrt (max 0 ((b + P.shift) / P.coercivityConstant))
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨R, fun u hu => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq : ‖u‖ ^ 2 ≤ max 0 ((b + P.shift) / P.coercivityConstant) :=
    (P.hasShiftedLowerBound_coercivityConstant_shift.norm_sq_le_of_mem_unitConstraint_of_energy_le
      hu.1 hu.2).trans (le_max_right _ _)
  exact Real.le_sqrt_of_sq_le hsq

/-- The set of minimizers of `P.energy` on `P.unitConstraint W` is norm bounded in `E`. -/
theorem isBounded_minimizers_unitConstraint (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) :
    Bornology.IsBounded {u ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) u} :=
  (P.hasBoundedSublevelsOn_energy_unitConstraint W).isBounded_minimizers

end UnitConstraint

/-! ### Real coercive shifts and existence of constrained Rayleigh minima -/

section RealCoercive

/-- For a real compact form pair with `P.HasShiftedLowerBound c ω`, every shift `α ≥ ω` makes the
shifted bilinear form `(P.shiftForm α).form` coercive (`IsCoercive`). -/
theorem HasShiftedLowerBound.isCoercive_form_shiftForm {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : CompactFormPair ℝ E H} {c ω α : ℝ}
    (h : P.HasShiftedLowerBound c ω) (hωα : ω ≤ α) :
    IsCoercive (P.shiftForm α).form := by
  refine ⟨c, h.pos, fun u => ?_⟩
  have hb := h.mul_norm_sq_le_energy_shiftForm hωα u
  rw [energy_def, RCLike.re_to_real, sq, ← mul_assoc] at hb
  exact hb

/-- Every shift `α ≥ P.shift` of a real compact form pair is coercive (`IsCoercive`). -/
theorem isCoercive_form_shiftForm_of_shift_le {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : CompactFormPair ℝ E H) {α : ℝ} (hα : P.shift ≤ α) :
    IsCoercive (P.shiftForm α).form :=
  P.hasShiftedLowerBound_coercivityConstant_shift.isCoercive_form_shiftForm hα

/-- Over `ℝ`, when `E` is a complete inner-product space and `H` is nontrivial, the least value of
`P.energy` on the unconstrained sphere `P.unitConstraint ⊤` equals
`‖hB.formSolutionOperator P.inclusion‖⁻¹ - α` for any coercive shift `α` of `P`. -/
theorem isLeast_energy_unitConstraint_top_real {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : CompactFormPair ℝ E H) {α : ℝ} (hB : IsCoercive (P.shiftForm α).form) :
    IsLeast (P.energy '' P.unitConstraint ⊤)
      (‖hB.formSolutionOperator P.inclusion‖⁻¹ - α) := by
  obtain ⟨u₀, hu₀⟩ := P.unitConstraint_top_nonempty
  have hJne : P.inclusion ≠ 0 := by
    intro h0
    exact P.inclusion_ne_zero_of_mem_unitConstraint hu₀ (by simp [h0])
  have hsymm : ∀ u v : E, (P.shiftForm α).form u v = (P.shiftForm α).form v u := fun u v => by
    simpa using (P.shiftForm α).hermitian u v
  have hleast := hB.isLeast_rayleighQuotient P.compact hsymm hJne
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv0, hv_eq⟩ := hleast.1
    let w : E := ‖P.inclusion v‖⁻¹ • v
    have hw : w ∈ P.unitConstraint ⊤ :=
      P.inv_norm_inclusion_smul_mem_unitConstraint Submodule.mem_top hv0
    refine ⟨w, hw, ?_⟩
    have hshift : (P.shiftForm α).energy w = P.energy w + α :=
      P.energy_shiftForm_on_unitConstraint α hw
    have hray : (P.shiftForm α).energy w = (P.shiftForm α).form v v / ‖P.inclusion v‖ ^ 2 := by
      have h1 := (P.shiftForm α).energy_inv_norm_inclusion_smul v
      rw [inclusion_shiftForm, RCLike.ofReal_real_eq_id, id_eq] at h1
      rw [h1, energy_def, RCLike.re_to_real]
    linarith
  · rintro _ ⟨u, hu, rfl⟩
    have hmem :
        P.energy u + α ∈
          {r : ℝ | ∃ v : E, P.inclusion v ≠ 0 ∧
            (P.shiftForm α).form v v / ‖P.inclusion v‖ ^ 2 = r} := by
      refine ⟨u, P.inclusion_ne_zero_of_mem_unitConstraint hu, ?_⟩
      have hshift : (P.shiftForm α).form u u = P.energy u + α := by
        have h1 := P.energy_shiftForm_on_unitConstraint α hu
        rwa [energy_def, RCLike.re_to_real] at h1
      rw [hshift, hu.2, one_pow, div_one]
    linarith [hleast.2 hmem]

end RealCoercive

section Existence

section EnergySpace

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Type synonym for `E` carrying the real Hilbert-space norm induced by the coercive shifted form
`(P.shiftForm P.shift).form`. -/
private def EnergySpace (_ : CompactFormPair ℝ E H) : Type _ :=
  E

private instance (P : CompactFormPair ℝ E H) : AddCommGroup P.EnergySpace :=
  inferInstanceAs (AddCommGroup E)

private instance (P : CompactFormPair ℝ E H) : Module ℝ P.EnergySpace :=
  inferInstanceAs (Module ℝ E)

private def energySpaceLinearEquiv (P : CompactFormPair ℝ E H) : P.EnergySpace ≃ₗ[ℝ] E :=
  LinearEquiv.refl ℝ E

@[instance_reducible]
private def energySpaceIPCore (P : CompactFormPair ℝ E H) :
    InnerProductSpace.Core ℝ P.EnergySpace where
  inner x y :=
    (P.shiftForm P.shift).form (P.energySpaceLinearEquiv x) (P.energySpaceLinearEquiv y)
  conj_inner_symm x y := by
    simpa using
      (P.shiftForm P.shift).hermitian (P.energySpaceLinearEquiv y) (P.energySpaceLinearEquiv x)
  re_inner_nonneg x := by
    have hle := P.mul_norm_sq_le_energy_shiftForm le_rfl (P.energySpaceLinearEquiv x)
    rw [energy_def] at hle
    exact (mul_nonneg P.coercivityConstant_pos.le (sq_nonneg _)).trans hle
  definite x hx := by
    have h0 : (P.shiftForm P.shift).energy (P.energySpaceLinearEquiv x) = 0 := by
      simpa [energy_def] using hx
    have hle := P.mul_norm_sq_le_energy_shiftForm le_rfl (P.energySpaceLinearEquiv x)
    rw [h0] at hle
    exact P.energySpaceLinearEquiv.injective <| norm_eq_zero.mp <| sq_eq_zero_iff.mp <|
      le_antisymm (nonpos_of_mul_nonpos_right hle P.coercivityConstant_pos) (sq_nonneg _)
  add_left x y z := by simp
  smul_left x y r := by simp

private instance (P : CompactFormPair ℝ E H) : NormedAddCommGroup P.EnergySpace :=
  P.energySpaceIPCore.toNormedAddCommGroup

private instance (P : CompactFormPair ℝ E H) : InnerProductSpace ℝ P.EnergySpace :=
  InnerProductSpace.ofCore P.energySpaceIPCore.toCore

private theorem norm_sq_energySpace (P : CompactFormPair ℝ E H) (x : P.EnergySpace) :
    ‖x‖ ^ 2 = (P.shiftForm P.shift).energy (P.energySpaceLinearEquiv x) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ), energy_def]
  rfl

private def energySpaceEquiv (P : CompactFormPair ℝ E H) : P.EnergySpace ≃L[ℝ] E :=
  let M : ℝ := max 1 (‖P.form‖ + |P.shift| * ‖P.inclusion‖ ^ 2)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  P.energySpaceLinearEquiv.toContinuousLinearEquivOfBounds
    (Real.sqrt P.coercivityConstant⁻¹) (Real.sqrt M)
    (fun x => by
      rw [← Real.sqrt_sq (norm_nonneg (P.energySpaceLinearEquiv x)),
        ← Real.sqrt_sq (norm_nonneg x),
        ← Real.sqrt_mul (inv_nonneg.mpr P.coercivityConstant_pos.le), P.norm_sq_energySpace x]
      exact Real.sqrt_le_sqrt <| (le_inv_mul_iff₀ P.coercivityConstant_pos).mpr <| by
        simpa [mul_comm] using
          P.mul_norm_sq_le_energy_shiftForm le_rfl (P.energySpaceLinearEquiv x))
    (fun y => by
      rw [← Real.sqrt_sq (norm_nonneg (P.energySpaceLinearEquiv.symm y)),
        ← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_mul hM.le,
        P.norm_sq_energySpace (P.energySpaceLinearEquiv.symm y),
        P.energySpaceLinearEquiv.apply_symm_apply]
      exact Real.sqrt_le_sqrt <| (P.energy_shiftForm_le P.shift y).trans <|
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ‖y‖))

private instance [CompleteSpace E] (P : CompactFormPair ℝ E H) : CompleteSpace P.EnergySpace :=
  ({ toEquiv := P.energySpaceEquiv.toEquiv
     uniformContinuous_toFun := (P.energySpaceEquiv : P.EnergySpace →L[ℝ] E).uniformContinuous
     uniformContinuous_invFun :=
       (P.energySpaceEquiv.symm : E →L[ℝ] P.EnergySpace).uniformContinuous } :
    P.EnergySpace ≃ᵤ E).completeSpace_iff.mpr inferInstance

end EnergySpace

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Existence of the constrained Rayleigh minimum.** On a complete form domain `E`, for every
norm-closed submodule `W` of `H` containing a nonzero image of `P.inclusion`, the quadratic energy
`P.energy` attains its minimum on `P.unitConstraint W`. Neither an inner product on `E` nor
completeness of `H` is required. -/
theorem exists_minimum_on_unitConstraint [CompleteSpace E]
    (P : CompactFormPair 𝕜 E H) (W : Submodule 𝕜 H) (hW : IsClosed (W : Set H))
    (hne : ∃ u : E, P.inclusion u ∈ W ∧ P.inclusion u ≠ 0) :
    ∃ u ∈ P.unitConstraint W, IsMinOn P.energy (P.unitConstraint W) u := by
  let EW : Submodule 𝕜 E := W.comap P.inclusion.toLinearMap
  have : CompleteSpace EW := (hW.preimage P.inclusion.continuous).completeSpace_coe
  let H₁ := (EW.map P.inclusion.toLinearMap).topologicalClosure
  let : NormedSpace ℝ EW := NormedSpace.restrictScalars ℝ 𝕜 EW
  let : InnerProductSpace ℝ H₁ := InnerProductSpace.rclikeToReal 𝕜 H₁
  let Q : CompactFormPair ℝ EW H₁ := (P.restrict EW).restrictScalars
  obtain ⟨u₀, hu₀W, hu₀0⟩ := hne
  have hQ_ne : Q.inclusion ⟨u₀, hu₀W⟩ ≠ 0 := fun h0 =>
    hu₀0 (by simpa [Q, H₁] using congrArg Subtype.val h0)
  have : Nontrivial H₁ := ⟨⟨Q.inclusion ⟨u₀, hu₀W⟩, 0, hQ_ne⟩⟩
  let Q' : CompactFormPair ℝ Q.EnergySpace H₁ := Q.congrE Q.energySpaceEquiv
  have hleast :=
    Q'.isLeast_energy_unitConstraint_top_real (Q'.isCoercive_form_shiftForm_of_shift_le le_rfl)
  obtain ⟨x, hx, hx_eq⟩ := hleast.1
  let v : EW := Q.energySpaceEquiv x
  have hv_norm : ‖P.inclusion (v : E)‖ = 1 := by simpa [Q', Q, H₁, v, unitConstraint] using hx
  refine ⟨v, ⟨v.2, hv_norm⟩, isMinOn_iff.mpr fun w hw => ?_⟩
  let y : Q.EnergySpace := Q.energySpaceEquiv.symm ⟨w, hw.1⟩
  have hy : y ∈ Q'.unitConstraint ⊤ := by simpa [Q', Q, H₁, y, unitConstraint] using hw.2
  have hle : Q'.energy x ≤ Q'.energy y := hx_eq.trans_le (hleast.2 ⟨y, hy, rfl⟩)
  simpa [Q', Q, H₁, v, y] using hle

end Existence

/-! ### The restricted Euler–Lagrange equation -/

section EulerLagrange

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- First variation of `P.energy` along the `H`-normalized arc through `u` in an `H`-orthogonal
direction `v`: when `‖P.inclusion u‖ = 1` and `inner 𝕜 (P.inclusion u) (P.inclusion v) = 0`, the
curve `t ↦ ‖P.inclusion (u + t • v)‖⁻¹ • (u + t • v)` has energy derivative
`2 * RCLike.re (P.form u v)` at `t = 0`. -/
theorem hasDerivAt_energy_normalized_arc_zero (P : CompactFormPair 𝕜 E H) {u v : E}
    (hu : ‖P.inclusion u‖ = 1) (horth : inner 𝕜 (P.inclusion u) (P.inclusion v) = 0) :
    HasDerivAt
      (fun t : ℝ =>
        P.energy (((‖P.inclusion (u + (t : 𝕜) • v)‖⁻¹ : ℝ) : 𝕜) • (u + (t : 𝕜) • v)))
      (2 * RCLike.re (P.form u v)) 0 := by
  let sqFn : ℝ → ℝ := (fun t : ℝ => t) * fun t : ℝ => t
  let w : ℝ → E := fun t => u + (t : 𝕜) • v
  let d : ℝ → ℝ := (fun _ => (1 : ℝ)) + fun t => sqFn t * ‖P.inclusion v‖ ^ 2
  have hnorm_sq : ∀ t, ‖P.inclusion (w t)‖ ^ 2 = d t := fun t => by
    rw [map_add, map_smul, norm_add_sq (𝕜 := 𝕜), inner_smul_right, horth, mul_zero, map_zero,
      mul_zero, add_zero, hu, one_pow, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
    simp [d, sqFn, sq]
  let num : ℝ → ℝ :=
    ((fun _ => P.energy u) + fun t => (2 * RCLike.re (P.form u v)) * t) +
      fun t => P.energy v * sqFn t
  have heq : (fun t : ℝ => P.energy (((‖P.inclusion (w t)‖⁻¹ : ℝ) : 𝕜) • w t)) = num / d := by
    ext t
    simp only [Pi.div_apply, P.energy_inv_norm_inclusion_smul (w t), hnorm_sq t]
    congr 1
    simp only [w, num, sqFn, Pi.add_apply, Pi.mul_apply, P.energy_add, P.energy_ofReal_smul]
    rw [map_smul, smul_eq_mul, RCLike.re_ofReal_mul]
    ring
  have hsq : HasDerivAt sqFn 0 0 := by
    simpa [sqFn] using HasDerivAt.mul (hasDerivAt_id' (0 : ℝ)) (hasDerivAt_id' (0 : ℝ))
  have hlin : HasDerivAt (fun t : ℝ => (2 * RCLike.re (P.form u v)) * t)
      (2 * RCLike.re (P.form u v)) 0 := by
    simpa using HasDerivAt.const_mul (2 * RCLike.re (P.form u v)) (hasDerivAt_id' (0 : ℝ))
  have hnum : HasDerivAt num (2 * RCLike.re (P.form u v)) 0 := by
    simpa [num] using HasDerivAt.add
      (HasDerivAt.add (hasDerivAt_const (0 : ℝ) (P.energy u)) hlin)
      (HasDerivAt.const_mul (P.energy v) hsq)
  have hden : HasDerivAt d 0 0 := by
    simpa [d] using HasDerivAt.add (hasDerivAt_const (0 : ℝ) (1 : ℝ))
      (HasDerivAt.mul_const hsq (‖P.inclusion v‖ ^ 2))
  exact heq ▸ by simpa [d, sqFn] using HasDerivAt.div hnum hden (by simp [d, sqFn])

/-- First variation along a normalized arc `t ↦ ‖j (u + t v)‖⁻¹ • (u + t v)` when `j v ∈ W` is
`H`-orthogonal to `j u`: a local extremum `u` of `P.energy` on `P.unitConstraint W` satisfies
`Re (P.form u v) = 0`. -/
private theorem re_form_eq_zero_of_isLocalExtrOn_unitConstraint_of_inner_eq_zero
    (P : CompactFormPair 𝕜 E H) {W : Submodule 𝕜 H} {u : E}
    (hu : u ∈ P.unitConstraint W) (hextr : IsLocalExtrOn P.energy (P.unitConstraint W) u)
    {v : E} (hvW : P.inclusion v ∈ W) (horth : inner 𝕜 (P.inclusion u) (P.inclusion v) = 0) :
    RCLike.re (P.form u v) = 0 := by
  let w : ℝ → E := fun t => u + (t : 𝕜) • v
  have hw_ne : ∀ t, P.inclusion (w t) ≠ 0 := fun t h0 => by
    have hsq : ‖P.inclusion (w t)‖ ^ 2 = 1 + t ^ 2 * ‖P.inclusion v‖ ^ 2 := by
      rw [map_add, map_smul, norm_add_sq (𝕜 := 𝕜), inner_smul_right, horth, mul_zero, map_zero,
        mul_zero, add_zero, hu.2, one_pow, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
    have hpos : 0 < 1 + t ^ 2 * ‖P.inclusion v‖ ^ 2 :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (sq_nonneg t) (sq_nonneg _))
    linarith [hpos, (by simp [h0] : ‖P.inclusion (w t)‖ ^ 2 = 0), hsq]
  let γ : ℝ → E := fun t => ((‖P.inclusion (w t)‖⁻¹ : ℝ) : 𝕜) • w t
  have hγ_mem : ∀ t, γ t ∈ P.unitConstraint W := fun t =>
    P.inv_norm_inclusion_smul_mem_unitConstraint
      (by simpa only [w, map_add, map_smul] using W.add_mem hu.1 (W.smul_mem (t : 𝕜) hvW))
      (hw_ne t)
  have hγ0 : γ 0 = u := by simp [γ, w, hu.2]
  have hγ_cont : Continuous γ := by
    have hw_cont : Continuous w :=
      continuous_const.add (RCLike.continuous_ofReal.smul continuous_const)
    exact (RCLike.continuous_ofReal.comp
      ((continuous_norm.comp (P.inclusion.continuous.comp hw_cont)).inv₀
        fun t => norm_ne_zero_iff.mpr (hw_ne t))).smul hw_cont
  have htend : Tendsto γ (𝓝 0) (𝓝[P.unitConstraint W] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hγ0 ▸ hγ_cont.continuousAt, Filter.Eventually.of_forall hγ_mem⟩
  have hextr_γ : IsLocalExtr (P.energy ∘ γ) 0 :=
    (hγ0.symm ▸ hextr).comp_of_tendsto (hγ0.symm ▸ htend)
  linarith [hextr_γ.hasDerivAt_eq_zero (P.hasDerivAt_energy_normalized_arc_zero hu.2 horth)]

/-- **Restricted Euler–Lagrange equation at a local extremum.** Any local extremum
`u ∈ P.unitConstraint W` of `P.energy` on `P.unitConstraint W` satisfies
`P.form u v = (P.energy u : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v)` for every `v : E` with
`P.inclusion v ∈ W`. Neither completeness nor closedness of `W` is required. -/
theorem equation_of_isLocalExtrOn_unitConstraint (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) (u : E) (hu : u ∈ P.unitConstraint W)
    (hextr : IsLocalExtrOn P.energy (P.unitConstraint W) u) :
    ∀ v : E, P.inclusion v ∈ W →
      P.form u v = (P.energy u : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v) := by
  have horth_zero : ∀ w : E, P.inclusion w ∈ W →
      inner 𝕜 (P.inclusion u) (P.inclusion w) = 0 → P.form u w = 0 := by
    intro w hwW hwu
    let z : 𝕜 := star (P.form u w)
    have hzwW : P.inclusion (z • w) ∈ W := by
      simpa only [map_smul] using W.smul_mem z hwW
    have hzw_orth : inner 𝕜 (P.inclusion u) (P.inclusion (z • w)) = 0 := by
      rw [map_smul, inner_smul_right, hwu, mul_zero]
    have hre := P.re_form_eq_zero_of_isLocalExtrOn_unitConstraint_of_inner_eq_zero
      hu hextr hzwW hzw_orth
    have hnorm : ‖P.form u w‖ ^ 2 = 0 := by
      have hmul : P.form u (z • w) = ((‖P.form u w‖ ^ 2 : ℝ) : 𝕜) := by
        rw [map_smul, smul_eq_mul]
        simpa [z, RCLike.star_def] using RCLike.conj_mul (P.form u w)
      simpa [hmul] using hre
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  intro v hvW
  let c : 𝕜 := inner 𝕜 (P.inclusion u) (P.inclusion v)
  let v₀ : E := v - c • u
  have hv₀W : P.inclusion v₀ ∈ W := by
    simpa only [v₀, map_sub, map_smul] using W.sub_mem hvW (W.smul_mem c hu.1)
  have hv₀_orth : inner 𝕜 (P.inclusion u) (P.inclusion v₀) = 0 := by
    rw [map_sub, map_smul, inner_sub_right, inner_smul_right,
      P.inner_inclusion_self_of_mem_unitConstraint hu, mul_one, sub_self]
  have hform_v₀ : P.form u v₀ = 0 := horth_zero v₀ hv₀W hv₀_orth
  have hform_sub : P.form u v - c * P.form u u = 0 := by
    simpa [v₀, map_sub, map_smul, smul_eq_mul] using hform_v₀
  rw [sub_eq_zero.mp hform_sub, P.form_self_eq_energy u, mul_comm]

/-- **Restricted Euler–Lagrange equation of a sphere minimizer.** For any minimizer
`u ∈ P.unitConstraint W` of `P.energy` on `P.unitConstraint W`,
`P.form u v = (P.energy u : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v)` holds for every `v : E`
with `P.inclusion v ∈ W`. -/
theorem equation_of_constrained_minimum (P : CompactFormPair 𝕜 E H)
    (W : Submodule 𝕜 H) (u : E) (hu : u ∈ P.unitConstraint W)
    (hmin : IsMinOn P.energy (P.unitConstraint W) u) :
    ∀ v : E, P.inclusion v ∈ W →
      P.form u v = (P.energy u : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v) :=
  P.equation_of_isLocalExtrOn_unitConstraint W u hu (Or.inl hmin.isLocalMinOn)

end EulerLagrange

end TauCeti.CompactFormPair

end
