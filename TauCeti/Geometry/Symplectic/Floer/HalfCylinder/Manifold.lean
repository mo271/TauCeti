/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.PeriodicOrbitLimit
public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.Analysis.Complex.Tietze
import TauCeti.Geometry.Manifold.Immersion.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Instances.AddCircle.PeriodicExtension
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Periodic orbits at the ends of finite-energy Floer half-cylinders in a manifold

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a symplectic manifold,
`H : ℝ → M → ℝ` a `C¹` Hamiltonian, `1`-periodic in time, and `u` a `C¹` solution of the Floer
equation

`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`

on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact set `K ⊆ M`, for
the cylindrical perturbation `K = H_t dt` and almost complex structures `J z` on the tangent
spaces `T_{u z} M`. This file shows that if `u` has finite energy, there are `s_n → ∞` such that
the loops `t ↦ u(s_n, t)` converge uniformly to a `1`-periodic orbit `x` of the Hamiltonian vector
field in `K`, along which the `L²` norms of the defects `∂_t u - X_{H_t}(u)` tend to `0`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, in the
namespace `TauCeti.SmoothTwoForm`). On a compact manifold `K` can be the whole manifold
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer`).
This is the first step of Floer breaking at an end of a Floer cylinder or a pair of pants in a
closed manifold; `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` proves it for a symplectic
vector space.

Measuring the convergence needs a metric near `K`. It is measured through a `C¹` map `e : M → F`
into a finite-dimensional normed space, injective on `K` and with injective differential at the
points of `K`; on a compact Hausdorff manifold such a map exists by Mathlib's
`exists_embedding_euclidean_of_compact`. Since `K` is compact, `e` restricts to a closed embedding
of `K`, so uniform convergence of the loops `e ∘ u(s_n, ·)` is uniform convergence in `K`, and it
gives pointwise convergence `u(s_n, t) → x(t)` in `M`. Uniform tameness and the defects are also
measured through `e`: `c ‖d e v‖² ≤ ω(v, J z v)` for a constant `c > 0`.

The proof transports the problem to `F`, where the vector-space theory applies.

* The pushforward `d e (X_{H_t})` of the Hamiltonian vector field is a continuous periodic field
  on the image `e(K)`, and extends to a continuous periodic field `Y` on all of `F` by the Tietze
  extension theorem (`Topology.IsClosedEmbedding.exists_continuous_periodic_extension`).
* The defect `∂_t (e ∘ u) - Y(e ∘ u)` of the loops of `e ∘ u` is `d e (∂_t u - X_{H_t}(u))`
  (`TauCeti.sliceDefect_comp_eq_mvfderiv_sub`). By the Floer equation, the energy density is
  `ω(η, J η)` for `η = ∂_t u - X_{H_t}(u)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_zero_left_eq_symplecticFormAt`), so
  the squared norm of the defect is at most the energy density divided by `c`, and has finite
  integral (`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`).
* Loops with square-integrable defect in the compact set `e(K)` accumulate at a periodic solution
  `y` of `y' = Y(t, y)`
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`).
  The limit lies in the closed set `e(K)`, so `y = e ∘ x` for a continuous periodic loop `x` in
  `K`, and there `y' = d e (X_{H_t}(x))`.
* Since `d e` is injective, `x` is differentiable with velocity `X_{H_t}(x)`
  (`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`), so `x` is a `1`-periodic orbit.

When `e ∘ u` also has bounded derivative on the half-cylinder and each `1`-periodic orbit of `X_H`
in `K` is isolated — in particular when `H` is `C²` on a Hausdorff boundaryless manifold and the
initial point of every `1`-periodic orbit in `K` is a nondegenerate fixed point of the time-one map
(`TauCeti.eventually_eq_of_mem_periodicSolutions_of_isNondegenerateFixedPt`) — the loops
`t ↦ u(s, t)` converge as `s → ∞` to a single `1`-periodic orbit, uniformly after applying `e` and
pointwise in `M`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`, and
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer` on a compact
manifold). Uniform tameness `c ‖d e v‖² ≤ ω(v, J v)` holds automatically on `D × K` for any
continuous family of `ω`-tamed almost complex structures over a compact parameter set `D` and
compact `K` (`IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le`), and hence for all time
for any `1`-periodic continuous family of `ω`-tamed smooth almost complex structures
(`IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le_of_periodic`).

## Main results

* `TauCeti.sliceDefect_comp_eq_mvfderiv_sub`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`: the loop defect of
  `e ∘ u` is `d e (∂_t u - X_{H_t}(u))`, and its `L²` norm is bounded by `c⁻¹` times the Floer
  energy.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le_of_periodic`:
  uniform tameness relative to `e` for continuous compact or `1`-periodic families of `ω`-tamed
  almost complex structures.
* `exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`,
  `exists_mem_periodicSolutions_tendstoUniformly_of_floer` (in
  `TauCeti.SmoothTwoForm.IsNondegenerate`): subsequential convergence of the slices of a
  finite-energy Floer half-cylinder to a `1`-periodic orbit.
* `exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated`,
  `exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`,
  `exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer` (in
  `TauCeti.SmoothTwoForm.IsNondegenerate`): convergence as `s → ∞` to an isolated or nondegenerate
  `1`-periodic orbit when `e ∘ u` has bounded derivative.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Bundle Set Filter Topology MeasureTheory Function
open scoped Manifold ENNReal

namespace TauCeti

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}

/-- Let `e : M → F` be differentiable at `u z`, and let `Y` be a time-dependent field on `F` whose
value at `e (u z)` is the pushforward `d e v` of a tangent vector `v` at `u z`. Then the defect
`∂_t (e ∘ u) - Y(e ∘ u)` of the loops of `e ∘ u` at `z` is `d e (∂_t u - v)`. -/
theorem sliceDefect_comp_eq_mvfderiv_sub {u : ℝ × ℝ → M} {z : ℝ × ℝ} {Y : ℝ → F → F}
    {v : TangentSpace I (u z)} (he : MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hY : Y z.2 (e (u z)) = mvfderiv I e (u z) v) :
    sliceDefect Y (e ∘ u) z =
      mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - v) := by
  -- The chain rule for `e ∘ u`, read as a map between vector spaces.
  have hd : fderiv ℝ (e ∘ u) z stdComplexLineImag =
      mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) :=
    (mvfderiv_eq_fderiv_apply (e ∘ u) z stdComplexLineImag).symm.trans
      (mvfderiv_comp_apply z he hu _)
  rw [sliceDefect_def, ← stdComplexLineImag_eq, hd, comp_apply, hY, map_sub]

namespace SmoothTwoForm

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}

/-- **The energy controls the defect, measured through `e`.** Let `u` solve the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on a measurable set `U`, where `e : M → F` and `u` are
differentiable, with almost complex structures satisfying `c ‖d e v‖² ≤ ω(v, J z v)`, and let `Y`
be a time-dependent field on `F` agreeing with the pushforward `d e (X_{H_t})` at the points of
`e ∘ u` over `U`. Then the integral over `U` of the squared defect `‖∂_t (e ∘ u) - Y(e ∘ u)‖²` of
the loops of `e ∘ u` is at most `1 / c` times the energy over `U`. -/
theorem IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {u : ℝ × ℝ → M} {Y : ℝ → F → F}
    (he : ∀ z ∈ U, MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : ∀ z ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hY : ∀ z ∈ U, Y z.2 (e (u z)) = mvfderiv I e (u z) (ω.hamiltonianVectorField (H z.2) (u z)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ∫⁻ z in U, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≤
      ENNReal.ofReal c⁻¹ *
        ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hU fun z hz ↦ ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [sliceDefect_comp_eq_mvfderiv_sub (he z hz) (hu z hz) (hY z hz),
    hω.floerEnergyDensity_zero_left_eq_symplecticFormAt (hfloer z hz), le_inv_mul_iff₀ hc]
  exact hJc z hz _

/-- **Finite energy gives a square-integrable defect, measured through `e`.** Under the hypotheses
of `TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`, if the energy
over `U` is finite, then so is the integral over `U` of `‖∂_t (e ∘ u) - Y(e ∘ u)‖²`. -/
theorem IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_ne_top (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {u : ℝ × ℝ → M} {Y : ℝ → F → F}
    (he : ∀ z ∈ U, MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : ∀ z ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hY : ∀ z ∈ U, Y z.2 (e (u z)) = mvfderiv I e (u z) (ω.hamiltonianVectorField (H z.2) (u z)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in U,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∫⁻ z in U, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ :=
  ((hω.lintegral_norm_sq_sliceDefect_comp_le hU he hu hY J hc hJc hfloer).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE.lt_top)).ne

section UniformTameness

variable [FiniteDimensional ℝ E]

/-- Along a continuous family `J` of almost complex structures, the pairing `ω_x(v, J(s, x) v)` is
continuous in the fiber coordinate of a local trivialization of `TM`. -/
private theorem continuousOn_symplecticFormAt_apply (hω : ω.IsNondegenerate)
    {P : Type*} [TopologicalSpace P] {D : Set P} {U L : Set M} (α : M)
    (hLU : L ⊆ U ∩ (trivializationAt E (TangentSpace I) α).baseSet)
    {J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ContinuousOn (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      q.2 (J q.1 q.2).toLinearMap.toContinuousLinearMap) (D ×ˢ U)) :
    ContinuousOn (fun r : (P × M) × E ↦
      hω.symplecticFormAt r.1.2 ((trivializationAt E (TangentSpace I) α).symm r.1.2 r.2)
        (J r.1.1 r.1.2 ((trivializationAt E (TangentSpace I) α).symm r.1.2 r.2)))
      ((D ×ˢ L) ×ˢ univ) := by
  have hv : ContinuousOn (fun r : (P × M) × E ↦ TotalSpace.mk' E r.1.2
      ((trivializationAt E (TangentSpace I) α).symm r.1.2 r.2)) ((D ×ˢ L) ×ˢ univ) :=
    (trivializationAt E (TangentSpace I) α).continuousOn_symm.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun (r : (P × M) × E) hr ↦ ⟨(hLU hr.1.2).2, mem_univ _⟩
  have hJv : ContinuousOn (fun r : (P × M) × E ↦ TotalSpace.mk' E r.1.2
      (J r.1.1 r.1.2 ((trivializationAt E (TangentSpace I) α).symm r.1.2 r.2)))
      ((D ×ˢ L) ×ˢ univ) :=
    (hJ.comp continuousOn_fst (s := (D ×ˢ L) ×ˢ univ)
      fun r hr ↦ ⟨hr.1.1, (hLU hr.1.2).1⟩).clm_bundle_apply hv
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le zero_le
  intro r₀ hr₀
  have h := hω₀.tendsto_apply (l := 𝓝[(D ×ˢ L) ×ˢ univ] r₀) (x := fun r ↦ r.1.2)
    (v := fun r ↦ ![(trivializationAt E (TangentSpace I) α).symm r.1.2 r.2,
      J r.1.1 r.1.2 ((trivializationAt E (TangentSpace I) α).symm r.1.2 r.2)])
    (v₀ := ![(trivializationAt E (TangentSpace I) α).symm r₀.1.2 r₀.2,
      J r₀.1.1 r₀.1.2 ((trivializationAt E (TangentSpace I) α).symm r₀.1.2 r₀.2)])
    continuousWithinAt_fst.snd (Fin.forall_fin_two.2 ⟨hv r₀ hr₀, hJv r₀ hr₀⟩)
  simpa only [ContinuousWithinAt, IsNondegenerate.symplecticFormAt_apply,
    SmoothBundleForm.eval₂_apply] using h

omit [FiniteDimensional ℝ E] in
/-- In a local trivialization of `TM`, `mvfderiv I e` evaluated on `eT.symm x a` is continuous for
a `C¹` map `e : M → F`. -/
private theorem continuousOn_mvfderiv_symm_aux (he : ContMDiff I 𝓘(ℝ, F) 1 e) (α : M)
    {L : Set M} (hL : L ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn (fun p : M × E ↦ mvfderiv I e p.1
      ((trivializationAt E (TangentSpace I) α).symm p.1 p.2))
      (L ×ˢ Metric.sphere (0 : E) 1) := by
  intro p₀ hp₀
  have hA : ContinuousAt (inTangentCoordinates I 𝓘(ℝ, F) id e (mfderiv I 𝓘(ℝ, F) e) p₀.1) p₀.1 :=
    ((he p₀.1).mfderiv_const (m := 0) (zero_add 1).le).continuousAt
  have hW : (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) p₀.1).baseSet ∈ 𝓝 p₀.1 :=
    ((trivializationAt E (TangentSpace I) α).open_baseSet.inter
      (trivializationAt E (TangentSpace I) p₀.1).open_baseSet).mem_nhds
      ⟨hL hp₀.1, FiberBundle.mem_baseSet_trivializationAt E _ p₀.1⟩
  have hC : ContinuousAt (fun x ↦ ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) p₀.1) x : E →L[ℝ] E)) p₀.1 :=
    (continuousOn_coordChange ℝ (trivializationAt E (TangentSpace I) α)
      (trivializationAt E (TangentSpace I) p₀.1)).continuousAt hW
  have hg : ContinuousAt (fun p : M × E ↦
      inTangentCoordinates I 𝓘(ℝ, F) id e (mfderiv I 𝓘(ℝ, F) e) p₀.1 p.1
        (((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) p₀.1) p.1 : E →L[ℝ] E) p.2)) p₀ :=
    (hA.comp continuousAt_fst).clm_apply ((hC.comp continuousAt_fst).clm_apply continuousAt_snd)
  refine (hg.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [continuousAt_fst.preimage_mem_nhds hW] with p hp
  rw [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  dsimp only [id_eq, ContinuousLinearEquiv.coe_coe]
  rw [(trivializationAt E (TangentSpace I) α).coordChangeL_apply _ hp,
    (trivializationAt E (TangentSpace I) p₀.1).symmL_apply hp.2,
    (trivializationAt E (TangentSpace I) p₀.1).symm_apply_apply_mk hp.2,
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (e p₀.1)).continuousLinearMapAt_apply ℝ,
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (e p₀.1)).linearMapAt_apply,
    trivializationAt_model_space_apply, mvfderiv_apply_eq_mfderiv_apply]
  simp only [TangentBundle.trivializationAt_baseSet, chartAt_self_eq,
    OpenPartialHomeomorph.refl_source, mem_univ, ↓reduceIte]
  rfl

/-- On a compact subset `L` of the trivialization domain at `α`, a continuous tamed family of
almost complex structures satisfies `c ‖d e v‖² ≤ ω(v, J s x v)` for one `c > 0`. -/
private theorem exists_pos_local_mul_norm_mvfderiv_sq_le_aux (hω : ω.IsNondegenerate)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {P : Type*} [TopologicalSpace P] {D : Set P} (hD : IsCompact D)
    {U : Set M} (α : M) {L : Set M} (hLc : IsCompact L)
    (hLU : L ⊆ U ∩ (trivializationAt E (TangentSpace I) α).baseSet)
    {J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ContinuousOn (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      q.2 (J q.1 q.2).toLinearMap.toContinuousLinearMap) (D ×ˢ U))
    (hJt : ∀ s ∈ D, ∀ x ∈ U, (hω.symplecticFormAt x).Tames (J s x)) :
    ∃ c > 0, ∀ s ∈ D, ∀ x ∈ L, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J s x v) := by
  -- Minimize `ω(v, J v)` and bound `‖d e v‖` on the unit sphere in the fiber coordinate.
  have hSc : IsCompact (((D ×ˢ L) ×ˢ Metric.sphere (0 : E) 1)) :=
    (hD.prod hLc).prod (isCompact_sphere 0 1)
  have hpos : ∀ r ∈ (D ×ˢ L) ×ˢ Metric.sphere (0 : E) 1, 0 < hω.symplecticFormAt r.1.2
      ((trivializationAt E (TangentSpace I) α).symm r.1.2 r.2)
      (J r.1.1 r.1.2 ((trivializationAt E (TangentSpace I) α).symm r.1.2 r.2)) :=
    fun r hr ↦ hJt r.1.1 hr.1.1 r.1.2 (hLU hr.1.2).1 _ <|
      ((trivializationAt E (TangentSpace I) α).symm_apply_ne_zero_iff ℝ (hLU hr.1.2).2).2
        (ne_zero_of_mem_sphere one_ne_zero ⟨r.2, hr.2⟩)
  obtain ⟨c₁, hc₁, hmin⟩ := hSc.exists_forall_le'
    ((continuousOn_symplecticFormAt_apply hω α hLU hJ).mono (prod_mono le_rfl (subset_univ _))) hpos
  obtain ⟨M₀, hM₀⟩ := (hLc.prod (isCompact_sphere 0 1)).exists_bound_of_continuousOn
    (continuousOn_mvfderiv_symm_aux he α fun _ hx ↦ (hLU hx).2)
  set B := max M₀ 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right M₀ 1)
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  refine ⟨c₁ / B ^ 2, div_pos hc₁ hB2, fun s hs x hxL v ↦ ?_⟩
  have hxB : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := (hLU hxL).2
  obtain ⟨a, hva⟩ : ∃ a : E, (trivializationAt E (TangentSpace I) α).symm x a = v :=
    ⟨(trivializationAt E (TangentSpace I) α ⟨x, v⟩).2,
      (trivializationAt E (TangentSpace I) α).symm_apply_apply_mk hxB v⟩
  rcases eq_or_ne a 0 with rfl | ha
  · have hv0 : v = 0 := by
      rw [← hva, ← (trivializationAt E (TangentSpace I) α).symmL_apply (R := ℝ) hxB, map_zero]
    have h0 : hω.symplecticFormAt x 0 (J s x 0) = 0 :=
      (hω.symplecticFormAt x).toBilinForm.map_zero₂ _
    rw [hv0, map_zero, norm_zero, zero_pow two_ne_zero, mul_zero, h0]
  · have hn : 0 < ‖a‖ := norm_pos_iff.2 ha
    have hu : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : E) 1 := by simp [norm_smul, hn.ne']
    have hvu : (trivializationAt E (TangentSpace I) α).symm x (‖a‖⁻¹ • a) = ‖a‖⁻¹ • v := by
      rw [(trivializationAt E (TangentSpace I) α).symm_apply_smul hxB, hva]
    have h1 : c₁ ≤ hω.symplecticFormAt x (‖a‖⁻¹ • v) (J s x (‖a‖⁻¹ • v)) := by
      simpa only [hvu] using hmin ((s, x), ‖a‖⁻¹ • a) ⟨⟨hs, hxL⟩, hu⟩
    have h2 : ‖mvfderiv I e x (‖a‖⁻¹ • v)‖ ≤ B := by
      refine le_trans ?_ (le_max_left M₀ 1)
      simpa only [hvu] using hM₀ (x, ‖a‖⁻¹ • a) ⟨hxL, hu⟩
    have hbilin : hω.symplecticFormAt x (‖a‖⁻¹ • v) (J s x (‖a‖⁻¹ • v)) =
        ‖a‖⁻¹ * (‖a‖⁻¹ * hω.symplecticFormAt x v (J s x v)) := by
      rw [(J s x).apply_smul]
      change (hω.symplecticFormAt x).toBilinForm (‖a‖⁻¹ • v) (‖a‖⁻¹ • J s x v) = _
      rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hbilin, le_inv_mul_iff₀ hn, le_inv_mul_iff₀ hn] at h1
    rw [ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn.le),
      inv_mul_le_iff₀ hn] at h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hB2]
    calc c₁ * ‖mvfderiv I e x v‖ ^ 2
        ≤ c₁ * (‖a‖ * B) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2)
          hc₁.le
      _ = (‖a‖ * (‖a‖ * c₁)) * B ^ 2 := by ring
      _ ≤ hω.symplecticFormAt x v (J s x v) * B ^ 2 := mul_le_mul_of_nonneg_right h1 hB2.le

/-- **Uniform tameness relative to a `C¹` map over a compact family.** Let `ω` be a nondegenerate
two-form on a finite-dimensional manifold `M`, `e : M → F` a `C¹` map into a normed space, `D` a
compact parameter set and `K ⊆ U` a compact subset of an open set `U ⊆ M`. Let `J(s, x)` be a
family of almost complex structures on `T_x M`, continuous on `D × U` as a section of `End(TM)` and
tamed by `ω` on `D × U`. Then there is `c > 0` such that `c ‖d e_x v‖² ≤ ω_x(v, J(s, x) v)` for all
`s ∈ D`, `x ∈ K` and `v ∈ T_x M`. Neither Hausdorffness of `M` nor injectivity of `d e` is
needed. -/
theorem IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le
    (hω : ω.IsNondegenerate) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {P : Type*} [TopologicalSpace P]
    {D : Set P} (hD : IsCompact D) {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ContinuousOn (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      q.2 (J q.1 q.2).toLinearMap.toContinuousLinearMap) (D ×ˢ U))
    (hJt : ∀ s ∈ D, ∀ x ∈ U, (hω.symplecticFormAt x).Tames (J s x)) :
    ∃ c > 0, ∀ s ∈ D, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J s x v) := by
  have : LocallyCompactSpace HM := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace HM M
  -- Around each point of `K`, choose a compact neighborhood inside `U` and a local trivialization.
  have hloc : ∀ α ∈ K, ∃ L : Set M, α ∈ interior L ∧ ∃ c > 0,
      ∀ s ∈ D, ∀ x ∈ L, ∀ v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J s x v) := by
    intro α hα
    obtain ⟨L, hLc, hαL, hLU⟩ := exists_compact_subset
      (hU.inter (trivializationAt E (TangentSpace I) α).open_baseSet)
      ⟨hKU hα, FiberBundle.mem_baseSet_trivializationAt E _ α⟩
    exact ⟨L, hαL, exists_pos_local_mul_norm_mvfderiv_sq_le_aux hω he hD α hLc hLU hJ hJt⟩
  choose! L hαL c hc hcL using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun α ↦ interior (L α))
    fun α hα ↦ isOpen_interior.mem_nhds (hαL α hα)
  -- Take the positive minimum of the local constants over the finite subcover (or `1` if empty).
  rcases t.eq_empty_or_nonempty with rfl | ht
  · refine ⟨1, zero_lt_one, fun _ _ x hxK ↦ ?_⟩
    exact False.elim (by simpa using hcov hxK)
  · refine ⟨t.inf' ht c, (Finset.lt_inf'_iff ht).2 fun α hα ↦ hc α (htK α hα),
      fun s hs x hxK v ↦ ?_⟩
    obtain ⟨α, hαt, hxα⟩ := mem_iUnion₂.1 (hcov hxK)
    exact (mul_le_mul_of_nonneg_right (Finset.inf'_le c hαt) (sq_nonneg _)).trans
      (hcL α (htK α hαt) s hs x (interior_subset hxα) v)

/-- **Uniform tameness for a `1`-periodic family of smooth almost complex structures.** Let
`J : ℝ → SmoothAlmostComplexStructure I M` be `1`-periodic, `ω`-tamed for every `t`, and continuous
on `ℝ × U` as a section of `End(TM)` over an open neighborhood `U` of a compact set `K ⊆ M`. Then
for any `C¹` map `e : M → F` there is `c > 0` such that `c ‖d e_x v‖² ≤ ω_x(v, J_t(x) v)` for all
`t : ℝ`, `x ∈ K` and `v ∈ T_x M`. -/
theorem IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le_of_periodic
    (hω : ω.IsNondegenerate) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {J : ℝ → SmoothAlmostComplexStructure I M}
    (hJp : Periodic J 1)
    (hJc : ContinuousOn (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      q.2 ((J q.1).toEndomorphism q.2)) (univ ×ˢ U))
    (hJt : ∀ t, ω.Tames (J t)) :
    ∃ c > 0, ∀ t, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤
        hω.symplecticFormAt x v ((J t).almostComplexStructureAt x v) := by
  have hJeq (q : ℝ × M) :
      ((J q.1).almostComplexStructureAt q.2).toLinearMap.toContinuousLinearMap =
        (J q.1).toEndomorphism q.2 := by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    exact ContinuousLinearMap.ext fun _ ↦ rfl
  obtain ⟨c, hc, hle⟩ := hω.exists_pos_forall_mul_norm_mvfderiv_sq_le he (isCompact_Icc (a := 0)
    (b := 1)) hK hU hKU (J := fun t x ↦ (J t).almostComplexStructureAt x)
    ((hJc.mono (prod_mono (subset_univ (Icc (0 : ℝ) 1)) le_rfl)).congr fun q _ ↦ by rw [hJeq])
    fun t _ x _ ↦ hω.tames_iff.1 (hJt t) x
  refine ⟨c, hc, fun t x hxK v ↦ ?_⟩
  have hfract : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hper : J (Int.fract t) = J t := by
    have h := hJp.sub_int_mul_eq (x := t) ⌊t⌋
    rwa [mul_one, ← Int.fract] at h
  rw [← hper]
  exact hle (Int.fract t) hfract x hxK v

end UniformTameness

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- Pull a `1`-periodic solution of the extended field `Y` in `e(K)` back to a `1`-periodic orbit
of `X_H` in `K` along an injective `C¹` immersion `e`. -/
private theorem exists_mem_periodicSolutions_of_hasDerivAt (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {Y : ℝ → F → F}
    (hYe : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    {x' : ℝ → F} (hx'per : Periodic x' 1) (hx' : ∀ t, HasDerivAt x' (Y t (x' t)) t)
    (hx'K : ∀ t, x' t ∈ e '' K) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ e ∘ x = x' := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.continuous.comp continuous_subtype_val).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  choose x hxK hx using hx'K
  have hex : e ∘ x = x' := funext hx
  have hxc : Continuous x := by
    have h : Continuous fun t ↦ (⟨x t, hxK t⟩ : K) :=
      hemb.isEmbedding.continuous_iff.2 <| hex ▸
        continuous_iff_continuousAt.2 fun t ↦ (hx' t).continuousAt
    exact continuous_subtype_val.comp h
  refine ⟨x, mem_periodicSolutions.2 ⟨fun t ↦ ?_, fun t ↦ he_inj (hxK _) (hxK _)
    (by rw [hx, hx, hx'per t])⟩, hxK, hex⟩
  refine hxc.continuousAt.hasMFDerivAt_of_hasDerivAt_comp (hde _ (hxK t)) ?_
  rw [hex, ← hYe t _ (hxK t), hx]
  exact hx' t

/-- Extend the pushforward `d e (X_{H_t})` from `e(K)` to a continuous `1`-periodic field `Y` on
`F` whose defect along `e ∘ u` is square-integrable over `(a, ∞) × [0, 1]`. -/
private theorem exists_extension_lintegral_norm_sq_sliceDefect_comp_ne_top
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    IsClosedEmbedding (fun p : K ↦ e p) ∧
      ∃ Y : ℝ → F → F, Continuous (uncurry Y) ∧ (∀ v, Periodic (fun t ↦ Y t v) 1) ∧
        (∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p)) ∧
        ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.continuous.comp continuous_subtype_val).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  -- The pushforward `(t, p) ↦ d e_p (X_{H_t}(p))` of the Hamiltonian vector field is continuous.
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
  obtain ⟨Y, hYc, hYper, hYe⟩ := hemb.exists_continuous_periodic_extension
    (f := fun t (p : K) ↦ mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    (T := 1) (hXe.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    fun p t ↦ congrArg (fun h ↦ mvfderiv I e p (ω.hamiltonianVectorField h p)) (hHper t)
  have hYe' : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p) :=
    fun t p hp ↦ hYe t ⟨p, hp⟩
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  refine ⟨hemb, Y, hYc, hYper, hYe',
    hω.lintegral_norm_sq_sliceDefect_comp_ne_top (measurableSet_Ioi.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
      (fun z hz ↦ (hu.contMDiffAt (hU.mem_nhds ⟨hz.1, mem_univ _⟩)).mdifferentiableAt one_ne_zero)
      (fun z hz ↦ hYe' _ _ (huK z.1 hz.1 z.2)) J hc hJc hfloer hE⟩

/-- **Periodic orbits at the end of a finite-energy Floer half-cylinder in a manifold.** Let `ω`
be a nondegenerate two-form on a manifold `M`, `H` a `C¹` Hamiltonian, `1`-periodic in time, and
let `u` be `C¹` on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact
set `K`, solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]`. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `K` and with
injective differential at the points of `K`, and suppose that the almost complex structures are
uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u`
over `(a, ∞) × [0, 1]` is finite, then there are `s_n → ∞`, with `s_n > a`, such that the loops
`t ↦ u(s_n, t)` converge to a `1`-periodic orbit `x` of the Hamiltonian vector field in `K`,
pointwise in `M` and uniformly after applying `e`, and the `L²` norms of their defects
`d e (∂_t u - X_{H_t}(u))` tend to `0`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (φ n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (φ n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (φ n, t)))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨hemb, Y, hYc, hYper, hYe', hfin⟩ :=
    exists_extension_lintegral_norm_sq_sliceDefect_comp_ne_top hω hH hHper he hK he_inj hu huK J
      hc hJc hfloer hE
  -- The loops of `e ∘ u` accumulate at a periodic solution of `y' = Y(t, y)` in `e(K)`.
  obtain ⟨x', hx'per, hx', φ, hφa, hφ, hconv, hL2⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top
      (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
      (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin
  obtain ⟨x, hx, hxK, hex⟩ := exists_mem_periodicSolutions_of_hasDerivAt he hK he_inj hde hYe'
    hx'per hx' fun t ↦ (hK.image he.continuous).isClosed.mem_of_tendsto (hconv.tendsto_at t)
      (Eventually.of_forall fun n ↦ mem_image_of_mem e (huK _ (hφa n) t))
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  refine ⟨x, hx, hxK, φ, hφa, hφ, hex ▸ hconv, fun t ↦ ?_,
    hL2.congr fun n ↦ intervalIntegral.integral_congr fun t _ ↦ ?_⟩
  · -- Inside `K`, convergence is measured by `e`.
    have h : Tendsto (fun n ↦ (⟨u (φ n, t), huK _ (hφa n) t⟩ : K)) atTop (𝓝 ⟨x t, hxK t⟩) :=
      hemb.isEmbedding.tendsto_nhds_iff.2 <| by
        simpa only [comp_def, ← hex] using hconv.tendsto_at t
    exact (continuous_subtype_val.tendsto _).comp h
  · rw [sliceDefect_comp_eq_mvfderiv_sub (he.mdifferentiableAt one_ne_zero)
      ((hu.contMDiffAt (hU.mem_nhds (mk_mem_prod (hφa n) (mem_univ t)))).mdifferentiableAt
        one_ne_zero)
      (hYe' t _ (huK _ (hφa n) t))]

/-- **Periodic orbits at the end of a finite-energy Floer half-cylinder in a closed manifold.** Let
`ω` be a nondegenerate two-form on a compact manifold `M`, `H` a `C¹` Hamiltonian, `1`-periodic in
time, and let `u` be `C¹` on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)`,
solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]`. Let
`e : M → F` be a `C¹` injective map with injective differential into a finite-dimensional normed
space, and suppose that the almost complex structures are uniformly tame with respect to `e`:
`c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `(a, ∞) × [0, 1]` is finite,
then there are `s_n → ∞`, with `s_n > a`, such that the loops `t ↦ u(s_n, t)` converge to a
`1`-periodic orbit `x` of the Hamiltonian vector field, pointwise in `M` and uniformly after
applying `e`, and the `L²` norms of their defects `d e (∂_t u - X_{H_t}(u))` tend to `0`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (φ n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (φ n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (φ n, t)))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨x, hx, -, h⟩ := hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
    hH hHper he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper
    (fun _ _ _ ↦ mem_univ _) J hc hJc hfloer hE
  exact ⟨x, hx, h⟩

/-! ### Convergence along the whole end -/

/-- **Convergence of a finite-energy Floer half-cylinder to an isolated periodic orbit in a
manifold.** Under the hypotheses of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, suppose that
`e ∘ u` has bounded derivative on `(a, ∞) × ℝ` and that each `1`-periodic orbit `x` of `X_H` in `K`
has an isolated initial point `x(0)` among the `1`-periodic orbits in `K`. Then the loops
`t ↦ u(s, t)` converge as `s → ∞` to a single `1`-periodic orbit `x` in `K`, uniformly after
applying `e` and pointwise in `M`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a C : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) → ∀ᶠ p in 𝓝 (x 0),
        ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
          (∀ t, y t ∈ K) → y 0 = p → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨hemb, Y, hYc, hYper, hYe', hfin⟩ :=
    exists_extension_lintegral_norm_sq_sliceDefect_comp_ne_top hω hH hHper he hK he_inj hu huK J
      hc hJc hfloer hE
  -- Every `1`-periodic solution of `Y` in `e(K)` lifts to `K` and inherits isolation through `e`.
  obtain ⟨x', hx'per, hx', hconv⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop
    (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
    (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
    (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin hC fun x' hx'per hx' hx'K ↦ by
      obtain ⟨x, hx, hxK, rfl⟩ :=
        exists_mem_periodicSolutions_of_hasDerivAt he hK he_inj hde hYe' hx'per hx' hx'K
      have hnhds : Subtype.val ⁻¹' {p : M |
          ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
            (∀ t, y t ∈ K) → y 0 = p → y = x} ∈ 𝓝 (⟨x 0, hxK 0⟩ : K) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (hiso x hx hxK)
      rw [hemb.isEmbedding.nhds_eq_comap] at hnhds
      obtain ⟨V, hV, hVK⟩ := mem_comap.1 hnhds
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
      refine ⟨ε, hε, fun y' hy'per hy' hy'K hdist ↦ ?_⟩
      obtain ⟨y, hy, hyK, rfl⟩ :=
        exists_mem_periodicSolutions_of_hasDerivAt he hK he_inj hde hYe' hy'per hy' hy'K
      have hyV : (⟨y 0, hyK 0⟩ : K) ∈ (fun p : K ↦ e p) ⁻¹' V := hball (hdist 0)
      exact congrArg (e ∘ ·) (hVK hyV y hy hyK rfl)
  obtain ⟨x, hx, hxK, hex⟩ := exists_mem_periodicSolutions_of_hasDerivAt he hK he_inj hde hYe'
    hx'per hx' fun t ↦ (hK.image he.continuous).isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop a).mono fun s hs ↦ mem_image_of_mem e (huK s hs t))
  refine ⟨x, hx, hxK, hex ▸ hconv, fun t ↦ tendsto_iff_forall_eventually_mem.2 fun W hW ↦ ?_⟩
  have hWK : Subtype.val ⁻¹' W ∈ 𝓝 (⟨x t, hxK t⟩ : K) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  rw [hemb.isEmbedding.nhds_eq_comap] at hWK
  obtain ⟨V, hV, hVK⟩ := mem_comap.1 hWK
  have hVx' : V ∈ 𝓝 (x' t) := by simpa only [← hex, comp_apply] using hV
  filter_upwards [eventually_gt_atTop a, (hconv.tendsto_at t).eventually hVx'] with s hs hse
  have hus : (⟨u (s, t), huK s hs t⟩ : K) ∈ (fun p : K ↦ e p) ⁻¹' V := hse
  exact hVK hus

/-- **Convergence of a finite-energy Floer half-cylinder to a nondegenerate periodic orbit in a
manifold.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `H` a
`C²` Hamiltonian, `1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s > a`, with
`1`-periodic loops `t ↦ u(s, t)` in a compact set `K`, solving `∂_s u + J (∂_t u - X_{H_t}(u)) = 0`
on `(a, ∞) × [0, 1]` with finite energy. Let `e : M → F` be a `C¹` map into a finite-dimensional
normed space, injective on `K` with injective differential at the points of `K`, such that `e ∘ u`
has bounded derivative on `(a, ∞) × ℝ` and `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If every
`1`-periodic orbit `x` of `X_H` in `K` has a nondegenerate initial point `x(0)` for the time-one
map, then the loops `t ↦ u(s, t)` converge as `s → ∞` to a single `1`-periodic orbit `x` in `K`,
uniformly after applying `e` and pointwise in `M`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a C : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, ω.hamiltonianVectorField (H p.1) p.2⟩ : TangentBundle I M)) :=
    hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (by norm_num [hH])
  have hXper : Periodic (fun t ↦ ω.hamiltonianVectorField (H t)) 1 :=
    fun t ↦ congrArg ω.hamiltonianVectorField (hHper t)
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
    (hH.of_le one_le_two) hHper he hK he_inj hde hu hper huK hC J hc hJc hfloer hE
    fun x hx hxK ↦ ?_
  have hiso := eventually_eq_of_mem_periodicSolutions_of_isNondegenerateFixedPt (s := 0) hX hXper
    one_ne_zero hx (by simpa only [zero_add] using hnd x hx hxK)
  exact hiso.mono fun p hp y hy _ hyp ↦ hp y hy hyp

/-- **Convergence of a finite-energy Floer half-cylinder to a nondegenerate periodic orbit in a
closed manifold.** Under the hypotheses of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`
on a compact Hausdorff boundaryless manifold `M` with `K = univ`, the loops `t ↦ u(s, t)` converge
as `s → ∞` to a single `1`-periodic orbit `x` of `X_H`, uniformly after applying `e` and pointwise
in `M`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a C : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact hH hHper he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _) hC J hc hJc
      hfloer hE fun x hx _ ↦ hnd x hx
  exact ⟨x, hx, h⟩

end SmoothTwoForm

end TauCeti
