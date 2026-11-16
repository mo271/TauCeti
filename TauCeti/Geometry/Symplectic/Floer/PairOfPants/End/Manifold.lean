/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Asymptotic periodic orbits at the ends of a Floer pair of pants in a manifold

Let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in a
manifold `M` carrying a nondegenerate two-form `ω`, equal to `H_q(t) dt` beyond some height `T₀` on
each end `q`, for period-one Hamiltonians `H_q`, and let `u : ℝ × ℝ → M` solve the Floer equation
`(du - X_K)^{0,1} = 0` on `S` with finite energy. This file proves that `u` breaks off a
`1`-periodic orbit of `X_{H_q}` at each end `q`, converges along the whole end `s → ∞` when the
`1`-periodic orbits are isolated or nondegenerate and the end derivative is bounded, and satisfies
the pair-of-pants energy identity and topological energy lower bound at these asymptotic orbits.
The vector-space counterparts are `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`.

**Positive end charts.** On the input ends `0` and `1` of `S` the radial coordinate `s` of the end
chart `φ_q` (`TauCeti.Floer.endChart`) tends to `+∞`, whereas on the output end `∞` it tends to
`-∞`. Passing to the holomorphic positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`) turns the perturbation beyond `T₀` into `H'_q(t) dt` for the
positive end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`). By
conformal invariance of the Floer equation and the energy on a manifold, `u ∘ φ'_q` solves the
half-cylinder Floer equation for `H'_q` beyond `T₀`
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`), with half-cylinder
energy bounded above by the energy of `u` over `S`
(`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). Reading a loop with the
time `±t` of the end identifies the `1`-periodic orbits of `H'_q` with those of `H_q`
(`SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`).

**Subsequential breaking and closed-manifold breaking.** Applying
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold` to `u ∘ φ'_q` yields, at each end `q`, a
`1`-periodic orbit `y` of `X_{H_q}` and heights `s_n → ∞` along which `t ↦ u(φ_q(±s_n, t))`
converges to `y`, pointwise in `M` and uniformly after applying an auxiliary immersion `e : M → F`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
and `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer` on a compact
manifold). On a compact Hausdorff smooth manifold equipped with the pair-of-pants perturbation
`TauCeti.Floer.pairOfPantsPerturbation` and the Cayley-interpolated pair-of-pants almost complex
structure `SmoothTwoForm.Compatible.pairOfPantsAlmostComplex`, combining Whitney's embedding
theorem (`exists_embedding_euclidean_of_compact`) with periodic uniform tameness eliminates both
`e` and the taming constant from the statement
(`SmoothTwoForm.Compatible.exists_mem_periodicSolutions_tendsto_endChart_of_floer`).

**Whole-end convergence and the energy identity.** When the derivative of `e ∘ u ∘ φ'_q` is bounded
on some half-cylinder and the `1`-periodic orbits of `X_{H_q}` in the target compact set are
isolated — in particular when `H_q` is `C²` on a Hausdorff boundaryless manifold and every
`1`-periodic orbit has a nondegenerate initial point for the time-one map — the loops
`t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y_q`
(`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated` and
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). Combined with
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic`, this upgrades finite Lebesgue
energy and integrable symplectic area to Bochner integrability of the Floer energy density and
proves both the pair-of-pants energy identity

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`

and the topological energy lower bound `-∑ q, B_q ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt` at the
asymptotic `1`-periodic orbits `y_q`
(`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`).

## Main results

* `TauCeti.SmoothTwoForm.hamiltonianVectorField_positiveEndHamiltonian_endSign_mul`,
  `TauCeti.SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`: relation between the
  Hamiltonian vector fields and `1`-periodic orbits of `H'_q` and `H_q`.
* `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`,
  `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_of_cylindrical`,
  `TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`: the ends of a
  manifold-valued Floer pair of pants as finite-energy Floer half-cylinders in positive end charts.
* `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer` (in
  `TauCeti.SmoothTwoForm.IsNondegenerate`): subsequential breaking of a finite-energy Floer pair of
  pants at each end in a manifold.
* `TauCeti.SmoothTwoForm.Compatible.exists_mem_periodicSolutions_tendsto_endChart_of_floer`:
  intrinsic subsequential breaking on a closed manifold for the pair-of-pants perturbation and
  pair-of-pants almost complex structure.
* `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated`,
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`,
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer` (in
  `TauCeti.SmoothTwoForm.IsNondegenerate`): convergence along `s → ∞` to isolated or nondegenerate
  periodic orbits at each end.
* `exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation` (in
  `TauCeti.SmoothTwoForm.IsNondegenerate`): the pair-of-pants energy identity and topological
  energy lower bound at the asymptotic `1`-periodic orbits.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
-/

public section

open Bundle Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti.SmoothTwoForm

open Floer

section SmoothManifold

variable {E HM M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}
  {e : M → F}

/-! ### Orbits in positive end charts -/

/-- At the time `±t` of the end, the Hamiltonian vector field of the positive end Hamiltonian
`H'_q` on `M` is `±` that of `H_q` at the time `t`: `X_{H'_q(±t)} = ±X_{H_q(t)}`. -/
theorem hamiltonianVectorField_positiveEndHamiltonian_endSign_mul (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (q : Puncture) (t : ℝ) :
    ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t)) =
      q.endSign • ω.hamiltonianVectorField (H q t) := by
  funext y
  rw [Pi.smul_apply, ← ω.hamiltonianVectorField_const_smul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, positiveEndHamiltonian_apply, endSign_mul_endSign_mul]

/-- Reading a loop with the time `±t` of an end identifies the `1`-periodic orbits of the positive
end Hamiltonian `H'_q` on `M` with those of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  have hX : (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) =
      fun t y ↦ q.endSign • ω.hamiltonianVectorField (H q (q.endSign * t)) y := by
    funext t y
    simpa only [Pi.smul_apply, endSign_mul_endSign_mul] using
      congrFun (ω.hamiltonianVectorField_positiveEndHamiltonian_endSign_mul H q (q.endSign * t)) y
  rw [hX]
  rcases q.endSign_eq_one_or_eq_neg_one with h | h
  · simp [h]
  · simp only [h, neg_one_mul, neg_one_smul]
    exact (mem_periodicSolutions_comp_neg_iff (I := I)
      (X := fun t ↦ ω.hamiltonianVectorField (H q t))).symm

/-! ### The ends of a Floer pair of pants in a manifold as Floer half-cylinders -/

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the global coordinate are differentiable
in the target point when the end Hamiltonian is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t)) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) = fun x ↦
      H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x *
        q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v := by
    funext x
    rw [hKH q _ x hre, smul_apply, smul_eq_mul]
  rw [h]
  have hmul : MDifferentiable 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun r : ℝ ↦ r * q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v) :=
    (contDiff_id.mul contDiff_const).contMDiff.mdifferentiable one_ne_zero
  exact hmul.mdifferentiableAt.comp y ((hHd q _) y)

/-- On the positive end beyond `T₀`, the pulled-back perturbation is `H'_q(t) dt`. -/
private theorem perturbedMFDeriv_comp_positiveEndChart_eq
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      ω.perturbedMFDeriv
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag)
        (u ∘ positiveEndChart q) ζ := by
  have hs : perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ =
      fun _ ↦ 0 :=
    funext (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ)
  have ht : perturbationPullback (positiveEndChart q)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ =
      positiveEndHamiltonian H q ζ.2 :=
    funext (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ)
  exact ContinuousLinearMap.ext fun _ ↦ by simp only [perturbedMFDeriv_apply, hs, ht]

/-- **The ends of a Floer pair of pants in a manifold solve the Floer equation of a half-cylinder.**
Let `K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve the Floer equation
`(du - X_K)^{0,1} = 0` for the almost complex structure `J` at `φ'_q(ζ)` with `ζ.1 ≥ T₀`. Then
`u ∘ φ'_q` solves the half-cylinder Floer equation at `ζ` for the positive end Hamiltonian
`H'_q`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart (ω : SmoothTwoForm I M)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} {q : Puncture} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

/-- **A cylindrical end of a Floer pair of pants in a manifold is a Floer half-cylinder.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` be differentiable on `S` and solve
the Floer equation `(du - X_K)^{0,1} = 0` there for a domain-dependent smooth almost complex
structure `J`. Suppose that on the end `q` beyond `T₀` the structure is cylindrical,
`J(φ_q(±s, t)) = J_q(t)`. Then at every point `ζ` of the positive end chart `φ'_q` with
`ζ.1 > max T₀ 0`, the map `u ∘ φ'_q` solves the half-cylinder Floer equation for `H'_q` and
`J'_q(t) = J_q(±t)`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_of_cylindrical
    (ω : SmoothTwoForm I M)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    {J : ℝ × ℝ → SmoothAlmostComplexStructure I M}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J z).almostComplexStructureAt (u z))
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    {q : Puncture} {Jq : ℝ → SmoothAlmostComplexStructure I M}
    (hJ : ∀ s t, T₀ ≤ s → J (endChart q (q.endSign * s, t)) = Jq t)
    {ζ : ℝ × ℝ} (hζ : max T₀ 0 < ζ.1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((Jq (q.endSign * ζ.2)).almostComplexStructureAt (u (positiveEndChart q ζ)))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  have hmem : positiveEndChart q ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hζ)
  have hJeq := eq_comp_positiveEndChart (u := u) (Jq := fun t _ ↦ Jq t)
    (fun s t hs ↦ hJ s t hs) ((le_max_left _ _).trans hζ.le)
  rw [← hJeq]
  exact ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    ((le_max_left _ _).trans hζ.le)
    (hu.mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hmem)) (hfloer _ hmem)

/-- **The energy of an end of a Floer pair of pants in a manifold.** For `a ≥ max T₀ 0`, the energy
of `u ∘ φ'_q` for the positive end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]` is
at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le (ω : SmoothTwoForm I M)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {u : ℝ × ℝ → M} (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    (q : Puncture) {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set edens : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set band : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hband : MeasurableSet band := measurableSet_Ioi.prod measurableSet_Ioo
  -- The closed band differs from the open band by a null set.
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] band := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  -- On the open band the energy density scales by the positive Jacobian determinant of `φ'_q`.
  have hdens : ∀ ζ ∈ band, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * edens (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζ₀ : 0 < ζ.1 := ha₀.trans_lt hζ.1
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hζ₀
    rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
      (hu.mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS))
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hband
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

/-! ### Asymptotic periodic orbits at the ends -/

/-- Package the half-cylinder Floer hypotheses for `fun z ↦ u (φ'_q z)` over `(a, ∞) × [0, 1]`
when `a ≥ max T₀ 0`. -/
private theorem floer_halfCylinder_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun z ↦ u (positiveEndChart q z)) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ u (positiveEndChart q (s, t))) 1) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
          J (positiveEndChart q z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
              ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
                (u (positiveEndChart q z))) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z) ≠ ⊤ := by
  have hHd : ∀ q t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t) := fun q t ↦
    ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hud : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal :=
    hu.mdifferentiableOn one_ne_zero
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun z hz ↦ hmem z hz.1,
    fun s _ t ↦ by simp only [positiveEndChart_add_one], fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      hud q ha₀ haT)⟩
  have hcl := ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le)
    (hud.mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds (hmem z hz.1)))
    (hfloer _ (hmem z hz.1))
  simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using
    (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
      (J (positiveEndChart q z))).1 hcl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

namespace IsNondegenerate

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
Let `ω` be a nondegenerate two-form on `M`, `K` equal to `H_q(t) dt` beyond `T₀` on each end `q` for
`1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be `C¹` on `S`, with image in a compact set
`B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let `e : M → F` be a `C¹` map
into a finite-dimensional normed space, injective on `B` with injective differential on `B`, such
that on the end `q` beyond some height `b` the structures are uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`. Then there are a `1`-periodic orbit `y` of `X_{H_q}` in `B`
and heights `σ_n → ∞` such that the loops `t ↦ u(φ_q(±σ_n, t))` converge to `y`, pointwise in `M`
and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHs hu hfloer hE q ha₀ haT
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v) hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, σ, hσ, ?_, fun t ↦ ?_⟩
  · have hloop (n : ℕ) : (fun t ↦ e (u (endChart q (q.endSign * σ n, t)))) =
        (fun t ↦ e (u (positiveEndChart q (σ n, t)))) ∘ fun t ↦ q.endSign * t := by
      funext t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [funext hloop]
    exact hux.comp _
  · simpa only [endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a compact manifold breaks off a periodic orbit at each
end.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` on a compact
manifold `M` with `B = univ`, each end `q` accumulates along some `σ_n → ∞` at a `1`-periodic orbit
`y` of `X_{H_q}`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hfloer hE q hc hJc
  exact ⟨y, hy, h⟩

end IsNondegenerate

/-- Beyond height `2` in the positive end chart, a solution for `pairOfPantsPerturbation H` and
`h₀.pairOfPantsAlmostComplex J hJt` satisfies the half-cylinder Floer equation for `H'_q` and
`J_q(±t)`. -/
private theorem floer_pairOfPantsAlmostComplex_positiveEndChart
    {J₀ : SmoothAlmostComplexStructure I M} (h₀ : ω.Compatible J₀)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t))
    {J : Puncture → ℝ → SmoothAlmostComplexStructure I M} {q : Puncture} (hJp : Periodic (J q) 1)
    (hJt : ∀ q t, ω.Tames (J q t)) {u : ℝ × ℝ → M}
    (hud : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    (hfloer : ∀ (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.pairOfPantsAlmostComplex J hJt
          ⟨Complex.equivRealProdCLM.symm z,
            mem_thricePuncturedSphereReal_iff.1 hz⟩).almostComplexStructureAt (u z))
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    {z : ℝ × ℝ} (hz : z ∈ Ioi (2 : ℝ) ×ˢ Icc 0 1) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
      ((J q (q.endSign * z.2)).almostComplexStructureAt (u (positiveEndChart q z)))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
          ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
            (u (positiveEndChart q z))) = 0 := by
  have hmem : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (zero_lt_two.trans hz.1)
  have hw : (⟨Complex.equivRealProdCLM.symm (positiveEndChart q z),
      mem_thricePuncturedSphereReal_iff.1 hmem⟩ : ThricePuncturedSphere).val =
      q.cylindricalEndLift (Complex.equivRealProdCLM.symm (q.endSign • z)) := by
    simp only [positiveEndChart_apply, equivRealProdCLM_symm_endChart]
  have hJz : h₀.pairOfPantsAlmostComplex J hJt ⟨_, mem_thricePuncturedSphereReal_iff.1 hmem⟩ =
      J q (q.endSign * z.2) := by
    simpa [Complex.equivRealProdCLM_symm_apply] using
      h₀.pairOfPantsAlmostComplex_cylindricalEndLift J hJt _ hJp hw (by
        simp only [Complex.equivRealProdCLM_symm_apply, Prod.smul_fst, smul_eq_mul, Complex.add_re,
          Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
          Complex.I_im, mul_one, sub_zero, add_zero, ← mul_assoc, endSign_mul_self, one_mul]
        exact hz.1.le)
  have hcl := ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (K := pairOfPantsPerturbation H) (T₀ := 2)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHd hz.1.le
    (hud.mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hmem)) (hfloer _ hmem)
  rw [hJz] at hcl
  simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using
    (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z _).1 hcl

/-- **Intrinsic breaking at the ends of a Floer pair of pants in a closed manifold.** Let `M` be a
compact Hausdorff smooth manifold with a nondegenerate two-form `ω` and an `ω`-compatible base
almost complex structure `J₀`. Let `H_q` be `1`-periodic `C¹` Hamiltonians on `M`, `J_q` be
`1`-periodic `ω`-tamed smooth almost complex structures continuous on `ℝ × M`, and let `u` be a `C¹`
map on `S` of finite Floer energy solving the Floer equation on `S` for `pairOfPantsPerturbation H`
and `h₀.pairOfPantsAlmostComplex J hJt`. Then at each end `q` there are a `1`-periodic orbit `y` of
`X_{H_q}` and heights `σ_n → ∞` such that `u(φ_q(±σ_n, t)) → y(t)` in `M` for all `t`. -/
theorem Compatible.exists_mem_periodicSolutions_tendsto_endChart_of_floer
    [CompactSpace M] [T2Space M] {J₀ : SmoothAlmostComplexStructure I M} (h₀ : ω.Compatible J₀)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {J : Puncture → ℝ → SmoothAlmostComplexStructure I M} (hJp : ∀ q, Periodic (J q) 1)
    (hJt : ∀ q t, ω.Tames (J q t))
    (hJc : ∀ q, Continuous (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((J q p.1).toEndomorphism p.2)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hfloer : ∀ (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.pairOfPantsAlmostComplex J hJt
          ⟨Complex.equivRealProdCLM.symm z,
            mem_thricePuncturedSphereReal_iff.1 hz⟩).almostComplexStructureAt (u z))
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  -- Pick a Whitney embedding of `M` and a uniform taming constant on the end `q`.
  obtain ⟨d, emb, hemb_smooth, hemb_closed, hemb_inj⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  have hemb1 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 1 emb := hemb_smooth.of_le (by simp)
  obtain ⟨c, hc, hle⟩ := h₀.isNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le_of_periodic
    hemb1 isCompact_univ isOpen_univ (subset_univ _) (hJp q) (hJc q).continuousOn (hJt q)
  have hHd : ∀ q t, MDifferentiable I 𝓘(ℝ, ℝ) (H q t) := fun q t ↦
    ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hud : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal :=
    hu.mdifferentiableOn one_ne_zero
  obtain ⟨x, hx, σ, -, hσ, -, hpt, -⟩ :=
    h₀.isNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      hemb1 hemb_closed.injective (fun p ↦ injective_mvfderiv_iff.2 (hemb_inj p))
      (u := fun w ↦ u (positiveEndChart q w))
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun z hz ↦
        positiveEndChart_mem_thricePuncturedSphereReal (zero_lt_two.trans hz.1))
      (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun z ↦ (J q (q.endSign * z.2)).almostComplexStructureAt (u (positiveEndChart q z))) hc
      (fun z _ v ↦ hle (q.endSign * z.2) _ (mem_univ _) v)
      (fun z hz ↦ floer_pairOfPantsAlmostComplex_positiveEndChart h₀ hH hHd (hJp q) hJt hud
        hfloer hz)
      (ne_top_of_le_ne_top hE (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
        (K := pairOfPantsPerturbation H) (T₀ := 2)
        (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHd hud q
        (by norm_num) le_rfl))
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    σ, hσ, fun t ↦ ?_⟩
  simpa only [endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-! ### Convergence along the whole end -/

namespace IsNondegenerate

/-- **Convergence of an end of a Floer pair of pants to an isolated periodic orbit in a manifold.**
Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, suppose that
`e ∘ u ∘ φ'_q` has bounded derivative on `(b, ∞) × ℝ` and that each `1`-periodic orbit `y` of
`X_{H_q}` in `B` has an isolated initial point `y(0)` among the `1`-periodic orbits in `B`. Then
the loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}`
in `B`, uniformly after applying `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b C c : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  obtain ⟨hu', hper', hfloer', hE'⟩ :=
    floer_halfCylinder_comp_positiveEndChart hKH hH hHs hu hfloer hE q ha₀ haT
  -- Isolation of `1`-periodic orbits transfers between `H_q` and `H'_q` via `t ↦ ±t`.
  have hiso' : ∀ x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
      (∀ t, x t ∈ B) → ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
          (∀ t, x' t ∈ B) → x' 0 = p → x' = x := by
    intro x hx hxB
    have hx' := mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx
    have hnhds := hiso (fun t ↦ x (q.endSign * t)) hx' (fun t ↦ hxB _)
    rw [mul_zero] at hnhds
    refine hnhds.mono fun p hp x' hx'p hx'B hx'0 ↦ funext fun t ↦ ?_
    have h := congrFun (hp (fun s ↦ x' (q.endSign * s))
      (mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx'p) (fun s ↦ hx'B _)
      (by simpa only [mul_zero] using hx'0)) (q.endSign * t)
    simpa only [endSign_mul_endSign_mul] using h
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' hper'
      (fun s hs t ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z hz ↦ hC z ((le_max_right _ _).trans_lt hz.1))
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v) hfloer' hE' hiso'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · have hloop (s : ℝ) : (fun t ↦ e (u (endChart q (q.endSign * s, t)))) =
        (fun t ↦ e (u (positiveEndChart q (s, t)))) ∘ fun t ↦ q.endSign * t := by
      funext t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [funext hloop]
    exact hux.comp _
  · simpa only [endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of an end of a Floer pair of pants to a nondegenerate periodic orbit in a
manifold.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` equal
to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q` such that `H_q`
is `C²` at the end `q`, and let `u` be `C¹` on `S`, with image in a compact set `B ⊆ M`, solving
`(du - X_K)^{0,1} = 0` on `S` with finite energy. If `e ∘ u ∘ φ'_q` has bounded derivative and `J`
is uniformly tame with respect to `e` beyond `b`, and every `1`-periodic orbit `y` of `X_{H_q}` in
`B` has a nondegenerate initial point `y(0)` for the time-one map, then the loops
`t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`,
uniformly after applying `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, ω.hamiltonianVectorField (H q p.1) p.2⟩ : TangentBundle I M)) :=
    hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (by norm_num [hHsq])
  have hXper : Periodic (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 :=
    fun t ↦ congrArg ω.hamiltonianVectorField (hH q t)
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated hKH
    hH hHs he hB he_inj hde hu huB hfloer hE q hC hc hJc fun y hy hyB ↦ ?_
  have hiso := eventually_eq_of_mem_periodicSolutions_of_isNondegenerateFixedPt (s := 0) hX hXper
    one_ne_zero hy (by simpa only [zero_add] using hnd y hy hyB)
  exact hiso.mono fun p hp y' hy' _ hy'p ↦ hp y' hy' hy'p

/-- **Convergence of an end of a Floer pair of pants to a nondegenerate periodic orbit in a closed
manifold.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` on a compact
Hausdorff boundaryless manifold `M` with `B = univ`, the loops `t ↦ u(φ_q(±s, t))` converge as
`s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}`, uniformly after applying `e` and pointwise
in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hfloer hE q
      hHsq hC hc hJc fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

end IsNondegenerate

end SmoothManifold

/-! ### The pair-of-pants energy identity at asymptotic periodic orbits -/

section EnergyIdentity

namespace IsNondegenerate

variable {E HM M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {e : M → F}

/-- **The pair-of-pants energy identity and topological energy bound at asymptotic periodic orbits
in a manifold.** Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation`
of bounded `1`-periodic `C²` Hamiltonians `H_q` (`|H_q| ≤ B_q`), whose `1`-periodic orbits in a
compact set `K₀ ⊆ M` are nondegenerate. Let `u` be a `C¹` map on `S` with image in `K₀`, integrable
symplectic area `u^*ω`, and finite Lebesgue Floer energy, solving `(du - X_K)^{0,1} = 0` on `S` for
`ω`-tamed almost complex structures `J z` such that on each end `q` the derivative of
`e ∘ u ∘ φ'_q` is bounded and `J` is uniformly tame with respect to `e` beyond some height. Then
there are asymptotic `1`-periodic orbits `y_q` of `X_{H_q}` in `K₀` at all three ends such that:
1. the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `y_q`, uniformly after applying `e`
   and pointwise in `M`;
2. the Floer energy density of `u` is Bochner-integrable over `S`;
3. `∫_S E = ∫_S u^*ω + ∑ q, q.endSign * ∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`; and
4. `-∑ q, B_q ≤ ∫_S u^*ω + ∑ q, q.endSign * ∫₀¹ H_q(t, y_q(t)) dt`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K₀ : Set M} (hK₀ : IsCompact K₀) (he_inj : InjOn e K₀)
    (hde : ∀ p ∈ K₀, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huK : ∀ z ∈ thricePuncturedSphereReal, u z ∈ K₀)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJt : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ K₀) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hb : ∀ q, ∃ b C c, 0 < c ∧
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
        c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
          hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ K₀) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) ∧
      -∑ q, B q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  -- Extract the asymptotic `1`-periodic orbit `y q` at each of the three ends.
  have hex : ∀ q, ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ K₀) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := fun q ↦ by
    obtain ⟨b, C, c, hc, hC, hJc⟩ := hb q
    exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      (K := pairOfPantsPerturbation H) (T₀ := 2)
      (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs1 he hK₀ he_inj
      hde hu huK hfloer hE q (hHs q) hC hc hJc (hnd q)
  choose y hy using hex
  have hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (y q t)) :=
    fun q t ↦ by simpa only [endChart_mk] using (hy q).2.2.2 t
  -- Upgrade finite Lebesgue energy and integrable area to Bochner integrability of the energy.
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hE_int : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal := by
    have hA' : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by rwa [IntegrableOn, hS] at hA
    have hR' : Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
      have h := integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn
      rwa [IntegrableOn, hS] at h
    exact (hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm
      (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
      (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hu
      (fun z hz ↦ floerEnergyDensity_nonneg hω (hJt z hz) (hfloer z hz)) hA' hR' fun q ↦ by
        simpa only [endChart_mk] using
          tendsto_intervalIntegral_endLoop (fun q ↦ (hHs1 q).continuous) hB hu.continuousOn
            (hx q)).integrableOn
  exact ⟨y, hy, hE_int,
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation hH hHs1 hB hu hx hE_int hA,
    hω.neg_sum_le_integral_add_sum_of_isComplexLinearMap hH hHs1 hB hu hx hE_int hA hJt hfloer⟩

end IsNondegenerate

end EnergyIdentity

end TauCeti.SmoothTwoForm
