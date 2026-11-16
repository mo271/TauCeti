/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Geometry.Manifold.Topology

/-!
# Monodromy integrals and exactness of `1`-forms with local primitives

A `1`-form `φ` that admits local primitives on a `C¹` manifold `M` can be integrated along every
continuous path `γ : Path x y`, with no regularity assumption on `φ`, no completeness assumption on
the coefficient space `F`, and no finite-dimensionality or Hausdorff assumption on `M`. By
`TauCeti.PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn`, projecting the space
`TauCeti.PrimitiveSpace φ` of local primitive values to `M` is a covering map. Lifting `γ` starting
at `(x, 0)` produces a continuous primitive along `γ`, and the **monodromy integral**
`TauCeti.monodromyIntegral φ γ` is its endpoint value (`TauCeti.monodromyIntegral_eq_sub`).

Because two lifts of `γ` differ by a constant translation of the fibre, the integral equals the
change of value along any continuous lift, reduces on a single primitive domain to the endpoint
difference of that primitive (`TauCeti.monodromyIntegral_eq_sub_of_isPrimitiveOn`), and equals the
sum of endpoint differences of local primitives over any finite subdivision of `[0, 1]` mapped into
primitive domains (`TauCeti.monodromyIntegral_eq_sum_sub_of_isPrimitiveOn`). By homotopy lifting for
covering maps, it depends only on the homotopy class of `γ` relative to its endpoints
(`TauCeti.monodromyIntegral_eq_of_homotopic`), vanishes on constant paths, is additive under path
concatenation, negates under path reversal, is linear in `φ`, and is natural under pullback along
differentiable maps (`TauCeti.monodromyIntegral_mpullback`). When `F` is complete and `φ` is
continuous, it agrees with the Bochner line integral `TauCeti.pathIntegral` along `C¹` curves
(`TauCeti.monodromyIntegral_eq_pathIntegral`).

On a connected `C¹` manifold, a `1`-form with local primitives has a global primitive if and only if
its monodromy integral vanishes around every loop at a basepoint, integration from the basepoint
supplying a global primitive (`TauCeti.isPrimitiveOn_univ_monodromyIntegral_somePath`,
`TauCeti.exists_isPrimitiveOn_univ_iff_forall_monodromyIntegral_eq_zero`). In particular, on a
simply connected `C¹` manifold—or any simply connected open subset of a `C¹` manifold—every
`1`-form with local primitives has a global primitive
(`TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`,
`IsOpen.exists_isPrimitiveOn_of_simplyConnectedSpace`).

## Main declarations

* `TauCeti.monodromyIntegral φ γ`: the monodromy integral of `φ` along a continuous path `γ`.
* `TauCeti.monodromyIntegral_eq_sub`: characterization as the value change along any continuous lift
  to `TauCeti.PrimitiveSpace φ`.
* `TauCeti.monodromyIntegral_eq_sum_sub_of_isPrimitiveOn`: evaluation as a sum of endpoint
  differences of local primitives over a finite subdivision of `[0, 1]`.
* `TauCeti.monodromyIntegral_eq_of_homotopic`: invariance under homotopy relative to endpoints.
* `TauCeti.monodromyIntegral_mpullback`: naturality under differentiable maps.
* `TauCeti.IsPrimitiveOn.pathIntegral_eq_sub` and `TauCeti.monodromyIntegral_eq_pathIntegral`:
  comparison with `TauCeti.pathIntegral` along `C¹` curves when `F` is complete.
* `TauCeti.exists_isPrimitiveOn_univ_iff_forall_monodromyIntegral_eq_zero`: loop-vanishing criterion
  for global primitives on a connected `C¹` manifold.
* `TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace` and
  `IsOpen.exists_isPrimitiveOn_of_simplyConnectedSpace`: exactness of `1`-forms with local
  primitives on simply connected `C¹` manifolds and open subsets.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields* (path independence, loop criterion, and exactness on simply connected manifolds
  for smooth closed covector fields along piecewise smooth curves).
* Allen Hatcher, *Algebraic Topology*, Section 1.3, Propositions 1.30, 1.33, and 1.34 (homotopy
  lifting, the lifting criterion, and uniqueness of lifts for covering spaces).
-/

public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology

namespace TauCeti

section PathIntegral

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Fundamental theorem of calculus for a local primitive.** If `g` is a primitive of `φ` on an
open set `U` and a curve `c` stays in `U` and is differentiable along `uIcc a b`, then the line
integral of `φ` along `c` from `a` to `b` is `g (c b) - g (c a)` as soon as the integrand is
interval integrable. -/
theorem IsPrimitiveOn.pathIntegral_eq_sub {φ : RoughForm I M F 1} {g : M → F} {U : Set M}
    (hg : IsPrimitiveOn φ g U) {c : ℝ → M} {a b : ℝ}
    (hc : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hcU : ∀ t ∈ uIcc a b, c t ∈ U)
    (hint : IntervalIntegrable (fun t ↦ φ (c t) fun _ ↦ Manifold.curveVelocity I c t) volume a b) :
    pathIntegral φ c a b = g (c b) - g (c a) := by
  rw [pathIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g ∘ c) (fun t ht ↦ ?_) hint
  rw [← hg.mextDeriv_eq (c t) (hcU t ht), mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  exact Manifold.hasDerivAt_comp_curve
    ((hg.mdifferentiableOn (c t) (hcU t ht)).mdifferentiableAt (hg.isOpen.mem_nhds (hcU t ht)))
    (Manifold.hasMFDerivAt_curveVelocity (hc t ht))

end PathIntegral

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [IsManifold I 1 M]
  {φ ψ : RoughForm I M F 1} {x y z : M}

/-! ### Definition and lift characterization -/

open Classical in
/-- The monodromy integral of a `1`-form `φ` along a continuous path `γ` from `x` to `y`: when `φ`
has local primitives everywhere on `M`, the value at the endpoint of the lift of `γ` to
`PrimitiveSpace φ` starting at `x` with value `0`; otherwise `0`. -/
def monodromyIntegral (φ : RoughForm I M F 1) (γ : Path x y) : F :=
  if h : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U then
    PrimitiveSpace.value φ
      ((PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn h).monodromy (.mk γ)
        ⟨PrimitiveSpace.graph φ 0 x, PrimitiveSpace.proj_graph x⟩)
  else 0

/-- When `φ` does not admit local primitives everywhere on `M`, `monodromyIntegral φ γ` is `0` by
convention. -/
theorem monodromyIntegral_undef
    (h : ¬∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U) (γ : Path x y) :
    monodromyIntegral φ γ = 0 :=
  dite_eq_right h

/-- **Integration along a lift.** For any continuous lift `Γ` of `γ` to `PrimitiveSpace φ`, the
monodromy integral of `φ` along `γ` is the endpoint difference of the value of `Γ`. -/
theorem monodromyIntegral_eq_sub
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {γ : Path x y} {Γ : unitInterval → PrimitiveSpace φ} (hΓ : Continuous Γ)
    (hΓγ : ∀ t, PrimitiveSpace.proj φ (Γ t) = γ t) :
    monodromyIntegral φ γ = PrimitiveSpace.value φ (Γ 1) - PrimitiveSpace.value φ (Γ 0) := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ
  -- Translate the lift vertically so that its initial value is `0`.
  let Γ' : C(unitInterval, PrimitiveSpace φ) :=
    ⟨fun t ↦ PrimitiveSpace.translate φ (-PrimitiveSpace.value φ (Γ 0)) (Γ t),
      (PrimitiveSpace.continuous_translate _).comp hΓ⟩
  have hΓ'0 : Γ' 0 = PrimitiveSpace.graph φ 0 x :=
    PrimitiveSpace.ext (by simp [Γ', hΓγ]) (by simp [Γ'])
  rw [monodromyIntegral, dite_eq_left hφ,
    hp.monodromy_eq_apply_one (Γ := Γ') (funext fun t ↦ by simp [Γ', hΓγ]) hΓ'0]
  simp [Γ', sub_eq_add_neg]

/-- The monodromy of `PrimitiveSpace φ` along the homotopy class of `γ` translates fibre values by
`monodromyIntegral φ γ`. -/
theorem PrimitiveSpace.value_monodromy_of_forall_exists_isPrimitiveOn
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) (e : PrimitiveSpace.proj φ ⁻¹' {x}) :
    PrimitiveSpace.value φ
        ((PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ).monodromy
          (.mk γ) e) =
      PrimitiveSpace.value φ e + monodromyIntegral φ γ := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ
  have he : γ 0 = PrimitiveSpace.proj φ e := γ.source.trans e.2.symm
  rw [monodromyIntegral_eq_sub hφ (hp.liftPath γ e he).continuous
      (fun t ↦ congrFun (hp.liftPath_lifts γ e he) t),
    hp.liftPath_zero, ← hp.coe_monodromy_mk γ e]
  abel

/-! ### Evaluation via local primitives and subdivisions -/

/-- **Integration inside a single primitive domain.** When `γ` lies in an open set `U` carrying a
primitive `g` of `φ`, the monodromy integral of `φ` along `γ` is `g y - g x`. -/
theorem monodromyIntegral_eq_sub_of_isPrimitiveOn
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {g : M → F} {U : Set M} (hgU : IsPrimitiveOn φ g U) (γ : Path x y) (hγU : ∀ t, γ t ∈ U) :
    monodromyIntegral φ γ = g y - g x := by
  rw [monodromyIntegral_eq_sub hφ
    ((PrimitiveSpace.continuousOn_graph hgU).comp_continuous γ.continuous hγU)
    (fun t ↦ PrimitiveSpace.proj_graph (γ t))]
  simp

/-- **Evaluation over a finite subdivision.** Given `0 = t 0 ≤ t 1 ≤ … ≤ t n = 1` in `[0, 1]` such
that `γ` maps each subinterval `[t i, t (i + 1)]` into an open set `U i` carrying a primitive `g i`
of `φ`, the monodromy integral of `φ` along `γ` is the sum of the endpoint differences
`g i (γ (t (i + 1))) - g i (γ (t i))`. -/
theorem monodromyIntegral_eq_sum_sub_of_isPrimitiveOn
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {γ : Path x y} {n : ℕ} {t : ℕ → unitInterval} {g : ℕ → M → F} {U : ℕ → Set M}
    (ht₀ : t 0 = 0) (htn : t n = 1) (hmono : ∀ i < n, t i ≤ t (i + 1))
    (hgU : ∀ i < n, IsPrimitiveOn φ (g i) (U i))
    (hγU : ∀ i < n, ∀ s ∈ Icc (t i) (t (i + 1)), γ s ∈ U i) :
    monodromyIntegral φ γ =
      ∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i))) := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ
  let e₀ : PrimitiveSpace φ := PrimitiveSpace.graph φ 0 x
  have he₀ : γ 0 = PrimitiveSpace.proj φ e₀ := γ.source.trans (PrimitiveSpace.proj_graph x).symm
  let Γ := hp.liftPath γ e₀ he₀
  have hΓγ (s : unitInterval) : PrimitiveSpace.proj φ (Γ s) = γ s :=
    congrFun (hp.liftPath_lifts γ e₀ he₀) s
  rw [monodromyIntegral_eq_sub hφ Γ.continuous hΓγ, ← htn, ← ht₀,
    ← Finset.sum_range_sub (fun i ↦ PrimitiveSpace.value φ (Γ (t i))) n]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  replace hi := Finset.mem_range.mp hi
  -- On the preconnected subinterval `[t i, t (i + 1)]`, `Γ` and the translated graph of `g i`
  -- agree at `t i` and both lift `γ`, so they agree at `t (i + 1)` by uniqueness of lifts.
  have hconn : IsPreconnected (Icc (t i) (t (i + 1))) := by
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
    have himg : (Subtype.val : unitInterval → ℝ) '' Icc (t i) (t (i + 1)) =
        Icc (t i : ℝ) (t (i + 1) : ℝ) := by
      ext u
      simp only [mem_image, mem_Icc]
      exact ⟨by rintro ⟨s, hs, rfl⟩; exact hs, fun hu ↦
        ⟨⟨u, (t i).2.1.trans hu.1, hu.2.trans (t (i + 1)).2.2⟩, hu, rfl⟩⟩
    rw [himg]
    exact isPreconnected_Icc
  let c : F := PrimitiveSpace.value φ (Γ (t i)) - g i (γ (t i))
  let Γi (s : unitInterval) : PrimitiveSpace φ :=
    PrimitiveSpace.graph φ (fun w ↦ g i w + c) (γ s)
  have hΓi_cont : ContinuousOn Γi (Icc (t i) (t (i + 1))) :=
    (PrimitiveSpace.continuousOn_graph ((hgU i hi).add_const c)).comp
      γ.continuous.continuousOn (hγU i hi)
  have heqOn := hp.eqOn_of_comp_eqOn hconn Γ.continuous.continuousOn hΓi_cont
    (fun s _ ↦ (hΓγ s).trans (PrimitiveSpace.proj_graph (γ s)).symm)
    ⟨le_rfl, hmono i hi⟩
    (PrimitiveSpace.ext ((hΓγ (t i)).trans (PrimitiveSpace.proj_graph (γ (t i))).symm)
      (by simp [Γi, c]))
  have hval := congrArg (PrimitiveSpace.value φ) (heqOn ⟨hmono i hi, le_rfl⟩)
  simp only [Γi, PrimitiveSpace.value_graph, c] at hval
  rw [hval]
  abel

/-! ### Homotopy invariance and path operations -/

/-- Paths that are homotopic relative to their endpoints have the same monodromy integral. -/
theorem monodromyIntegral_eq_of_homotopic {γ γ' : Path x y} (h : γ.Homotopic γ') :
    monodromyIntegral φ γ = monodromyIntegral φ γ' := by
  simp only [monodromyIntegral, Path.Homotopic.Quotient.eq.mpr h]

/-- The monodromy integral along a constant path vanishes. -/
@[simp]
theorem monodromyIntegral_refl (x : M) : monodromyIntegral φ (Path.refl x) = 0 := by
  by_cases h : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U
  · have e := PrimitiveSpace.value_monodromy_of_forall_exists_isPrimitiveOn h (Path.refl x)
      ⟨PrimitiveSpace.graph φ 0 x, PrimitiveSpace.proj_graph x⟩
    rw [Path.Homotopic.Quotient.mk_refl,
      (PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn h).monodromy_refl,
      id, PrimitiveSpace.value_graph] at e
    simpa using e.symm
  · exact monodromyIntegral_undef h _

/-- Casting the endpoints of a path does not change its monodromy integral. -/
@[simp]
theorem monodromyIntegral_cast (γ : Path x y) {x' y' : M} (hx : x' = x) (hy : y' = y) :
    monodromyIntegral φ (γ.cast hx hy) = monodromyIntegral φ γ := by
  subst hx hy
  rfl

/-- The monodromy integral along a concatenation of paths is the sum of the integrals. -/
@[simp]
theorem monodromyIntegral_trans (γ : Path x y) (γ' : Path y z) :
    monodromyIntegral φ (γ.trans γ') = monodromyIntegral φ γ + monodromyIntegral φ γ' := by
  by_cases h : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U
  · have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn h
    have e := PrimitiveSpace.value_monodromy_of_forall_exists_isPrimitiveOn h (γ.trans γ')
      ⟨PrimitiveSpace.graph φ 0 x, PrimitiveSpace.proj_graph x⟩
    rw [Path.Homotopic.Quotient.mk_trans, hp.monodromy_trans_apply,
      PrimitiveSpace.value_monodromy_of_forall_exists_isPrimitiveOn h,
      PrimitiveSpace.value_monodromy_of_forall_exists_isPrimitiveOn h] at e
    simpa using e.symm
  · simp [monodromyIntegral_undef h]

/-- The monodromy integral along the reversal of a path is the negation of the integral. -/
@[simp]
theorem monodromyIntegral_symm (γ : Path x y) :
    monodromyIntegral φ γ.symm = -monodromyIntegral φ γ := by
  rw [eq_neg_iff_add_eq_zero, ← monodromyIntegral_trans,
    monodromyIntegral_eq_of_homotopic (Path.Homotopic.symm_trans γ), monodromyIntegral_refl]

/-- Paths that agree pointwise have the same monodromy integral, even when their endpoints are
written differently. -/
theorem monodromyIntegral_eq_of_apply_eq {x' y' : M} (γ : Path x y) (γ' : Path x' y')
    (h : ∀ t, γ t = γ' t) : monodromyIntegral φ γ = monodromyIntegral φ γ' := by
  obtain rfl : x = x' := by simpa using h 0
  obtain rfl : y = y' := by simpa using h 1
  rw [Path.ext (funext h)]

/-! ### Exact forms -/

/-- **Fundamental theorem of calculus along continuous paths.** The monodromy integral of the
exterior derivative of a differentiable function `g` along any continuous path `γ` from `x` to `y`
is `g y - g x`. No continuity of `dg` is required. -/
theorem monodromyIntegral_mextDeriv_ofFunction {g : M → F} (hg : MDifferentiable I 𝓘(ℝ, F) g)
    (γ : Path x y) :
    monodromyIntegral (mextDeriv (RoughForm.ofFunction I g)) γ = g y - g x := by
  have hgU : IsPrimitiveOn (mextDeriv (RoughForm.ofFunction I g)) g univ :=
    isPrimitiveOn_univ_of_mextDeriv_eq hg rfl
  exact monodromyIntegral_eq_sub_of_isPrimitiveOn (fun p ↦ ⟨g, univ, mem_univ p, hgU⟩) hgU γ
    fun _ ↦ mem_univ _

/-- **Fundamental theorem of calculus along continuous paths**, for a differentiable `0`-form
`ψ`. -/
theorem monodromyIntegral_mextDeriv {ψ : RoughForm I M F 0}
    (hψ : MDifferentiable I 𝓘(ℝ, F) fun p ↦ ψ p 0) (γ : Path x y) :
    monodromyIntegral (mextDeriv ψ) γ = ψ y 0 - ψ x 0 := by
  have h := monodromyIntegral_mextDeriv_ofFunction hψ γ
  rwa [← RoughForm.eq_ofFunction] at h

/-! ### Linearity in the form -/

/-- Monodromy integration along continuous paths is linear on `1`-forms with local primitives. -/
theorem monodromyIntegral_smul_add_smul
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hψ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn ψ g U)
    (a b : ℝ) (γ : Path x y) :
    monodromyIntegral (a • φ + b • ψ) γ =
      a • monodromyIntegral φ γ + b • monodromyIntegral ψ γ := by
  have hpφ := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ
  have hpψ := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hψ
  obtain ⟨Γ, hΓγ, -⟩ := hpφ.exists_path_lifts γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
    (by simp)
  obtain ⟨Δ, hΔγ, -⟩ := hpψ.exists_path_lifts γ.toContinuousMap (PrimitiveSpace.graph ψ 0 x)
    (by simp)
  have hΓγ' (t : unitInterval) : PrimitiveSpace.proj φ (Γ t) = γ t := congrFun hΓγ t
  have hΔγ' (t : unitInterval) : PrimitiveSpace.proj ψ (Δ t) = γ t := congrFun hΔγ t
  have hlin : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn (a • φ + b • ψ) g U :=
    fun p ↦ by
      obtain ⟨g, U, hpU, hgU⟩ := hφ p
      obtain ⟨h, V, hpV, hhV⟩ := hψ p
      exact ⟨_, U ∩ V, ⟨hpU, hpV⟩, (hgU.const_smul a).add (hhV.const_smul b)⟩
  let Λ (t : unitInterval) : PrimitiveSpace (a • φ + b • ψ) :=
    PrimitiveSpace.graph _ (fun _ ↦ a • PrimitiveSpace.value φ (Γ t) +
      b • PrimitiveSpace.value ψ (Δ t)) (γ t)
  have hΛ : Continuous Λ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_forall_exists_isPrimitiveOn hφ
        Γ.continuous.continuousAt (t := t₀)
    obtain ⟨h, V, hxV, hhV, d, hd⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_forall_exists_isPrimitiveOn hψ
        Δ.continuous.continuousAt (t := t₀)
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Λ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      (((hgU.const_smul a).add (hhV.const_smul b)).add_const (a • c + b • d))
      (by simp only [Λ, PrimitiveSpace.proj_graph]; rw [hΓγ'] at hxU; rw [hΔγ'] at hxV
          exact ⟨hxU, hxV⟩) ?_
    filter_upwards [hc, hd] with s hcs hds
    simp only [PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, Λ, hcs.2, hds.2, hΓγ',
      hΔγ', Pi.add_apply, Pi.smul_apply, smul_add]
    abel
  rw [monodromyIntegral_eq_sub hlin hΛ (fun t ↦ PrimitiveSpace.proj_graph (γ t)),
    monodromyIntegral_eq_sub hφ Γ.continuous hΓγ',
    monodromyIntegral_eq_sub hψ Δ.continuous hΔγ']
  simp only [PrimitiveSpace.value_graph, Λ, smul_sub]
  abel

/-- Monodromy integration is additive on `1`-forms with local primitives. -/
theorem monodromyIntegral_add
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hψ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn ψ g U) (γ : Path x y) :
    monodromyIntegral (φ + ψ) γ = monodromyIntegral φ γ + monodromyIntegral ψ γ := by
  simpa using monodromyIntegral_smul_add_smul hφ hψ 1 1 γ

/-- The monodromy integral of the zero `1`-form vanishes. -/
@[simp]
theorem monodromyIntegral_zero (γ : Path x y) :
    monodromyIntegral (0 : RoughForm I M F 1) γ = 0 := by
  have h0 : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn (0 : RoughForm I M F 1) g U :=
    fun p ↦ ⟨0, univ, mem_univ p, isPrimitiveOn_zero isOpen_univ⟩
  simpa using monodromyIntegral_smul_add_smul h0 h0 0 0 γ

/-- Monodromy integration commutes with real scalar multiplication of the form. -/
@[simp]
theorem monodromyIntegral_smul (a : ℝ) (γ : Path x y) :
    monodromyIntegral (a • φ) γ = a • monodromyIntegral φ γ := by
  by_cases hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U
  · simpa using monodromyIntegral_smul_add_smul hφ hφ a 0 γ
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have haφ : ¬∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn (a • φ) g U :=
        fun h' ↦ hφ fun p ↦ by
          obtain ⟨g, U, hpU, hgU⟩ := h' p
          exact ⟨a⁻¹ • g, U, hpU, by simpa [smul_smul, inv_mul_cancel₀ ha] using hgU.const_smul a⁻¹⟩
      rw [monodromyIntegral_undef hφ, monodromyIntegral_undef haφ, smul_zero]

/-- Monodromy integration commutes with negation of the form. -/
@[simp]
theorem monodromyIntegral_neg (γ : Path x y) :
    monodromyIntegral (-φ) γ = -monodromyIntegral φ γ := by
  simpa using monodromyIntegral_smul (-1 : ℝ) γ (φ := φ)

/-- Monodromy integration preserves differences of `1`-forms with local primitives. -/
theorem monodromyIntegral_sub
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hψ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn ψ g U) (γ : Path x y) :
    monodromyIntegral (φ - ψ) γ = monodromyIntegral φ γ - monodromyIntegral ψ γ := by
  simpa [sub_eq_add_neg] using monodromyIntegral_smul_add_smul hφ hψ 1 (-1) γ

/-! ### Naturality under differentiable maps -/

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']

/-- **Naturality of monodromy integrals.** For a differentiable map `f : M → M'` and a `1`-form `θ`
with local primitives on `M'`, the monodromy integral of `f^* θ` along `γ` equals the monodromy
integral of `θ` along `f ∘ γ`. -/
theorem monodromyIntegral_mpullback {θ : RoughForm I' M' F 1} {f : M → M'}
    (hf : MDifferentiable I I' f)
    (hθ : ∀ q : M', ∃ (g : M' → F) (U : Set M'), q ∈ U ∧ IsPrimitiveOn θ g U)
    (γ : Path x y) :
    monodromyIntegral (mpullback I I' f θ) γ = monodromyIntegral θ (γ.map hf.continuous) := by
  have hfθ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn (mpullback I I' f θ) g U :=
    fun p ↦ by
      obtain ⟨g, U, hfpU, hgU⟩ := hθ (f p)
      exact ⟨g ∘ f, f ⁻¹' U, hfpU, hgU.mpullback hf⟩
  have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hθ
  obtain ⟨Γ, hΓγ, -⟩ := hp.exists_path_lifts (γ.map hf.continuous).toContinuousMap
    (PrimitiveSpace.graph θ 0 (f x)) (by simp)
  have hΓγ' (t : unitInterval) : PrimitiveSpace.proj θ (Γ t) = f (γ t) := congrFun hΓγ t
  let Λ (t : unitInterval) : PrimitiveSpace (mpullback I I' f θ) :=
    PrimitiveSpace.graph _ (fun _ ↦ PrimitiveSpace.value θ (Γ t)) (γ t)
  have hΛ : Continuous Λ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_forall_exists_isPrimitiveOn hθ
        Γ.continuous.continuousAt (t := t₀)
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Λ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      ((hgU.mpullback hf).add_const c)
      (by simpa only [Λ, PrimitiveSpace.proj_graph, mem_preimage, ← hΓγ'] using hxU) ?_
    filter_upwards [hc] with s hs
    simp only [Λ, PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, hs.2, hΓγ',
      Function.comp_apply]
  rw [monodromyIntegral_eq_sub hfθ hΛ (fun t ↦ PrimitiveSpace.proj_graph (γ t)),
    monodromyIntegral_eq_sub hθ Γ.continuous hΓγ']
  simp [Λ]

end Pullback

/-! ### Comparison with line integrals along `C¹` curves -/

/-- **Agreement with `pathIntegral`.** When `F` is complete and `φ` is a continuous `1`-form with
local primitives, the monodromy integral of `φ` along a path `γ` following a `C¹` curve `c` agrees
with the Bochner line integral `pathIntegral φ c 0 1`. -/
theorem monodromyIntegral_eq_pathIntegral [CompleteSpace F]
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hφ₀ : IsSmoothForm I 0 φ) {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {γ : Path x y}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    monodromyIntegral φ γ = pathIntegral φ c 0 1 := by
  have hint := hφ₀.intervalIntegrable_apply_curveVelocity hc
  let Γ (t : unitInterval) : PrimitiveSpace φ :=
    PrimitiveSpace.graph φ (fun _ ↦ pathIntegral φ c 0 t) (γ t)
  have hΓ : Continuous Γ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU⟩ := hφ (c t₀)
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp (hgU.isOpen.preimage hc.continuous) (t₀ : ℝ) hxU
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Γ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      (hgU.add_const (pathIntegral φ c 0 t₀ - g (c t₀)))
      (by simp only [Γ, PrimitiveSpace.proj_graph, hγ]; exact hxU) ?_
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (t₀ : ℝ) hδ)] with s hs
    have hsub : uIcc (t₀ : ℝ) s ⊆ c ⁻¹' U := by
      refine (Set.OrdConnected.uIcc_subset ?_ (Metric.mem_ball_self (x := (t₀ : ℝ)) hδ) hs).trans
        hball
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo
    simp only [PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, Γ, hγ]
    rw [← pathIntegral_add_adjacent (hint 0 t₀) (hint t₀ s),
      hgU.pathIntegral_eq_sub (fun t _ ↦ (hc t).mdifferentiableAt one_ne_zero)
        (fun t ht ↦ hsub ht) (hint t₀ s)]
    abel
  rw [monodromyIntegral_eq_sub hφ hΓ (fun t ↦ PrimitiveSpace.proj_graph (γ t))]
  simp [Γ]

/-! ### Vanishing loop integrals and exactness on simply connected manifolds -/

omit [IsManifold I 1 M] in
/-- For any continuous section `s` of `PrimitiveSpace.proj φ`, the value coordinate
`y ↦ PrimitiveSpace.value φ (s y)` is a global primitive of `φ`. -/
theorem PrimitiveSpace.isPrimitiveOn_univ_value_of_proj_eq
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {s : M → PrimitiveSpace φ} (hs : Continuous s) (hps : ∀ y, PrimitiveSpace.proj φ (s y) = y) :
    IsPrimitiveOn φ (fun y ↦ PrimitiveSpace.value φ (s y)) univ := by
  refine IsPrimitiveOn.of_forall_eventuallyEq_add_const isOpen_univ fun y _ ↦ ?_
  obtain ⟨g, U, hyU, hgU, c, hc⟩ :=
    PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_forall_exists_isPrimitiveOn hφ
      (hs.continuousAt (x := y))
  rw [hps] at hyU
  exact ⟨g, U, hyU, hgU, c, hc.mono fun z hz ↦ by rw [hz.2, hps]⟩

/-- **Global primitive from vanishing loop integrals.** On a path-connected `C¹` manifold `M`, if
`φ` has local primitives everywhere and its monodromy integral vanishes around every loop based at
`x₀`, then integrating `φ` from `x₀` along any chosen family of paths gives a global primitive of
`φ` on `M`. -/
theorem isPrimitiveOn_univ_monodromyIntegral_somePath [PathConnectedSpace M]
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {x₀ : M} (hloop : ∀ γ : Path x₀ x₀, monodromyIntegral φ γ = 0) :
    IsPrimitiveOn φ (fun y ↦ monodromyIntegral φ (PathConnectedSpace.somePath x₀ y)) univ := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ
  have hpath {y : M} (pγ pγ' : Path x₀ y) :
      monodromyIntegral φ pγ = monodromyIntegral φ pγ' := by
    rw [← sub_eq_zero, sub_eq_add_neg, ← monodromyIntegral_symm, ← monodromyIntegral_trans]
    exact hloop (pγ.trans pγ'.symm)
  obtain ⟨s, ⟨hs₀, hps⟩, -⟩ := hp.isLocalHomeomorph.existsUnique_continuousMap_lifts (.id M) x₀
    (PrimitiveSpace.graph φ 0 x₀) (PrimitiveSpace.proj_graph x₀)
    (fun γ hγ₀ ↦ by
      obtain ⟨Γ, hΓ₁, hΓ₀⟩ := hp.exists_path_lifts γ (PrimitiveSpace.graph φ 0 x₀)
        (hγ₀.trans (PrimitiveSpace.proj_graph x₀).symm)
      exact ⟨Γ, hΓ₀, hΓ₁⟩)
    (fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 ↦ by
      let pγ : Path x₀ (γ 1) := ⟨γ, γ_0, rfl⟩
      let pγ' : Path x₀ (γ 1) := ⟨γ', γ'_0, γγ'1.symm⟩
      have hΓp (t : unitInterval) : PrimitiveSpace.proj φ (Γ t) = pγ t := by
        simpa [pγ] using congrFun Γ_lifts t
      have hΓ'p (t : unitInterval) : PrimitiveSpace.proj φ (Γ' t) = pγ' t := by
        simpa [pγ'] using congrFun Γ'_lifts t
      have hΓv : monodromyIntegral φ pγ = PrimitiveSpace.value φ (Γ 1) := by
        simpa [Γ_0] using monodromyIntegral_eq_sub hφ Γ.continuous hΓp
      have hΓ'v : monodromyIntegral φ pγ' = PrimitiveSpace.value φ (Γ' 1) := by
        simpa [Γ'_0] using monodromyIntegral_eq_sub hφ Γ'.continuous hΓ'p
      have hpΓ : PrimitiveSpace.proj φ (Γ 1) = PrimitiveSpace.proj φ (Γ' 1) := by
        rw [hΓp, hΓ'p, pγ.target, pγ'.target]
      exact PrimitiveSpace.ext hpΓ (hΓv.symm.trans ((hpath pγ pγ').trans hΓ'v)))
  have hps' (y : M) : PrimitiveSpace.proj φ (s y) = y := congrFun hps y
  refine (PrimitiveSpace.isPrimitiveOn_univ_value_of_proj_eq hφ s.continuous hps').congr
    fun y _ ↦ ?_
  let γ := PathConnectedSpace.somePath x₀ y
  rw [monodromyIntegral_eq_sub hφ (s.continuous.comp γ.continuous) (fun t ↦ hps' (γ t))]
  simp [Function.comp_apply, γ.source, γ.target, hs₀]

/-- **Loop-vanishing criterion for global primitives.** On a connected `C¹` manifold `M`, a
`1`-form `φ` with local primitives everywhere has a global primitive on `M` if and only if its
monodromy integral vanishes around every loop based at `x₀`. -/
theorem exists_isPrimitiveOn_univ_iff_forall_monodromyIntegral_eq_zero [PreconnectedSpace M]
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U) (x₀ : M) :
    (∃ g : M → F, IsPrimitiveOn φ g univ) ↔
      ∀ γ : Path x₀ x₀, monodromyIntegral φ γ = 0 := by
  refine ⟨fun ⟨g, hg⟩ γ ↦ ?_, fun hloop ↦ ?_⟩
  · rw [monodromyIntegral_eq_sub_of_isPrimitiveOn hφ hg γ (fun _ ↦ mem_univ _), sub_self]
  · have : Nonempty M := ⟨x₀⟩
    have := I.pathConnectedSpace M
    exact ⟨_, isPrimitiveOn_univ_monodromyIntegral_somePath hφ hloop⟩

/-- **Exactness on simply connected manifolds.** Every `1`-form with local primitives on a simply
connected `C¹` manifold over any real model with corners has a global primitive. No regularity of
`φ`, completeness of `F`, finite dimensionality, or Hausdorff assumption is required. -/
theorem exists_isPrimitiveOn_univ_of_simplyConnectedSpace [SimplyConnectedSpace M]
    {φ : RoughForm I M F 1}
    (hφ : ∀ x : M, ∃ (g : M → F) (U : Set M), x ∈ U ∧ IsPrimitiveOn φ g U) :
    ∃ g : M → F, IsPrimitiveOn φ g univ := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  refine ⟨_, isPrimitiveOn_univ_monodromyIntegral_somePath (x₀ := x₀) hφ fun γ ↦ ?_⟩
  rw [monodromyIntegral_eq_of_homotopic (SimplyConnectedSpace.paths_homotopic γ (.refl x₀)),
    monodromyIntegral_refl]

/-- On a simply connected open submanifold `W` of a `C¹` manifold `M`, any `1`-form `φ` that
admits local primitives near every point of `W` has a primitive on `W`. -/
theorem _root_.TopologicalSpace.Opens.exists_isPrimitiveOn_of_simplyConnectedSpace
    (W : Opens M) [SimplyConnectedSpace W] {φ : RoughForm I M F 1}
    (hφ : ∀ x ∈ W, ∃ (g : M → F) (U : Set M), x ∈ U ∧ IsPrimitiveOn φ g U) :
    ∃ g : M → F, IsPrimitiveOn φ g W := by
  rw [← exists_isPrimitiveOn_mpullback_subtype_val_univ_iff]
  refine exists_isPrimitiveOn_univ_of_simplyConnectedSpace fun x ↦ ?_
  obtain ⟨g, U, hxU, hgU⟩ := hφ x x.2
  exact ⟨g ∘ Subtype.val, Subtype.val ⁻¹' U, hxU,
    hgU.mpullback (contMDiff_subtype_val.mdifferentiable one_ne_zero)⟩

/-- On a simply connected open subset `W` of a `C¹` manifold `M`, any `1`-form `φ` that admits
local primitives near every point of `W` has a primitive on `W`. -/
theorem _root_.IsOpen.exists_isPrimitiveOn_of_simplyConnectedSpace {W : Set M}
    (hW : IsOpen W) [SimplyConnectedSpace W] {φ : RoughForm I M F 1}
    (hφ : ∀ x ∈ W, ∃ (g : M → F) (U : Set M), x ∈ U ∧ IsPrimitiveOn φ g U) :
    ∃ g : M → F, IsPrimitiveOn φ g W :=
  (⟨W, hW⟩ : Opens M).exists_isPrimitiveOn_of_simplyConnectedSpace hφ

end TauCeti
