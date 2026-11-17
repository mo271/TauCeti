/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Topology.CategoryTheory.ComposableArrows

import TauCeti.Geometry.Manifold.FiberProduct.Associativity
import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# The smooth nerve of a Lie groupoid

For a Lie groupoid `C` (`TauCeti.IsLieGroupoid`), the strings `ComposableArrows C k` of `k`
composable arrows form a smooth (`C^∞`) manifold for every `k : ℕ`, modelled on
`Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ` and carrying the exact nerve topology
`CategoryTheory.ComposableArrows.instTopologicalSpace` from `TauCeti.Topology.CategoryTheory.Nerve`.

When `C` is nonempty, `dim M ≤ dim Γ` and the dimension of `ComposableArrows C k` equals
`dim M + k * (dim Γ - dim M)`. The recursive construction builds `nerveChartedSpace` simultaneously
with the manifold property and the fact that the initial-vertex map `F ↦ F.left` is a smooth
submersion:
* at degree `0`, the atlas is transported from `C` via
  `CategoryTheory.ComposableArrows.zeroHomeomorph` and a model diffeomorphism
  `H ≃ₘ^∞ (Fin (finrank ℝ E) → ℝ)`;
* at degree `k + 1`, the transverse fibre product `{p : Quiver.Total C × ComposableArrows C k //
  p.1.right = p.2.left}` is formed from the target submersion `t` and the inductive initial-vertex
  submersion `F ↦ F.left`, standardised to `Fin (nerveModelDim d₀ d₁ (k + 1)) → ℝ`, and pulled back
  along `CategoryTheory.ComposableArrows.precompHomeomorph`.

Every arrow-extractor `F ↦ F.totalArrow i j hij` is smooth, and a map into `ComposableArrows C k` is
smooth if and only if every arrow `F.totalArrow i j hij` depends smoothly on the parameter.
Consequently, every reindexing `F ↦ F.whiskerLeft Φ` is smooth, so all simplicial operators of
`CategoryTheory.nerve C` — in particular every face map `δ i` and every degeneracy map `σ i` — are
smooth. The face map `δ₀` forgetting the first arrow and the first-arrow projection are smooth
submersions.

We also record explicit low-degree diffeomorphisms (`nerveZeroDiffeomorph`, `nerveOneDiffeomorph`,
`nerveTwoCategoricalDiffeomorph`, `nerveTwoDiffeomorph`) and the associator diffeomorphism between
the two iterated transverse fibre products of geometric composable triples
(`composableTriplesAssocDiffeomorph`), obtained from `TauCeti.fiberProductAssocDiffeomorph`.

No global `ChartedSpace` instance is installed on `ComposableArrows C k`; consumers bind
`nerveChartedSpace` locally with `letI`.

## Main definitions

* `TauCeti.IsLieGroupoid.nerveModelDim`: model dimension of `ComposableArrows C k`.
* `TauCeti.IsLieGroupoid.nerveChartedSpace`: smooth manifold atlas on `ComposableArrows C k` with
  its canonical nerve topology.
* `TauCeti.IsLieGroupoid.nerveZeroDiffeomorph`: `ComposableArrows C 0 ≃ₘ^∞ C`.
* `TauCeti.IsLieGroupoid.nervePrecompChartedSpace`,
  `TauCeti.IsLieGroupoid.nervePrecompDiffeomorph`: atlas on `Γ ×_{t, left} ComposableArrows C k`
  and its identification with `ComposableArrows C (k + 1)`.
* `TauCeti.IsLieGroupoid.nerveOneDiffeomorph`: `ComposableArrows C 1 ≃ₘ^∞ Quiver.Total C`.
* `TauCeti.IsLieGroupoid.nerveTwoCategoricalDiffeomorph`: `ComposableArrows C 2 ≃ₘ^∞ Γ ×_{t,s} Γ`.
* `TauCeti.IsLieGroupoid.nerveTwoDiffeomorph`: `ComposableArrows C 2 ≃ₘ^∞ Γ ×_{s,t} Γ`.
* `TauCeti.IsLieGroupoid.composableTriplesLeftChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesRightChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesAssocDiffeomorph`: iterated transverse fibre products of
  geometric composable triples and their canonical associator diffeomorphism.

## Main results

* `TauCeti.IsLieGroupoid.nerveModelDim_eq_add_mul`: `nerveModelDim d₀ d₁ k = d₀ + k * (d₁ - d₀)`
  when `d₀ ≤ d₁`.
* `TauCeti.IsLieGroupoid.isManifold_nerve`, `TauCeti.IsLieGroupoid.isManifold_nervePrecomp`:
  `ComposableArrows C k` and `Γ ×_{t, left} ComposableArrows C k` are smooth manifolds for all `k`.
* `TauCeti.IsLieGroupoid.isSubmersion_nerve_left`,
  `TauCeti.IsLieGroupoid.isSubmersion_nerve_firstArrow`,
  `TauCeti.IsLieGroupoid.isSubmersion_nerve_δ₀`: initial vertex, first arrow, and `δ₀` are smooth
  submersions.
* `TauCeti.IsLieGroupoid.contMDiff_totalArrow`,
  `TauCeti.IsLieGroupoid.contMDiff_composableArrows_iff_totalArrow`: universal property of the
  smooth structure on `ComposableArrows C k`.
* `TauCeti.IsLieGroupoid.contMDiff_whiskerLeft`, `TauCeti.IsLieGroupoid.contMDiff_nerve_map`,
  `TauCeti.IsLieGroupoid.contMDiff_nerve_δ`, `TauCeti.IsLieGroupoid.contMDiff_nerve_σ`: smoothness
  of all simplicial operators, face maps, and degeneracy maps of the nerve.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
-/

public section

open CategoryTheory Manifold Module Opposite Simplicial Topology
open scoped ContDiff Manifold

namespace TauCeti.IsLieGroupoid

/-! ### Model dimension of the smooth nerve -/

/-- Recursive model dimension of the manifold of `k` composable arrows in a Lie groupoid with
`d₀`-dimensional object manifold and `d₁`-dimensional arrow manifold. -/
def nerveModelDim (d₀ d₁ : ℕ) : ℕ → ℕ
  | 0 => d₀
  | k + 1 => d₁ + nerveModelDim d₀ d₁ k - d₀

@[simp]
theorem nerveModelDim_zero (d₀ d₁ : ℕ) : nerveModelDim d₀ d₁ 0 = d₀ := (rfl)

@[simp]
theorem nerveModelDim_succ (d₀ d₁ k : ℕ) :
    nerveModelDim d₀ d₁ (k + 1) = d₁ + nerveModelDim d₀ d₁ k - d₀ := (rfl)

/-- Degree `1` of the smooth nerve has model dimension `d₁`. -/
theorem nerveModelDim_one (d₀ d₁ : ℕ) : nerveModelDim d₀ d₁ 1 = d₁ := by
  simp [nerveModelDim]

/-- Degree `2` of the smooth nerve has model dimension `d₁ + d₁ - d₀`. -/
theorem nerveModelDim_two (d₀ d₁ : ℕ) : nerveModelDim d₀ d₁ 2 = d₁ + d₁ - d₀ := by
  simp [nerveModelDim]

/-- When `d₀ ≤ d₁`, the dimension of the `k`-simplex manifold is `d₀ + k * (d₁ - d₀)`. -/
theorem nerveModelDim_eq_add_mul {d₀ d₁ : ℕ} (h : d₀ ≤ d₁) (k : ℕ) :
    nerveModelDim d₀ d₁ k = d₀ + k * (d₁ - d₀) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [nerveModelDim_succ, ih, Nat.succ_mul]
    omega

/-- When `d₀ ≤ d₁`, the dimension of the `k`-simplex manifold is at least `d₀`. -/
theorem le_nerveModelDim {d₀ d₁ : ℕ} (h : d₀ ≤ d₁) (k : ℕ) :
    d₀ ≤ nerveModelDim d₀ d₁ k := by
  rw [nerveModelDim_eq_add_mul h]
  omega

/-! ### Private model-transport helpers -/

private noncomputable def modelToEuclideanDiffeomorph {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    H ≃ₘ^∞⟮I, 𝓘(ℝ, Fin (finrank ℝ E) → ℝ)⟯ (Fin (finrank ℝ E) → ℝ) :=
  let hsymm : ContMDiff 𝓘(ℝ, E) I ∞ I.symm :=
    contMDiffOn_univ.mp (by simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := (∞ : ℕ∞ω)))
  let e : H ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E :=
    { toFun := I
      invFun := I.symm
      left_inv := I.left_inv
      right_inv := fun y ↦ I.right_inv (I.range_eq_univ.symm ▸ Set.mem_univ y)
      contMDiff_toFun := I.contMDiff
      contMDiff_invFun := hsymm }
  let c : E ≃L[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let dc : E ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, Fin (finrank ℝ E) → ℝ)⟯ (Fin (finrank ℝ E) → ℝ) :=
    { toEquiv := c.toLinearEquiv.toEquiv
      contMDiff_toFun := c.contDiff.contMDiff
      contMDiff_invFun := c.symm.contDiff.contMDiff }
  e.trans dc

private noncomputable def finFunCongrDiffeomorph {a b : ℕ} (h : a = b) :
    (Fin a → ℝ) ≃ₘ^∞⟮𝓘(ℝ, Fin a → ℝ), 𝓘(ℝ, Fin b → ℝ)⟯ (Fin b → ℝ) :=
  let c : (Fin a → ℝ) ≃L[ℝ] (Fin b → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [h])
  { toEquiv := c.toLinearEquiv.toEquiv
    contMDiff_toFun := c.contDiff.contMDiff
    contMDiff_invFun := c.symm.contDiff.contMDiff }

section Transport

variable {EA HA EB HB M N : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA] [TopologicalSpace HA]
  {IA : ModelWithCorners ℝ EA HA}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HA M] [TopologicalSpace N]

@[instance_reducible]
private noncomputable def transportPullbackChartedSpace
    (Φ : HA ≃ₘ^∞⟮IA, IB⟯ HB) (e : N ≃ₜ M) : ChartedSpace HB N :=
  letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  letI := ChartedSpace.comp HB HA M
  e.pullbackChartedSpace

private theorem isManifold_transportPullback [IsManifold IA ∞ M]
    (Φ : HA ≃ₘ^∞⟮IA, IB⟯ HB) (e : N ≃ₜ M) :
    letI := transportPullbackChartedSpace Φ e
    IsManifold IB ∞ N := by
  let := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp HB HA M
  have := Φ.isManifold_chartedSpaceComp M
  exact e.pullback_isManifold IB ∞

private noncomputable def transportPullbackDiffeomorph
    (Φ : HA ≃ₘ^∞⟮IA, IB⟯ HB) (e : N ≃ₜ M) :
    letI := transportPullbackChartedSpace Φ e
    N ≃ₘ^∞⟮IB, IA⟯ M :=
  letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  letI := ChartedSpace.comp HB HA M
  letI := e.pullbackChartedSpace (H := HB)
  (e.pullbackDiffeomorph IB ∞).trans (Φ.chartedSpaceCompDiffeomorph M).symm

private theorem transportPullbackDiffeomorph_apply
    (Φ : HA ≃ₘ^∞⟮IA, IB⟯ HB) (e : N ≃ₜ M) (x : N) :
    letI := transportPullbackChartedSpace Φ e
    transportPullbackDiffeomorph Φ e x = e x := by
  let := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp HB HA M
  let := e.pullbackChartedSpace (H := HB)
  simp only [transportPullbackDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.coe_chartedSpaceCompDiffeomorph_symm, Homeomorph.coe_pullbackDiffeomorph, id_eq]

private theorem transportPullbackDiffeomorph_symm_apply
    (Φ : HA ≃ₘ^∞⟮IA, IB⟯ HB) (e : N ≃ₜ M) (y : M) :
    letI := transportPullbackChartedSpace Φ e
    (transportPullbackDiffeomorph Φ e).symm y = e.symm y := by
  let := transportPullbackChartedSpace Φ e
  have h : transportPullbackDiffeomorph Φ e ((transportPullbackDiffeomorph Φ e).symm y) =
      transportPullbackDiffeomorph Φ e (e.symm y) := by
    rw [Diffeomorph.apply_symm_apply, transportPullbackDiffeomorph_apply, e.apply_symm_apply]
  exact (transportPullbackDiffeomorph Φ e).injective h

end Transport

private theorem isSubmersion_of_diffeomorph {EA HA A EB HB B : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA] [TopologicalSpace HA]
    {IA : ModelWithCorners ℝ EA HA} [IA.Boundaryless]
    [TopologicalSpace A] [ChartedSpace HA A] [IsManifold IA ∞ A]
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
    {IB : ModelWithCorners ℝ EB HB}
    [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
    (e : A ≃ₘ^∞⟮IA, IB⟯ B) : Manifold.IsSubmersion IA IB ∞ e :=
  (e.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun x ↦ by
    have hid := mfderiv_comp (e x) (e.contMDiff.mdifferentiable (by simp) _)
      (e.symm.contMDiff.mdifferentiable (by simp) _)
    have heq : ⇑e ∘ ⇑e.symm = id := funext e.apply_symm_apply
    rw [e.symm_apply_apply, heq, mfderiv_id] at hid
    intro v
    refine ⟨mfderiv IB IA e.symm (e x) v, ?_⟩
    exact congrArg (fun f : TangentSpace IB (e x) →L[ℝ] TangentSpace IB (e x) ↦ f v)
      hid.symm).isSubmersion

private theorem continuous_comp_raw {C : Type*} [Category C] [IsGroupoid C]
    [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)] (h : IsTopologicalGroupoid C) :
    Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C) := by
  convert h.continuous_comp using 1
  funext p
  exact (Quiver.Total.comp_def p.1.1 p.1.2 p.2).symm

private theorem totalArrow_mk₁ {C : Type*} [Category C] (a : Quiver.Total C) :
    (ComposableArrows.mk₁ a.hom).totalArrow 0 1 (Fin.zero_le _) = a := by
  rcases a with ⟨x, y, f⟩
  rw [ComposableArrows.totalArrow_def]
  rfl

section Nerve

private structure NerveData {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (C : Type*) [Category C]
    [TopologicalSpace C] [ChartedSpace H C] [TopologicalSpace (Quiver.Total C)]
    (d₁ k : ℕ) where
  charted : ChartedSpace (Fin (nerveModelDim (finrank ℝ E) d₁ k) → ℝ)
    (ComposableArrows C k)
  isManifold :
    letI := charted
    IsManifold 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) d₁ k) → ℝ) ∞
      (ComposableArrows C k)
  isSubmersion_left :
    letI := charted
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) d₁ k) → ℝ) I ∞
      (fun F : ComposableArrows C k ↦ F.left)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  [I.Boundaryless] [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

/-! ### Recursive smooth atlas on `ComposableArrows C k` -/

private noncomputable def nerveZeroData : NerveData I C (finrank ℝ E') 0 :=
  let Φ := modelToEuclideanDiffeomorph I
  let e₀ := ComposableArrows.zeroHomeomorph (continuous_source I J C) (continuous_unit I J C)
  { charted := transportPullbackChartedSpace Φ e₀
    isManifold := isManifold_transportPullback Φ e₀
    isSubmersion_left := by
      let := transportPullbackChartedSpace Φ e₀
      have := isManifold_transportPullback Φ e₀
      have hsub := isSubmersion_of_diffeomorph (transportPullbackDiffeomorph Φ e₀)
      have heq : ⇑(transportPullbackDiffeomorph Φ e₀) =
          fun F : ComposableArrows C 0 ↦ F.left := funext fun F ↦
        (transportPullbackDiffeomorph_apply Φ e₀ F).trans
          (ComposableArrows.zeroHomeomorph_apply _ _ F)
      exact heq ▸ hsub }

private noncomputable def nerveStepData (k : ℕ) (prev : NerveData I C (finrank ℝ E') k) :
    NerveData I C (finrank ℝ E') (k + 1) := by
  letI := prev.charted
  haveI := prev.isManifold
  let m := nerveModelDim (finrank ℝ E) (finrank ℝ E') k
  let htr := transverse_of_isSubmersion_left (IY := 𝓘(ℝ, Fin m → ℝ)) (n := (∞ : ℕ∞ω)) (by simp)
    (f := (Quiver.Total.right : Quiver.Total C → C))
    (g := fun F : ComposableArrows C k ↦ F.left)
    (isSubmersion_target (I := I) (J := J) (C := C))
  letI cFP := transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) prev.isSubmersion_left.contMDiff htr
  haveI hmFP := isManifold_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) prev.isSubmersion_left.contMDiff htr
  have hdim : finrank ℝ E' + finrank ℝ (Fin m → ℝ) - finrank ℝ E =
      nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1) := by
    simp [nerveModelDim, m]
  let Φ := finFunCongrDiffeomorph hdim
  let e := ComposableArrows.precompHomeomorph (continuous_source I J C) (continuous_unit I J C)
    (continuous_comp_raw (toIsTopologicalGroupoid I J C)) k
  refine
    { charted := transportPullbackChartedSpace Φ e
      isManifold := isManifold_transportPullback Φ e
      isSubmersion_left := ?_ }
  let := transportPullbackChartedSpace Φ e
  have := isManifold_transportPullback Φ e
  have hsub_d := isSubmersion_of_diffeomorph (transportPullbackDiffeomorph Φ e)
  have hsub_fst := isSubmersion_fst_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) prev.isSubmersion_left.contMDiff htr prev.isSubmersion_left
  have hleft := (isSubmersion_source (I := I) (J := J) (C := C)).comp
    (hsub_fst.comp hsub_d (by simp)) (by simp)
  have heq : (Quiver.Total.left ∘
      ((fun p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} ↦ p.1.1) ∘
        ⇑(transportPullbackDiffeomorph Φ e))) =
      fun F : ComposableArrows C (k + 1) ↦ F.left := funext fun F ↦
    (congrArg (fun p ↦ p.val.1.left) (transportPullbackDiffeomorph_apply Φ e F)).trans
      ((congrArg (fun p ↦ p.1.left) (ComposableArrows.precompHomeomorph_apply
        (continuous_source I J C) (continuous_unit I J C)
        (continuous_comp_raw (toIsTopologicalGroupoid I J C)) k F)).trans
        (ComposableArrows.totalArrow_left F 0 1 (Fin.zero_le _)))
  exact heq ▸ hleft

private noncomputable def nerveData : ∀ k : ℕ, NerveData I C (finrank ℝ E') k
  | 0 => nerveZeroData I J C
  | k + 1 => nerveStepData I J C k (nerveData k)

/-- The smooth manifold atlas on `ComposableArrows C k`, modelled on
`Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ` and carrying the canonical nerve
topology `CategoryTheory.ComposableArrows.instTopologicalSpace`. Not installed as a global
instance. -/
@[instance_reducible]
noncomputable def nerveChartedSpace (k : ℕ) :
    ChartedSpace (Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ)
      (ComposableArrows C k) :=
  (nerveData I J C k).charted

/-- Every space of `k` composable arrows in a Lie groupoid is a smooth manifold of dimension
`nerveModelDim (finrank ℝ E) (finrank ℝ E') k`. -/
theorem isManifold_nerve (k : ℕ) :
    letI := nerveChartedSpace I J C k
    IsManifold 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) ∞
      (ComposableArrows C k) :=
  (nerveData I J C k).isManifold

/-- The initial-vertex map `F ↦ F.left` on `ComposableArrows C k` is a smooth submersion onto
the object manifold `C`. -/
theorem isSubmersion_nerve_left (k : ℕ) :
    letI := nerveChartedSpace I J C k
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) I ∞
      (fun F : ComposableArrows C k ↦ F.left) :=
  (nerveData I J C k).isSubmersion_left

/-! ### Degree-0 and inductive step diffeomorphisms -/

/-- Degree `0` of the smooth nerve is canonically diffeomorphic to the object manifold `C`. -/
noncomputable def nerveZeroDiffeomorph :
    letI := nerveChartedSpace I J C 0
    ComposableArrows C 0 ≃ₘ^∞⟮
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') 0) → ℝ), I⟯ C :=
  transportPullbackDiffeomorph (modelToEuclideanDiffeomorph I)
    (ComposableArrows.zeroHomeomorph (continuous_source I J C) (continuous_unit I J C))

@[simp]
theorem nerveZeroDiffeomorph_apply (F : ComposableArrows C 0) :
    letI := nerveChartedSpace I J C 0
    nerveZeroDiffeomorph I J C F = F.obj 0 := by
  let := nerveChartedSpace I J C 0
  exact (transportPullbackDiffeomorph_apply _ _ F).trans
    (ComposableArrows.zeroHomeomorph_apply _ _ F)

@[simp]
theorem nerveZeroDiffeomorph_symm_apply (x : C) :
    letI := nerveChartedSpace I J C 0
    (nerveZeroDiffeomorph I J C).symm x = ComposableArrows.mk₀ x := by
  let := nerveChartedSpace I J C 0
  exact (transportPullbackDiffeomorph_symm_apply _ _ x).trans
    (ComposableArrows.zeroHomeomorph_symm_apply _ _ x)

private theorem transverse_nervePrecomp (k : ℕ) :
    letI := nerveChartedSpace I J C k
    ∀ p : Quiver.Total C × ComposableArrows C k, p.1.right = p.2.left →
      (mfderiv J I Quiver.Total.right p.1).range ⊔
        (((tangentSpaceCast I p.2.left p.1.right).toContinuousLinearMap).comp
          (mfderiv 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) I
            (fun F : ComposableArrows C k ↦ F.left) p.2)).range = ⊤ := by
  let := nerveChartedSpace I J C k
  have := isManifold_nerve I J C k
  exact transverse_of_isSubmersion_left
    (IY := 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ)) (n := (∞ : ℕ∞ω))
    (by simp) (isSubmersion_target (I := I) (J := J) (C := C))

/-- The smooth transverse-fibre-product atlas on `Γ ×_{t, left} ComposableArrows C k`. -/
@[instance_reducible]
noncomputable def nervePrecompChartedSpace (k : ℕ) :
    ChartedSpace
      (Fin (finrank ℝ E' +
        finrank ℝ (Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) -
        finrank ℝ E) → ℝ)
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} := by
  letI := nerveChartedSpace I J C k
  haveI := isManifold_nerve I J C k
  exact transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (transverse_nervePrecomp I J C k)

/-- The transverse fibre product `Γ ×_{t, left} ComposableArrows C k` is a smooth manifold. -/
theorem isManifold_nervePrecomp (k : ℕ) :
    letI := nervePrecompChartedSpace I J C k
    IsManifold
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) -
        finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} := by
  let := nerveChartedSpace I J C k
  have := isManifold_nerve I J C k
  exact isManifold_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (transverse_nervePrecomp I J C k)

/-- The transverse fibre product identification
`ComposableArrows C (k + 1) ≃ₘ^∞ Γ ×_{t, left} ComposableArrows C k`, splitting a string of
`k + 1` arrows into its first arrow and its tail `F.δ₀`. -/
noncomputable def nervePrecompDiffeomorph (k : ℕ) :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nervePrecompChartedSpace I J C k
    ComposableArrows C (k + 1) ≃ₘ^∞⟮
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1)) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) -
        finrank ℝ E) → ℝ)⟯
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} := by
  letI := nervePrecompChartedSpace I J C k
  have hdim : finrank ℝ E' +
      finrank ℝ (Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) - finrank ℝ E =
      nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1) := by simp [nerveModelDim]
  exact transportPullbackDiffeomorph (finFunCongrDiffeomorph hdim)
    (ComposableArrows.precompHomeomorph (continuous_source I J C) (continuous_unit I J C)
      (continuous_comp_raw (toIsTopologicalGroupoid I J C)) k)

@[simp]
theorem nervePrecompDiffeomorph_apply (k : ℕ) (F : ComposableArrows C (k + 1)) :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nervePrecompChartedSpace I J C k
    (nervePrecompDiffeomorph I J C k F).val =
      (F.totalArrow 0 1 (Fin.zero_le _), F.δ₀) := by
  let := nerveChartedSpace I J C (k + 1)
  let := nervePrecompChartedSpace I J C k
  exact (congrArg Subtype.val (transportPullbackDiffeomorph_apply _ _ F)).trans
    (ComposableArrows.precompHomeomorph_apply (continuous_source I J C) (continuous_unit I J C)
      (continuous_comp_raw (toIsTopologicalGroupoid I J C)) k F)

@[simp]
theorem nervePrecompDiffeomorph_symm_apply (k : ℕ)
    (p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left}) :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nervePrecompChartedSpace I J C k
    (nervePrecompDiffeomorph I J C k).symm p =
      p.1.2.precomp (p.1.1.hom ≫ eqToHom p.2) := by
  let := nerveChartedSpace I J C (k + 1)
  let := nervePrecompChartedSpace I J C k
  exact (transportPullbackDiffeomorph_symm_apply _ _ p).trans
    (ComposableArrows.precompHomeomorph_symm_apply (continuous_source I J C)
      (continuous_unit I J C) (continuous_comp_raw (toIsTopologicalGroupoid I J C)) k p)

/-- The first-arrow projection `F ↦ F.totalArrow 0 1 _` is a smooth submersion onto
`Quiver.Total C`. -/
theorem isSubmersion_nerve_firstArrow (k : ℕ) :
    letI := nerveChartedSpace I J C (k + 1)
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1)) → ℝ) J ∞
      (fun F : ComposableArrows C (k + 1) ↦ F.totalArrow 0 1 (Fin.zero_le _)) := by
  let := nerveChartedSpace I J C (k + 1)
  have := isManifold_nerve I J C (k + 1)
  let := nerveChartedSpace I J C k
  have := isManifold_nerve I J C k
  let := nervePrecompChartedSpace I J C k
  have := isManifold_nervePrecomp I J C k
  have hfst := isSubmersion_fst_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (transverse_nervePrecomp I J C k) (isSubmersion_nerve_left I J C k)
  have hcomp := hfst.comp (isSubmersion_of_diffeomorph (nervePrecompDiffeomorph I J C k)) (by simp)
  have heq : (fun p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} ↦
      p.1.1) ∘ (nervePrecompDiffeomorph I J C k) =
      fun F : ComposableArrows C (k + 1) ↦ F.totalArrow 0 1 (Fin.zero_le _) :=
    funext fun F ↦ congrArg Prod.fst (nervePrecompDiffeomorph_apply I J C k F)
  exact heq ▸ hcomp

/-- The face map `F ↦ F.δ₀` forgetting the first arrow is a smooth submersion
`ComposableArrows C (k + 1) → ComposableArrows C k`. -/
theorem isSubmersion_nerve_δ₀ (k : ℕ) :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nerveChartedSpace I J C k
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1)) → ℝ)
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) ∞
      (fun F : ComposableArrows C (k + 1) ↦ F.δ₀) := by
  let := nerveChartedSpace I J C (k + 1)
  have := isManifold_nerve I J C (k + 1)
  let := nerveChartedSpace I J C k
  have := isManifold_nerve I J C k
  let := nervePrecompChartedSpace I J C k
  have := isManifold_nervePrecomp I J C k
  have hsnd := isSubmersion_snd_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (transverse_nervePrecomp I J C k) (isSubmersion_target (I := I) (J := J) (C := C))
  have hcomp := hsnd.comp (isSubmersion_of_diffeomorph (nervePrecompDiffeomorph I J C k)) (by simp)
  have heq : (fun p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} ↦
      p.1.2) ∘ (nervePrecompDiffeomorph I J C k) =
      fun F : ComposableArrows C (k + 1) ↦ F.δ₀ :=
    funext fun F ↦ congrArg Prod.snd (nervePrecompDiffeomorph_apply I J C k F)
  exact heq ▸ hcomp

/-! ### Smoothness universal property and simplicial operators -/

/-- A map into `ComposableArrows C 0` is smooth if and only if its vertex is smooth. -/
theorem contMDiff_composableArrows_zero_iff {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {F : X → ComposableArrows C 0} :
    letI := nerveChartedSpace I J C 0
    ContMDiff IX 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') 0) → ℝ) ∞ F ↔
      ContMDiff IX I ∞ (fun x ↦ (F x).obj 0) := by
  let := nerveChartedSpace I J C 0
  constructor
  · intro hF
    have heq : (fun x ↦ (F x).obj 0) = ⇑(nerveZeroDiffeomorph I J C) ∘ F :=
      funext fun x ↦ (nerveZeroDiffeomorph_apply I J C (F x)).symm
    exact heq ▸ (nerveZeroDiffeomorph I J C).contMDiff.comp hF
  · intro h0
    have heq : F = (nerveZeroDiffeomorph I J C).symm ∘ fun x ↦ (F x).obj 0 := by
      funext x
      simp only [Function.comp_apply, ← nerveZeroDiffeomorph_apply I J C (F x),
        Diffeomorph.symm_apply_apply]
    exact heq ▸ (nerveZeroDiffeomorph I J C).symm.contMDiff.comp h0

/-- A map into `ComposableArrows C (k + 1)` is smooth if and only if its first arrow and its tail
`δ₀` are smooth. -/
theorem contMDiff_composableArrows_iff_first_tail {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    (k : ℕ) {F : X → ComposableArrows C (k + 1)} :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nerveChartedSpace I J C k
    ContMDiff IX 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1)) → ℝ) ∞ F ↔
      ContMDiff IX J ∞ (fun x ↦ (F x).totalArrow 0 1 (Fin.zero_le _)) ∧
      ContMDiff IX 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) ∞
        (fun x ↦ (F x).δ₀) := by
  let := nerveChartedSpace I J C (k + 1)
  let := nerveChartedSpace I J C k
  have := isManifold_nerve I J C k
  let := nervePrecompChartedSpace I J C k
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (transverse_nervePrecomp I J C k)
  refine ⟨fun hF ↦ ⟨(isSubmersion_nerve_firstArrow I J C k).contMDiff.comp hF,
    (isSubmersion_nerve_δ₀ I J C k).contMDiff.comp hF⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  have hp : ContMDiff IX
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) -
        finrank ℝ E) → ℝ) ∞ (fun x ↦ nervePrecompDiffeomorph I J C k (F x)) := by
    apply hemb.contMDiff_iff_comp.mpr
    have heq : (Subtype.val ∘ fun x ↦ nervePrecompDiffeomorph I J C k (F x)) =
        fun x ↦ ((F x).totalArrow 0 1 (Fin.zero_le _), (F x).δ₀) :=
      funext fun x ↦ nervePrecompDiffeomorph_apply I J C k (F x)
    exact heq ▸ h1.prodMk h2
  have heq : F = (nervePrecompDiffeomorph I J C k).symm ∘
      fun x ↦ nervePrecompDiffeomorph I J C k (F x) :=
    funext fun x ↦ ((nervePrecompDiffeomorph I J C k).symm_apply_apply (F x)).symm
  exact heq ▸ (nervePrecompDiffeomorph I J C k).symm.contMDiff.comp hp

/-- Every arrow `F.totalArrow i j hij` of a string of composable arrows depends smoothly on `F`. -/
theorem contMDiff_totalArrow (k : ℕ) (i j : Fin (k + 1)) (hij : i ≤ j) :
    letI := nerveChartedSpace I J C k
    ContMDiff 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) J ∞
      (fun F : ComposableArrows C k ↦ F.totalArrow i j hij) := by
  induction k with
  | zero =>
    let := nerveChartedSpace I J C 0
    obtain rfl : i = 0 := Fin.ext (by omega)
    obtain rfl : j = 0 := Fin.ext (by omega)
    have heq : (fun F : ComposableArrows C 0 ↦ F.totalArrow 0 0 hij) =
        (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) ∘ nerveZeroDiffeomorph I J C := by
      funext F
      rw [Function.comp_apply, nerveZeroDiffeomorph_apply, ComposableArrows.totalArrow_self]
    exact heq ▸ (contMDiff_unit (I := I) (J := J) (C := C)).comp
      (nerveZeroDiffeomorph I J C).contMDiff
  | succ k ih =>
    let := nerveChartedSpace I J C (k + 1)
    let := nerveChartedSpace I J C k
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        have heq : (fun F : ComposableArrows C (k + 1) ↦ F.totalArrow 0 0 hij) =
            (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) ∘
              (fun F : ComposableArrows C (k + 1) ↦ F.left) :=
          funext fun F ↦ ComposableArrows.totalArrow_self F 0
        exact heq ▸ (contMDiff_unit (I := I) (J := J) (C := C)).comp
          (isSubmersion_nerve_left I J C (k + 1)).contMDiff
      | succ j' =>
        have hfirst := (isSubmersion_nerve_firstArrow I J C k).contMDiff
        have hle : (1 : Fin (k + 2)) ≤ j'.succ := Fin.succ_le_succ_iff.mpr (Fin.zero_le j')
        have htail_eq : (fun F : ComposableArrows C (k + 1) ↦ F.totalArrow 1 j'.succ hle) =
            (fun G : ComposableArrows C k ↦ G.totalArrow 0 j' (Fin.zero_le j')) ∘
              (fun F : ComposableArrows C (k + 1) ↦ F.δ₀) :=
          funext fun F ↦ (F.totalArrow_whiskerLeft (Fin.succFunctor (k + 1)) 0 j' _).symm
        have htail := htail_eq ▸
          (ih 0 j' (Fin.zero_le j')).comp (isSubmersion_nerve_δ₀ I J C k).contMDiff
        have hmatch (F : ComposableArrows C (k + 1)) :
            (F.totalArrow 0 1 (Fin.zero_le _)).right = (F.totalArrow 1 j'.succ hle).left := by simp
        have heq : (fun F : ComposableArrows C (k + 1) ↦ F.totalArrow 0 j'.succ hij) =
            fun F ↦ (F.totalArrow 0 1 (Fin.zero_le _)).comp
              (F.totalArrow 1 j'.succ hle) (hmatch F) := by
          funext F
          simp only [Quiver.Total.comp_def, ComposableArrows.totalArrow_def]
          refine congrArg (fun f ↦ (⟨F.obj 0, F.obj j'.succ, f⟩ : Quiver.Total C)) ?_
          rw [eqToHom_refl, Category.id_comp, ← F.map_comp]
          exact congrArg F.map (Subsingleton.elim _ _)
        exact heq ▸ contMDiff_comp_of_contMDiff I J C hfirst htail hmatch
    | succ i' =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j' =>
        have hle : i' ≤ j' := Fin.succ_le_succ_iff.mp hij
        have heq : (fun F : ComposableArrows C (k + 1) ↦ F.totalArrow i'.succ j'.succ hij) =
            (fun G : ComposableArrows C k ↦ G.totalArrow i' j' hle) ∘
              (fun F : ComposableArrows C (k + 1) ↦ F.δ₀) :=
          funext fun F ↦ (F.totalArrow_whiskerLeft (Fin.succFunctor (k + 1)) i' j' hle).symm
        exact heq ▸ (ih i' j' hle).comp (isSubmersion_nerve_δ₀ I J C k).contMDiff

/-- Every vertex map `F ↦ F.obj i` on `ComposableArrows C k` is smooth. -/
theorem contMDiff_nerve_obj (k : ℕ) (i : Fin (k + 1)) :
    letI := nerveChartedSpace I J C k
    ContMDiff 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) I ∞
      (fun F : ComposableArrows C k ↦ F.obj i) := by
  let := nerveChartedSpace I J C k
  have heq : (fun F : ComposableArrows C k ↦ F.obj i) =
      Quiver.Total.left ∘ fun F ↦ F.totalArrow i i le_rfl :=
    funext fun F ↦ (ComposableArrows.totalArrow_left F i i le_rfl).symm
  exact heq ▸ (contMDiff_source I J C).comp (contMDiff_totalArrow I J C k i i le_rfl)

/-- **Universal property of the smooth nerve.** A map into `ComposableArrows C k` is smooth if and
only if every arrow `F.totalArrow i j hij` depends smoothly on the parameter. -/
theorem contMDiff_composableArrows_iff_totalArrow {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    (k : ℕ) {F : X → ComposableArrows C k} :
    letI := nerveChartedSpace I J C k
    ContMDiff IX 𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) ∞ F ↔
      ∀ i j (hij : i ≤ j), ContMDiff IX J ∞ fun x ↦ (F x).totalArrow i j hij := by
  induction k with
  | zero =>
    let := nerveChartedSpace I J C 0
    refine ⟨fun hF i j hij ↦ (contMDiff_totalArrow I J C 0 i j hij).comp hF, fun h ↦ ?_⟩
    rw [contMDiff_composableArrows_zero_iff I J C]
    have heq : (fun x ↦ (F x).obj 0) =
        Quiver.Total.left ∘ fun x ↦ (F x).totalArrow 0 0 le_rfl :=
      funext fun x ↦ (ComposableArrows.totalArrow_left (F x) 0 0 le_rfl).symm
    exact heq ▸ (contMDiff_source I J C).comp (h 0 0 le_rfl)
  | succ k ih =>
    let := nerveChartedSpace I J C (k + 1)
    let := nerveChartedSpace I J C k
    refine ⟨fun hF i j hij ↦ (contMDiff_totalArrow I J C (k + 1) i j hij).comp hF, fun h ↦ ?_⟩
    rw [contMDiff_composableArrows_iff_first_tail I J C k]
    refine ⟨h 0 1 (Fin.zero_le _), (ih).2 fun i j hij ↦ ?_⟩
    have heq : (fun x ↦ (F x).δ₀.totalArrow i j hij) =
        fun x ↦ (F x).totalArrow i.succ j.succ (Fin.succ_le_succ_iff.mpr hij) :=
      funext fun x ↦ (F x).totalArrow_whiskerLeft (Fin.succFunctor (k + 1)) i j hij
    exact heq ▸ h i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)

/-- Reindexing strings of composable arrows along any poset functor `Φ : Fin (m + 1) ⥤ Fin (k + 1)`
is smooth. -/
theorem contMDiff_whiskerLeft {m k : ℕ} (Φ : Fin (m + 1) ⥤ Fin (k + 1)) :
    letI := nerveChartedSpace I J C k
    letI := nerveChartedSpace I J C m
    ContMDiff
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ)
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') m) → ℝ) ∞
      (fun F : ComposableArrows C k ↦ F.whiskerLeft Φ) := by
  let := nerveChartedSpace I J C k
  let := nerveChartedSpace I J C m
  rw [contMDiff_composableArrows_iff_totalArrow I J C m]
  intro i j hij
  have heq : (fun F : ComposableArrows C k ↦ (F.whiskerLeft Φ).totalArrow i j hij) =
      fun F : ComposableArrows C k ↦ F.totalArrow (Φ.obj i) (Φ.obj j) (Φ.monotone hij) :=
    funext fun F ↦ F.totalArrow_whiskerLeft Φ i j hij
  exact heq ▸ contMDiff_totalArrow I J C k (Φ.obj i) (Φ.obj j) (Φ.monotone hij)

/-- Every simplicial operator of `CategoryTheory.nerve C` is smooth. -/
theorem contMDiff_nerve_map {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    letI := nerveChartedSpace I J C Δ.unop.len
    letI := nerveChartedSpace I J C Δ'.unop.len
    ContMDiff (M := ComposableArrows C Δ.unop.len) (M' := ComposableArrows C Δ'.unop.len)
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') Δ.unop.len) → ℝ)
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') Δ'.unop.len) → ℝ) ∞
      (fun F ↦ (nerve C).map f F) :=
  contMDiff_whiskerLeft I J C (SimplexCategory.toCat.map f.unop).toFunctor

/-- Every face map `δ i : ComposableArrows C (k + 1) → ComposableArrows C k` of the nerve is
smooth. -/
theorem contMDiff_nerve_δ (k : ℕ) (i : Fin (k + 2)) :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nerveChartedSpace I J C k
    ContMDiff (M := ComposableArrows C (k + 1)) (M' := ComposableArrows C k)
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1)) → ℝ)
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ) ∞
      (fun F ↦ (nerve C).δ i F) :=
  contMDiff_nerve_map I J C (SimplexCategory.δ i).op

/-- Every degeneracy map `σ i : ComposableArrows C k → ComposableArrows C (k + 1)` of the nerve is
smooth. -/
theorem contMDiff_nerve_σ (k : ℕ) (i : Fin (k + 1)) :
    letI := nerveChartedSpace I J C k
    letI := nerveChartedSpace I J C (k + 1)
    ContMDiff (M := ComposableArrows C k) (M' := ComposableArrows C (k + 1))
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') k) → ℝ)
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') (k + 1)) → ℝ) ∞
      (fun F ↦ (nerve C).σ i F) :=
  contMDiff_nerve_map I J C (SimplexCategory.σ i).op

/-! ### Explicit low-degree identifications -/

/-- Degree `1` of the smooth nerve is canonically diffeomorphic to the total arrow manifold
`Quiver.Total C`. -/
noncomputable def nerveOneDiffeomorph :
    letI := nerveChartedSpace I J C 1
    ComposableArrows C 1 ≃ₘ^∞⟮
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') 1) → ℝ), J⟯ Quiver.Total C := by
  letI := nerveChartedSpace I J C 1
  exact
    { toFun := fun F ↦ F.totalArrow 0 1 (Fin.zero_le _)
      invFun := fun a ↦ ComposableArrows.mk₁ a.hom
      left_inv := fun F ↦ by
        refine ComposableArrows.ext_succ_of_totalArrow ?_ (totalArrow_mk₁ _)
        exact ComposableArrows.ext₀ (ComposableArrows.totalArrow_right F 0 1 (Fin.zero_le _))
      right_inv := totalArrow_mk₁
      contMDiff_toFun := (isSubmersion_nerve_firstArrow I J C 0).contMDiff
      contMDiff_invFun := by
        let := nerveChartedSpace I J C 0
        rw [contMDiff_composableArrows_iff_first_tail I J C 0]
        refine ⟨?_, ?_⟩
        · have heq : (fun a : Quiver.Total C ↦
              (ComposableArrows.mk₁ a.hom).totalArrow 0 1 (Fin.zero_le _)) = id :=
            funext totalArrow_mk₁
          exact heq ▸ contMDiff_id
        · rw [contMDiff_composableArrows_zero_iff I J C]
          exact contMDiff_target I J C }

@[simp]
theorem nerveOneDiffeomorph_apply (F : ComposableArrows C 1) :
    letI := nerveChartedSpace I J C 1
    nerveOneDiffeomorph I J C F = F.totalArrow 0 1 (Fin.zero_le _) := (rfl)

@[simp]
theorem nerveOneDiffeomorph_symm_apply (a : Quiver.Total C) :
    letI := nerveChartedSpace I J C 1
    (nerveOneDiffeomorph I J C).symm a = ComposableArrows.mk₁ a.hom := (rfl)

/-- Degree `2` of the smooth nerve is canonically diffeomorphic to categorical composable pairs
`{p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}`. -/
noncomputable def nerveTwoCategoricalDiffeomorph :
    letI := nerveChartedSpace I J C 2
    letI := categoricalComposablePairsChartedSpace I J C
    ComposableArrows C 2 ≃ₘ^∞⟮
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') 2) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} := by
  letI := nerveChartedSpace I J C 2
  letI := nerveChartedSpace I J C 1
  letI := categoricalComposablePairsChartedSpace I J C
  exact
    { toFun := fun F ↦
        ⟨(F.totalArrow 0 1 (Fin.zero_le _), F.totalArrow 1 2 (by decide)), by simp⟩
      invFun := fun p ↦
        (ComposableArrows.mk₁ p.1.2.hom).precomp (p.1.1.hom ≫ eqToHom p.2)
      left_inv := fun F ↦ by
        refine ComposableArrows.ext_succ_of_totalArrow ?_ ?_
        · rw [ComposableArrows.precomp_δ₀]
          refine ComposableArrows.ext_succ_of_totalArrow ?_ ?_
          · exact ComposableArrows.ext₀ (ComposableArrows.totalArrow_right F 1 2 (by decide))
          · exact (totalArrow_mk₁ _).trans
              (F.totalArrow_whiskerLeft (Fin.succFunctor 2) 0 1 (Fin.zero_le _)).symm
        · exact ComposableArrows.totalArrow_precomp_zero_one
            (F.totalArrow 0 1 (Fin.zero_le _))
            (ComposableArrows.mk₁ (F.totalArrow 1 2 (by decide)).hom) (by simp)
      right_inv := fun p ↦ by
        rcases p with ⟨⟨⟨x, y, f⟩, ⟨y', z, g⟩⟩, h⟩
        dsimp only at h
        subst h
        apply Subtype.ext
        exact Prod.ext
          (ComposableArrows.totalArrow_precomp_zero_one ⟨x, y, f⟩ (ComposableArrows.mk₁ g) rfl)
          ((ComposableArrows.totalArrow_precomp_succ_succ (ComposableArrows.mk₁ g) _ 0 1
            (Fin.zero_le _)).trans (totalArrow_mk₁ ⟨y, z, g⟩))
      contMDiff_toFun :=
        (isSmoothEmbedding_coe_categoricalComposablePairs I J C).contMDiff_iff_comp.mpr
          ((contMDiff_totalArrow I J C 2 0 1 (Fin.zero_le _)).prodMk
            (contMDiff_totalArrow I J C 2 1 2 (by decide)))
      contMDiff_invFun := by
        rw [contMDiff_composableArrows_iff_first_tail I J C 1]
        have hfst := (isSmoothEmbedding_coe_categoricalComposablePairs I J C).contMDiff.fst
        have hsnd := (isSmoothEmbedding_coe_categoricalComposablePairs I J C).contMDiff.snd
        refine ⟨?_, (nerveOneDiffeomorph I J C).symm.contMDiff.comp hsnd⟩
        have heq : (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
            ((ComposableArrows.mk₁ p.1.2.hom).precomp
              (p.1.1.hom ≫ eqToHom p.2)).totalArrow 0 1 (Fin.zero_le _)) = fun p ↦ p.1.1 :=
          funext fun p ↦ ComposableArrows.totalArrow_precomp_zero_one p.1.1
            (ComposableArrows.mk₁ p.1.2.hom) p.2
        exact heq ▸ hfst }

@[simp]
theorem nerveTwoCategoricalDiffeomorph_apply (F : ComposableArrows C 2) :
    letI := nerveChartedSpace I J C 2
    letI := categoricalComposablePairsChartedSpace I J C
    (nerveTwoCategoricalDiffeomorph I J C F).val =
      (F.totalArrow 0 1 (Fin.zero_le _), F.totalArrow 1 2 (by decide)) := (rfl)

/-- Degree `2` of the smooth nerve is canonically diffeomorphic to geometric composable pairs
`{p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}` (`Γ ×_{s,t} Γ`). -/
noncomputable def nerveTwoDiffeomorph :
    letI := nerveChartedSpace I J C 2
    letI := composablePairsChartedSpace I J C
    ComposableArrows C 2 ≃ₘ^∞⟮
      𝓘(ℝ, Fin (nerveModelDim (finrank ℝ E) (finrank ℝ E') 2) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} := by
  letI := nerveChartedSpace I J C 2
  letI := composablePairsChartedSpace I J C
  letI := categoricalComposablePairsChartedSpace I J C
  exact (nerveTwoCategoricalDiffeomorph I J C).trans (composablePairsSwapDiffeomorph I J C).symm

@[simp]
theorem nerveTwoDiffeomorph_apply (F : ComposableArrows C 2) :
    letI := nerveChartedSpace I J C 2
    letI := composablePairsChartedSpace I J C
    (nerveTwoDiffeomorph I J C F).val =
      (F.totalArrow 1 2 (by decide), F.totalArrow 0 1 (Fin.zero_le _)) := by
  let := nerveChartedSpace I J C 2
  let := composablePairsChartedSpace I J C
  let := categoricalComposablePairsChartedSpace I J C
  simp only [nerveTwoDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    composablePairsSwapDiffeomorph_symm_apply, nerveTwoCategoricalDiffeomorph_apply]

/-! ### Associativity of iterated fibre products of composable triples -/

/-- The smooth manifold atlas on left-associated geometric composable triples
`(Γ ×_{s,t} Γ) ×_{s∘pr₂, t} Γ`. -/
@[instance_reducible]
noncomputable def composableTriplesLeftChartedSpace :
    ChartedSpace
      (Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
        p.1.1.2.left = p.2.right} := by
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  exact transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    ((contMDiff_source I J C).comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.snd)
    (contMDiff_target I J C)
    (transverse_of_isSubmersion_right (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))

/-- The smooth manifold atlas on right-associated geometric composable triples
`Γ ×_{s, t∘pr₁} (Γ ×_{s,t} Γ)`. -/
@[instance_reducible]
noncomputable def composableTriplesRightChartedSpace :
    ChartedSpace
      (Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
        p.1.left = p.2.1.1.right} := by
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  exact transverseFiberProductChartedSpace (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C)
    ((contMDiff_target I J C).comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.fst)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- Left-associated geometric composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesLeft :
    letI := composableTriplesLeftChartedSpace I J C
    IsManifold
      𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
        p.1.1.2.left = p.2.right} := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact isManifold_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    ((contMDiff_source I J C).comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.snd)
    (contMDiff_target I J C)
    (transverse_of_isSubmersion_right (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))

/-- Right-associated geometric composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesRight :
    letI := composableTriplesRightChartedSpace I J C
    IsManifold
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
        p.1.left = p.2.1.1.right} := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact isManifold_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C)
    ((contMDiff_target I J C).comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.fst)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))

/-- The canonical associator diffeomorphism between left- and right-associated geometric composable
triples `(Γ ×_{s,t} Γ) ×_{s∘pr₂, t} Γ ≃ₘ^∞ Γ ×_{s, t∘pr₁} (Γ ×_{s,t} Γ)`. -/
noncomputable def composableTriplesAssocDiffeomorph :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
        p.1.1.2.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ)⟯
      {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
        p.1.left = p.2.1.1.right} := by
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  letI := composableTriplesLeftChartedSpace I J C
  letI := composableTriplesRightChartedSpace I J C
  have hP₂ := isSmoothEmbedding_coe_composablePairs I J C
  have hL := isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    ((contMDiff_source I J C).comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.snd)
    (contMDiff_target I J C)
    (transverse_of_isSubmersion_right (by simp) (isSubmersion_target (I := I) (J := J) (C := C)))
  have hR := isSmoothEmbedding_coe_transverseFiberProduct (n := (∞ : ℕ∞ω)) (by simp)
    (contMDiff_source I J C)
    ((contMDiff_target I J C).comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff.fst)
    (transverse_of_isSubmersion_left (by simp) (isSubmersion_source (I := I) (J := J) (C := C)))
  exact fiberProductAssocDiffeomorph hP₂ hP₂ hL hR

@[simp]
theorem composableTriplesAssocDiffeomorph_apply
    (p : {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
      p.1.1.2.left = p.2.right}) :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    composableTriplesAssocDiffeomorph I J C p =
      ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), p.2⟩), p.1.1.2⟩ := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let := composableTriplesLeftChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  exact fiberProductAssocDiffeomorph_apply _ _ _ _ p

@[simp]
theorem composableTriplesAssocDiffeomorph_symm_apply
    (p : {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
      p.1.left = p.2.1.1.right}) :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    (composableTriplesAssocDiffeomorph I J C).symm p =
      ⟨(⟨(p.1.1, p.1.2.1.1), p.2⟩, p.1.2.1.2), p.1.2.2⟩ := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let := composableTriplesLeftChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  exact fiberProductAssocDiffeomorph_symm_apply _ _ _ _ p

end Nerve

end TauCeti.IsLieGroupoid
