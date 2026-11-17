/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel

/-!
# Source and target fibres and translations of a Lie groupoid

For a Lie groupoid `C` (`TauCeti.IsLieGroupoid`), every object `x : C` is a regular value of both
the source map `s = Quiver.Total.left` and the target map `t = Quiver.Total.right`. Consequently,
the regular-fibre construction (`TauCeti.regularFiberChartedSpace`) equips every source fibre
`s⁻¹(x) = {a : Quiver.Total C // a.left = x}` and every target fibre
`t⁻¹(x) = {a : Quiver.Total C // a.right = x}` with a smooth (`C^∞`) embedded submanifold
structure of dimension `dim Γ - dim M`, carrying the subspace topology.

For an arrow `g : Quiver.Total C` running from `s(g) = g.left` to `t(g) = g.right`:
* left multiplication `h ↦ gh` (`h.comp g`) is defined precisely on the target fibre `t⁻¹(s(g))`
  and gives a smooth diffeomorphism `t⁻¹(s(g)) ≃ₘ^∞ t⁻¹(t(g))` preserving the source map;
* right multiplication `h ↦ hg` (`g.comp h`) is defined precisely on the source fibre `s⁻¹(t(g))`
  and gives a smooth diffeomorphism `s⁻¹(t(g)) ≃ₘ^∞ s⁻¹(s(g))` preserving the target map;
* arrow inversion identifies the source fibre `s⁻¹(x)` diffeomorphically with the target fibre
  `t⁻¹(x)`, intertwining right translation by `g` with left translation by `g⁻¹`.

No global `ChartedSpace` instance is installed on the fibres; consumers bind
`sourceFiberChartedSpace` or `targetFiberChartedSpace` locally with `letI`.

## Main definitions

* `TauCeti.IsLieGroupoid.sourceFiberChartedSpace`, `TauCeti.IsLieGroupoid.targetFiberChartedSpace`:
  the regular-fibre smooth atlases on `s⁻¹(x)` and `t⁻¹(x)`.
* `TauCeti.IsLieGroupoid.inverseSourceToTargetDiffeomorph`: arrow inversion as a `C^∞`
  diffeomorphism `s⁻¹(x) ≃ₘ^∞ t⁻¹(x)`.
* `TauCeti.IsLieGroupoid.leftTranslationDiffeomorph`: left translation
  `t⁻¹(s(g)) ≃ₘ^∞ t⁻¹(t(g))`, `h ↦ gh`.
* `TauCeti.IsLieGroupoid.rightTranslationDiffeomorph`: right translation
  `s⁻¹(t(g)) ≃ₘ^∞ s⁻¹(s(g))`, `h ↦ hg`.

## Main results

* `TauCeti.IsLieGroupoid.isManifold_sourceFiber`, `TauCeti.IsLieGroupoid.isManifold_targetFiber`:
  every source fibre and every target fibre is a smooth manifold of dimension `dim Γ - dim M`.
* `TauCeti.IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber`,
  `TauCeti.IsLieGroupoid.isSmoothEmbedding_coe_targetFiber`: the fibre inclusions are smooth
  embeddings.
* `TauCeti.IsLieGroupoid.range_mfderiv_coe_sourceFiber`,
  `TauCeti.IsLieGroupoid.range_mfderiv_coe_targetFiber`: the tangent spaces of `s⁻¹(x)` and
  `t⁻¹(x)` identify with `ker ds` and `ker dt`.
* `TauCeti.IsLieGroupoid.leftTranslationDiffeomorph_unit`,
  `TauCeti.IsLieGroupoid.leftTranslationDiffeomorph_comp_val`,
  `TauCeti.IsLieGroupoid.leftTranslationDiffeomorph_trans`,
  `TauCeti.IsLieGroupoid.leftTranslationDiffeomorph_symm_eq`: functoriality and inverse laws for
  left translations.
* `TauCeti.IsLieGroupoid.rightTranslationDiffeomorph_unit`,
  `TauCeti.IsLieGroupoid.rightTranslationDiffeomorph_comp_val`,
  `TauCeti.IsLieGroupoid.rightTranslationDiffeomorph_trans`,
  `TauCeti.IsLieGroupoid.rightTranslationDiffeomorph_symm_eq`: contravariant functoriality and
  inverse laws for right translations.
* `TauCeti.IsLieGroupoid.inverseSourceToTargetDiffeomorph_rightTranslation`,
  `TauCeti.IsLieGroupoid.inverseSourceToTargetDiffeomorph_symm_leftTranslation`: inversion
  intertwines right translation by `g` with left translation by `g⁻¹`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1 and Section 1.4.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
-/

public section

open CategoryTheory Manifold Module
open scoped ContDiff Manifold

namespace TauCeti.IsLieGroupoid

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

/-! ### Source fibres -/

/-- The smooth manifold atlas on the source fibre `s⁻¹(x) = {a : Quiver.Total C // a.left = x}`,
equipped with its subspace topology via `TauCeti.regularFiberChartedSpace`. -/
@[instance_reducible]
noncomputable def sourceFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      {a : Quiver.Total C // a.left = x} :=
  regularFiberChartedSpace (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

/-- Every source fibre `s⁻¹(x)` is a smooth manifold of dimension `dim Γ - dim M`. -/
theorem isManifold_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {a : Quiver.Total C // a.left = x} :=
  isManifold_regularFiber (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

/-- The inclusion of a source fibre `s⁻¹(x) ↪ Γ` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : {a : Quiver.Total C // a.left = x} → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

/-- The tangent space of the source fibre `s⁻¹(x)` maps onto `ker ds`. -/
theorem range_mfderiv_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    ∀ a : {a : Quiver.Total C // a.left = x},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J
        (Subtype.val : {a : Quiver.Total C // a.left = x} → Quiver.Total C) a).range =
        (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) a.1).ker :=
  range_mfderiv_coe_regularFiber (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

/-- The target map restricted to a source fibre `s⁻¹(x) → C` is smooth. -/
theorem contMDiff_target_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) I ∞
      fun a : {a : Quiver.Total C // a.left = x} ↦ a.1.right := by
  let := sourceFiberChartedSpace I J C x
  exact (contMDiff_target I J C).comp (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff

/-! ### Target fibres -/

/-- The smooth manifold atlas on the target fibre `t⁻¹(x) = {a : Quiver.Total C // a.right = x}`,
equipped with its subspace topology via `TauCeti.regularFiberChartedSpace`. -/
@[instance_reducible]
noncomputable def targetFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      {a : Quiver.Total C // a.right = x} :=
  regularFiberChartedSpace (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- Every target fibre `t⁻¹(x)` is a smooth manifold of dimension `dim Γ - dim M`. -/
theorem isManifold_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J C x
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {a : Quiver.Total C // a.right = x} :=
  isManifold_regularFiber (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- The inclusion of a target fibre `t⁻¹(x) ↪ Γ` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J C x
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : {a : Quiver.Total C // a.right = x} → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- The tangent space of the target fibre `t⁻¹(x)` maps onto `ker dt`. -/
theorem range_mfderiv_coe_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J C x
    ∀ a : {a : Quiver.Total C // a.right = x},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J
        (Subtype.val : {a : Quiver.Total C // a.right = x} → Quiver.Total C) a).range =
        (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) a.1).ker :=
  range_mfderiv_coe_regularFiber (m := (∞ : ℕ∞ω)) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- The source map restricted to a target fibre `t⁻¹(x) → C` is smooth. -/
theorem contMDiff_source_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J C x
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) I ∞
      fun a : {a : Quiver.Total C // a.right = x} ↦ a.1.left := by
  let := targetFiberChartedSpace I J C x
  exact (contMDiff_source I J C).comp (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff

/-! ### Inversion between source and target fibres -/

/-- Arrow inversion restricts to a `C^∞` diffeomorphism `s⁻¹(x) ≃ₘ^∞ t⁻¹(x)` between the source
fibre and the target fibre over `x`. -/
noncomputable def inverseSourceToTargetDiffeomorph (x : C) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    {a : Quiver.Total C // a.left = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {a : Quiver.Total C // a.right = x} := by
  letI := sourceFiberChartedSpace I J C x
  letI := targetFiberChartedSpace I J C x
  exact
    { toFun := fun a ↦ ⟨⟨a.1.right, a.1.left, inv a.1.hom⟩, a.2⟩
      invFun := fun a ↦ ⟨⟨a.1.right, a.1.left, inv a.1.hom⟩, a.2⟩
      left_inv := fun a ↦ Subtype.ext (by rcases a with ⟨⟨_, _, _⟩, _⟩; simp)
      right_inv := fun a ↦ Subtype.ext (by rcases a with ⟨⟨_, _, _⟩, _⟩; simp)
      contMDiff_toFun :=
        (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff_iff_comp.mpr
          ((contMDiff_inverse (I := I) (J := J) (C := C)).comp
            (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff)
      contMDiff_invFun :=
        (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff_iff_comp.mpr
          ((contMDiff_inverse (I := I) (J := J) (C := C)).comp
            (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff) }

@[simp]
theorem inverseSourceToTargetDiffeomorph_apply (x : C)
    (a : {a : Quiver.Total C // a.left = x}) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    (inverseSourceToTargetDiffeomorph I J C x a).1 =
      ⟨a.1.right, a.1.left, inv a.1.hom⟩ := (rfl)

@[simp]
theorem inverseSourceToTargetDiffeomorph_symm_apply (x : C)
    (a : {a : Quiver.Total C // a.right = x}) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    ((inverseSourceToTargetDiffeomorph I J C x).symm a).1 =
      ⟨a.1.right, a.1.left, inv a.1.hom⟩ := (rfl)

@[simp]
theorem inverseSourceToTargetDiffeomorph_unit (x : C) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    inverseSourceToTargetDiffeomorph I J C x ⟨⟨x, x, 𝟙 x⟩, rfl⟩ = ⟨⟨x, x, 𝟙 x⟩, rfl⟩ := by
  let := sourceFiberChartedSpace I J C x
  let := targetFiberChartedSpace I J C x
  apply Subtype.ext
  simp

/-! ### Left translation on target fibres -/

/-- Left translation by an arrow `g : s(g) → t(g)` is a `C^∞` diffeomorphism
`t⁻¹(s(g)) ≃ₘ^∞ t⁻¹(t(g))` sending `h ↦ gh` (in categorical order `h.comp g`). Its inverse is
left translation by `g⁻¹`. -/
noncomputable def leftTranslationDiffeomorph (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    {h : Quiver.Total C // h.right = g.left} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {h : Quiver.Total C // h.right = g.right} := by
  letI := targetFiberChartedSpace I J C g.left
  letI := targetFiberChartedSpace I J C g.right
  exact
    { toFun := fun h ↦ ⟨h.1.comp g h.2, Quiver.Total.comp_right h.1 g h.2⟩
      invFun := fun k ↦
        ⟨k.1.comp ⟨g.right, g.left, inv g.hom⟩ k.2,
          Quiver.Total.comp_right k.1 ⟨g.right, g.left, inv g.hom⟩ k.2⟩
      left_inv := fun h ↦ Subtype.ext (Quiver.Total.comp_comp_inv h.1 g h.2 (by simp))
      right_inv := fun k ↦ Subtype.ext (Quiver.Total.comp_inv_cancel_right k.1 g k.2 (by simp))
      contMDiff_toFun :=
        (isSmoothEmbedding_coe_targetFiber I J C g.right).contMDiff_iff_comp.mpr
          (contMDiff_comp_of_contMDiff I J C
            (isSmoothEmbedding_coe_targetFiber I J C g.left).contMDiff
            contMDiff_const fun h ↦ h.2)
      contMDiff_invFun :=
        (isSmoothEmbedding_coe_targetFiber I J C g.left).contMDiff_iff_comp.mpr
          (contMDiff_comp_of_contMDiff I J C
            (isSmoothEmbedding_coe_targetFiber I J C g.right).contMDiff
            contMDiff_const fun k ↦ k.2) }

@[simp]
theorem leftTranslationDiffeomorph_apply (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.right = g.left}) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (leftTranslationDiffeomorph I J C g h).1 = h.1.comp g h.2 := (rfl)

@[simp]
theorem leftTranslationDiffeomorph_symm_apply (g : Quiver.Total C)
    (k : {k : Quiver.Total C // k.right = g.right}) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    ((leftTranslationDiffeomorph I J C g).symm k).1 =
      k.1.comp ⟨g.right, g.left, inv g.hom⟩ k.2 := (rfl)

/-- Left translation preserves the source of every arrow in the target fibre. -/
theorem left_leftTranslationDiffeomorph (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.right = g.left}) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (leftTranslationDiffeomorph I J C g h).1.left = h.1.left := by
  let := targetFiberChartedSpace I J C g.left
  let := targetFiberChartedSpace I J C g.right
  exact Quiver.Total.comp_left h.1 g h.2

/-- Left translation by a unit arrow is the identity diffeomorphism on its target fibre. -/
@[simp]
theorem leftTranslationDiffeomorph_unit (x : C)
    (h : {h : Quiver.Total C // h.right = x}) :
    letI := targetFiberChartedSpace I J C x
    leftTranslationDiffeomorph I J C ⟨x, x, 𝟙 x⟩ h = h := by
  let := targetFiberChartedSpace I J C x
  obtain ⟨a, rfl⟩ := h
  apply Subtype.ext
  exact Quiver.Total.comp_id a

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
theorem leftTranslationDiffeomorph_symm_eq (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (leftTranslationDiffeomorph I J C g).symm =
      leftTranslationDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩ := by
  let := targetFiberChartedSpace I J C g.left
  let := targetFiberChartedSpace I J C g.right
  exact Diffeomorph.ext fun _ ↦ Subtype.ext rfl

/-- Left translation is covariant with respect to geometric multiplication:
`L_{g₁ g₂}(h) = L_{g₁}(L_{g₂}(h))`. -/
theorem leftTranslationDiffeomorph_comp_val (g₁ g₂ : Quiver.Total C) (hg : g₁.left = g₂.right)
    (h : {h : Quiver.Total C // h.right = g₂.left}) :
    letI := targetFiberChartedSpace I J C (g₂.comp g₁ hg.symm).left
    letI := targetFiberChartedSpace I J C (g₂.comp g₁ hg.symm).right
    letI := targetFiberChartedSpace I J C g₂.left
    letI := targetFiberChartedSpace I J C g₂.right
    letI := targetFiberChartedSpace I J C g₁.left
    letI := targetFiberChartedSpace I J C g₁.right
    (leftTranslationDiffeomorph I J C (g₂.comp g₁ hg.symm)
        ⟨h.1, h.2.trans (Quiver.Total.comp_left g₂ g₁ hg.symm).symm⟩).1 =
      (leftTranslationDiffeomorph I J C g₁
        ⟨(leftTranslationDiffeomorph I J C g₂ h).1,
          (leftTranslationDiffeomorph I J C g₂ h).2.trans hg.symm⟩).1 := by
  let := targetFiberChartedSpace I J C (g₂.comp g₁ hg.symm).left
  let := targetFiberChartedSpace I J C (g₂.comp g₁ hg.symm).right
  let := targetFiberChartedSpace I J C g₂.left
  let := targetFiberChartedSpace I J C g₂.right
  let := targetFiberChartedSpace I J C g₁.left
  let := targetFiberChartedSpace I J C g₁.right
  exact (Quiver.Total.comp_assoc h.1 g₂ g₁ h.2 hg.symm).symm

/-- For composable morphisms `f : x ⟶ y` and `g : y ⟶ z`, left translation by `f ≫ g` is the
composite of the diffeomorphisms `L_f` and `L_g`. -/
theorem leftTranslationDiffeomorph_trans {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    letI := targetFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C y
    letI := targetFiberChartedSpace I J C z
    (leftTranslationDiffeomorph I J C ⟨x, y, f⟩).trans
        (leftTranslationDiffeomorph I J C ⟨y, z, g⟩) =
      leftTranslationDiffeomorph I J C ⟨x, z, f ≫ g⟩ := by
  let := targetFiberChartedSpace I J C x
  let := targetFiberChartedSpace I J C y
  let := targetFiberChartedSpace I J C z
  refine Diffeomorph.ext fun h ↦ Subtype.ext ?_
  have hcomp := Quiver.Total.comp_assoc h.1 ⟨x, y, f⟩ ⟨y, z, g⟩ h.2 rfl
  simpa only [Diffeomorph.coe_trans, Function.comp_apply, leftTranslationDiffeomorph_apply,
    Quiver.Total.mk_comp_mk] using hcomp

/-! ### Right translation on source fibres -/

/-- Right translation by an arrow `g : s(g) → t(g)` is a `C^∞` diffeomorphism
`s⁻¹(t(g)) ≃ₘ^∞ s⁻¹(s(g))` sending `h ↦ hg` (in categorical order `g.comp h`). Its inverse is
right translation by `g⁻¹`. -/
noncomputable def rightTranslationDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    {h : Quiver.Total C // h.left = g.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {h : Quiver.Total C // h.left = g.left} := by
  letI := sourceFiberChartedSpace I J C g.right
  letI := sourceFiberChartedSpace I J C g.left
  exact
    { toFun := fun h ↦ ⟨g.comp h.1 h.2.symm, Quiver.Total.comp_left g h.1 h.2.symm⟩
      invFun := fun k ↦
        ⟨(⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C).comp k.1 k.2.symm,
          Quiver.Total.comp_left ⟨g.right, g.left, inv g.hom⟩ k.1 k.2.symm⟩
      left_inv := fun h ↦ Subtype.ext (Quiver.Total.inv_comp_comp g h.1 h.2.symm (by simp))
      right_inv := fun k ↦ Subtype.ext (Quiver.Total.comp_inv_comp g k.1 k.2.symm (by simp))
      contMDiff_toFun :=
        (isSmoothEmbedding_coe_sourceFiber I J C g.left).contMDiff_iff_comp.mpr
          (contMDiff_comp_of_contMDiff I J C
            contMDiff_const
            (isSmoothEmbedding_coe_sourceFiber I J C g.right).contMDiff
            fun h ↦ h.2.symm)
      contMDiff_invFun :=
        (isSmoothEmbedding_coe_sourceFiber I J C g.right).contMDiff_iff_comp.mpr
          (contMDiff_comp_of_contMDiff I J C
            contMDiff_const
            (isSmoothEmbedding_coe_sourceFiber I J C g.left).contMDiff
            fun k ↦ k.2.symm) }

@[simp]
theorem rightTranslationDiffeomorph_apply (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.left = g.right}) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    (rightTranslationDiffeomorph I J C g h).1 = g.comp h.1 h.2.symm := (rfl)

@[simp]
theorem rightTranslationDiffeomorph_symm_apply (g : Quiver.Total C)
    (k : {k : Quiver.Total C // k.left = g.left}) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    ((rightTranslationDiffeomorph I J C g).symm k).1 =
      (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C).comp k.1 k.2.symm := (rfl)

/-- Right translation preserves the target of every arrow in the source fibre. -/
theorem right_rightTranslationDiffeomorph (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.left = g.right}) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    (rightTranslationDiffeomorph I J C g h).1.right = h.1.right := by
  let := sourceFiberChartedSpace I J C g.right
  let := sourceFiberChartedSpace I J C g.left
  exact Quiver.Total.comp_right g h.1 h.2.symm

/-- Right translation by a unit arrow is the identity diffeomorphism on its source fibre. -/
@[simp]
theorem rightTranslationDiffeomorph_unit (x : C)
    (h : {h : Quiver.Total C // h.left = x}) :
    letI := sourceFiberChartedSpace I J C x
    rightTranslationDiffeomorph I J C ⟨x, x, 𝟙 x⟩ h = h := by
  let := sourceFiberChartedSpace I J C x
  obtain ⟨a, rfl⟩ := h
  apply Subtype.ext
  exact Quiver.Total.id_comp a

/-- The inverse of right translation by `g` is right translation by `g⁻¹`. -/
theorem rightTranslationDiffeomorph_symm_eq (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    (rightTranslationDiffeomorph I J C g).symm =
      rightTranslationDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩ := by
  let := sourceFiberChartedSpace I J C g.right
  let := sourceFiberChartedSpace I J C g.left
  exact Diffeomorph.ext fun _ ↦ Subtype.ext rfl

/-- Right translation is contravariant with respect to geometric multiplication:
`R_{g₁ g₂}(h) = R_{g₂}(R_{g₁}(h))`. -/
theorem rightTranslationDiffeomorph_comp_val (g₁ g₂ : Quiver.Total C) (hg : g₁.left = g₂.right)
    (h : {h : Quiver.Total C // h.left = g₁.right}) :
    letI := sourceFiberChartedSpace I J C (g₂.comp g₁ hg.symm).right
    letI := sourceFiberChartedSpace I J C (g₂.comp g₁ hg.symm).left
    letI := sourceFiberChartedSpace I J C g₁.right
    letI := sourceFiberChartedSpace I J C g₁.left
    letI := sourceFiberChartedSpace I J C g₂.right
    letI := sourceFiberChartedSpace I J C g₂.left
    (rightTranslationDiffeomorph I J C (g₂.comp g₁ hg.symm)
        ⟨h.1, h.2.trans (Quiver.Total.comp_right g₂ g₁ hg.symm).symm⟩).1 =
      (rightTranslationDiffeomorph I J C g₂
        ⟨(rightTranslationDiffeomorph I J C g₁ h).1,
          (rightTranslationDiffeomorph I J C g₁ h).2.trans hg⟩).1 := by
  let := sourceFiberChartedSpace I J C (g₂.comp g₁ hg.symm).right
  let := sourceFiberChartedSpace I J C (g₂.comp g₁ hg.symm).left
  let := sourceFiberChartedSpace I J C g₁.right
  let := sourceFiberChartedSpace I J C g₁.left
  let := sourceFiberChartedSpace I J C g₂.right
  let := sourceFiberChartedSpace I J C g₂.left
  exact Quiver.Total.comp_assoc g₂ g₁ h.1 hg.symm h.2.symm

/-- For composable morphisms `f : x ⟶ y` and `g : y ⟶ z`, right translation by `f ≫ g` is the
composite of the diffeomorphisms `R_g` and `R_f`. -/
theorem rightTranslationDiffeomorph_trans {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    letI := sourceFiberChartedSpace I J C z
    letI := sourceFiberChartedSpace I J C y
    letI := sourceFiberChartedSpace I J C x
    (rightTranslationDiffeomorph I J C ⟨y, z, g⟩).trans
        (rightTranslationDiffeomorph I J C ⟨x, y, f⟩) =
      rightTranslationDiffeomorph I J C ⟨x, z, f ≫ g⟩ := by
  let := sourceFiberChartedSpace I J C z
  let := sourceFiberChartedSpace I J C y
  let := sourceFiberChartedSpace I J C x
  refine Diffeomorph.ext fun h ↦ Subtype.ext ?_
  have hcomp := Quiver.Total.comp_assoc ⟨x, y, f⟩ ⟨y, z, g⟩ h.1 rfl h.2.symm
  simpa only [Diffeomorph.coe_trans, Function.comp_apply, rightTranslationDiffeomorph_apply,
    Quiver.Total.mk_comp_mk] using hcomp.symm

/-! ### Intertwining of left and right translation under inversion -/

/-- Inversion intertwines right translation by `g` with left translation by `g⁻¹`:
`(hg)⁻¹ = g⁻¹ h⁻¹`. -/
theorem inverseSourceToTargetDiffeomorph_rightTranslation (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.left = g.right}) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    letI := targetFiberChartedSpace I J C g.left
    inverseSourceToTargetDiffeomorph I J C g.left (rightTranslationDiffeomorph I J C g h) =
      leftTranslationDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩
        (inverseSourceToTargetDiffeomorph I J C g.right h) := by
  let := sourceFiberChartedSpace I J C g.right
  let := sourceFiberChartedSpace I J C g.left
  let := targetFiberChartedSpace I J C g.right
  let := targetFiberChartedSpace I J C g.left
  apply Subtype.ext
  exact Quiver.Total.inv_comp_eq g h.1 h.2.symm

/-- Inversion intertwines left translation by `g` with right translation by `g⁻¹`:
`(gh)⁻¹ = h⁻¹ g⁻¹`. -/
theorem inverseSourceToTargetDiffeomorph_symm_leftTranslation (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.right = g.left}) :
    letI := sourceFiberChartedSpace I J C g.left
    letI := sourceFiberChartedSpace I J C g.right
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (inverseSourceToTargetDiffeomorph I J C g.right).symm
        (leftTranslationDiffeomorph I J C g h) =
      rightTranslationDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩
        ((inverseSourceToTargetDiffeomorph I J C g.left).symm h) := by
  let := sourceFiberChartedSpace I J C g.left
  let := sourceFiberChartedSpace I J C g.right
  let := targetFiberChartedSpace I J C g.left
  let := targetFiberChartedSpace I J C g.right
  apply Subtype.ext
  exact Quiver.Total.inv_comp_eq h.1 g h.2

end TauCeti.IsLieGroupoid
