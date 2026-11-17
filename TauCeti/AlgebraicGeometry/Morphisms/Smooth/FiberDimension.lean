/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Fibre dimension of smooth morphisms

For any morphism of schemes `f : X ⟶ Y` and point `y : Y`, the natural number
`AlgebraicGeometry.Scheme.Hom.fiberDimension f y` records the Krull dimension of the
scheme-theoretic fibre `f.fiber y` (defaulting to `0` if the fibre is empty or
infinite-dimensional).

When `f` is smooth and the fibre `f.fiber y` is connected, regularity of the stalks of `f.fiber y`
forces `f.fiber y` to be integral, so it is smooth of relative dimension `f.fiberDimension y` over
`Spec κ(y)` and its Krull dimension equals `f.fiberDimension y` exactly. When every fibre of a
smooth morphism `f` is connected (in particular whenever `f` is smooth and geometrically
connected), the fibre dimension is locally constant on `Y`: around a point `x` in the fibre over
`y`, a standard smooth chart `V ⊆ X` of relative dimension `m` maps onto an open neighbourhood
`f '' V` of `y` on which every fibre contains a nonempty open of Krull dimension `m`.
Consequently, `f` is smooth of relative dimension `n` if and only if every fibre has dimension `n`,
and fibre dimensions add along compositions and fibre products.

Finally, a smooth geometrically connected morphism whose fibres all have dimension zero is étale,
surjective, and universally injective (its base-changed fibres are integral of dimension zero,
hence singletons), and therefore an isomorphism.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.fiberDimension`: the Krull dimension of `f.fiber y` as a natural
  number.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_fiber_eq_fiberDimension`: for a smooth morphism
  with connected fibre at `y`, `topologicalKrullDim (f.fiber y) = f.fiberDimension y`.
* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_fiberToSpecResidueField`: the fibre over
  `y` is smooth of relative dimension `f.fiberDimension y`.
* `AlgebraicGeometry.Scheme.Hom.isLocallyConstant_fiberDimension`: for a smooth morphism with
  connected fibres, `f.fiberDimension` is locally constant on the base.
* `TauCeti.AlgebraicGeometry.fiberDimension_eq_of_isPullback`: for a locally finite type
  morphism, fibre dimension is preserved by arbitrary base change.
* `AlgebraicGeometry.Scheme.Hom.fiberDimension_comp` and
  `AlgebraicGeometry.Scheme.Hom.fiberDimension_pullback_fst_comp`: additivity of fibre dimension
  under composition and fibre products of smooth morphisms with connected fibres.
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_forall_fiberDimension_eq`: a smooth
  morphism with connected fibres is smooth of relative dimension `n` if and only if all fibres
  have dimension `n`.
* `TauCeti.AlgebraicGeometry.isIso_iff_forall_fiberDimension_eq_zero`: a smooth geometrically
  connected morphism is an isomorphism if and only if all of its fibres have dimension zero.

## References

* Stacks Project, Tag 025G (étale universally injective morphisms are open immersions).
* Stacks Project, Tag 02K5 (relative dimension of smooth morphisms).
-/

public section

open CategoryTheory Limits RingHom TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- The Krull dimension of the scheme-theoretic fibre `f.fiber y`, as a natural number.
When `f` is smooth with connected fibre at `y`, this equals `topologicalKrullDim (f.fiber y)`
exactly (`topologicalKrullDim_fiber_eq_fiberDimension`). -/
noncomputable def fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) : ℕ :=
  ((topologicalKrullDim (f.fiber y)).unbotD 0).toNat

/-- Around every point of a smooth morphism, there is an open neighbourhood on which the morphism
is smooth of some fixed relative dimension. -/
private lemma exists_open_smoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) :
    ∃ (V : X.Opens) (m : ℕ), x ∈ V ∧ SmoothOfRelativeDimension m (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth f x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hst
  have hm : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    ⟨_, _, _, ‹_›, P, rfl⟩
  have : IsAffine V := hV
  refine ⟨V, P.dimension, hxV, ⟨fun v ↦ ?_⟩⟩
  have e' : ⊤ ≤ (V.ι ≫ f) ⁻¹ᵁ U := fun z _ ↦ e z.2
  refine ⟨U, hU, ⊤, isAffineOpen_top V, trivial, e', ?_⟩
  have htop : V.ι ''ᵁ ⊤ = V := V.ι.image_top_eq_opensRange.trans V.opensRange_ι
  have e'' : V.ι ''ᵁ ⊤ ≤ f ⁻¹ᵁ U := htop.le.trans e
  have hcomp :
      (V.ι ≫ f).appLE U ⊤ e' = f.appLE U (V.ι ''ᵁ ⊤) e'' ≫ (V.ι.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  have happ : f.appLE U (V.ι ''ᵁ ⊤) e'' =
      f.appLE U V e ≫ X.presheaf.map (eqToHom htop).op := by
    rw [Scheme.Hom.appLE_map]
  rw [hcomp, happ, Category.assoc]
  exact ((isStandardSmoothOfRelativeDimension_respectsIso (n := P.dimension)).cancel_right_isIso
    (f.appLE U V e) (X.presheaf.map (eqToHom htop).op ≫ (V.ι.appIso ⊤).hom)).mpr hm

/-- A connected fibre of a smooth morphism is integral. -/
private lemma isIntegral_fiber_of_smooth_of_connected {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (y : Y) [ConnectedSpace (f.fiber y)] : IsIntegral (f.fiber y) := by
  have : Smooth (f.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd f (Y.fromSpecResidueField y)))
  have : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  have : ∀ z : f.fiber y, IsRegularLocalRing ((f.fiber y).presheaf.stalk z) :=
    isRegularLocalRing_stalk_of_smooth (f.fiberToSpecResidueField y)
  exact isIntegral_of_connected_of_isRegularLocalRing_stalk (f.fiber y)

/-- If `f` is smooth of relative dimension `m` on an open `V ⊆ X` meeting the connected fibre over
`y`, then `f.fiber y` has Krull dimension `m`. -/
private lemma topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_comp_ι {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (y : Y) [ConnectedSpace (f.fiber y)] (V : X.Opens) (m : ℕ)
    [SmoothOfRelativeDimension m (V.ι ≫ f)] (hy : y ∈ f '' (V : Set X)) :
    topologicalKrullDim (f.fiber y) = m := by
  obtain ⟨x, hxV, rfl⟩ := hy
  have : IsIntegral (f.fiber (f x)) := isIntegral_fiber_of_smooth_of_connected f (f x)
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField (f x))))
  have hsm : SmoothOfRelativeDimension m ((V.ι ≫ f).fiberToSpecResidueField (f x)) :=
    inferInstanceAs (SmoothOfRelativeDimension m
      (pullback.snd (V.ι ≫ f) (Y.fromSpecResidueField (f x))))
  have : Nonempty ((V.ι ≫ f) ⁻¹' {f x}) := ⟨⟨⟨x, hxV⟩, rfl⟩⟩
  have hne : Nonempty ((V.ι ≫ f).fiber (f x)) :=
    ⟨((V.ι ≫ f).fiberHomeo (f x)).symm ⟨⟨x, hxV⟩, rfl⟩⟩
  have hVdim : topologicalKrullDim ((V.ι ≫ f).fiber (f x)) = m :=
    @topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y.residueField (f x)) inferInstance _
      ((V.ι ≫ f).fiberToSpecResidueField (f x)) hne m hsm
  have hopen := isOpenEmbedding_fiber V.ι f (f x)
  have hdim_eq :
      topologicalKrullDim (V.ι ⁻¹' (f ⁻¹' {f x})) = topologicalKrullDim (f.fiber (f x)) :=
    @topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType (Y.residueField (f x))
      inferInstance _ (f.fiberToSpecResidueField (f x)) hft inferInstance _ _ this _ hopen
  rw [← hdim_eq, ← hVdim]
  exact ((V.ι ≫ f).fiberHomeo (f x)).isHomeomorph.topologicalKrullDim_eq.symm

/-- For a smooth morphism whose fibre at `y` is connected, `f.fiberDimension y` equals the Krull
dimension of `f.fiber y`. -/
theorem topologicalKrullDim_fiber_eq_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (y : Y) [ConnectedSpace (f.fiber y)] :
    topologicalKrullDim (f.fiber y) = f.fiberDimension y := by
  obtain ⟨z⟩ : Nonempty (f.fiber y) := inferInstance
  have hy : f (f.fiberι y z) = y := ((f.fiberHomeo y) z).2
  obtain ⟨V, m, hxV, hVm⟩ := exists_open_smoothOfRelativeDimension f (f.fiberι y z)
  have hdim : topologicalKrullDim (f.fiber y) = m :=
    topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_comp_ι f y V m ⟨_, hxV, hy⟩
  simp [fiberDimension, hdim]

/-- A connected fibre of a smooth morphism `f : X ⟶ Y` at `y` is smooth of relative dimension
`f.fiberDimension y` over `Spec κ(y)`. -/
theorem smoothOfRelativeDimension_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] (y : Y) [ConnectedSpace (f.fiber y)] :
    SmoothOfRelativeDimension (f.fiberDimension y) (f.fiberToSpecResidueField y) := by
  have : IsIntegral (f.fiber y) := isIntegral_fiber_of_smooth_of_connected f y
  have hsm : Smooth (f.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd f (Y.fromSpecResidueField y)))
  exact @smoothOfRelativeDimension_of_topologicalKrullDim_eq (Y.residueField y) inferInstance _
    (f.fiberToSpecResidueField y) hsm inferInstance _
    (f.topologicalKrullDim_fiber_eq_fiberDimension y)

/-- A morphism smooth of relative dimension `n` has fibre dimension `n` at every point whose fibre
is nonempty. -/
theorem fiberDimension_eq_of_smoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    [SmoothOfRelativeDimension n f] (y : Y) [Nonempty (f.fiber y)] :
    f.fiberDimension y = n := by
  have hsm : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
    inferInstanceAs (SmoothOfRelativeDimension n (pullback.snd f (Y.fromSpecResidueField y)))
  have hdim : topologicalKrullDim (f.fiber y) = n :=
    @topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y.residueField y) inferInstance _
      (f.fiberToSpecResidueField y) inferInstance n hsm
  simp [fiberDimension, hdim]

/-- For a smooth morphism with connected fibres (in particular, any smooth geometrically connected
morphism), the fibre dimension is locally constant on the base. -/
theorem isLocallyConstant_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [∀ y : Y, ConnectedSpace (f.fiber y)] :
    IsLocallyConstant f.fiberDimension := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  obtain ⟨z⟩ : Nonempty (f.fiber y) := inferInstance
  have hy : f (f.fiberι y z) = y := ((f.fiberHomeo y) z).2
  obtain ⟨V, m, hxV, hVm⟩ := exists_open_smoothOfRelativeDimension f (f.fiberι y z)
  refine ⟨f '' (V : Set X), f.isOpenMap _ V.isOpen, ⟨_, hxV, hy⟩, fun y' hy' ↦ ?_⟩
  have hy_dim : topologicalKrullDim (f.fiber y) = m :=
    topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_comp_ι f y V m ⟨_, hxV, hy⟩
  have hy'_dim : topologicalKrullDim (f.fiber y') = m :=
    topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_comp_ι f y' V m hy'
  simp [fiberDimension, hy_dim, hy'_dim]

/-- Every isomorphism has fibre dimension zero everywhere. -/
@[simp]
theorem fiberDimension_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (y : Y) :
    f.fiberDimension y = 0 := by
  have : Nonempty (f.fiber y) :=
    ⟨(f.fiberHomeo y).symm ⟨inv f y, by simp [← Scheme.Hom.comp_apply]⟩⟩
  exact f.fiberDimension_eq_of_smoothOfRelativeDimension y

/-- Precomposing with an isomorphism preserves fibre dimension. -/
@[simp]
theorem fiberDimension_comp_of_isIso_left {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (f : Y ⟶ Z) (z : Z) : (e ≫ f).fiberDimension z = f.fiberDimension z := by
  have he_inv (y : Y) : e (inv e y) = y := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have hinv_e (x : X) : inv e (e x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  let h : (e ≫ f) ⁻¹' {z} ≃ₜ f ⁻¹' {z} :=
    { toFun := fun x ↦ ⟨e x.1, (Scheme.Hom.comp_apply e f x.1).symm.trans x.2⟩
      invFun := fun y ↦ ⟨inv e y.1,
        Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr
          ((Scheme.Hom.comp_apply e f (inv e y.1)).trans
            ((congrArg f (he_inv y.1)).trans (Set.mem_singleton_iff.mp y.2))))⟩
      left_inv := fun x ↦ Subtype.ext (hinv_e x.1)
      right_inv := fun y ↦ Subtype.ext (he_inv y.1)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((inv e).continuous.comp continuous_subtype_val).subtype_mk _ }
  have hdim : topologicalKrullDim ((e ≫ f).fiber z) = topologicalKrullDim (f.fiber z) :=
    (((e ≫ f).fiberHomeo z).trans
      (h.trans (f.fiberHomeo z).symm)).isHomeomorph.topologicalKrullDim_eq
  simp [fiberDimension, hdim]

/-- Postcomposing with an isomorphism shifts fibre dimension along the isomorphism. -/
@[simp]
theorem fiberDimension_comp_of_isIso_right {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z)
    [IsIso e] (y : Y) : (f ≫ e).fiberDimension (e y) = f.fiberDimension y := by
  have hpre : (f ≫ e) ⁻¹' {e y} = f ⁻¹' {y} := by
    ext x
    exact (asIso e).hom.homeomorph.injective.eq_iff
  have hdim : topologicalKrullDim ((f ≫ e).fiber (e y)) = topologicalKrullDim (f.fiber y) :=
    (((f ≫ e).fiberHomeo (e y)).trans
      ((Homeomorph.setCongr hpre).trans (f.fiberHomeo y).symm)).isHomeomorph.topologicalKrullDim_eq
  simp [fiberDimension, hdim]

end Scheme.Hom

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Fibre dimension of a morphism locally of finite type is invariant under arbitrary base
change. -/
theorem fiberDimension_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [LocallyOfFiniteType f] (y : Y) :
    snd.fiberDimension y = f.fiberDimension (g y) := by
  have hfib := isPullback_fiberToSpecResidueField_of_isPullback h y
  let := (g.residueFieldMap y).hom.toAlgebra
  have hSpec : Spec.map (g.residueFieldMap y) =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (g y)) (Y.residueField y))) := rfl
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Z.fromSpecResidueField (g y))))
  have hdim : topologicalKrullDim (snd.fiber y) = topologicalKrullDim (f.fiber (g y)) :=
    (hfib.isoPullback.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq).trans <| by
      rw [hSpec]
      exact @topologicalKrullDim_pullback_Spec_map_of_field (Z.residueField (g y))
        (Y.residueField y) _ _ _ _ (f.fiberToSpecResidueField (g y)) hft
  simp [Scheme.Hom.fiberDimension, hdim]

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- Fibre dimension along the second projection of a pullback. -/
@[simp]
theorem fiberDimension_pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] (y : Y) :
    (pullback.snd f g).fiberDimension y = f.fiberDimension (g y) :=
  TauCeti.AlgebraicGeometry.fiberDimension_eq_of_isPullback (IsPullback.of_hasPullback f g) y

/-- Fibre dimension along the first projection of a pullback. -/
@[simp]
theorem fiberDimension_pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (x : X) :
    (pullback.fst f g).fiberDimension x = g.fiberDimension (f x) :=
  TauCeti.AlgebraicGeometry.fiberDimension_eq_of_isPullback (IsPullback.of_hasPullback f g).flip x

/-- Over an open subset `U ⊆ Y` where every fibre of a smooth morphism `g : X ⟶ Y` with
connected fibres has dimension `m`, the restriction `g ∣_ U` is smooth of relative
dimension `m`. -/
private lemma smoothOfRelativeDimension_res_of_fiberDimension_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [Smooth g] [∀ y : Y, ConnectedSpace (g.fiber y)] (U : Y.Opens) (m : ℕ)
    (hU : ∀ y ∈ U, g.fiberDimension y = m) :
    SmoothOfRelativeDimension m (g ∣_ U) := by
  have hVm : SmoothOfRelativeDimension m ((g ⁻¹ᵁ U).ι ≫ g) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨W, k, hxW, hWk⟩ := exists_open_smoothOfRelativeDimension ((g ⁻¹ᵁ U).ι ≫ g) x
    have hk_open : SmoothOfRelativeDimension k (((g ⁻¹ᵁ U).ι ''ᵁ W).ι ≫ g) := by
      let e : (W : Scheme.{u}) ≅ ((g ⁻¹ᵁ U).ι ''ᵁ W : Scheme.{u}) :=
        IsOpenImmersion.isoOfRangeEq (W.ι ≫ (g ⁻¹ᵁ U).ι)
          ((g ⁻¹ᵁ U).ι ''ᵁ W).ι <| by
          simp [Scheme.Opens.range_ι, Set.range_comp]
      have he :
          e.inv ≫ W.ι ≫ (g ⁻¹ᵁ U).ι ≫ g = ((g ⁻¹ᵁ U).ι ''ᵁ W).ι ≫ g := by
        rw [← Category.assoc, ← Category.assoc, Category.assoc e.inv,
          IsOpenImmersion.isoOfRangeEq_inv_fac]
      rw [← he]
      have : SmoothOfRelativeDimension (0 + k) (e.inv ≫ W.ι ≫ (g ⁻¹ᵁ U).ι ≫ g) :=
        inferInstance
      simpa using this
    have hk : k = m := by
      have hdim := topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_comp_ι g
        (g x.1) ((g ⁻¹ᵁ U).ι ''ᵁ W) k ⟨x.1, ⟨x, hxW, rfl⟩, rfl⟩
      have h1 : g.fiberDimension (g x.1) = k := by simp [fiberDimension, hdim]
      exact h1.symm.trans (hU (g x.1) x.2)
    have : SmoothOfRelativeDimension m (W.ι ≫ (g ⁻¹ᵁ U).ι ≫ g) := hk ▸ hWk
    obtain ⟨A, B, _, hxB, eB, hchart⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_of_comp_ι
        ((g ⁻¹ᵁ U).ι ≫ g) W m hxW
    exact ⟨A.1, A.2, B.1, B.2, hxB, eB, hchart⟩
  have hq_pb :
      IsPullback (𝟙 (g ⁻¹ᵁ U : Scheme.{u})) (g ∣_ U) ((g ⁻¹ᵁ U).ι ≫ g) U.ι :=
    IsPullback.of_isLimit (c := PullbackCone.mk (𝟙 _) (g ∣_ U) (by simp)) <|
      PullbackCone.isLimitAux' _ fun s ↦
        ⟨s.fst, Category.comp_id _,
          (cancel_mono U.ι).mp (by simpa [Category.assoc] using s.condition),
          fun {t} ht _ ↦ (Category.comp_id t).symm.trans ht⟩
  exact MorphismProperty.of_isPullback hq_pb hVm

/-- The base change of a smooth morphism `g : X ⟶ Y` (with connected fibres) to the fibre of
`f : Y ⟶ Z` over `f y` is smooth of constant relative dimension `g.fiberDimension y`. -/
private lemma smoothOfRelativeDimension_pullback_snd_fiberι {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) [Smooth g] [∀ y : Y, ConnectedSpace (g.fiber y)] (y : Y)
    [ConnectedSpace (f.fiber (f y))] :
    SmoothOfRelativeDimension (g.fiberDimension y) (pullback.snd g (f.fiberι (f y))) := by
  let m := g.fiberDimension y
  let U : Y.Opens := ⟨g.fiberDimension ⁻¹' {m}, g.isLocallyConstant_fiberDimension {m}⟩
  have hconst : IsLocallyConstant (g.fiberDimension ∘ f.fiberι (f y)) :=
    g.isLocallyConstant_fiberDimension.comp_continuous (f.fiberι (f y)).continuous
  have hrange : Set.range (f.fiberι (f y)) ⊆ (U : Set Y) := by
    rintro _ ⟨w, rfl⟩
    have hwy := hconst.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ w)
      (Set.mem_univ (f.asFiber y))
    simpa [U, m] using hwy
  have : SmoothOfRelativeDimension m (g ∣_ U) :=
    smoothOfRelativeDimension_res_of_fiberDimension_eq g U m fun _ hyU ↦ hyU
  let j : f.fiber (f y) ⟶ U :=
    IsOpenImmersion.lift U.ι (f.fiberι (f y)) (by simpa [Scheme.Opens.range_ι])
  have hj : j ≫ U.ι = f.fiberι (f y) := IsOpenImmersion.lift_fac _ _ _
  let p : pullback g (f.fiberι (f y)) ⟶ f.fiber (f y) := pullback.snd g (f.fiberι (f y))
  have hfst_range :
      Set.range (pullback.fst g (f.fiberι (f y))) ⊆ Set.range (g ⁻¹ᵁ U).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : g (pullback.fst g (f.fiberι (f y)) w) = f.fiberι (f y) (p w) := by
      have hcond := congrArg (fun k : pullback g (f.fiberι (f y)) ⟶ Y ↦ k w)
        (pullback.condition (f := g) (g := f.fiberι (f y)))
      exact (Scheme.Hom.comp_apply _ _ w).symm.trans (hcond.trans (Scheme.Hom.comp_apply _ _ w))
    exact Set.mem_preimage.mpr (hw.symm ▸ hrange ⟨p w, rfl⟩)
  let fst' : pullback g (f.fiberι (f y)) ⟶ (g ⁻¹ᵁ U : Scheme.{u}) :=
    IsOpenImmersion.lift (g ⁻¹ᵁ U).ι (pullback.fst g (f.fiberι (f y))) hfst_range
  have hfst' : fst' ≫ (g ⁻¹ᵁ U).ι = pullback.fst g (f.fiberι (f y)) :=
    IsOpenImmersion.lift_fac _ _ _
  have hp_pb : IsPullback fst' p (g ∣_ U) j := by
    refine IsPullback.of_right (h₁₂ := (g ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ ?_
      (isPullback_morphismRestrict g U).flip
    · rw [hfst', hj]
      exact IsPullback.of_hasPullback g (f.fiberι (f y))
    · exact (cancel_mono U.ι).mp <| by
        rw [Category.assoc, (isPullback_morphismRestrict g U).w, ← Category.assoc, hfst',
          Category.assoc, hj]
        exact pullback.condition
  exact MorphismProperty.of_isPullback hp_pb inferInstance

/-- Fibre dimensions add under composition of smooth morphisms when `g` has connected fibres and
`f.fiber (f y)` is connected. -/
theorem fiberDimension_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    [Smooth g] [∀ y : Y, ConnectedSpace (g.fiber y)]
    [Smooth f] (y : Y) [ConnectedSpace (f.fiber (f y))] :
    (g ≫ f).fiberDimension (f y) = g.fiberDimension y + f.fiberDimension (f y) := by
  let m := g.fiberDimension y
  let n := f.fiberDimension (f y)
  let p : pullback g (f.fiberι (f y)) ⟶ f.fiber (f y) := pullback.snd g (f.fiberι (f y))
  have : SmoothOfRelativeDimension m p := smoothOfRelativeDimension_pullback_snd_fiberι g f y
  have : SmoothOfRelativeDimension n (f.fiberToSpecResidueField (f y)) :=
    f.smoothOfRelativeDimension_fiberToSpecResidueField (f y)
  have hgf_pb :
      IsPullback (pullback.fst g (f.fiberι (f y))) (p ≫ f.fiberToSpecResidueField (f y))
        (g ≫ f) (Z.fromSpecResidueField (f y)) :=
    (IsPullback.of_hasPullback g (f.fiberι (f y))).paste_vert
      (IsPullback.of_hasPullback f (Z.fromSpecResidueField (f y)))
  have hsm_gf : SmoothOfRelativeDimension (m + n) ((g ≫ f).fiberToSpecResidueField (f y)) := by
    dsimp only [fiber, fiberToSpecResidueField]
    rw [← hgf_pb.isoPullback_inv_snd]
    have h0 : SmoothOfRelativeDimension (0 + (m + n))
        (hgf_pb.isoPullback.inv ≫ p ≫ f.fiberToSpecResidueField (f y)) := inferInstance
    simpa [zero_add] using h0
  obtain ⟨z⟩ : Nonempty (g.fiber y) := inferInstance
  have hx : (g ≫ f) (g.fiberι y z) = f y := by
    rw [Scheme.Hom.comp_apply]
    exact congrArg f ((g.fiberHomeo y) z).2
  have hne : Nonempty ((g ≫ f).fiber (f y)) := ⟨((g ≫ f).fiberHomeo (f y)).symm ⟨_, hx⟩⟩
  have hdim : topologicalKrullDim ((g ≫ f).fiber (f y)) = (m + n : ℕ) :=
    @topologicalKrullDim_eq_of_smoothOfRelativeDimension (Z.residueField (f y)) inferInstance _
      ((g ≫ f).fiberToSpecResidueField (f y)) hne (m + n) hsm_gf
  have hto : ((topologicalKrullDim ((g ≫ f).fiber (f y))).unbotD 0).toNat = m + n := by
    rw [hdim]
    exact ENat.toNat_natCast (m + n)
  exact hto

/-- For morphisms `f : X ⟶ S`, `g : Y ⟶ S`, and `h : T ⟶ S`, the fibre product
`(X ×_S T) ×_T (Y ×_S T)` is a pullback of `pullback.fst f g ≫ f` along `h`. -/
private lemma isPullback_pullback_snd_pullback {X Y T S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : T ⟶ S) :
    IsPullback
      (pullback.lift
        (pullback.fst (pullback.snd f h) (pullback.snd g h) ≫ pullback.fst f h)
        (pullback.snd (pullback.snd f h) (pullback.snd g h) ≫ pullback.fst g h)
        (by
          rw [Category.assoc, pullback.condition, Category.assoc, pullback.condition,
            ← Category.assoc, ← Category.assoc, pullback.condition]))
      (pullback.fst (pullback.snd f h) (pullback.snd g h) ≫ pullback.snd f h)
      (pullback.fst f g ≫ f) h := by
  let u := pullback.lift
    (pullback.fst (pullback.snd f h) (pullback.snd g h) ≫ pullback.fst f h)
    (pullback.snd (pullback.snd f h) (pullback.snd g h) ≫ pullback.fst g h)
    (by
      rw [Category.assoc, pullback.condition, Category.assoc, pullback.condition,
        ← Category.assoc, ← Category.assoc, pullback.condition])
  refine IsPullback.of_isLimit (c := PullbackCone.mk u _ ?_) (PullbackCone.isLimitAux' _ ?_)
  · dsimp only [u]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, pullback.condition]
  · intro c
    let w₁ : c.pt ⟶ pullback f h :=
      pullback.lift (c.fst ≫ pullback.fst f g) c.snd (by simpa [Category.assoc] using c.condition)
    let w₂ : c.pt ⟶ pullback g h :=
      pullback.lift (c.fst ≫ pullback.snd f g) c.snd <| by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc]
        simpa [Category.assoc] using c.condition
    refine ⟨pullback.lift w₁ w₂ (by simp [w₁, w₂]), ?_, ?_, ?_⟩
    · apply pullback.hom_ext <;> simp [u, w₁, w₂]
    · simp [w₁]
    · intro m hm₁ hm₂
      dsimp only [PullbackCone.mk_pt, PullbackCone.mk_fst, PullbackCone.mk_snd] at m hm₁ hm₂ ⊢
      apply pullback.hom_ext <;> apply pullback.hom_ext
      · simpa [u, w₁, Category.assoc] using congrArg (· ≫ pullback.fst f g) hm₁
      · simpa [w₁, Category.assoc] using hm₂
      · simpa [u, w₂, Category.assoc] using congrArg (· ≫ pullback.snd f g) hm₁
      · have hcond := congrArg (m ≫ ·)
          (pullback.condition (f := pullback.snd f h) (g := pullback.snd g h))
        simpa [w₂, Category.assoc] using hcond.symm.trans hm₂

/-- Fibre dimensions add for the fibre product of two smooth morphisms whose fibres over `s` are
connected (no connectedness assumption on the product fibre is needed). -/
theorem fiberDimension_pullback_fst_comp {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Smooth f] [Smooth g] (s : S)
    [ConnectedSpace (f.fiber s)] [ConnectedSpace (g.fiber s)] :
    (pullback.fst f g ≫ f).fiberDimension s = f.fiberDimension s + g.fiberDimension s := by
  let m := f.fiberDimension s
  let n := g.fiberDimension s
  let h := S.fromSpecResidueField s
  have : SmoothOfRelativeDimension m (pullback.snd f h) :=
    f.smoothOfRelativeDimension_fiberToSpecResidueField s
  have : SmoothOfRelativeDimension n (pullback.snd g h) :=
    g.smoothOfRelativeDimension_fiberToSpecResidueField s
  have : SmoothOfRelativeDimension n (pullback.fst (pullback.snd f h) (pullback.snd g h)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hpb := isPullback_pullback_snd_pullback f g h
  have hsm : SmoothOfRelativeDimension (n + m)
      ((pullback.fst f g ≫ f).fiberToSpecResidueField s) := by
    dsimp only [fiber, fiberToSpecResidueField]
    rw [← hpb.isoPullback_inv_snd]
    have h0 : SmoothOfRelativeDimension (0 + (n + m))
        (hpb.isoPullback.inv ≫ pullback.fst (pullback.snd f h) (pullback.snd g h) ≫
          pullback.snd f h) := inferInstance
    simpa [zero_add] using h0
  have : Nonempty (pullback f h : Scheme.{u}) := inferInstanceAs (Nonempty (f.fiber s))
  have : Nonempty (pullback g h : Scheme.{u}) := inferInstanceAs (Nonempty (g.fiber s))
  let P : Scheme.{u} := pullback (pullback.snd f h) (pullback.snd g h)
  have : Nonempty P := inferInstance
  have hne : Nonempty ((pullback.fst f g ≫ f).fiber s) :=
    ⟨hpb.isoPullback.hom (Classical.arbitrary P)⟩
  have hdim : topologicalKrullDim ((pullback.fst f g ≫ f).fiber s) = (n + m : ℕ) :=
    @topologicalKrullDim_eq_of_smoothOfRelativeDimension (S.residueField s) inferInstance _
      ((pullback.fst f g ≫ f).fiberToSpecResidueField s) hne (n + m) hsm
  have hto :
      ((topologicalKrullDim ((pullback.fst f g ≫ f).fiber s)).unbotD 0).toNat = m + n := by
    rw [hdim, add_comm]
    exact ENat.toNat_natCast (m + n)
  exact hto

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- A smooth morphism with connected fibres is smooth of relative dimension `n` if and only if
every fibre has dimension `n`. -/
theorem smoothOfRelativeDimension_iff_forall_fiberDimension_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [∀ y : Y, ConnectedSpace (f.fiber y)] (n : ℕ) :
    SmoothOfRelativeDimension n f ↔ ∀ y : Y, f.fiberDimension y = n := by
  refine ⟨fun _ y ↦ f.fiberDimension_eq_of_smoothOfRelativeDimension y,
    fun hdim ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨V, m, hxV, hVm⟩ := Scheme.Hom.exists_open_smoothOfRelativeDimension f x
  have hm : m = n := by
    have h1 := Scheme.Hom.topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_comp_ι
      f (f x) V m ⟨x, hxV, rfl⟩
    have h2 : f.fiberDimension (f x) = m := by simp [Scheme.Hom.fiberDimension, h1]
    exact h2.symm.trans (hdim (f x))
  have : SmoothOfRelativeDimension n (V.ι ≫ f) := hm ▸ hVm
  obtain ⟨W, V', _, hxV', e, hchart⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_of_comp_ι f V n hxV
  exact ⟨W.1, W.2, V'.1, V'.2, hxV', e, hchart⟩

/-- A smooth, geometrically connected morphism is an isomorphism if and only if every fibre has
dimension zero. -/
theorem isIso_iff_forall_fiberDimension_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [GeometricallyConnected f] :
    IsIso f ↔ ∀ y : Y, f.fiberDimension y = 0 := by
  refine ⟨fun _ y ↦ f.fiberDimension_of_isIso y, fun h0 ↦ ?_⟩
  have : SmoothOfRelativeDimension 0 f :=
    (smoothOfRelativeDimension_iff_forall_fiberDimension_eq f 0).mpr h0
  have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero (f := f)).mpr inferInstance
  have : UniversallyInjective f := by
    refine ⟨fun P Z i₁ i₂ f' h ↦ ?_⟩
    have h' : IsPullback i₁ f' f i₂ := h.flip
    have : Smooth f' := MorphismProperty.of_isPullback h' inferInstance
    have : GeometricallyConnected f' := MorphismProperty.of_isPullback h' inferInstance
    have : GeometricallyIntegral f' := Smooth.geometricallyIntegral f'
    intro p₁ p₂ hp
    have hdim : topologicalKrullDim (f'.fiber (f' p₁)) = 0 := by
      rw [f'.topologicalKrullDim_fiber_eq_fiberDimension (f' p₁),
        fiberDimension_eq_of_isPullback h' (f' p₁), h0 (i₂ (f' p₁))]
      rfl
    have : Subsingleton (f'.fiber (f' p₁)) :=
      topologicalKrullDim_eq_zero_iff_subsingleton.mp hdim
    have hsub : Subsingleton (f' ⁻¹' {f' p₁}) :=
      (f'.fiberHomeo (f' p₁)).symm.injective.subsingleton
    exact congrArg Subtype.val (@Subsingleton.elim _ hsub ⟨p₁, rfl⟩ ⟨p₂, hp.symm⟩)
  exact isIso_of_etale_of_universallyInjective_of_surjective f

end TauCeti.AlgebraicGeometry
