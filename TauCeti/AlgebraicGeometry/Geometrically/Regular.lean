/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.RingTheory.RegularLocalRing.GeometricallyRegular

import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# Geometrically regular morphisms of schemes and smoothness criteria

A morphism of schemes `f : X ⟶ Y` is *geometrically regular* (`GeometricallyRegular f`) if for
every field `K` and every morphism `Spec K ⟶ Y`, the base change `X ×[Y] Spec K` is a regular
scheme (`IsRegular`). This instantiates `AlgebraicGeometry.geometrically` at `IsRegular`.

Over an imperfect field, regularity of `X` alone does not survive base change and does not imply
smoothness; geometric regularity is the base-change-invariant strengthening that characterizes
smoothness for morphisms locally of finite type over a field, and—combined with flatness and local
finite presentation—for morphisms over an arbitrary base scheme.

## Main declarations

* `TauCeti.AlgebraicGeometry.GeometricallyRegular`: geometric regularity of a morphism of schemes,
  stable under base change and Zariski-local on both source and target.
* `TauCeti.AlgebraicGeometry.Smooth.geometricallyRegular`: smooth morphisms are geometrically
  regular.
* `TauCeti.AlgebraicGeometry.GeometricallyRegular.geometricallyReduced`: geometrically regular
  morphisms are geometrically reduced.
* `TauCeti.AlgebraicGeometry.geometricallyRegular_Spec_iff`: for a finite-type algebra `B` over a
  field `k`, `Spec B ⟶ Spec k` is geometrically regular iff
  `TauCeti.Excellence.GeometricallyRegular k B`.
* `TauCeti.AlgebraicGeometry.Smooth.of_isRegular_of_isPullback_of_perfectField` and
  `TauCeti.AlgebraicGeometry.smooth_iff_isRegular_pullback_of_perfectField`: a morphism locally of
  finite type over `k` is smooth iff its base change to a given perfect field extension `K / k` (in
  particular `AlgebraicClosure k`) is regular.
* `TauCeti.AlgebraicGeometry.smooth_iff_forall_isRegular_pullback_isPurelyInseparable` and
  `TauCeti.AlgebraicGeometry.smooth_iff_geometricallyRegular`: for `f : X ⟶ Spec k` locally of
  finite type, smoothness is equivalent to regularity after all finite purely inseparable base
  changes, and to geometric regularity.
* `TauCeti.AlgebraicGeometry.Smooth.of_geometricallyRegular` and
  `smooth_iff_locallyOfFinitePresentation_and_flat_and_geometricallyRegular`: a morphism is smooth
  iff it is locally of finite presentation, flat, and geometrically regular.

## References

* A. Grothendieck, *Éléments de géométrie algébrique* IV₂, §6.7; IV₄, Théorème 17.5.1 and
  Corollaire 17.5.2.
* [Stacks Project, Tags 0382, 038X, and 01V8](https://stacks.math.columbia.edu/tag/01V8)
-/

public section

open CategoryTheory MorphismProperty Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

universe u

/-- Scheme regularity is closed under scheme isomorphisms. -/
instance isClosedUnderIsomorphisms_isRegular :
    ObjectProperty.IsClosedUnderIsomorphisms IsRegular where
  of_iso e _ := .of_isOpenImmersion e.inv

/-- A morphism of schemes `f : X ⟶ Y` is **geometrically regular** if `X ×[Y] Spec K` is a regular
scheme for every field `K` and every morphism `Spec K ⟶ Y`. -/
@[mk_iff, stacks 0382]
class GeometricallyRegular {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  geometrically_isRegular : geometrically IsRegular f

/-- `GeometricallyRegular` agrees with `AlgebraicGeometry.geometrically IsRegular`. -/
theorem GeometricallyRegular.eq_geometrically :
    @GeometricallyRegular = geometrically IsRegular := by
  ext
  exact geometricallyRegular_iff _

instance : IsStableUnderBaseChange @GeometricallyRegular :=
  GeometricallyRegular.eq_geometrically ▸ inferInstance

instance : RespectsIso @GeometricallyRegular :=
  IsStableUnderBaseChange.respectsIso

instance : IsZariskiLocalAtTarget @GeometricallyRegular :=
  GeometricallyRegular.eq_geometrically ▸ inferInstance

/-- Geometric regularity is Zariski-local on the source: pulling back an open cover of `X` gives an
open cover of every field fiber product `X ×[Y] Spec K`. -/
instance : IsZariskiLocalAtSource @GeometricallyRegular := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 ↦ ?_
  simp only [geometricallyRegular_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  exact ⟨fun hf i K _ y ↦ (isRegular_iff_openCover
      (Scheme.Pullback.openCoverOfLeft 𝒰 f y)).mp (hf K y) i,
    fun hf K _ y ↦ (isRegular_iff_openCover
      (Scheme.Pullback.openCoverOfLeft 𝒰 f y)).mpr fun i ↦ hf i K y⟩

section Stability

variable {W X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Geometric regularity is preserved under arbitrary pullback squares. -/
theorem GeometricallyRegular.of_isPullback {fst : W ⟶ X} {snd : W ⟶ Y}
    (h : IsPullback fst snd f g) [GeometricallyRegular g] : GeometricallyRegular fst :=
  ⟨MorphismProperty.of_isPullback h.flip GeometricallyRegular.geometrically_isRegular⟩

instance [GeometricallyRegular g] : GeometricallyRegular (pullback.fst f g) :=
  GeometricallyRegular.of_isPullback f g (.of_hasPullback f g)

instance [GeometricallyRegular f] : GeometricallyRegular (pullback.snd f g) :=
  GeometricallyRegular.of_isPullback g f (.flip (.of_hasPullback f g))

instance (V : S.Opens) [GeometricallyRegular f] : GeometricallyRegular (f ∣_ V) :=
  GeometricallyRegular.of_isPullback _ f (isPullback_morphismRestrict f V)

instance (s : S) [GeometricallyRegular f] : GeometricallyRegular (f.fiberToSpecResidueField s) :=
  GeometricallyRegular.of_isPullback _ f (.flip (.of_hasPullback f (S.fromSpecResidueField s)))

instance {K : Type u} [Field K] (y : Spec (.of K) ⟶ S) [GeometricallyRegular f] :
    IsRegular (pullback f y) :=
  pullback_of_geometrically GeometricallyRegular.geometrically_isRegular K y

instance {K : Type u} [Field K] (y : Spec (.of K) ⟶ S) [GeometricallyRegular f] :
    IsRegular (pullback y f) :=
  pullback_of_geometrically' GeometricallyRegular.geometrically_isRegular K y

instance (s : S) [GeometricallyRegular f] : IsRegular (f.fiber s) :=
  fiber_of_geometrically GeometricallyRegular.geometrically_isRegular s

/-- A scheme geometrically regular over `Spec K` (or any integral subsingleton scheme) is
regular. -/
theorem GeometricallyRegular.isRegular_of_isIntegral_of_subsingleton [IsIntegral S]
    [Subsingleton S] [GeometricallyRegular f] : IsRegular X :=
  self_of_isIntegral_of_geometrically (GeometricallyRegular.geometrically_isRegular (f := f))

/-- A morphism is geometrically regular if and only if all of its scheme-theoretic fibers are
geometrically regular over their residue fields. -/
theorem GeometricallyRegular.iff_forall_fiberToSpecResidueField :
    GeometricallyRegular f ↔ ∀ s : S, GeometricallyRegular (f.fiberToSpecResidueField s) :=
  (geometricallyRegular_iff f).trans (geometrically_iff_forall_fiberToSpecResidueField.trans
    (forall_congr' fun s ↦ (geometricallyRegular_iff (f.fiberToSpecResidueField s)).symm))

end Stability

/-- Smooth morphisms are geometrically regular: base-changing `f` to any field yields a smooth
morphism over a regular base `Spec K`, whose source is regular. -/
instance (priority := low) Smooth.geometricallyRegular {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyRegular f where
  geometrically_isRegular _ _ _ _ _ snd h := by
    have : Smooth snd := MorphismProperty.of_isPullback h inferInstance
    exact IsRegular.of_smooth snd

/-- Geometrically regular morphisms are geometrically reduced, since every regular scheme is normal
and hence reduced. -/
instance (priority := low) GeometricallyRegular.geometricallyReduced {X Y : Scheme.{u}}
    (f : X ⟶ Y) [GeometricallyRegular f] : GeometricallyReduced f where
  geometrically_isReduced _ _ y _ fst snd h := by
    have : IsRegular _ := GeometricallyRegular.geometrically_isRegular y fst snd h
    infer_instance

section AffineOverField

/-- If `B` is Noetherian and `Spec B ⟶ Spec k` is geometrically regular, then `B` is geometrically
regular over `k` in the ring-theoretic sense (`TauCeti.Excellence.GeometricallyRegular k B`). -/
theorem GeometricallyRegular.excellence_of_Spec {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    [IsNoetherianRing B]
    (hf : GeometricallyRegular (Spec.map (CommRingCat.ofHom (algebraMap k B)))) :
    TauCeti.Excellence.GeometricallyRegular k B where
  isNoetherianRing := inferInstance
  isRegularRing_tensorProduct L _ _ _ _ := by
    have : IsRegular (pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := inferInstance
    have hSpec : IsRegular (Spec (.of (B ⊗[k] L))) :=
      .of_isOpenImmersion (pullbackSpecIso k B L).inv
    have : IsRegularRing (B ⊗[k] L) := (isRegular_Spec_iff (.of (B ⊗[k] L))).mp hSpec
    exact .of_ringEquiv (Algebra.TensorProduct.comm k B L).toRingEquiv

/-- For a finite-type `k`-algebra `B`, `Spec B ⟶ Spec k` is geometrically regular if and only if
`B` is geometrically regular over `k`. -/
theorem geometricallyRegular_Spec_iff {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] :
    GeometricallyRegular (Spec.map (CommRingCat.ofHom (algebraMap k B))) ↔
      TauCeti.Excellence.GeometricallyRegular k B := by
  refine ⟨fun hf ↦ ?_, fun _ ↦ ?_⟩
  · have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
    exact GeometricallyRegular.excellence_of_Spec hf
  · have : Algebra.Smooth k B := TauCeti.Excellence.GeometricallyRegular.smooth
    have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
      exact RingHom.smooth_algebraMap.mpr inferInstance
    infer_instance

end AffineOverField

section SmoothOverField

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- If `f : X ⟶ Spec k` is locally of finite type and its base change `Y` to a perfect field
extension `K / k` is regular, then `f` is smooth: `Y ⟶ Spec K` is smooth over the perfect field `K`,
and smoothness descends along `Spec K ⟶ Spec k`. -/
theorem Smooth.of_isRegular_of_isPullback_of_perfectField {K : Type u} [Field K] [PerfectField K]
    [Algebra k K] {Y : Scheme.{u}} {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of K)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) [IsRegular Y] :
    Smooth f := by
  have : LocallyOfFiniteType snd := MorphismProperty.of_isPullback h inferInstance
  have : Smooth snd := snd.smooth_of_isRegularLocalRing_stalk
  have hpb : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hpb

/-- A morphism locally of finite type over `k` is smooth if and only if a given pullback of `X`
along a perfect field extension `K / k` is regular. -/
theorem smooth_iff_isRegular_of_isPullback_of_perfectField {K : Type u} [Field K] [PerfectField K]
    [Algebra k K] {Y : Scheme.{u}} {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of K)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Smooth f ↔ IsRegular Y :=
  ⟨fun _ ↦ by
      have : Smooth snd := MorphismProperty.of_isPullback h inferInstance
      exact IsRegular.of_smooth snd,
    fun _ ↦ Smooth.of_isRegular_of_isPullback_of_perfectField f h⟩

/-- A morphism locally of finite type over `k` is smooth if and only if its base change to a given
perfect field extension `K / k` is regular. -/
theorem smooth_iff_isRegular_pullback_of_perfectField (K : Type u) [Field K] [PerfectField K]
    [Algebra k K] :
    Smooth f ↔ IsRegular (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  smooth_iff_isRegular_of_isPullback_of_perfectField f (.of_hasPullback _ _)

/-- A morphism locally of finite type over `k` is smooth if and only if its base change to
`AlgebraicClosure k` is regular. -/
theorem smooth_iff_isRegular_pullback_algebraicClosure :
    Smooth f ↔
      IsRegular (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
  smooth_iff_isRegular_pullback_of_perfectField f (AlgebraicClosure k)

/-- If `f : X ⟶ Spec k` is locally of finite type and `X ×[Spec k] Spec L` is regular for every
finite purely inseparable extension `L / k`, then `f` is smooth. -/
theorem Smooth.of_forall_isRegular_pullback_isPurelyInseparable
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [Module.Finite k L] [IsPurelyInseparable k L],
      IsRegular (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))))) :
    Smooth f := by
  have : IsZariskiLocalAtSource @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  change id (Smooth f)
  wlog hX : ∃ B : CommRingCat.{u}, X = Spec B generalizing X f with H
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) X.affineCover]
    intro i
    refine H (X.affineCover.f i ≫ f) (fun L _ _ _ _ ↦ ?_) ⟨_, rfl⟩
    exact (isRegular_iff_openCover (Scheme.Pullback.openCoverOfLeft X.affineCover f _)).mp (h L) i
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hft : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹LocallyOfFiniteType _›
  algebraize [φ.hom]
  have hφ : φ = CommRingCat.ofHom (algebraMap k B) := by
    ext
    simp [RingHom.algebraMap_toAlgebra]
  have hgeom : TauCeti.Excellence.GeometricallyRegular k B := by
    refine ⟨Algebra.FiniteType.isNoetherianRing k B, fun L _ _ _ _ ↦ ?_⟩
    have hpb : IsRegular (pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := hφ ▸ h L
    have hSpec : IsRegular (Spec (.of (B ⊗[k] L))) :=
      .of_isOpenImmersion (pullbackSpecIso k B L).inv
    have : IsRegularRing (B ⊗[k] L) := (isRegular_Spec_iff (.of (B ⊗[k] L))).mp hSpec
    exact .of_ringEquiv (Algebra.TensorProduct.comm k B L).toRingEquiv
  have : Algebra.Smooth k B := TauCeti.Excellence.GeometricallyRegular.smooth
  rw [hφ, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- A morphism locally of finite type over `k` is smooth if and only if its base change to every
finite purely inseparable field extension `L / k` is regular. -/
theorem smooth_iff_forall_isRegular_pullback_isPurelyInseparable :
    Smooth f ↔ ∀ (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
      [IsPurelyInseparable k L],
      IsRegular (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
  ⟨fun _ _ _ _ _ _ ↦ inferInstance,
    Smooth.of_forall_isRegular_pullback_isPurelyInseparable f⟩

/-- **Over a field, a locally finite-type morphism is smooth if and only if it is geometrically
regular.** -/
@[stacks 038X]
theorem smooth_iff_geometricallyRegular : Smooth f ↔ GeometricallyRegular f :=
  ⟨fun _ ↦ inferInstance,
    fun _ ↦ Smooth.of_forall_isRegular_pullback_isPurelyInseparable f fun _ _ _ _ _ ↦ inferInstance⟩

end SmoothOverField

section SmoothArbitraryBase

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Fiberwise regularity criterion for smoothness (EGA IV₄, Corollaire 17.5.2; Stacks 01V8).**
A flat, locally finitely presented, geometrically regular morphism of schemes is smooth. -/
@[stacks 01V8]
theorem Smooth.of_geometricallyRegular [LocallyOfFinitePresentation f] [Flat f]
    [GeometricallyRegular f] : Smooth f :=
  Smooth.of_smooth_fiberToSpecResidueField f fun y ↦ by
    let g : f.fiber y ⟶ Spec (.of (Y.residueField y)) := f.fiberToSpecResidueField y
    have : LocallyOfFiniteType g :=
      MorphismProperty.of_isPullback (.of_hasPullback f (Y.fromSpecResidueField y)) inferInstance
    have : GeometricallyRegular g :=
      inferInstanceAs (GeometricallyRegular (f.fiberToSpecResidueField y))
    exact (smooth_iff_geometricallyRegular g).mpr inferInstance

/-- **Characterization of smooth morphisms of schemes (EGA IV₄, Corollaire 17.5.2; Stacks 01V8).**
A morphism of schemes is smooth if and only if it is locally of finite presentation, flat, and
geometrically regular. -/
@[stacks 01V8]
theorem smooth_iff_locallyOfFinitePresentation_and_flat_and_geometricallyRegular :
    Smooth f ↔ LocallyOfFinitePresentation f ∧ Flat f ∧ GeometricallyRegular f :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨_, _, _⟩ ↦ Smooth.of_geometricallyRegular f⟩

end SmoothArbitraryBase

end TauCeti.AlgebraicGeometry
