/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import TauCeti.Algebra.TensorProduct.CommonOverfield
import TauCeti.RingTheory.Idempotents.Connected.ScalarExtension

/-!
# Geometric connectedness over separably closed fields, field extensions, and affine products

Over a separably closed field `K`, connectedness is geometric: if `X` is a connected scheme over
`K`, then `X ⟶ Spec K` is geometrically connected, so `X ×_K Spec M` is connected for every field
extension `M / K`. Consequently, for any `K`-algebra `M` with connected prime spectrum, the base
change projection `X' ⟶ X` induces a homeomorphism on connected components and identifies each
connected component of `X'` with the preimage of a connected component of `X`.

The proof mirrors the irreducible case:

* Over an algebraically closed field `Ω`, the tensor product of two connected algebras has
  connected spectrum (`TauCeti.connectedSpace_primeSpectrum_tensorProduct_of_isAlgClosed`), so
  `Spec A ⟶ Spec Ω` is geometrically connected whenever `Spec A` is connected.
* For a separably closed field `K`, its algebraic closure `Ω` is purely inseparable over `K`, so
  `Spec (Ω ⊗[K] A) ⟶ Spec A` is a homeomorphism and `Spec Ω ⟶ Spec K` is geometrically connected;
  descent along surjections (`AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective`) gives
  geometric connectedness of `Spec A ⟶ Spec K`, and in particular of `Spec M ⟶ Spec K` for every
  field extension `M / K`.
* For an arbitrary connected scheme `X` over `Spec K`, universal openness and geometric
  connectedness of `Spec M ⟶ Spec K` make `X ×_K Spec M` connected.

Conversely, geometric connectedness over a field `k` is invariant under arbitrary field extensions
`L / k` (`TauCeti.geometricallyConnected_iff_of_isPullback_field`), using a common overfield
(`TauCeti.Algebra.TensorProduct.commonOverfield`). In particular, geometric connectedness over `k`
may be tested after base change to any separably closed extension of `k`.

The file also records compatibility with isomorphisms, affine tensor products, dominant morphisms
over a field, and preimages of connected components under geometrically connected open morphisms.

## Main declarations

* `AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective`: geometric connectedness
  descends along surjective scheme morphisms.
* `AlgebraicGeometry.GeometricallyConnected.of_comp_isDominant`: geometric connectedness over a
  field descends along dominant morphisms.
* `AlgebraicGeometry.Scheme.Hom.preimage_connectedComponent`: preimage of a connected component
  under a geometrically connected open morphism.
* `TauCeti.geometricallyConnected_respectsIso`: geometric connectedness respects isomorphisms.
* `TauCeti.geometricallyConnected_tensorProduct`: the tensor product of two commutative algebras
  with geometrically connected, universally open spectra is geometrically connected.
* `TauCeti.geometricallyConnected_Spec_of_isSepClosed`: over a separably closed field, a morphism
  from a connected affine scheme is geometrically connected.
* `TauCeti.geometricallyConnected_of_isSepClosed`: over a separably closed field, every morphism
  from a connected scheme is geometrically connected.
* `TauCeti.geometricallyConnected_iff_of_isPullback_field`: geometric connectedness over a field is
  invariant under base change to any field extension.
* `TauCeti.geometricallyConnected_iff_connectedSpace_of_isPullback_isSepClosed`: geometric
  connectedness over a field is equivalent to connectedness after base change to a separably closed
  field extension.

The separably-closed and surjection/dominant descent arguments parallel the irreducible case in
`TauCeti.AlgebraicGeometry.Geometrically.Irreducible` (whose surjection and dominant-descent lemmas
were adapted from Axel Delaval, Jie Xu, and Shitan Xu's Jacobian library, commit
`baef7723da528551b7d2f93bd9a9a53303b04dbc`,
`Jacobian/AlgebraicGeometry/Geometrically/Irreducible.lean`).

## References

* The Stacks Project, Section 10.48 (Tag 05DV), *Geometrically connected algebras*.
* The Stacks Project, Section 33.7 (Tag 04KT), *Geometrically connected schemes*.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Geometric connectedness descends along surjections: if `f ≫ g` is geometrically connected and
`f` is surjective, then `g` is geometrically connected. -/
theorem GeometricallyConnected.of_comp_of_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Surjective f] [GeometricallyConnected (f ≫ g)] :
    GeometricallyConnected g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have : ConnectedSpace ↥(pullback f (pullback.fst g x)) :=
    (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff.mpr
      (geometrically_iff_of_isClosedUnderIsomorphisms.mp
        (GeometricallyConnected.geometrically_connectedSpace (f := f ≫ g)) K x)
  exact (pullback.snd f (pullback.fst g x)).surjective.connectedSpace
    (pullback.snd f (pullback.fst g x)).continuous

/-- Base-changing the source of a geometrically connected composite to a field gives a connected
scheme. -/
theorem GeometricallyConnected.connectedSpace_pullback_of_comp
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyConnected (f ≫ g)] {K : Type u} [Field K]
    {x : Spec (.of K) ⟶ Z} {fst : W ⟶ Y} {snd : W ⟶ Spec (.of K)}
    (h : IsPullback fst snd g x) :
    ConnectedSpace ↥(pullback f fst) :=
  GeometricallyConnected.geometrically_connectedSpace _ _ _
    ((IsPullback.of_hasPullback f fst).paste_vert h)

/-- Geometric connectedness of a composite over a field descends along a dominant morphism. -/
theorem GeometricallyConnected.of_comp_isDominant {K : Type u} [Field K]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    (g : Y ⟶ Spec (.of K)) [GeometricallyConnected (f ≫ g)] :
    GeometricallyConnected g := by
  refine ⟨fun L _ x W fst snd h ↦ ?_⟩
  have : ConnectedSpace ↥(pullback f fst) :=
    GeometricallyConnected.connectedSpace_pullback_of_comp f g h
  have : UniversallyOpen fst := MorphismProperty.of_isPullback h.flip inferInstance
  have hdense : Dense (Set.range (pullback.snd f fst)) := by
    rw [Scheme.Pullback.range_snd]
    exact f.denseRange.preimage fst.isOpenMap
  have hconn : _root_.IsConnected (Set.range (pullback.snd f fst)) := by
    simpa only [Set.image_univ] using
      isConnected_univ.image (pullback.snd f fst) (pullback.snd f fst).continuous.continuousOn
  apply connectedSpace_iff_univ.mpr
  simpa only [hdense.closure_eq] using hconn.closure

/-- Under a geometrically connected open morphism `f : X ⟶ S`, the preimage of the connected
component of `f x` is the connected component of `x`. -/
theorem Scheme.Hom.preimage_connectedComponent {X S : Scheme.{u}} (f : X ⟶ S)
    [GeometricallyConnected f] (hf : IsOpenMap f) (x : X) :
    f ⁻¹' connectedComponent (f x) = connectedComponent x := by
  ext y
  simp only [Set.mem_preimage, ← ConnectedComponents.coe_eq_coe']
  exact (f.connectedComponentsHomeomorph hf).injective.eq_iff (a := y) (b := x)

end AlgebraicGeometry

namespace TauCeti

open _root_.AlgebraicGeometry

/-- Geometric connectedness of morphisms of schemes respects isomorphisms, being stable under
base change. -/
instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

section TensorProduct

variable {k : Type u} [CommRing k]

/-- The spectrum of a tensor product of commutative `k`-algebras is geometrically connected over
`k` when the spectra of both factors are geometrically connected and universally open over `k`.
Universal openness is automatic when `k` is a field. -/
theorem geometricallyConnected_tensorProduct
    (S T : Type u) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    [UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap k S)))]
    [UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap k T)))]
    (hS : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (hT : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k T)))) :
    GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k (S ⊗[k] T)))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
    (pullbackSpecIso k S T).hom, pullbackSpecIso_hom_base]
  exact .comp _ _

end TensorProduct

/-- Over an algebraically closed field `K`, every morphism `Spec A ⟶ Spec K` from a connected
affine scheme is geometrically connected. -/
private theorem geometricallyConnected_Spec_of_isAlgClosed {K A : Type u} [Field K]
    [IsAlgClosed K] [CommRing A] [ConnectedSpace (PrimeSpectrum A)]
    (g : Spec (.of A) ⟶ Spec (.of K)) :
    GeometricallyConnected g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  have : ConnectedSpace (PrimeSpectrum (A ⊗[K] M)) :=
    connectedSpace_primeSpectrum_tensorProduct_of_isAlgClosed K A M
  exact (pullbackSpecIso K A M).inv.homeomorph.connectedSpace_iff.mp this

/-- A purely inseparable field extension `L / K` gives a geometrically connected morphism
`Spec L ⟶ Spec K`: its base change to every field is homeomorphic to a point. -/
instance geometricallyConnected_Spec_of_isPurelyInseparable {K L : Type u} [Field K] [Field L]
    [Algebra K L] [IsPurelyInseparable K L] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  have : ConnectedSpace (PrimeSpectrum (M ⊗[K] L)) :=
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable K L M).homeomorph.symm
      |>.connectedSpace_iff.mp inferInstance
  have : ConnectedSpace (PrimeSpectrum (L ⊗[K] M)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv (Algebra.TensorProduct.comm K L M).toRingEquiv)
      |>.connectedSpace_iff.mpr this
  exact (pullbackSpecIso K L M).inv.homeomorph.connectedSpace_iff.mp this

/-- Over a separably closed field `K`, every morphism `Spec A ⟶ Spec K` from a connected affine
scheme is geometrically connected: `Spec (A ⊗[K] M)` is connected for every field `M` over `K`. -/
instance geometricallyConnected_Spec_of_isSepClosed {K A : Type u} [Field K] [IsSepClosed K]
    [CommRing A] [ConnectedSpace (PrimeSpectrum A)] {g : Spec (.of A) ⟶ Spec (.of K)} :
    GeometricallyConnected g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  let Ω := AlgebraicClosure K
  -- `Spec (Ω ⊗[K] A)` is homeomorphic to `Spec A`, since `Ω / K` is purely inseparable.
  let p : Spec (.of (Ω ⊗[K] A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  have hp : IsHomeomorph
      (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight.toRingHom : A →+* Ω ⊗[K] A)) := by
    have h : (Algebra.TensorProduct.includeRight.toRingHom : A →+* Ω ⊗[K] A) =
        (Algebra.TensorProduct.comm K A Ω).toRingHom.comp (algebraMap A (A ⊗[K] Ω)) := by
      ext a
      simp
    rw [h, PrimeSpectrum.comap_comp]
    exact (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable K Ω A).comp
      (PrimeSpectrum.isHomeomorph_comap_of_bijective (Algebra.TensorProduct.comm K A Ω).bijective)
  have : ConnectedSpace (PrimeSpectrum (Ω ⊗[K] A)) :=
    hp.homeomorph.connectedSpace_iff.mpr inferInstance
  have : Surjective p := ⟨hp.surjective⟩
  have := geometricallyConnected_Spec_of_isAlgClosed (K := Ω)
    (Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] A))))
  have : GeometricallyConnected (p ≫ Spec.map φ) := by
    have h : p ≫ Spec.map φ = Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      simp only [p, ← Spec.map_comp]
      congr 1
      ext x
      simp [Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]
    rw [h]
    exact GeometricallyConnected.comp _ _
  exact GeometricallyConnected.of_comp_of_surjective p _

/-- **Over a separably closed field, connectedness of any scheme is geometric**
(Stacks, Lemma 33.7.4 (Tag 04KT)). If `X` is a connected scheme over a separably closed field `K`,
then `f : X ⟶ Spec K` is geometrically connected. No affineness, quasi-compactness, or finite-type
hypothesis is required. -/
theorem geometricallyConnected_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [ConnectedSpace X] :
    GeometricallyConnected f := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  infer_instance

/-- Over a separably closed field `K`, a scheme `X` is geometrically connected over `Spec K` if and
only if `X` is connected. -/
theorem geometricallyConnected_iff_connectedSpace_of_isSepClosed {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    GeometricallyConnected f ↔ ConnectedSpace X :=
  ⟨fun _ ↦ GeometricallyConnected.connectedSpace_of_subsingleton f,
    fun _ ↦ geometricallyConnected_of_isSepClosed f⟩

/-- Let `X` be a scheme over a separably closed field `K` and `X'` its base change to a
`K`-algebra `M` with connected spectrum (for instance a field extension of `K`), with projection
`g : X' ⟶ X`. Then `g` induces a homeomorphism on connected components. -/
noncomputable def connectedComponentsHomeomorphOfIsSepClosed {K M : Type u} [Field K]
    [IsSepClosed K] [CommRing M] [Algebra K M] [ConnectedSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M)))) :
    ConnectedComponents X' ≃ₜ ConnectedComponents X :=
  have : GeometricallyConnected g := MorphismProperty.of_isPullback H.flip inferInstance
  have : UniversallyOpen g := MorphismProperty.of_isPullback H.flip inferInstance
  g.connectedComponentsHomeomorph g.isOpenMap

/-- Over a separably closed field `K`, `connectedComponentsHomeomorphOfIsSepClosed` acts on the
class of a point `x' : X'` by applying the projection `g : X' ⟶ X`. -/
@[simp]
theorem connectedComponentsHomeomorphOfIsSepClosed_mk {K M : Type u} [Field K]
    [IsSepClosed K] [CommRing M] [Algebra K M] [ConnectedSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M)))) (x' : X') :
    connectedComponentsHomeomorphOfIsSepClosed H x' = g x' :=
  (rfl)

/-- Over a separably closed field `K`, base-changing a scheme `X` to a `K`-algebra `M` with
connected spectrum identifies the connected component of each `x' : X'` with the preimage of the
connected component of `g x'`. -/
theorem preimage_connectedComponent_of_isSepClosed {K M : Type u} [Field K]
    [IsSepClosed K] [CommRing M] [Algebra K M] [ConnectedSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M)))) (x' : X') :
    g ⁻¹' connectedComponent (g x') = connectedComponent x' := by
  have : GeometricallyConnected g := MorphismProperty.of_isPullback H.flip inferInstance
  have : UniversallyOpen g := MorphismProperty.of_isPullback H.flip inferInstance
  exact g.preimage_connectedComponent g.isOpenMap x'

/-- **Geometric connectedness over a field descends along any field extension.** If `X'` is the
base change of `f : X ⟶ Spec k` along `Spec L ⟶ Spec k` for a field extension `L / k` and
`f' : X' ⟶ Spec L` is geometrically connected, then `f` is geometrically connected. -/
theorem geometricallyConnected_of_isPullback_field {k L : Type u} [Field k] [Field L]
    [Algebra k L] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of L)}
    {g : X' ⟶ X} (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [GeometricallyConnected f'] :
    GeometricallyConnected f := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  -- Embed `L` and `M` into a common overfield `Ω` over `k`.
  let d := Algebra.TensorProduct.commonOverfield k L M
  let pL : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let pM : Spec (.of M) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k M))
  let iL : Spec (.of d.Ω) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom (algebraMap L d.Ω))
  let iM : Spec (.of d.Ω) ⟶ Spec (.of M) := Spec.map (CommRingCat.ofHom d.right.toRingHom)
  have hcomm : iL ≫ pL = iM ≫ pM := by
    simp only [iL, pL, iM, pM, ← Spec.map_comp]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply k L d.Ω x).symm.trans (d.right.commutes x).symm
  -- Compare the two pullbacks of `f` to `Spec d.Ω` through `Spec L` and through `Spec M`.
  have hL : IsPullback (pullback.fst f' iL ≫ g) (pullback.snd f' iL) f (iL ≫ pL) :=
    (IsPullback.of_hasPullback f' iL).paste_horiz H
  have hM : IsPullback
      (pullback.fst (pullback.snd f pM) iM ≫ pullback.fst f pM)
      (pullback.snd (pullback.snd f pM) iM) f (iM ≫ pM) :=
    (IsPullback.of_hasPullback (pullback.snd f pM) iM).paste_horiz (IsPullback.of_hasPullback f pM)
  have hL' : IsPullback (pullback.fst f' iL ≫ g) (pullback.snd f' iL) f (iM ≫ pM) :=
    hcomm ▸ hL
  let e : pullback f' iL ≅ pullback (pullback.snd f pM) iM :=
    hL'.isoPullback ≪≫ hM.isoPullback.symm
  have : ConnectedSpace ↥(pullback f' iL) :=
    GeometricallyConnected.geometrically_connectedSpace iL _ _ (.of_hasPullback f' iL)
  have : ConnectedSpace ↥(pullback (pullback.snd f pM) iM) :=
    e.hom.homeomorph.connectedSpace_iff.mp this
  have : Surjective iM := ⟨Function.surjective_to_subsingleton _⟩
  exact (pullback.fst (pullback.snd f pM) iM).surjective.connectedSpace
    (pullback.fst (pullback.snd f pM) iM).continuous

/-- **Geometric connectedness over a field is invariant under arbitrary field extensions.** -/
theorem geometricallyConnected_iff_of_isPullback_field {k L : Type u} [Field k] [Field L]
    [Algebra k L] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of L)}
    {g : X' ⟶ X} (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    GeometricallyConnected f' ↔ GeometricallyConnected f :=
  ⟨fun _ ↦ geometricallyConnected_of_isPullback_field H,
    fun _ ↦ MorphismProperty.of_isPullback H inferInstance⟩

/-- **Geometric connectedness over a field can be tested over any separably closed extension**
(Stacks, Lemma 33.7.4 (Tag 04KT)). For a field extension `L / k` with `L` separably closed (for
instance `AlgebraicClosure k` or `SeparableClosure k`), `f : X ⟶ Spec k` is geometrically connected
if and only if its base change `X'` to `L` is connected. -/
theorem geometricallyConnected_iff_connectedSpace_of_isPullback_isSepClosed {k L : Type u}
    [Field k] [Field L] [Algebra k L] [IsSepClosed L] {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of L)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    GeometricallyConnected f ↔ ConnectedSpace X' :=
  (geometricallyConnected_iff_of_isPullback_field H).symm.trans
    (geometricallyConnected_iff_connectedSpace_of_isSepClosed f')

end TauCeti
