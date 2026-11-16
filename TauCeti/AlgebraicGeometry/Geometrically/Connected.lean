/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.AlgebraicGeometry.Scheme.ConnectedComponent
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.Topology.Connected.Clopen
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Criteria for geometric connectedness of morphisms of schemes

This file develops scheme-level criteria for `AlgebraicGeometry.GeometricallyConnected` without
finiteness or affineness assumptions:

* Compatibility with isomorphisms, Zariski-local descent on the target, affine tensor products,
  and descent along surjective morphisms.
* Over a separably closed field `K` (and hence over any algebraically closed field), a morphism
  `X ⟶ Spec K` is geometrically connected if and only if `X` is connected (Stacks, Tags 0377 and
  04KT).
* For an arbitrary morphism of schemes `f : X ⟶ Y`, geometric connectedness can be tested solely
  against geometric points `Spec K ⟶ Y` with `K` algebraically closed; over a field `K`, it
  suffices to test connectedness after base change to `SeparableClosure K`, to
  `AlgebraicClosure K`, or to any single algebraically closed field over `K` (Stacks, Tag 0379).
* A preconnected scheme `X` over a field `K` admitting a morphism `s : Z ⟶ X` whose composite with
  `X ⟶ Spec K` is geometrically connected (for instance a `K`-rational point, or a point over a
  purely inseparable extension of `K`) is geometrically connected over `K` (Stacks, Tag 04KV).
* A clopen subscheme `C ↪ X` that is geometrically connected over `K` pulls back along any field
  extension `L / K` to a single connected component of the base change `X_L`.

## Main declarations

* `TauCeti.geometricallyConnected_respectsIso` and
  `TauCeti.isZariskiLocalAtTarget_geometricallyConnected`: invariance under isomorphisms and
  Zariski-locality on the target.
* `TauCeti.geometricallyConnected_of_isIso`: isomorphisms of schemes are geometrically connected.
* `TauCeti.geometricallyConnected_tensorProduct`: geometric connectedness of affine tensor
  products.
* `TauCeti.geometricallyConnected_of_comp_of_surjective`: descent of geometric connectedness along
  surjective morphisms.
* `TauCeti.geometricallyConnected_iff_connectedSpace_of_isSepClosed`: over a separably closed
  field, geometric connectedness is equivalent to connectedness.
* `TauCeti.geometricallyConnected_iff_of_isAlgClosed`,
  `TauCeti.geometricallyConnected_iff_of_isPullback_isAlgClosed`,
  `TauCeti.geometricallyConnected_iff_connectedSpace_separableClosure`, and
  `TauCeti.geometricallyConnected_iff_connectedSpace_algebraicClosure`: testing geometric
  connectedness on algebraically closed fields, on `SeparableClosure K`, and on
  `AlgebraicClosure K`.
* `TauCeti.geometricallyConnected_of_geometricallyConnected_comp`: a preconnected scheme over a
  field with a point over a geometrically connected `K`-scheme is geometrically connected.
* `TauCeti.range_eq_connectedComponent_of_isPullback` and
  `TauCeti.preimage_connectedComponentOpen_of_isPullback`: base change of a geometrically connected
  clopen component along an arbitrary field extension remains a single connected component.

## References

* [The Stacks Project, Tag 0377](https://stacks.math.columbia.edu/tag/0377)
* [The Stacks Project, Tag 0379](https://stacks.math.columbia.edu/tag/0379)
* [The Stacks Project, Tag 04KT](https://stacks.math.columbia.edu/tag/04KT)
* [The Stacks Project, Tag 04KV](https://stacks.math.columbia.edu/tag/04KV)
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

/-- Geometric connectedness of morphisms of schemes respects isomorphisms, being stable under
base change. -/
instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- `GeometricallyConnected` is Zariski-local on the target. -/
instance isZariskiLocalAtTarget_geometricallyConnected :
    IsZariskiLocalAtTarget @GeometricallyConnected :=
  GeometricallyConnected.eq_geometrically ▸ inferInstance

/-- An isomorphism of schemes is geometrically connected. -/
lemma geometricallyConnected_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyConnected f :=
  ⟨fun _ _ _ _ _ snd h ↦
    have := h.isIso_snd_of_isIso
    (asIso snd).schemeIsoToHomeo.connectedSpace_iff.mpr inferInstance⟩

/-- Geometric connectedness descends along surjections: if `f ≫ g` is geometrically connected and
`f` is surjective, then `g` is geometrically connected. -/
theorem geometricallyConnected_of_comp_of_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [GeometricallyConnected (f ≫ g)] :
    GeometricallyConnected g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have : ConnectedSpace ↥(pullback f (pullback.fst g x)) :=
    (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff.mpr
      (pullback_of_geometrically
        (GeometricallyConnected.geometrically_connectedSpace (f := f ≫ g)) K x)
  exact (pullback.snd f (pullback.fst g x)).surjective.connectedSpace
    (pullback.snd f (pullback.fst g x)).continuous

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

section SepClosed

/-- Over a separably closed field `K` (in particular over an algebraically closed field), every
connected scheme `X` over `Spec K` is geometrically connected. No finiteness assumption on `X` is
required. -/
theorem geometricallyConnected_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun M _ y ↦ ?_⟩
  -- Over a separably closed field, `Spec M ⟶ Spec K` is geometrically irreducible (hence
  -- geometrically connected) and universally open, so `X ×_{Spec K} Spec M` is connected.
  have : GeometricallyIrreducible y :=
    AlgebraicGeometry.geometricallyIrreducible_Spec_of_isSepClosed
  infer_instance

/-- Over a separably closed field `K`, a morphism `f : X ⟶ Spec K` is geometrically connected if
and only if `X` is connected. -/
theorem geometricallyConnected_iff_connectedSpace_of_isSepClosed {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    GeometricallyConnected f ↔ ConnectedSpace X :=
  ⟨fun _ ↦ GeometricallyConnected.connectedSpace_of_subsingleton f,
    fun _ ↦ geometricallyConnected_of_isSepClosed f⟩

end SepClosed

section AlgClosed

/-- Geometric connectedness of an arbitrary morphism of schemes `f : X ⟶ Y` can be tested on
geometric points `Spec K ⟶ Y` with `K` algebraically closed. -/
theorem geometricallyConnected_iff_of_isAlgClosed {X Y : Scheme.{u}} (f : X ⟶ Y) :
    GeometricallyConnected f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ Y),
        ConnectedSpace ↥(pullback f y) := by
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  refine ⟨fun h K _ _ y ↦ h K y, fun h K _ y ↦ ?_⟩
  let Ω := AlgebraicClosure K
  let g : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Surjective g := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hpb : IsPullback (pullback.fst (pullback.snd f y) g ≫ pullback.fst f y)
      (pullback.snd (pullback.snd f y) g) f (g ≫ y) :=
    (IsPullback.of_hasPullback (pullback.snd f y) g).paste_horiz (.of_hasPullback f y)
  have hΩ : ConnectedSpace ↥(pullback (pullback.snd f y) g) :=
    hpb.isoPullback.inv.homeomorph.connectedSpace_iff.mp (h Ω (g ≫ y))
  exact (pullback.fst (pullback.snd f y) g).surjective.connectedSpace
    (pullback.fst (pullback.snd f y) g).continuous

/-- For a scheme `X` over a field `K` and any separably closed algebraic extension `Ω / K` (such as
`SeparableClosure K` or `AlgebraicClosure K`), a pullback `Z` of `X` along `Spec Ω ⟶ Spec K` is
connected if and only if `X ⟶ Spec K` is geometrically connected (Stacks, Tag 0379). -/
theorem geometricallyConnected_iff_of_isPullback_isSepClosed {K Ω : Type u} [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosed Ω] [Algebra.IsAlgebraic K Ω] {X Z : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {fst : Z ⟶ X} {snd : Z ⟶ Spec (.of Ω)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) :
    GeometricallyConnected f ↔ ConnectedSpace Z := by
  refine ⟨fun hf ↦ hf.geometrically_connectedSpace _ _ _ h, fun hZ ↦ ?_⟩
  have hsnd : GeometricallyConnected snd := geometricallyConnected_of_isSepClosed snd
  rw [geometricallyConnected_iff_of_isAlgClosed]
  intro L _ _ y
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  -- Embed the algebraic extension `Ω / K` into the algebraically closed extension `L / K`.
  let ψ : Ω →ₐ[K] L := IsAlgClosed.lift
  let q : Spec (.of L) ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hfac : Spec.map φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact (ψ.commutes c).symm
  have hpb : IsPullback (pullback.fst snd q ≫ fst) (pullback.snd snd q) f (Spec.map φ) := by
    rw [hfac]
    exact (IsPullback.of_hasPullback snd q).paste_horiz h
  have : ConnectedSpace ↥(pullback snd q) :=
    pullback_of_geometrically hsnd.geometrically_connectedSpace L q
  exact hpb.isoPullback.hom.homeomorph.connectedSpace_iff.mp this

/-- Over a field `K`, a morphism `f : X ⟶ Spec K` is geometrically connected if and only if the
base change of `X` to `SeparableClosure K` is connected (Stacks, Tag 0379). -/
theorem geometricallyConnected_iff_connectedSpace_separableClosure {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    GeometricallyConnected f ↔
      ConnectedSpace
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))))) :=
  geometricallyConnected_iff_of_isPullback_isSepClosed (.of_hasPullback _ _)

/-- Over a field `K`, a morphism `f : X ⟶ Spec K` is geometrically connected if and only if the
base change of `X` to `AlgebraicClosure K` is connected (Stacks, Tag 0379). -/
theorem geometricallyConnected_iff_connectedSpace_algebraicClosure {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    GeometricallyConnected f ↔
      ConnectedSpace
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) :=
  geometricallyConnected_iff_of_isPullback_isSepClosed (.of_hasPullback _ _)

/-- For a scheme `X` over a field `K` and *any* algebraically closed field `Ω` with a morphism
`p : Spec Ω ⟶ Spec K` (not necessarily algebraic), a pullback `Z` of `X` along `p` is connected if
and only if `X ⟶ Spec K` is geometrically connected (Stacks, Tag 0379). -/
theorem geometricallyConnected_iff_of_isPullback_isAlgClosed {K Ω : Type u} [Field K] [Field Ω]
    [IsAlgClosed Ω] {X Z : Scheme.{u}} {f : X ⟶ Spec (.of K)} {p : Spec (.of Ω) ⟶ Spec (.of K)}
    {fst : Z ⟶ X} {snd : Z ⟶ Spec (.of Ω)} (h : IsPullback fst snd f p) :
    GeometricallyConnected f ↔ ConnectedSpace Z := by
  refine ⟨fun hf ↦ hf.geometrically_connectedSpace _ _ _ h, fun hZ ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  algebraize [φ.hom]
  let Kbar := AlgebraicClosure K
  let g : Spec (.of Kbar) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Kbar))
  let ψ : Kbar →ₐ[K] Ω := IsAlgClosed.lift
  let q : Spec (.of Ω) ⟶ Spec (.of Kbar) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have : Surjective q := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hfac : Spec.map φ = q ≫ g := by
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact (ψ.commutes c).symm
  have hpb : IsPullback (pullback.fst (pullback.snd f g) q ≫ pullback.fst f g)
      (pullback.snd (pullback.snd f g) q) f (Spec.map φ) := by
    rw [hfac]
    exact (IsPullback.of_hasPullback (pullback.snd f g) q).paste_horiz (.of_hasPullback f g)
  have : ConnectedSpace ↥(pullback (pullback.snd f g) q) :=
    (h.isoIsPullback _ _ hpb).hom.homeomorph.connectedSpace_iff.mp hZ
  have : ConnectedSpace ↥(pullback f g) :=
    (pullback.fst (pullback.snd f g) q).surjective.connectedSpace
      (pullback.fst (pullback.snd f g) q).continuous
  exact (geometricallyConnected_iff_connectedSpace_algebraicClosure f).mpr this

/-- **Geometric connectedness from a geometrically connected point.** Let `X` be a preconnected
scheme over a field `K`. If there is a morphism `s : Z ⟶ X` such that `s ≫ f : Z ⟶ Spec K` is
geometrically connected (for example a `K`-rational point `Spec K ⟶ X`, or a point valued in a
purely inseparable extension of `K`), then `f : X ⟶ Spec K` is geometrically connected. -/
theorem geometricallyConnected_of_geometricallyConnected_comp {K : Type u} [Field K]
    {Z X : Scheme.{u}} [PreconnectedSpace X] (s : Z ⟶ X) (f : X ⟶ Spec (.of K))
    [GeometricallyConnected (s ≫ f)] :
    GeometricallyConnected f := by
  rw [geometricallyConnected_iff_connectedSpace_algebraicClosure]
  let Ω := AlgebraicClosure K
  let g : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let π : pullback f g ⟶ X := pullback.fst f g
  -- `Z ×_{Spec K} Spec Ω ≅ Z ×_X (X ×_{Spec K} Spec Ω)` is connected by hypothesis.
  have hZΩ : ConnectedSpace ↥(pullback s π) :=
    GeometricallyConnected.geometrically_connectedSpace g _ _
      ((IsPullback.of_hasPullback s π).paste_vert (.of_hasPullback f g))
  have : Nonempty ↥(pullback f g) := Nonempty.map (pullback.snd s π) inferInstance
  have ⟨z₀⟩ : Nonempty Z := Nonempty.map (pullback.fst s π) inferInstance
  -- `g : Spec Ω ⟶ Spec K` is integral (hence universally closed) and universally open, so `π`
  -- sends clopen sets to clopen sets.
  have : IsIntegralHom g :=
    IsIntegralHom.SpecMap_iff.mpr fun x ↦ Algebra.IsIntegral.isIntegral x
  have hempty : ∀ {V : Set ↥(pullback f g)},
      IsClopen V → pullback.snd s π ⁻¹' V = ∅ → V = ∅ := by
    intro V hV hpre
    by_contra hVne
    have hclopen : IsClopen (π '' V) :=
      ⟨π.isClosedMap V hV.isClosed, π.isOpenMap V hV.isOpen⟩
    have huniv : π '' V = Set.univ :=
      (isClopen_iff.mp hclopen).resolve_left ((Set.nonempty_iff_ne_empty.mpr hVne).image π).ne_empty
    obtain ⟨v, hvV, hπv⟩ : s z₀ ∈ π '' V := huniv ▸ Set.mem_univ _
    have hmem : v ∈ Set.range (pullback.snd s π) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨z₀, hπv.symm⟩
    obtain ⟨w, rfl⟩ := hmem
    exact Set.eq_empty_iff_forall_notMem.mp hpre w hvV
  have : PreconnectedSpace ↥(pullback f g) :=
    preconnectedSpace_iff_clopen.mpr fun U hU ↦ by
      rcases isClopen_iff.mp (hU.preimage (pullback.snd s π).continuous) with h | h
      · exact Or.inl (hempty hU h)
      · refine Or.inr (Set.compl_empty_iff.mp (hempty hU.compl ?_))
        rw [Set.preimage_compl, h, Set.compl_univ]
  exact ⟨inferInstance⟩

end AlgClosed

section BaseChangeComponent

variable {K L : Type u} [Field K] [Field L]

/-- If `j : C ⟶ X` is both an open and a closed immersion whose composite with `f : X ⟶ Spec K` is
geometrically connected, then after base change along any field morphism `q : Spec L ⟶ Spec K` the
induced morphism `j' : C' ⟶ X'` has topological image equal to the connected component of `j' c'`
for every `c' : C'`. No local connectedness assumption on `X` or `X'` is required. -/
theorem range_eq_connectedComponent_of_isPullback {C X C' X' : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {q : Spec (.of L) ⟶ Spec (.of K)} {j : C ⟶ X}
    [IsOpenImmersion j] [IsClosedImmersion j] [GeometricallyConnected (j ≫ f)]
    {fstX : X' ⟶ X} {sndX : X' ⟶ Spec (.of L)} {fstC : C' ⟶ C} {j' : C' ⟶ X'}
    (hX : IsPullback fstX sndX f q) (hC : IsPullback fstC j' j fstX) (c' : C') :
    Set.range j' = connectedComponent (j' c') := by
  have : ConnectedSpace C' :=
    GeometricallyConnected.geometrically_connectedSpace q fstC (j' ≫ sndX) (hC.paste_vert hX)
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback hC inferInstance
  have : IsClosedImmersion j' := MorphismProperty.of_isPullback hC inferInstance
  exact j'.range_eq_connectedComponent c'

/-- Let `X` be a locally connected scheme over a field `K` and `x : X` a point whose component open
is geometrically connected over `K`. For any base change `X'` of `X` along `q : Spec L ⟶ Spec K`
and any point `x' : X'` mapping into `connectedComponent x`, the preimage of `connectedComponent x`
in `X'` is the connected component of `x'`. No local connectedness assumption on `X'` is needed. -/
theorem preimage_connectedComponent_of_isPullback {X X' : Scheme.{u}} [LocallyConnectedSpace X]
    {f : X ⟶ Spec (.of K)} {q : Spec (.of L) ⟶ Spec (.of K)}
    {fstX : X' ⟶ X} {sndX : X' ⟶ Spec (.of L)} (hX : IsPullback fstX sndX f q)
    {x : X} [GeometricallyConnected ((X.connectedComponentOpen x).ι ≫ f)]
    {x' : X'} (hx' : fstX x' ∈ connectedComponent x) :
    fstX ⁻¹' connectedComponent x = connectedComponent x' := by
  let U : X.Opens := X.connectedComponentOpen x
  let c' : (fstX ⁻¹ᵁ U).toScheme := ⟨x', by simpa [U] using hx'⟩
  have hrange := range_eq_connectedComponent_of_isPullback hX
    (isPullback_morphismRestrict fstX U) c'
  simpa [U, c'] using hrange

/-- Open-subscheme form of `preimage_connectedComponent_of_isPullback`: when `X'` is also locally
connected, pulling back a geometrically connected component open of `X` along `fstX : X' ⟶ X`
yields the component open of any point `x' : X'` above it. -/
theorem preimage_connectedComponentOpen_of_isPullback {X X' : Scheme.{u}}
    [LocallyConnectedSpace X] [LocallyConnectedSpace X']
    {f : X ⟶ Spec (.of K)} {q : Spec (.of L) ⟶ Spec (.of K)}
    {fstX : X' ⟶ X} {sndX : X' ⟶ Spec (.of L)} (hX : IsPullback fstX sndX f q)
    {x : X} [GeometricallyConnected ((X.connectedComponentOpen x).ι ≫ f)]
    {x' : X'} (hx' : fstX x' ∈ connectedComponent x) :
    fstX ⁻¹ᵁ X.connectedComponentOpen x = X'.connectedComponentOpen x' :=
  SetLike.coe_injective (by simpa using preimage_connectedComponent_of_isPullback hX hx')

end BaseChangeComponent

end TauCeti
