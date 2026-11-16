/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.AlgebraicGeometry.Scheme.ConnectedComponent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Integral
import TauCeti.Algebra.TensorProduct.CommonOverfield
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.RingTheory.Idempotents.Connected.ScalarExtension
import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Geometric connectedness and integrality from rational points

A connected scheme over a field `k` with a `k`-rational point is geometrically connected
(Stacks, Lemma 33.7.14 (Tag 04KV)). If in addition it is smooth over `k`, then it is geometrically
integral (Stacks, Lemma 33.25.10 (Tag 0CDW)). Consequently, on any locally connected `k`-scheme
`X` (in particular any locally Noetherian `k`-scheme, or any scheme locally of finite type over
`k`), the connected component of a `k`-rational point is an open and closed subscheme that is
geometrically connected over `k`, remains a single connected component after arbitrary extension of
the ground field, and is integral and geometrically integral whenever `X` is smooth over `k`.

The connectedness proof requires no affineness, quasi-compactness, or finite-type hypothesis on
`X`:

1. Given any morphism `f : X ⟶ S` with a section `s : S ⟶ X` (`s ≫ f = 𝟙 S`) and an arbitrary
   pullback square `h : IsPullback fst snd f g` along `g : S' ⟶ S` (compare
   `TauCeti.AlgebraicGeometry.baseChangeSection` for the chosen limit `pullback T.hom f` in
   `Over S`), the lifted section `s' : S' ⟶ Z` fits into a pullback square `IsPullback s' g fst s`.
   Because the forgetful functor from schemes to topological spaces does not preserve fibre
   products, `Set.range s' = fst ⁻¹' Set.range s` is deduced scheme-theoretically from
   `Scheme.Pullback.range_fst` applied to `IsPullback s' g fst s`.
2. When `X` is preconnected, `S'` is connected, and `fst` is both open and closed, any clopen
   subset of `Z` disjoint from `Set.range s'` pushes forward to a proper clopen subset of `X` and
   is therefore empty; thus `Z` is connected
   (`TauCeti.AlgebraicGeometry.connectedSpace_of_isPullback_of_section`).
3. Over a field `k`, the morphism `Spec (AlgebraicClosure k) ⟶ Spec k` is both universally open and
   integral (hence universally closed), so the base change of `X` to `AlgebraicClosure k` is
   connected. Geometric connectedness over `AlgebraicClosure k` and descent along field extensions
   (`TauCeti.geometricallyConnected_iff_connectedSpace_of_isPullback_isSepClosed`) then give
   `GeometricallyConnected f`.
4. Combining `GeometricallyConnected f` with
   `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral` yields `GeometricallyIntegral f` when
   `f` is smooth.

On affine coordinate rings, an augmentation `ε : A →ₐ[k] k` of a `k`-algebra with preconnected
prime spectrum makes `PrimeSpectrum (A ⊗[k] K)` connected—and forces every idempotent of `A ⊗[k] K`
to be `0` or `1`—for every field extension `K / k` in an arbitrary universe.

## Main declarations

* `TauCeti.AlgebraicGeometry.sectionPullbackLift`: canonical lift of a section along an arbitrary
  `IsPullback` square.
* `TauCeti.AlgebraicGeometry.connectedSpace_of_isPullback_of_section`: connectedness of a pullback
  in the presence of a section when the projection to `X` is both open and closed.
* `TauCeti.AlgebraicGeometry.geometricallyConnected_of_section`: a preconnected scheme over a field
  with a rational point is geometrically connected (Stacks, Tag 04KV).
* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_smooth_of_section`: a preconnected smooth
  scheme over a field with a rational point is geometrically integral (Stacks, Tag 0CDW).
* `AlgHom.connectedSpace_primeSpectrum_tensorProduct`: a `k`-algebra with preconnected spectrum and
  a `k`-algebra augmentation has connected spectrum after every field extension.
* `TauCeti.AlgebraicGeometry.geometricallyConnected_connectedComponentOpen_of_section`: on a
  locally connected `k`-scheme, the connected component of a `k`-rational point is geometrically
  connected.
* `TauCeti.AlgebraicGeometry.range_isPullback_connectedComponentOpen_eq_connectedComponent`: after
  base change to any field `K / k`, the pullback of that connected component is the connected
  component of the lifted `K`-point.
* `TauCeti.AlgebraicGeometry.geometricallyIntegral_connectedComponentOpen_of_smooth_of_section`: on
  a smooth `k`-scheme, the connected component of a `k`-rational point is geometrically integral.
* `TauCeti.AlgebraicGeometry.exists_clopen_geometricallyIntegral_of_smooth_of_section`: packaging
  of the clopen, smooth, integral, geometrically integral component of a rational point on any
  smooth `k`-scheme without requiring a separate `LocallyConnectedSpace` hypothesis.

## References

* The Stacks Project, Lemma 33.7.14 (Tag 04KV), connected schemes with a rational point are
  geometrically connected.
* The Stacks Project, Lemma 33.25.10 (Tag 0CDW), smooth schemes with a rational point and
  geometrically integral components.
* The Stacks Project, Section 10.48 (Tag 05DV), geometrically connected algebras.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace TauCeti.AlgebraicGeometry

/-! ### Base change of sections and connectedness along open-and-closed pullbacks -/

section PullbackSection

variable {X S S' Z : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X} {g : S' ⟶ S} {fst : Z ⟶ X} {snd : Z ⟶ S'}

/-- Lift a section `s` of `f : X ⟶ S` (`s ≫ f = 𝟙 S`) along an arbitrary pullback square
`IsPullback fst snd f g` to a section of `snd : Z ⟶ S'` (compare
`TauCeti.AlgebraicGeometry.baseChangeSection` for the canonical pullback `pullback T.hom f`). -/
noncomputable def sectionPullbackLift (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g) : S' ⟶ Z :=
  h.lift (g ≫ s) (𝟙 S') (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- Composing `sectionPullbackLift` with the first projection `fst : Z ⟶ X` gives `g ≫ s`. -/
@[reassoc (attr := simp)]
theorem sectionPullbackLift_fst (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g) :
    sectionPullbackLift hs h ≫ fst = g ≫ s :=
  h.lift_fst _ _ _

/-- `sectionPullbackLift` is a section of the base-changed morphism `snd : Z ⟶ S'`. -/
@[reassoc (attr := simp)]
theorem sectionPullbackLift_snd (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g) :
    sectionPullbackLift hs h ≫ snd = 𝟙 S' :=
  h.lift_snd _ _ _

/-- Universal characterization of `sectionPullbackLift` by its compositions with `fst` and `snd`. -/
theorem eq_sectionPullbackLift_iff (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g) {l : S' ⟶ Z} :
    l = sectionPullbackLift hs h ↔ l ≫ fst = g ≫ s ∧ l ≫ snd = 𝟙 S' :=
  ⟨fun hl ↦ hl ▸ ⟨sectionPullbackLift_fst hs h, sectionPullbackLift_snd hs h⟩,
    fun ⟨h₁, h₂⟩ ↦
      h.hom_ext (h₁.trans (sectionPullbackLift_fst hs h).symm)
        (h₂.trans (sectionPullbackLift_snd hs h).symm)⟩

/-- The lifted section fits into a pullback square against the original section `s : S ⟶ X`. -/
theorem isPullback_sectionPullbackLift (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g) :
    IsPullback (sectionPullbackLift hs h) g fst s := by
  have houter : IsPullback g (sectionPullbackLift hs h ≫ snd) (s ≫ f) g := by
    rw [sectionPullbackLift_snd hs h, hs]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact (IsPullback.of_bot houter (sectionPullbackLift_fst hs h).symm h).flip

/-- The topological image of the lifted section is the full preimage under `fst` of the image of
`s`. -/
theorem range_sectionPullbackLift (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g) :
    Set.range (sectionPullbackLift hs h) = fst ⁻¹' Set.range s := by
  have hpb := isPullback_sectionPullbackLift hs h
  rw [← hpb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hpb.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- If `f : X ⟶ S` has a section `s`, `X` is preconnected, `S'` is connected, and the projection
`fst : Z ⟶ X` of a pullback of `f` along `g : S' ⟶ S` is both open and closed, then `Z` is
connected. -/
theorem connectedSpace_of_isPullback_of_section [PreconnectedSpace X] [ConnectedSpace S']
    (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g)
    (hopen : IsOpenMap fst) (hclosed : IsClosedMap fst) :
    ConnectedSpace Z := by
  let s' := sectionPullbackLift hs h
  have hrange : Set.range s' = fst ⁻¹' Set.range s := range_sectionPullbackLift hs h
  obtain ⟨y₀⟩ := (inferInstance : Nonempty S')
  have : Nonempty Z := ⟨s' y₀⟩
  -- Any clopen `V ⊆ Z` disjoint from `Set.range s'` maps to a proper clopen subset of `X`.
  have hempty : ∀ {V : Set Z}, IsClopen V → Disjoint V (Set.range s') → V = ∅ := by
    intro V hV hdisj
    have hVimg : IsClopen (fst '' V) := ⟨hclosed V hV.isClosed, hopen V hV.isOpen⟩
    rcases isClopen_iff.mp hVimg with himg | himg
    · exact Set.image_eq_empty.mp himg
    · exfalso
      have hmem : s (g y₀) ∈ fst '' V := himg ▸ Set.mem_univ _
      obtain ⟨z, hzV, hzfst⟩ := hmem
      have hzs' : z ∈ Set.range s' := by
        rw [hrange]
        exact ⟨g y₀, hzfst.symm⟩
      exact Set.disjoint_left.mp hdisj hzV hzs'
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun W hW ↦ ?_⟩
  rcases isClopen_iff.mp (hW.preimage s'.continuous) with hW' | hW'
  · left
    refine hempty hW (Set.disjoint_left.mpr ?_)
    rintro _ hWz ⟨y, rfl⟩
    have hy : y ∈ s' ⁻¹' W := hWz
    rw [hW'] at hy
    exact hy
  · right
    have hWc : Wᶜ = ∅ := by
      refine hempty hW.compl (Set.disjoint_left.mpr ?_)
      rintro _ hWcz ⟨y, rfl⟩
      have hy : y ∈ s' ⁻¹' W := by rw [hW']; trivial
      exact hWcz hy
    rw [← compl_compl W, hWc, Set.compl_empty]

/-- If `f : X ⟶ S` has a section, `X` is preconnected, and `g : S' ⟶ S` has connected source and
is both universally open and universally closed, then the pullback of `f` along `g` is connected. -/
theorem connectedSpace_of_isPullback_of_universallyOpen_of_universallyClosed_of_section
    [PreconnectedSpace X] [ConnectedSpace S'] [UniversallyOpen g] [UniversallyClosed g]
    (hs : s ≫ f = 𝟙 S) (h : IsPullback fst snd f g) :
    ConnectedSpace Z := by
  have : UniversallyOpen fst := MorphismProperty.of_isPullback h.flip inferInstance
  have : UniversallyClosed fst := MorphismProperty.of_isPullback h.flip inferInstance
  exact connectedSpace_of_isPullback_of_section hs h fst.isOpenMap fst.isClosedMap

/-- Base-changing a preconnected `k`-scheme with a `k`-rational point along an integral field
extension `L / k` yields a connected scheme. -/
theorem connectedSpace_of_isPullback_of_isIntegral_of_section {k L : Type u} [Field k] [Field L]
    [Algebra k L] [Algebra.IsIntegral k L] {X Z : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [PreconnectedSpace X] {s : Spec (.of k) ⟶ X} (hs : s ≫ f = 𝟙 _)
    {fst : Z ⟶ X} {snd : Z ⟶ Spec (.of L)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    ConnectedSpace Z := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  exact connectedSpace_of_isPullback_of_universallyOpen_of_universallyClosed_of_section hs h

end PullbackSection

/-! ### Geometric connectedness and integrality of a scheme with a rational point -/

section RationalPoint

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {s : Spec (.of k) ⟶ X}

/-- **A preconnected scheme over a field with a rational point is geometrically connected**
(Stacks, Lemma 33.7.14 (Tag 04KV)). No affineness, quasi-compactness, or finite-type hypothesis is
required. -/
theorem geometricallyConnected_of_section [PreconnectedSpace X] (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  let L := AlgebraicClosure k
  let g : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : ConnectedSpace ↥(pullback f g) :=
    connectedSpace_of_isPullback_of_isIntegral_of_section hs (.of_hasPullback f g)
  exact (TauCeti.geometricallyConnected_iff_connectedSpace_of_isPullback_isSepClosed
    (.of_hasPullback f g)).mpr this

/-- A `k`-scheme with a `k`-rational point is geometrically connected if and only if its underlying
topological space is preconnected. -/
theorem geometricallyConnected_iff_preconnectedSpace_of_section (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f ↔ PreconnectedSpace X :=
  ⟨fun _ ↦ (GeometricallyConnected.connectedSpace_of_subsingleton f).toPreconnectedSpace,
    fun _ ↦ geometricallyConnected_of_section hs⟩

/-- A `k`-scheme with a `k`-rational point is geometrically connected if and only if its underlying
topological space is connected. -/
theorem geometricallyConnected_iff_connectedSpace_of_section (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f ↔ ConnectedSpace X :=
  ⟨fun _ ↦ GeometricallyConnected.connectedSpace_of_subsingleton f,
    fun _ ↦ geometricallyConnected_of_section hs⟩

/-- **A preconnected scheme smooth over a field with a rational point is geometrically integral**
(Stacks, Lemma 33.25.10 (Tag 0CDW)). -/
theorem geometricallyIntegral_of_smooth_of_section [Smooth f] [PreconnectedSpace X]
    (hs : s ≫ f = 𝟙 _) : GeometricallyIntegral f :=
  have := geometricallyConnected_of_section hs
  inferInstance

/-- A preconnected scheme smooth over a field with a rational point is integral. -/
theorem isIntegral_of_smooth_of_section [Smooth f] [PreconnectedSpace X] (hs : s ≫ f = 𝟙 _) :
    IsIntegral X :=
  have := geometricallyIntegral_of_smooth_of_section hs
  GeometricallyIntegral.isIntegral_of_subsingleton f

/-- A smooth `k`-scheme with a `k`-rational point is geometrically integral if and only if its
underlying topological space is preconnected. -/
theorem geometricallyIntegral_iff_preconnectedSpace_of_smooth_of_section [Smooth f]
    (hs : s ≫ f = 𝟙 _) : GeometricallyIntegral f ↔ PreconnectedSpace X :=
  ⟨fun _ ↦
    have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
    inferInstance,
    fun _ ↦ geometricallyIntegral_of_smooth_of_section hs⟩

/-- A smooth `k`-scheme with a `k`-rational point is geometrically integral if and only if its
underlying topological space is connected. -/
theorem geometricallyIntegral_iff_connectedSpace_of_smooth_of_section [Smooth f]
    (hs : s ≫ f = 𝟙 _) : GeometricallyIntegral f ↔ ConnectedSpace X :=
  ⟨fun _ ↦
    have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
    inferInstance,
    fun _ ↦ geometricallyIntegral_of_smooth_of_section hs⟩

/-- A smooth `k`-scheme with a `k`-rational point is geometrically integral if and only if it is
integral. Without a rational point this fails for nontrivial finite separable field extensions. -/
theorem geometricallyIntegral_iff_isIntegral_of_smooth_of_section [Smooth f]
    (hs : s ≫ f = 𝟙 _) : GeometricallyIntegral f ↔ IsIntegral X :=
  ⟨fun _ ↦ GeometricallyIntegral.isIntegral_of_subsingleton f,
    fun _ ↦ geometricallyIntegral_of_smooth_of_section hs⟩

end RationalPoint

end TauCeti.AlgebraicGeometry

/-! ### Coordinate-ring and idempotent formulations -/

namespace AlgHom

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- If a commutative `k`-algebra `A` has preconnected prime spectrum and admits a `k`-algebra
homomorphism `ε : A →ₐ[k] k`, then `Spec A ⟶ Spec k` is geometrically connected. -/
theorem geometricallyConnected_Spec {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [PreconnectedSpace (PrimeSpectrum A)] (ε : A →ₐ[k] k) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  let s : Spec (.of k) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom ε.toRingHom)
  have hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact ε.commutes x
  have : PreconnectedSpace ↥(Spec (.of A)) := ‹PreconnectedSpace (PrimeSpectrum A)›
  exact TauCeti.AlgebraicGeometry.geometricallyConnected_of_section hs

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **A commutative `k`-algebra with preconnected spectrum and an augmentation `A →ₐ[k] k` remains
connected after every field extension**, including extensions in an arbitrary universe. -/
theorem connectedSpace_primeSpectrum_tensorProduct {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [PreconnectedSpace (PrimeSpectrum A)] (ε : A →ₐ[k] k)
    (K : Type v) [Field K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum (A ⊗[k] K)) := by
  let Ω := AlgebraicClosure k
  have hspec := ε.geometricallyConnected_Spec
  have hpull : ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hAΩ : ConnectedSpace (PrimeSpectrum (A ⊗[k] Ω)) :=
    (pullbackSpecIso k A Ω).hom.homeomorph.connectedSpace_iff.mp hpull
  have hΩA : ConnectedSpace (PrimeSpectrum (Ω ⊗[k] A)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k A Ω).toRingEquiv).connectedSpace_iff.mp hAΩ
  let d := TauCeti.Algebra.TensorProduct.commonOverfield k Ω K
  have hext : ConnectedSpace (PrimeSpectrum ((Ω ⊗[k] A) ⊗[Ω] d.Ω)) :=
    TauCeti.connectedSpace_primeSpectrum_tensorProduct_of_isAlgClosed Ω (Ω ⊗[k] A) d.Ω
  have hAdΩ : ConnectedSpace (PrimeSpectrum (A ⊗[k] d.Ω)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv (d.comparison A)).connectedSpace_iff.mp hext
  exact (d.map A).toRingHom.connectedSpace_primeSpectrum_of_injective (d.map_injective A)

/-- In `A ⊗[k] K`, where `A` has preconnected spectrum and admits an augmentation `A →ₐ[k] k` and
`K / k` is any field extension, every idempotent is `0` or `1`. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [PreconnectedSpace (PrimeSpectrum A)] (ε : A →ₐ[k] k)
    {K : Type v} [Field K] [Algebra k K] {e : A ⊗[k] K} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 :=
  have := ε.connectedSpace_primeSpectrum_tensorProduct K
  he.eq_zero_or_eq_one_of_preconnectedSpace

end AlgHom

/-! ### The connected component of a rational point and its base change -/

namespace TauCeti.AlgebraicGeometry

section Component

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {s : Spec (.of k) ⟶ X}

/-- On a locally connected scheme over a field `k`, the connected component of a `k`-rational point
is geometrically connected over `k`. -/
theorem geometricallyConnected_connectedComponentOpen_of_section [LocallyConnectedSpace X]
    (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected ((X.connectedComponentOpen (s default)).ι ≫ f) :=
  geometricallyConnected_of_section (s.liftConnectedComponentOpen_comp_eq_id hs default)

section BaseChange

variable [LocallyConnectedSpace X] {K : Type u} [Field K] {y : Spec (.of K) ⟶ Spec (.of k)}
  {X_K U_K : Scheme.{u}} {fstX : X_K ⟶ X} {sndX : X_K ⟶ Spec (.of K)}
  {fstU : U_K ⟶ (X.connectedComponentOpen (s default)).toScheme}
  {jU : U_K ⟶ X_K}

/-- Base-changing the connected component of a `k`-rational point along any field-valued point
`y : Spec K ⟶ Spec k` yields a geometrically connected `K`-scheme. -/
theorem geometricallyConnected_of_isPullback_connectedComponentOpen_of_section
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    GeometricallyConnected (jU ≫ sndX) :=
  have := geometricallyConnected_connectedComponentOpen_of_section hs
  MorphismProperty.of_isPullback (hU.paste_vert hX) inferInstance

/-- Base-changing the connected component of a `k`-rational point along `y : Spec K ⟶ Spec k`
yields a connected scheme. -/
theorem connectedSpace_of_isPullback_connectedComponentOpen_of_section
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    ConnectedSpace U_K :=
  have := geometricallyConnected_of_isPullback_connectedComponentOpen_of_section hs hX hU
  GeometricallyConnected.connectedSpace_of_subsingleton (jU ≫ sndX)

/-- The `K`-rational point of the base-changed component `U_K` induced by the original `k`-section
`s`. -/
noncomputable def connectedComponentOpenPullbackSection
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    Spec (.of K) ⟶ U_K :=
  hU.lift (y ≫ s.liftConnectedComponentOpen default)
    (sectionPullbackLift hs hX)
    (by rw [Category.assoc, Scheme.Hom.liftConnectedComponentOpen_ι, sectionPullbackLift_fst])

/-- Projection of `connectedComponentOpenPullbackSection` to the component over `k`. -/
@[reassoc (attr := simp)]
theorem connectedComponentOpenPullbackSection_fstU
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    connectedComponentOpenPullbackSection hs hX hU ≫ fstU =
      y ≫ s.liftConnectedComponentOpen default :=
  hU.lift_fst _ _ _

/-- Composing `connectedComponentOpenPullbackSection` with `jU : U_K ⟶ X_K` recovers the lifted
section of `X_K`. -/
@[reassoc (attr := simp)]
theorem connectedComponentOpenPullbackSection_jU
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    connectedComponentOpenPullbackSection hs hX hU ≫ jU = sectionPullbackLift hs hX :=
  hU.lift_snd _ _ _

/-- `connectedComponentOpenPullbackSection` is a section of the structure morphism
`jU ≫ sndX : U_K ⟶ Spec K`. -/
@[reassoc]
theorem connectedComponentOpenPullbackSection_comp_sndX
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    connectedComponentOpenPullbackSection hs hX hU ≫ (jU ≫ sndX) = 𝟙 _ := by
  rw [← Category.assoc, connectedComponentOpenPullbackSection_jU, sectionPullbackLift_snd]

/-- **Base change commutes with taking the connected component of a rational point.** After
pulling back `X` to `X_K` along `y : Spec K ⟶ Spec k`, the pullback `jU : U_K ⟶ X_K` of the
connected component of `s` has topological image equal to the connected component of the lifted
`K`-rational point in `X_K`. -/
theorem range_isPullback_connectedComponentOpen_eq_connectedComponent
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    Set.range jU = connectedComponent (sectionPullbackLift hs hX default) := by
  have : IsOpenImmersion jU := MorphismProperty.of_isPullback hU inferInstance
  have : IsClosedImmersion jU := MorphismProperty.of_isPullback hU inferInstance
  have : ConnectedSpace U_K :=
    connectedSpace_of_isPullback_connectedComponentOpen_of_section hs hX hU
  let cK := connectedComponentOpenPullbackSection hs hX hU
  have hcK : jU (cK default) = sectionPullbackLift hs hX default := by
    rw [← Scheme.Hom.comp_apply, connectedComponentOpenPullbackSection_jU]
  rw [← hcK]
  exact jU.range_eq_connectedComponent _

/-- When `X_K` is also locally connected (for instance whenever `f` is locally of finite type), the
base-changed component `U_K` is canonically isomorphic over `X_K` to the component open of the
lifted `K`-rational point. -/
noncomputable def isoConnectedComponentOpenOfIsPullback [LocallyConnectedSpace X_K]
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    U_K ≅ (X_K.connectedComponentOpen (sectionPullbackLift hs hX default)).toScheme :=
  letI : IsOpenImmersion jU := MorphismProperty.of_isPullback hU inferInstance
  IsOpenImmersion.isoOfRangeEq jU
    (X_K.connectedComponentOpen (sectionPullbackLift hs hX default)).ι (by
      rw [range_isPullback_connectedComponentOpen_eq_connectedComponent hs hX hU,
        Scheme.Opens.range_ι, X_K.coe_connectedComponentOpen])

/-- The forward direction of `isoConnectedComponentOpenOfIsPullback` commutes with the inclusions
into `X_K`. -/
@[reassoc (attr := simp)]
theorem isoConnectedComponentOpenOfIsPullback_hom_ι [LocallyConnectedSpace X_K]
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    (isoConnectedComponentOpenOfIsPullback hs hX hU).hom ≫
      (X_K.connectedComponentOpen (sectionPullbackLift hs hX default)).ι = jU :=
  letI : IsOpenImmersion jU := MorphismProperty.of_isPullback hU inferInstance
  IsOpenImmersion.isoOfRangeEq_hom_fac jU _ (by
    rw [range_isPullback_connectedComponentOpen_eq_connectedComponent hs hX hU,
      Scheme.Opens.range_ι, X_K.coe_connectedComponentOpen])

/-- The inverse direction of `isoConnectedComponentOpenOfIsPullback` commutes with the inclusions
into `X_K`. -/
@[reassoc (attr := simp)]
theorem isoConnectedComponentOpenOfIsPullback_inv_fac [LocallyConnectedSpace X_K]
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    (isoConnectedComponentOpenOfIsPullback hs hX hU).inv ≫ jU =
      (X_K.connectedComponentOpen (sectionPullbackLift hs hX default)).ι :=
  letI : IsOpenImmersion jU := MorphismProperty.of_isPullback hU inferInstance
  IsOpenImmersion.isoOfRangeEq_inv_fac jU _ (by
    rw [range_isPullback_connectedComponentOpen_eq_connectedComponent hs hX hU,
      Scheme.Opens.range_ι, X_K.coe_connectedComponentOpen])

end BaseChange

/-! ### Smooth schemes: geometric integrality of the rational-point component -/

/-- **On a smooth scheme over a field, the connected component of a rational point is geometrically
integral** (Stacks, Lemma 33.25.10 (Tag 0CDW)). -/
theorem geometricallyIntegral_connectedComponentOpen_of_smooth_of_section
    [LocallyConnectedSpace X] [Smooth f] (hs : s ≫ f = 𝟙 _) :
    GeometricallyIntegral ((X.connectedComponentOpen (s default)).ι ≫ f) :=
  have := geometricallyConnected_connectedComponentOpen_of_section hs
  inferInstance

/-- On a smooth scheme over a field, the connected component of a rational point is integral. -/
theorem isIntegral_connectedComponentOpen_of_smooth_of_section
    [LocallyConnectedSpace X] [Smooth f] (hs : s ≫ f = 𝟙 _) :
    IsIntegral (X.connectedComponentOpen (s default)).toScheme :=
  have := geometricallyIntegral_connectedComponentOpen_of_smooth_of_section hs
  GeometricallyIntegral.isIntegral_of_subsingleton ((X.connectedComponentOpen (s default)).ι ≫ f)

/-- Base-changing the connected component of a `k`-rational point on a smooth `k`-scheme along any
field-valued point `y : Spec K ⟶ Spec k` yields a geometrically integral `K`-scheme. -/
theorem geometricallyIntegral_of_isPullback_connectedComponentOpen_of_smooth_of_section
    [LocallyConnectedSpace X] [Smooth f] {K : Type u} [Field K]
    {y : Spec (.of K) ⟶ Spec (.of k)} {X_K U_K : Scheme.{u}}
    {fstX : X_K ⟶ X} {sndX : X_K ⟶ Spec (.of K)}
    {fstU : U_K ⟶ (X.connectedComponentOpen (s default)).toScheme}
    {jU : U_K ⟶ X_K}
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    GeometricallyIntegral (jU ≫ sndX) :=
  have := geometricallyIntegral_connectedComponentOpen_of_smooth_of_section hs
  MorphismProperty.of_isPullback (hU.paste_vert hX) inferInstance

/-- Base-changing the connected component of a `k`-rational point on a smooth `k`-scheme along any
field-valued point `y : Spec K ⟶ Spec k` yields an integral scheme. -/
theorem isIntegral_of_isPullback_connectedComponentOpen_of_smooth_of_section
    [LocallyConnectedSpace X] [Smooth f] {K : Type u} [Field K]
    {y : Spec (.of K) ⟶ Spec (.of k)} {X_K U_K : Scheme.{u}}
    {fstX : X_K ⟶ X} {sndX : X_K ⟶ Spec (.of K)}
    {fstU : U_K ⟶ (X.connectedComponentOpen (s default)).toScheme}
    {jU : U_K ⟶ X_K}
    (hs : s ≫ f = 𝟙 _) (hX : IsPullback fstX sndX f y)
    (hU : IsPullback fstU jU (X.connectedComponentOpen (s default)).ι fstX) :
    IsIntegral U_K :=
  have := geometricallyIntegral_of_isPullback_connectedComponentOpen_of_smooth_of_section hs hX hU
  GeometricallyIntegral.isIntegral_of_subsingleton (jU ≫ sndX)

/-- On any smooth `k`-scheme `X` with a `k`-rational point `s`, the connected component of `s` is
an open and closed subscheme that is smooth, integral, and geometrically integral over `k`, and
through which `s` factors as a `k`-rational point. Local connectedness of `X` is deduced
internally from local Noetherianity of schemes locally of finite type over `k`. -/
theorem exists_clopen_geometricallyIntegral_of_smooth_of_section [Smooth f] (hs : s ≫ f = 𝟙 _) :
    ∃ U : X.Opens,
      (U : Set X) = connectedComponent (s default) ∧
      IsClosed (U : Set X) ∧
      Smooth (U.ι ≫ f) ∧
      GeometricallyIntegral (U.ι ≫ f) ∧
      IsIntegral U.toScheme ∧
      ∃ c : Spec (.of k) ⟶ U.toScheme, c ≫ U.ι = s ∧ c ≫ (U.ι ≫ f) = 𝟙 _ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨X.connectedComponentOpen (s default),
    X.coe_connectedComponentOpen _, X.isClosed_connectedComponentOpen _, inferInstance,
    geometricallyIntegral_connectedComponentOpen_of_smooth_of_section hs,
    isIntegral_connectedComponentOpen_of_smooth_of_section hs,
    s.liftConnectedComponentOpen default,
    s.liftConnectedComponentOpen_ι _, s.liftConnectedComponentOpen_comp_eq_id hs _⟩

/-! ### Non-vacuity and sharpness checks -/

-- Polynomial ring in one variable over `k` evaluated at `0` remains connected after every field
-- extension `K / k` via `AlgHom.connectedSpace_primeSpectrum_tensorProduct`.
example (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum (Polynomial k ⊗[k] K)) :=
  (Polynomial.aeval (0 : k)).connectedSpace_primeSpectrum_tensorProduct K

-- Disjoint union `Spec k ⨿ Spec L` for any smooth `k`-algebra `L` (e.g. a nontrivial finite
-- separable field extension `L / k`): the ambient smooth `k`-scheme is disconnected, yet the
-- component selected by the left `k`-rational point is clopen, smooth, integral, and geometrically
-- integral.
example (k L : Type u) [Field k] [CommRing L] [Algebra k L] [Algebra.Smooth k L] :
    let f : Spec (.of k) ⨿ Spec (.of L) ⟶ Spec (.of k) :=
      coprod.desc (𝟙 (Spec (.of k))) (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    let s : Spec (.of k) ⟶ Spec (.of k) ⨿ Spec (.of L) := coprod.inl
    have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
      exact RingHom.smooth_algebraMap.mpr ‹_›
    have : Smooth f := by
      let 𝒰 := coprodOpenCover.{u, 0} (Spec (.of k)) (Spec (.of L))
      have : ∀ i, IsAffine (𝒰.X i) := by
        rintro (_ | _) <;> dsimp [𝒰, coprodOpenCover, Sum.elim] <;> infer_instance
      rw [HasRingHomProperty.iff_of_source_openCover (P := @Smooth) 𝒰]
      rintro i
      have := this i
      rcases i with _ | _ <;>
        (rw [← HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
         dsimp [𝒰, coprodOpenCover, f]
         simp only [coprod.inl_desc, coprod.inr_desc]
         infer_instance)
    ∃ U : (Spec (.of k) ⨿ Spec (.of L)).Opens,
      (U : Set ↑(Spec (.of k) ⨿ Spec (.of L))) = connectedComponent (s default) ∧
      IsClosed (U : Set ↑(Spec (.of k) ⨿ Spec (.of L))) ∧
      Smooth (U.ι ≫ f) ∧
      GeometricallyIntegral (U.ι ≫ f) ∧
      IsIntegral U.toScheme ∧
      ∃ c : Spec (.of k) ⟶ U.toScheme, c ≫ U.ι = s ∧ c ≫ (U.ι ≫ f) = 𝟙 _ := by
  intro f s _ _
  exact exists_clopen_geometricallyIntegral_of_smooth_of_section (f := f) (s := s)
    (coprod.inl_desc _ _)

end Component

end TauCeti.AlgebraicGeometry
