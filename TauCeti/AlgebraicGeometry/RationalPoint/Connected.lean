/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Geometric connectedness and integrality of rational-point components

Let `X` be a scheme over a field `K` with structure morphism `f : X ⟶ Spec K`, and let
`s : Spec K ⟶ X` be a `K`-rational point, i.e. a section `s ≫ f = 𝟙 (Spec K)`.

* **Preconnected schemes.** If `X` is preconnected, then `f` is geometrically connected over `K`
  (Stacks, Tag 04KV); the same holds more generally when `X` admits a point valued in a purely
  inseparable extension of `K`. If `f` is in addition smooth, then `f` is geometrically integral
  (Stacks, Tag 0CDW) and `X` is an integral scheme.
* **Connected component of a rational point.** On an arbitrary locally connected scheme `X`, any
  section `s : S ⟶ X` over a preconnected base `S` lifts via `Scheme.connectedComponentOpenLift` to
  a section on the component open `X.connectedComponentOpen (s y)`. Over `S = Spec K`, the
  component open of a `K`-rational point is therefore clopen and geometrically connected over `K`,
  and geometrically integral (hence integral) when `f` is smooth. When `f` is locally of finite
  type, `X` is locally Noetherian and hence automatically locally connected, giving self-contained
  existence statements for the marked clopen component without any topological hypothesis on `X`.
* **Persistence under field extensions.** For any field morphism `q : Spec L ⟶ Spec K` and any
  base change `X'` of `X` along `q`, pulling back the connected component of a `K`-rational point
  `s` yields a single connected component of `X'` — namely the connected component of any
  compatible `L`-point `s' : Spec L ⟶ X'` (`s' ≫ fstX = q ≫ s`) — both as underlying sets and,
  when `X'` is locally connected, as `Opens`.

## Main results

* `TauCeti.AlgebraicGeometry.geometricallyConnected_of_section` and
  `TauCeti.AlgebraicGeometry.geometricallyConnected_of_isPurelyInseparable_comp`: a preconnected
  `K`-scheme with a rational or purely inseparable point is geometrically connected.
* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_smooth_of_section` and
  `TauCeti.AlgebraicGeometry.isIntegral_of_smooth_of_section`: a smooth preconnected `K`-scheme
  with a `K`-rational point is geometrically integral, hence integral.
* `TauCeti.AlgebraicGeometry.geometricallyConnected_connectedComponentOpen_of_section` and
  `TauCeti.AlgebraicGeometry.geometricallyIntegral_connectedComponentOpen_of_smooth_of_section`:
  geometric connectedness and geometric integrality of the component open of a rational point.
* `TauCeti.AlgebraicGeometry.exists_clopen_geometricallyConnected_of_locallyOfFiniteType_of_section`
  and `TauCeti.AlgebraicGeometry.exists_clopen_geometricallyIntegral_of_smooth_of_section`:
  existence of the marked clopen geometrically connected / geometrically integral component when `f`
  is locally of finite type / smooth.
* `TauCeti.AlgebraicGeometry.preimage_connectedComponent_of_section_comp` and
  `TauCeti.AlgebraicGeometry.preimage_connectedComponentOpen_of_section_comp`: the connected
  component of a rational point pulls back along any field extension to the connected component of
  the base-changed rational point.

## References

* [The Stacks Project, Tag 04KV](https://stacks.math.columbia.edu/tag/04KV)
* [The Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-! ### Lifting sections to component opens -/

section LiftSection

variable {X S : Scheme.{u}} [LocallyConnectedSpace X] [PreconnectedSpace S]
  {f : X ⟶ S} {s : S ⟶ X}

/-- A section `s : S ⟶ X` of `f : X ⟶ S` over a preconnected base `S` lifts via
`Scheme.connectedComponentOpenLift` to a section of the restricted morphism
`(X.connectedComponentOpen x).ι ≫ f` on the component open hit by `s`. -/
@[reassoc]
theorem connectedComponentOpenLift_comp_of_section (hs : s ≫ f = 𝟙 S) {x : X} {y : S}
    (hy : s y ∈ connectedComponent x) :
    X.connectedComponentOpenLift s hy ≫ (X.connectedComponentOpen x).ι ≫ f = 𝟙 S := by
  rw [X.connectedComponentOpenLift_ι_assoc, hs]

end LiftSection

/-! ### Preconnected schemes with a rational or purely inseparable point -/

section Preconnected

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A smooth, preconnected scheme `X` over a field `K` admitting a morphism `t : Z ⟶ X` whose
composite with `f : X ⟶ Spec K` is geometrically connected is geometrically integral over `K`. -/
theorem geometricallyIntegral_of_smooth_of_geometricallyConnected_comp {Z : Scheme.{u}}
    [PreconnectedSpace X] (t : Z ⟶ X) (f : X ⟶ Spec (.of K)) [Smooth f]
    [GeometricallyConnected (t ≫ f)] : GeometricallyIntegral f := by
  have := geometricallyConnected_of_geometricallyConnected_comp t f
  infer_instance

variable {f : X ⟶ Spec (.of K)} {s : Spec (.of K) ⟶ X}

/-- A preconnected scheme over a field `K` admitting a `K`-rational point is geometrically
connected over `K` (Stacks, Tag 04KV). No finiteness assumption on `X` is required. -/
theorem geometricallyConnected_of_section [PreconnectedSpace X]
    (hs : s ≫ f = 𝟙 (Spec (.of K))) : GeometricallyConnected f := by
  have : GeometricallyConnected (s ≫ f) := by
    rw [hs]
    exact geometricallyConnected_of_isIso _
  exact geometricallyConnected_of_geometricallyConnected_comp s f

/-- More generally, a preconnected scheme over a field `K` admitting a point over a purely
inseparable field extension `L / K` is geometrically connected over `K` (Stacks, Tag 04KV). -/
theorem geometricallyConnected_of_isPurelyInseparable_comp {L : Type u} [Field L]
    [Algebra K L] [IsPurelyInseparable K L] [PreconnectedSpace X] {t : Spec (.of L) ⟶ X}
    (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    GeometricallyConnected f := by
  have : GeometricallyConnected (t ≫ f) := by
    rw [ht]
    infer_instance
  exact geometricallyConnected_of_geometricallyConnected_comp t f

/-- **A smooth connected scheme over a field with a rational point is geometrically integral**
(Stacks, Tag 0CDW). Because the rational point witnesses nonemptiness, `PreconnectedSpace X`
suffices. -/
theorem geometricallyIntegral_of_smooth_of_section [PreconnectedSpace X] [Smooth f]
    (hs : s ≫ f = 𝟙 (Spec (.of K))) : GeometricallyIntegral f := by
  have := geometricallyConnected_of_section hs
  infer_instance

/-- A smooth, preconnected scheme over a field `K` admitting a point valued in a purely inseparable
extension `L / K` is geometrically integral over `K`. -/
theorem geometricallyIntegral_of_smooth_of_isPurelyInseparable_comp {L : Type u} [Field L]
    [Algebra K L] [IsPurelyInseparable K L] [PreconnectedSpace X] [Smooth f]
    {t : Spec (.of L) ⟶ X} (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    GeometricallyIntegral f := by
  have := geometricallyConnected_of_isPurelyInseparable_comp ht
  infer_instance

/-- A smooth, preconnected scheme over a field `K` admitting a `K`-rational point is integral. -/
theorem isIntegral_of_smooth_of_section [PreconnectedSpace X] [Smooth f]
    (hs : s ≫ f = 𝟙 (Spec (.of K))) : IsIntegral X := by
  have := geometricallyIntegral_of_smooth_of_section hs
  exact GeometricallyIntegral.isIntegral_of_subsingleton f

end Preconnected

/-! ### The connected component of a rational point -/

section Component

variable {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)} {s : Spec (.of K) ⟶ X}

/-- On a locally connected `K`-scheme `X`, any component open containing the image of a
`K`-rational point is geometrically connected over `K`. -/
theorem geometricallyConnected_connectedComponentOpen_of_mem_of_section [LocallyConnectedSpace X]
    (hs : s ≫ f = 𝟙 (Spec (.of K))) {x : X} {y : Spec (.of K)}
    (hy : s y ∈ connectedComponent x) :
    GeometricallyConnected ((X.connectedComponentOpen x).ι ≫ f) :=
  geometricallyConnected_of_section (connectedComponentOpenLift_comp_of_section hs hy)

/-- On a locally connected `K`-scheme `X`, the component open of a `K`-rational point is
geometrically connected over `K`. -/
theorem geometricallyConnected_connectedComponentOpen_of_section [LocallyConnectedSpace X]
    (hs : s ≫ f = 𝟙 (Spec (.of K))) (y : Spec (.of K)) :
    GeometricallyConnected ((X.connectedComponentOpen (s y)).ι ≫ f) :=
  geometricallyConnected_connectedComponentOpen_of_mem_of_section hs mem_connectedComponent

/-- On a locally connected smooth `K`-scheme `X`, the component open of a `K`-rational point is
geometrically integral over `K` (Stacks, Tag 0CDW). -/
theorem geometricallyIntegral_connectedComponentOpen_of_smooth_of_section
    [LocallyConnectedSpace X] [Smooth f] (hs : s ≫ f = 𝟙 (Spec (.of K))) (y : Spec (.of K)) :
    GeometricallyIntegral ((X.connectedComponentOpen (s y)).ι ≫ f) := by
  have := geometricallyConnected_connectedComponentOpen_of_section hs y
  infer_instance

/-- On a locally connected smooth `K`-scheme `X`, the component open of a `K`-rational point is an
integral scheme. -/
theorem isIntegral_connectedComponentOpen_of_smooth_of_section
    [LocallyConnectedSpace X] [Smooth f] (hs : s ≫ f = 𝟙 (Spec (.of K))) (y : Spec (.of K)) :
    IsIntegral (X.connectedComponentOpen (s y)).toScheme := by
  have := geometricallyIntegral_connectedComponentOpen_of_smooth_of_section hs y
  exact GeometricallyIntegral.isIntegral_of_subsingleton ((X.connectedComponentOpen (s y)).ι ≫ f)

/-- For a scheme `X` locally of finite type over a field `K` with a `K`-rational point `s`, the
connected component of `s` carries an open-subscheme structure `U : X.Opens` that is also closed in
`X`, admits a lifted `K`-rational point `s'`, and is geometrically connected over `K`. Local
connectedness of `X` is supplied automatically by Noetherianity. -/
theorem exists_clopen_geometricallyConnected_of_locallyOfFiniteType_of_section
    [LocallyOfFiniteType f] (hs : s ≫ f = 𝟙 (Spec (.of K))) :
    ∃ (U : X.Opens) (s' : Spec (.of K) ⟶ U.toScheme),
      (U : Set X) = connectedComponent (s (IsLocalRing.closedPoint K)) ∧
        IsClosedImmersion U.ι ∧ s' ≫ U.ι = s ∧ s' ≫ U.ι ≫ f = 𝟙 (Spec (.of K)) ∧
        GeometricallyConnected (U.ι ≫ f) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  let y₀ : Spec (.of K) := IsLocalRing.closedPoint K
  refine ⟨X.connectedComponentOpen (s y₀),
    X.connectedComponentOpenLift s (x := s y₀) (y := y₀) mem_connectedComponent,
    X.coe_connectedComponentOpen (s y₀), inferInstance, X.connectedComponentOpenLift_ι s _,
    connectedComponentOpenLift_comp_of_section hs mem_connectedComponent,
    geometricallyConnected_connectedComponentOpen_of_section hs y₀⟩

/-- **Connected component of a rational point on a smooth scheme** (Stacks, Tag 0CDW). If `X` is
smooth over a field `K` and `s : Spec K ⟶ X` is a `K`-rational point, then the connected component
of `s` is a clopen subscheme `U : X.Opens` admitting a lifted `K`-rational point `s'` such that
`U` is smooth and geometrically integral over `K` (and in particular an integral scheme). -/
theorem exists_clopen_geometricallyIntegral_of_smooth_of_section
    [Smooth f] (hs : s ≫ f = 𝟙 (Spec (.of K))) :
    ∃ (U : X.Opens) (s' : Spec (.of K) ⟶ U.toScheme),
      (U : Set X) = connectedComponent (s (IsLocalRing.closedPoint K)) ∧
        IsClosedImmersion U.ι ∧ s' ≫ U.ι = s ∧ s' ≫ U.ι ≫ f = 𝟙 (Spec (.of K)) ∧
        Smooth (U.ι ≫ f) ∧ GeometricallyIntegral (U.ι ≫ f) ∧ IsIntegral U.toScheme := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  let y₀ : Spec (.of K) := IsLocalRing.closedPoint K
  refine ⟨X.connectedComponentOpen (s y₀),
    X.connectedComponentOpenLift s (x := s y₀) (y := y₀) mem_connectedComponent,
    X.coe_connectedComponentOpen (s y₀), inferInstance, X.connectedComponentOpenLift_ι s _,
    connectedComponentOpenLift_comp_of_section hs mem_connectedComponent, inferInstance,
    geometricallyIntegral_connectedComponentOpen_of_smooth_of_section hs y₀,
    isIntegral_connectedComponentOpen_of_smooth_of_section hs y₀⟩

end Component

/-! ### Persistence of the rational-point component under field extensions -/

section BaseChange

variable {K L : Type u} [Field K] [Field L] {X X' : Scheme.{u}}
  {f : X ⟶ Spec (.of K)} {s : Spec (.of K) ⟶ X} {q : Spec (.of L) ⟶ Spec (.of K)}
  {fstX : X' ⟶ X} {sndX : X' ⟶ Spec (.of L)}

/-- Let `X` be a locally connected `K`-scheme with a `K`-rational point `s`, and let `X'` be a
base change of `X` along a field morphism `q : Spec L ⟶ Spec K`. For any point `x' : X'` mapping
into the connected component of `s`, the preimage in `X'` of that connected component is the
connected component of `x'`. No local connectedness assumption on `X'` is required. -/
theorem preimage_connectedComponent_of_section [LocallyConnectedSpace X]
    (hX : IsPullback fstX sndX f q) (hs : s ≫ f = 𝟙 (Spec (.of K))) (y : Spec (.of K))
    {x' : X'} (hx' : fstX x' ∈ connectedComponent (s y)) :
    fstX ⁻¹' connectedComponent (s y) = connectedComponent x' := by
  have := geometricallyConnected_connectedComponentOpen_of_section hs y
  exact preimage_connectedComponent_of_isPullback hX hx'

/-- Under base change along `q : Spec L ⟶ Spec K`, the preimage of the connected component of a
`K`-rational point `s : Spec K ⟶ X` is the connected component of any compatible `L`-point
`s' : Spec L ⟶ X'` (`s' ≫ fstX = q ≫ s`), with no local connectedness assumption on `X'`. -/
theorem preimage_connectedComponent_of_section_comp [LocallyConnectedSpace X]
    (hX : IsPullback fstX sndX f q) (hs : s ≫ f = 𝟙 (Spec (.of K)))
    {s' : Spec (.of L) ⟶ X'} (hs' : s' ≫ fstX = q ≫ s)
    (y : Spec (.of K)) (y' : Spec (.of L)) :
    fstX ⁻¹' connectedComponent (s y) = connectedComponent (s' y') := by
  refine preimage_connectedComponent_of_section hX hs y ?_
  have hpt : fstX (s' y') = s y := by
    calc
      fstX (s' y') = (s' ≫ fstX) y' := (Scheme.Hom.comp_apply s' fstX y').symm
      _ = s (q y') := by rw [hs', Scheme.Hom.comp_apply]
      _ = s y := congrArg s (Subsingleton.elim (q y') y)
  rw [hpt]
  exact mem_connectedComponent

/-- Open-subscheme form of `preimage_connectedComponent_of_section_comp`: when both `X` and `X'`
are locally connected, pulling back the component open of `s` along `fstX : X' ⟶ X` yields the
component open of any compatible `L`-point `s' : Spec L ⟶ X'`. -/
theorem preimage_connectedComponentOpen_of_section_comp
    [LocallyConnectedSpace X] [LocallyConnectedSpace X']
    (hX : IsPullback fstX sndX f q) (hs : s ≫ f = 𝟙 (Spec (.of K)))
    {s' : Spec (.of L) ⟶ X'} (hs' : s' ≫ fstX = q ≫ s)
    (y : Spec (.of K)) (y' : Spec (.of L)) :
    fstX ⁻¹ᵁ X.connectedComponentOpen (s y) = X'.connectedComponentOpen (s' y') :=
  SetLike.coe_injective
    (by simpa using preimage_connectedComponent_of_section_comp hX hs hs' y y')

/-- When `f : X ⟶ Spec K` is locally of finite type, no topological connectedness assumption on `X`
or `X'` is needed: the preimage in `X'` of the connected component of a `K`-rational point `s` is
the connected component of any compatible `L`-point `s' : Spec L ⟶ X'`. -/
theorem preimage_connectedComponent_of_locallyOfFiniteType_of_section_comp
    [LocallyOfFiniteType f] (hX : IsPullback fstX sndX f q) (hs : s ≫ f = 𝟙 (Spec (.of K)))
    {s' : Spec (.of L) ⟶ X'} (hs' : s' ≫ fstX = q ≫ s)
    (y : Spec (.of K)) (y' : Spec (.of L)) :
    fstX ⁻¹' connectedComponent (s y) = connectedComponent (s' y') := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  exact preimage_connectedComponent_of_section_comp hX hs hs' y y'

end BaseChange

end AlgebraicGeometry

end TauCeti
