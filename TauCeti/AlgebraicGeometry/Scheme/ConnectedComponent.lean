/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Connected components as open subschemes

On a locally connected scheme, a connected component is open and closed. Equip it with the
open-subscheme structure, so that its inclusion is both an open and a closed immersion.
This keeps the scheme structure on each component, including nilpotents, rather than giving
the closed set its reduced induced structure.

Any morphism from a preconnected scheme factors uniquely through the component open containing the
image of a chosen point (`AlgebraicGeometry.Scheme.Hom.liftConnectedComponentOpen`); in particular
a section over a preconnected base restricts to a section of the component open containing it.
Conversely, any open and closed immersion from a preconnected scheme into `X` has topological image
equal to a connected component (`AlgebraicGeometry.Scheme.Hom.range_eq_connectedComponent`) and is
canonically isomorphic to the corresponding component open
(`AlgebraicGeometry.Scheme.Hom.isoConnectedComponentOpen`).

## Main declarations

* `AlgebraicGeometry.Scheme.connectedComponentOpen`: the connected component of a point as an open
  subscheme of a locally connected scheme.
* `AlgebraicGeometry.Scheme.isAffine_connectedComponentOpen`: a component open of an affine locally
  connected scheme is affine.
* `AlgebraicGeometry.Scheme.Hom.liftConnectedComponentOpen`: the unique lift of a morphism from a
  preconnected scheme into the component open of the image of a chosen point.
* `AlgebraicGeometry.Scheme.Hom.range_eq_connectedComponent`: the range of an open and closed
  immersion from a preconnected scheme is the connected component of any image point.
* `AlgebraicGeometry.Scheme.Hom.isoConnectedComponentOpen`: the canonical isomorphism between the
  source of an open and closed immersion from a preconnected scheme and the component open of any
  image point.

## References

* The Stacks Project, Topology, Section 5.7 (Tag 004T), connected components.
* The Stacks Project, Schemes, Section 26.23, open and closed subschemes.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

namespace Hom

/-- The topological image of a morphism that is both an open and a closed immersion is clopen. -/
theorem isClopen_range {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] :
    IsClopen (Set.range j) :=
  ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩

/-- If `j : U ⟶ X` is both an open and a closed immersion with `U` preconnected, then for any point
`u : U` the image of `j` is the connected component of `j u` in `X`. -/
theorem range_eq_connectedComponent {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] [PreconnectedSpace U] (u : U) :
    Set.range j = connectedComponent (j u) :=
  ((isPreconnected_range j.continuous).subset_connectedComponent
    (Set.mem_range_self u)).antisymm
    (j.isClopen_range.connectedComponent_subset (Set.mem_range_self u))

end Hom

section LocallyConnected

variable (X : Scheme.{u}) [LocallyConnectedSpace X]

/-- The connected component of a point, with its open-subscheme structure. -/
def connectedComponentOpen (x : X) : X.Opens :=
  ⟨connectedComponent x, isOpen_connectedComponent⟩

/-- The points of the component open are precisely the topological connected component. -/
@[simp]
theorem coe_connectedComponentOpen (x : X) :
    (connectedComponentOpen X x : Set X) = connectedComponent x :=
  (rfl)

/-- Membership in `X.connectedComponentOpen x` is membership in `connectedComponent x`. -/
@[simp]
theorem mem_connectedComponentOpen {X : Scheme.{u}} [LocallyConnectedSpace X] {x y : X} :
    y ∈ X.connectedComponentOpen x ↔ y ∈ connectedComponent x :=
  Iff.rfl

/-- Every point belongs to its own component open. -/
theorem self_mem_connectedComponentOpen (x : X) : x ∈ X.connectedComponentOpen x :=
  mem_connectedComponent

/-- The underlying set of a component open is closed. -/
theorem isClosed_connectedComponentOpen (x : X) :
    IsClosed (X.connectedComponentOpen x : Set X) :=
  isClosed_connectedComponent

/-- The underlying set of a component open is clopen. -/
theorem isClopen_connectedComponentOpen (x : X) :
    IsClopen (X.connectedComponentOpen x : Set X) :=
  isClopen_connectedComponent

/-- A component open is connected and nonempty. -/
instance connectedSpace_connectedComponentOpen (x : X) :
    ConnectedSpace (connectedComponentOpen X x).toScheme :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- The inclusion of a component open is also a closed immersion. -/
instance isClosedImmersion_connectedComponentOpen_ι (x : X) :
    IsClosedImmersion (connectedComponentOpen X x).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Opens.range_ι, coe_connectedComponentOpen] using
      (isClosed_connectedComponent (x := x)))

/-- A component open of an affine locally connected scheme is affine, since its inclusion is a
closed immersion and hence an affine morphism. -/
instance isAffine_connectedComponentOpen [IsAffine X] (x : X) :
    IsAffine (X.connectedComponentOpen x).toScheme :=
  isAffine_of_isAffineHom (X.connectedComponentOpen x).ι

/-- If `y` lies in the component open of `x`, then the two component opens coincide. -/
theorem connectedComponentOpen_eq_of_mem {X : Scheme.{u}} [LocallyConnectedSpace X] {x y : X}
    (hy : y ∈ X.connectedComponentOpen x) :
    X.connectedComponentOpen y = X.connectedComponentOpen x :=
  TopologicalSpace.Opens.ext (connectedComponent_eq hy).symm

/-- Two points define the same component open if and only if one lies in the connected component
of the other. -/
theorem connectedComponentOpen_eq_iff {X : Scheme.{u}} [LocallyConnectedSpace X] {x y : X} :
    X.connectedComponentOpen x = X.connectedComponentOpen y ↔ x ∈ connectedComponent y :=
  TopologicalSpace.Opens.ext_iff.trans connectedComponent_eq_iff_mem

/-- On a preconnected locally connected scheme, every component open is the whole scheme. -/
theorem connectedComponentOpen_eq_top_of_preconnectedSpace [PreconnectedSpace X] (x : X) :
    X.connectedComponentOpen x = ⊤ :=
  TopologicalSpace.Opens.ext (PreconnectedSpace.connectedComponent_eq_univ x)

/-- The component open of a point `x : X` is the whole scheme if and only if `X` is connected. -/
theorem connectedComponentOpen_eq_top_iff (x : X) :
    X.connectedComponentOpen x = ⊤ ↔ ConnectedSpace X := by
  refine ⟨fun h ↦ connectedSpace_iff_univ.mpr ?_,
    fun _ ↦ X.connectedComponentOpen_eq_top_of_preconnectedSpace x⟩
  have huniv : (Set.univ : Set X) = connectedComponent x := by
    simpa only [TopologicalSpace.Opens.coe_top, coe_connectedComponentOpen] using
      congrArg SetLike.coe h.symm
  exact huniv ▸ isConnected_connectedComponent

end LocallyConnected

namespace Hom

/-- A morphism from a preconnected scheme maps the whole source into the connected component of any
point containing at least one image point. -/
theorem range_subset_connectedComponent_of_mem {Y X : Scheme.{u}} [PreconnectedSpace Y]
    (g : Y ⟶ X) {x : X} {y : Y} (hy : g y ∈ connectedComponent x) :
    Set.range g ⊆ connectedComponent x := by
  rw [connectedComponent_eq hy]
  exact (isPreconnected_range g.continuous).subset_connectedComponent (Set.mem_range_self y)

section Lift

variable {Y X : Scheme.{u}} [PreconnectedSpace Y] [LocallyConnectedSpace X] (g : Y ⟶ X)

/-- Lift a morphism `g : Y ⟶ X` from a preconnected scheme into a component open of `X` that
contains `g y` for some `y : Y`. -/
noncomputable def liftConnectedComponentOpenOfMem {x : X} {y : Y}
    (hy : g y ∈ X.connectedComponentOpen x) :
    Y ⟶ (X.connectedComponentOpen x).toScheme :=
  IsOpenImmersion.lift (X.connectedComponentOpen x).ι g (by
    simpa only [Opens.range_ι, coe_connectedComponentOpen] using
      g.range_subset_connectedComponent_of_mem hy)

/-- Composing `liftConnectedComponentOpenOfMem` with the component inclusion recovers the original
morphism. -/
@[reassoc (attr := simp)]
theorem liftConnectedComponentOpenOfMem_ι {x : X} {y : Y}
    (hy : g y ∈ X.connectedComponentOpen x) :
    g.liftConnectedComponentOpenOfMem hy ≫ (X.connectedComponentOpen x).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- On underlying points, `liftConnectedComponentOpenOfMem` agrees with the original morphism. -/
@[simp]
theorem val_liftConnectedComponentOpenOfMem_apply {x : X} {y : Y}
    (hy : g y ∈ X.connectedComponentOpen x) (z : Y) :
    (g.liftConnectedComponentOpenOfMem hy z).1 = g z :=
  ((X.connectedComponentOpen x).ι_apply _).symm.trans
    (by rw [← Hom.comp_apply, g.liftConnectedComponentOpenOfMem_ι hy])

/-- A morphism into `X.connectedComponentOpen x` equals `g.liftConnectedComponentOpenOfMem hy` if
and only if its composition with the component inclusion is `g`. -/
theorem eq_liftConnectedComponentOpenOfMem_iff {x : X} {y : Y}
    (hy : g y ∈ X.connectedComponentOpen x)
    {l : Y ⟶ (X.connectedComponentOpen x).toScheme} :
    l = g.liftConnectedComponentOpenOfMem hy ↔ l ≫ (X.connectedComponentOpen x).ι = g :=
  ⟨fun h ↦ h ▸ g.liftConnectedComponentOpenOfMem_ι hy, IsOpenImmersion.lift_uniq _ _ _ _⟩

/-- Lift a morphism `g : Y ⟶ X` from a preconnected scheme into the component open of `g y`. -/
noncomputable def liftConnectedComponentOpen (y : Y) :
    Y ⟶ (X.connectedComponentOpen (g y)).toScheme :=
  g.liftConnectedComponentOpenOfMem (X.self_mem_connectedComponentOpen (g y))

/-- Composing `liftConnectedComponentOpen` with the component inclusion recovers `g`. -/
@[reassoc (attr := simp)]
theorem liftConnectedComponentOpen_ι (y : Y) :
    g.liftConnectedComponentOpen y ≫ (X.connectedComponentOpen (g y)).ι = g :=
  g.liftConnectedComponentOpenOfMem_ι _

/-- On underlying points, `liftConnectedComponentOpen` agrees with `g`. -/
@[simp]
theorem val_liftConnectedComponentOpen_apply (y z : Y) :
    (g.liftConnectedComponentOpen y z).1 = g z :=
  g.val_liftConnectedComponentOpenOfMem_apply _ z

/-- Uniqueness of the lift into `X.connectedComponentOpen (g y)`. -/
theorem eq_liftConnectedComponentOpen_iff (y : Y)
    {l : Y ⟶ (X.connectedComponentOpen (g y)).toScheme} :
    l = g.liftConnectedComponentOpen y ↔ l ≫ (X.connectedComponentOpen (g y)).ι = g :=
  g.eq_liftConnectedComponentOpenOfMem_iff _

/-- A section `g` of `f : X ⟶ Y` over a preconnected base restricts to a section of the component
open containing `g y`. -/
theorem liftConnectedComponentOpen_comp_eq_id {f : X ⟶ Y} (hg : g ≫ f = 𝟙 Y) (y : Y) :
    g.liftConnectedComponentOpen y ≫ ((X.connectedComponentOpen (g y)).ι ≫ f) = 𝟙 Y := by
  rw [← Category.assoc, g.liftConnectedComponentOpen_ι, hg]

end Lift

section Iso

variable {U X : Scheme.{u}} [LocallyConnectedSpace X] (j : U ⟶ X)
  [IsOpenImmersion j] [IsClosedImmersion j] [PreconnectedSpace U]

/-- An open and closed immersion from a preconnected scheme into a locally connected scheme `X` is
canonically isomorphic to the component open of any image point `j u`. -/
noncomputable def isoConnectedComponentOpen (u : U) :
    U ≅ (X.connectedComponentOpen (j u)).toScheme :=
  IsOpenImmersion.isoOfRangeEq j (X.connectedComponentOpen (j u)).ι (by
    rw [j.range_eq_connectedComponent u, Opens.range_ι, X.coe_connectedComponentOpen])

/-- The forward direction of `isoConnectedComponentOpen` commutes with the inclusions into `X`. -/
@[reassoc (attr := simp)]
theorem isoConnectedComponentOpen_hom_ι (u : U) :
    (j.isoConnectedComponentOpen u).hom ≫ (X.connectedComponentOpen (j u)).ι = j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse direction of `isoConnectedComponentOpen` commutes with the inclusions into `X`. -/
@[reassoc (attr := simp)]
theorem isoConnectedComponentOpen_inv_fac (u : U) :
    (j.isoConnectedComponentOpen u).inv ≫ j = (X.connectedComponentOpen (j u)).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

end Iso

end Hom

end AlgebraicGeometry.Scheme
