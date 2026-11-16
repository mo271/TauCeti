/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen

/-!
# Connected components as open subschemes

On a locally connected scheme, a connected component is open and closed. Equip it with the
open-subscheme structure, so that its inclusion is both an open and a closed immersion.
This keeps the scheme structure on each component, including nilpotents, rather than giving
the closed set its reduced induced structure.

Because the component inclusion is a closed immersion, a component open of an affine scheme is
again affine. Every morphism from a preconnected scheme that hits a given component factors
uniquely through that component open, and conversely any morphism from a preconnected scheme that
is simultaneously an open and a closed immersion identifies its source with the component open of
any point in its image. Restricting along a component inclusion also preserves dense subsets, so a
dense open of the ambient scheme restricts to a nonempty dense open of each component.

## Main declarations

* `AlgebraicGeometry.Scheme.connectedComponentOpen`: the connected component of a point as an open
  subscheme.
* `AlgebraicGeometry.Scheme.isClosedImmersion_connectedComponentOpen_ι` and
  `AlgebraicGeometry.Scheme.isAffine_connectedComponentOpen`: the component inclusion is a closed
  immersion, so components of affine schemes are affine.
* `AlgebraicGeometry.Scheme.connectedComponentOpenLift`: universal factorization of a morphism from
  a preconnected scheme through the component open hit by any of its points.
* `AlgebraicGeometry.Scheme.Hom.range_eq_connectedComponent` and
  `AlgebraicGeometry.Scheme.isoConnectedComponentOpen`: a clopen immersion from a preconnected
  scheme has range equal to the connected component of any image point, inducing a canonical
  isomorphism with `connectedComponentOpen`.
* `AlgebraicGeometry.Scheme.dense_preimage_connectedComponentOpen_ι`: dense subsets pull back to
  dense subsets of each component open.

## References

* [The Stacks Project, Tag 004T](https://stacks.math.columbia.edu/tag/004T)
* [The Stacks Project, Tag 04MF](https://stacks.math.columbia.edu/tag/04MF)
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- A morphism from a preconnected scheme `Y` into `X` that sends some point into
`connectedComponent x` maps all of `Y` into `connectedComponent x`. -/
theorem range_subset_connectedComponent_of_mem {X Y : Scheme} [PreconnectedSpace Y] (g : Y ⟶ X)
    {x : X} {y : Y} (hy : g y ∈ connectedComponent x) :
    Set.range g ⊆ connectedComponent x := by
  rw [connectedComponent_eq hy]
  exact (isPreconnected_range g.continuous).subset_connectedComponent ⟨y, rfl⟩

/-- If `j : C ⟶ X` is both an open and a closed immersion from a preconnected scheme `C`, then its
topological image is the connected component of `j c` for every point `c : C`. No local
connectedness assumption on `X` is required. -/
theorem range_eq_connectedComponent {C X : Scheme} (j : C ⟶ X) [PreconnectedSpace C]
    [IsOpenImmersion j] [IsClosedImmersion j] (c : C) :
    Set.range j = connectedComponent (j c) := by
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  exact Set.Subset.antisymm (j.range_subset_connectedComponent_of_mem mem_connectedComponent)
    (hclopen.connectedComponent_subset ⟨c, rfl⟩)

end Scheme.Hom

namespace Scheme

universe u

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

/-- The underlying set of a component open is clopen. -/
theorem isClopen_connectedComponentOpen (x : X) :
    IsClopen (X.connectedComponentOpen x : Set X) :=
  isClopen_connectedComponent

/-- On a preconnected scheme, every component open is the whole scheme. -/
@[simp]
theorem connectedComponentOpen_eq_top [PreconnectedSpace X] (x : X) :
    X.connectedComponentOpen x = ⊤ := by
  ext y
  simp [PreconnectedSpace.connectedComponent_eq_univ]

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

/-- A component open of an affine scheme is affine, because its inclusion is a closed (hence
affine) morphism. -/
instance isAffine_connectedComponentOpen (x : X) [IsAffine X] :
    IsAffine (X.connectedComponentOpen x).toScheme :=
  isAffine_of_isAffineHom (X.connectedComponentOpen x).ι

end LocallyConnected

section Membership

variable {X : Scheme.{u}} [LocallyConnectedSpace X]

/-- Membership in `X.connectedComponentOpen x` is membership in `connectedComponent x`. -/
@[simp]
theorem mem_connectedComponentOpen {x y : X} :
    y ∈ X.connectedComponentOpen x ↔ y ∈ connectedComponent x :=
  Iff.rfl

/-- Every point belongs to its own component open. -/
theorem mem_connectedComponentOpen_self (x : X) :
    x ∈ X.connectedComponentOpen x :=
  mem_connectedComponent

/-- Two component opens coincide if and only if the first base point lies in the connected
component of the second. -/
theorem connectedComponentOpen_eq_iff {x y : X} :
    X.connectedComponentOpen x = X.connectedComponentOpen y ↔ x ∈ connectedComponent y := by
  rw [← SetLike.coe_set_eq, coe_connectedComponentOpen, coe_connectedComponentOpen,
    connectedComponent_eq_iff_mem]

/-- If `x` lies in the connected component of `y`, their component opens coincide. -/
theorem connectedComponentOpen_eq_of_mem {x y : X} (h : x ∈ connectedComponent y) :
    X.connectedComponentOpen x = X.connectedComponentOpen y :=
  connectedComponentOpen_eq_iff.mpr h

end Membership

section Lift

variable {X Y : Scheme.{u}} [LocallyConnectedSpace X] [PreconnectedSpace Y]

/-- Universal property of `connectedComponentOpen`: a morphism `g : Y ⟶ X` from a preconnected
scheme that sends some point `y : Y` into `connectedComponent x` factors through
`(X.connectedComponentOpen x).ι`. -/
noncomputable def connectedComponentOpenLift (g : Y ⟶ X) {x : X} {y : Y}
    (hy : g y ∈ connectedComponent x) :
    Y ⟶ (X.connectedComponentOpen x).toScheme :=
  IsOpenImmersion.lift (X.connectedComponentOpen x).ι g <| by
    simpa only [Opens.range_ι, coe_connectedComponentOpen] using
      g.range_subset_connectedComponent_of_mem hy

/-- `connectedComponentOpenLift` followed by the component inclusion recovers the original
morphism. -/
@[reassoc (attr := simp)]
theorem connectedComponentOpenLift_ι (g : Y ⟶ X) {x : X} {y : Y}
    (hy : g y ∈ connectedComponent x) :
    X.connectedComponentOpenLift g hy ≫ (X.connectedComponentOpen x).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- On underlying points, `connectedComponentOpenLift` agrees with `g` after coercion to `X`. -/
@[simp]
theorem connectedComponentOpenLift_apply_coe (g : Y ⟶ X) {x : X} {y : Y}
    (hy : g y ∈ connectedComponent x) (z : Y) :
    (X.connectedComponentOpenLift g hy z).1 = g z := by
  change (X.connectedComponentOpen x).ι (X.connectedComponentOpenLift g hy z) = g z
  rw [← Scheme.Hom.comp_apply, connectedComponentOpenLift_ι]

/-- Any factorization of `g : Y ⟶ X` through `(X.connectedComponentOpen x).ι` equals
`connectedComponentOpenLift`. -/
theorem eq_connectedComponentOpenLift_of_comp_eq {g : Y ⟶ X} {x : X} {y : Y}
    (hy : g y ∈ connectedComponent x) {l : Y ⟶ (X.connectedComponentOpen x).toScheme}
    (hl : l ≫ (X.connectedComponentOpen x).ι = g) :
    l = X.connectedComponentOpenLift g hy :=
  (cancel_mono (X.connectedComponentOpen x).ι).mp
    (hl.trans (X.connectedComponentOpenLift_ι g hy).symm)

/-- Precomposing `connectedComponentOpenLift` with a morphism from a preconnected scheme gives the
`connectedComponentOpenLift` of the composite. -/
@[reassoc]
theorem comp_connectedComponentOpenLift {Z : Scheme.{u}} [PreconnectedSpace Z] (h : Z ⟶ Y)
    (g : Y ⟶ X) {x : X} {z : Z} (hz : (h ≫ g) z ∈ connectedComponent x) :
    h ≫ X.connectedComponentOpenLift g (y := h z) (by simpa using hz) =
      X.connectedComponentOpenLift (h ≫ g) hz :=
  eq_connectedComponentOpenLift_of_comp_eq hz (by simp)

end Lift

section Iso

variable {X C : Scheme.{u}} [LocallyConnectedSpace X] [PreconnectedSpace C]

/-- A morphism from a preconnected scheme `C` into a locally connected scheme `X` that is both an
open and a closed immersion identifies `C` with the component open of `j c` for any `c : C`. -/
noncomputable def isoConnectedComponentOpen (j : C ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (c : C) :
    C ≅ (X.connectedComponentOpen (j c)).toScheme :=
  IsOpenImmersion.isoOfRangeEq j (X.connectedComponentOpen (j c)).ι <| by
    rw [j.range_eq_connectedComponent c, Opens.range_ι, coe_connectedComponentOpen]

/-- The forward morphism of `isoConnectedComponentOpen` commutes with the inclusions into `X`. -/
@[reassoc (attr := simp)]
theorem isoConnectedComponentOpen_hom_ι (j : C ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (c : C) :
    (X.isoConnectedComponentOpen j c).hom ≫ (X.connectedComponentOpen (j c)).ι = j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse morphism of `isoConnectedComponentOpen` commutes with the inclusions into `X`. -/
@[reassoc (attr := simp)]
theorem isoConnectedComponentOpen_inv_fac (j : C ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (c : C) :
    (X.isoConnectedComponentOpen j c).inv ≫ j = (X.connectedComponentOpen (j c)).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- On underlying points, `(X.isoConnectedComponentOpen j c).hom` agrees with `j` after coercion
to `X`. -/
@[simp]
theorem isoConnectedComponentOpen_hom_apply_coe (j : C ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] (c c' : C) :
    ((X.isoConnectedComponentOpen j c).hom c').1 = j c' := by
  change (X.connectedComponentOpen (j c)).ι ((X.isoConnectedComponentOpen j c).hom c') = j c'
  rw [← Scheme.Hom.comp_apply, isoConnectedComponentOpen_hom_ι]

end Iso

section Dense

variable (X : Scheme.{u}) [LocallyConnectedSpace X]

/-- Pulling back a dense subset of `X` along a component inclusion yields a dense subset of the
component open. -/
theorem dense_preimage_connectedComponentOpen_ι {s : Set X} (hs : Dense s) (x : X) :
    Dense ((X.connectedComponentOpen x).ι ⁻¹' s) :=
  hs.preimage (X.connectedComponentOpen x).ι.isOpenEmbedding.isOpenMap

/-- The restriction of a dense open of `X` to any component open is nonempty. -/
theorem nonempty_preimage_connectedComponentOpen_ι_of_dense {U : X.Opens}
    (hU : Dense (U : Set X)) (x : X) :
    Nonempty ((X.connectedComponentOpen x).ι ⁻¹ᵁ U) := by
  obtain ⟨p, -, hp⟩ :=
    (X.dense_preimage_connectedComponentOpen_ι hU x).inter_open_nonempty
      Set.univ isOpen_univ Set.univ_nonempty
  exact ⟨⟨p, hp⟩⟩

end Dense

end Scheme

end AlgebraicGeometry
