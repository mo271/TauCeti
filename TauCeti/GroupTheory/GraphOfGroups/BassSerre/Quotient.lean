/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Basic

/-!
# Quotient of the Bass–Serre tree, edgeless cases, and uncollapsed path quotients

For a graph of groups `𝔸` over a Serre graph `Γ` and a base vertex `v₀ : Γ.V`, forgetting the path
component sends every vertex `p A_v` and dart `p α_e(A_e)` of `bassSerreTree 𝔸 v₀` into the
connected component `Γ.component v₀` of `v₀` in `Γ` (`bassSerreProjHom`). This morphism is
invariant under `π₁(𝔸, v₀)` and its fibres are the `π₁(𝔸, v₀)`-orbits, so it descends to a graph
isomorphism `(bassSerreTree 𝔸 v₀).quotient.Iso (Γ.component v₀)` (`quotientBassSerreTreeIso`).
When `Γ` is preconnected, composing with `Γ.componentIsoOfPreconnected` identifies the quotient
`(bassSerreTree 𝔸 v₀).quotient` with `Γ` itself (`quotientBassSerreTreeIsoOfPreconnected`). As a
consequence, `π₁(𝔸, v₀)` acts transitively on the vertices of `bassSerreTree 𝔸 v₀` if and only if
`Γ.component v₀` has a single vertex.

When `Γ` has no edges (`[IsEmpty Γ.E]`), `bassSerreTree 𝔸 v₀` has no darts and a unique vertex
`bassSerreBase 𝔸 v₀`, so it is isomorphic to the one-vertex tree `GTree.point (π₁ 𝔸 v₀)`
(`bassSerreTreePointIso`), even when `Γ` has additional isolated components such as `noEdge Bool`
where `IsEmpty (𝔸.Path ⟨false⟩ ⟨true⟩)` while both `bassSerreTree 𝔸 v₀` and its quotient have
`Nat.card` equal to `1`.

Finally, we contrast `bassSerreVertex` with the uncollapsed homotopy quotient
`Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩)` without the right `A_v`-coset relation: left concatenation by
`π₁(𝔸, v₀)` acts *freely* on `Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩)` (`pathQuotientSmul_eq_self_iff`),
and `a ↦ ⟦Path.ofVertex a⟧` injects `A_{v₀}` into `Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩)`
(`pathQuotientOfVertex_injective`), so omitting the right `A_v`-quotient destroys the vertex
stabilizers `p A_v p⁻¹`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreProjHom`: the `π₁(𝔸, v₀)`-invariant projection
  `(bassSerreTree 𝔸 v₀).toSerreGraph.Hom (Γ.component v₀)`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeHom`: the induced morphism
  `(bassSerreTree 𝔸 v₀).quotient.Hom (Γ.component v₀)`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeIso`: the isomorphism
  `(bassSerreTree 𝔸 v₀).quotient.Iso (Γ.component v₀)`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeIsoOfPreconnected`: the isomorphism
  `(bassSerreTree 𝔸 v₀).quotient.Iso Γ` when `Γ` is preconnected.
* `TauCeti.GraphOfGroups.bassSerreTreePointIso`: the isomorphism with `GTree.point (π₁ 𝔸 v₀)` when
  `[IsEmpty Γ.E]`.
* `TauCeti.GraphOfGroups.pathQuotientSmul`: left concatenation of `π₁(𝔸, v₀)` on uncollapsed
  homotopy classes `Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩)`.

## Main results

* `TauCeti.GraphOfGroups.isPretransitive_bassSerreTree_V_iff`: `π₁(𝔸, v₀)` acts transitively on the
  vertices of `bassSerreTree 𝔸 v₀` if and only if `Subsingleton (Γ.component v₀).V`.
* `TauCeti.GraphOfGroups.isEmpty_path_of_isEmpty_dart_of_ne`: over an edgeless graph, there is no
  `𝔸`-path between distinct vertices.
* `TauCeti.GraphOfGroups.pathQuotientSmul_eq_self_iff`,
  `TauCeti.GraphOfGroups.pathQuotientOfVertex_injective`: without the right `A_v`-quotient,
  `π₁(𝔸, v₀)` acts freely on path homotopy classes and separates distinct elements of `A_{v₀}`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5 and Proposition 2.6.
* J.-P. Serre, *Trees*, Chapter I, §5.3–§5.4.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

open SerreGraph _root_.MulAction

/-! ### Projection to `Γ.component v₀` and the quotient graph isomorphism -/

section Quotient

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- The `π₁(𝔸, v₀)`-invariant morphism of Serre graphs from `bassSerreTree 𝔸 v₀` onto the
connected component `Γ.component v₀`, forgetting the path coset and retaining the underlying vertex
or dart. -/
def bassSerreProjHom : (bassSerreTree 𝔸 v₀).toSerreGraph.Hom (Γ.component v₀) where
  mapV x := ⟨x.1, Quotient.inductionOn x.2 fun p => mem_componentVertices_iff.mpr ⟨p.edgePath⟩⟩
  mapE d := ⟨d.1, mem_inducedDarts_componentVertices_iff.mpr
    (Quotient.inductionOn d.2 fun p => mem_componentVertices_iff.mpr ⟨p.edgePath⟩)⟩
  map_src _ := Subtype.ext rfl
  map_rev _ := Subtype.ext rfl

@[simp] theorem bassSerreProjHom_mapV_bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreProjHom 𝔸 v₀).mapV (bassSerreVertex p) =
      ⟨v, mem_componentVertices_iff.mpr ⟨p.edgePath⟩⟩ :=
  Subtype.ext (bassSerreVertex_fst p)

@[simp] theorem bassSerreProjHom_mapV_bassSerreBase :
    (bassSerreProjHom 𝔸 v₀).mapV (bassSerreBase 𝔸 v₀) = Γ.componentBase v₀ := by
  rw [← bassSerreVertex_nil, bassSerreProjHom_mapV_bassSerreVertex]
  rfl

@[simp] theorem bassSerreProjHom_mapE_bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreProjHom 𝔸 v₀).mapE (bassSerreDart e p) =
      ⟨e, mem_inducedDarts_componentVertices_iff.mpr
        (mem_componentVertices_iff.mpr ⟨p.edgePath⟩)⟩ :=
  Subtype.ext (bassSerreDart_fst e p)

@[simp] theorem bassSerreProjHom_mapE_bassSerreArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (e : a ⟶ b) : ((bassSerreProjHom 𝔸 v₀).mapE (bassSerreArrowDart p e)).1 = e.1 :=
  bassSerreArrowDart_fst p e

/-- The projection `bassSerreProjHom` is invariant under the action of `π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreProjHom_comp_action (g : π₁ 𝔸 v₀) :
    Hom.comp (bassSerreProjHom 𝔸 v₀) ((bassSerreTree 𝔸 v₀).action g).toHom =
      bassSerreProjHom 𝔸 v₀ := by
  refine Hom.ext _ (funext fun x => ?_) (funext fun d => ?_)
  · induction x using bassSerreVertex_induction_on with | mk p =>
    induction g using π₁.induction_on with | _ s =>
    rw [Hom.comp_mapV, Iso.toHom_mapV, Function.comp_apply, ← Aut.smul_vertex_def,
      ← GTree.smul_vertex_def, mk_smul_bassSerreVertex]
    exact Subtype.ext (by simp)
  · induction d using bassSerreDart_induction_on with | mk e p =>
    induction g using π₁.induction_on with | _ s =>
    rw [Hom.comp_mapE, Iso.toHom_mapE, Function.comp_apply, ← Aut.smul_dart_def,
      ← GTree.smul_dart_def, mk_smul_bassSerreDart]
    exact Subtype.ext (by simp)

/-- The morphism `(bassSerreTree 𝔸 v₀).quotient.Hom (Γ.component v₀)` descended from
`bassSerreProjHom`. -/
def quotientBassSerreTreeHom : (bassSerreTree 𝔸 v₀).quotient.Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (bassSerreTree 𝔸 v₀).smul_ne_rev (bassSerreProjHom 𝔸 v₀)
    (bassSerreProjHom_comp_action 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeHom_comp_quotientMap :
    Hom.comp (quotientBassSerreTreeHom 𝔸 v₀) (bassSerreTree 𝔸 v₀).quotientMap =
      bassSerreProjHom 𝔸 v₀ :=
  SerreGraph.quotientLift_comp_quotientMap _ _

@[simp] theorem quotientBassSerreTreeHom_mapV_quotientMap (x : (bassSerreTree 𝔸 v₀).V) :
    (quotientBassSerreTreeHom 𝔸 v₀).mapV ((bassSerreTree 𝔸 v₀).quotientMap.mapV x) =
      (bassSerreProjHom 𝔸 v₀).mapV x :=
  SerreGraph.quotientLift_mapV_quotientMap _ _ x

@[simp] theorem quotientBassSerreTreeHom_mapE_quotientMap (d : (bassSerreTree 𝔸 v₀).E) :
    (quotientBassSerreTreeHom 𝔸 v₀).mapE ((bassSerreTree 𝔸 v₀).quotientMap.mapE d) =
      (bassSerreProjHom 𝔸 v₀).mapE d :=
  SerreGraph.quotientLift_mapE_quotientMap _ _ d

/-- `quotientBassSerreTreeHom` is bijective on vertices. -/
theorem quotientBassSerreTreeHom_mapV_bijective :
    Function.Bijective (quotientBassSerreTreeHom 𝔸 v₀).mapV := by
  refine ⟨fun q₁ q₂ h => ?_, fun ⟨v, hv⟩ => ?_⟩
  · obtain ⟨x₁, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective q₁
    obtain ⟨x₂, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective q₂
    induction x₁ using bassSerreVertex_induction_on with | @mk v₁ p₁ =>
    induction x₂ using bassSerreVertex_induction_on with | @mk v₂ p₂ =>
    rw [quotientBassSerreTreeHom_mapV_quotientMap, quotientBassSerreTreeHom_mapV_quotientMap,
      bassSerreProjHom_mapV_bassSerreVertex, bassSerreProjHom_mapV_bassSerreVertex] at h
    have hv : v₁ = v₂ := congrArg Subtype.val h
    subst hv
    refine SerreGraph.quotientMap_mapV_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    change π₁.mk (p₂.comp p₁.reverse) • bassSerreVertex p₁ = bassSerreVertex p₂
    rw [mk_smul_bassSerreVertex]
    exact bassSerreVertex_congr (by
      simpa only [Quiver.Path.comp_nil] using
        Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨P⟩ := mem_componentVertices_iff.mp hv
    exact ⟨(bassSerreTree 𝔸 v₀).quotientMap.mapV (bassSerreVertex ((dartPrefunctor 𝔸).mapPath P)),
      Subtype.ext (by simp)⟩

/-- `quotientBassSerreTreeHom` is bijective on darts. -/
theorem quotientBassSerreTreeHom_mapE_bijective :
    Function.Bijective (quotientBassSerreTreeHom 𝔸 v₀).mapE := by
  refine ⟨fun q₁ q₂ h => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨d₁, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapE_surjective q₁
    obtain ⟨d₂, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapE_surjective q₂
    induction d₁ using bassSerreDart_induction_on with | mk e₁ p₁ =>
    induction d₂ using bassSerreDart_induction_on with | mk e₂ p₂ =>
    rw [quotientBassSerreTreeHom_mapE_quotientMap, quotientBassSerreTreeHom_mapE_quotientMap,
      bassSerreProjHom_mapE_bassSerreDart, bassSerreProjHom_mapE_bassSerreDart] at h
    have he : e₁ = e₂ := congrArg Subtype.val h
    subst he
    refine SerreGraph.quotientMap_mapE_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    change π₁.mk (p₂.comp p₁.reverse) • bassSerreDart e₁ p₁ = bassSerreDart e₁ p₂
    rw [mk_smul_bassSerreDart]
    exact bassSerreDart_congr (by
      simpa only [Quiver.Path.comp_nil] using
        Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨P⟩ := mem_componentVertices_iff.mp (mem_inducedDarts_componentVertices_iff.mp he)
    exact ⟨(bassSerreTree 𝔸 v₀).quotientMap.mapE (bassSerreDart e ((dartPrefunctor 𝔸).mapPath P)),
      Subtype.ext (by simp)⟩

/-- The quotient of the Bass–Serre tree `bassSerreTree 𝔸 v₀` by `π₁(𝔸, v₀)` is canonically
isomorphic to the connected component `Γ.component v₀`. -/
noncomputable def quotientBassSerreTreeIso :
    (bassSerreTree 𝔸 v₀).quotient.Iso (Γ.component v₀) :=
  (quotientBassSerreTreeHom 𝔸 v₀).toIso (quotientBassSerreTreeHom_mapV_bijective 𝔸 v₀)
    (quotientBassSerreTreeHom_mapE_bijective 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeIso_toHom :
    (quotientBassSerreTreeIso 𝔸 v₀).toHom = quotientBassSerreTreeHom 𝔸 v₀ :=
  Hom.toIso_toHom ..

@[simp] theorem quotientBassSerreTreeIso_equivV_quotientMap (x : (bassSerreTree 𝔸 v₀).V) :
    (quotientBassSerreTreeIso 𝔸 v₀).equivV ((bassSerreTree 𝔸 v₀).quotientMap.mapV x) =
      (bassSerreProjHom 𝔸 v₀).mapV x := by
  rw [quotientBassSerreTreeIso, Hom.toIso_equivV_apply, quotientBassSerreTreeHom_mapV_quotientMap]

@[simp] theorem quotientBassSerreTreeIso_equivE_quotientMap (d : (bassSerreTree 𝔸 v₀).E) :
    (quotientBassSerreTreeIso 𝔸 v₀).equivE ((bassSerreTree 𝔸 v₀).quotientMap.mapE d) =
      (bassSerreProjHom 𝔸 v₀).mapE d := by
  rw [quotientBassSerreTreeIso, Hom.toIso_equivE_apply, quotientBassSerreTreeHom_mapE_quotientMap]

/-- When `Γ` is preconnected, the quotient `(bassSerreTree 𝔸 v₀).quotient` is canonically
isomorphic to `Γ`. -/
noncomputable def quotientBassSerreTreeIsoOfPreconnected (hΓ : Γ.Preconnected) (v₀ : Γ.V) :
    (bassSerreTree 𝔸 v₀).quotient.Iso Γ :=
  (quotientBassSerreTreeIso 𝔸 v₀).trans (Γ.componentIsoOfPreconnected hΓ v₀)

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivV_quotientMap
    (hΓ : Γ.Preconnected) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (quotientBassSerreTreeIsoOfPreconnected 𝔸 hΓ v₀).equivV
      ((bassSerreTree 𝔸 v₀).quotientMap.mapV (bassSerreVertex p)) = v := by
  rw [quotientBassSerreTreeIsoOfPreconnected, Iso.trans_equivV, Equiv.trans_apply,
    quotientBassSerreTreeIso_equivV_quotientMap, bassSerreProjHom_mapV_bassSerreVertex]
  exact componentIsoOfPreconnected_equivV_apply hΓ v₀ _

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivE_quotientMap
    (hΓ : Γ.Preconnected) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (quotientBassSerreTreeIsoOfPreconnected 𝔸 hΓ v₀).equivE
      ((bassSerreTree 𝔸 v₀).quotientMap.mapE (bassSerreDart e p)) = e := by
  rw [quotientBassSerreTreeIsoOfPreconnected, Iso.trans_equivE, Equiv.trans_apply,
    quotientBassSerreTreeIso_equivE_quotientMap, bassSerreProjHom_mapE_bassSerreDart]
  exact componentIsoOfPreconnected_equivE_apply hΓ v₀ _

/-- `π₁(𝔸, v₀)` acts transitively on the vertices of `bassSerreTree 𝔸 v₀` if and only if
`Γ.component v₀` has at most one vertex. -/
theorem isPretransitive_bassSerreTree_V_iff :
    IsPretransitive (π₁ 𝔸 v₀) (bassSerreTree 𝔸 v₀).V ↔ Subsingleton (Γ.component v₀).V := by
  refine ⟨fun h => (quotientBassSerreTreeIso 𝔸 v₀).equivV.subsingleton_congr.mp ⟨fun a b => ?_⟩,
    fun h => ⟨fun x y => ?_⟩⟩
  · obtain ⟨x, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective a
    obtain ⟨y, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective b
    obtain ⟨g, rfl⟩ := h.exists_smul_eq x y
    exact (SerreGraph.quotientMap_mapV_smul g x).symm
  · have hq : (bassSerreTree 𝔸 v₀).quotientMap.mapV x = (bassSerreTree 𝔸 v₀).quotientMap.mapV y :=
      (quotientBassSerreTreeIso 𝔸 v₀).equivV.injective (Subsingleton.elim _ _)
    exact SerreGraph.quotientMap_mapV_eq_iff.mp hq

/-- Over a graph with at most one vertex, `π₁(𝔸, v₀)` acts transitively on the vertices of
`bassSerreTree 𝔸 v₀`. -/
instance [Subsingleton Γ.V] : IsPretransitive (π₁ 𝔸 v₀) (bassSerreTree 𝔸 v₀).V :=
  (isPretransitive_bassSerreTree_V_iff 𝔸 v₀).mpr
    ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩

end Quotient

/-! ### Edgeless and disconnected graphs of groups -/

section Edgeless

universe u' v'

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Over a graph without edges, `bassSerreTree 𝔸 v₀` has no darts. -/
instance [IsEmpty Γ.E] : IsEmpty (bassSerreTree 𝔸 v₀).E :=
  ⟨fun d => isEmptyElim d.1⟩

/-- Over a graph without edges, `bassSerreBase 𝔸 v₀` is the unique vertex of
`bassSerreTree 𝔸 v₀`. -/
instance [IsEmpty Γ.E] : Unique (bassSerreTree 𝔸 v₀).V where
  default := bassSerreBase 𝔸 v₀
  uniq x := @Subsingleton.elim _
    (((bassSerreTree 𝔸 v₀).connected_iff.mp (IsTree.connected _ (bassSerreTree 𝔸 v₀).isTree)).2
      |>.subsingleton_of_isEmpty)
    x _

@[simp] theorem bassSerreTree_action_eq_one_of_isEmpty [IsEmpty Γ.E] :
    (bassSerreTree 𝔸 v₀).action = 1 := by
  ext g x
  · exact Subsingleton.elim _ _
  · exact isEmptyElim x

/-- Over a graph `Γ` without edges, `bassSerreTree 𝔸 v₀` is isomorphic as a Serre graph to the
one-vertex tree `GTree.point (π₁ 𝔸 v₀)`. -/
noncomputable def bassSerreTreePointIso [IsEmpty Γ.E] :
    (bassSerreTree 𝔸 v₀).toSerreGraph.Iso (GTree.point.{u', v'} (π₁ 𝔸 v₀)).toSerreGraph := by
  have _ : IsEmpty (GTree.point.{u', v'} (π₁ 𝔸 v₀)).E :=
    (GTree.point.{u', v'} (π₁ 𝔸 v₀)).isAcyclic.isEmpty_dart_of_subsingleton
  have _ : Nonempty (GTree.point.{u', v'} (π₁ 𝔸 v₀)).V :=
    ((GTree.point.{u', v'} (π₁ 𝔸 v₀)).connected_iff.mp
      (IsTree.connected _ (GTree.point.{u', v'} (π₁ 𝔸 v₀)).isTree)).1
  exact
    { equivV :=
        { toFun := fun _ => Classical.arbitrary _
          invFun := fun _ => bassSerreBase 𝔸 v₀
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ }
      equivE := Equiv.equivOfIsEmpty _ _
      map_src := fun d => isEmptyElim d
      map_rev := fun d => isEmptyElim d }

/-- Over a graph `Γ` without edges, `bassSerreTree 𝔸 v₀` lies in the same deformation space as the
one-vertex tree `GTree.point (π₁ 𝔸 v₀)`. -/
theorem bassSerreTree_sameDeformationSpace_point [IsEmpty Γ.E] :
    (bassSerreTree 𝔸 v₀).SameDeformationSpace (GTree.point.{u', v'} (π₁ 𝔸 v₀)) :=
  GTree.sameDeformationSpace_iff.mpr
    ⟨(bassSerreTree 𝔸 v₀).dominates_point,
      GTree.point_dominates_iff.mpr ((bassSerreTree 𝔸 v₀).isEllipticSubgroup_of_subsingleton ⊤)⟩

/-- Over a graph without edges, there is no `𝔸`-path between distinct vertices. -/
theorem isEmpty_path_of_isEmpty_dart_of_ne [IsEmpty Γ.E] {v₁ v₂ : Γ.V} (h : v₁ ≠ v₂) :
    IsEmpty (𝔸.Path ⟨v₁⟩ ⟨v₂⟩) :=
  ⟨fun p => h (Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim p.edgePath)⟩

/-- Over the disconnected two-vertex edgeless graph `noEdge Bool`, there is no `𝔸`-path from
`false` to `true`, whereas `bassSerreTree 𝔸 v₀` and its quotient both have `1` vertex (isomorphic
to `(noEdge Bool).component v₀`, not to `noEdge Bool`). -/
theorem isEmpty_path_noEdge_bool_false_true (𝔸 : GraphOfGroups.{0, 0, w, x} (noEdge Bool)) :
    IsEmpty (𝔸.Path ⟨false⟩ ⟨true⟩) :=
  isEmpty_path_of_isEmpty_dart_of_ne 𝔸 Bool.false_ne_true

theorem natCard_bassSerreTree_V_of_isEmpty [IsEmpty Γ.E] :
    Nat.card (bassSerreTree 𝔸 v₀).V = 1 :=
  Nat.card_unique

theorem natCard_quotient_bassSerreTree_V_of_isEmpty [IsEmpty Γ.E] :
    Nat.card (bassSerreTree 𝔸 v₀).quotient.V = 1 := by
  have _ : Unique (bassSerreTree 𝔸 v₀).quotient.V :=
    (quotientBassSerreTreeIso 𝔸 v₀).equivV.unique
  exact Nat.card_unique

end Edgeless

/-! ### Comparison with uncollapsed homotopy classes of `𝔸`-paths -/

section UncollapsedPathQuotient

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ v : Γ.V)

/-- Left concatenation of `π₁(𝔸, v₀)` on the uncollapsed homotopy quotient
`Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩)` (without dividing out by `A_v` on the right). -/
def pathQuotientSmul :
    π₁ 𝔸 v₀ → Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) → Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) :=
  π₁.lift
    (fun s => Quotient.lift (fun p => Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) (s.comp p))
      fun _ _ hpq => Quotient.sound (hpq.comp_left s))
    fun _ _ hs => funext fun q => Quotient.inductionOn q fun p =>
      Quotient.sound (hs.comp_right p)

@[simp] theorem pathQuotientSmul_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    pathQuotientSmul 𝔸 v₀ v (π₁.mk s) (Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) p) =
      Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) (s.comp p) := by
  rw [pathQuotientSmul, π₁.lift_mk]
  rfl

@[simp] theorem pathQuotientSmul_one (q : Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩)) :
    pathQuotientSmul 𝔸 v₀ v 1 q = q :=
  Quotient.inductionOn q fun p => by
    rw [← π₁.mk_nil, pathQuotientSmul_mk, Quiver.Path.nil_comp]

@[simp] theorem pathQuotientSmul_mul (g₁ g₂ : π₁ 𝔸 v₀)
    (q : Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩)) :
    pathQuotientSmul 𝔸 v₀ v (g₁ * g₂) q =
      pathQuotientSmul 𝔸 v₀ v g₁ (pathQuotientSmul 𝔸 v₀ v g₂ q) :=
  π₁.induction_on g₁ fun s₁ => π₁.induction_on g₂ fun s₂ => Quotient.inductionOn q fun p => by
    rw [← π₁.mk_comp, pathQuotientSmul_mk, pathQuotientSmul_mk, pathQuotientSmul_mk,
      Quiver.Path.comp_assoc]

/-- Without the right `A_v`-coset quotient, `π₁(𝔸, v₀)` acts freely on homotopy classes of
`𝔸`-paths from `v₀` to `v`: `g` fixes `⟦p⟧` if and only if `g = 1`, rather than `g ∈ p A_v p⁻¹`. -/
@[simp] theorem pathQuotientSmul_eq_self_iff (g : π₁ 𝔸 v₀) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    pathQuotientSmul 𝔸 v₀ v g (Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) p) =
      Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) p ↔ g = 1 := by
  induction g using π₁.induction_on with | _ s =>
  rw [pathQuotientSmul_mk, Quotient.eq (r := Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩), Path.setoid_r, ← π₁.mk_nil,
    π₁.mk_eq_mk_iff]
  exact ⟨fun hs => Path.Homotopic.comp_right_iff.mp (by simpa only [Quiver.Path.nil_comp] using hs),
    fun hs => by simpa only [Quiver.Path.nil_comp] using hs.comp_right p⟩

/-- Without the right `A_{v₀}`-coset quotient, distinct elements of `A_{v₀}` give distinct classes
`⟦Path.ofVertex a⟧` in `Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩)`, whereas in `bassSerreTree 𝔸 v₀` they
all equal `bassSerreBase 𝔸 v₀`. -/
theorem pathQuotientOfVertex_injective :
    Function.Injective fun a : 𝔸.vertexGroup v₀ =>
      Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex a) := fun _ _ h =>
  Path.ofVertex_homotopic_ofVertex_iff.mp
    ((Path.setoid_r _ _).mp ((Quotient.eq (r := Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩)).mp h))

end UncollapsedPathQuotient

end TauCeti.GraphOfGroups
