/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso
public import TauCeti.Combinatorics.Graph.Serre.Path.Basic

/-!
# Connected components of Serre graphs

The connected component `Γ.component v` of a vertex `v` in a Serre graph `Γ` is the subgraph
induced on the vertices reachable from `v` by a path of `Γ`. Because darts can be traversed in
both directions, a dart has both endpoints in the component as soon as its source lies in the
component. Every path of `Γ` starting in the component lifts to `Γ.component v`, so
`Γ.component v` is connected. When `Γ` is preconnected, the inclusion `Γ.componentInclusion v`
is bijective on vertices and on darts and upgrades to an isomorphism
`Γ.componentIsoOfPreconnected v`.

## Main declarations

* `TauCeti.SerreGraph.componentVertices`, `TauCeti.SerreGraph.componentDarts`: the vertices and
  darts of the connected component of a vertex.
* `TauCeti.SerreGraph.component`, `TauCeti.SerreGraph.componentBase`,
  `TauCeti.SerreGraph.componentInclusion`: the connected component subgraph, its base vertex, and
  its inclusion into `Γ`.
* `TauCeti.SerreGraph.component_connected`: `Γ.component v` is connected.
* `TauCeti.SerreGraph.componentIsoOfPreconnected`: `(Γ.component v).Iso Γ` when `Γ` is
  preconnected.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

universe u v

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph.{u, v}) (v : Γ.V)

/-- The vertices of the connected component of `v`: those reachable from `v` by a path of `Γ`. -/
def componentVertices : Set Γ.V :=
  {a | Nonempty (Γ.Path v a)}

variable {Γ v} in
@[simp] theorem mem_componentVertices_iff {a : Γ.V} :
    a ∈ Γ.componentVertices v ↔ Nonempty (Γ.Path v a) :=
  Iff.rfl

/-- Every vertex belongs to its own connected component. -/
theorem self_mem_componentVertices : v ∈ Γ.componentVertices v :=
  ⟨.nil⟩

variable {Γ v} in
/-- The target of a dart lies in the component of `v` if and only if its source does. -/
theorem tgt_mem_componentVertices_iff {e : Γ.E} :
    Γ.tgt e ∈ Γ.componentVertices v ↔ Γ.src e ∈ Γ.componentVertices v :=
  ⟨fun ⟨p⟩ => ⟨p.cons (Quiver.reverse (Γ.dart e))⟩, fun ⟨p⟩ => ⟨p.cons (Γ.dart e)⟩⟩

/-- The darts of the connected component of `v`: the darts induced on `Γ.componentVertices v`. -/
def componentDarts : Set Γ.E :=
  Γ.inducedDarts (Γ.componentVertices v)

variable {Γ v} in
@[simp] theorem mem_componentDarts_iff {e : Γ.E} :
    e ∈ Γ.componentDarts v ↔ Γ.src e ∈ Γ.componentVertices v := by
  rw [componentDarts, mem_inducedDarts_iff, tgt_mem_componentVertices_iff, and_self]

variable {Γ v} in
theorem src_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.src e ∈ Γ.componentVertices v :=
  mem_componentDarts_iff.mp he

variable {Γ v} in
theorem tgt_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.tgt e ∈ Γ.componentVertices v :=
  tgt_mem_componentVertices_iff.mpr (mem_componentDarts_iff.mp he)

variable {Γ v} in
theorem rev_mem_componentDarts_iff {e : Γ.E} :
    Γ.rev e ∈ Γ.componentDarts v ↔ e ∈ Γ.componentDarts v :=
  rev_mem_inducedDarts_iff

/-- The connected component of `v` in `Γ`, as a Serre subgraph. -/
abbrev component : SerreGraph.{u, v} :=
  Γ.subgraph (Γ.componentVertices v) (Γ.componentDarts v)
    (fun _ => src_mem_componentVertices) (fun _ => rev_mem_componentDarts_iff.mpr)

/-- The base vertex `v` inside its connected component `Γ.component v`. -/
def componentBase : (Γ.component v).V :=
  ⟨v, Γ.self_mem_componentVertices v⟩

@[simp] theorem componentBase_val : (Γ.componentBase v).1 = v :=
  (rfl)

/-- The inclusion of the connected component of `v` into `Γ`. -/
abbrev componentInclusion : (Γ.component v).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

/-- The endpoint of a path starting in `Γ.componentVertices v` also lies in
`Γ.componentVertices v`. -/
theorem mem_componentVertices_of_path {a b : Γ.V} (ha : a ∈ Γ.componentVertices v)
    (p : Γ.Path a b) : b ∈ Γ.componentVertices v := by
  obtain ⟨p₀⟩ := mem_componentVertices_iff.mp ha
  exact mem_componentVertices_iff.mpr ⟨p₀.comp p⟩

/-- Every dart traversed by a path starting in `Γ.componentVertices v` lies in
`Γ.componentDarts v`. -/
theorem mem_componentDarts_of_mem_darts {a b : Γ.V} (ha : a ∈ Γ.componentVertices v)
    (p : Γ.Path a b) {e : Γ.E} (he : e ∈ Path.darts Γ p) : e ∈ Γ.componentDarts v := by
  obtain ⟨p₀⟩ := mem_componentVertices_iff.mp ha
  obtain ⟨q, _, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  exact mem_componentDarts_iff.mpr (mem_componentVertices_iff.mpr ⟨p₀.comp q⟩)

/-- Every path of `Γ` starting in the component of `v` lifts to `Γ.component v`. -/
theorem exists_component_path {a b : Γ.V} (ha : a ∈ Γ.componentVertices v) (p : Γ.Path a b) :
    ∃ q : (Γ.component v).Path ⟨a, ha⟩ ⟨b, Γ.mem_componentVertices_of_path v ha p⟩,
      (Γ.componentInclusion v).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path _ _ _ _ p (fun _ he => Γ.mem_componentDarts_of_mem_darts v ha p he) ha _

/-- Every vertex of `Γ.component v` is reachable from `Γ.componentBase v` within the component. -/
theorem component_reachable (a : (Γ.component v).V) :
    Nonempty ((Γ.component v).Path (Γ.componentBase v) a) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨p⟩ := mem_componentVertices_iff.mp ha
  exact ⟨(Γ.exists_component_path v (Γ.self_mem_componentVertices v) p).choose⟩

/-- The connected component `Γ.component v` is a connected Serre graph. -/
theorem component_connected : (Γ.component v).Connected :=
  (Γ.component v).connected_iff.mpr
    ⟨⟨Γ.componentBase v⟩,
      (Γ.component v).preconnected_iff.mpr fun a b =>
        ⟨(Γ.component_reachable v a).some.reverse.comp (Γ.component_reachable v b).some⟩⟩

/-- When `Γ` is preconnected, the inclusion of `Γ.component v` into `Γ` is an isomorphism. -/
noncomputable def componentIsoOfPreconnected (hΓ : Γ.Preconnected) : (Γ.component v).Iso Γ :=
  (Γ.componentInclusion v).toIso
    ⟨Subtype.val_injective, fun a =>
      ⟨⟨a, mem_componentVertices_iff.mpr (Γ.preconnected_iff.mp hΓ v a)⟩, rfl⟩⟩
    ⟨Subtype.val_injective, fun e =>
      ⟨⟨e, mem_componentDarts_iff.mpr
        (mem_componentVertices_iff.mpr (Γ.preconnected_iff.mp hΓ v (Γ.src e)))⟩, rfl⟩⟩

@[simp] theorem componentIsoOfPreconnected_equivV_apply (hΓ : Γ.Preconnected)
    (a : (Γ.component v).V) : (Γ.componentIsoOfPreconnected v hΓ).equivV a = a.1 :=
  Hom.toIso_equivV_apply ..

@[simp] theorem componentIsoOfPreconnected_equivE_apply (hΓ : Γ.Preconnected)
    (e : (Γ.component v).E) : (Γ.componentIsoOfPreconnected v hΓ).equivE e = e.1 :=
  Hom.toIso_equivE_apply ..

@[simp] theorem componentIsoOfPreconnected_equivV_symm_apply (hΓ : Γ.Preconnected) (a : Γ.V) :
    ((Γ.componentIsoOfPreconnected v hΓ).equivV.symm a).1 = a := by
  simpa only [componentIsoOfPreconnected_equivV_apply] using
    (Γ.componentIsoOfPreconnected v hΓ).equivV.apply_symm_apply a

@[simp] theorem componentIsoOfPreconnected_equivE_symm_apply (hΓ : Γ.Preconnected) (e : Γ.E) :
    ((Γ.componentIsoOfPreconnected v hΓ).equivE.symm e).1 = e := by
  simpa only [componentIsoOfPreconnected_equivE_apply] using
    (Γ.componentIsoOfPreconnected v hΓ).equivE.apply_symm_apply e

/-- In a graph without edges, the connected component of any vertex has a single vertex. -/
instance instUniqueNoEdgeComponent {V : Type u} (v : V) :
    Unique (((noEdge.{u, v} V).component v).V) where
  default := (noEdge.{u, v} V).componentBase v
  uniq a := Subtype.ext <| by
    rw [componentBase_val]
    exact (noEdge_nonempty_path_iff.mp (mem_componentVertices_iff.mp a.2)).symm

end TauCeti.SerreGraph
