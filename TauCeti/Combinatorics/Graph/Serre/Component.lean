/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso

/-!
# Connected components of Serre graphs

For a Serre graph `Γ` and a vertex `v₀`, the connected component `Γ.component v₀` is the subgraph on
the vertices reachable from `v₀` by a path of `Γ`, together with the darts between them. Because
every dart of a Serre graph has a reverse, a dart has one endpoint reachable from `v₀` if and only
if both of its endpoints are reachable from `v₀`; thus `Γ.component v₀` contains every dart of `Γ`
incident to any of its vertices.

The component `Γ.component v₀` is always connected, with base vertex `Γ.componentBase v₀`. When `Γ`
is preconnected, every vertex and dart of `Γ` belongs to `Γ.component v₀`, so the inclusion
`Γ.componentInclusion v₀` upgrades to an isomorphism `Γ.componentIsoOfPreconnected` onto `Γ`. On the
other hand, when every dart of `Γ` is a loop (in particular for a graph `noEdge V` without edges),
`Γ.component v₀` has `v₀` as its unique vertex even when `Γ` itself has other isolated components.

## Main definitions

* `TauCeti.SerreGraph.componentVertices`: the set of vertices reachable from `v₀`.
* `TauCeti.SerreGraph.component`: the connected component of `v₀` as a `SerreGraph`.
* `TauCeti.SerreGraph.componentBase`: `v₀` as a vertex of `Γ.component v₀`.
* `TauCeti.SerreGraph.componentInclusion`: the inclusion morphism `(Γ.component v₀).Hom Γ`.
* `TauCeti.SerreGraph.componentIsoOfPreconnected`: the isomorphism `(Γ.component v₀).Iso Γ` when `Γ`
  is preconnected.

## Main results

* `TauCeti.SerreGraph.component_connected`: `Γ.component v₀` is connected.
* `TauCeti.SerreGraph.mem_inducedDarts_componentVertices_iff`: a dart lies in `Γ.component v₀` if
  and only if its source is reachable from `v₀`.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1 and §5.3.
-/

public section

universe u v

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph.{u, v}) (v₀ : Γ.V)

/-- The vertices of `Γ` reachable by a path from `v₀`. -/
def componentVertices : Set Γ.V :=
  {v | Nonempty (Γ.Path v₀ v)}

variable {Γ v₀} in
@[simp] theorem mem_componentVertices_iff {v : Γ.V} :
    v ∈ Γ.componentVertices v₀ ↔ Nonempty (Γ.Path v₀ v) := Iff.rfl

theorem self_mem_componentVertices : v₀ ∈ Γ.componentVertices v₀ :=
  ⟨.nil⟩

variable {Γ v₀} in
/-- The target of a dart is reachable from `v₀` whenever its source is. -/
theorem tgt_mem_componentVertices_of_src_mem {e : Γ.E} (he : Γ.src e ∈ Γ.componentVertices v₀) :
    Γ.tgt e ∈ Γ.componentVertices v₀ :=
  let ⟨p⟩ := he
  ⟨p.cons (Γ.dart e)⟩

variable {Γ v₀} in
/-- The endpoints of a dart are reachable from `v₀` together. -/
theorem tgt_mem_componentVertices_iff {e : Γ.E} :
    Γ.tgt e ∈ Γ.componentVertices v₀ ↔ Γ.src e ∈ Γ.componentVertices v₀ :=
  ⟨fun he => by
    simpa only [tgt_rev] using
      tgt_mem_componentVertices_of_src_mem (e := Γ.rev e) (by simpa only [src_rev] using he),
    tgt_mem_componentVertices_of_src_mem⟩

variable {Γ v₀} in
/-- A dart has both endpoints in the component of `v₀` if and only if its source lies in it. -/
theorem mem_inducedDarts_componentVertices_iff {e : Γ.E} :
    e ∈ Γ.inducedDarts (Γ.componentVertices v₀) ↔ Γ.src e ∈ Γ.componentVertices v₀ :=
  mem_inducedDarts_iff.trans (and_iff_left_of_imp tgt_mem_componentVertices_of_src_mem)

/-- The connected component of a vertex `v₀` in a Serre graph `Γ`: the subgraph on the vertices
reachable from `v₀` and the darts between them. -/
abbrev component : SerreGraph.{u, v} :=
  Γ.subgraph (Γ.componentVertices v₀) (Γ.inducedDarts (Γ.componentVertices v₀))
    (fun _ he => (mem_inducedDarts_iff.mp he).1) (fun _ he => rev_mem_inducedDarts_iff.mpr he)

/-- The vertex `v₀` inside its connected component `Γ.component v₀`. The body is exposed so that
paths mapped by `componentInclusion` have the corresponding ambient endpoints. -/
@[expose] def componentBase : (Γ.component v₀).V :=
  ⟨v₀, Γ.self_mem_componentVertices v₀⟩

@[simp] theorem componentBase_val : (Γ.componentBase v₀).1 = v₀ := (rfl)

/-- The inclusion of `Γ.component v₀` into `Γ`. -/
abbrev componentInclusion : (Γ.component v₀).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

/-- Every path in `Γ` starting at `v₀` lifts to a path in `Γ.component v₀` from `componentBase v₀`
to its endpoint. -/
theorem component_reachable_of_path :
    ∀ {a : Γ.V} (p : Γ.Path v₀ a),
      Nonempty ((Γ.component v₀).Path (Γ.componentBase v₀) ⟨a, mem_componentVertices_iff.mpr ⟨p⟩⟩)
  | _, .nil => ⟨.nil⟩
  | _, .cons p e =>
    (component_reachable_of_path p).map fun q =>
      q.cons ⟨⟨e.1, mem_inducedDarts_componentVertices_iff.mpr
        (by rw [e.2.1]; exact mem_componentVertices_iff.mpr ⟨p⟩)⟩,
        Subtype.ext e.2.1, Subtype.ext e.2.2⟩

/-- Every vertex of `Γ.component v₀` is reachable from `componentBase v₀` within the component. -/
theorem component_reachable (a : (Γ.component v₀).V) :
    Nonempty ((Γ.component v₀).Path (Γ.componentBase v₀) a) := by
  obtain ⟨p⟩ := mem_componentVertices_iff.mp a.2
  exact component_reachable_of_path Γ v₀ p

/-- The connected component `Γ.component v₀` is connected. -/
theorem component_connected : (Γ.component v₀).Connected :=
  ((Γ.component v₀).connected_iff).mpr ⟨⟨Γ.componentBase v₀⟩,
    preconnected_of_forall_nonempty_path _ (Γ.componentBase v₀) (Γ.component_reachable v₀)⟩

variable {Γ v₀} in
/-- In a preconnected graph, every vertex lies in the component of `v₀`. -/
theorem Preconnected.mem_componentVertices (hΓ : Γ.Preconnected) (v : Γ.V) :
    v ∈ Γ.componentVertices v₀ :=
  mem_componentVertices_iff.mpr ((Γ.preconnected_iff.mp hΓ) v₀ v)

variable {Γ v₀} in
/-- When `Γ` is preconnected, the inclusion `Γ.component v₀ → Γ` is bijective on vertices. -/
theorem Preconnected.componentInclusion_mapV_bijective (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapV :=
  ⟨Γ.subgraphInclusion_mapV_injective _ _ _ _, fun v => ⟨⟨v, hΓ.mem_componentVertices v⟩, rfl⟩⟩

variable {Γ v₀} in
/-- When `Γ` is preconnected, the inclusion `Γ.component v₀ → Γ` is bijective on darts. -/
theorem Preconnected.componentInclusion_mapE_bijective (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapE :=
  ⟨Γ.subgraphInclusion_mapE_injective _ _ _ _, fun e =>
    ⟨⟨e, mem_inducedDarts_iff.mpr ⟨hΓ.mem_componentVertices _, hΓ.mem_componentVertices _⟩⟩, rfl⟩⟩

variable {Γ} in
/-- When `Γ` is preconnected, `Γ.component v₀` is isomorphic to `Γ` via the inclusion morphism. -/
noncomputable def componentIsoOfPreconnected (hΓ : Γ.Preconnected) (v₀ : Γ.V) :
    (Γ.component v₀).Iso Γ :=
  (Γ.componentInclusion v₀).toIso hΓ.componentInclusion_mapV_bijective
    hΓ.componentInclusion_mapE_bijective

@[simp] theorem componentIsoOfPreconnected_toHom {Γ : SerreGraph.{u, v}} (hΓ : Γ.Preconnected)
    (v₀ : Γ.V) : (componentIsoOfPreconnected hΓ v₀).toHom = Γ.componentInclusion v₀ :=
  Hom.toIso_toHom ..

@[simp] theorem componentIsoOfPreconnected_equivV_apply {Γ : SerreGraph.{u, v}}
    (hΓ : Γ.Preconnected) (v₀ : Γ.V) (a : (Γ.component v₀).V) :
    (componentIsoOfPreconnected hΓ v₀).equivV a = a.1 :=
  Hom.toIso_equivV_apply ..

@[simp] theorem componentIsoOfPreconnected_equivE_apply {Γ : SerreGraph.{u, v}}
    (hΓ : Γ.Preconnected) (v₀ : Γ.V) (e : (Γ.component v₀).E) :
    (componentIsoOfPreconnected hΓ v₀).equivE e = e.1 :=
  Hom.toIso_equivE_apply ..

/-- When all darts of `Γ` are loops, `v₀` is the unique vertex of `Γ.component v₀`. -/
theorem subsingleton_component_V_of_forall_src_eq_tgt (h : ∀ e, Γ.src e = Γ.tgt e) :
    Subsingleton (Γ.component v₀).V :=
  ⟨fun ⟨_, ha⟩ ⟨_, hb⟩ => by
    obtain ⟨p⟩ := mem_componentVertices_iff.mp ha
    obtain ⟨q⟩ := mem_componentVertices_iff.mp hb
    exact Subtype.ext
      ((Γ.eq_of_path_of_forall_src_eq_tgt h p).symm.trans
        (Γ.eq_of_path_of_forall_src_eq_tgt h q))⟩

/-- Over a graph without edges, every connected component has no darts. -/
instance [IsEmpty Γ.E] : IsEmpty (Γ.component v₀).E :=
  ⟨fun e => isEmptyElim e.1⟩

/-- Over a graph without edges, `v₀` is the unique vertex of `Γ.component v₀`. -/
instance [IsEmpty Γ.E] : Unique (Γ.component v₀).V where
  default := Γ.componentBase v₀
  uniq a := @Subsingleton.elim _
    (Γ.subsingleton_component_V_of_forall_src_eq_tgt v₀ isEmptyElim) a _

end TauCeti.SerreGraph
