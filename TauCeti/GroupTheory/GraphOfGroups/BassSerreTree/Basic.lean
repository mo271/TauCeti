/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Defs

/-!
# Stabilizers, quotient graph, and vertex stars of the Bass–Serre tree

This file establishes the structural properties of the Bass–Serre tree `X(𝔸, v₀)`
(`GraphOfGroups.bassSerreTree 𝔸 v₀`) of a graph of groups `𝔸` over a Serre graph `Γ`:

* **Stabilizers:** the stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` is `p A_v p⁻¹`, the range of
  `π₁.vertexHom p` (`GraphOfGroups.stabilizer_vertex`), canonically isomorphic to `A_v`
  (`GraphOfGroups.vertexStabilizerEquiv`). In particular every embedded vertex group
  `(π₁.vertexHom p).range` is elliptic in `X(𝔸, v₀)`
  (`GraphOfGroups.isEllipticSubgroup_range_vertexHom`). The stabilizer of the dart `(p, e)` is
  `p α_e(A_e) p⁻¹` (`GraphOfGroups.stabilizer_edge`), canonically isomorphic to `A_e`
  (`GraphOfGroups.edgeStabilizerEquiv`), and the dart `(p a₀, e)` from `p A_a` to `(p a₀ e) A_b`
  has stabilizer `p (a₀ α_e(A_e) a₀⁻¹) p⁻¹` (`GraphOfGroups.stabilizer_edge_cons_vertex`). When all
  vertex groups are trivial, `π₁(𝔸, v₀)` acts freely on vertices and darts.
* **Quotient graph:** the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is canonically isomorphic to the
  connected component `Γ.component v₀` of `v₀` in `Γ` (`GraphOfGroups.quotientBassSerreTreeIso`),
  and to `Γ` itself when `Γ` is preconnected
  (`GraphOfGroups.quotientBassSerreTreeIsoOfPreconnected`).
* **Stars of vertices:** the outgoing darts from `p A_v` (or from any vertex `x`) decompose over the
  outgoing darts `e` of `Γ` from `v` as the disjoint union of the left coset spaces
  `A_v ⧸ (𝔸.α e).range` (`GraphOfGroups.bassSerreTree.starEquiv`,
  `GraphOfGroups.bassSerreTree.starEquivVertex`), and the target map identifies those outgoing darts
  bijectively with the neighbours of `x` (`GraphOfGroups.bassSerreTree.neighbourEquiv`).

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

variable {Γ : SerreGraph.{u, v}}

/-! ### Vertex and edge stabilizers -/

section Stabilizers

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- A closed path `s` at `v₀` multiplies `p` on the left into the homotopy class of `p g` if and
only if `[s] = π₁.vertexHom p g`. -/
private theorem comp_homotopic_cons_vertex_iff {v : Γ.V} (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v) :
    Path.Homotopic (s.comp p) (p.cons (Letter.vertex g)) ↔ π₁.mk s = π₁.vertexHom p g := by
  rw [π₁.vertexHom_apply, π₁.mk_eq_mk_iff, Path.comp_ofVertex]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (Path.Homotopic.comp_comp_reverse s p).symm.trans (h.comp_right p.reverse)
  · refine (h.comp_right p).trans ?_
    rw [Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.comp_nil] using (Path.Homotopic.reverse_comp p).comp_left _

/-- The stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` of the Bass–Serre tree is `p A_v p⁻¹`,
the range of `π₁.vertexHom p`. -/
@[simp] theorem stabilizer_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.mkVertex p) =
      (π₁.vertexHom p).range := by
  ext x
  induction x using π₁.induction_on with | _ s =>
  rw [MulAction.mem_stabilizer_iff, bassSerreTree.mk_smul_mkVertex,
    bassSerreTree.mkVertex_eq_mkVertex_iff, MonoidHom.mem_range]
  exact exists_congr fun g => (comp_homotopic_cons_vertex_iff s p g).trans eq_comm

/-- The stabilizer of the base vertex `1 · A_{v₀}` is the embedded base vertex group
`(π₁.vertexHom .nil).range`. -/
@[simp] theorem stabilizer_baseVertex :
    MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.baseVertex 𝔸 v₀) =
      (π₁.vertexHom (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range := by
  rw [bassSerreTree.baseVertex_def, stabilizer_vertex]

/-- Every conjugated vertex group `(π₁.vertexHom p).range` is elliptic in `bassSerreTree 𝔸 v₀`. -/
@[simp] theorem isEllipticSubgroup_range_vertexHom {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreTree 𝔸 v₀).IsEllipticSubgroup (π₁.vertexHom p).range := by
  rw [← stabilizer_vertex]
  exact (bassSerreTree 𝔸 v₀).isEllipticSubgroup_stabilizer (bassSerreTree.mkVertex p)

/-- The canonical isomorphism between the vertex group `A_v` and the stabilizer of `p A_v` in
`π₁(𝔸, v₀)`, sending `g` to `π₁.vertexHom p g`. -/
noncomputable def vertexStabilizerEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.vertexGroup v ≃* MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.mkVertex p) :=
  (MonoidHom.ofInjective (f := π₁.vertexHom p) (π₁.vertexHom_injective p)).trans
    (MulEquiv.subgroupCongr (stabilizer_vertex p).symm)

@[simp] theorem coe_vertexStabilizerEquiv_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (g : 𝔸.vertexGroup v) :
    (vertexStabilizerEquiv p g : π₁ 𝔸 v₀) = π₁.vertexHom p g := by
  simp [vertexStabilizerEquiv, MonoidHom.ofInjective_apply]

/-- The stabilizer in `π₁(𝔸, v₀)` of the dart `(p, e)` of the Bass–Serre tree is `p α_e(A_e) p⁻¹`,
the range of `(π₁.vertexHom p).comp (𝔸.αArrow e)`. -/
@[simp] theorem stabilizer_edge {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.mkDart p e) =
      ((π₁.vertexHom p).comp (𝔸.αArrow e)).range := by
  ext x
  induction x using π₁.induction_on with | _ s =>
  rw [MulAction.mem_stabilizer_iff, bassSerreTree.mk_smul_mkDart,
    bassSerreTree.mkDart_eq_mkDart_iff, MonoidHom.mem_range]
  exact exists_congr fun c => (comp_homotopic_cons_vertex_iff s p (𝔸.αArrow e c)).trans eq_comm

/-- For `a₀ ∈ A_a` and `e : a ⟶ b`, the dart from `p A_a` to `(p a₀ e) A_b` has stabilizer
`p (a₀ α_e(A_e) a₀⁻¹) p⁻¹`. -/
theorem stabilizer_edge_cons_vertex {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (a₀ : 𝔸.vertexGroup a) (e : a ⟶ b) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.mkDart (p.cons (Letter.vertex a₀)) e) =
      ((𝔸.αArrow e).range.map (MulAut.conj a₀).toMonoidHom).map (π₁.vertexHom p) := by
  rw [stabilizer_edge, MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map,
    Subgroup.map_map]
  refine congrArg (Subgroup.map · (⊤ : Subgroup (𝔸.edgeGroup (Γ.toGeomEdge e.1))))
    (MonoidHom.ext fun c => ?_)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [π₁.vertexHom_eq_conj_comp_apply p (p.cons (.vertex a₀)), ← Path.comp_ofVertex,
    ← π₁.vertexHom_apply, ← map_inv, ← map_mul, ← map_mul]

/-- The canonical isomorphism between the edge group `A_e` and the stabilizer of `(p, e)` in
`π₁(𝔸, v₀)`, sending `c` to `π₁.vertexHom p (𝔸.αArrow e c)`. -/
noncomputable def edgeStabilizerEquiv {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    𝔸.edgeGroup (Γ.toGeomEdge e.1) ≃*
      MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.mkDart p e) :=
  (MonoidHom.ofInjective (f := (π₁.vertexHom p).comp (𝔸.αArrow e))
    ((π₁.vertexHom_injective p).comp (𝔸.αArrow_injective e))).trans
    (MulEquiv.subgroupCongr (stabilizer_edge p e).symm)

@[simp] theorem coe_edgeStabilizerEquiv_apply {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (e : a ⟶ b) (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    (edgeStabilizerEquiv p e c : π₁ 𝔸 v₀) = π₁.vertexHom p (𝔸.αArrow e c) := by
  simp [edgeStabilizerEquiv, MonoidHom.ofInjective_apply]

/-- When all vertex groups are trivial, `π₁(𝔸, v₀)` acts freely on the vertices of
`bassSerreTree 𝔸 v₀`. -/
theorem stabilizer_vertex_eq_bot_of_subsingleton [∀ v, Subsingleton (𝔸.vertexGroup v)]
    (x : (bassSerreTree 𝔸 v₀).V) :
    MulAction.stabilizer (π₁ 𝔸 v₀) x = ⊥ := by
  induction x using bassSerreTree.vertex_induction_on with | _ p =>
  rw [stabilizer_vertex, eq_bot_iff]
  rintro _ ⟨g, rfl⟩
  rw [Subsingleton.elim g 1, map_one]
  exact Subgroup.one_mem ⊥

/-- When all vertex groups are trivial, `π₁(𝔸, v₀)` acts freely on the darts of
`bassSerreTree 𝔸 v₀`. -/
theorem stabilizer_dart_eq_bot_of_subsingleton [∀ v, Subsingleton (𝔸.vertexGroup v)]
    (d : (bassSerreTree 𝔸 v₀).E) :
    MulAction.stabilizer (π₁ 𝔸 v₀) d = ⊥ := by
  induction d using bassSerreTree.dart_induction_on with | _ p e =>
  rw [stabilizer_edge, eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  simp [Subsingleton.elim (𝔸.αArrow e c) 1]

end Stabilizers

/-! ### The quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` -/

section Quotient

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

namespace bassSerreTree

/-- Every vertex of `bassSerreTree 𝔸 v₀` projects into the connected component
`Γ.componentVertices v₀` of the base vertex. -/
theorem toGraphVertex_mem_componentVertices (x : (bassSerreTree 𝔸 v₀).V) :
    toGraphVertex x ∈ Γ.componentVertices v₀ := by
  induction x using vertex_induction_on with | _ p =>
  rw [toGraphVertex_mkVertex]
  exact Γ.mem_componentVertices_iff.mpr ⟨p.edgePath⟩

/-- Every dart of `bassSerreTree 𝔸 v₀` projects into `Γ.componentDarts v₀`. -/
theorem toGraphDart_mem_componentDarts (d : (bassSerreTree 𝔸 v₀).E) :
    toGraphDart d ∈ Γ.componentDarts v₀ := by
  rw [Γ.mem_componentDarts_iff, ← toGraphVertex_src]
  exact toGraphVertex_mem_componentVertices 𝔸 v₀ _

/-- The projection of `bassSerreTree 𝔸 v₀` onto the connected component `Γ.component v₀`. -/
def toComponentHom : (bassSerreTree 𝔸 v₀).toSerreGraph.Hom (Γ.component v₀) where
  mapV x := ⟨toGraphVertex x, toGraphVertex_mem_componentVertices 𝔸 v₀ x⟩
  mapE d := ⟨toGraphDart d, toGraphDart_mem_componentDarts 𝔸 v₀ d⟩
  map_src d := Subtype.ext (toGraphVertex_src d).symm
  map_rev d := Subtype.ext (toGraphDart_rev d)

@[simp] theorem toComponentHom_mapV_val (x : (bassSerreTree 𝔸 v₀).V) :
    ((toComponentHom 𝔸 v₀).mapV x).1 = toGraphVertex x :=
  (rfl)

@[simp] theorem toComponentHom_mapE_val (d : (bassSerreTree 𝔸 v₀).E) :
    ((toComponentHom 𝔸 v₀).mapE d).1 = toGraphDart d :=
  (rfl)

/-- The morphism from `(bassSerreTree 𝔸 v₀).quotient` to `Γ.component v₀` induced by
`toComponentHom`. -/
def quotientToComponentHom : (bassSerreTree 𝔸 v₀).quotient.Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (bassSerreTree 𝔸 v₀).smul_ne_rev (toComponentHom 𝔸 v₀) fun g => by
    ext x
    · refine Subtype.ext ?_
      simp [← SerreGraph.Aut.smul_vertex_def, ← GTree.smul_vertex_def]
    · refine Subtype.ext ?_
      simp [← SerreGraph.Aut.smul_dart_def, ← GTree.smul_dart_def]

@[simp] theorem quotientToComponentHom_mapV_quotientMap (x : (bassSerreTree 𝔸 v₀).V) :
    (quotientToComponentHom 𝔸 v₀).mapV ((bassSerreTree 𝔸 v₀).quotientMap.mapV x) =
      (toComponentHom 𝔸 v₀).mapV x := by
  simp [quotientToComponentHom]

@[simp] theorem quotientToComponentHom_mapE_quotientMap (d : (bassSerreTree 𝔸 v₀).E) :
    (quotientToComponentHom 𝔸 v₀).mapE ((bassSerreTree 𝔸 v₀).quotientMap.mapE d) =
      (toComponentHom 𝔸 v₀).mapE d := by
  simp [quotientToComponentHom]

private theorem quotientToComponentHom_mapV_bijective :
    Function.Bijective (quotientToComponentHom 𝔸 v₀).mapV := by
  refine ⟨fun q₁ q₂ h => ?_, fun ⟨v, hv⟩ => ?_⟩
  · obtain ⟨x₁, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective q₁
    obtain ⟨x₂, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective q₂
    induction x₁ using vertex_induction_on with | @h v₁ p₁ =>
    induction x₂ using vertex_induction_on with | @h v₂ p₂ =>
    have hv : v₁ = v₂ := by simpa using congrArg Subtype.val h
    subst hv
    have hkey := Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil
    rw [Quiver.Path.comp_nil] at hkey
    refine (bassSerreTree 𝔸 v₀).quotientMap_mapV_eq_iff.mpr
      ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [mk_smul_mkVertex]
    exact mkVertex_congr hkey
  · obtain ⟨pΓ⟩ := Γ.mem_componentVertices_iff.mp hv
    exact ⟨(bassSerreTree 𝔸 v₀).quotientMap.mapV
      (mkVertex ((dartPrefunctor 𝔸).mapPath pΓ)), Subtype.ext (by simp)⟩

private theorem quotientToComponentHom_mapE_bijective :
    Function.Bijective (quotientToComponentHom 𝔸 v₀).mapE := by
  refine ⟨fun q₁ q₂ h => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨d₁, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapE_surjective q₁
    obtain ⟨d₂, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapE_surjective q₂
    induction d₁ using dart_induction_on with | _ p₁ e₁ =>
    induction d₂ using dart_induction_on with | _ p₂ e₂ =>
    obtain ⟨e₁, rfl, rfl⟩ := e₁
    obtain ⟨e₂, rfl, rfl⟩ := e₂
    have he : e₁ = e₂ := by simpa using congrArg Subtype.val h
    subst he
    have hkey := Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil
    rw [Quiver.Path.comp_nil] at hkey
    refine (bassSerreTree 𝔸 v₀).quotientMap_mapE_eq_iff.mpr
      ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [mk_smul_mkDart]
    exact mkDart_congr hkey _
  · obtain ⟨pΓ⟩ := Γ.mem_componentVertices_iff.mp (Γ.mem_componentDarts_iff.mp he)
    refine ⟨(bassSerreTree 𝔸 v₀).quotientMap.mapE
      (mkDart ((dartPrefunctor 𝔸).mapPath pΓ) (Γ.dart e)), ?_⟩
    exact Subtype.ext (by simp)

end bassSerreTree

/-- The canonical isomorphism between the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` of the Bass–Serre
tree and the connected component of `v₀` in `Γ`. -/
noncomputable def quotientBassSerreTreeIso :
    (bassSerreTree 𝔸 v₀).quotient.Iso (Γ.component v₀) :=
  (bassSerreTree.quotientToComponentHom 𝔸 v₀).toIso
    (bassSerreTree.quotientToComponentHom_mapV_bijective 𝔸 v₀)
    (bassSerreTree.quotientToComponentHom_mapE_bijective 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeIso_equivV_quotientMap (x : (bassSerreTree 𝔸 v₀).V) :
    ((quotientBassSerreTreeIso 𝔸 v₀).equivV ((bassSerreTree 𝔸 v₀).quotientMap.mapV x)).1 =
      bassSerreTree.toGraphVertex x := by
  rw [quotientBassSerreTreeIso, SerreGraph.Hom.toIso_equivV_apply,
    bassSerreTree.quotientToComponentHom_mapV_quotientMap, bassSerreTree.toComponentHom_mapV_val]

@[simp] theorem quotientBassSerreTreeIso_equivE_quotientMap (d : (bassSerreTree 𝔸 v₀).E) :
    ((quotientBassSerreTreeIso 𝔸 v₀).equivE ((bassSerreTree 𝔸 v₀).quotientMap.mapE d)).1 =
      bassSerreTree.toGraphDart d := by
  rw [quotientBassSerreTreeIso, SerreGraph.Hom.toIso_equivE_apply,
    bassSerreTree.quotientToComponentHom_mapE_quotientMap, bassSerreTree.toComponentHom_mapE_val]

/-- When the underlying graph `Γ` is preconnected, the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is
canonically isomorphic to `Γ` itself. -/
noncomputable def quotientBassSerreTreeIsoOfPreconnected (hΓ : Γ.Preconnected) :
    (bassSerreTree 𝔸 v₀).quotient.Iso Γ :=
  (quotientBassSerreTreeIso 𝔸 v₀).trans (Γ.componentIsoOfPreconnected v₀ hΓ)

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivV_quotientMap (hΓ : Γ.Preconnected)
    (x : (bassSerreTree 𝔸 v₀).V) :
    (quotientBassSerreTreeIsoOfPreconnected 𝔸 v₀ hΓ).equivV
      ((bassSerreTree 𝔸 v₀).quotientMap.mapV x) = bassSerreTree.toGraphVertex x := by
  simp [quotientBassSerreTreeIsoOfPreconnected]

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivE_quotientMap (hΓ : Γ.Preconnected)
    (d : (bassSerreTree 𝔸 v₀).E) :
    (quotientBassSerreTreeIsoOfPreconnected 𝔸 v₀ hΓ).equivE
      ((bassSerreTree 𝔸 v₀).quotientMap.mapE d) = bassSerreTree.toGraphDart d := by
  simp [quotientBassSerreTreeIsoOfPreconnected]

end Quotient

/-! ### Stars of vertices and coset decompositions -/

section Star

namespace bassSerreTree

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

private def outDartFibreFun {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (𝔸.vertexGroup a ⧸ (𝔸.αArrow e).range) →
      {d : (bassSerreTree 𝔸 v₀).E //
        (bassSerreTree 𝔸 v₀).src d = mkVertex p ∧ toGraphDart d = e.1} :=
  Quotient.lift
    (fun g => ⟨mkDart (p.cons (Letter.vertex g)) e,
      (src_mkDart _ e).trans (mkVertex_cons_vertex p g), toGraphDart_mkDart _ e⟩)
    fun g₁ g₂ h => by
      obtain ⟨c, hc⟩ : g₁⁻¹ * g₂ ∈ (𝔸.αArrow e).range := QuotientGroup.leftRel_apply.mp h
      have hg₂ : g₂ = g₁ * 𝔸.αArrow e c := eq_mul_of_inv_mul_eq hc.symm
      subst hg₂
      exact Subtype.ext (mkDart_eq_mkDart_iff.mpr ⟨c, (Path.Homotopic.mul p g₁ _).symm⟩).symm

private theorem outDartFibreFun_bijective {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    Function.Bijective (outDartFibreFun p e) := by
  refine ⟨?_, ?_⟩
  · intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with | _ g₁ =>
    induction q₂ using QuotientGroup.induction_on with | _ g₂ =>
    obtain ⟨c, hc⟩ := mkDart_eq_mkDart_iff.mp (Subtype.mk.inj h)
    have hmul :
        Path.Homotopic (p.comp (Path.ofVertex g₁))
          (p.comp (Path.ofVertex (g₂ * 𝔸.αArrow e c))) := by
      simpa only [Path.comp_ofVertex] using hc.trans (Path.Homotopic.mul p g₂ (𝔸.αArrow e c))
    have hg : g₁ = g₂ * 𝔸.αArrow e c := π₁.vertexHom_injective p <| by
      rw [π₁.vertexHom_apply, π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
      exact hmul.comp_right p.reverse
    refine QuotientGroup.eq.mpr ⟨c⁻¹, ?_⟩
    rw [map_inv, hg, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨d, hsrc, he⟩
    induction d using dart_induction_on with | _ q e' =>
    obtain ⟨d₀, rfl, rfl⟩ := e'
    obtain ⟨d₁, rfl, rfl⟩ := e
    rw [toGraphDart_mkDart] at he
    subst he
    rw [src_mkDart] at hsrc
    obtain ⟨g, hg⟩ := mkVertex_eq_mkVertex_iff.mp hsrc
    exact ⟨QuotientGroup.mk g, Subtype.ext (mkDart_congr hg.symm _)⟩

/-- For a vertex `p A_a` of `bassSerreTree 𝔸 v₀` and an outgoing arrow `e : a ⟶ b` of `Γ`, the
outgoing darts of `bassSerreTree 𝔸 v₀` from `p A_a` over `e` correspond bijectively to the left
cosets `A_a ⧸ α_e(A_e)` via `g α_e(A_e) ↦ (p g, e)`. -/
noncomputable def outDartFibreEquiv {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (𝔸.vertexGroup a ⧸ (𝔸.αArrow e).range) ≃
      {d : (bassSerreTree 𝔸 v₀).E //
        (bassSerreTree 𝔸 v₀).src d = mkVertex p ∧ toGraphDart d = e.1} :=
  Equiv.ofBijective (outDartFibreFun p e) (outDartFibreFun_bijective p e)

@[simp] theorem outDartFibreEquiv_mk_val {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (e : a ⟶ b) (g : 𝔸.vertexGroup a) :
    (outDartFibreEquiv p e (QuotientGroup.mk g)).1 = mkDart (p.cons (Letter.vertex g)) e := by
  rw [outDartFibreEquiv, Equiv.ofBijective_apply]
  rfl

private noncomputable def outDartFibreEquivOfSrcEq {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    {e₀ : Γ.E} (he : Γ.src e₀ = v) :
    (𝔸.vertexGroup (Γ.src e₀) ⧸ (𝔸.α e₀).range) ≃
      {d : (bassSerreTree 𝔸 v₀).E //
        (bassSerreTree 𝔸 v₀).src d = mkVertex p ∧ toGraphDart d = e₀} := by
  cases he
  exact (Subgroup.quotientEquivOfEq (𝔸.range_αArrow_dart e₀).symm).trans
    ((outDartFibreEquiv p (Γ.dart e₀)).trans
      (Equiv.subtypeEquivRight fun d => by rw [Γ.dart_val]))

/-- The outgoing darts of `bassSerreTree 𝔸 v₀` from `p A_v` decompose over the outgoing darts
`e` of `Γ` from `v` as the disjoint union of the coset spaces `A_v ⧸ α_e(A_e)`. -/
noncomputable def starEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range) ≃
      {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = mkVertex p} :=
  let proj : {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = mkVertex p} →
      {e : Γ.E // Γ.src e = v} :=
    fun d => ⟨toGraphDart d.1, by rw [← toGraphVertex_src, d.2, toGraphVertex_mkVertex]⟩
  (Equiv.sigmaCongrRight fun e =>
    (outDartFibreEquivOfSrcEq p e.2).trans
      { toFun := fun ⟨d, hsrc, hd⟩ => ⟨⟨d, hsrc⟩, Subtype.ext hd⟩
        invFun := fun ⟨⟨d, hsrc⟩, hd⟩ => ⟨d, hsrc, congrArg Subtype.val hd⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans
    (Equiv.sigmaFiberEquiv proj)

@[simp] theorem starEquiv_mk_val {e₀ : Γ.E} (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₀⟩)
    (g : 𝔸.vertexGroup (Γ.src e₀)) :
    (starEquiv p ⟨⟨e₀, rfl⟩, QuotientGroup.mk g⟩).1 =
      mkDart (p.cons (Letter.vertex g)) (Γ.dart e₀) := by
  simp [starEquiv, outDartFibreEquivOfSrcEq, Subgroup.quotientEquivOfEq_mk]

/-- For any vertex `x` of `bassSerreTree 𝔸 v₀`, its outgoing darts are in bijection with
`Σ e : {e : Γ.E // Γ.src e = toGraphVertex x}, A_{src e} ⧸ α_e(A_e)`. -/
noncomputable def starEquivVertex (x : (bassSerreTree 𝔸 v₀).V) :
    (Σ e : {e : Γ.E // Γ.src e = toGraphVertex x},
      𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range) ≃
      {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = x} :=
  let h := exists_mkVertex x
  (starEquiv h.choose).trans
    (Equiv.subtypeEquivRight fun d => by rw [h.choose_spec])

/-- For any vertex `x` of `bassSerreTree 𝔸 v₀`, the target map identifies its outgoing darts
bijectively with its neighbours in the tree. -/
noncomputable def neighbourEquiv (x : (bassSerreTree 𝔸 v₀).V) :
    {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = x} ≃
      {y : (bassSerreTree 𝔸 v₀).V //
        ∃ d : (bassSerreTree 𝔸 v₀).E,
          (bassSerreTree 𝔸 v₀).src d = x ∧ (bassSerreTree 𝔸 v₀).tgt d = y} :=
  (bassSerreTree 𝔸 v₀).isAcyclic.outDartEquivNeighbour x

@[simp] theorem neighbourEquiv_apply_val (x : (bassSerreTree 𝔸 v₀).V)
    (d : {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = x}) :
    (neighbourEquiv x d).1 = (bassSerreTree 𝔸 v₀).tgt d.1 :=
  (bassSerreTree 𝔸 v₀).isAcyclic.outDartEquivNeighbour_apply_val x d

end bassSerreTree

end Star

end TauCeti.GraphOfGroups
