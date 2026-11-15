/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Special cases and concrete examples of Bass–Serre trees

This file computes the Bass–Serre tree `X(𝔸, v₀)` (`GraphOfGroups.bassSerreTree 𝔸 v₀`) in the
canonical low-complexity families of graphs of groups:

* **Graphs without edges and disconnected graphs:** when `Γ` has no darts (`[IsEmpty Γ.E]`), the
  Bass–Serre tree `X(𝔸, v₀)` has no darts and a unique vertex `baseVertex 𝔸 v₀` fixed by all of
  `π₁(𝔸, v₀)` (`GraphOfGroups.bassSerreTreePointIso`,
  `GraphOfGroups.bassSerreTree_sameDeformationSpace_point`). When `Γ` also has more than one vertex
  (for example two isolated vertices `noEdge Bool`), no `𝔸`-path reaches any vertex `v ≠ v₀`
  (`GraphOfGroups.isEmpty_path_of_isEmpty_of_ne`), and the single-vertex quotient
  `X(𝔸, v₀) / π₁(𝔸, v₀)` is not isomorphic to `Γ`
  (`GraphOfGroups.isEmpty_quotient_iso_of_isEmpty_of_nontrivial`).
* **Comparison with unquotiented path homotopy classes:** the canonical projection
  `bassSerreTree.ofPathQuotient` from based `𝔸`-path homotopy classes at `v` onto the fibre over
  `v` in `X(𝔸, v₀)` is injective if and only if `A_v` is trivial
  (`GraphOfGroups.bassSerreTree.ofPathQuotient_injective_iff`). Whenever `A_{v₀}` is nontrivial,
  `ofPathQuotient` is not injective at `v₀` (`GraphOfGroups.not_injective_ofPathQuotient`) and
  `baseVertex 𝔸 v₀` has nontrivial stabilizer (`GraphOfGroups.stabilizer_baseVertex_ne_bot`).
* **HNN loops and Baumslag–Solitar groups:** for `GraphOfGroups.loop f g hf hg`, every vertex of
  `X(𝔸, ())` has outgoing star `(G ⧸ f.range) ⊕ (G ⧸ g.range)` (`GraphOfGroups.loopStarEquiv`).
  For `BS(m, n)` (`m, n ≠ 0`), every vertex has valence `|m| + |n|`
  (`GraphOfGroups.baumslagSolitar_natCard_star`); in particular `X(BS(1, 2))` is a `3`-regular tree
  with dart-stabilizer indices `1` and `2`
  (`GraphOfGroups.baumslagSolitar_one_two_natCard_star`).
* **Segments and free products:** for `GraphOfGroups.segment f g hf hg`, a vertex over `false` has
  outgoing star `A ⧸ f.range` (`GraphOfGroups.segmentStarFalseEquiv`) and a vertex over `true` has
  outgoing star `B ⧸ g.range` (`GraphOfGroups.segmentStarTrueEquiv`). When the edge group is
  trivial, the neighbours of `baseVertex` are parameterized by `A` via
  `a ↦ π₁.mk (Path.ofVertex a) • mkVertex (Path.ofDart ⟨false, rfl, rfl⟩)`
  (`GraphOfGroups.segmentBaseNeighbourEquiv`), and for `ℤ ∗ ℤ` every vertex is countably
  infinite-valent (`GraphOfGroups.freeProductZ2_cardinalMk_star`) with base-vertex neighbours
  `k ↦ a ^ k • ⟨b⟩` (`GraphOfGroups.freeProductZ2BaseNeighbourEquiv`).

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1 and §5.3.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

/-! ### Graphs without edges and disconnected graphs -/

section NoEdges

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) [IsEmpty Γ.E]

/-- When `Γ` has no darts, its Bass–Serre tree has no darts. -/
instance bassSerreTree.isEmpty_dart_of_isEmpty : IsEmpty (bassSerreTree 𝔸 v₀).E :=
  ⟨fun d => isEmptyElim (bassSerreTree.toGraphDart d)⟩

/-- When `Γ` has no darts, every vertex of `bassSerreTree 𝔸 v₀` equals `baseVertex 𝔸 v₀`. -/
theorem bassSerreTree.mkVertex_eq_baseVertex_of_isEmpty {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    bassSerreTree.mkVertex p = bassSerreTree.baseVertex 𝔸 v₀ := by
  have key : ∀ {b : 𝔸.LetterVertex} (q : 𝔸.Path ⟨v₀⟩ b),
      bassSerreTree.mkVertex (v := b.as) q = bassSerreTree.baseVertex 𝔸 v₀ := by
    intro b q
    induction q with
    | nil => exact (bassSerreTree.baseVertex_def 𝔸 v₀).symm
    | cons q l ih =>
      cases l with
      | vertex g => exact (bassSerreTree.mkVertex_cons_vertex q g).trans ih
      | dart e => exact isEmptyElim e.1
  exact key p

/-- When `Γ` has no darts, `bassSerreTree 𝔸 v₀` has `baseVertex 𝔸 v₀` as its unique vertex. -/
instance bassSerreTree.instUniqueVertexOfIsEmpty : Unique (bassSerreTree 𝔸 v₀).V where
  default := bassSerreTree.baseVertex 𝔸 v₀
  uniq x := by
    induction x using bassSerreTree.vertex_induction_on with | _ p =>
    exact bassSerreTree.mkVertex_eq_baseVertex_of_isEmpty 𝔸 v₀ p

theorem bassSerreTree.smul_vertex_eq_self_of_isEmpty (g : π₁ 𝔸 v₀)
    (x : (bassSerreTree 𝔸 v₀).V) : g • x = x :=
  Subsingleton.elim _ _

/-- When `Γ` has no darts, the entire fundamental group `π₁(𝔸, v₀)` stabilizes `baseVertex 𝔸 v₀`. -/
theorem stabilizer_baseVertex_eq_top_of_isEmpty :
    MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.baseVertex 𝔸 v₀) = ⊤ := by
  ext g
  rw [MulAction.mem_stabilizer_iff, bassSerreTree.smul_vertex_eq_self_of_isEmpty]
  exact iff_of_true rfl (Subgroup.mem_top g)

/-- When `Γ` has no darts, the underlying Serre graph of `bassSerreTree 𝔸 v₀` is isomorphic to the
single-vertex edgeless graph `noEdge PUnit`. -/
def bassSerreTreePointIso :
    (bassSerreTree 𝔸 v₀).toSerreGraph.Iso (SerreGraph.noEdge.{0, 0} PUnit) where
  equivV :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => default
      left_inv := fun x => (Unique.eq_default x).symm
      right_inv := fun _ => rfl }
  equivE := Equiv.equivOfIsEmpty (bassSerreTree 𝔸 v₀).E PEmpty
  map_src d := isEmptyElim d
  map_rev d := isEmptyElim d

/-- When `Γ` has no darts, `bassSerreTree 𝔸 v₀` lies in the same deformation space as the
one-vertex `π₁(𝔸, v₀)`-tree `GTree.point (π₁ 𝔸 v₀)`. -/
theorem bassSerreTree_sameDeformationSpace_point :
    (bassSerreTree 𝔸 v₀).SameDeformationSpace (GTree.point.{0, 0} (π₁ 𝔸 v₀)) :=
  GTree.sameDeformationSpace_iff.mpr
    ⟨(bassSerreTree 𝔸 v₀).dominates_point,
      GTree.point_dominates_iff.mpr ((bassSerreTree 𝔸 v₀).isEllipticSubgroup_of_subsingleton ⊤)⟩

/-- When `Γ` has no darts, the quotient graph `(bassSerreTree 𝔸 v₀).quotient` has a unique
vertex. -/
instance bassSerreTree.instUniqueQuotientVertexOfIsEmpty :
    Unique (bassSerreTree 𝔸 v₀).quotient.V where
  default := (bassSerreTree 𝔸 v₀).quotientMap.mapV (bassSerreTree.baseVertex 𝔸 v₀)
  uniq q := by
    obtain ⟨x, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective q
    rw [Unique.eq_default x]
    rfl

/-- When `Γ` has no darts, the quotient graph `(bassSerreTree 𝔸 v₀).quotient` has no darts. -/
instance bassSerreTree.isEmpty_quotient_dart_of_isEmpty :
    IsEmpty (bassSerreTree 𝔸 v₀).quotient.E :=
  ⟨fun q => by
    obtain ⟨d, -⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapE_surjective q
    exact isEmptyElim d⟩

/-- In a graph without darts, no `𝔸`-path from `v₀` reaches any distinct vertex `v ≠ v₀`. -/
theorem isEmpty_path_of_isEmpty_of_ne {v : Γ.V} (hne : v₀ ≠ v) :
    IsEmpty (𝔸.Path ⟨v₀⟩ ⟨v⟩) :=
  ⟨fun p => hne (Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim p.edgePath)⟩

/-- When `Γ` has no darts and more than one vertex (for example two isolated vertices
`noEdge Bool`), `(bassSerreTree 𝔸 v₀).quotient` has a single vertex and is therefore not isomorphic
to `Γ`, showing that preconnectedness cannot be omitted in
`quotientBassSerreTreeIsoOfPreconnected`. -/
theorem isEmpty_quotient_iso_of_isEmpty_of_nontrivial [Nontrivial Γ.V] :
    IsEmpty ((bassSerreTree 𝔸 v₀).quotient.Iso Γ) :=
  ⟨fun φ => by
    obtain ⟨u, v, huv⟩ := exists_pair_ne Γ.V
    exact huv (φ.equivV.symm.injective (Subsingleton.elim _ _))⟩

end NoEdges

/-! ### Comparison with unquotiented path homotopy classes -/

section NotPathQuotient

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

namespace bassSerreTree

/-- The canonical projection from homotopy classes of `𝔸`-paths from `v₀` to `v` to vertices of
`bassSerreTree 𝔸 v₀`, quotienting further on the right by `A_v`. -/
def ofPathQuotient {v : Γ.V} :
    Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) → (bassSerreTree 𝔸 v₀).V :=
  Quotient.lift mkVertex fun _ _ h => mkVertex_congr h

@[simp] theorem ofPathQuotient_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    ofPathQuotient (Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) p) = mkVertex p :=
  (rfl)

/-- For a reachable vertex `v`, the projection from unquotiented path homotopy classes to
`bassSerreTree 𝔸 v₀` is injective if and only if the vertex group `A_v` is trivial. -/
theorem ofPathQuotient_injective_iff (v : Γ.V) [Nonempty (𝔸.Path ⟨v₀⟩ ⟨v⟩)] :
    Function.Injective (ofPathQuotient (𝔸 := 𝔸) (v₀ := v₀) (v := v)) ↔
      Subsingleton (𝔸.vertexGroup v) := by
  refine ⟨fun hinj => ⟨fun g₁ g₂ => ?_⟩, fun hsub q₁ q₂ h => ?_⟩
  · obtain ⟨p⟩ := ‹Nonempty (𝔸.Path ⟨v₀⟩ ⟨v⟩)›
    have heq : ofPathQuotient (Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) (p.cons (.vertex g₁))) =
        ofPathQuotient (Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) (p.cons (.vertex g₂))) := by
      simp
    have hhom : Path.Homotopic (p.cons (.vertex g₁)) (p.cons (.vertex g₂)) :=
      Quotient.exact (hinj heq)
    rw [← Path.comp_ofVertex, ← Path.comp_ofVertex] at hhom
    exact π₁.vertexHom_injective p <| by
      rw [π₁.vertexHom_apply, π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
      exact hhom.comp_right p.reverse
  · induction q₁ using Quotient.ind with | _ p₁ =>
    induction q₂ using Quotient.ind with | _ p₂ =>
    obtain ⟨g, hg⟩ := mkVertex_eq_mkVertex_iff.mp h
    rw [Subsingleton.elim g 1] at hg
    exact Quotient.sound (hg.trans (Path.Homotopic.one p₂))

end bassSerreTree

/-- When the base vertex group `A_{v₀}` is nontrivial, `bassSerreTree.ofPathQuotient` is not
injective at `v₀`: unquotiented closed `𝔸`-path homotopy classes distinguish elements of `A_{v₀}`
whereas `baseVertex 𝔸 v₀` identifies them. -/
theorem not_injective_ofPathQuotient [Nontrivial (𝔸.vertexGroup v₀)] :
    ¬ Function.Injective (bassSerreTree.ofPathQuotient (𝔸 := 𝔸) (v₀ := v₀) (v := v₀)) := by
  have : Nonempty (𝔸.Path ⟨v₀⟩ ⟨v₀⟩) := ⟨.nil⟩
  rw [bassSerreTree.ofPathQuotient_injective_iff]
  exact not_subsingleton _

/-- When `A_{v₀}` is nontrivial, `baseVertex 𝔸 v₀` has nontrivial stabilizer in `π₁(𝔸, v₀)`,
unlike the free left-multiplication action of `π₁(𝔸, v₀)` on itself. -/
theorem stabilizer_baseVertex_ne_bot [Nontrivial (𝔸.vertexGroup v₀)] :
    MulAction.stabilizer (π₁ 𝔸 v₀) (bassSerreTree.baseVertex 𝔸 v₀) ≠ ⊥ := by
  intro hbot
  obtain ⟨g, hg⟩ := exists_ne (1 : 𝔸.vertexGroup v₀)
  have hmem : π₁.vertexHom (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) g ∈ (⊥ : Subgroup (π₁ 𝔸 v₀)) := by
    rw [← hbot, stabilizer_baseVertex]
    exact ⟨g, rfl⟩
  exact hg ((π₁.vertexHom_eq_one_iff .nil).mp (Subgroup.mem_bot.mp hmem))

end NotPathQuotient

/-! ### HNN loops and Baumslag–Solitar groups -/

section Loop

variable {G : Type w} {C : Type x} [Group G] [Group C]
  (f g : C →* G) (hf : Function.Injective f) (hg : Function.Injective g)

/-- For the HNN loop `GraphOfGroups.loop f g hf hg`, the outgoing darts of its Bass–Serre tree from
any vertex `x` are in bijection with `(G ⧸ f.range) ⊕ (G ⧸ g.range)`, corresponding to the positive
dart `((), true)` and negative dart `((), false)` of the loop. -/
noncomputable def loopStarEquiv (x : (bassSerreTree (loop f g hf hg) ()).V) :
    (G ⧸ f.range) ⊕ (G ⧸ g.range) ≃
      {d : (bassSerreTree (loop f g hf hg) ()).E //
        (bassSerreTree (loop f g hf hg) ()).src d = x} :=
  let htrue := loop_α_true f g hf hg
  let hfalse := loop_α_false f g hf hg
  let hv : () = bassSerreTree.toGraphVertex x := Subsingleton.elim _ _
  ({ toFun := Sum.elim
       (fun q => ⟨⟨((), true), hv⟩,
         Subgroup.quotientEquivOfEq (congrArg MonoidHom.range htrue.symm) q⟩)
       (fun q => ⟨⟨((), false), hv⟩,
         Subgroup.quotientEquivOfEq (congrArg MonoidHom.range hfalse.symm) q⟩)
     invFun := fun ⟨⟨⟨⟨⟩, b⟩, _⟩, q⟩ =>
       match b, q with
       | true, q => Sum.inl (Subgroup.quotientEquivOfEq (congrArg MonoidHom.range htrue) q)
       | false, q => Sum.inr (Subgroup.quotientEquivOfEq (congrArg MonoidHom.range hfalse) q)
     left_inv := by
       rintro (q | q) <;>
         induction q using QuotientGroup.induction_on <;>
         rfl
     right_inv := by
       rintro ⟨⟨⟨⟨⟩, (_ | _)⟩, _⟩, q⟩ <;>
         induction q using QuotientGroup.induction_on <;>
         exact Sigma.ext (Subtype.ext rfl) (heq_of_eq rfl) } :
    (G ⧸ f.range) ⊕ (G ⧸ g.range) ≃
      Σ e : {e : (SerreGraph.rose Unit).E //
        (SerreGraph.rose Unit).src e = bassSerreTree.toGraphVertex x},
        (loop f g hf hg).vertexGroup ((SerreGraph.rose Unit).src e.1) ⧸
          ((loop f g hf hg).α e.1).range).trans
    (bassSerreTree.starEquivVertex x)

/-- When `f.range` and `g.range` have finite index in `G`, every vertex of the Bass–Serre tree of
`loop f g hf hg` has valence `f.range.index + g.range.index`. -/
theorem loop_natCard_star [Finite (G ⧸ f.range)] [Finite (G ⧸ g.range)]
    (x : (bassSerreTree (loop f g hf hg) ()).V) :
    Nat.card {d : (bassSerreTree (loop f g hf hg) ()).E //
      (bassSerreTree (loop f g hf hg) ()).src d = x} = f.range.index + g.range.index := by
  rw [← Nat.card_congr (loopStarEquiv f g hf hg x), Nat.card_sum, Subgroup.index, Subgroup.index]

/-- On the positive dart `((), true)` of `baumslagSolitar m n hm hn`, the image of `α` has index
`m.natAbs` in the vertex group `Multiplicative ℤ`. -/
theorem baumslagSolitar_α_true_range_index (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((baumslagSolitar m n hm hn).α ((), true)).range.index = m.natAbs := by
  have hrange : (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range =
      (AddSubgroup.zmultiples m).toSubgroup := by
    ext x
    simp only [MonoidHom.mem_range, zpowGroupHom_apply, Multiplicative.mem_toSubgroup,
      AddSubgroup.mem_zmultiples_iff]
    refine ⟨fun ⟨y, hy⟩ => ⟨y.toAdd, ?_⟩, fun ⟨k, hk⟩ => ⟨Multiplicative.ofAdd k, ?_⟩⟩
    · simp [← hy, toAdd_zpow, mul_comm]
    · apply Multiplicative.toAdd.injective
      simp [toAdd_zpow, mul_comm, ← hk]
  have hidx : (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range.index = m.natAbs := by
    rw [hrange, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  exact (congrArg (Subgroup.index ∘ MonoidHom.range)
    (baumslagSolitar_α_true m n hm hn)).trans hidx

/-- On the positive dart `((), true)` of `baumslagSolitar m n hm hn`, the image of `ω` has index
`n.natAbs` in the vertex group `Multiplicative ℤ`. -/
theorem baumslagSolitar_ω_true_range_index (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((baumslagSolitar m n hm hn).ω ((), true)).range.index = n.natAbs :=
  (congrArg (Subgroup.index ∘ MonoidHom.range)
    ((baumslagSolitar_ω_true m n hm hn).trans (baumslagSolitar_α_true n m hn hm).symm)).trans
    (baumslagSolitar_α_true_range_index n m hn hm)

/-- For nonzero `m` and `n`, every vertex of the Bass–Serre tree of `baumslagSolitar m n hm hn`
has `m.natAbs + n.natAbs` outgoing darts. -/
theorem baumslagSolitar_natCard_star (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : (bassSerreTree (baumslagSolitar m n hm hn) ()).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar m n hm hn) ()).E //
      (bassSerreTree (baumslagSolitar m n hm hn) ()).src d = x} =
      m.natAbs + n.natAbs := by
  have hm_idx :
      (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range.index = m.natAbs :=
    (congrArg (Subgroup.index ∘ MonoidHom.range)
      (baumslagSolitar_α_true m n hm hn).symm).trans
      (baumslagSolitar_α_true_range_index m n hm hn)
  have hn_idx :
      (zpowGroupHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n.natAbs :=
    (congrArg (Subgroup.index ∘ MonoidHom.range)
      (baumslagSolitar_ω_true m n hm hn).symm).trans
      (baumslagSolitar_ω_true_range_index m n hm hn)
  have : Finite (Multiplicative ℤ ⧸
      (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range) :=
    Subgroup.index_ne_zero_iff_finite.mp (hm_idx ▸ Int.natAbs_ne_zero.mpr hm)
  have : Finite (Multiplicative ℤ ⧸
      (zpowGroupHom n : Multiplicative ℤ →* Multiplicative ℤ).range) :=
    Subgroup.index_ne_zero_iff_finite.mp (hn_idx ▸ Int.natAbs_ne_zero.mpr hn)
  exact (loop_natCard_star (zpowGroupHom (α := Multiplicative ℤ) m) (zpowGroupHom n)
    (zpow_left_injective hm) (zpow_left_injective hn) x).trans (by rw [hm_idx, hn_idx])

/-- For nonzero `m` and `n`, every vertex of the Bass–Serre tree of `baumslagSolitar m n hm hn`
has `m.natAbs + n.natAbs` neighbours. -/
theorem baumslagSolitar_natCard_neighbour (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : (bassSerreTree (baumslagSolitar m n hm hn) ()).V) :
    Nat.card {y : (bassSerreTree (baumslagSolitar m n hm hn) ()).V //
      ∃ d : (bassSerreTree (baumslagSolitar m n hm hn) ()).E,
        (bassSerreTree (baumslagSolitar m n hm hn) ()).src d = x ∧
        (bassSerreTree (baumslagSolitar m n hm hn) ()).tgt d = y} =
      m.natAbs + n.natAbs := by
  rw [← Nat.card_congr (bassSerreTree.neighbourEquiv x)]
  exact baumslagSolitar_natCard_star m n hm hn x

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has `1 + 2 = 3` outgoing darts, so
`X(BS(1, 2))` is `3`-regular. -/
theorem baumslagSolitar_one_two_natCard_star
    (x : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).E //
      (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).src d = x} = 3 :=
  baumslagSolitar_natCard_star 1 2 one_ne_zero two_ne_zero x

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has `3` neighbours. -/
theorem baumslagSolitar_one_two_natCard_neighbour
    (x : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).V) :
    Nat.card {y : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).V //
      ∃ d : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).E,
        (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).src d = x ∧
        (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).tgt d = y} = 3 :=
  baumslagSolitar_natCard_neighbour 1 2 one_ne_zero two_ne_zero x

end Loop

/-! ### Segments and free products (`ℤ ∗ ℤ`) -/

section Segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C]
  (f : C →* A) (g : C →* B) (hf : Function.Injective f) (hg : Function.Injective g)

/-- At a vertex `x` over `false` in the Bass–Serre tree of `segment f g hf hg`, the outgoing darts
are in bijection with `A ⧸ f.range`. -/
noncomputable def segmentStarFalseEquiv {v₀ : SerreGraph.segment.V}
    {x : (bassSerreTree (segment f g hf hg) v₀).V}
    (hx : bassSerreTree.toGraphVertex x = (false : SerreGraph.segment.V)) :
    (A ⧸ f.range) ≃
      {d : (bassSerreTree (segment f g hf hg) v₀).E //
        (bassSerreTree (segment f g hf hg) v₀).src d = x} :=
  let hfalse := segment_α_false f g hf hg
  ({ toFun := fun q =>
       ⟨⟨false, hx.symm⟩, Subgroup.quotientEquivOfEq (congrArg MonoidHom.range hfalse.symm) q⟩
     invFun := fun ⟨⟨b, hb⟩, q⟩ =>
       match b, hb, q with
       | false, _, q => Subgroup.quotientEquivOfEq (congrArg MonoidHom.range hfalse) q
       | true, hb, _ =>
         Bool.noConfusion ((SerreGraph.segment_src true).symm.trans (hb.trans hx))
     left_inv := fun q => by induction q using QuotientGroup.induction_on; rfl
     right_inv := by
       rintro ⟨⟨(_ | _), hb⟩, q⟩
       · induction q using QuotientGroup.induction_on
         exact Sigma.ext (Subtype.ext rfl) (heq_of_eq rfl)
       · exact Bool.noConfusion ((SerreGraph.segment_src true).symm.trans (hb.trans hx)) } :
    (A ⧸ f.range) ≃
      Σ e : {e : SerreGraph.segment.E //
        SerreGraph.segment.src e = bassSerreTree.toGraphVertex x},
        (segment f g hf hg).vertexGroup (SerreGraph.segment.src e.1) ⧸
          ((segment f g hf hg).α e.1).range).trans
    (bassSerreTree.starEquivVertex x)

/-- At a vertex `x` over `true` in the Bass–Serre tree of `segment f g hf hg`, the outgoing darts
are in bijection with `B ⧸ g.range`. -/
noncomputable def segmentStarTrueEquiv {v₀ : SerreGraph.segment.V}
    {x : (bassSerreTree (segment f g hf hg) v₀).V}
    (hx : bassSerreTree.toGraphVertex x = (true : SerreGraph.segment.V)) :
    (B ⧸ g.range) ≃
      {d : (bassSerreTree (segment f g hf hg) v₀).E //
        (bassSerreTree (segment f g hf hg) v₀).src d = x} :=
  let htrue := segment_α_true f g hf hg
  ({ toFun := fun q =>
       ⟨⟨true, hx.symm⟩, Subgroup.quotientEquivOfEq (congrArg MonoidHom.range htrue.symm) q⟩
     invFun := fun ⟨⟨b, hb⟩, q⟩ =>
       match b, hb, q with
       | true, _, q => Subgroup.quotientEquivOfEq (congrArg MonoidHom.range htrue) q
       | false, hb, _ =>
         Bool.noConfusion ((SerreGraph.segment_src false).symm.trans (hb.trans hx))
     left_inv := fun q => by induction q using QuotientGroup.induction_on; rfl
     right_inv := by
       rintro ⟨⟨(_ | _), hb⟩, q⟩
       · exact Bool.noConfusion ((SerreGraph.segment_src false).symm.trans (hb.trans hx))
       · induction q using QuotientGroup.induction_on
         exact Sigma.ext (Subtype.ext rfl) (heq_of_eq rfl) } :
    (B ⧸ g.range) ≃
      Σ e : {e : SerreGraph.segment.E //
        SerreGraph.segment.src e = bassSerreTree.toGraphVertex x},
        (segment f g hf hg).vertexGroup (SerreGraph.segment.src e.1) ⧸
          ((segment f g hf hg).α e.1).range).trans
    (bassSerreTree.starEquivVertex x)

private def segmentFalseVertex : SerreGraph.segment.V := false
private def segmentTrueVertex : SerreGraph.segment.V := true
private def segmentFalseArrow : segmentFalseVertex ⟶ segmentTrueVertex :=
  ⟨(false : SerreGraph.segment.E), rfl, rfl⟩

/-- When the edge group `C` of `segment f g hf hg` is trivial, the neighbours of `baseVertex` at
`false` are in bijection with `A` via
`a ↦ π₁.mk (Path.ofVertex a) • mkVertex (Path.ofDart ⟨false, rfl, rfl⟩)`. -/
noncomputable def segmentBaseNeighbourEquiv [Subsingleton C] :
    A ≃ {y : (bassSerreTree (segment f g hf hg) false).V //
      ∃ d : (bassSerreTree (segment f g hf hg) false).E,
        (bassSerreTree (segment f g hf hg) false).src d =
          bassSerreTree.baseVertex (segment f g hf hg) false ∧
        (bassSerreTree (segment f g hf hg) false).tgt d = y} :=
  let 𝔸 := segment f g hf hg
  let v₀ := segmentFalseVertex
  have hbot : (𝔸.αArrow segmentFalseArrow).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨c, rfl⟩
    have hc : c = 1 := Subsingleton.elim (α := C) c 1
    rw [hc, map_one]
    exact Subgroup.one_mem ⊥
  have eA : A ≃ 𝔸.vertexGroup v₀ := Equiv.refl A
  (eA.trans ((QuotientGroup.quotientEquivSelf (𝔸.vertexGroup v₀)).symm.trans
    (Subgroup.quotientEquivOfEq hbot.symm))).trans <|
    (bassSerreTree.outDartFibreEquiv (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) segmentFalseArrow).trans <|
      ({ toFun := fun ⟨d, hsrc, _⟩ => ⟨d, hsrc.trans (bassSerreTree.baseVertex_def 𝔸 v₀).symm⟩
         invFun := fun ⟨d, hsrc⟩ =>
           ⟨d, hsrc.trans (bassSerreTree.baseVertex_def 𝔸 v₀), by
             have hs : SerreGraph.segment.src (bassSerreTree.toGraphDart d) = false := by
               rw [← bassSerreTree.toGraphVertex_src, hsrc, bassSerreTree.toGraphVertex_baseVertex]
               rfl
             cases h : (bassSerreTree.toGraphDart d : Bool)
             · rfl
             · rw [h] at hs
               exact Bool.noConfusion hs⟩
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        {d : (bassSerreTree 𝔸 v₀).E //
          (bassSerreTree 𝔸 v₀).src d = bassSerreTree.mkVertex .nil ∧
            bassSerreTree.toGraphDart d = segmentFalseArrow.1} ≃
          {d : (bassSerreTree 𝔸 v₀).E //
            (bassSerreTree 𝔸 v₀).src d = bassSerreTree.baseVertex 𝔸 v₀}).trans
        (bassSerreTree.neighbourEquiv (bassSerreTree.baseVertex 𝔸 v₀))

@[simp] theorem segmentBaseNeighbourEquiv_apply_val [Subsingleton C] (a : A) :
    (segmentBaseNeighbourEquiv f g hf hg a).1 =
      π₁.mk (Path.ofVertex (𝔸 := segment f g hf hg) (a := false) a) •
        bassSerreTree.mkVertex
          (Path.ofDart (𝔸 := segment f g hf hg) (a := false) (b := true) ⟨false, rfl, rfl⟩) := by
  let 𝔸 := segment f g hf hg
  let v₀ := segmentFalseVertex
  let a' : 𝔸.vertexGroup v₀ := a
  let d₀ := bassSerreTree.outDartFibreEquiv (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    segmentFalseArrow (QuotientGroup.mk a')
  have hlhs : (segmentBaseNeighbourEquiv f g hf hg a).1 = (bassSerreTree 𝔸 v₀).tgt d₀.1 :=
    bassSerreTree.neighbourEquiv_apply_val (bassSerreTree.baseVertex 𝔸 v₀)
      ⟨d₀.1, d₀.2.1.trans (bassSerreTree.baseVertex_def 𝔸 v₀).symm⟩
  have hpath :
      ((.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩).cons (Letter.vertex a')).cons
          (Letter.dart segmentFalseArrow) =
        (Path.ofVertex a').comp (Path.ofDart segmentFalseArrow) := by
    rw [Path.comp_ofDart, ← Path.comp_ofVertex, Quiver.Path.nil_comp]
  have hinner : (bassSerreTree 𝔸 v₀).tgt d₀.1 =
      π₁.mk (Path.ofVertex a') •
        bassSerreTree.mkVertex (Path.ofDart segmentFalseArrow) := by
    rw [bassSerreTree.outDartFibreEquiv_mk_val, bassSerreTree.tgt_mkDart, hpath,
      ← bassSerreTree.mk_smul_mkVertex]
  exact hlhs.trans hinner

/-- The graph of groups of the free product `ℤ ∗ ℤ`: two vertices with vertex group
`Multiplicative ℤ` joined by a single edge with trivial edge group `PUnit`. -/
abbrev freeProductZ2 : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  segment (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- Every vertex of the Bass–Serre tree of `ℤ ∗ ℤ` (`freeProductZ2`) has countably infinitely many
(`ℵ₀`) outgoing darts. -/
theorem freeProductZ2_cardinalMk_star {v₀ : SerreGraph.segment.V}
    (x : (bassSerreTree freeProductZ2 v₀).V) :
    Cardinal.mk {d : (bassSerreTree freeProductZ2 v₀).E //
      (bassSerreTree freeProductZ2 v₀).src d = x} = Cardinal.aleph0 := by
  have hbot : (1 : PUnit →* Multiplicative ℤ).range = ⊥ := MonoidHom.range_one
  have hcard : Cardinal.mk (Multiplicative ℤ ⧸ (1 : PUnit →* Multiplicative ℤ).range) =
      Cardinal.aleph0 := by
    rw [Cardinal.mk_congr (Subgroup.quotientEquivOfEq hbot),
      Cardinal.mk_congr (QuotientGroup.quotientEquivSelf (Multiplicative ℤ)),
      Cardinal.mk_congr Multiplicative.toAdd, Cardinal.mk_int]
  obtain hfalse | htrue :
      bassSerreTree.toGraphVertex x = (false : SerreGraph.segment.V) ∨
      bassSerreTree.toGraphVertex x = (true : SerreGraph.segment.V) := by
    cases (bassSerreTree.toGraphVertex x : Bool)
    · exact .inl rfl
    · exact .inr rfl
  · rw [← Cardinal.mk_congr (segmentStarFalseEquiv _ _ _ _ hfalse)]
    exact hcard
  · rw [← Cardinal.mk_congr (segmentStarTrueEquiv _ _ _ _ htrue)]
    exact hcard

/-- For `ℤ ∗ ℤ` (`freeProductZ2` based at `false`), the neighbours of the base vertex `1 · ⟨a⟩`
are parameterized by `ℤ` via `k ↦ a ^ k • ⟨b⟩`. -/
noncomputable def freeProductZ2BaseNeighbourEquiv :
    ℤ ≃ {y : (bassSerreTree freeProductZ2 false).V //
      ∃ d : (bassSerreTree freeProductZ2 false).E,
        (bassSerreTree freeProductZ2 false).src d =
          bassSerreTree.baseVertex freeProductZ2 false ∧
        (bassSerreTree freeProductZ2 false).tgt d = y} :=
  Multiplicative.ofAdd.trans (segmentBaseNeighbourEquiv _ _ _ _)

@[simp] theorem freeProductZ2BaseNeighbourEquiv_apply_val (k : ℤ) :
    (freeProductZ2BaseNeighbourEquiv k).1 =
      π₁.mk (Path.ofVertex (𝔸 := freeProductZ2) (a := false) (Multiplicative.ofAdd k)) •
        bassSerreTree.mkVertex
          (Path.ofDart (𝔸 := freeProductZ2) (a := false) (b := true) ⟨false, rfl, rfl⟩) :=
  segmentBaseNeighbourEquiv_apply_val _ _ _ _ (Multiplicative.ofAdd k)

end Segment

end TauCeti.GraphOfGroups
