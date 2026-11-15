/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Quotient
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Bass–Serre trees of one-edge graphs of groups

This file specializes the Bass–Serre tree `GraphOfGroups.bassSerreTree` and its local star and
neighbor equivalences to the one-edge graphs of groups `GraphOfGroups.segment` (amalgamated
products and free products), `GraphOfGroups.loop` (HNN extensions), `GraphOfGroups.baumslagSolitar`,
and `GraphOfGroups.cyclicAmalgam`:

* For `segment f g hf hg` (`A ∗_C B`), each vertex of `SerreGraph.segment` has a single outgoing
  dart, so the outgoing darts and adjacent vertices of `p A` (over `false`) are in bijection with
  `A ⧸ f.range`, and those of `q B` (over `true`) are in bijection with `B ⧸ g.range`. At the base
  vertex `1 A` (`v₀ = SerreGraph.segment.vertex false`), the neighbor corresponding to `a f(C)` is
  `a • (e₀ B)`, where `e₀ = SerreGraph.segment.edge` is the arrow from `false` to `true`.
* When the edge group `C` is trivial (`[Subsingleton C]`), the neighbor sets over `false` and `true`
  identify with `A` and `B` themselves. Specializing to `intFreeProduct` (`ℤ ∗ ℤ`), the neighbors of
  the base vertex `⟨a⟩` are indexed by `k : ℤ` via `k ↦ a ^ k • ⟨b⟩`, and every vertex of the
  Bass–Serre tree has countably infinite degree `ℵ₀`.
* For `loop f g hf hg` (an HNN extension of `G` over `f, g : C →* G`), the fundamental group acts
  transitively on the vertices of the Bass–Serre tree, and the star and neighbor set of every vertex
  `p G` are in bijection with `(G ⧸ f.range) ⊕ (G ⧸ g.range)`, hence have cardinal
  `#(G ⧸ f.range) + #(G ⧸ g.range)`. When `f.range` and `g.range` have finite index in `G`, every
  vertex has finite degree `f.range.index + g.range.index`.
* For `baumslagSolitar m n hm hn` (`BS(m, n)`), the images of the two boundary maps have indices
  `m.natAbs` and `n.natAbs` in `Multiplicative ℤ`, so the Bass–Serre tree is
  `(m.natAbs + n.natAbs)`-regular; in particular, for `BS(1, 2)` the two indices are `1` and `2`
  and every vertex has degree `3`. For `cyclicAmalgam m n hm hn`, vertices over `false` and `true`
  have degrees `m.natAbs` and `n.natAbs`.

## Main definitions

* `TauCeti.GraphOfGroups.segmentStarEquivFalse`, `TauCeti.GraphOfGroups.segmentStarEquivTrue`:
  outgoing darts at a vertex of the Bass–Serre tree of `segment f g hf hg` as `A ⧸ f.range` or
  `B ⧸ g.range`.
* `TauCeti.GraphOfGroups.segmentNeighborEquivFalse`,
  `TauCeti.GraphOfGroups.segmentNeighborEquivTrue`: adjacent vertices in the Bass–Serre tree of
  `segment f g hf hg` as `A ⧸ f.range` or `B ⧸ g.range`.
* `TauCeti.GraphOfGroups.segmentFreeProductNeighborEquivFalse`,
  `TauCeti.GraphOfGroups.segmentFreeProductNeighborEquivTrue`: adjacent vertices in the Bass–Serre
  tree of a free product (`[Subsingleton C]`) as `A` or `B`.
* `TauCeti.GraphOfGroups.intFreeProduct`: the segment graph of groups for `ℤ ∗ ℤ`, with
  `intFreeProductNeighborEquivBase` indexing the neighbors of `⟨a⟩` by `ℤ` via `k ↦ a ^ k • ⟨b⟩`.
* `TauCeti.GraphOfGroups.loopStarEquiv`, `TauCeti.GraphOfGroups.loopNeighborEquiv`: outgoing darts
  and adjacent vertices in the Bass–Serre tree of `loop f g hf hg` as
  `(G ⧸ f.range) ⊕ (G ⧸ g.range)`.

## Main results

* `TauCeti.GraphOfGroups.cardinalMk_neighbor_bassSerreTree_intFreeProduct`,
  `TauCeti.GraphOfGroups.cardinalMk_star_bassSerreTree_intFreeProduct`: every vertex of the
  Bass–Serre tree of `ℤ ∗ ℤ` has degree `ℵ₀`.
* `TauCeti.GraphOfGroups.cardinalMk_star_bassSerreTree_loop`,
  `TauCeti.GraphOfGroups.cardinalMk_neighbor_bassSerreTree_loop`,
  `TauCeti.GraphOfGroups.natCard_star_bassSerreTree_loop`,
  `TauCeti.GraphOfGroups.natCard_neighbor_bassSerreTree_loop`: cardinal and finite-index vertex
  degrees of the Bass–Serre tree of `loop f g hf hg`.
* `TauCeti.GraphOfGroups.natCard_star_bassSerreTree_baumslagSolitar`,
  `TauCeti.GraphOfGroups.natCard_neighbor_bassSerreTree_baumslagSolitar`: every vertex of the
  Bass–Serre tree of `BS(m, n)` has degree `m.natAbs + n.natAbs`.
* `TauCeti.GraphOfGroups.natCard_star_bassSerreTree_baumslagSolitar_one_two`,
  `TauCeti.GraphOfGroups.natCard_neighbor_bassSerreTree_baumslagSolitar_one_two`: every vertex of
  the Bass–Serre tree of `BS(1, 2)` has degree `3`.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1–4.2 and §5.3.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe w x

namespace TauCeti

namespace GraphOfGroups

/-! ### Amalgamated products and free products: `segment` -/

section Segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C]
  (f : C →* A) (g : C →* B) (hf : Function.Injective f) (hg : Function.Injective g)

/-- Each vertex `b` of `SerreGraph.segment` is the source of a unique dart, namely `b` itself. -/
private def sigmaSegmentSrcEquiv (b : SerreGraph.segment.V)
    (β : {e : SerreGraph.segment.E // SerreGraph.segment.src e = b} → Type*) :
    (Σ e, β e) ≃ β ⟨b, rfl⟩ where
  toFun := fun ⟨⟨_, rfl⟩, y⟩ => y
  invFun y := ⟨⟨b, rfl⟩, y⟩
  left_inv := fun ⟨⟨_, rfl⟩, _⟩ => rfl
  right_inv _ := rfl

private theorem segment_αArrow_false_range :
    (((segment f g hf hg).αArrow SerreGraph.segment.edge).range : Subgroup A) = f.range :=
  congrArg MonoidHom.range (((segment f g hf hg).αArrow_mk false).trans (segment_α_false f g hf hg))

private theorem segment_αArrow_true_range :
    (((segment f g hf hg).αArrow SerreGraph.segment.revEdge).range : Subgroup B) = g.range :=
  congrArg MonoidHom.range (((segment f g hf hg).αArrow_mk true).trans (segment_α_true f g hf hg))

/-- Outgoing darts at a vertex `p A` over `false` in the Bass–Serre tree of `segment f g hf hg` are
in bijection with left cosets `A ⧸ f.range`. -/
noncomputable def segmentStarEquivFalse {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex false⟩) :
    {d : (bassSerreTree (segment f g hf hg) v₀).E //
      (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} ≃ A ⧸ f.range :=
  (bassSerreStarEquiv p).trans <|
    (sigmaSegmentSrcEquiv (SerreGraph.segment.vertex false) _).trans
      (Subgroup.quotientEquivOfEq (α := A) (segment_αArrow_false_range f g hf hg))

@[simp] theorem segmentStarEquivFalse_symm_mk {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex false⟩) (a : A) :
    ((segmentStarEquivFalse f g hf hg p).symm (a : A ⧸ f.range)).1 =
      bassSerreDart false (p.cons (.vertex a)) :=
  (bassSerreStarEquiv_symm_mk p ⟨SerreGraph.segment.vertex false, rfl⟩ a).trans
    (bassSerreArrowDart_mk (𝔸 := segment f g hf hg) false (p.cons (.vertex a)))

/-- Outgoing darts at a vertex `p B` over `true` in the Bass–Serre tree of `segment f g hf hg` are
in bijection with left cosets `B ⧸ g.range`. -/
noncomputable def segmentStarEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex true⟩) :
    {d : (bassSerreTree (segment f g hf hg) v₀).E //
      (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} ≃ B ⧸ g.range :=
  (bassSerreStarEquiv p).trans <|
    (sigmaSegmentSrcEquiv (SerreGraph.segment.vertex true) _).trans
      (Subgroup.quotientEquivOfEq (α := B) (segment_αArrow_true_range f g hf hg))

@[simp] theorem segmentStarEquivTrue_symm_mk {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex true⟩) (b : B) :
    ((segmentStarEquivTrue f g hf hg p).symm (b : B ⧸ g.range)).1 =
      bassSerreDart true (p.cons (.vertex b)) :=
  (bassSerreStarEquiv_symm_mk p ⟨SerreGraph.segment.vertex true, rfl⟩ b).trans
    (bassSerreArrowDart_mk (𝔸 := segment f g hf hg) true (p.cons (.vertex b)))

/-- Adjacent vertices of `p A` over `false` in the Bass–Serre tree of `segment f g hf hg` are in
bijection with left cosets `A ⧸ f.range`. -/
noncomputable def segmentNeighborEquivFalse {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex false⟩) :
    {y : (bassSerreTree (segment f g hf hg) v₀).V // Nonempty (bassSerreVertex p ⟶ y)} ≃
      A ⧸ f.range :=
  (bassSerreNeighborEquiv p).trans <|
    (sigmaSegmentSrcEquiv (SerreGraph.segment.vertex false) _).trans
      (Subgroup.quotientEquivOfEq (α := A) (segment_αArrow_false_range f g hf hg))

@[simp] theorem segmentNeighborEquivFalse_symm_mk {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex false⟩) (a : A) :
    ((segmentNeighborEquivFalse f g hf hg p).symm (a : A ⧸ f.range)).1 =
      bassSerreVertex ((p.cons (.vertex a)).cons (.dart SerreGraph.segment.edge)) :=
  bassSerreNeighborEquiv_symm_mk p ⟨SerreGraph.segment.vertex false, rfl⟩ a

/-- At the base vertex `1 A` (`v₀ = SerreGraph.segment.vertex false`), the neighbor corresponding to
`a f(C) ∈ A ⧸ f.range` is `a • (e₀ B)`, where `e₀ = SerreGraph.segment.edge` is the arrow from
`false` to `true`. -/
theorem segmentNeighborEquivFalse_nil_symm_mk (a : A) :
    ((segmentNeighborEquivFalse f g hf hg
      (Quiver.Path.nil :
        (segment f g hf hg).Path
          ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩)).symm
      (a : A ⧸ f.range)).1 =
      π₁.vertexHom
        (Quiver.Path.nil :
          (segment f g hf hg).Path
            ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩) a •
        bassSerreVertex (Path.ofDart (𝔸 := segment f g hf hg) SerreGraph.segment.edge) := by
  refine (segmentNeighborEquivFalse_symm_mk f g hf hg
    (Quiver.Path.nil :
      (segment f g hf hg).Path ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩)
    a).trans ?_
  refine (congrArg bassSerreVertex ?_).trans
    (vertexHom_nil_smul_bassSerreVertex (𝔸 := segment f g hf hg)
      (v₀ := SerreGraph.segment.vertex false) a
      (Path.ofDart (𝔸 := segment f g hf hg) SerreGraph.segment.edge)).symm
  exact congrArg₂ Quiver.Path.comp
    (Path.ofVertex_eq_nil_cons (𝔸 := segment f g hf hg)
      (a := SerreGraph.segment.vertex false) a).symm
    (Path.ofDart_def (𝔸 := segment f g hf hg) SerreGraph.segment.edge).symm

/-- Adjacent vertices of `p B` over `true` in the Bass–Serre tree of `segment f g hf hg` are in
bijection with left cosets `B ⧸ g.range`. -/
noncomputable def segmentNeighborEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex true⟩) :
    {y : (bassSerreTree (segment f g hf hg) v₀).V // Nonempty (bassSerreVertex p ⟶ y)} ≃
      B ⧸ g.range :=
  (bassSerreNeighborEquiv p).trans <|
    (sigmaSegmentSrcEquiv (SerreGraph.segment.vertex true) _).trans
      (Subgroup.quotientEquivOfEq (α := B) (segment_αArrow_true_range f g hf hg))

@[simp] theorem segmentNeighborEquivTrue_symm_mk {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex true⟩) (b : B) :
    ((segmentNeighborEquivTrue f g hf hg p).symm (b : B ⧸ g.range)).1 =
      bassSerreVertex ((p.cons (.vertex b)).cons (.dart SerreGraph.segment.revEdge)) :=
  bassSerreNeighborEquiv_symm_mk p ⟨SerreGraph.segment.vertex true, rfl⟩ b

/-! #### Free products: trivial edge group -/

section FreeProduct

variable [Subsingleton C]

/-- When the edge group `C` is trivial, the neighbors of `p A` over `false` in the Bass–Serre tree
of `segment f g hf hg` (`A ∗ B`) are in bijection with `A`. -/
noncomputable def segmentFreeProductNeighborEquivFalse {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex false⟩) :
    {y : (bassSerreTree (segment f g hf hg) v₀).V // Nonempty (bassSerreVertex p ⟶ y)} ≃ A :=
  (segmentNeighborEquivFalse f g hf hg p).trans <|
    (Subgroup.quotientEquivOfEq (MonoidHom.range_eq_bot_iff.mpr (Subsingleton.elim f 1))).trans
      (QuotientGroup.quotientEquivSelf A)

@[simp] theorem segmentFreeProductNeighborEquivFalse_symm_apply {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex false⟩) (a : A) :
    ((segmentFreeProductNeighborEquivFalse f g hf hg p).symm a).1 =
      bassSerreVertex ((p.cons (.vertex a)).cons (.dart SerreGraph.segment.edge)) :=
  segmentNeighborEquivFalse_symm_mk f g hf hg p a

/-- In the Bass–Serre tree of `A ∗ B` based at `SerreGraph.segment.vertex false`, the neighbor of
`1 A` indexed by `a : A` is `a • (e₀ B)`. -/
theorem segmentFreeProductNeighborEquivFalse_nil_symm_apply (a : A) :
    ((segmentFreeProductNeighborEquivFalse f g hf hg
      (Quiver.Path.nil :
        (segment f g hf hg).Path
          ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩)).symm a).1 =
      π₁.vertexHom
        (Quiver.Path.nil :
          (segment f g hf hg).Path
            ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩) a •
        bassSerreVertex (Path.ofDart (𝔸 := segment f g hf hg) SerreGraph.segment.edge) :=
  segmentNeighborEquivFalse_nil_symm_mk f g hf hg a

/-- When the edge group `C` is trivial, the neighbors of `p B` over `true` in the Bass–Serre tree
of `segment f g hf hg` (`A ∗ B`) are in bijection with `B`. -/
noncomputable def segmentFreeProductNeighborEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex true⟩) :
    {y : (bassSerreTree (segment f g hf hg) v₀).V // Nonempty (bassSerreVertex p ⟶ y)} ≃ B :=
  (segmentNeighborEquivTrue f g hf hg p).trans <|
    (Subgroup.quotientEquivOfEq (MonoidHom.range_eq_bot_iff.mpr (Subsingleton.elim g 1))).trans
      (QuotientGroup.quotientEquivSelf B)

@[simp] theorem segmentFreeProductNeighborEquivTrue_symm_apply {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex true⟩) (b : B) :
    ((segmentFreeProductNeighborEquivTrue f g hf hg p).symm b).1 =
      bassSerreVertex ((p.cons (.vertex b)).cons (.dart SerreGraph.segment.revEdge)) :=
  segmentNeighborEquivTrue_symm_mk f g hf hg p b

end FreeProduct

end Segment

/-! #### The free product `ℤ ∗ ℤ` -/

section IntFreeProduct

open Multiplicative

/-- The segment graph of groups of the free product `ℤ ∗ ℤ`, with infinite cyclic vertex groups
`Multiplicative ℤ` and trivial edge group `PUnit`. -/
@[expose, instance_reducible] def intFreeProduct : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  segment (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- The neighbors of the base vertex `⟨a⟩`
(`bassSerreBase intFreeProduct (SerreGraph.segment.vertex false)`) in the Bass–Serre tree of
`ℤ ∗ ℤ` are indexed by `ℤ`, sending `k : ℤ` to `a ^ k • ⟨b⟩`. -/
noncomputable def intFreeProductNeighborEquivBase :
    {y : (bassSerreTree intFreeProduct (SerreGraph.segment.vertex false)).V //
      Nonempty (bassSerreBase intFreeProduct (SerreGraph.segment.vertex false) ⟶ y)} ≃ ℤ :=
  (segmentFreeProductNeighborEquivFalse (1 : PUnit →* Multiplicative ℤ)
    (1 : PUnit →* Multiplicative ℤ) (Function.injective_of_subsingleton _)
    (Function.injective_of_subsingleton _)
    (Quiver.Path.nil :
      intFreeProduct.Path
        ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩)).trans
    Multiplicative.toAdd

/-- Under `intFreeProductNeighborEquivBase.symm`, `k : ℤ` maps to `a ^ k • ⟨b⟩`, where `a` is the
generator of the base vertex group `ℤ` in
`π₁(intFreeProduct, SerreGraph.segment.vertex false)` and `⟨b⟩` is the adjacent vertex over `true`
along `SerreGraph.segment.edge`. -/
@[simp] theorem intFreeProductNeighborEquivBase_symm_apply (k : ℤ) :
    (intFreeProductNeighborEquivBase.symm k).1 =
      (π₁.vertexHom
        (Quiver.Path.nil :
          intFreeProduct.Path ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩)
        (ofAdd (1 : ℤ))) ^ k •
        bassSerreVertex (Path.ofDart (𝔸 := intFreeProduct) SerreGraph.segment.edge) := by
  have hk : ofAdd k = (ofAdd (1 : ℤ)) ^ k := by simp [← ofAdd_zsmul]
  refine (segmentFreeProductNeighborEquivFalse_nil_symm_apply
    (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)
    (ofAdd k)).trans ?_
  exact congrArg
    (· • bassSerreVertex (Path.ofDart (𝔸 := intFreeProduct) SerreGraph.segment.edge)) <|
    (congrArg
      (π₁.vertexHom
        (Quiver.Path.nil :
          intFreeProduct.Path ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩))
      hk).trans
      (map_zpow
        (π₁.vertexHom
          (Quiver.Path.nil :
            intFreeProduct.Path
              ⟨SerreGraph.segment.vertex false⟩ ⟨SerreGraph.segment.vertex false⟩))
        (ofAdd (1 : ℤ)) k)

/-- Every vertex of the Bass–Serre tree of `ℤ ∗ ℤ` has countably infinite neighbor degree `ℵ₀`. -/
theorem cardinalMk_neighbor_bassSerreTree_intFreeProduct
    (x : (bassSerreTree intFreeProduct (SerreGraph.segment.vertex false)).V) :
    Cardinal.mk
      {y : (bassSerreTree intFreeProduct (SerreGraph.segment.vertex false)).V //
        Nonempty (x ⟶ y)} =
      Cardinal.aleph0 := by
  induction x using bassSerreVertex_induction_on with | @mk v p =>
  cases v
  · exact (Cardinal.mk_congr ((segmentFreeProductNeighborEquivFalse
      (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
      (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _) p).trans
      Multiplicative.toAdd)).trans Cardinal.mk_int
  · exact (Cardinal.mk_congr ((segmentFreeProductNeighborEquivTrue
      (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
      (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _) p).trans
      Multiplicative.toAdd)).trans Cardinal.mk_int

/-- Every vertex of the Bass–Serre tree of `ℤ ∗ ℤ` has `ℵ₀` outgoing darts. -/
theorem cardinalMk_star_bassSerreTree_intFreeProduct
    (x : (bassSerreTree intFreeProduct (SerreGraph.segment.vertex false)).V) :
    Cardinal.mk {d : (bassSerreTree intFreeProduct (SerreGraph.segment.vertex false)).E //
      (bassSerreTree intFreeProduct (SerreGraph.segment.vertex false)).src d = x} =
      Cardinal.aleph0 := by
  induction x using bassSerreVertex_induction_on with | @mk v p =>
  exact (Cardinal.mk_congr ((bassSerreStarEquiv p).trans (bassSerreNeighborEquiv p).symm)).trans
    (cardinalMk_neighbor_bassSerreTree_intFreeProduct (bassSerreVertex p))

end IntFreeProduct

/-! ### HNN extensions: `loop` -/

section Loop

variable {G : Type w} {C : Type x} [Group G] [Group C]
  (f g : C →* G) (hf : Function.Injective f) (hg : Function.Injective g)

/-- The single vertex `()` of `SerreGraph.rose Unit` has exactly two outgoing darts: `((), true)`
and `((), false)`. -/
private def sigmaLoopSrcEquiv
    (β : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = ()} → Type*) :
    (Σ e, β e) ≃ β ⟨((), true), rfl⟩ ⊕ β ⟨((), false), rfl⟩ where
  toFun
    | ⟨⟨((), true), _⟩, y⟩ => .inl y
    | ⟨⟨((), false), _⟩, y⟩ => .inr y
  invFun
    | .inl y => ⟨⟨((), true), rfl⟩, y⟩
    | .inr y => ⟨⟨((), false), rfl⟩, y⟩
  left_inv
    | ⟨⟨((), true), rfl⟩, _⟩ => rfl
    | ⟨⟨((), false), rfl⟩, _⟩ => rfl
  right_inv
    | .inl _ => rfl
    | .inr _ => rfl

private theorem loop_αArrow_true_range :
    (((loop f g hf hg).αArrow
      (⟨((), true), rfl, rfl⟩ :
        (SerreGraph.rose Unit).src ((), true) ⟶
          (SerreGraph.rose Unit).tgt ((), true))).range : Subgroup G) =
      f.range :=
  congrArg MonoidHom.range (((loop f g hf hg).αArrow_mk ((), true)).trans (loop_α_true f g hf hg))

private theorem loop_αArrow_false_range :
    (((loop f g hf hg).αArrow
      (⟨((), false), rfl, rfl⟩ :
        (SerreGraph.rose Unit).src ((), false) ⟶
          (SerreGraph.rose Unit).tgt ((), false))).range : Subgroup G) =
      g.range :=
  congrArg MonoidHom.range (((loop f g hf hg).αArrow_mk ((), false)).trans (loop_α_false f g hf hg))

/-- Outgoing darts at `p G` in the Bass–Serre tree of `loop f g hf hg` are in bijection with
`(G ⧸ f.range) ⊕ (G ⧸ g.range)`, corresponding to the dart `((), true)` (with `α = f`) and its
reverse `((), false)` (with `α = g`). -/
noncomputable def loopStarEquiv (p : (loop f g hf hg).Path ⟨()⟩ ⟨()⟩) :
    {d : (bassSerreTree (loop f g hf hg) ()).E //
      (bassSerreTree (loop f g hf hg) ()).src d = bassSerreVertex p} ≃
      (G ⧸ f.range) ⊕ (G ⧸ g.range) :=
  (bassSerreStarEquiv p).trans <|
    (sigmaLoopSrcEquiv _).trans <|
      Equiv.sumCongr
        (Subgroup.quotientEquivOfEq (α := G) (loop_αArrow_true_range f g hf hg))
        (Subgroup.quotientEquivOfEq (α := G) (loop_αArrow_false_range f g hf hg))

@[simp] theorem loopStarEquiv_symm_inl (p : (loop f g hf hg).Path ⟨()⟩ ⟨()⟩) (a : G) :
    ((loopStarEquiv f g hf hg p).symm (.inl (a : G ⧸ f.range))).1 =
      bassSerreDart ((), true) (p.cons (.vertex a)) :=
  (bassSerreStarEquiv_symm_mk p ⟨((), true), rfl⟩ a).trans
    (bassSerreArrowDart_mk (𝔸 := loop f g hf hg) ((), true) (p.cons (.vertex a)))

@[simp] theorem loopStarEquiv_symm_inr (p : (loop f g hf hg).Path ⟨()⟩ ⟨()⟩) (a : G) :
    ((loopStarEquiv f g hf hg p).symm (.inr (a : G ⧸ g.range))).1 =
      bassSerreDart ((), false) (p.cons (.vertex a)) :=
  (bassSerreStarEquiv_symm_mk p ⟨((), false), rfl⟩ a).trans
    (bassSerreArrowDart_mk (𝔸 := loop f g hf hg) ((), false) (p.cons (.vertex a)))

/-- Adjacent vertices of `p G` in the Bass–Serre tree of `loop f g hf hg` are in bijection with
`(G ⧸ f.range) ⊕ (G ⧸ g.range)`. -/
noncomputable def loopNeighborEquiv (p : (loop f g hf hg).Path ⟨()⟩ ⟨()⟩) :
    {y : (bassSerreTree (loop f g hf hg) ()).V // Nonempty (bassSerreVertex p ⟶ y)} ≃
      (G ⧸ f.range) ⊕ (G ⧸ g.range) :=
  (bassSerreNeighborEquiv p).trans <|
    (sigmaLoopSrcEquiv _).trans <|
      Equiv.sumCongr
        (Subgroup.quotientEquivOfEq (α := G) (loop_αArrow_true_range f g hf hg))
        (Subgroup.quotientEquivOfEq (α := G) (loop_αArrow_false_range f g hf hg))

@[simp] theorem loopNeighborEquiv_symm_inl (p : (loop f g hf hg).Path ⟨()⟩ ⟨()⟩) (a : G) :
    ((loopNeighborEquiv f g hf hg p).symm (.inl (a : G ⧸ f.range))).1 =
      bassSerreVertex
        ((p.cons (.vertex a)).cons (.dart ((SerreGraph.rose Unit).dart ((), true)))) :=
  (bassSerreNeighborEquiv_symm_mk p ⟨((), true), rfl⟩ a).trans <|
    congrArg (fun d => bassSerreVertex ((p.cons (.vertex a)).cons (.dart d)))
      ((SerreGraph.rose Unit).dart_def ((), true)).symm

@[simp] theorem loopNeighborEquiv_symm_inr (p : (loop f g hf hg).Path ⟨()⟩ ⟨()⟩) (a : G) :
    ((loopNeighborEquiv f g hf hg p).symm (.inr (a : G ⧸ g.range))).1 =
      bassSerreVertex
        ((p.cons (.vertex a)).cons (.dart ((SerreGraph.rose Unit).dart ((), false)))) :=
  (bassSerreNeighborEquiv_symm_mk p ⟨((), false), rfl⟩ a).trans <|
    congrArg (fun d => bassSerreVertex ((p.cons (.vertex a)).cons (.dart d)))
      ((SerreGraph.rose Unit).dart_def ((), false)).symm

/-- Every vertex of the Bass–Serre tree of `loop f g hf hg` has cardinal
`Cardinal.mk (G ⧸ f.range) + Cardinal.mk (G ⧸ g.range)` of outgoing darts. -/
theorem cardinalMk_star_bassSerreTree_loop
    (x : (bassSerreTree (loop f g hf hg) ()).V) :
    Cardinal.mk {d : (bassSerreTree (loop f g hf hg) ()).E //
      (bassSerreTree (loop f g hf hg) ()).src d = x} =
      Cardinal.mk (G ⧸ f.range) + Cardinal.mk (G ⧸ g.range) := by
  induction x using bassSerreVertex_induction_on with | @mk v p =>
  cases v
  exact (Cardinal.mk_congr (loopStarEquiv f g hf hg p)).trans
    (Cardinal.add_def (G ⧸ f.range) (G ⧸ g.range)).symm

/-- Every vertex of the Bass–Serre tree of `loop f g hf hg` has cardinal
`Cardinal.mk (G ⧸ f.range) + Cardinal.mk (G ⧸ g.range)` of adjacent vertices. -/
theorem cardinalMk_neighbor_bassSerreTree_loop
    (x : (bassSerreTree (loop f g hf hg) ()).V) :
    Cardinal.mk {y : (bassSerreTree (loop f g hf hg) ()).V // Nonempty (x ⟶ y)} =
      Cardinal.mk (G ⧸ f.range) + Cardinal.mk (G ⧸ g.range) := by
  induction x using bassSerreVertex_induction_on with | @mk v p =>
  cases v
  exact (Cardinal.mk_congr (loopNeighborEquiv f g hf hg p)).trans
    (Cardinal.add_def (G ⧸ f.range) (G ⧸ g.range)).symm

/-- When `f.range` and `g.range` have finite index in `G`, every vertex of the Bass–Serre tree of
`loop f g hf hg` has `f.range.index + g.range.index` outgoing darts. -/
theorem natCard_star_bassSerreTree_loop [f.range.FiniteIndex] [g.range.FiniteIndex]
    (x : (bassSerreTree (loop f g hf hg) ()).V) :
    Nat.card {d : (bassSerreTree (loop f g hf hg) ()).E //
      (bassSerreTree (loop f g hf hg) ()).src d = x} = f.range.index + g.range.index := by
  induction x using bassSerreVertex_induction_on with | @mk v p =>
  cases v
  exact (Nat.card_congr (loopStarEquiv f g hf hg p)).trans (Nat.card_sum (α := G ⧸ f.range)
    (β := G ⧸ g.range))

/-- When `f.range` and `g.range` have finite index in `G`, every vertex of the Bass–Serre tree of
`loop f g hf hg` has `f.range.index + g.range.index` adjacent vertices. -/
theorem natCard_neighbor_bassSerreTree_loop [f.range.FiniteIndex] [g.range.FiniteIndex]
    (x : (bassSerreTree (loop f g hf hg) ()).V) :
    Nat.card {y : (bassSerreTree (loop f g hf hg) ()).V // Nonempty (x ⟶ y)} =
      f.range.index + g.range.index := by
  induction x using bassSerreVertex_induction_on with | @mk v p =>
  cases v
  exact (Nat.card_congr (loopNeighborEquiv f g hf hg p)).trans (Nat.card_sum (α := G ⧸ f.range)
    (β := G ⧸ g.range))

end Loop

/-! ### Baumslag–Solitar groups and cyclic amalgams -/

section Cyclic

/-- The image of `c ↦ c ^ k` on `Multiplicative ℤ` has index `k.natAbs`. -/
private theorem index_range_zpowGroupHom_multiplicative_int (k : ℤ) :
    (zpowGroupHom (α := Multiplicative ℤ) k).range.index = k.natAbs := by
  have heq :
      Nat.card (Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) k).range) =
        Nat.card (ℤ ⧸ AddSubgroup.zmultiples k) := by
    refine Nat.card_congr (Quotient.congr Multiplicative.toAdd fun x y => ?_)
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply, MonoidHom.mem_range,
      AddSubgroup.mem_zmultiples_iff]
    refine ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, ?_⟩, fun ⟨d, hd⟩ => ⟨Multiplicative.ofAdd d, ?_⟩⟩
    · have := congrArg Multiplicative.toAdd hc
      simpa [zpowGroupHom_apply, mul_comm, add_comm] using this
    · apply Multiplicative.toAdd.injective
      simpa [zpowGroupHom_apply, mul_comm, add_comm] using hd
  exact heq.trans (Int.index_zmultiples k)

private theorem finiteIndex_range_zpowGroupHom_multiplicative_int {k : ℤ} (hk : k ≠ 0) :
    (zpowGroupHom (α := Multiplicative ℤ) k).range.FiniteIndex :=
  ⟨by rw [index_range_zpowGroupHom_multiplicative_int]; exact Int.natAbs_ne_zero.mpr hk⟩

theorem baumslagSolitar_α_true_range_index (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((baumslagSolitar m n hm hn).α ((), true)).range.index = m.natAbs :=
  (congrArg (fun φ : Multiplicative ℤ →* Multiplicative ℤ => Subgroup.index φ.range)
    (baumslagSolitar_α_true m n hm hn)).trans
    (index_range_zpowGroupHom_multiplicative_int m)

theorem baumslagSolitar_ω_true_range_index (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((baumslagSolitar m n hm hn).ω ((), true)).range.index = n.natAbs :=
  (congrArg (fun φ : Multiplicative ℤ →* Multiplicative ℤ => Subgroup.index φ.range)
    (baumslagSolitar_ω_true m n hm hn)).trans
    (index_range_zpowGroupHom_multiplicative_int n)

/-- Every vertex of the Bass–Serre tree of `baumslagSolitar m n hm hn` (`BS(m, n)`) has
`m.natAbs + n.natAbs` outgoing darts. -/
theorem natCard_star_bassSerreTree_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : (bassSerreTree (baumslagSolitar m n hm hn) ()).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar m n hm hn) ()).E //
      (bassSerreTree (baumslagSolitar m n hm hn) ()).src d = x} = m.natAbs + n.natAbs := by
  have := finiteIndex_range_zpowGroupHom_multiplicative_int hm
  have := finiteIndex_range_zpowGroupHom_multiplicative_int hn
  exact (natCard_star_bassSerreTree_loop _ _ (zpow_left_injective hm)
    (zpow_left_injective hn) x).trans <| by
      rw [index_range_zpowGroupHom_multiplicative_int, index_range_zpowGroupHom_multiplicative_int]

/-- Every vertex of the Bass–Serre tree of `baumslagSolitar m n hm hn` (`BS(m, n)`) has degree
`m.natAbs + n.natAbs`: the Bass–Serre tree of `BS(m, n)` is `(m.natAbs + n.natAbs)`-regular. -/
theorem natCard_neighbor_bassSerreTree_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : (bassSerreTree (baumslagSolitar m n hm hn) ()).V) :
    Nat.card {y : (bassSerreTree (baumslagSolitar m n hm hn) ()).V // Nonempty (x ⟶ y)} =
      m.natAbs + n.natAbs := by
  have := finiteIndex_range_zpowGroupHom_multiplicative_int hm
  have := finiteIndex_range_zpowGroupHom_multiplicative_int hn
  exact (natCard_neighbor_bassSerreTree_loop _ _ (zpow_left_injective hm)
    (zpow_left_injective hn) x).trans <| by
      rw [index_range_zpowGroupHom_multiplicative_int, index_range_zpowGroupHom_multiplicative_int]

/-- For `BS(1, 2)`, the boundary monomorphism `α` on `((), true)` has image of index `1`. -/
theorem baumslagSolitar_one_two_α_true_range_index :
    ((baumslagSolitar 1 2 one_ne_zero two_ne_zero).α ((), true)).range.index = 1 :=
  baumslagSolitar_α_true_range_index 1 2 one_ne_zero two_ne_zero

/-- For `BS(1, 2)`, the boundary monomorphism `ω` on `((), true)` has image of index `2`. -/
theorem baumslagSolitar_one_two_ω_true_range_index :
    ((baumslagSolitar 1 2 one_ne_zero two_ne_zero).ω ((), true)).range.index = 2 :=
  baumslagSolitar_ω_true_range_index 1 2 one_ne_zero two_ne_zero

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has `3` outgoing darts (`1 + 2 = 3`). -/
theorem natCard_star_bassSerreTree_baumslagSolitar_one_two
    (x : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).E //
      (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).src d = x} = 3 :=
  natCard_star_bassSerreTree_baumslagSolitar 1 2 one_ne_zero two_ne_zero x

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has `3` adjacent vertices: the Bass–Serre
tree of `BS(1, 2)` is a `3`-regular tree. -/
theorem natCard_neighbor_bassSerreTree_baumslagSolitar_one_two
    (x : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).V) :
    Nat.card {y : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero two_ne_zero) ()).V //
      Nonempty (x ⟶ y)} = 3 :=
  natCard_neighbor_bassSerreTree_baumslagSolitar 1 2 one_ne_zero two_ne_zero x

/-- In the Bass–Serre tree of `cyclicAmalgam m n hm hn`, every vertex over `false` has `m.natAbs`
adjacent vertices. -/
theorem natCard_neighbor_bassSerreTree_cyclicAmalgam_false (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {v₀ : SerreGraph.segment.V}
    (p : (cyclicAmalgam m n hm hn).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex false⟩) :
    Nat.card {y : (bassSerreTree (cyclicAmalgam m n hm hn) v₀).V //
      Nonempty (bassSerreVertex p ⟶ y)} = m.natAbs :=
  (Nat.card_congr (segmentNeighborEquivFalse _ _ (zpow_left_injective hm)
    (zpow_left_injective hn) p)).trans (index_range_zpowGroupHom_multiplicative_int m)

/-- In the Bass–Serre tree of `cyclicAmalgam m n hm hn`, every vertex over `true` has `n.natAbs`
adjacent vertices. -/
theorem natCard_neighbor_bassSerreTree_cyclicAmalgam_true (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {v₀ : SerreGraph.segment.V}
    (p : (cyclicAmalgam m n hm hn).Path ⟨v₀⟩ ⟨SerreGraph.segment.vertex true⟩) :
    Nat.card {y : (bassSerreTree (cyclicAmalgam m n hm hn) v₀).V //
      Nonempty (bassSerreVertex p ⟶ y)} = n.natAbs :=
  (Nat.card_congr (segmentNeighborEquivTrue _ _ (zpow_left_injective hm)
    (zpow_left_injective hn) p)).trans (index_range_zpowGroupHom_multiplicative_int n)

end Cyclic

end GraphOfGroups

end TauCeti
