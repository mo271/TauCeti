/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Order.Sum.Order
public import TauCeti.Combinatorics.SimpleGraph.Sum
public import TauCeti.Topology.Tangle.Incidence.Basic

/-!
# Connected Components, Cell Restriction, and Disjoint Union of Diagram Incidence Data

This file develops cell-level connectivity, whole-cell subdiagram restriction, and horizontal
disjoint union (juxtaposition) for finite directed diagram incidence data
(`TauCeti.DiagramIncidence`).

## Main definitions

* `TauCeti.DiagramIncidence.Cell`: the finite sum `(D.Coupon ⊕ D.Edge) ⊕ D.Circle` of coupons,
  interval edges, and vertex-free circle components of `D`.
* `TauCeti.DiagramIncidence.cellGraph`: the finite simple graph on `D.Cell` linking a coupon `c` and
  an interval edge `e` whenever `D.src e` or `D.tgt e` is attached to `c`, with circle cells
  isolated. Because boundary ports have degree `1` and coupons are connected cells, the connected
  components of `D.cellGraph` match those of any geometric realization of `D`.
* `TauCeti.DiagramIncidence.ConnectedComponent` and `TauCeti.DiagramIncidence.componentCount`:
  finite connected components of `D` and their cardinality.
* `TauCeti.DiagramIncidence.Subcells` and `TauCeti.DiagramIncidence.restrict`: clopen unions of
  whole cells of `D` (closed under coupon-edge incidence, including `⊥`, `⊤`, unions, intersections,
  complements, and individual connected components) and restriction of `D` to such a subdiagram.
* `TauCeti.DiagramIncidence.disjointUnion`: horizontal juxtaposition placing `D₁` to the left of
  `D₂` using lexicographic disjoint sums `⊕ₗ` on lower and upper boundary ports.

## Main results

* `TauCeti.DiagramIncidence.Iso.connectedComponentEquiv` and
  `TauCeti.DiagramIncidence.Iso.componentCount_eq`: invariance of connected components under diagram
  isomorphism.
* `TauCeti.DiagramIncidence.componentCount_disjointUnion`:
  `(D₁.disjointUnion D₂).componentCount = D₁.componentCount + D₂.componentCount`, via
  `SimpleGraph.connectedComponentSumEquiv`.
* `TauCeti.DiagramIncidence.Iso.disjointUnion`, `emptyDisjointUnionIso`, `disjointUnionEmptyIso`,
  and `disjointUnionAssocIso`: functoriality, two-sided `empty` unitality, and associativity of
  `disjointUnion` up to canonical diagram isomorphism.

## References

* A. Joyal, R. Street, *The geometry of tensor calculus, I*, Adv. Math. **88** (1991), 55–112, §1.
* N. Yu. Reshetikhin, V. G. Turaev, *Ribbon graphs and their invariants derived from quantum
  groups*, Comm. Math. Phys. **127** (1990), 1–26, §4.2, pp. 8–9.
-/

@[expose] public section

universe u v

namespace TauCeti

namespace DiagramIncidence

/-! ### Empty boundary instances on elementary constructors -/

instance instIsEmptyEmptyInPort : IsEmpty (empty.{u}).InPort := inferInstanceAs (IsEmpty PEmpty)
instance instIsEmptyEmptyOutPort : IsEmpty (empty.{u}).OutPort := inferInstanceAs (IsEmpty PEmpty)
instance instIsEmptySingleCircleInPort : IsEmpty (singleCircle.{u}).InPort :=
  inferInstanceAs (IsEmpty PEmpty)
instance instIsEmptySingleCircleOutPort : IsEmpty (singleCircle.{u}).OutPort :=
  inferInstanceAs (IsEmpty PEmpty)
instance instIsEmptyNullaryCouponInPort : IsEmpty (nullaryCoupon.{u}).InPort :=
  inferInstanceAs (IsEmpty PEmpty)
instance instIsEmptyNullaryCouponOutPort : IsEmpty (nullaryCoupon.{u}).OutPort :=
  inferInstanceAs (IsEmpty PEmpty)
instance instIsEmptyCupInPort (d : StrandDir) : IsEmpty (cup.{u} d).InPort :=
  inferInstanceAs (IsEmpty PEmpty)
instance instIsEmptyCapOutPort (d : StrandDir) : IsEmpty (cap.{u} d).OutPort :=
  inferInstanceAs (IsEmpty PEmpty)

/-! ### Cell incidence graph and connected components -/

section ConnectedComponents

variable (D : DiagramIncidence.{u})

/-- Every port `p : D.Port` is either the source or the target of its incident edge `D.edgeAt p`. -/
theorem src_edgeAt_or_tgt_edgeAt (p : D.Port) :
    D.src (D.edgeAt p) = p ∨ D.tgt (D.edgeAt p) = p := by
  obtain ⟨e | e, rfl⟩ := D.endpointEquiv.surjective p
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

/-- The finite type of cells of `D`: internal coupons, interval edges, and vertex-free circles. -/
abbrev Cell : Type u :=
  (D.Coupon ⊕ D.Edge) ⊕ D.Circle

/-- Symmetric relation on `D.Cell` linking a coupon `c` and an interval edge `e` whenever `e` has
an endpoint attached to `c`. Vertex-free circles have no incident coupons or interval edges. -/
def cellAdj : D.Cell → D.Cell → Prop
  | .inl (.inl c), .inl (.inr e) => (D.src e).coupon? = some c ∨ (D.tgt e).coupon? = some c
  | .inl (.inr e), .inl (.inl c) => (D.src e).coupon? = some c ∨ (D.tgt e).coupon? = some c
  | .inl (.inl _), .inl (.inl _) => False
  | .inl (.inr _), .inl (.inr _) => False
  | .inl (.inl _), .inr _ => False
  | .inl (.inr _), .inr _ => False
  | .inr _, .inl (.inl _) => False
  | .inr _, .inl (.inr _) => False
  | .inr _, .inr _ => False

instance instDecidableRelCellAdj : DecidableRel D.cellAdj
  | .inl (.inl c), .inl (.inr e) => inferInstanceAs
      (Decidable ((D.src e).coupon? = some c ∨ (D.tgt e).coupon? = some c))
  | .inl (.inr e), .inl (.inl c) => inferInstanceAs
      (Decidable ((D.src e).coupon? = some c ∨ (D.tgt e).coupon? = some c))
  | .inl (.inl _), .inl (.inl _) => isFalse not_false
  | .inl (.inr _), .inl (.inr _) => isFalse not_false
  | .inl (.inl _), .inr _ => isFalse not_false
  | .inl (.inr _), .inr _ => isFalse not_false
  | .inr _, .inl (.inl _) => isFalse not_false
  | .inr _, .inl (.inr _) => isFalse not_false
  | .inr _, .inr _ => isFalse not_false

/-- The finite cell incidence graph of `D`. -/
def cellGraph : SimpleGraph D.Cell where
  Adj := D.cellAdj
  symm := ⟨fun x y h => by
    rcases x with (c | e) | k <;> rcases y with (c' | e') | k' <;> exact h⟩
  loopless := ⟨fun x h => by rcases x with (c | e) | k <;> exact h⟩

instance instDecidableRelCellGraphAdj : DecidableRel D.cellGraph.Adj :=
  D.instDecidableRelCellAdj

@[simp]
theorem cellGraph_adj_coupon_edge (c : D.Coupon) (e : D.Edge) :
    D.cellGraph.Adj (.inl (.inl c)) (.inl (.inr e)) ↔
      (D.src e).coupon? = some c ∨ (D.tgt e).coupon? = some c :=
  Iff.rfl

@[simp]
theorem cellGraph_adj_edge_coupon (e : D.Edge) (c : D.Coupon) :
    D.cellGraph.Adj (.inl (.inr e)) (.inl (.inl c)) ↔
      (D.src e).coupon? = some c ∨ (D.tgt e).coupon? = some c :=
  Iff.rfl

/-- Connected components of the cell incidence graph of `D`. -/
abbrev ConnectedComponent : Type u :=
  D.cellGraph.ConnectedComponent

/-- Number of connected components of `D`. -/
def componentCount : ℕ :=
  Fintype.card D.ConnectedComponent

end ConnectedComponents

namespace Iso

variable {D₁ : DiagramIncidence.{u}} {D₂ : DiagramIncidence.{v}}

/-- Adjacency preservation along the cell equivalence induced by a diagram isomorphism. -/
theorem cellGraphIso_map_rel (φ : D₁.Iso D₂) (x y : D₁.Cell) :
    D₂.cellGraph.Adj (((φ.coupon.sumCongr φ.edge).sumCongr φ.circle) x)
      (((φ.coupon.sumCongr φ.edge).sumCongr φ.circle) y) ↔
      D₁.cellGraph.Adj x y := by
  rcases x with (c | e) | k <;> rcases y with (c' | e') | k' <;>
    simp [cellGraph, cellAdj, φ.map_src', φ.map_tgt', portEquiv]

/-- Graph isomorphism on cell incidence graphs induced by a diagram isomorphism. -/
def cellGraphIso (φ : D₁.Iso D₂) : D₁.cellGraph ≃g D₂.cellGraph where
  toEquiv := (φ.coupon.sumCongr φ.edge).sumCongr φ.circle
  map_rel_iff' := cellGraphIso_map_rel φ _ _

/-- Equivalence on connected components induced by a diagram isomorphism. -/
def connectedComponentEquiv (φ : D₁.Iso D₂) :
    D₁.ConnectedComponent ≃ D₂.ConnectedComponent :=
  φ.cellGraphIso.connectedComponentEquiv

/-- Diagram isomorphisms preserve connected component counts. -/
theorem componentCount_eq (φ : D₁.Iso D₂) : D₁.componentCount = D₂.componentCount :=
  Fintype.card_congr φ.connectedComponentEquiv

end Iso

/-! ### Component counts of elementary diagrams -/

/-- When a simple graph is `⊥`, its connected components identify bijectively with its vertices. -/
def connectedComponentEquivOfEqBot {V : Type u} {G : SimpleGraph V} (h : G = ⊥) :
    G.ConnectedComponent ≃ V where
  toFun := SimpleGraph.ConnectedComponent.lift id fun _ _ p _ => by
    subst h
    exact SimpleGraph.reachable_bot.mp p.reachable
  invFun := G.connectedComponentMk
  left_inv := SimpleGraph.ConnectedComponent.ind fun _ => rfl
  right_inv _ := rfl

/-- A diagram with no coupons has discrete cell incidence graph `⊥`. -/
theorem cellGraph_eq_bot_of_isEmpty_coupon (D : DiagramIncidence.{u}) [IsEmpty D.Coupon] :
    D.cellGraph = ⊥ := by
  ext x y
  rcases x with (c | _) | _ <;> rcases y with (c' | _) | _
  · exact isEmptyElim c
  · exact isEmptyElim c
  · exact isEmptyElim c
  · exact isEmptyElim c'
  · exact Iff.rfl
  · exact Iff.rfl
  · exact isEmptyElim c'
  · exact Iff.rfl
  · exact Iff.rfl

@[simp]
theorem componentCount_empty : (empty.{u}).componentCount = 0 := by
  have : IsEmpty (empty.{u}).Cell := by
    refine ⟨fun x => ?_⟩
    rcases x with (c | e) | k
    exacts [c.elim, e.elim, k.elim]
  exact Fintype.card_eq_zero

@[simp]
theorem componentCount_singleCircle : (singleCircle.{u}).componentCount = 1 := by
  have : IsEmpty (singleCircle.{u}).Coupon := inferInstanceAs (IsEmpty PEmpty)
  have hbot := cellGraph_eq_bot_of_isEmpty_coupon singleCircle.{u}
  have eCell : (singleCircle.{u}).Cell ≃ PUnit.{u + 1} :=
    Equiv.emptySum (PEmpty ⊕ PEmpty) PUnit
  rw [componentCount, Fintype.card_congr ((connectedComponentEquivOfEqBot hbot).trans eCell)]
  exact Fintype.card_unique

@[simp]
theorem componentCount_singleCoupon (InP OutP : Type u) [Fintype InP] [Fintype OutP]
    [LinearOrder InP] [LinearOrder OutP] (inD : InP → StrandDir) (outD : OutP → StrandDir) :
    (singleCoupon InP OutP inD outD).componentCount = 1 := by
  have hreach : ∀ x : (singleCoupon InP OutP inD outD).Cell,
      (singleCoupon InP OutP inD outD).cellGraph.Reachable (.inl (.inl PUnit.unit)) x := by
    rintro ((⟨⟩ | (i | j)) | k)
    · exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      dsimp [cellGraph, cellAdj, singleCoupon]
      cases inD i <;> simp
    · refine SimpleGraph.Adj.reachable ?_
      dsimp [cellGraph, cellAdj, singleCoupon]
      cases outD j <;> simp
    · exact k.elim
  let eComp : (singleCoupon InP OutP inD outD).ConnectedComponent ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => (singleCoupon InP OutP inD outD).cellGraph.connectedComponentMk
        (.inl (.inl PUnit.unit))
      left_inv := SimpleGraph.ConnectedComponent.ind fun x =>
        SimpleGraph.ConnectedComponent.eq.mpr (hreach x)
      right_inv := fun () => rfl }
  rw [componentCount, Fintype.card_congr eComp]
  exact Fintype.card_unique

@[simp]
theorem componentCount_nullaryCoupon : (nullaryCoupon.{u}).componentCount = 1 :=
  componentCount_singleCoupon ..

@[simp]
theorem componentCount_identity (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    (identity P dir).componentCount = Fintype.card P := by
  have : IsEmpty (identity P dir).Coupon := inferInstanceAs (IsEmpty PEmpty)
  have hbot := cellGraph_eq_bot_of_isEmpty_coupon (identity P dir)
  have eCell : (identity P dir).Cell ≃ P :=
    (Equiv.sumEmpty (PEmpty ⊕ P) PEmpty).trans (Equiv.emptySum PEmpty P)
  exact Fintype.card_congr ((connectedComponentEquivOfEqBot hbot).trans eCell)

@[simp]
theorem componentCount_singleInterval (d : StrandDir) :
    (singleInterval.{u} d).componentCount = 1 := by
  rw [singleInterval, componentCount_identity]
  exact Fintype.card_unique

@[simp]
theorem componentCount_cup (d : StrandDir) : (cup.{u} d).componentCount = 1 := by
  have : IsEmpty (cup.{u} d).Coupon := inferInstanceAs (IsEmpty PEmpty)
  have hbot := cellGraph_eq_bot_of_isEmpty_coupon (cup.{u} d)
  have eCell : (cup.{u} d).Cell ≃ PUnit.{u + 1} :=
    (Equiv.sumEmpty (PEmpty ⊕ PUnit) PEmpty).trans (Equiv.emptySum PEmpty PUnit)
  rw [componentCount, Fintype.card_congr ((connectedComponentEquivOfEqBot hbot).trans eCell)]
  exact Fintype.card_unique

@[simp]
theorem componentCount_cap (d : StrandDir) : (cap.{u} d).componentCount = 1 := by
  have : IsEmpty (cap.{u} d).Coupon := inferInstanceAs (IsEmpty PEmpty)
  have hbot := cellGraph_eq_bot_of_isEmpty_coupon (cap.{u} d)
  have eCell : (cap.{u} d).Cell ≃ PUnit.{u + 1} :=
    (Equiv.sumEmpty (PEmpty ⊕ PUnit) PEmpty).trans (Equiv.emptySum PEmpty PUnit)
  rw [componentCount, Fintype.card_congr ((connectedComponentEquivOfEqBot hbot).trans eCell)]
  exact Fintype.card_unique

/-! ### Restriction to a union of whole cells -/

/-- A clopen union of whole cells of `D`: finite subsets of coupons, interval edges, and circle
components such that an interval edge belongs to `edges` if and only if any coupon incident to it
belongs to `coupons`. -/
@[ext]
structure Subcells (D : DiagramIncidence.{u}) where
  /-- Selected coupons. -/
  coupons : Finset D.Coupon
  /-- Selected interval edges. -/
  edges : Finset D.Edge
  /-- Selected circle components. -/
  circles : Finset D.Circle
  /-- Whole-cell closure: if an edge `e` meets a coupon `c`, then `e` is selected iff `c` is. -/
  mem_edges_iff_mem_coupons : ∀ (e : D.Edge) (c : D.Coupon),
    ((D.src e).coupon? = some c ∨ (D.tgt e).coupon? = some c) →
      (e ∈ edges ↔ c ∈ coupons)

namespace Subcells

variable {D : DiagramIncidence.{u}}

/-- The empty selection of cells. -/
protected def bot (D : DiagramIncidence.{u}) : D.Subcells where
  coupons := ∅
  edges := ∅
  circles := ∅
  mem_edges_iff_mem_coupons _ _ _ := by simp

/-- The full selection of all cells of `D`. -/
protected def top (D : DiagramIncidence.{u}) : D.Subcells where
  coupons := Finset.univ
  edges := Finset.univ
  circles := Finset.univ
  mem_edges_iff_mem_coupons _ _ _ := by simp

/-- Union of two whole-cell selections. -/
protected def sup (S₁ S₂ : D.Subcells) : D.Subcells where
  coupons := S₁.coupons ∪ S₂.coupons
  edges := S₁.edges ∪ S₂.edges
  circles := S₁.circles ∪ S₂.circles
  mem_edges_iff_mem_coupons e c h := by
    simp [S₁.mem_edges_iff_mem_coupons e c h, S₂.mem_edges_iff_mem_coupons e c h]

/-- Intersection of two whole-cell selections. -/
protected def inf (S₁ S₂ : D.Subcells) : D.Subcells where
  coupons := S₁.coupons ∩ S₂.coupons
  edges := S₁.edges ∩ S₂.edges
  circles := S₁.circles ∩ S₂.circles
  mem_edges_iff_mem_coupons e c h := by
    simp [S₁.mem_edges_iff_mem_coupons e c h, S₂.mem_edges_iff_mem_coupons e c h]

/-- Complement of a whole-cell selection. -/
protected def compl (S : D.Subcells) : D.Subcells where
  coupons := S.couponsᶜ
  edges := S.edgesᶜ
  circles := S.circlesᶜ
  mem_edges_iff_mem_coupons e c h := by
    simp [S.mem_edges_iff_mem_coupons e c h]

instance : Bot D.Subcells := ⟨Subcells.bot D⟩
instance : Top D.Subcells := ⟨Subcells.top D⟩
instance : Max D.Subcells := ⟨Subcells.sup⟩
instance : Min D.Subcells := ⟨Subcells.inf⟩
instance : Compl D.Subcells := ⟨Subcells.compl⟩

@[simp] theorem bot_coupons : (⊥ : D.Subcells).coupons = ∅ := rfl
@[simp] theorem bot_edges : (⊥ : D.Subcells).edges = ∅ := rfl
@[simp] theorem bot_circles : (⊥ : D.Subcells).circles = ∅ := rfl
@[simp] theorem top_coupons : (⊤ : D.Subcells).coupons = Finset.univ := rfl
@[simp] theorem top_edges : (⊤ : D.Subcells).edges = Finset.univ := rfl
@[simp] theorem top_circles : (⊤ : D.Subcells).circles = Finset.univ := rfl

/-- The whole-cell selection spanned by a single connected component `K : D.ConnectedComponent`. -/
def ofConnectedComponent (K : D.ConnectedComponent) : D.Subcells where
  coupons := Finset.univ.filter fun c => (.inl (.inl c) : D.Cell) ∈ K.supp
  edges := Finset.univ.filter fun e => (.inl (.inr e) : D.Cell) ∈ K.supp
  circles := Finset.univ.filter fun k => (.inr k : D.Cell) ∈ K.supp
  mem_edges_iff_mem_coupons e c h := by
    have hadj : D.cellGraph.Adj (.inl (.inl c)) (.inl (.inr e)) := h
    have heq : D.cellGraph.connectedComponentMk (.inl (.inl c)) =
        D.cellGraph.connectedComponentMk (.inl (.inr e)) :=
      SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff, heq]

theorem mem_coupons_of_src {S : D.Subcells} {e : D.Edge} (he : e ∈ S.edges) {c : D.Coupon}
    (hc : (D.src e).coupon? = some c) : c ∈ S.coupons :=
  (S.mem_edges_iff_mem_coupons e c (Or.inl hc)).mp he

theorem mem_coupons_of_tgt {S : D.Subcells} {e : D.Edge} (he : e ∈ S.edges) {c : D.Coupon}
    (hc : (D.tgt e).coupon? = some c) : c ∈ S.coupons :=
  (S.mem_edges_iff_mem_coupons e c (Or.inr hc)).mp he

theorem edgeAt_mem_edges_of_coupon {S : D.Subcells} {p : D.Port} {c : D.Coupon}
    (hp : p.coupon? = some c) (hc : c ∈ S.coupons) : D.edgeAt p ∈ S.edges := by
  have hinc : (D.src (D.edgeAt p)).coupon? = some c ∨ (D.tgt (D.edgeAt p)).coupon? = some c := by
    rcases D.src_edgeAt_or_tgt_edgeAt p with h | h
    · exact Or.inl (h.symm ▸ hp)
    · exact Or.inr (h.symm ▸ hp)
  exact (S.mem_edges_iff_mem_coupons (D.edgeAt p) c hinc).mpr hc

theorem mem_coupons_of_edgeAt_coupon {S : D.Subcells} {p : D.Port} {c : D.Coupon}
    (hp : p.coupon? = some c) (he : D.edgeAt p ∈ S.edges) : c ∈ S.coupons := by
  have hinc : (D.src (D.edgeAt p)).coupon? = some c ∨ (D.tgt (D.edgeAt p)).coupon? = some c := by
    rcases D.src_edgeAt_or_tgt_edgeAt p with h | h
    · exact Or.inl (h.symm ▸ hp)
    · exact Or.inr (h.symm ▸ hp)
  exact (S.mem_edges_iff_mem_coupons (D.edgeAt p) c hinc).mp he

end Subcells

section Restrict

/-- Lift a port `p : D.Port` whose incident edge belongs to `S.edges` into the port type of
`D.restrict S`. -/
def restrictPort (D : DiagramIncidence.{u}) (S : D.Subcells) (p : D.Port)
    (he : D.edgeAt p ∈ S.edges) :
    DiagramPort
      { i : D.InPort // D.edgeAt (.inBound i) ∈ S.edges }
      { j : D.OutPort // D.edgeAt (.outBound j) ∈ S.edges }
      { c : D.Coupon // c ∈ S.coupons }
      (fun c => D.CouponIn c.1)
      (fun c => D.CouponOut c.1) :=
  match p, he with
  | .inBound i, hi => .inBound ⟨i, hi⟩
  | .outBound j, hj => .outBound ⟨j, hj⟩
  | .couponIn c i, hci => .couponIn ⟨c, S.mem_coupons_of_edgeAt_coupon rfl hci⟩ i
  | .couponOut c j, hcj => .couponOut ⟨c, S.mem_coupons_of_edgeAt_coupon rfl hcj⟩ j

/-- Forgetful inclusion from ports of `D.restrict S` into `D.Port`. -/
def unrestrictPort (D : DiagramIncidence.{u}) (S : D.Subcells) :
    DiagramPort
      { i : D.InPort // D.edgeAt (.inBound i) ∈ S.edges }
      { j : D.OutPort // D.edgeAt (.outBound j) ∈ S.edges }
      { c : D.Coupon // c ∈ S.coupons }
      (fun c => D.CouponIn c.1)
      (fun c => D.CouponOut c.1) → D.Port
  | .inBound i => .inBound i.1
  | .outBound j => .outBound j.1
  | .couponIn c i => .couponIn c.1 i
  | .couponOut c j => .couponOut c.1 j

/-- The forgetful port inclusion `unrestrictPort` is injective. -/
theorem unrestrictPort_injective (D : DiagramIncidence.{u}) (S : D.Subcells) :
    Function.Injective (unrestrictPort D S) := by
  rintro (⟨i₁, _⟩ | ⟨j₁, _⟩ | ⟨⟨c₁, _⟩, i₁⟩ | ⟨⟨c₁, _⟩, j₁⟩)
    (⟨i₂, _⟩ | ⟨j₂, _⟩ | ⟨⟨c₂, _⟩, i₂⟩ | ⟨⟨c₂, _⟩, j₂⟩) h
  · exact congrArg DiagramPort.inBound (Subtype.ext (DiagramPort.inBound.inj h))
  · cases h
  · cases h
  · cases h
  · cases h
  · exact congrArg DiagramPort.outBound (Subtype.ext (DiagramPort.outBound.inj h))
  · cases h
  · cases h
  · cases h
  · cases h
  · rcases DiagramPort.couponIn.inj h with ⟨rfl, hi⟩
    exact congrArg (DiagramPort.couponIn _) (eq_of_heq hi)
  · cases h
  · cases h
  · cases h
  · cases h
  · rcases DiagramPort.couponOut.inj h with ⟨rfl, hj⟩
    exact congrArg (DiagramPort.couponOut _) (eq_of_heq hj)

/-- Restricted edge endpoints form a bijection onto the restricted port type. -/
theorem bijective_sumElim_restrict (D : DiagramIncidence.{u}) (S : D.Subcells) :
    Function.Bijective
      (Sum.elim
        (fun e : { e : D.Edge // e ∈ S.edges } =>
          restrictPort D S (D.src e.1) (by rw [D.edgeAt_src]; exact e.2))
        (fun e : { e : D.Edge // e ∈ S.edges } =>
          restrictPort D S (D.tgt e.1) (by rw [D.edgeAt_tgt]; exact e.2))) := by
  have hunrestrict_restrict : ∀ (p : D.Port) (hp : D.edgeAt p ∈ S.edges),
      unrestrictPort D S (restrictPort D S p hp) = p := by
    rintro (i | j | ⟨c, i⟩ | ⟨c, j⟩) _ <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hval := congrArg (unrestrictPort D S) hxy
    rcases x with ⟨e₁, _⟩ | ⟨e₁, _⟩ <;> rcases y with ⟨e₂, _⟩ | ⟨e₂, _⟩ <;>
      simp only [Sum.elim_inl, Sum.elim_inr, hunrestrict_restrict] at hval
    · exact congrArg Sum.inl (Subtype.ext (D.src_injective hval))
    · exact (D.src_ne_tgt e₁ e₂ hval).elim
    · exact (D.src_ne_tgt e₂ e₁ hval.symm).elim
    · exact congrArg Sum.inr (Subtype.ext (D.tgt_injective hval))
  · intro q
    have hq : D.edgeAt (unrestrictPort D S q) ∈ S.edges := by
      rcases q with ⟨_, hi⟩ | ⟨_, hj⟩ | ⟨⟨_, hc⟩, _⟩ | ⟨⟨_, hc⟩, _⟩
      · exact hi
      · exact hj
      · exact S.edgeAt_mem_edges_of_coupon rfl hc
      · exact S.edgeAt_mem_edges_of_coupon rfl hc
    rcases hsymm : D.endpointEquiv.symm (unrestrictPort D S q) with e | e
    · have he : e ∈ S.edges := by simpa [edgeAt, hsymm] using hq
      have hsrc : D.src e = unrestrictPort D S q := D.endpointEquiv.eq_symm_apply.mp hsymm.symm
      refine ⟨.inl ⟨e, he⟩, unrestrictPort_injective D S ?_⟩
      simp only [Sum.elim_inl, hunrestrict_restrict, hsrc]
    · have he : e ∈ S.edges := by simpa [edgeAt, hsymm] using hq
      have htgt : D.tgt e = unrestrictPort D S q := D.endpointEquiv.eq_symm_apply.mp hsymm.symm
      refine ⟨.inr ⟨e, he⟩, unrestrictPort_injective D S ?_⟩
      simp only [Sum.elim_inr, hunrestrict_restrict, htgt]

/-- Restriction of `D` to a clopen union `S : D.Subcells` of whole cells, retaining all ports of
selected coupons together with the lower and upper boundary ports incident to selected edges. -/
def restrict (D : DiagramIncidence.{u}) (S : D.Subcells) : DiagramIncidence.{u} where
  InPort := { i : D.InPort // D.edgeAt (.inBound i) ∈ S.edges }
  OutPort := { j : D.OutPort // D.edgeAt (.outBound j) ∈ S.edges }
  Coupon := { c : D.Coupon // c ∈ S.coupons }
  CouponIn c := D.CouponIn c.1
  CouponOut c := D.CouponOut c.1
  Edge := { e : D.Edge // e ∈ S.edges }
  Circle := { k : D.Circle // k ∈ S.circles }
  src e := restrictPort D S (D.src e.1) (by rw [D.edgeAt_src]; exact e.2)
  tgt e := restrictPort D S (D.tgt e.1) (by rw [D.edgeAt_tgt]; exact e.2)
  bijective_sumElim_src_tgt := bijective_sumElim_restrict D S

@[simp]
theorem edgeCount_restrict (D : DiagramIncidence.{u}) (S : D.Subcells) :
    (D.restrict S).edgeCount = S.edges.card :=
  Fintype.card_coe S.edges

@[simp]
theorem couponCount_restrict (D : DiagramIncidence.{u}) (S : D.Subcells) :
    (D.restrict S).couponCount = S.coupons.card :=
  Fintype.card_coe S.coupons

@[simp]
theorem circleCount_restrict (D : DiagramIncidence.{u}) (S : D.Subcells) :
    (D.restrict S).circleCount = S.circles.card :=
  Fintype.card_coe S.circles

/-- Restricting `D` to `⊥` is canonically isomorphic to `empty`. -/
def restrictBotIso (D : DiagramIncidence.{u}) : (D.restrict ⊥).Iso empty where
  inPort :=
    { toEquiv := ⟨fun i => (Finset.notMem_empty _ i.2).elim, PEmpty.elim,
        fun i => (Finset.notMem_empty _ i.2).elim, fun x => x.elim⟩
      map_rel_iff' := @fun i => (Finset.notMem_empty _ i.2).elim }
  outPort :=
    { toEquiv := ⟨fun j => (Finset.notMem_empty _ j.2).elim, PEmpty.elim,
        fun j => (Finset.notMem_empty _ j.2).elim, fun x => x.elim⟩
      map_rel_iff' := @fun j => (Finset.notMem_empty _ j.2).elim }
  coupon := ⟨fun c => (Finset.notMem_empty _ c.2).elim, PEmpty.elim,
    fun c => (Finset.notMem_empty _ c.2).elim, fun x => x.elim⟩
  couponIn c := (Finset.notMem_empty _ c.2).elim
  couponOut c := (Finset.notMem_empty _ c.2).elim
  edge := ⟨fun e => (Finset.notMem_empty _ e.2).elim, PEmpty.elim,
    fun e => (Finset.notMem_empty _ e.2).elim, fun x => x.elim⟩
  circle := ⟨fun k => (Finset.notMem_empty _ k.2).elim, PEmpty.elim,
    fun k => (Finset.notMem_empty _ k.2).elim, fun x => x.elim⟩
  map_src e := (Finset.notMem_empty _ e.2).elim
  map_tgt e := (Finset.notMem_empty _ e.2).elim

/-- Port compatibility for `restrictTopIso`. -/
theorem restrictTopIso_port (D : DiagramIncidence.{u}) (p : D.Port)
    (hp : D.edgeAt p ∈ (⊤ : D.Subcells).edges) :
    DiagramPort.congr (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _)
      (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _)
      (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _)
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
      (restrictPort D ⊤ p hp) = p := by
  cases p <;> rfl

/-- Restricting `D` to `⊤` is canonically isomorphic to `D`. -/
def restrictTopIso (D : DiagramIncidence.{u}) : (D.restrict ⊤).Iso D where
  inPort :=
    { toEquiv := Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _
      map_rel_iff' := Iff.rfl }
  outPort :=
    { toEquiv := Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _
      map_rel_iff' := Iff.rfl }
  coupon := Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _
  couponIn _ := OrderIso.refl _
  couponOut _ := OrderIso.refl _
  edge := Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _
  circle := Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _
  map_src e := (restrictTopIso_port D (D.src e.1) _).symm
  map_tgt e := (restrictTopIso_port D (D.tgt e.1) _).symm

end Restrict

/-! ### Horizontal disjoint union (juxtaposition) -/

section DisjointUnion

/-- Combined port equivalence between `D₁.Port ⊕ D₂.Port` and the port type of
`D₁.disjointUnion D₂`, ordering lower and upper boundary ports by lexicographic sum `⊕ₗ`. -/
def disjointPortEquiv (D₁ D₂ : DiagramIncidence.{u}) :
    D₁.Port ⊕ D₂.Port ≃
      DiagramPort (D₁.InPort ⊕ₗ D₂.InPort) (D₁.OutPort ⊕ₗ D₂.OutPort)
        (D₁.Coupon ⊕ D₂.Coupon)
        (Sum.elim D₁.CouponIn D₂.CouponIn)
        (Sum.elim D₁.CouponOut D₂.CouponOut) where
  toFun
    | .inl (.inBound i) => .inBound (toLex (.inl i))
    | .inl (.outBound j) => .outBound (toLex (.inl j))
    | .inl (.couponIn c i) => .couponIn (.inl c) i
    | .inl (.couponOut c j) => .couponOut (.inl c) j
    | .inr (.inBound i) => .inBound (toLex (.inr i))
    | .inr (.outBound j) => .outBound (toLex (.inr j))
    | .inr (.couponIn c i) => .couponIn (.inr c) i
    | .inr (.couponOut c j) => .couponOut (.inr c) j
  invFun
    | .inBound s => match ofLex s with
      | .inl i => .inl (.inBound i)
      | .inr i => .inr (.inBound i)
    | .outBound s => match ofLex s with
      | .inl j => .inl (.outBound j)
      | .inr j => .inr (.outBound j)
    | .couponIn (.inl c) i => .inl (.couponIn c i)
    | .couponIn (.inr c) i => .inr (.couponIn c i)
    | .couponOut (.inl c) j => .inl (.couponOut c j)
    | .couponOut (.inr c) j => .inr (.couponOut c j)
  left_inv x := by rcases x with (_ | _ | _ | _) | (_ | _ | _ | _) <;> rfl
  right_inv y := by rcases y with (i | i) | (j | j) | ⟨_ | _, _⟩ | ⟨_ | _, _⟩ <;> rfl

@[simp]
theorem disjointPortEquiv_inl_inBound (D₁ D₂ : DiagramIncidence.{u}) (i : D₁.InPort) :
    disjointPortEquiv D₁ D₂ (.inl (.inBound i)) = .inBound (toLex (.inl i)) := rfl

@[simp]
theorem disjointPortEquiv_inl_outBound (D₁ D₂ : DiagramIncidence.{u}) (j : D₁.OutPort) :
    disjointPortEquiv D₁ D₂ (.inl (.outBound j)) = .outBound (toLex (.inl j)) := rfl

@[simp]
theorem disjointPortEquiv_inl_couponIn (D₁ D₂ : DiagramIncidence.{u}) (c : D₁.Coupon)
    (i : D₁.CouponIn c) :
    disjointPortEquiv D₁ D₂ (.inl (.couponIn c i)) = .couponIn (.inl c) i := rfl

@[simp]
theorem disjointPortEquiv_inl_couponOut (D₁ D₂ : DiagramIncidence.{u}) (c : D₁.Coupon)
    (j : D₁.CouponOut c) :
    disjointPortEquiv D₁ D₂ (.inl (.couponOut c j)) = .couponOut (.inl c) j := rfl

@[simp]
theorem disjointPortEquiv_inr_inBound (D₁ D₂ : DiagramIncidence.{u}) (i : D₂.InPort) :
    disjointPortEquiv D₁ D₂ (.inr (.inBound i)) = .inBound (toLex (.inr i)) := rfl

@[simp]
theorem disjointPortEquiv_inr_outBound (D₁ D₂ : DiagramIncidence.{u}) (j : D₂.OutPort) :
    disjointPortEquiv D₁ D₂ (.inr (.outBound j)) = .outBound (toLex (.inr j)) := rfl

@[simp]
theorem disjointPortEquiv_inr_couponIn (D₁ D₂ : DiagramIncidence.{u}) (c : D₂.Coupon)
    (i : D₂.CouponIn c) :
    disjointPortEquiv D₁ D₂ (.inr (.couponIn c i)) = .couponIn (.inr c) i := rfl

@[simp]
theorem disjointPortEquiv_inr_couponOut (D₁ D₂ : DiagramIncidence.{u}) (c : D₂.Coupon)
    (j : D₂.CouponOut c) :
    disjointPortEquiv D₁ D₂ (.inr (.couponOut c j)) = .couponOut (.inr c) j := rfl

/-- Endpoint bijection for horizontal disjoint union. -/
theorem bijective_sumElim_disjointUnion (D₁ D₂ : DiagramIncidence.{u}) :
    Function.Bijective
      (Sum.elim
        (Sum.elim (fun e₁ => disjointPortEquiv D₁ D₂ (.inl (D₁.src e₁)))
          (fun e₂ => disjointPortEquiv D₁ D₂ (.inr (D₂.src e₂))))
        (Sum.elim (fun e₁ => disjointPortEquiv D₁ D₂ (.inl (D₁.tgt e₁)))
          (fun e₂ => disjointPortEquiv D₁ D₂ (.inr (D₂.tgt e₂))))) := by
  let reorder : (D₁.Edge ⊕ D₂.Edge) ⊕ (D₁.Edge ⊕ D₂.Edge) ≃
      (D₁.Edge ⊕ D₁.Edge) ⊕ (D₂.Edge ⊕ D₂.Edge) :=
    Equiv.sumSumSumComm D₁.Edge D₂.Edge D₁.Edge D₂.Edge
  have hcomp :
      Sum.elim
        (Sum.elim (fun e₁ => disjointPortEquiv D₁ D₂ (.inl (D₁.src e₁)))
          (fun e₂ => disjointPortEquiv D₁ D₂ (.inr (D₂.src e₂))))
        (Sum.elim (fun e₁ => disjointPortEquiv D₁ D₂ (.inl (D₁.tgt e₁)))
          (fun e₂ => disjointPortEquiv D₁ D₂ (.inr (D₂.tgt e₂)))) =
      disjointPortEquiv D₁ D₂ ∘
        Sum.map (Sum.elim D₁.src D₁.tgt) (Sum.elim D₂.src D₂.tgt) ∘ reorder := by
    ext ((e₁ | e₂) | (e₁ | e₂)) <;> rfl
  rw [hcomp]
  exact (disjointPortEquiv D₁ D₂).bijective.comp
    ((D₁.bijective_sumElim_src_tgt.sumMap D₂.bijective_sumElim_src_tgt).comp reorder.bijective)

/-- Horizontal disjoint union (juxtaposition) placing `D₁` to the left of `D₂`, ordering boundary
ports via `⊕ₗ` so all boundary ports of `D₁` precede all boundary ports of `D₂`. -/
def disjointUnion (D₁ D₂ : DiagramIncidence.{u}) : DiagramIncidence.{u} where
  InPort := D₁.InPort ⊕ₗ D₂.InPort
  OutPort := D₁.OutPort ⊕ₗ D₂.OutPort
  Coupon := D₁.Coupon ⊕ D₂.Coupon
  CouponIn := Sum.elim D₁.CouponIn D₂.CouponIn
  CouponOut := Sum.elim D₁.CouponOut D₂.CouponOut
  Edge := D₁.Edge ⊕ D₂.Edge
  Circle := D₁.Circle ⊕ D₂.Circle
  instFintypeCouponIn := Sum.rec D₁.instFintypeCouponIn D₂.instFintypeCouponIn
  instFintypeCouponOut := Sum.rec D₁.instFintypeCouponOut D₂.instFintypeCouponOut
  instLinearOrderCouponIn := Sum.rec D₁.instLinearOrderCouponIn D₂.instLinearOrderCouponIn
  instLinearOrderCouponOut := Sum.rec D₁.instLinearOrderCouponOut D₂.instLinearOrderCouponOut
  src := Sum.elim (fun e₁ => disjointPortEquiv D₁ D₂ (.inl (D₁.src e₁)))
    (fun e₂ => disjointPortEquiv D₁ D₂ (.inr (D₂.src e₂)))
  tgt := Sum.elim (fun e₁ => disjointPortEquiv D₁ D₂ (.inl (D₁.tgt e₁)))
    (fun e₂ => disjointPortEquiv D₁ D₂ (.inr (D₂.tgt e₂)))
  bijective_sumElim_src_tgt := bijective_sumElim_disjointUnion D₁ D₂

@[simp]
theorem src_disjointUnion_inl (D₁ D₂ : DiagramIncidence.{u}) (e₁ : D₁.Edge) :
    (D₁.disjointUnion D₂).src (.inl e₁) = disjointPortEquiv D₁ D₂ (.inl (D₁.src e₁)) := rfl

@[simp]
theorem src_disjointUnion_inr (D₁ D₂ : DiagramIncidence.{u}) (e₂ : D₂.Edge) :
    (D₁.disjointUnion D₂).src (.inr e₂) = disjointPortEquiv D₁ D₂ (.inr (D₂.src e₂)) := rfl

@[simp]
theorem tgt_disjointUnion_inl (D₁ D₂ : DiagramIncidence.{u}) (e₁ : D₁.Edge) :
    (D₁.disjointUnion D₂).tgt (.inl e₁) = disjointPortEquiv D₁ D₂ (.inl (D₁.tgt e₁)) := rfl

@[simp]
theorem tgt_disjointUnion_inr (D₁ D₂ : DiagramIncidence.{u}) (e₂ : D₂.Edge) :
    (D₁.disjointUnion D₂).tgt (.inr e₂) = disjointPortEquiv D₁ D₂ (.inr (D₂.tgt e₂)) := rfl

@[simp]
theorem edgeCount_disjointUnion (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).edgeCount = D₁.edgeCount + D₂.edgeCount := by
  dsimp [edgeCount, disjointUnion]; exact Fintype.card_sum

@[simp]
theorem couponCount_disjointUnion (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).couponCount = D₁.couponCount + D₂.couponCount := by
  dsimp [couponCount, disjointUnion]; exact Fintype.card_sum

@[simp]
theorem circleCount_disjointUnion (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).circleCount = D₁.circleCount + D₂.circleCount := by
  dsimp [circleCount, disjointUnion]; exact Fintype.card_sum

@[simp]
theorem portCount_disjointUnion (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).portCount = D₁.portCount + D₂.portCount := by
  have h₁ := D₁.two_mul_edgeCount_eq_portCount
  have h₂ := D₂.two_mul_edgeCount_eq_portCount
  have h₁₂ := (D₁.disjointUnion D₂).two_mul_edgeCount_eq_portCount
  rw [edgeCount_disjointUnion] at h₁₂
  omega

@[simp]
theorem inDir_disjointUnion_inl (D₁ D₂ : DiagramIncidence.{u}) (i : D₁.InPort) :
    (D₁.disjointUnion D₂).inDir (toLex (.inl i)) = D₁.inDir i := by
  cases h : D₁.inDir i
  · obtain ⟨e, he⟩ := (D₁.inDir_eq_upward_iff i).mp h
    exact ((D₁.disjointUnion D₂).inDir_eq_upward_iff _).mpr
      ⟨.inl e, by rw [src_disjointUnion_inl, he]; rfl⟩
  · obtain ⟨e, he⟩ := (D₁.inDir_eq_downward_iff i).mp h
    exact ((D₁.disjointUnion D₂).inDir_eq_downward_iff _).mpr
      ⟨.inl e, by rw [tgt_disjointUnion_inl, he]; rfl⟩

@[simp]
theorem inDir_disjointUnion_inr (D₁ D₂ : DiagramIncidence.{u}) (i : D₂.InPort) :
    (D₁.disjointUnion D₂).inDir (toLex (.inr i)) = D₂.inDir i := by
  cases h : D₂.inDir i
  · obtain ⟨e, he⟩ := (D₂.inDir_eq_upward_iff i).mp h
    exact ((D₁.disjointUnion D₂).inDir_eq_upward_iff _).mpr
      ⟨.inr e, by rw [src_disjointUnion_inr, he]; rfl⟩
  · obtain ⟨e, he⟩ := (D₂.inDir_eq_downward_iff i).mp h
    exact ((D₁.disjointUnion D₂).inDir_eq_downward_iff _).mpr
      ⟨.inr e, by rw [tgt_disjointUnion_inr, he]; rfl⟩

@[simp]
theorem outDir_disjointUnion_inl (D₁ D₂ : DiagramIncidence.{u}) (j : D₁.OutPort) :
    (D₁.disjointUnion D₂).outDir (toLex (.inl j)) = D₁.outDir j := by
  cases h : D₁.outDir j
  · obtain ⟨e, he⟩ := (D₁.outDir_eq_upward_iff j).mp h
    exact ((D₁.disjointUnion D₂).outDir_eq_upward_iff _).mpr
      ⟨.inl e, by rw [tgt_disjointUnion_inl, he]; rfl⟩
  · obtain ⟨e, he⟩ := (D₁.outDir_eq_downward_iff j).mp h
    exact ((D₁.disjointUnion D₂).outDir_eq_downward_iff _).mpr
      ⟨.inl e, by rw [src_disjointUnion_inl, he]; rfl⟩

@[simp]
theorem outDir_disjointUnion_inr (D₁ D₂ : DiagramIncidence.{u}) (j : D₂.OutPort) :
    (D₁.disjointUnion D₂).outDir (toLex (.inr j)) = D₂.outDir j := by
  cases h : D₂.outDir j
  · obtain ⟨e, he⟩ := (D₂.outDir_eq_upward_iff j).mp h
    exact ((D₁.disjointUnion D₂).outDir_eq_upward_iff _).mpr
      ⟨.inr e, by rw [tgt_disjointUnion_inr, he]; rfl⟩
  · obtain ⟨e, he⟩ := (D₂.outDir_eq_downward_iff j).mp h
    exact ((D₁.disjointUnion D₂).outDir_eq_downward_iff _).mpr
      ⟨.inr e, by rw [src_disjointUnion_inr, he]; rfl⟩

/-- Coupon extraction on left ports in a disjoint union. -/
@[simp]
theorem coupon?_disjointPortEquiv_inl (D₁ D₂ : DiagramIncidence.{u}) (p : D₁.Port) :
    (disjointPortEquiv D₁ D₂ (.inl p)).coupon? = Option.map Sum.inl p.coupon? := by
  cases p <;> rfl

/-- Coupon extraction on right ports in a disjoint union. -/
@[simp]
theorem coupon?_disjointPortEquiv_inr (D₁ D₂ : DiagramIncidence.{u}) (p : D₂.Port) :
    (disjointPortEquiv D₁ D₂ (.inr p)).coupon? = Option.map Sum.inr p.coupon? := by
  cases p <;> rfl

/-- Explicit cell reindexing between `(D₁.disjointUnion D₂).Cell` and `D₁.Cell ⊕ D₂.Cell`. -/
def cellDisjointUnionEquiv (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).Cell ≃ D₁.Cell ⊕ D₂.Cell where
  toFun
    | .inl (.inl (.inl c₁)) => .inl (.inl (.inl c₁))
    | .inl (.inl (.inr c₂)) => .inr (.inl (.inl c₂))
    | .inl (.inr (.inl e₁)) => .inl (.inl (.inr e₁))
    | .inl (.inr (.inr e₂)) => .inr (.inl (.inr e₂))
    | .inr (.inl k₁) => .inl (.inr k₁)
    | .inr (.inr k₂) => .inr (.inr k₂)
  invFun
    | .inl (.inl (.inl c₁)) => .inl (.inl (.inl c₁))
    | .inl (.inl (.inr e₁)) => .inl (.inr (.inl e₁))
    | .inl (.inr k₁) => .inr (.inl k₁)
    | .inr (.inl (.inl c₂)) => .inl (.inl (.inr c₂))
    | .inr (.inl (.inr e₂)) => .inl (.inr (.inr e₂))
    | .inr (.inr k₂) => .inr (.inr k₂)
  left_inv x := by rcases x with ((_ | _) | (_ | _)) | (_ | _) <;> rfl
  right_inv y := by rcases y with ((_ | _) | _) | ((_ | _) | _) <;> rfl

/-- Adjacency preservation between `(D₁.disjointUnion D₂).cellGraph` and
`D₁.cellGraph ⊕g D₂.cellGraph`. -/
theorem cellGraphDisjointUnionIso_map_rel (D₁ D₂ : DiagramIncidence.{u})
    (x y : (D₁.disjointUnion D₂).Cell) :
    (D₁.cellGraph ⊕g D₂.cellGraph).Adj
      (cellDisjointUnionEquiv D₁ D₂ x) (cellDisjointUnionEquiv D₁ D₂ y) ↔
      (D₁.disjointUnion D₂).cellGraph.Adj x y := by
  rcases x with ((c₁ | c₂) | (e₁ | e₂)) | (k₁ | k₂) <;>
    rcases y with ((c₁' | c₂') | (e₁' | e₂')) | (k₁' | k₂') <;>
    first
    | (simp [cellDisjointUnionEquiv, cellGraph, cellAdj]; done)
    | (dsimp only [cellDisjointUnionEquiv, cellGraph, cellAdj, Sum.elim_inl, Sum.elim_inr]
       simp only [Equiv.coe_fn_mk, SimpleGraph.sum_adj]
       try erw [coupon?_disjointPortEquiv_inl, coupon?_disjointPortEquiv_inl]
       try erw [coupon?_disjointPortEquiv_inr, coupon?_disjointPortEquiv_inr]
       dsimp only [disjointUnion]
       simp [Option.map_eq_some_iff, cellAdj])

/-- The cell incidence graph of `D₁.disjointUnion D₂` is canonically isomorphic to the disjoint sum
graph `D₁.cellGraph ⊕g D₂.cellGraph`. -/
def cellGraphDisjointUnionIso (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).cellGraph ≃g D₁.cellGraph ⊕g D₂.cellGraph where
  toEquiv := cellDisjointUnionEquiv D₁ D₂
  map_rel_iff' := cellGraphDisjointUnionIso_map_rel D₁ D₂ _ _

/-- Canonical equivalence between the connected components of `D₁.disjointUnion D₂` and the sum of
connected components of `D₁` and `D₂`. -/
def connectedComponentDisjointUnionEquiv (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).ConnectedComponent ≃
      D₁.ConnectedComponent ⊕ D₂.ConnectedComponent :=
  (cellGraphDisjointUnionIso D₁ D₂).connectedComponentEquiv.trans
    (SimpleGraph.connectedComponentSumEquiv D₁.cellGraph D₂.cellGraph)

/-- Disjoint union adds connected component counts. -/
@[simp]
theorem componentCount_disjointUnion (D₁ D₂ : DiagramIncidence.{u}) :
    (D₁.disjointUnion D₂).componentCount = D₁.componentCount + D₂.componentCount := by
  unfold componentCount
  rw [Fintype.card_congr (connectedComponentDisjointUnionEquiv D₁ D₂), Fintype.card_sum]

/-- Functoriality of `disjointUnion` along diagram isomorphisms. -/
def Iso.disjointUnion {D₁ D₂ : DiagramIncidence.{u}} {D₁' D₂' : DiagramIncidence.{v}}
    (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂') :
    (D₁.disjointUnion D₂).Iso (D₁'.disjointUnion D₂') where
  inPort := φ₁.inPort.sumLexCongr φ₂.inPort
  outPort := φ₁.outPort.sumLexCongr φ₂.outPort
  coupon := φ₁.coupon.sumCongr φ₂.coupon
  couponIn := Sum.rec φ₁.couponIn φ₂.couponIn
  couponOut := Sum.rec φ₁.couponOut φ₂.couponOut
  edge := φ₁.edge.sumCongr φ₂.edge
  circle := φ₁.circle.sumCongr φ₂.circle
  map_src
    | .inl e₁ => by
      dsimp only [DiagramIncidence.disjointUnion]; erw [Equiv.sumCongr_apply]
      dsimp only [Sum.map_inl, Sum.elim_inl]; rw [φ₁.map_src']; cases D₁.src e₁ <;> rfl
    | .inr e₂ => by
      dsimp only [DiagramIncidence.disjointUnion]; erw [Equiv.sumCongr_apply]
      dsimp only [Sum.map_inr, Sum.elim_inr]; rw [φ₂.map_src']; cases D₂.src e₂ <;> rfl
  map_tgt
    | .inl e₁ => by
      dsimp only [DiagramIncidence.disjointUnion]; erw [Equiv.sumCongr_apply]
      dsimp only [Sum.map_inl, Sum.elim_inl]; rw [φ₁.map_tgt']; cases D₁.tgt e₁ <;> rfl
    | .inr e₂ => by
      dsimp only [DiagramIncidence.disjointUnion]; erw [Equiv.sumCongr_apply]
      dsimp only [Sum.map_inr, Sum.elim_inr]; rw [φ₂.map_tgt']; cases D₂.tgt e₂ <;> rfl

/-- Left unitor isomorphism `(empty.disjointUnion D).Iso D`. -/
def emptyDisjointUnionIso (D : DiagramIncidence.{u}) : (empty.disjointUnion D).Iso D where
  inPort := OrderIso.emptySumLex
  outPort := OrderIso.emptySumLex
  coupon := Equiv.emptySum PEmpty D.Coupon
  couponIn
    | .inl c => c.elim
    | .inr c => OrderIso.refl (D.CouponIn c)
  couponOut
    | .inl c => c.elim
    | .inr c => OrderIso.refl (D.CouponOut c)
  edge := Equiv.emptySum PEmpty D.Edge
  circle := Equiv.emptySum PEmpty D.Circle
  map_src
    | .inl e => e.elim
    | .inr e => by
      dsimp only [disjointUnion]; erw [Equiv.emptySum_apply_inr]
      dsimp only [Sum.elim_inr]; cases D.src e <;> rfl
  map_tgt
    | .inl e => e.elim
    | .inr e => by
      dsimp only [disjointUnion]; erw [Equiv.emptySum_apply_inr]
      dsimp only [Sum.elim_inr]; cases D.tgt e <;> rfl

/-- Right unitor isomorphism `(D.disjointUnion empty).Iso D`. -/
def disjointUnionEmptyIso (D : DiagramIncidence.{u}) : (D.disjointUnion empty).Iso D where
  inPort := OrderIso.sumLexEmpty
  outPort := OrderIso.sumLexEmpty
  coupon := Equiv.sumEmpty D.Coupon PEmpty
  couponIn
    | .inl c => OrderIso.refl (D.CouponIn c)
    | .inr c => c.elim
  couponOut
    | .inl c => OrderIso.refl (D.CouponOut c)
    | .inr c => c.elim
  edge := Equiv.sumEmpty D.Edge PEmpty
  circle := Equiv.sumEmpty D.Circle PEmpty
  map_src
    | .inl e => by
      dsimp only [disjointUnion]; erw [Equiv.sumEmpty_apply_inl]
      dsimp only [Sum.elim_inl]; cases D.src e <;> rfl
    | .inr e => e.elim
  map_tgt
    | .inl e => by
      dsimp only [disjointUnion]; erw [Equiv.sumEmpty_apply_inl]
      dsimp only [Sum.elim_inl]; cases D.tgt e <;> rfl
    | .inr e => e.elim

/-- Associator isomorphism for horizontal disjoint union. -/
def disjointUnionAssocIso (D₁ D₂ D₃ : DiagramIncidence.{u}) :
    ((D₁.disjointUnion D₂).disjointUnion D₃).Iso
      (D₁.disjointUnion (D₂.disjointUnion D₃)) where
  inPort := OrderIso.sumLexAssoc D₁.InPort D₂.InPort D₃.InPort
  outPort := OrderIso.sumLexAssoc D₁.OutPort D₂.OutPort D₃.OutPort
  coupon := Equiv.sumAssoc D₁.Coupon D₂.Coupon D₃.Coupon
  couponIn
    | .inl (.inl c₁) => OrderIso.refl (D₁.CouponIn c₁)
    | .inl (.inr c₂) => OrderIso.refl (D₂.CouponIn c₂)
    | .inr c₃ => OrderIso.refl (D₃.CouponIn c₃)
  couponOut
    | .inl (.inl c₁) => OrderIso.refl (D₁.CouponOut c₁)
    | .inl (.inr c₂) => OrderIso.refl (D₂.CouponOut c₂)
    | .inr c₃ => OrderIso.refl (D₃.CouponOut c₃)
  edge := Equiv.sumAssoc D₁.Edge D₂.Edge D₃.Edge
  circle := Equiv.sumAssoc D₁.Circle D₂.Circle D₃.Circle
  map_src
    | .inl (.inl e₁) => by
      dsimp only [disjointUnion]; erw [Equiv.sumAssoc_apply_inl_inl]
      dsimp only [Sum.elim_inl]; cases D₁.src e₁ <;> rfl
    | .inl (.inr e₂) => by
      dsimp only [disjointUnion]; erw [Equiv.sumAssoc_apply_inl_inr]
      dsimp only [Sum.elim_inl, Sum.elim_inr]; cases D₂.src e₂ <;> rfl
    | .inr e₃ => by
      dsimp only [disjointUnion]; erw [Equiv.sumAssoc_apply_inr]
      dsimp only [Sum.elim_inr]; cases D₃.src e₃ <;> rfl
  map_tgt
    | .inl (.inl e₁) => by
      dsimp only [disjointUnion]; erw [Equiv.sumAssoc_apply_inl_inl]
      dsimp only [Sum.elim_inl]; cases D₁.tgt e₁ <;> rfl
    | .inl (.inr e₂) => by
      dsimp only [disjointUnion]; erw [Equiv.sumAssoc_apply_inl_inr]
      dsimp only [Sum.elim_inl, Sum.elim_inr]; cases D₂.tgt e₂ <;> rfl
    | .inr e₃ => by
      dsimp only [disjointUnion]; erw [Equiv.sumAssoc_apply_inr]
      dsimp only [Sum.elim_inr]; cases D₃.tgt e₃ <;> rfl

end DisjointUnion

end DiagramIncidence

end TauCeti
