/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice

/-!
# Finite directed diagram incidence data

This file defines the finite combinatorial incidence carrier underlying string, braid, tangle, and
ribbon diagrams with coupons of arbitrary finite arity.

A `TauCeti.DiagramIncidence` bundles:
* finite linearly ordered boundary port types `InPort` (lower boundary) and `OutPort` (upper
  boundary);
* a finite type `Coupon` of internal coupons, each equipped with finite linearly ordered input and
  output port types `CouponIn c` and `CouponOut c`;
* a finite type `Edge` of directed interval edges whose endpoints `src`, `tgt` partition the full
  port type `DiagramPort InPort OutPort Coupon CouponIn CouponOut` via a bijection
  `Edge ⊕ Edge → Port`; and
* a finite type `Circle` of vertex-free directed circle components.

Because `Sum.elim src tgt` is bijective, every boundary or coupon port is incident to a unique
interval edge end and has a canonically determined local progression direction (`StrandDir.upward`
or `StrandDir.downward`), while empty diagrams, nullary coupons, and vertex-free circles are all
represented faithfully without free or unconstrained fields. Object labels, turning numbers, and
normal framings can be attached as additional structure over this same carrier.

## Main definitions

* `TauCeti.StrandDir`: progression direction (`upward` or `downward`) of a directed strand at a
  boundary or coupon port.
* `TauCeti.DiagramPort`: disjoint union of lower boundary ports, upper boundary ports, coupon
  input ports, and coupon output ports.
* `TauCeti.DiagramIncidence`: finite directed diagram incidence data with ordered ports, interval
  edges, and circle components.
* `TauCeti.DiagramIncidence.Iso`: universe-polymorphic structure-preserving isomorphism of
  incidence data (preserving the linear orders on boundary and coupon ports), with minimal
  extensionality (`DiagramIncidence.Iso.ext`) determined by the coupon, edge, and circle maps.
* `TauCeti.DiagramIncidence.relabel`: transport of `DiagramIncidence` along arbitrary finite
  equivalences, carrying the port linear orders across the equivalences.
* `TauCeti.DiagramIncidence.empty`, `singleCircle`, `singleCoupon`, `nullaryCoupon`, `identity`,
  `singleInterval`, `cup`, `cap`: elementary diagram constructors.

## References

* A. Joyal, R. Street, *The geometry of tensor calculus, I*, Adv. Math. **88** (1991), 55–112, §1.
* N. Yu. Reshetikhin, V. G. Turaev, *Ribbon graphs and their invariants derived from quantum
  groups*, Comm. Math. Phys. **127** (1990), 1–26, §4.2, pp. 8–9.
-/

@[expose] public section

universe u v w

namespace TauCeti

/-- Local progression direction of a directed strand at a boundary or coupon port, read from lower
boundary (`InPort`) toward upper boundary (`OutPort`). -/
inductive StrandDir : Type
  | upward : StrandDir
  | downward : StrandDir
  deriving DecidableEq

namespace StrandDir

/-- Reversing the orientation of a strand flips `upward` and `downward`. -/
def flip : StrandDir → StrandDir
  | .upward => .downward
  | .downward => .upward

/-- Flipping `upward` gives `downward`. -/
@[simp]
theorem flip_upward : flip .upward = .downward := (rfl)

/-- Flipping `downward` gives `upward`. -/
@[simp]
theorem flip_downward : flip .downward = .upward := (rfl)

/-- `StrandDir.flip` is an involution. -/
@[simp]
theorem flip_flip (d : StrandDir) : d.flip.flip = d := by
  cases d <;> rfl

/-- Equivalence between `StrandDir` and `Bool` (`upward ↦ true`, `downward ↦ false`). -/
def equivBool : StrandDir ≃ Bool where
  toFun
    | .upward => true
    | .downward => false
  invFun
    | true => .upward
    | false => .downward
  left_inv d := by cases d <;> rfl
  right_inv b := by cases b <;> rfl

/-- Finite enumeration of `StrandDir`. -/
instance instFintype : Fintype StrandDir :=
  Fintype.ofEquiv Bool equivBool.symm

/-- `StrandDir` has cardinality `2`. -/
@[simp]
theorem card : Fintype.card StrandDir = 2 := by
  rw [Fintype.card_congr equivBool, Fintype.card_bool]

end StrandDir

/-- The full port type of a diagram with lower boundary `InPort`, upper boundary `OutPort`, coupons
`Coupon`, and coupon input/output port families `CouponIn`, `CouponOut`. -/
inductive DiagramPort (InPort OutPort Coupon : Type u)
    (CouponIn CouponOut : Coupon → Type u) : Type u
  | inBound : InPort → DiagramPort InPort OutPort Coupon CouponIn CouponOut
  | outBound : OutPort → DiagramPort InPort OutPort Coupon CouponIn CouponOut
  | couponIn (c : Coupon) : CouponIn c → DiagramPort InPort OutPort Coupon CouponIn CouponOut
  | couponOut (c : Coupon) : CouponOut c → DiagramPort InPort OutPort Coupon CouponIn CouponOut

namespace DiagramPort

variable {InPort OutPort Coupon : Type u} {CouponIn CouponOut : Coupon → Type u}

/-- The coupon to which a port is attached, or `none` if the port lies on the external boundary. -/
def coupon? : DiagramPort InPort OutPort Coupon CouponIn CouponOut → Option Coupon
  | .inBound _ | .outBound _ => none
  | .couponIn c _ | .couponOut c _ => some c

@[simp] theorem coupon?_inBound (i : InPort) :
    (inBound i : DiagramPort InPort OutPort Coupon CouponIn CouponOut).coupon? = none := (rfl)

@[simp] theorem coupon?_outBound (j : OutPort) :
    (outBound j : DiagramPort InPort OutPort Coupon CouponIn CouponOut).coupon? = none := (rfl)

@[simp] theorem coupon?_couponIn (c : Coupon) (i : CouponIn c) :
    (couponIn c i : DiagramPort InPort OutPort Coupon CouponIn CouponOut).coupon? = some c := (rfl)

@[simp] theorem coupon?_couponOut (c : Coupon) (j : CouponOut c) :
    (couponOut c j : DiagramPort InPort OutPort Coupon CouponIn CouponOut).coupon? = some c := (rfl)

/-- Whether a port lies on the external boundary (`inBound` or `outBound`). -/
def isBoundary : DiagramPort InPort OutPort Coupon CouponIn CouponOut → Bool
  | .inBound _ | .outBound _ => true
  | .couponIn _ _ | .couponOut _ _ => false

@[simp] theorem isBoundary_inBound (i : InPort) :
    (inBound i : DiagramPort InPort OutPort Coupon CouponIn CouponOut).isBoundary = true := (rfl)

@[simp] theorem isBoundary_outBound (j : OutPort) :
    (outBound j : DiagramPort InPort OutPort Coupon CouponIn CouponOut).isBoundary = true := (rfl)

@[simp] theorem isBoundary_couponIn (c : Coupon) (i : CouponIn c) :
    (couponIn c i : DiagramPort InPort OutPort Coupon CouponIn CouponOut).isBoundary = false :=
  (rfl)

@[simp] theorem isBoundary_couponOut (c : Coupon) (j : CouponOut c) :
    (couponOut c j : DiagramPort InPort OutPort Coupon CouponIn CouponOut).isBoundary = false :=
  (rfl)

/-- Canonical decomposition of `DiagramPort` as a sum of boundary ports and sigma types of coupon
ports. -/
def equivSum :
    DiagramPort InPort OutPort Coupon CouponIn CouponOut ≃
      (InPort ⊕ OutPort) ⊕ ((Σ c, CouponIn c) ⊕ (Σ c, CouponOut c)) where
  toFun
    | .inBound i => .inl (.inl i)
    | .outBound j => .inl (.inr j)
    | .couponIn c i => .inr (.inl ⟨c, i⟩)
    | .couponOut c j => .inr (.inr ⟨c, j⟩)
  invFun
    | .inl (.inl i) => .inBound i
    | .inl (.inr j) => .outBound j
    | .inr (.inl ⟨c, i⟩) => .couponIn c i
    | .inr (.inr ⟨c, j⟩) => .couponOut c j
  left_inv p := by cases p <;> rfl
  right_inv s := by rcases s with (i | j) | (⟨c, i⟩ | ⟨c, j⟩) <;> rfl

/-- Finite enumeration of `DiagramPort` from finiteness of its component port and coupon types. -/
instance instFintype [Fintype InPort] [Fintype OutPort] [Fintype Coupon]
    [∀ c, Fintype (CouponIn c)] [∀ c, Fintype (CouponOut c)] :
    Fintype (DiagramPort InPort OutPort Coupon CouponIn CouponOut) :=
  Fintype.ofEquiv _ equivSum.symm

/-- Decidable equality on `DiagramPort` from decidable equality on its component types. -/
instance instDecidableEq [DecidableEq InPort] [DecidableEq OutPort] [DecidableEq Coupon]
    [∀ c, DecidableEq (CouponIn c)] [∀ c, DecidableEq (CouponOut c)] :
    DecidableEq (DiagramPort InPort OutPort Coupon CouponIn CouponOut) :=
  equivSum.decidableEq

/-- Functorial equivalence on `DiagramPort` induced by equivalences on boundary ports, coupons, and
fiberwise coupon ports. -/
def congr {InPort₂ OutPort₂ Coupon₂ : Type v} {CouponIn₂ CouponOut₂ : Coupon₂ → Type v}
    (eIn : InPort ≃ InPort₂) (eOut : OutPort ≃ OutPort₂) (eC : Coupon ≃ Coupon₂)
    (eCIn : ∀ c, CouponIn c ≃ CouponIn₂ (eC c))
    (eCOut : ∀ c, CouponOut c ≃ CouponOut₂ (eC c)) :
    DiagramPort InPort OutPort Coupon CouponIn CouponOut ≃
      DiagramPort InPort₂ OutPort₂ Coupon₂ CouponIn₂ CouponOut₂ :=
  equivSum.trans <|
    ((eIn.sumCongr eOut).sumCongr ((eC.sigmaCongr eCIn).sumCongr (eC.sigmaCongr eCOut))).trans
      equivSum.symm

@[simp]
theorem congr_inBound {InPort₂ OutPort₂ Coupon₂ : Type v} {CouponIn₂ CouponOut₂ : Coupon₂ → Type v}
    (eIn : InPort ≃ InPort₂) (eOut : OutPort ≃ OutPort₂) (eC : Coupon ≃ Coupon₂)
    (eCIn : ∀ c, CouponIn c ≃ CouponIn₂ (eC c))
    (eCOut : ∀ c, CouponOut c ≃ CouponOut₂ (eC c)) (i : InPort) :
    congr eIn eOut eC eCIn eCOut (.inBound i) = .inBound (eIn i) := (rfl)

@[simp]
theorem congr_outBound {InPort₂ OutPort₂ Coupon₂ : Type v} {CouponIn₂ CouponOut₂ : Coupon₂ → Type v}
    (eIn : InPort ≃ InPort₂) (eOut : OutPort ≃ OutPort₂) (eC : Coupon ≃ Coupon₂)
    (eCIn : ∀ c, CouponIn c ≃ CouponIn₂ (eC c))
    (eCOut : ∀ c, CouponOut c ≃ CouponOut₂ (eC c)) (j : OutPort) :
    congr eIn eOut eC eCIn eCOut (.outBound j) = .outBound (eOut j) := (rfl)

@[simp]
theorem congr_couponIn {InPort₂ OutPort₂ Coupon₂ : Type v} {CouponIn₂ CouponOut₂ : Coupon₂ → Type v}
    (eIn : InPort ≃ InPort₂) (eOut : OutPort ≃ OutPort₂) (eC : Coupon ≃ Coupon₂)
    (eCIn : ∀ c, CouponIn c ≃ CouponIn₂ (eC c))
    (eCOut : ∀ c, CouponOut c ≃ CouponOut₂ (eC c)) (c : Coupon) (i : CouponIn c) :
    congr eIn eOut eC eCIn eCOut (.couponIn c i) = .couponIn (eC c) (eCIn c i) := (rfl)

@[simp]
theorem congr_couponOut {InPort₂ OutPort₂ Coupon₂ : Type v}
    {CouponIn₂ CouponOut₂ : Coupon₂ → Type v}
    (eIn : InPort ≃ InPort₂) (eOut : OutPort ≃ OutPort₂) (eC : Coupon ≃ Coupon₂)
    (eCIn : ∀ c, CouponIn c ≃ CouponIn₂ (eC c))
    (eCOut : ∀ c, CouponOut c ≃ CouponOut₂ (eC c)) (c : Coupon) (j : CouponOut c) :
    congr eIn eOut eC eCIn eCOut (.couponOut c j) = .couponOut (eC c) (eCOut c j) := (rfl)

@[simp]
theorem coupon?_congr {InPort₂ OutPort₂ Coupon₂ : Type v} {CouponIn₂ CouponOut₂ : Coupon₂ → Type v}
    (eIn : InPort ≃ InPort₂) (eOut : OutPort ≃ OutPort₂) (eC : Coupon ≃ Coupon₂)
    (eCIn : ∀ c, CouponIn c ≃ CouponIn₂ (eC c))
    (eCOut : ∀ c, CouponOut c ≃ CouponOut₂ (eC c))
    (p : DiagramPort InPort OutPort Coupon CouponIn CouponOut) :
    (congr eIn eOut eC eCIn eCOut p).coupon? = p.coupon?.map eC := by
  cases p <;> rfl

end DiagramPort

/-- **Finite directed diagram incidence data**: finite linearly ordered boundary and coupon port
types together with directed interval edges partitioning the ports and vertex-free circle
components. -/
structure DiagramIncidence : Type (u + 1) where
  /-- Lower boundary port type. -/
  InPort : Type u
  /-- Upper boundary port type. -/
  OutPort : Type u
  /-- Internal coupon type. -/
  Coupon : Type u
  /-- Input port family of each coupon. -/
  CouponIn : Coupon → Type u
  /-- Output port family of each coupon. -/
  CouponOut : Coupon → Type u
  /-- Directed interval edge type. -/
  Edge : Type u
  /-- Vertex-free directed circle component type. -/
  Circle : Type u
  [instFintypeInPort : Fintype InPort]
  [instFintypeOutPort : Fintype OutPort]
  [instFintypeCoupon : Fintype Coupon]
  [instFintypeCouponIn : ∀ c, Fintype (CouponIn c)]
  [instFintypeCouponOut : ∀ c, Fintype (CouponOut c)]
  [instFintypeEdge : Fintype Edge]
  [instFintypeCircle : Fintype Circle]
  [instLinearOrderInPort : LinearOrder InPort]
  [instLinearOrderOutPort : LinearOrder OutPort]
  [instLinearOrderCouponIn : ∀ c, LinearOrder (CouponIn c)]
  [instLinearOrderCouponOut : ∀ c, LinearOrder (CouponOut c)]
  [instDecidableEqCoupon : DecidableEq Coupon]
  [instDecidableEqEdge : DecidableEq Edge]
  [instDecidableEqCircle : DecidableEq Circle]
  /-- Initial port of each directed interval edge. -/
  src : Edge → DiagramPort InPort OutPort Coupon CouponIn CouponOut
  /-- Terminal port of each directed interval edge. -/
  tgt : Edge → DiagramPort InPort OutPort Coupon CouponIn CouponOut
  /-- Every port is the initial or terminal port of a unique interval edge end. -/
  bijective_sumElim_src_tgt : Function.Bijective (Sum.elim src tgt)

attribute [instance]
  DiagramIncidence.instFintypeInPort
  DiagramIncidence.instFintypeOutPort
  DiagramIncidence.instFintypeCoupon
  DiagramIncidence.instFintypeCouponIn
  DiagramIncidence.instFintypeCouponOut
  DiagramIncidence.instFintypeEdge
  DiagramIncidence.instFintypeCircle
  DiagramIncidence.instLinearOrderInPort
  DiagramIncidence.instLinearOrderOutPort
  DiagramIncidence.instLinearOrderCouponIn
  DiagramIncidence.instLinearOrderCouponOut
  DiagramIncidence.instDecidableEqCoupon
  DiagramIncidence.instDecidableEqEdge
  DiagramIncidence.instDecidableEqCircle

namespace DiagramIncidence

variable (D : DiagramIncidence.{u})

/-- The combined port type of `D`. -/
abbrev Port : Type u :=
  DiagramPort D.InPort D.OutPort D.Coupon D.CouponIn D.CouponOut

/-- Computable bijection matching edge sources (`Sum.inl e`) and edge targets (`Sum.inr e`) with
the ports of `D`. -/
def endpointEquiv : D.Edge ⊕ D.Edge ≃ D.Port where
  toFun := Sum.elim D.src D.tgt
  invFun := Fintype.bijInv D.bijective_sumElim_src_tgt
  left_inv := Fintype.leftInverse_bijInv D.bijective_sumElim_src_tgt
  right_inv := Fintype.rightInverse_bijInv D.bijective_sumElim_src_tgt

@[simp]
theorem endpointEquiv_inl (e : D.Edge) : D.endpointEquiv (.inl e) = D.src e := (rfl)

@[simp]
theorem endpointEquiv_inr (e : D.Edge) : D.endpointEquiv (.inr e) = D.tgt e := (rfl)

@[simp]
theorem endpointEquiv_symm_src (e : D.Edge) : D.endpointEquiv.symm (D.src e) = .inl e :=
  D.endpointEquiv.symm_apply_eq.mpr rfl

@[simp]
theorem endpointEquiv_symm_tgt (e : D.Edge) : D.endpointEquiv.symm (D.tgt e) = .inr e :=
  D.endpointEquiv.symm_apply_eq.mpr rfl

/-- Distinct interval edges have distinct initial ports. -/
theorem src_injective : Function.Injective D.src := fun _ _ h =>
  Sum.inl.inj (D.endpointEquiv.injective h)

/-- Distinct interval edges have distinct terminal ports. -/
theorem tgt_injective : Function.Injective D.tgt := fun _ _ h =>
  Sum.inr.inj (D.endpointEquiv.injective h)

/-- No port is simultaneously the initial port of an edge and the terminal port of an edge. -/
theorem src_ne_tgt (e₁ e₂ : D.Edge) : D.src e₁ ≠ D.tgt e₂ := fun h =>
  Sum.inl_ne_inr (D.endpointEquiv.injective h)

/-- The unique interval edge incident to a port `p : D.Port`. -/
def edgeAt (p : D.Port) : D.Edge :=
  Sum.elim id id (D.endpointEquiv.symm p)

@[simp]
theorem edgeAt_src (e : D.Edge) : D.edgeAt (D.src e) = e := by
  simp [edgeAt]

@[simp]
theorem edgeAt_tgt (e : D.Edge) : D.edgeAt (D.tgt e) = e := by
  simp [edgeAt]

/-- Local progression direction of the strand at port `p`: upward strands leave `inBound` and
`couponOut` ports as `src` and arrive at `outBound` and `couponIn` ports as `tgt`; downward strands
do the opposite. -/
def portDir (p : D.Port) : StrandDir :=
  match p, D.endpointEquiv.symm p with
  | .inBound _, .inl _ | .couponOut _ _, .inl _ => .upward
  | .inBound _, .inr _ | .couponOut _ _, .inr _ => .downward
  | .outBound _, .inr _ | .couponIn _ _, .inr _ => .upward
  | .outBound _, .inl _ | .couponIn _ _, .inl _ => .downward

/-- Strand progression direction at a lower boundary port. -/
def inDir (i : D.InPort) : StrandDir :=
  D.portDir (.inBound i)

/-- Strand progression direction at an upper boundary port. -/
def outDir (j : D.OutPort) : StrandDir :=
  D.portDir (.outBound j)

/-- Strand progression direction at a coupon input port. -/
def couponInDir (c : D.Coupon) (i : D.CouponIn c) : StrandDir :=
  D.portDir (.couponIn c i)

/-- Strand progression direction at a coupon output port. -/
def couponOutDir (c : D.Coupon) (j : D.CouponOut c) : StrandDir :=
  D.portDir (.couponOut c j)

/-- At a lower boundary port `i`, `D.inDir i = .upward` iff `.inBound i` is an edge source. -/
theorem inDir_eq_upward_iff (i : D.InPort) :
    D.inDir i = .upward ↔ ∃ e : D.Edge, D.src e = .inBound i := by
  unfold inDir portDir
  rcases h : D.endpointEquiv.symm (.inBound i) with e | e
  · exact ⟨fun _ => ⟨e, D.endpointEquiv.eq_symm_apply.mp h.symm⟩, fun _ => rfl⟩
  · constructor
    · intro hdir; cases hdir
    · rintro ⟨e', he'⟩
      have h' := D.endpointEquiv_symm_src e'
      rw [he', h] at h'
      cases h'

/-- At a lower boundary port `i`, `D.inDir i = .downward` iff `.inBound i` is an edge target. -/
theorem inDir_eq_downward_iff (i : D.InPort) :
    D.inDir i = .downward ↔ ∃ e : D.Edge, D.tgt e = .inBound i := by
  unfold inDir portDir
  rcases h : D.endpointEquiv.symm (.inBound i) with e | e
  · constructor
    · intro hdir; cases hdir
    · rintro ⟨e', he'⟩
      have h' := D.endpointEquiv_symm_tgt e'
      rw [he', h] at h'
      cases h'
  · exact ⟨fun _ => ⟨e, D.endpointEquiv.eq_symm_apply.mp h.symm⟩, fun _ => rfl⟩

/-- At an upper boundary port `j`, `D.outDir j = .upward` iff `.outBound j` is an edge target. -/
theorem outDir_eq_upward_iff (j : D.OutPort) :
    D.outDir j = .upward ↔ ∃ e : D.Edge, D.tgt e = .outBound j := by
  unfold outDir portDir
  rcases h : D.endpointEquiv.symm (.outBound j) with e | e
  · constructor
    · intro hdir; cases hdir
    · rintro ⟨e', he'⟩
      have h' := D.endpointEquiv_symm_tgt e'
      rw [he', h] at h'
      cases h'
  · exact ⟨fun _ => ⟨e, D.endpointEquiv.eq_symm_apply.mp h.symm⟩, fun _ => rfl⟩

/-- At an upper boundary port `j`, `D.outDir j = .downward` iff `.outBound j` is an edge source. -/
theorem outDir_eq_downward_iff (j : D.OutPort) :
    D.outDir j = .downward ↔ ∃ e : D.Edge, D.src e = .outBound j := by
  unfold outDir portDir
  rcases h : D.endpointEquiv.symm (.outBound j) with e | e
  · exact ⟨fun _ => ⟨e, D.endpointEquiv.eq_symm_apply.mp h.symm⟩, fun _ => rfl⟩
  · constructor
    · intro hdir; cases hdir
    · rintro ⟨e', he'⟩
      have h' := D.endpointEquiv_symm_src e'
      rw [he', h] at h'
      cases h'

/-- Number of interval edges in `D`. -/
def edgeCount : ℕ := Fintype.card D.Edge

/-- Number of vertex-free circle components in `D`. -/
def circleCount : ℕ := Fintype.card D.Circle

/-- Number of internal coupons in `D`. -/
def couponCount : ℕ := Fintype.card D.Coupon

/-- Total number of boundary and coupon ports in `D`. -/
def portCount : ℕ := Fintype.card D.Port

/-- Every interval edge contributes exactly two ports (its source and its target). -/
theorem two_mul_edgeCount_eq_portCount : 2 * D.edgeCount = D.portCount := by
  unfold edgeCount portCount
  rw [← Fintype.card_congr D.endpointEquiv, Fintype.card_sum]
  omega

/-! ### Structure-preserving isomorphisms -/

/-- Universe-polymorphic isomorphism of diagram incidence data, preserving linear orders on all
boundary and coupon port types, equivalences on coupons, edges, and circles, and edge endpoints. -/
structure Iso (D₁ : DiagramIncidence.{u}) (D₂ : DiagramIncidence.{v}) where
  /-- Order isomorphism on lower boundary ports. -/
  inPort : D₁.InPort ≃o D₂.InPort
  /-- Order isomorphism on upper boundary ports. -/
  outPort : D₁.OutPort ≃o D₂.OutPort
  /-- Bijection on coupons. -/
  coupon : D₁.Coupon ≃ D₂.Coupon
  /-- Fiberwise order isomorphism on coupon input ports. -/
  couponIn : ∀ c, D₁.CouponIn c ≃o D₂.CouponIn (coupon c)
  /-- Fiberwise order isomorphism on coupon output ports. -/
  couponOut : ∀ c, D₁.CouponOut c ≃o D₂.CouponOut (coupon c)
  /-- Bijection on directed interval edges. -/
  edge : D₁.Edge ≃ D₂.Edge
  /-- Bijection on vertex-free circle components. -/
  circle : D₁.Circle ≃ D₂.Circle
  /-- Compatibility with initial ports of interval edges. -/
  map_src : ∀ e, D₂.src (edge e) =
    DiagramPort.congr inPort.toEquiv outPort.toEquiv coupon
      (fun c => (couponIn c).toEquiv) (fun c => (couponOut c).toEquiv) (D₁.src e)
  /-- Compatibility with terminal ports of interval edges. -/
  map_tgt : ∀ e, D₂.tgt (edge e) =
    DiagramPort.congr inPort.toEquiv outPort.toEquiv coupon
      (fun c => (couponIn c).toEquiv) (fun c => (couponOut c).toEquiv) (D₁.tgt e)

namespace Iso

variable {D : DiagramIncidence.{u}} {D₁ : DiagramIncidence.{u}} {D₂ : DiagramIncidence.{v}}
  {D₃ : DiagramIncidence.{w}}

/-- Combined equivalence on ports induced by a diagram isomorphism. -/
def portEquiv (φ : D₁.Iso D₂) : D₁.Port ≃ D₂.Port :=
  DiagramPort.congr φ.inPort.toEquiv φ.outPort.toEquiv φ.coupon
    (fun c => (φ.couponIn c).toEquiv) (fun c => (φ.couponOut c).toEquiv)

@[simp] theorem portEquiv_inBound (φ : D₁.Iso D₂) (i : D₁.InPort) :
    φ.portEquiv (.inBound i) = .inBound (φ.inPort i) := (rfl)

@[simp] theorem portEquiv_outBound (φ : D₁.Iso D₂) (j : D₁.OutPort) :
    φ.portEquiv (.outBound j) = .outBound (φ.outPort j) := (rfl)

@[simp] theorem portEquiv_couponIn (φ : D₁.Iso D₂) (c : D₁.Coupon) (i : D₁.CouponIn c) :
    φ.portEquiv (.couponIn c i) = .couponIn (φ.coupon c) (φ.couponIn c i) := (rfl)

@[simp] theorem portEquiv_couponOut (φ : D₁.Iso D₂) (c : D₁.Coupon) (j : D₁.CouponOut c) :
    φ.portEquiv (.couponOut c j) = .couponOut (φ.coupon c) (φ.couponOut c j) := (rfl)

@[simp] theorem map_src' (φ : D₁.Iso D₂) (e : D₁.Edge) :
    D₂.src (φ.edge e) = φ.portEquiv (D₁.src e) := φ.map_src e

@[simp] theorem map_tgt' (φ : D₁.Iso D₂) (e : D₁.Edge) :
    D₂.tgt (φ.edge e) = φ.portEquiv (D₁.tgt e) := φ.map_tgt e

/-- **Minimal extensionality for `DiagramIncidence.Iso`**: because every port is an endpoint of an
interval edge, an isomorphism is uniquely determined by its action on coupons, edges, and circles
alone. -/
@[ext]
theorem ext {φ ψ : D₁.Iso D₂}
    (hcoupon : ∀ c, φ.coupon c = ψ.coupon c)
    (hedge : ∀ e, φ.edge e = ψ.edge e)
    (hcircle : ∀ o, φ.circle o = ψ.circle o) : φ = ψ := by
  have hport : ∀ p : D₁.Port, φ.portEquiv p = ψ.portEquiv p := by
    intro p
    obtain ⟨e | e, rfl⟩ := D₁.endpointEquiv.surjective p
    · rw [endpointEquiv_inl, ← φ.map_src', ← ψ.map_src', hedge e]
    · rw [endpointEquiv_inr, ← φ.map_tgt', ← ψ.map_tgt', hedge e]
  have hin : φ.inPort = ψ.inPort := OrderIso.ext <| funext fun i => by
    have hi := congrArg DiagramPort.equivSum (hport (.inBound i))
    exact Sum.inl.inj (Sum.inl.inj hi)
  have hout : φ.outPort = ψ.outPort := OrderIso.ext <| funext fun j => by
    have hj := congrArg DiagramPort.equivSum (hport (.outBound j))
    exact Sum.inr.inj (Sum.inl.inj hj)
  have hc : φ.coupon = ψ.coupon := Equiv.ext hcoupon
  have he : φ.edge = ψ.edge := Equiv.ext hedge
  have ho : φ.circle = ψ.circle := Equiv.ext hcircle
  rcases φ with ⟨in₁, out₁, c₁, cin₁, cout₁, e₁, o₁, _, _⟩
  rcases ψ with ⟨in₂, out₂, c₂, cin₂, cout₂, e₂, o₂, _, _⟩
  subst hin hout hc he ho
  have hcin : cin₁ = cin₂ := funext fun c => OrderIso.ext <| funext fun i => by
    have hi := congrArg DiagramPort.equivSum (hport (.couponIn c i))
    exact eq_of_heq (Sigma.mk.inj (Sum.inl.inj (Sum.inr.inj hi))).2
  have hcout : cout₁ = cout₂ := funext fun c => OrderIso.ext <| funext fun j => by
    have hj := congrArg DiagramPort.equivSum (hport (.couponOut c j))
    exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Sum.inr.inj hj))).2
  subst hcin hcout
  rfl

/-- Identity isomorphism on `D`. -/
@[refl]
def refl (D : DiagramIncidence.{u}) : D.Iso D where
  inPort := OrderIso.refl D.InPort
  outPort := OrderIso.refl D.OutPort
  coupon := Equiv.refl D.Coupon
  couponIn c := OrderIso.refl (D.CouponIn c)
  couponOut c := OrderIso.refl (D.CouponOut c)
  edge := Equiv.refl D.Edge
  circle := Equiv.refl D.Circle
  map_src e := by dsimp; cases D.src e <;> rfl
  map_tgt e := by dsimp; cases D.tgt e <;> rfl

/-- Composition of diagram isomorphisms. -/
@[trans]
def trans (φ : D₁.Iso D₂) (ψ : D₂.Iso D₃) : D₁.Iso D₃ where
  inPort := φ.inPort.trans ψ.inPort
  outPort := φ.outPort.trans ψ.outPort
  coupon := φ.coupon.trans ψ.coupon
  couponIn c := (φ.couponIn c).trans (ψ.couponIn (φ.coupon c))
  couponOut c := (φ.couponOut c).trans (ψ.couponOut (φ.coupon c))
  edge := φ.edge.trans ψ.edge
  circle := φ.circle.trans ψ.circle
  map_src e := by
    rw [Equiv.trans_apply, ψ.map_src', φ.map_src']
    cases D₁.src e <;> rfl
  map_tgt e := by
    rw [Equiv.trans_apply, ψ.map_tgt', φ.map_tgt']
    cases D₁.tgt e <;> rfl

/-- Cast an order isomorphism along an equality of fiber indices. -/
def fiberOrderIsoCast {C : Type v} (F : C → Type v) [∀ c, LE (F c)] {c₁ c₂ : C}
    (h : c₁ = c₂) : F c₁ ≃o F c₂ :=
  h ▸ OrderIso.refl (F c₁)

private theorem coupon_symm_cast_apply {C₁ : Type u} {C₂ : Type v}
    {F₁ : C₁ → Type u} {F₂ : C₂ → Type v} [∀ c, LE (F₁ c)] [∀ c, LE (F₂ c)]
    (eC : C₁ ≃ C₂) (eF : ∀ c, F₁ c ≃o F₂ (eC c))
    {c c' : C₁} (hc : c' = c) (h₂ : eC c' = eC c) (x : F₁ c) :
    (⟨c', ((fiberOrderIsoCast F₂ h₂.symm).trans (eF c').symm) (eF c x)⟩ : Σ a, F₁ a) = ⟨c, x⟩ := by
  subst hc
  have hh : h₂ = rfl := Subsingleton.elim _ _
  subst hh
  simp [fiberOrderIsoCast]

/-- Inverse of a diagram isomorphism. -/
@[symm]
def symm (φ : D₁.Iso D₂) : D₂.Iso D₁ where
  inPort := φ.inPort.symm
  outPort := φ.outPort.symm
  coupon := φ.coupon.symm
  couponIn c₂ := (fiberOrderIsoCast D₂.CouponIn (φ.coupon.apply_symm_apply c₂).symm).trans
    (φ.couponIn (φ.coupon.symm c₂)).symm
  couponOut c₂ := (fiberOrderIsoCast D₂.CouponOut (φ.coupon.apply_symm_apply c₂).symm).trans
    (φ.couponOut (φ.coupon.symm c₂)).symm
  edge := φ.edge.symm
  circle := φ.circle.symm
  map_src e₂ := by
    have hinv : ∀ p : D₁.Port,
        DiagramPort.congr φ.inPort.symm.toEquiv φ.outPort.symm.toEquiv φ.coupon.symm
          (fun c₂ => ((fiberOrderIsoCast D₂.CouponIn (φ.coupon.apply_symm_apply c₂).symm).trans
            (φ.couponIn (φ.coupon.symm c₂)).symm).toEquiv)
          (fun c₂ => ((fiberOrderIsoCast D₂.CouponOut (φ.coupon.apply_symm_apply c₂).symm).trans
            (φ.couponOut (φ.coupon.symm c₂)).symm).toEquiv)
          (φ.portEquiv p) = p := by
      rintro (i | j | ⟨c, i⟩ | ⟨c, j⟩)
      · exact congrArg DiagramPort.inBound (φ.inPort.symm_apply_apply i)
      · exact congrArg DiagramPort.outBound (φ.outPort.symm_apply_apply j)
      · exact congrArg (fun s : Σ a, D₁.CouponIn a => DiagramPort.couponIn s.1 s.2)
          (coupon_symm_cast_apply φ.coupon φ.couponIn
            (φ.coupon.symm_apply_apply c) (φ.coupon.apply_symm_apply (φ.coupon c)) i)
      · exact congrArg (fun s : Σ a, D₁.CouponOut a => DiagramPort.couponOut s.1 s.2)
          (coupon_symm_cast_apply φ.coupon φ.couponOut
            (φ.coupon.symm_apply_apply c) (φ.coupon.apply_symm_apply (φ.coupon c)) j)
    obtain ⟨e₁, rfl⟩ := φ.edge.surjective e₂
    rw [φ.edge.symm_apply_apply, φ.map_src', hinv]
  map_tgt e₂ := by
    have hinv : ∀ p : D₁.Port,
        DiagramPort.congr φ.inPort.symm.toEquiv φ.outPort.symm.toEquiv φ.coupon.symm
          (fun c₂ => ((fiberOrderIsoCast D₂.CouponIn (φ.coupon.apply_symm_apply c₂).symm).trans
            (φ.couponIn (φ.coupon.symm c₂)).symm).toEquiv)
          (fun c₂ => ((fiberOrderIsoCast D₂.CouponOut (φ.coupon.apply_symm_apply c₂).symm).trans
            (φ.couponOut (φ.coupon.symm c₂)).symm).toEquiv)
          (φ.portEquiv p) = p := by
      rintro (i | j | ⟨c, i⟩ | ⟨c, j⟩)
      · exact congrArg DiagramPort.inBound (φ.inPort.symm_apply_apply i)
      · exact congrArg DiagramPort.outBound (φ.outPort.symm_apply_apply j)
      · exact congrArg (fun s : Σ a, D₁.CouponIn a => DiagramPort.couponIn s.1 s.2)
          (coupon_symm_cast_apply φ.coupon φ.couponIn
            (φ.coupon.symm_apply_apply c) (φ.coupon.apply_symm_apply (φ.coupon c)) i)
      · exact congrArg (fun s : Σ a, D₁.CouponOut a => DiagramPort.couponOut s.1 s.2)
          (coupon_symm_cast_apply φ.coupon φ.couponOut
            (φ.coupon.symm_apply_apply c) (φ.coupon.apply_symm_apply (φ.coupon c)) j)
    obtain ⟨e₁, rfl⟩ := φ.edge.surjective e₂
    rw [φ.edge.symm_apply_apply, φ.map_tgt', hinv]

@[simp] theorem symm_symm (φ : D₁.Iso D₂) : φ.symm.symm = φ := by ext <;> simp [symm]
@[simp] theorem self_trans_symm (φ : D₁.Iso D₂) : φ.trans φ.symm = refl D₁ := by
  ext <;> simp [trans, symm, refl]
@[simp] theorem symm_trans_self (φ : D₁.Iso D₂) : φ.symm.trans φ = refl D₂ := by
  ext <;> simp [trans, symm, refl]

/-- Diagram isomorphisms intertwine `endpointEquiv.symm`. -/
theorem endpointEquiv_symm_portEquiv (φ : D₁.Iso D₂) (p : D₁.Port) :
    D₂.endpointEquiv.symm (φ.portEquiv p) =
      φ.edge.sumCongr φ.edge (D₁.endpointEquiv.symm p) := by
  obtain ⟨e | e, rfl⟩ := D₁.endpointEquiv.surjective p
  · rw [endpointEquiv_inl, ← φ.map_src', endpointEquiv_symm_src, endpointEquiv_symm_src,
      Equiv.sumCongr_apply, Sum.map_inl]
  · rw [endpointEquiv_inr, ← φ.map_tgt', endpointEquiv_symm_tgt, endpointEquiv_symm_tgt,
      Equiv.sumCongr_apply, Sum.map_inr]

/-- Diagram isomorphisms preserve local strand progression directions at every port. -/
@[simp]
theorem portDir_portEquiv (φ : D₁.Iso D₂) (p : D₁.Port) :
    D₂.portDir (φ.portEquiv p) = D₁.portDir p := by
  unfold portDir
  rw [φ.endpointEquiv_symm_portEquiv]
  rcases p with i | j | ⟨c, i⟩ | ⟨c, j⟩ <;>
    rcases D₁.endpointEquiv.symm _ with e | e <;> rfl

@[simp]
theorem inDir_apply (φ : D₁.Iso D₂) (i : D₁.InPort) :
    D₂.inDir (φ.inPort i) = D₁.inDir i :=
  φ.portDir_portEquiv (.inBound i)

@[simp]
theorem outDir_apply (φ : D₁.Iso D₂) (j : D₁.OutPort) :
    D₂.outDir (φ.outPort j) = D₁.outDir j :=
  φ.portDir_portEquiv (.outBound j)

/-- Diagram isomorphisms preserve interval edge counts. -/
theorem edgeCount_eq (φ : D₁.Iso D₂) : D₁.edgeCount = D₂.edgeCount :=
  Fintype.card_congr φ.edge

/-- Diagram isomorphisms preserve vertex-free circle counts. -/
theorem circleCount_eq (φ : D₁.Iso D₂) : D₁.circleCount = D₂.circleCount :=
  Fintype.card_congr φ.circle

/-- Diagram isomorphisms preserve coupon counts. -/
theorem couponCount_eq (φ : D₁.Iso D₂) : D₁.couponCount = D₂.couponCount :=
  Fintype.card_congr φ.coupon

/-- Diagram isomorphisms preserve total port counts. -/
theorem portCount_eq (φ : D₁.Iso D₂) : D₁.portCount = D₂.portCount :=
  Fintype.card_congr φ.portEquiv

end Iso

/-! ### Finite relabelling with transported port order -/

section Relabel

private theorem relabel_fiber_le {C₁ : Type u} {C₂ : Type v}
    {F₁ : C₁ → Type u} {F₂ : C₂ → Type v} [∀ c, LE (F₁ c)]
    (eC : C₁ ≃ C₂) (eF : ∀ c, F₁ c ≃ F₂ (eC c))
    {c c' : C₁} (hc : c' = c) (h₂ : eC c' = eC c) (x y : F₁ c) :
    ((eF c').trans (Equiv.cast (congrArg F₂ h₂))).symm (eF c x) ≤
      ((eF c').trans (Equiv.cast (congrArg F₂ h₂))).symm (eF c y) ↔ x ≤ y := by
  subst hc
  have hh : h₂ = rfl := Subsingleton.elim _ _
  subst hh
  simp

/-- Finite relabelling of `D` along arbitrary equivalences on ports, coupons, edges, and circles,
transporting finiteness, decidable equality, and the linear orders on boundary and coupon ports
along the equivalences. -/
def relabel (D : DiagramIncidence.{u})
    {InPort' OutPort' Coupon' : Type v} {CouponIn' CouponOut' : Coupon' → Type v}
    {Edge' Circle' : Type v}
    (eIn : D.InPort ≃ InPort') (eOut : D.OutPort ≃ OutPort')
    (eCoupon : D.Coupon ≃ Coupon')
    (eCouponIn : ∀ c, D.CouponIn c ≃ CouponIn' (eCoupon c))
    (eCouponOut : ∀ c, D.CouponOut c ≃ CouponOut' (eCoupon c))
    (eEdge : D.Edge ≃ Edge') (eCircle : D.Circle ≃ Circle') : DiagramIncidence.{v} :=
  let eCIn' : ∀ c', D.CouponIn (eCoupon.symm c') ≃ CouponIn' c' := fun c' =>
    (eCouponIn (eCoupon.symm c')).trans
      (Equiv.cast (congrArg CouponIn' (eCoupon.apply_symm_apply c')))
  let eCOut' : ∀ c', D.CouponOut (eCoupon.symm c') ≃ CouponOut' c' := fun c' =>
    (eCouponOut (eCoupon.symm c')).trans
      (Equiv.cast (congrArg CouponOut' (eCoupon.apply_symm_apply c')))
  let portMap := DiagramPort.congr eIn eOut eCoupon eCouponIn eCouponOut
  { InPort := InPort'
    OutPort := OutPort'
    Coupon := Coupon'
    CouponIn := CouponIn'
    CouponOut := CouponOut'
    Edge := Edge'
    Circle := Circle'
    instFintypeInPort := Fintype.ofEquiv D.InPort eIn
    instFintypeOutPort := Fintype.ofEquiv D.OutPort eOut
    instFintypeCoupon := Fintype.ofEquiv D.Coupon eCoupon
    instFintypeCouponIn := fun c' => Fintype.ofEquiv _ (eCIn' c')
    instFintypeCouponOut := fun c' => Fintype.ofEquiv _ (eCOut' c')
    instFintypeEdge := Fintype.ofEquiv D.Edge eEdge
    instFintypeCircle := Fintype.ofEquiv D.Circle eCircle
    instLinearOrderInPort := LinearOrder.lift' eIn.symm eIn.symm.injective
    instLinearOrderOutPort := LinearOrder.lift' eOut.symm eOut.symm.injective
    instLinearOrderCouponIn := fun c' => LinearOrder.lift' (eCIn' c').symm (eCIn' c').symm.injective
    instLinearOrderCouponOut := fun c' =>
      LinearOrder.lift' (eCOut' c').symm (eCOut' c').symm.injective
    instDecidableEqCoupon := eCoupon.symm.decidableEq
    instDecidableEqEdge := eEdge.symm.decidableEq
    instDecidableEqCircle := eCircle.symm.decidableEq
    src := fun e' => portMap (D.src (eEdge.symm e'))
    tgt := fun e' => portMap (D.tgt (eEdge.symm e'))
    bijective_sumElim_src_tgt := by
      have hcomp : Sum.elim (fun e' => portMap (D.src (eEdge.symm e')))
          (fun e' => portMap (D.tgt (eEdge.symm e'))) =
            portMap ∘ Sum.elim D.src D.tgt ∘ eEdge.symm.sumCongr eEdge.symm := by
        ext (e' | e') <;> rfl
      rw [hcomp]
      exact portMap.bijective.comp
        (D.bijective_sumElim_src_tgt.comp (eEdge.symm.sumCongr eEdge.symm).bijective) }

/-- Canonical isomorphism from `D` to its finite relabelling `D.relabel ...`. -/
def relabelIso (D : DiagramIncidence.{u})
    {InPort' OutPort' Coupon' : Type v} {CouponIn' CouponOut' : Coupon' → Type v}
    {Edge' Circle' : Type v}
    (eIn : D.InPort ≃ InPort') (eOut : D.OutPort ≃ OutPort')
    (eCoupon : D.Coupon ≃ Coupon')
    (eCouponIn : ∀ c, D.CouponIn c ≃ CouponIn' (eCoupon c))
    (eCouponOut : ∀ c, D.CouponOut c ≃ CouponOut' (eCoupon c))
    (eEdge : D.Edge ≃ Edge') (eCircle : D.Circle ≃ Circle') :
    D.Iso (D.relabel eIn eOut eCoupon eCouponIn eCouponOut eEdge eCircle) where
  inPort :=
    { toEquiv := eIn
      map_rel_iff' := @fun x y => by
        dsimp only [relabel]
        -- `LinearOrder.lift' eIn.symm` defines `b₁ ≤ b₂` as `eIn.symm b₁ ≤ eIn.symm b₂`.
        change eIn.symm (eIn x) ≤ eIn.symm (eIn y) ↔ x ≤ y
        simp }
  outPort :=
    { toEquiv := eOut
      map_rel_iff' := @fun x y => by
        dsimp only [relabel]
        -- `LinearOrder.lift' eOut.symm` defines `b₁ ≤ b₂` as `eOut.symm b₁ ≤ eOut.symm b₂`.
        change eOut.symm (eOut x) ≤ eOut.symm (eOut y) ↔ x ≤ y
        simp }
  coupon := eCoupon
  couponIn c :=
    { toEquiv := eCouponIn c
      map_rel_iff' := @fun i₁ i₂ => by
        dsimp only [relabel]
        exact relabel_fiber_le eCoupon eCouponIn
          (eCoupon.symm_apply_apply c) (eCoupon.apply_symm_apply (eCoupon c)) i₁ i₂ }
  couponOut c :=
    { toEquiv := eCouponOut c
      map_rel_iff' := @fun j₁ j₂ => by
        dsimp only [relabel]
        exact relabel_fiber_le eCoupon eCouponOut
          (eCoupon.symm_apply_apply c) (eCoupon.apply_symm_apply (eCoupon c)) j₁ j₂ }
  edge := eEdge
  circle := eCircle
  map_src e :=
    congrArg (DiagramPort.congr eIn eOut eCoupon eCouponIn eCouponOut ∘ D.src)
      (eEdge.symm_apply_apply e)
  map_tgt e :=
    congrArg (DiagramPort.congr eIn eOut eCoupon eCouponIn eCouponOut ∘ D.tgt)
      (eEdge.symm_apply_apply e)

end Relabel

/-! ### Elementary diagram constructors -/

/-- The empty diagram: zero ports, zero coupons, zero interval edges, and zero circle components. -/
def empty : DiagramIncidence.{u} where
  InPort := PEmpty
  OutPort := PEmpty
  Coupon := PEmpty
  CouponIn _ := PEmpty
  CouponOut _ := PEmpty
  Edge := PEmpty
  Circle := PEmpty
  src := PEmpty.elim
  tgt := PEmpty.elim
  bijective_sumElim_src_tgt :=
    ⟨fun x _ _ => by rcases x with e | e <;> exact e.elim,
      fun p => by
        rcases p with i | j | ⟨c, _⟩ | ⟨c, _⟩
        exacts [i.elim, j.elim, c.elim, c.elim]⟩

@[simp] theorem edgeCount_empty : (empty.{u}).edgeCount = 0 := by
  dsimp [edgeCount, empty]; exact Fintype.card_eq_zero
@[simp] theorem couponCount_empty : (empty.{u}).couponCount = 0 := by
  dsimp [couponCount, empty]; exact Fintype.card_eq_zero
@[simp] theorem circleCount_empty : (empty.{u}).circleCount = 0 := by
  dsimp [circleCount, empty]; exact Fintype.card_eq_zero
@[simp] theorem portCount_empty : (empty.{u}).portCount = 0 := by
  rw [← two_mul_edgeCount_eq_portCount, edgeCount_empty]

/-- A single vertex-free closed loop: zero boundary or coupon ports, zero coupons, zero interval
edges, and one circle component. -/
def singleCircle : DiagramIncidence.{u} where
  InPort := PEmpty
  OutPort := PEmpty
  Coupon := PEmpty
  CouponIn _ := PEmpty
  CouponOut _ := PEmpty
  Edge := PEmpty
  Circle := PUnit
  src := PEmpty.elim
  tgt := PEmpty.elim
  bijective_sumElim_src_tgt :=
    ⟨fun x _ _ => by rcases x with e | e <;> exact e.elim,
      fun p => by
        rcases p with i | j | ⟨c, _⟩ | ⟨c, _⟩
        exacts [i.elim, j.elim, c.elim, c.elim]⟩

@[simp] theorem edgeCount_singleCircle : (singleCircle.{u}).edgeCount = 0 := by
  dsimp [edgeCount, singleCircle]; exact Fintype.card_eq_zero
@[simp] theorem couponCount_singleCircle : (singleCircle.{u}).couponCount = 0 := by
  dsimp [couponCount, singleCircle]; exact Fintype.card_eq_zero
@[simp] theorem circleCount_singleCircle : (singleCircle.{u}).circleCount = 1 := (rfl)
@[simp] theorem portCount_singleCircle : (singleCircle.{u}).portCount = 0 := by
  rw [← two_mul_edgeCount_eq_portCount, edgeCount_singleCircle]

/-- Elementary diagram with a single coupon of input arity `InP` and output arity `OutP` connected
by radial interval edges to matching lower and upper boundary ports with prescribed strand
directions. -/
def singleCoupon (InP OutP : Type u) [Fintype InP] [Fintype OutP]
    [LinearOrder InP] [LinearOrder OutP]
    (inDir : InP → StrandDir) (outDir : OutP → StrandDir) : DiagramIncidence.{u} where
  InPort := InP
  OutPort := OutP
  Coupon := PUnit
  CouponIn _ := InP
  CouponOut _ := OutP
  Edge := InP ⊕ OutP
  Circle := PEmpty
  src
    | .inl i => match inDir i with
      | .upward => .inBound i
      | .downward => .couponIn PUnit.unit i
    | .inr j => match outDir j with
      | .upward => .couponOut PUnit.unit j
      | .downward => .outBound j
  tgt
    | .inl i => match inDir i with
      | .upward => .couponIn PUnit.unit i
      | .downward => .inBound i
    | .inr j => match outDir j with
      | .upward => .outBound j
      | .downward => .couponOut PUnit.unit j
  bijective_sumElim_src_tgt := by
    let inv : DiagramPort InP OutP PUnit (fun _ => InP) (fun _ => OutP) →
        (InP ⊕ OutP) ⊕ (InP ⊕ OutP) := fun
      | .inBound i => match inDir i with
        | .upward => .inl (.inl i)
        | .downward => .inr (.inl i)
      | .outBound j => match outDir j with
        | .upward => .inr (.inr j)
        | .downward => .inl (.inr j)
      | .couponIn _ i => match inDir i with
        | .upward => .inr (.inl i)
        | .downward => .inl (.inl i)
      | .couponOut _ j => match outDir j with
        | .upward => .inl (.inr j)
        | .downward => .inr (.inr j)
    refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
    · rintro ((i | j) | (i | j))
      · cases h : inDir i <;> simp [inv, h]
      · cases h : outDir j <;> simp [inv, h]
      · cases h : inDir i <;> simp [inv, h]
      · cases h : outDir j <;> simp [inv, h]
    · rintro (i | j | ⟨⟨⟩, i⟩ | ⟨⟨⟩, j⟩)
      · cases h : inDir i <;> simp [inv, h]
      · cases h : outDir j <;> simp [inv, h]
      · cases h : inDir i <;> simp [inv, h]
      · cases h : outDir j <;> simp [inv, h]

@[simp]
theorem couponCount_singleCoupon (InP OutP : Type u) [Fintype InP] [Fintype OutP]
    [LinearOrder InP] [LinearOrder OutP] (inDir : InP → StrandDir) (outDir : OutP → StrandDir) :
    (singleCoupon InP OutP inDir outDir).couponCount = 1 := (rfl)

@[simp]
theorem circleCount_singleCoupon (InP OutP : Type u) [Fintype InP] [Fintype OutP]
    [LinearOrder InP] [LinearOrder OutP] (inDir : InP → StrandDir) (outDir : OutP → StrandDir) :
    (singleCoupon InP OutP inDir outDir).circleCount = 0 := by
  dsimp [circleCount, singleCoupon]; exact Fintype.card_eq_zero

@[simp]
theorem edgeCount_singleCoupon (InP OutP : Type u) [Fintype InP] [Fintype OutP]
    [LinearOrder InP] [LinearOrder OutP] (inDir : InP → StrandDir) (outDir : OutP → StrandDir) :
    (singleCoupon InP OutP inDir outDir).edgeCount = Fintype.card InP + Fintype.card OutP := by
  dsimp [edgeCount, singleCoupon]; exact Fintype.card_sum

@[simp]
theorem inDir_singleCoupon (InP OutP : Type u) [Fintype InP] [Fintype OutP]
    [LinearOrder InP] [LinearOrder OutP] (inD : InP → StrandDir) (outD : OutP → StrandDir)
    (i : InP) : (singleCoupon InP OutP inD outD).inDir i = inD i := by
  cases h : inD i
  · exact ((singleCoupon InP OutP inD outD).inDir_eq_upward_iff i).mpr
      ⟨.inl i, by simp [singleCoupon, h]⟩
  · exact ((singleCoupon InP OutP inD outD).inDir_eq_downward_iff i).mpr
      ⟨.inl i, by simp [singleCoupon, h]⟩

@[simp]
theorem outDir_singleCoupon (InP OutP : Type u) [Fintype InP] [Fintype OutP]
    [LinearOrder InP] [LinearOrder OutP] (inD : InP → StrandDir) (outD : OutP → StrandDir)
    (j : OutP) : (singleCoupon InP OutP inD outD).outDir j = outD j := by
  cases h : outD j
  · exact ((singleCoupon InP OutP inD outD).outDir_eq_upward_iff j).mpr
      ⟨.inr j, by simp [singleCoupon, h]⟩
  · exact ((singleCoupon InP OutP inD outD).outDir_eq_downward_iff j).mpr
      ⟨.inr j, by simp [singleCoupon, h]⟩

/-- A nullary coupon (`𝟙 → 𝟙`): zero ports, zero interval edges, zero circles, and one coupon. -/
def nullaryCoupon : DiagramIncidence.{u} :=
  singleCoupon PEmpty PEmpty PEmpty.elim PEmpty.elim

@[simp] theorem couponCount_nullaryCoupon : (nullaryCoupon.{u}).couponCount = 1 :=
  couponCount_singleCoupon ..
@[simp] theorem edgeCount_nullaryCoupon : (nullaryCoupon.{u}).edgeCount = 0 := by
  rw [nullaryCoupon, edgeCount_singleCoupon]
  have h0 : Fintype.card PEmpty.{u + 1} = 0 := Fintype.card_eq_zero
  omega
@[simp] theorem circleCount_nullaryCoupon : (nullaryCoupon.{u}).circleCount = 0 :=
  circleCount_singleCoupon ..
@[simp] theorem portCount_nullaryCoupon : (nullaryCoupon.{u}).portCount = 0 := by
  rw [← two_mul_edgeCount_eq_portCount, edgeCount_nullaryCoupon]

/-- Identity diagram on a finite linearly ordered port type `P` with strand directions `dir`: one
through-strand connecting `.inBound p` and `.outBound p` for each `p : P`, zero coupons, and zero
circles. -/
def identity (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    DiagramIncidence.{u} where
  InPort := P
  OutPort := P
  Coupon := PEmpty
  CouponIn _ := PEmpty
  CouponOut _ := PEmpty
  Edge := P
  Circle := PEmpty
  src p := match dir p with
    | .upward => .inBound p
    | .downward => .outBound p
  tgt p := match dir p with
    | .upward => .outBound p
    | .downward => .inBound p
  bijective_sumElim_src_tgt := by
    let inv : DiagramPort P P PEmpty (fun _ => PEmpty) (fun _ => PEmpty) → P ⊕ P := fun
      | .inBound p => match dir p with
        | .upward => .inl p
        | .downward => .inr p
      | .outBound p => match dir p with
        | .upward => .inr p
        | .downward => .inl p
      | .couponIn c _ => c.elim
      | .couponOut c _ => c.elim
    refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
    · rintro (p | p) <;> cases h : dir p <;> simp [inv, h]
    · rintro (p | p | ⟨c, _⟩ | ⟨c, _⟩)
      · cases h : dir p <;> simp [inv, h]
      · cases h : dir p <;> simp [inv, h]
      · exact c.elim
      · exact c.elim

@[simp]
theorem edgeCount_identity (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    (identity P dir).edgeCount = Fintype.card P := (rfl)

@[simp]
theorem couponCount_identity (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    (identity P dir).couponCount = 0 := by
  dsimp [couponCount, identity]; exact Fintype.card_eq_zero

@[simp]
theorem circleCount_identity (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    (identity P dir).circleCount = 0 := by
  dsimp [circleCount, identity]; exact Fintype.card_eq_zero

@[simp]
theorem inDir_identity (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) (p : P) :
    (identity P dir).inDir p = dir p := by
  cases h : dir p
  · exact ((identity P dir).inDir_eq_upward_iff p).mpr ⟨p, by simp [identity, h]⟩
  · exact ((identity P dir).inDir_eq_downward_iff p).mpr ⟨p, by simp [identity, h]⟩

@[simp]
theorem outDir_identity (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) (p : P) :
    (identity P dir).outDir p = dir p := by
  cases h : dir p
  · exact ((identity P dir).outDir_eq_upward_iff p).mpr ⟨p, by simp [identity, h]⟩
  · exact ((identity P dir).outDir_eq_downward_iff p).mpr ⟨p, by simp [identity, h]⟩

/-- A single identity interval strand of direction `d`. -/
def singleInterval (d : StrandDir) : DiagramIncidence.{u} :=
  identity PUnit (fun _ => d)

@[simp] theorem edgeCount_singleInterval (d : StrandDir) :
    (singleInterval.{u} d).edgeCount = 1 := (rfl)
@[simp] theorem couponCount_singleInterval (d : StrandDir) :
    (singleInterval.{u} d).couponCount = 0 := couponCount_identity ..
@[simp] theorem circleCount_singleInterval (d : StrandDir) :
    (singleInterval.{u} d).circleCount = 0 := circleCount_identity ..
@[simp] theorem portCount_singleInterval (d : StrandDir) :
    (singleInterval.{u} d).portCount = 2 := by
  rw [← two_mul_edgeCount_eq_portCount, edgeCount_singleInterval]

/-- Elementary cup (`0` lower ports, `2` upper ports `ULift Bool` ordered `false < true`, `1`
interval edge). When `d = .upward`, the strand enters downward at `false` and exits upward at
`true`; when `d = .downward`, it enters downward at `true` and exits upward at `false`. -/
def cup (d : StrandDir) : DiagramIncidence.{u} where
  InPort := PEmpty
  OutPort := ULift Bool
  Coupon := PEmpty
  CouponIn _ := PEmpty
  CouponOut _ := PEmpty
  Edge := PUnit
  Circle := PEmpty
  src _ := .outBound ⟨match d with | .upward => false | .downward => true⟩
  tgt _ := .outBound ⟨match d with | .upward => true | .downward => false⟩
  bijective_sumElim_src_tgt := by
    let inv : DiagramPort PEmpty (ULift Bool) PEmpty (fun _ => PEmpty) (fun _ => PEmpty) →
        PUnit ⊕ PUnit := fun
      | .inBound i => i.elim
      | .outBound ⟨b⟩ => match d, b with
        | .upward, false | .downward, true => .inl PUnit.unit
        | .upward, true | .downward, false => .inr PUnit.unit
      | .couponIn c _ => c.elim
      | .couponOut c _ => c.elim
    refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
    · rintro (⟨⟩ | ⟨⟩) <;> cases d <;> rfl
    · rintro (i | ⟨false | true⟩ | ⟨c, _⟩ | ⟨c, _⟩)
      · exact i.elim
      · cases d <;> rfl
      · cases d <;> rfl
      · exact c.elim
      · exact c.elim

@[simp] theorem edgeCount_cup (d : StrandDir) : (cup.{u} d).edgeCount = 1 := (rfl)
@[simp] theorem couponCount_cup (d : StrandDir) : (cup.{u} d).couponCount = 0 := by
  dsimp [couponCount, cup]; exact Fintype.card_eq_zero
@[simp] theorem circleCount_cup (d : StrandDir) : (cup.{u} d).circleCount = 0 := by
  dsimp [circleCount, cup]; exact Fintype.card_eq_zero

@[simp]
theorem outDir_cup (d : StrandDir) (b : ULift Bool) :
    (cup.{u} d).outDir b = match d, b.down with
      | .upward, false | .downward, true => .downward
      | .upward, true | .downward, false => .upward := by
  rcases b with ⟨false | true⟩ <;> cases d
  · exact ((cup .upward).outDir_eq_downward_iff ⟨false⟩).mpr ⟨PUnit.unit, rfl⟩
  · exact ((cup .downward).outDir_eq_upward_iff ⟨false⟩).mpr ⟨PUnit.unit, rfl⟩
  · exact ((cup .upward).outDir_eq_upward_iff ⟨true⟩).mpr ⟨PUnit.unit, rfl⟩
  · exact ((cup .downward).outDir_eq_downward_iff ⟨true⟩).mpr ⟨PUnit.unit, rfl⟩

/-- Elementary cap (`2` lower ports `ULift Bool` ordered `false < true`, `0` upper ports, `1`
interval edge) with lower boundary directions matching `cup d`. -/
def cap (d : StrandDir) : DiagramIncidence.{u} where
  InPort := ULift Bool
  OutPort := PEmpty
  Coupon := PEmpty
  CouponIn _ := PEmpty
  CouponOut _ := PEmpty
  Edge := PUnit
  Circle := PEmpty
  src _ := .inBound ⟨match d with | .upward => true | .downward => false⟩
  tgt _ := .inBound ⟨match d with | .upward => false | .downward => true⟩
  bijective_sumElim_src_tgt := by
    let inv : DiagramPort (ULift Bool) PEmpty PEmpty (fun _ => PEmpty) (fun _ => PEmpty) →
        PUnit ⊕ PUnit := fun
      | .inBound ⟨b⟩ => match d, b with
        | .upward, true | .downward, false => .inl PUnit.unit
        | .upward, false | .downward, true => .inr PUnit.unit
      | .outBound j => j.elim
      | .couponIn c _ => c.elim
      | .couponOut c _ => c.elim
    refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
    · rintro (⟨⟩ | ⟨⟩) <;> cases d <;> rfl
    · rintro (⟨false | true⟩ | j | ⟨c, _⟩ | ⟨c, _⟩)
      · cases d <;> rfl
      · cases d <;> rfl
      · exact j.elim
      · exact c.elim
      · exact c.elim

@[simp] theorem edgeCount_cap (d : StrandDir) : (cap.{u} d).edgeCount = 1 := (rfl)
@[simp] theorem couponCount_cap (d : StrandDir) : (cap.{u} d).couponCount = 0 := by
  dsimp [couponCount, cap]; exact Fintype.card_eq_zero
@[simp] theorem circleCount_cap (d : StrandDir) : (cap.{u} d).circleCount = 0 := by
  dsimp [circleCount, cap]; exact Fintype.card_eq_zero

@[simp]
theorem inDir_cap (d : StrandDir) (b : ULift Bool) :
    (cap.{u} d).inDir b = (cup.{u} d).outDir b := by
  rw [outDir_cup]
  rcases b with ⟨false | true⟩ <;> cases d
  · exact ((cap .upward).inDir_eq_downward_iff ⟨false⟩).mpr ⟨PUnit.unit, rfl⟩
  · exact ((cap .downward).inDir_eq_upward_iff ⟨false⟩).mpr ⟨PUnit.unit, rfl⟩
  · exact ((cap .upward).inDir_eq_upward_iff ⟨true⟩).mpr ⟨PUnit.unit, rfl⟩
  · exact ((cap .downward).inDir_eq_downward_iff ⟨true⟩).mpr ⟨PUnit.unit, rfl⟩

end DiagramIncidence

end TauCeti
