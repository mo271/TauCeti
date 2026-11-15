/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Logic.Equiv.Trace
public import TauCeti.Topology.Tangle.Incidence.Operations

/-!
# Boundary-Port Gluing of Finite Diagram Incidence Data

This file constructs vertical boundary-port gluing `DiagramIncidence.glue` along an order
isomorphism `seam : D₁.OutPort ≃o D₂.InPort` compatible with boundary strand progression
directions (`∀ q, D₁.outDir q = D₂.inDir (seam q)`), suppressing interior seam vertices via the
computable finite feedback trace `Equiv.trace` while recording closed loops formed across the seam
via `Equiv.TraceLoop`.

## Main definitions

* `TauCeti.DiagramIncidence.portIsSrc`: boolean predicate testing whether a port is an edge source.
* `TauCeti.DiagramIncidence.gluePortSplitEquiv`: decomposition of `D₁.Port ⊕ D₂.Port` into retained
  ports `GluePort D₁ D₂` and seam ports `D₁.OutPort ⊕ D₂.InPort`.
* `TauCeti.DiagramIncidence.seamStep`: one-step feedback bijection
  `GlueSrc D₁ D₂ ⊕ D₁.OutPort ≃ GlueTgt D₁ D₂ ⊕ D₁.OutPort`.
* `TauCeti.DiagramIncidence.glue`: glued diagram incidence data suppressing seam subdivisions and
  adjoining closed seam loops `seamStep.TraceLoop`.
* `TauCeti.DiagramIncidence.Iso.glue`: isomorphism invariance of `glue`.
* `TauCeti.DiagramIncidence.glueOfIsEmptyIso`: gluing along an empty seam is canonically isomorphic
  to `disjointUnion`.
* `TauCeti.DiagramIncidence.cupGlueCapIso`: gluing `cup d` to `cap d` yields `singleCircle`.
* `TauCeti.DiagramIncidence.identityGlueIdentityIso`,
  `TauCeti.DiagramIncidence.singleIntervalGlueIso`: subdivision suppression when gluing identity
  strands along their matching seam.
-/

@[expose] public section

namespace TauCeti

namespace DiagramIncidence

universe u v

/-! ### Source/target port classification -/

/-- Boolean test for whether `p : D.Port` is the initial port (`src`) of its incident edge. -/
def portIsSrc (D : DiagramIncidence.{u}) (p : D.Port) : Bool :=
  (D.endpointEquiv.symm p).isLeft

@[simp]
theorem portIsSrc_src (D : DiagramIncidence.{u}) (e : D.Edge) :
    D.portIsSrc (D.src e) = true := by
  simp [portIsSrc]

@[simp]
theorem portIsSrc_tgt (D : DiagramIncidence.{u}) (e : D.Edge) :
    D.portIsSrc (D.tgt e) = false := by
  simp [portIsSrc]

/-- If `D.portIsSrc p = true`, then `p` is the source of `D.edgeAt p`. -/
theorem src_edgeAt_of_portIsSrc {D : DiagramIncidence.{u}} {p : D.Port}
    (hp : D.portIsSrc p = true) : D.src (D.edgeAt p) = p := by
  unfold portIsSrc edgeAt at *
  rcases h : D.endpointEquiv.symm p with e | e
  · exact D.endpointEquiv.eq_symm_apply.mp h.symm
  · rw [h] at hp; cases hp

/-- If `D.portIsSrc p = false`, then `p` is the target of `D.edgeAt p`. -/
theorem tgt_edgeAt_of_portIsSrc_eq_false {D : DiagramIncidence.{u}} {p : D.Port}
    (hp : D.portIsSrc p = false) : D.tgt (D.edgeAt p) = p := by
  unfold portIsSrc edgeAt at *
  rcases h : D.endpointEquiv.symm p with e | e
  · rw [h] at hp; cases hp
  · exact D.endpointEquiv.eq_symm_apply.mp h.symm

theorem portIsSrc_eq_true_iff (D : DiagramIncidence.{u}) (p : D.Port) :
    D.portIsSrc p = true ↔ ∃ e : D.Edge, D.src e = p :=
  ⟨fun hp => ⟨D.edgeAt p, src_edgeAt_of_portIsSrc hp⟩, fun ⟨e, he⟩ => he ▸ D.portIsSrc_src e⟩

theorem portIsSrc_eq_false_iff (D : DiagramIncidence.{u}) (p : D.Port) :
    D.portIsSrc p = false ↔ ∃ e : D.Edge, D.tgt e = p :=
  ⟨fun hp => ⟨D.edgeAt p, tgt_edgeAt_of_portIsSrc_eq_false hp⟩,
    fun ⟨e, he⟩ => he ▸ D.portIsSrc_tgt e⟩

theorem portIsSrc_inBound_eq_true_iff (D : DiagramIncidence.{u}) (i : D.InPort) :
    D.portIsSrc (.inBound i) = true ↔ D.inDir i = .upward := by
  rw [D.portIsSrc_eq_true_iff, D.inDir_eq_upward_iff]

theorem portIsSrc_inBound_eq_false_iff (D : DiagramIncidence.{u}) (i : D.InPort) :
    D.portIsSrc (.inBound i) = false ↔ D.inDir i = .downward := by
  rw [D.portIsSrc_eq_false_iff, D.inDir_eq_downward_iff]

theorem portIsSrc_outBound_eq_true_iff (D : DiagramIncidence.{u}) (j : D.OutPort) :
    D.portIsSrc (.outBound j) = true ↔ D.outDir j = .downward := by
  rw [D.portIsSrc_eq_true_iff, D.outDir_eq_downward_iff]

theorem portIsSrc_outBound_eq_false_iff (D : DiagramIncidence.{u}) (j : D.OutPort) :
    D.portIsSrc (.outBound j) = false ↔ D.outDir j = .upward := by
  rw [D.portIsSrc_eq_false_iff, D.outDir_eq_upward_iff]

/-- Diagram isomorphisms preserve `portIsSrc`. -/
@[simp]
theorem Iso.portIsSrc_portEquiv {D₁ : DiagramIncidence.{u}} {D₂ : DiagramIncidence.{v}}
    (φ : D₁.Iso D₂) (p : D₁.Port) : D₂.portIsSrc (φ.portEquiv p) = D₁.portIsSrc p := by
  obtain ⟨e | e, rfl⟩ := D₁.endpointEquiv.surjective p
  · rw [endpointEquiv_inl, ← φ.map_src', portIsSrc_src, portIsSrc_src]
  · rw [endpointEquiv_inr, ← φ.map_tgt', portIsSrc_tgt, portIsSrc_tgt]

/-! ### Retained ports, seam ports, and the feedback step -/

/-- Retained port type when gluing `D₁` below `D₂` along `D₁.OutPort` and `D₂.InPort`. -/
abbrev GluePort (D₁ D₂ : DiagramIncidence.{u}) : Type u :=
  DiagramPort D₁.InPort D₂.OutPort (D₁.Coupon ⊕ D₂.Coupon)
    (Sum.elim D₁.CouponIn D₂.CouponIn) (Sum.elim D₁.CouponOut D₂.CouponOut)

/-- Finite enumeration on `GluePort D₁ D₂`. -/
instance (priority := 1100) instFintypeGluePort (D₁ D₂ : DiagramIncidence.{u}) :
    Fintype (GluePort D₁ D₂) :=
  letI : ∀ c, Fintype (Sum.elim D₁.CouponIn D₂.CouponIn c) :=
    Sum.rec D₁.instFintypeCouponIn D₂.instFintypeCouponIn
  letI : ∀ c, Fintype (Sum.elim D₁.CouponOut D₂.CouponOut c) :=
    Sum.rec D₁.instFintypeCouponOut D₂.instFintypeCouponOut
  DiagramPort.instFintype

/-- Decidable equality on `GluePort D₁ D₂`. -/
instance (priority := 1100) instDecidableEqGluePort (D₁ D₂ : DiagramIncidence.{u}) :
    DecidableEq (GluePort D₁ D₂) :=
  letI : ∀ c, DecidableEq (Sum.elim D₁.CouponIn D₂.CouponIn c) :=
    Sum.rec (fun c => inferInstanceAs (DecidableEq (D₁.CouponIn c)))
      (fun c => inferInstanceAs (DecidableEq (D₂.CouponIn c)))
  letI : ∀ c, DecidableEq (Sum.elim D₁.CouponOut D₂.CouponOut c) :=
    Sum.rec (fun c => inferInstanceAs (DecidableEq (D₁.CouponOut c)))
      (fun c => inferInstanceAs (DecidableEq (D₂.CouponOut c)))
  DiagramPort.instDecidableEq

/-- Decomposition of `D₁.Port ⊕ D₂.Port` into retained ports `GluePort D₁ D₂` and seam ports
`D₁.OutPort ⊕ D₂.InPort`. -/
def gluePortSplitEquiv (D₁ D₂ : DiagramIncidence.{u}) :
    D₁.Port ⊕ D₂.Port ≃ GluePort D₁ D₂ ⊕ (D₁.OutPort ⊕ D₂.InPort) where
  toFun
    | .inl (.inBound i) => .inl (.inBound i)
    | .inl (.outBound q) => .inr (.inl q)
    | .inl (.couponIn c i) => .inl (.couponIn (.inl c) i)
    | .inl (.couponOut c j) => .inl (.couponOut (.inl c) j)
    | .inr (.inBound i) => .inr (.inr i)
    | .inr (.outBound j) => .inl (.outBound j)
    | .inr (.couponIn c i) => .inl (.couponIn (.inr c) i)
    | .inr (.couponOut c j) => .inl (.couponOut (.inr c) j)
  invFun
    | .inl (.inBound i) => .inl (.inBound i)
    | .inl (.outBound j) => .inr (.outBound j)
    | .inl (.couponIn (.inl c) i) => .inl (.couponIn c i)
    | .inl (.couponIn (.inr c) i) => .inr (.couponIn c i)
    | .inl (.couponOut (.inl c) j) => .inl (.couponOut c j)
    | .inl (.couponOut (.inr c) j) => .inr (.couponOut c j)
    | .inr (.inl q) => .inl (.outBound q)
    | .inr (.inr i) => .inr (.inBound i)
  left_inv x := by rcases x with (_ | _ | ⟨_, _⟩ | ⟨_, _⟩) | (_ | _ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
  right_inv y := by rcases y with (_ | _ | ⟨_ | _, _⟩ | ⟨_ | _, _⟩) | (_ | _) <;> rfl

/-- Whether a retained port in `GluePort D₁ D₂` is an edge source in `D₁` or `D₂`. -/
def gluePortIsSrc (D₁ D₂ : DiagramIncidence.{u}) (p : GluePort D₁ D₂) : Bool :=
  Sum.elim D₁.portIsSrc D₂.portIsSrc ((gluePortSplitEquiv D₁ D₂).symm (.inl p))

/-- Retained initial ports when gluing `D₁` below `D₂`: these index the interval edges of the
glued diagram. -/
abbrev GlueSrc (D₁ D₂ : DiagramIncidence.{u}) : Type u :=
  { p : GluePort D₁ D₂ // gluePortIsSrc D₁ D₂ p = true }

/-- Retained terminal ports when gluing `D₁` below `D₂`. -/
abbrev GlueTgt (D₁ D₂ : DiagramIncidence.{u}) : Type u :=
  { p : GluePort D₁ D₂ // gluePortIsSrc D₁ D₂ p = false }

/-- Partition of `GluePort D₁ D₂` into `GlueSrc D₁ D₂` and `GlueTgt D₁ D₂`. -/
def glueSrcSumTgtEquiv (D₁ D₂ : DiagramIncidence.{u}) :
    GlueSrc D₁ D₂ ⊕ GlueTgt D₁ D₂ ≃ GluePort D₁ D₂ where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun p := match h : gluePortIsSrc D₁ D₂ p with
    | true => .inl ⟨p, h⟩
    | false => .inr ⟨p, h⟩
  left_inv
    | .inl ⟨p, hp⟩ => by
      dsimp only [Sum.elim_inl]
      split
      · rfl
      · rename_i h; cases hp.symm.trans h
    | .inr ⟨p, hp⟩ => by
      dsimp only [Sum.elim_inr]
      split
      · rename_i h; cases hp.symm.trans h
      · rfl
  right_inv p := by
    dsimp only
    split <;> rfl

/-- The seam port in `D₁.Port ⊕ D₂.Port` acting as an edge source at seam index `q`. -/
def seamSrcPort (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (q : D₁.OutPort) : D₁.Port ⊕ D₂.Port :=
  match D₁.outDir q with
  | .upward => .inr (.inBound (seam q))
  | .downward => .inl (.outBound q)

/-- The seam port in `D₁.Port ⊕ D₂.Port` acting as an edge target at seam index `q`. -/
def seamTgtPort (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (q : D₁.OutPort) : D₁.Port ⊕ D₂.Port :=
  match D₁.outDir q with
  | .upward => .inl (.outBound q)
  | .downward => .inr (.inBound (seam q))

theorem portIsSrc_seamSrcPort (D₁ D₂ : DiagramIncidence.{u})
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (q : D₁.OutPort) :
    Sum.elim D₁.portIsSrc D₂.portIsSrc (seamSrcPort D₁ D₂ seam q) = true := by
  unfold seamSrcPort
  cases h : D₁.outDir q
  · exact (D₂.portIsSrc_inBound_eq_true_iff (seam q)).mpr ((hdir q).symm.trans h)
  · exact (D₁.portIsSrc_outBound_eq_true_iff q).mpr h

theorem portIsSrc_seamTgtPort (D₁ D₂ : DiagramIncidence.{u})
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (q : D₁.OutPort) :
    Sum.elim D₁.portIsSrc D₂.portIsSrc (seamTgtPort D₁ D₂ seam q) = false := by
  unfold seamTgtPort
  cases h : D₁.outDir q
  · exact (D₁.portIsSrc_outBound_eq_false_iff q).mpr h
  · exact (D₂.portIsSrc_inBound_eq_false_iff (seam q)).mpr ((hdir q).symm.trans h)

theorem sumMap_src_edgeAt {D₁ D₂ : DiagramIncidence.{u}} {x : D₁.Port ⊕ D₂.Port}
    (hx : Sum.elim D₁.portIsSrc D₂.portIsSrc x = true) :
    Sum.map D₁.src D₂.src (Sum.map D₁.edgeAt D₂.edgeAt x) = x := by
  rcases x with p₁ | p₂
  · exact congrArg Sum.inl (src_edgeAt_of_portIsSrc hx)
  · exact congrArg Sum.inr (src_edgeAt_of_portIsSrc hx)

theorem sumMap_tgt_edgeAt {D₁ D₂ : DiagramIncidence.{u}} {x : D₁.Port ⊕ D₂.Port}
    (hx : Sum.elim D₁.portIsSrc D₂.portIsSrc x = false) :
    Sum.map D₁.tgt D₂.tgt (Sum.map D₁.edgeAt D₂.edgeAt x) = x := by
  rcases x with p₁ | p₂
  · exact congrArg Sum.inl (tgt_edgeAt_of_portIsSrc_eq_false hx)
  · exact congrArg Sum.inr (tgt_edgeAt_of_portIsSrc_eq_false hx)

/-- Classify a source port in `D₁.Port ⊕ D₂.Port` as either a retained source or a seam index. -/
def classifySrcPort (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort) :
    (x : D₁.Port ⊕ D₂.Port) → Sum.elim D₁.portIsSrc D₂.portIsSrc x = true →
      GlueSrc D₁ D₂ ⊕ D₁.OutPort
  | .inl (.inBound i), hx => .inl ⟨.inBound i, hx⟩
  | .inl (.outBound q), _ => .inr q
  | .inl (.couponIn c i), hx => .inl ⟨.couponIn (.inl c) i, hx⟩
  | .inl (.couponOut c j), hx => .inl ⟨.couponOut (.inl c) j, hx⟩
  | .inr (.inBound i), _ => .inr (seam.symm i)
  | .inr (.outBound j), hx => .inl ⟨.outBound j, hx⟩
  | .inr (.couponIn c i), hx => .inl ⟨.couponIn (.inr c) i, hx⟩
  | .inr (.couponOut c j), hx => .inl ⟨.couponOut (.inr c) j, hx⟩

/-- Embed `GlueSrc D₁ D₂ ⊕ D₁.OutPort` into `D₁.Port ⊕ D₂.Port` as source ports. -/
def unclassifySrcPort (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort) :
    GlueSrc D₁ D₂ ⊕ D₁.OutPort → D₁.Port ⊕ D₂.Port
  | .inl p => (gluePortSplitEquiv D₁ D₂).symm (.inl p.1)
  | .inr q => seamSrcPort D₁ D₂ seam q

theorem unclassifySrcPort_classifySrcPort (D₁ D₂ : DiagramIncidence.{u})
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (x : D₁.Port ⊕ D₂.Port) (hx : Sum.elim D₁.portIsSrc D₂.portIsSrc x = true) :
    unclassifySrcPort D₁ D₂ seam (classifySrcPort D₁ D₂ seam x hx) = x := by
  rcases x with (i₁ | q₁ | ⟨c₁, i₁⟩ | ⟨c₁, j₁⟩) | (i₂ | j₂ | ⟨c₂, i₂⟩ | ⟨c₂, j₂⟩)
  · rfl
  · dsimp only [classifySrcPort, unclassifySrcPort, seamSrcPort]
    rw [(D₁.portIsSrc_outBound_eq_true_iff q₁).mp hx]
  · rfl
  · rfl
  · dsimp only [classifySrcPort, unclassifySrcPort, seamSrcPort]
    have hup : D₁.outDir (seam.symm i₂) = .upward := by
      rw [hdir (seam.symm i₂), seam.apply_symm_apply]
      exact (D₂.portIsSrc_inBound_eq_true_iff i₂).mp hx
    rw [hup, seam.apply_symm_apply]
  · rfl
  · rfl
  · rfl

theorem classifySrcPort_unclassifySrcPort (D₁ D₂ : DiagramIncidence.{u})
    (seam : D₁.OutPort ≃o D₂.InPort)
    (y : GlueSrc D₁ D₂ ⊕ D₁.OutPort)
    (hy : Sum.elim D₁.portIsSrc D₂.portIsSrc (unclassifySrcPort D₁ D₂ seam y) = true) :
    classifySrcPort D₁ D₂ seam (unclassifySrcPort D₁ D₂ seam y) hy = y := by
  rcases y with ⟨p, hp⟩ | q
  · rcases p with i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩ <;> rfl
  · revert hy
    dsimp only [unclassifySrcPort, seamSrcPort]
    cases D₁.outDir q <;> intro hy
    · exact congrArg Sum.inr (seam.symm_apply_apply q)
    · rfl

/-- Classify a target port in `D₁.Port ⊕ D₂.Port` as either a retained target or a seam index. -/
def classifyTgtPort (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort) :
    (x : D₁.Port ⊕ D₂.Port) → Sum.elim D₁.portIsSrc D₂.portIsSrc x = false →
      GlueTgt D₁ D₂ ⊕ D₁.OutPort
  | .inl (.inBound i), hx => .inl ⟨.inBound i, hx⟩
  | .inl (.outBound q), _ => .inr q
  | .inl (.couponIn c i), hx => .inl ⟨.couponIn (.inl c) i, hx⟩
  | .inl (.couponOut c j), hx => .inl ⟨.couponOut (.inl c) j, hx⟩
  | .inr (.inBound i), _ => .inr (seam.symm i)
  | .inr (.outBound j), hx => .inl ⟨.outBound j, hx⟩
  | .inr (.couponIn c i), hx => .inl ⟨.couponIn (.inr c) i, hx⟩
  | .inr (.couponOut c j), hx => .inl ⟨.couponOut (.inr c) j, hx⟩

/-- Embed `GlueTgt D₁ D₂ ⊕ D₁.OutPort` into `D₁.Port ⊕ D₂.Port` as target ports. -/
def unclassifyTgtPort (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort) :
    GlueTgt D₁ D₂ ⊕ D₁.OutPort → D₁.Port ⊕ D₂.Port
  | .inl p => (gluePortSplitEquiv D₁ D₂).symm (.inl p.1)
  | .inr q => seamTgtPort D₁ D₂ seam q

theorem unclassifyTgtPort_classifyTgtPort (D₁ D₂ : DiagramIncidence.{u})
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (x : D₁.Port ⊕ D₂.Port) (hx : Sum.elim D₁.portIsSrc D₂.portIsSrc x = false) :
    unclassifyTgtPort D₁ D₂ seam (classifyTgtPort D₁ D₂ seam x hx) = x := by
  rcases x with (i₁ | q₁ | ⟨c₁, i₁⟩ | ⟨c₁, j₁⟩) | (i₂ | j₂ | ⟨c₂, i₂⟩ | ⟨c₂, j₂⟩)
  · rfl
  · dsimp only [classifyTgtPort, unclassifyTgtPort, seamTgtPort]
    rw [(D₁.portIsSrc_outBound_eq_false_iff q₁).mp hx]
  · rfl
  · rfl
  · dsimp only [classifyTgtPort, unclassifyTgtPort, seamTgtPort]
    have hdown : D₁.outDir (seam.symm i₂) = .downward := by
      rw [hdir (seam.symm i₂), seam.apply_symm_apply]
      exact (D₂.portIsSrc_inBound_eq_false_iff i₂).mp hx
    rw [hdown, seam.apply_symm_apply]
  · rfl
  · rfl
  · rfl

theorem classifyTgtPort_unclassifyTgtPort (D₁ D₂ : DiagramIncidence.{u})
    (seam : D₁.OutPort ≃o D₂.InPort)
    (y : GlueTgt D₁ D₂ ⊕ D₁.OutPort)
    (hy : Sum.elim D₁.portIsSrc D₂.portIsSrc (unclassifyTgtPort D₁ D₂ seam y) = false) :
    classifyTgtPort D₁ D₂ seam (unclassifyTgtPort D₁ D₂ seam y) hy = y := by
  rcases y with ⟨p, hp⟩ | q
  · rcases p with i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩ <;> rfl
  · revert hy
    dsimp only [unclassifyTgtPort, seamTgtPort]
    cases D₁.outDir q <;> intro hy
    · rfl
    · exact congrArg Sum.inr (seam.symm_apply_apply q)

/-- Bijection matching the interval edges `D₁.Edge ⊕ D₂.Edge` with their classified initial ports
`GlueSrc D₁ D₂ ⊕ D₁.OutPort`. -/
def glueSrcEquiv (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) :
    D₁.Edge ⊕ D₂.Edge ≃ GlueSrc D₁ D₂ ⊕ D₁.OutPort where
  toFun e := classifySrcPort D₁ D₂ seam (Sum.map D₁.src D₂.src e) (by cases e <;> simp)
  invFun y := Sum.map D₁.edgeAt D₂.edgeAt (unclassifySrcPort D₁ D₂ seam y)
  left_inv e := by
    dsimp only
    rw [unclassifySrcPort_classifySrcPort D₁ D₂ seam hdir]
    rcases e with e₁ | e₂ <;> simp
  right_inv y := by
    have hy : Sum.elim D₁.portIsSrc D₂.portIsSrc (unclassifySrcPort D₁ D₂ seam y) = true := by
      rcases y with ⟨_, hp⟩ | q
      · exact hp
      · exact portIsSrc_seamSrcPort D₁ D₂ seam hdir q
    have hmap := sumMap_src_edgeAt hy
    dsimp only
    generalize_proofs hprf
    revert hprf
    rw [hmap]
    intro hprf
    exact classifySrcPort_unclassifySrcPort D₁ D₂ seam y hprf

/-- Bijection matching the interval edges `D₁.Edge ⊕ D₂.Edge` with their classified terminal ports
`GlueTgt D₁ D₂ ⊕ D₁.OutPort`. -/
def glueTgtEquiv (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) :
    D₁.Edge ⊕ D₂.Edge ≃ GlueTgt D₁ D₂ ⊕ D₁.OutPort where
  toFun e := classifyTgtPort D₁ D₂ seam (Sum.map D₁.tgt D₂.tgt e) (by cases e <;> simp)
  invFun y := Sum.map D₁.edgeAt D₂.edgeAt (unclassifyTgtPort D₁ D₂ seam y)
  left_inv e := by
    dsimp only
    rw [unclassifyTgtPort_classifyTgtPort D₁ D₂ seam hdir]
    rcases e with e₁ | e₂ <;> simp
  right_inv y := by
    have hy : Sum.elim D₁.portIsSrc D₂.portIsSrc (unclassifyTgtPort D₁ D₂ seam y) = false := by
      rcases y with ⟨_, hp⟩ | q
      · exact hp
      · exact portIsSrc_seamTgtPort D₁ D₂ seam hdir q
    have hmap := sumMap_tgt_edgeAt hy
    dsimp only
    generalize_proofs hprf
    revert hprf
    rw [hmap]
    intro hprf
    exact classifyTgtPort_unclassifyTgtPort D₁ D₂ seam y hprf

@[simp]
theorem glueSrcEquiv_symm_apply (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) (y : GlueSrc D₁ D₂ ⊕ D₁.OutPort) :
    (glueSrcEquiv D₁ D₂ seam hdir).symm y =
      Sum.map D₁.edgeAt D₂.edgeAt (unclassifySrcPort D₁ D₂ seam y) := (rfl)

@[simp]
theorem glueTgtEquiv_symm_apply (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) (y : GlueTgt D₁ D₂ ⊕ D₁.OutPort) :
    (glueTgtEquiv D₁ D₂ seam hdir).symm y =
      Sum.map D₁.edgeAt D₂.edgeAt (unclassifyTgtPort D₁ D₂ seam y) := (rfl)

theorem glueSrcEquiv_eq_of_unclassify {D₁ D₂ : DiagramIncidence.{u}}
    {seam : D₁.OutPort ≃o D₂.InPort} {hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)}
    {e : D₁.Edge ⊕ D₂.Edge} {y : GlueSrc D₁ D₂ ⊕ D₁.OutPort}
    (h : Sum.map D₁.src D₂.src e = unclassifySrcPort D₁ D₂ seam y) :
    glueSrcEquiv D₁ D₂ seam hdir e = y := by
  rw [← (glueSrcEquiv D₁ D₂ seam hdir).eq_symm_apply, glueSrcEquiv_symm_apply, ← h]
  rcases e with e₁ | e₂ <;> simp

theorem glueTgtEquiv_eq_of_unclassify {D₁ D₂ : DiagramIncidence.{u}}
    {seam : D₁.OutPort ≃o D₂.InPort} {hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)}
    {e : D₁.Edge ⊕ D₂.Edge} {y : GlueTgt D₁ D₂ ⊕ D₁.OutPort}
    (h : Sum.map D₁.tgt D₂.tgt e = unclassifyTgtPort D₁ D₂ seam y) :
    glueTgtEquiv D₁ D₂ seam hdir e = y := by
  rw [← (glueTgtEquiv D₁ D₂ seam hdir).eq_symm_apply, glueTgtEquiv_symm_apply, ← h]
  rcases e with e₁ | e₂ <;> simp

/-- One-step feedback bijection across the seam `D₁.OutPort`, sending each classified edge source in
`GlueSrc D₁ D₂ ⊕ D₁.OutPort` to the classified target of the same interval edge in
`GlueTgt D₁ D₂ ⊕ D₁.OutPort`. -/
def seamStep (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) :
    GlueSrc D₁ D₂ ⊕ D₁.OutPort ≃ GlueTgt D₁ D₂ ⊕ D₁.OutPort :=
  (glueSrcEquiv D₁ D₂ seam hdir).symm.trans (glueTgtEquiv D₁ D₂ seam hdir)

@[simp]
theorem seamStep_glueSrcEquiv (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) (e : D₁.Edge ⊕ D₂.Edge) :
    seamStep D₁ D₂ seam hdir (glueSrcEquiv D₁ D₂ seam hdir e) =
      glueTgtEquiv D₁ D₂ seam hdir e := by
  simp [seamStep]

/-- Endpoint bijection for vertical boundary-port gluing. -/
theorem bijective_sumElim_glue (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) :
    Function.Bijective
      (Sum.elim (Subtype.val : GlueSrc D₁ D₂ → GluePort D₁ D₂)
        (fun e => ((seamStep D₁ D₂ seam hdir).trace e).1)) := by
  have hcomp :
      Sum.elim (Subtype.val : GlueSrc D₁ D₂ → GluePort D₁ D₂)
        (fun e => ((seamStep D₁ D₂ seam hdir).trace e).1) =
      glueSrcSumTgtEquiv D₁ D₂ ∘
        ((Equiv.refl (GlueSrc D₁ D₂)).sumCongr (seamStep D₁ D₂ seam hdir).trace) := by
    ext (e | e) <;> rfl
  rw [hcomp]
  exact (glueSrcSumTgtEquiv D₁ D₂).bijective.comp (Equiv.bijective _)

/-- **Vertical boundary-port gluing** of `D₁` (lower) and `D₂` (upper) along a direction-compatible
order isomorphism `seam : D₁.OutPort ≃o D₂.InPort`. Interior seam vertices are suppressed by tracing
open paths via `(seamStep D₁ D₂ seam hdir).trace`, and closed loops formed across the seam are
adjoined via `(seamStep D₁ D₂ seam hdir).TraceLoop`. -/
def glue (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) : DiagramIncidence.{u} where
  InPort := D₁.InPort
  OutPort := D₂.OutPort
  Coupon := D₁.Coupon ⊕ D₂.Coupon
  CouponIn := Sum.elim D₁.CouponIn D₂.CouponIn
  CouponOut := Sum.elim D₁.CouponOut D₂.CouponOut
  Edge := GlueSrc D₁ D₂
  Circle := (D₁.Circle ⊕ D₂.Circle) ⊕ (seamStep D₁ D₂ seam hdir).TraceLoop
  instFintypeCouponIn := Sum.rec D₁.instFintypeCouponIn D₂.instFintypeCouponIn
  instFintypeCouponOut := Sum.rec D₁.instFintypeCouponOut D₂.instFintypeCouponOut
  instLinearOrderCouponIn := Sum.rec D₁.instLinearOrderCouponIn D₂.instLinearOrderCouponIn
  instLinearOrderCouponOut := Sum.rec D₁.instLinearOrderCouponOut D₂.instLinearOrderCouponOut
  src e := e.1
  tgt e := ((seamStep D₁ D₂ seam hdir).trace e).1
  bijective_sumElim_src_tgt := bijective_sumElim_glue D₁ D₂ seam hdir

@[simp]
theorem couponCount_glue (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) :
    (D₁.glue D₂ seam hdir).couponCount = D₁.couponCount + D₂.couponCount := by
  dsimp [couponCount, glue]
  exact Fintype.card_sum

@[simp]
theorem portIsSrc_glue (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) (p : GluePort D₁ D₂) :
    (D₁.glue D₂ seam hdir).portIsSrc p = gluePortIsSrc D₁ D₂ p := by
  cases h : gluePortIsSrc D₁ D₂ p
  · rw [Bool.eq_false_iff]
    intro htrue
    obtain ⟨⟨_, hp'⟩, rfl⟩ := ((D₁.glue D₂ seam hdir).portIsSrc_eq_true_iff p).mp htrue
    exact Bool.false_ne_true (h.symm.trans hp')
  · exact ((D₁.glue D₂ seam hdir).portIsSrc_eq_true_iff p).mpr ⟨⟨p, h⟩, rfl⟩

@[simp]
theorem inDir_glue (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) (i : D₁.InPort) :
    (D₁.glue D₂ seam hdir).inDir i = D₁.inDir i := by
  cases h : D₁.inDir i
  · exact ((D₁.glue D₂ seam hdir).portIsSrc_inBound_eq_true_iff i).mp
      ((portIsSrc_glue D₁ D₂ seam hdir (.inBound i)).trans
        ((D₁.portIsSrc_inBound_eq_true_iff i).mpr h))
  · exact ((D₁.glue D₂ seam hdir).portIsSrc_inBound_eq_false_iff i).mp
      ((portIsSrc_glue D₁ D₂ seam hdir (.inBound i)).trans
        ((D₁.portIsSrc_inBound_eq_false_iff i).mpr h))

@[simp]
theorem outDir_glue (D₁ D₂ : DiagramIncidence.{u}) (seam : D₁.OutPort ≃o D₂.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) (j : D₂.OutPort) :
    (D₁.glue D₂ seam hdir).outDir j = D₂.outDir j := by
  cases h : D₂.outDir j
  · exact ((D₁.glue D₂ seam hdir).portIsSrc_outBound_eq_false_iff j).mp
      ((portIsSrc_glue D₁ D₂ seam hdir (.outBound j)).trans
        ((D₂.portIsSrc_outBound_eq_false_iff j).mpr h))
  · exact ((D₁.glue D₂ seam hdir).portIsSrc_outBound_eq_true_iff j).mp
      ((portIsSrc_glue D₁ D₂ seam hdir (.outBound j)).trans
        ((D₂.portIsSrc_outBound_eq_true_iff j).mpr h))

/-! ### Isomorphism invariance of gluing -/

/-- Port equivalence on `GluePort` induced by diagram isomorphisms on the two factors. -/
def Iso.gluePortEquiv {D₁ D₂ : DiagramIncidence.{u}} {D₁' D₂' : DiagramIncidence.{v}}
    (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂') : GluePort D₁ D₂ ≃ GluePort D₁' D₂' :=
  DiagramPort.congr φ₁.inPort.toEquiv φ₂.outPort.toEquiv (φ₁.coupon.sumCongr φ₂.coupon)
    (Sum.rec (fun c => (φ₁.couponIn c).toEquiv) (fun c => (φ₂.couponIn c).toEquiv))
    (Sum.rec (fun c => (φ₁.couponOut c).toEquiv) (fun c => (φ₂.couponOut c).toEquiv))

@[simp]
theorem Iso.gluePortIsSrc_gluePortEquiv {D₁ D₂ : DiagramIncidence.{u}}
    {D₁' D₂' : DiagramIncidence.{v}} (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂') (p : GluePort D₁ D₂) :
    gluePortIsSrc D₁' D₂' (Iso.gluePortEquiv φ₁ φ₂ p) = gluePortIsSrc D₁ D₂ p := by
  rcases p with i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩
  · exact φ₁.portIsSrc_portEquiv (.inBound i)
  · exact φ₂.portIsSrc_portEquiv (.outBound j)
  · exact φ₁.portIsSrc_portEquiv (.couponIn c i)
  · exact φ₂.portIsSrc_portEquiv (.couponIn c i)
  · exact φ₁.portIsSrc_portEquiv (.couponOut c j)
  · exact φ₂.portIsSrc_portEquiv (.couponOut c j)

/-- Source-port equivalence on `GlueSrc` induced by diagram isomorphisms on the two factors. -/
def Iso.glueSrcCongr {D₁ D₂ : DiagramIncidence.{u}} {D₁' D₂' : DiagramIncidence.{v}}
    (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂') : GlueSrc D₁ D₂ ≃ GlueSrc D₁' D₂' :=
  (Iso.gluePortEquiv φ₁ φ₂).subtypeEquiv fun p => by rw [Iso.gluePortIsSrc_gluePortEquiv]

/-- Target-port equivalence on `GlueTgt` induced by diagram isomorphisms on the two factors. -/
def Iso.glueTgtCongr {D₁ D₂ : DiagramIncidence.{u}} {D₁' D₂' : DiagramIncidence.{v}}
    (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂') : GlueTgt D₁ D₂ ≃ GlueTgt D₁' D₂' :=
  (Iso.gluePortEquiv φ₁ φ₂).subtypeEquiv fun p => by rw [Iso.gluePortIsSrc_gluePortEquiv]

theorem Iso.seamStep_congr {D₁ D₂ : DiagramIncidence.{u}} {D₁' D₂' : DiagramIncidence.{v}}
    (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂')
    (seam : D₁.OutPort ≃o D₂.InPort) (seam' : D₁'.OutPort ≃o D₂'.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (hdir' : ∀ q', D₁'.outDir q' = D₂'.inDir (seam' q'))
    (hseam : ∀ q, seam' (φ₁.outPort q) = φ₂.inPort (seam q))
    (x : GlueSrc D₁ D₂ ⊕ D₁.OutPort) :
    seamStep D₁' D₂' seam' hdir' ((Iso.glueSrcCongr φ₁ φ₂).sumCongr φ₁.outPort.toEquiv x) =
      (Iso.glueTgtCongr φ₁ φ₂).sumCongr φ₁.outPort.toEquiv (seamStep D₁ D₂ seam hdir x) := by
  have hunsrc : ∀ y : GlueSrc D₁ D₂ ⊕ D₁.OutPort,
      unclassifySrcPort D₁' D₂' seam' ((Iso.glueSrcCongr φ₁ φ₂).sumCongr φ₁.outPort.toEquiv y) =
        Sum.map φ₁.portEquiv φ₂.portEquiv (unclassifySrcPort D₁ D₂ seam y) := by
    rintro (⟨p, _⟩ | q)
    · rcases p with i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩ <;> rfl
    · dsimp only [Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inr, RelIso.coe_fn_toEquiv,
        unclassifySrcPort, seamSrcPort]
      rw [φ₁.outDir_apply q]
      cases D₁.outDir q
      · exact congrArg (Sum.inr ∘ DiagramPort.inBound) (hseam q)
      · rfl
  have huntgt : ∀ y : GlueTgt D₁ D₂ ⊕ D₁.OutPort,
      unclassifyTgtPort D₁' D₂' seam' ((Iso.glueTgtCongr φ₁ φ₂).sumCongr φ₁.outPort.toEquiv y) =
        Sum.map φ₁.portEquiv φ₂.portEquiv (unclassifyTgtPort D₁ D₂ seam y) := by
    rintro (⟨p, _⟩ | q)
    · rcases p with i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩ <;> rfl
    · dsimp only [Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inr, RelIso.coe_fn_toEquiv,
        unclassifyTgtPort, seamTgtPort]
      rw [φ₁.outDir_apply q]
      cases D₁.outDir q
      · rfl
      · exact congrArg (Sum.inr ∘ DiagramPort.inBound) (hseam q)
  obtain ⟨e, rfl⟩ := (glueSrcEquiv D₁ D₂ seam hdir).surjective x
  have hesrc : glueSrcEquiv D₁' D₂' seam' hdir' ((φ₁.edge.sumCongr φ₂.edge) e) =
      (Iso.glueSrcCongr φ₁ φ₂).sumCongr φ₁.outPort.toEquiv (glueSrcEquiv D₁ D₂ seam hdir e) := by
    refine glueSrcEquiv_eq_of_unclassify ?_
    rw [hunsrc]
    have he := unclassifySrcPort_classifySrcPort D₁ D₂ seam hdir (Sum.map D₁.src D₂.src e)
      (by cases e <;> simp)
    dsimp only [glueSrcEquiv, Equiv.coe_fn_mk]
    rw [he]
    rcases e with e₁ | e₂ <;> simp
  have hetgt : glueTgtEquiv D₁' D₂' seam' hdir' ((φ₁.edge.sumCongr φ₂.edge) e) =
      (Iso.glueTgtCongr φ₁ φ₂).sumCongr φ₁.outPort.toEquiv (glueTgtEquiv D₁ D₂ seam hdir e) := by
    refine glueTgtEquiv_eq_of_unclassify ?_
    rw [huntgt]
    have he := unclassifyTgtPort_classifyTgtPort D₁ D₂ seam hdir (Sum.map D₁.tgt D₂.tgt e)
      (by cases e <;> simp)
    dsimp only [glueTgtEquiv, Equiv.coe_fn_mk]
    rw [he]
    rcases e with e₁ | e₂ <;> simp
  rw [← hesrc, seamStep_glueSrcEquiv, hetgt, seamStep_glueSrcEquiv]

theorem Iso.glue_map_tgt {D₁ D₂ : DiagramIncidence.{u}} {D₁' D₂' : DiagramIncidence.{v}}
    (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂')
    (seam : D₁.OutPort ≃o D₂.InPort) (seam' : D₁'.OutPort ≃o D₂'.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (hdir' : ∀ q', D₁'.outDir q' = D₂'.inDir (seam' q'))
    (hseam : ∀ q, seam' (φ₁.outPort q) = φ₂.inPort (seam q)) (e : GlueSrc D₁ D₂) :
    ((seamStep D₁' D₂' seam' hdir').trace (Iso.glueSrcCongr φ₁ φ₂ e)).1 =
      Iso.gluePortEquiv φ₁ φ₂ ((seamStep D₁ D₂ seam hdir).trace e).1 := by
  have htr := Equiv.trace_congr_apply (Iso.glueSrcCongr φ₁ φ₂) (Iso.glueTgtCongr φ₁ φ₂)
    φ₁.outPort.toEquiv (Iso.seamStep_congr φ₁ φ₂ seam seam' hdir hdir' hseam) e
  exact (congrArg Subtype.val htr).symm

/-- Functoriality (isomorphism invariance) of vertical boundary-port gluing. -/
def Iso.glue {D₁ D₂ : DiagramIncidence.{u}} {D₁' D₂' : DiagramIncidence.{v}}
    (φ₁ : D₁.Iso D₁') (φ₂ : D₂.Iso D₂')
    (seam : D₁.OutPort ≃o D₂.InPort) (seam' : D₁'.OutPort ≃o D₂'.InPort)
    (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (hdir' : ∀ q', D₁'.outDir q' = D₂'.inDir (seam' q'))
    (hseam : ∀ q, seam' (φ₁.outPort q) = φ₂.inPort (seam q)) :
    (D₁.glue D₂ seam hdir).Iso (D₁'.glue D₂' seam' hdir') where
  inPort := φ₁.inPort
  outPort := φ₂.outPort
  coupon := φ₁.coupon.sumCongr φ₂.coupon
  couponIn := Sum.rec φ₁.couponIn φ₂.couponIn
  couponOut := Sum.rec φ₁.couponOut φ₂.couponOut
  edge := Iso.glueSrcCongr φ₁ φ₂
  circle := (φ₁.circle.sumCongr φ₂.circle).sumCongr
    (Equiv.traceLoopCongr (Iso.glueSrcCongr φ₁ φ₂) (Iso.glueTgtCongr φ₁ φ₂) φ₁.outPort.toEquiv
      (Iso.seamStep_congr φ₁ φ₂ seam seam' hdir hdir' hseam))
  map_src e := by
    dsimp only [DiagramIncidence.glue]
    erw [Equiv.subtypeEquiv_apply]
    rcases e with ⟨i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩, _⟩ <;> rfl
  map_tgt e := by
    dsimp only [DiagramIncidence.glue]
    erw [Iso.glue_map_tgt φ₁ φ₂ seam seam' hdir hdir' hseam e]
    rcases (seamStep D₁ D₂ seam hdir).trace e with ⟨i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩, _⟩ <;> rfl

/-! ### Empty seam gluing and component preservation -/

section EmptySeam

theorem glueOfIsEmpty_map_src (D₁ D₂ : DiagramIncidence.{u}) [IsEmpty D₁.OutPort]
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (x : GlueSrc D₁ D₂) :
    haveI : IsEmpty D₂.InPort := seam.toEquiv.symm.isEmpty
    (D₁.disjointUnion D₂).src ((glueSrcEquiv D₁ D₂ seam hdir).symm (.inl x)) =
      DiagramPort.congr OrderIso.sumLexEmpty.symm.toEquiv OrderIso.emptySumLex.symm.toEquiv
        (Equiv.refl (D₁.Coupon ⊕ D₂.Coupon))
        (fun c => Equiv.refl ((D₁.glue D₂ seam hdir).CouponIn c))
        (fun c => Equiv.refl ((D₁.glue D₂ seam hdir).CouponOut c))
        x.1 := by
  have : IsEmpty D₂.InPort := seam.toEquiv.symm.isEmpty
  have hdisj : ∀ e : D₁.Edge ⊕ D₂.Edge,
      (D₁.disjointUnion D₂).src e = disjointPortEquiv D₁ D₂ (Sum.map D₁.src D₂.src e) := by
    rintro (e₁ | e₂) <;> rfl
  have hinner : Sum.map D₁.src D₂.src ((glueSrcEquiv D₁ D₂ seam hdir).symm (.inl x)) =
      (gluePortSplitEquiv D₁ D₂).symm (.inl x.1) := by
    rw [glueSrcEquiv_symm_apply]
    exact sumMap_src_edgeAt x.2
  exact (hdisj _).trans ((congrArg (disjointPortEquiv D₁ D₂) hinner).trans
    (by rcases x with ⟨i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩, _⟩ <;> rfl))

theorem glueOfIsEmpty_map_tgt (D₁ D₂ : DiagramIncidence.{u}) [IsEmpty D₁.OutPort]
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q))
    (x : GlueSrc D₁ D₂) :
    haveI : IsEmpty D₂.InPort := seam.toEquiv.symm.isEmpty
    (D₁.disjointUnion D₂).tgt ((glueSrcEquiv D₁ D₂ seam hdir).symm (.inl x)) =
      DiagramPort.congr OrderIso.sumLexEmpty.symm.toEquiv OrderIso.emptySumLex.symm.toEquiv
        (Equiv.refl (D₁.Coupon ⊕ D₂.Coupon))
        (fun c => Equiv.refl ((D₁.glue D₂ seam hdir).CouponIn c))
        (fun c => Equiv.refl ((D₁.glue D₂ seam hdir).CouponOut c))
        ((seamStep D₁ D₂ seam hdir).trace x).1 := by
  have : IsEmpty D₂.InPort := seam.toEquiv.symm.isEmpty
  have hdisj : ∀ e : D₁.Edge ⊕ D₂.Edge,
      (D₁.disjointUnion D₂).tgt e = disjointPortEquiv D₁ D₂ (Sum.map D₁.tgt D₂.tgt e) := by
    rintro (e₁ | e₂) <;> rfl
  set y := (seamStep D₁ D₂ seam hdir).trace x
  have hstep : seamStep D₁ D₂ seam hdir (.inl x) = .inl y := by
    rcases h : seamStep D₁ D₂ seam hdir (.inl x) with y' | q
    · exact congrArg Sum.inl (((seamStep D₁ D₂ seam hdir).trace_apply_of_inl h).trans rfl).symm
    · exact isEmptyElim q
  have heq : (glueSrcEquiv D₁ D₂ seam hdir).symm (.inl x) =
      (glueTgtEquiv D₁ D₂ seam hdir).symm (.inl y) :=
    (glueTgtEquiv D₁ D₂ seam hdir).injective
      (hstep.trans ((glueTgtEquiv D₁ D₂ seam hdir).apply_symm_apply (.inl y)).symm)
  have hinner : Sum.map D₁.tgt D₂.tgt ((glueTgtEquiv D₁ D₂ seam hdir).symm (.inl y)) =
      (gluePortSplitEquiv D₁ D₂).symm (.inl y.1) := by
    rw [glueTgtEquiv_symm_apply]
    exact sumMap_tgt_edgeAt y.2
  rw [heq]
  exact (hdisj _).trans ((congrArg (disjointPortEquiv D₁ D₂) hinner).trans
    (by rcases y with ⟨i | j | ⟨c | c, i⟩ | ⟨c | c, j⟩, _⟩ <;> rfl))

/-- Gluing along an empty seam `D₁.OutPort` is canonically isomorphic to `D₁.disjointUnion D₂`. -/
def glueOfIsEmptyIso (D₁ D₂ : DiagramIncidence.{u}) [IsEmpty D₁.OutPort]
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) :
    (D₁.glue D₂ seam hdir).Iso (D₁.disjointUnion D₂) :=
  letI : IsEmpty D₂.InPort := seam.toEquiv.symm.isEmpty
  { inPort := OrderIso.sumLexEmpty.symm
    outPort := OrderIso.emptySumLex.symm
    coupon := Equiv.refl (D₁.Coupon ⊕ D₂.Coupon)
    couponIn := fun c => OrderIso.refl ((D₁.glue D₂ seam hdir).CouponIn c)
    couponOut := fun c => OrderIso.refl ((D₁.glue D₂ seam hdir).CouponOut c)
    edge := (Equiv.sumEmpty (GlueSrc D₁ D₂) D₁.OutPort).symm.trans
      (glueSrcEquiv D₁ D₂ seam hdir).symm
    circle := Equiv.sumEmpty (D₁.Circle ⊕ D₂.Circle) (seamStep D₁ D₂ seam hdir).TraceLoop
    map_src x := by
      dsimp only [glue]
      erw [Equiv.trans_apply, Equiv.sumEmpty_symm_apply]
      exact glueOfIsEmpty_map_src D₁ D₂ seam hdir x
    map_tgt x := by
      dsimp only [glue]
      erw [Equiv.trans_apply, Equiv.sumEmpty_symm_apply]
      exact glueOfIsEmpty_map_tgt D₁ D₂ seam hdir x }

/-- Gluing along an empty seam adds connected component counts. -/
@[simp]
theorem componentCount_glue_of_isEmpty (D₁ D₂ : DiagramIncidence.{u}) [IsEmpty D₁.OutPort]
    (seam : D₁.OutPort ≃o D₂.InPort) (hdir : ∀ q, D₁.outDir q = D₂.inDir (seam q)) :
    (D₁.glue D₂ seam hdir).componentCount = D₁.componentCount + D₂.componentCount := by
  rw [(glueOfIsEmptyIso D₁ D₂ seam hdir).componentCount_eq, componentCount_disjointUnion]

/-- Gluing `D` on top of `empty` (when `D.InPort` is empty) is canonically isomorphic to `D`. -/
def emptyGlueIso (D : DiagramIncidence.{u}) [IsEmpty D.InPort]
    (seam : (empty.{u}).OutPort ≃o D.InPort)
    (hdir : ∀ q, (empty.{u}).outDir q = D.inDir (seam q)) :
    ((empty.{u}).glue D seam hdir).Iso D :=
  (glueOfIsEmptyIso empty D seam hdir).trans (emptyDisjointUnionIso D)

/-- Gluing `empty` on top of `D` (when `D.OutPort` is empty) is canonically isomorphic to `D`. -/
def glueEmptyIso (D : DiagramIncidence.{u}) [IsEmpty D.OutPort]
    (seam : D.OutPort ≃o (empty.{u}).InPort)
    (hdir : ∀ q, D.outDir q = (empty.{u}).inDir (seam q)) :
    (D.glue empty seam hdir).Iso D :=
  (glueOfIsEmptyIso D empty seam hdir).trans (disjointUnionEmptyIso D)

@[simp]
theorem componentCount_empty_glue (D : DiagramIncidence.{u}) [IsEmpty D.InPort]
    (seam : (empty.{u}).OutPort ≃o D.InPort)
    (hdir : ∀ q, (empty.{u}).outDir q = D.inDir (seam q)) :
    ((empty.{u}).glue D seam hdir).componentCount = D.componentCount :=
  (emptyGlueIso D seam hdir).componentCount_eq

@[simp]
theorem componentCount_glue_empty (D : DiagramIncidence.{u}) [IsEmpty D.OutPort]
    (seam : D.OutPort ≃o (empty.{u}).InPort)
    (hdir : ∀ q, D.outDir q = (empty.{u}).inDir (seam q)) :
    (D.glue empty seam hdir).componentCount = D.componentCount :=
  (glueEmptyIso D seam hdir).componentCount_eq

end EmptySeam

/-! ### Closed loop formation: `cup` glued to `cap` -/

section CupCap

instance instIsEmptyGluePortCupCap (d : StrandDir) : IsEmpty (GluePort (cup.{u} d) (cap.{u} d)) :=
  ⟨fun p => by
    rcases p with i | j | ⟨c | c, _⟩ | ⟨c | c, _⟩
    exacts [i.elim, j.elim, c.elim, c.elim, c.elim, c.elim]⟩

theorem seamStep_cup_cap_false (d : StrandDir) :
    seamStep (cup.{u} d) (cap.{u} d) (OrderIso.refl (ULift Bool))
      (fun b => (inDir_cap d b).symm) (.inr ⟨false⟩) = .inr ⟨true⟩ := by
  cases d
  · have hsrc : glueSrcEquiv (cup.{u} .upward) (cap.{u} .upward)
        (OrderIso.refl (ULift Bool)) (fun b => (inDir_cap .upward b).symm)
        (.inl PUnit.unit) = .inr ⟨false⟩ := by
      refine glueSrcEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inl, unclassifySrcPort, seamSrcPort]
      rw [outDir_cup]
      rfl
    have htgt : glueTgtEquiv (cup.{u} .upward) (cap.{u} .upward)
        (OrderIso.refl (ULift Bool)) (fun b => (inDir_cap .upward b).symm)
        (.inl PUnit.unit) = .inr ⟨true⟩ := by
      refine glueTgtEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inl, unclassifyTgtPort, seamTgtPort]
      rw [outDir_cup]
      rfl
    rw [← hsrc]
    exact (seamStep_glueSrcEquiv (cup.{u} .upward) (cap.{u} .upward)
      (OrderIso.refl (ULift Bool)) (fun b => (inDir_cap .upward b).symm) (.inl PUnit.unit)).trans
      htgt
  · have hsrc : glueSrcEquiv (cup.{u} .downward) (cap.{u} .downward)
        (OrderIso.refl (ULift Bool)) (fun b => (inDir_cap .downward b).symm)
        (.inr PUnit.unit) = .inr ⟨false⟩ := by
      refine glueSrcEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inr, unclassifySrcPort, seamSrcPort]
      rw [outDir_cup]
      rfl
    have htgt : glueTgtEquiv (cup.{u} .downward) (cap.{u} .downward)
        (OrderIso.refl (ULift Bool)) (fun b => (inDir_cap .downward b).symm)
        (.inr PUnit.unit) = .inr ⟨true⟩ := by
      refine glueTgtEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inr, unclassifyTgtPort, seamTgtPort]
      rw [outDir_cup]
      rfl
    rw [← hsrc]
    exact (seamStep_glueSrcEquiv (cup.{u} .downward) (cap.{u} .downward)
      (OrderIso.refl (ULift Bool)) (fun b => (inDir_cap .downward b).symm) (.inr PUnit.unit)).trans
      htgt

/-- Unique closed feedback loop formed when gluing `cup d` to `cap d`. -/
instance instUniqueTraceLoopCupCap (d : StrandDir) :
    Unique (seamStep (cup.{u} d) (cap.{u} d) (OrderIso.refl (ULift Bool))
      (fun b => (inDir_cap d b).symm)).TraceLoop :=
  let S := seamStep (cup.{u} d) (cap.{u} d) (OrderIso.refl (ULift Bool))
    (fun b => (inDir_cap d b).symm)
  let c₀ : S.TraceClosed := ⟨⟨false⟩, fun ⟨⟨p, _⟩, _, _⟩ => isEmptyElim p⟩
  S.uniqueTraceLoopOfSameCycle c₀ fun ⟨⟨b⟩, _⟩ => by
    cases b
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, Subtype.ext <| by
        rw [zpow_one]
        exact Sum.inr.inj ((S.inr_val_tracePerm_apply c₀).trans (seamStep_cup_cap_false d))⟩

/-- Gluing `cup d` below `cap d` along their two matching boundary ports yields `singleCircle`. -/
def cupGlueCapIso (d : StrandDir) :
    ((cup.{u} d).glue (cap.{u} d) (OrderIso.refl (ULift Bool))
      (fun b => (inDir_cap d b).symm)).Iso singleCircle.{u} where
  inPort := OrderIso.refl PEmpty
  outPort := OrderIso.refl PEmpty
  coupon := Equiv.sumEmpty PEmpty PEmpty
  couponIn
    | .inl c => c.elim
    | .inr c => c.elim
  couponOut
    | .inl c => c.elim
    | .inr c => c.elim
  edge := Equiv.equivOfIsEmpty (GlueSrc (cup.{u} d) (cap.{u} d)) PEmpty
  circle := ((Equiv.sumEmpty PEmpty PEmpty).sumCongr (Equiv.refl _)).trans
    ((Equiv.emptySum PEmpty _).trans (Equiv.equivPUnit _))
  map_src := fun e => isEmptyElim e.1
  map_tgt := fun e => isEmptyElim e.1

@[simp]
theorem edgeCount_cup_glue_cap (d : StrandDir) :
    ((cup.{u} d).glue (cap.{u} d) (OrderIso.refl (ULift Bool))
      (fun b => (inDir_cap d b).symm)).edgeCount = 0 :=
  (cupGlueCapIso d).edgeCount_eq.trans edgeCount_singleCircle

@[simp]
theorem circleCount_cup_glue_cap (d : StrandDir) :
    ((cup.{u} d).glue (cap.{u} d) (OrderIso.refl (ULift Bool))
      (fun b => (inDir_cap d b).symm)).circleCount = 1 :=
  (cupGlueCapIso d).circleCount_eq.trans circleCount_singleCircle

@[simp]
theorem componentCount_cup_glue_cap (d : StrandDir) :
    ((cup.{u} d).glue (cap.{u} d) (OrderIso.refl (ULift Bool))
      (fun b => (inDir_cap d b).symm)).componentCount = 1 :=
  (cupGlueCapIso d).componentCount_eq.trans componentCount_singleCircle

end CupCap

/-! ### Subdivision suppression on identity strands -/

section IdentityGlue

/-- Direction compatibility for gluing `identity P dir` to itself along `OrderIso.refl P`. -/
theorem identitySeamCompat (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir)
    (p : P) : (identity P dir).outDir p = (identity P dir).inDir (OrderIso.refl P p) :=
  (outDir_identity P dir p).trans (inDir_identity P dir p).symm

@[simp]
theorem portIsSrc_identity_inBound (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir)
    (p : P) : (identity P dir).portIsSrc (.inBound p) = (dir p == .upward) := by
  cases h : dir p
  · have hs : (identity P dir).src p = .inBound p := by simp [identity, h]
    exact (congrArg (identity P dir).portIsSrc hs.symm).trans ((identity P dir).portIsSrc_src p)
  · have ht : (identity P dir).tgt p = .inBound p := by simp [identity, h]
    exact (congrArg (identity P dir).portIsSrc ht.symm).trans ((identity P dir).portIsSrc_tgt p)

@[simp]
theorem portIsSrc_identity_outBound (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir)
    (p : P) : (identity P dir).portIsSrc (.outBound p) = (dir p == .downward) := by
  cases h : dir p
  · have ht : (identity P dir).tgt p = .outBound p := by simp [identity, h]
    exact (congrArg (identity P dir).portIsSrc ht.symm).trans ((identity P dir).portIsSrc_tgt p)
  · have hs : (identity P dir).src p = .outBound p := by simp [identity, h]
    exact (congrArg (identity P dir).portIsSrc hs.symm).trans ((identity P dir).portIsSrc_src p)

/-- Retained source port equivalence `P ≃ GlueSrc (identity P dir) (identity P dir)`. -/
def identityGlueSrcEquiv (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    P ≃ GlueSrc (identity P dir) (identity P dir) where
  toFun p :=
    if h : dir p = .upward then
      ⟨.inBound p, (portIsSrc_identity_inBound P dir p).trans (beq_iff_eq.mpr h)⟩
    else
      ⟨.outBound p, (portIsSrc_identity_outBound P dir p).trans
        (beq_iff_eq.mpr (by cases hd : dir p <;> simp_all))⟩
  invFun
    | ⟨.inBound p, _⟩ => p
    | ⟨.outBound p, _⟩ => p
    | ⟨.couponIn c _, _⟩ => c.elim PEmpty.elim PEmpty.elim
    | ⟨.couponOut c _, _⟩ => c.elim PEmpty.elim PEmpty.elim
  left_inv p := by
    by_cases h : dir p = .upward <;> simp [h]
  right_inv := by
    rintro ⟨p, hp⟩
    rcases p with p | p | ⟨c | c, _⟩ | ⟨c | c, _⟩
    · have hp' : dir p = .upward :=
        beq_iff_eq.mp ((portIsSrc_identity_inBound P dir p).symm.trans hp)
      exact Subtype.ext (by simp [hp'])
    · have hp' : dir p = .downward :=
        beq_iff_eq.mp ((portIsSrc_identity_outBound P dir p).symm.trans hp)
      exact Subtype.ext (by simp [hp'])
    · exact c.elim
    · exact c.elim
    · exact c.elim
    · exact c.elim

/-- Retained target port equivalence `P ≃ GlueTgt (identity P dir) (identity P dir)`. -/
def identityGlueTgtEquiv (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    P ≃ GlueTgt (identity P dir) (identity P dir) where
  toFun p :=
    if h : dir p = .upward then
      ⟨.outBound p, (portIsSrc_identity_outBound P dir p).trans
        (beq_eq_false_iff_ne.mpr (by simp [h]))⟩
    else
      ⟨.inBound p, (portIsSrc_identity_inBound P dir p).trans (beq_eq_false_iff_ne.mpr h)⟩
  invFun
    | ⟨.inBound p, _⟩ => p
    | ⟨.outBound p, _⟩ => p
    | ⟨.couponIn c _, _⟩ => c.elim PEmpty.elim PEmpty.elim
    | ⟨.couponOut c _, _⟩ => c.elim PEmpty.elim PEmpty.elim
  left_inv p := by
    by_cases h : dir p = .upward <;> simp [h]
  right_inv := by
    rintro ⟨p, hp⟩
    rcases p with p | p | ⟨c | c, _⟩ | ⟨c | c, _⟩
    · have hp' : dir p ≠ .upward :=
        beq_eq_false_iff_ne.mp ((portIsSrc_identity_inBound P dir p).symm.trans hp)
      exact Subtype.ext (by simp [hp'])
    · have hp' : dir p = .upward := by
        have hne := beq_eq_false_iff_ne.mp ((portIsSrc_identity_outBound P dir p).symm.trans hp)
        cases hd : dir p <;> simp_all
      exact Subtype.ext (by simp [hp'])
    · exact c.elim
    · exact c.elim
    · exact c.elim
    · exact c.elim

theorem val_identityGlueSrcEquiv (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir)
    (p : P) : (identityGlueSrcEquiv P dir p).1 =
      match dir p with | .upward => .inBound p | .downward => .outBound p := by
  cases h : dir p <;> simp [identityGlueSrcEquiv, h]

theorem val_identityGlueTgtEquiv (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir)
    (p : P) : (identityGlueTgtEquiv P dir p).1 =
      match dir p with | .upward => .outBound p | .downward => .inBound p := by
  cases h : dir p <;> simp [identityGlueTgtEquiv, h]

theorem seamStep_identity_inl (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir)
    (p : P) :
    seamStep (identity P dir) (identity P dir) (OrderIso.refl P) (identitySeamCompat P dir)
      (.inl (identityGlueSrcEquiv P dir p)) = .inr p := by
  cases h : dir p
  · have hsrc : glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inl p) = .inl (identityGlueSrcEquiv P dir p) := by
      refine glueSrcEquiv_eq_of_unclassify ?_
      dsimp only [unclassifySrcPort, Sum.map_inl]
      rw [val_identityGlueSrcEquiv, h]
      simp [identity, h]
      rfl
    have htgt : glueTgtEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inl p) = .inr p := by
      refine glueTgtEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inl, unclassifyTgtPort, seamTgtPort]
      rw [outDir_identity]
      simp [identity, h]
    rw [← hsrc]
    exact (seamStep_glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
      (identitySeamCompat P dir) (.inl p)).trans htgt
  · have hsrc : glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inr p) = .inl (identityGlueSrcEquiv P dir p) := by
      refine glueSrcEquiv_eq_of_unclassify ?_
      dsimp only [unclassifySrcPort, Sum.map_inr]
      rw [val_identityGlueSrcEquiv, h]
      simp [identity, h]
      rfl
    have htgt : glueTgtEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inr p) = .inr p := by
      refine glueTgtEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inr, unclassifyTgtPort, seamTgtPort]
      rw [outDir_identity]
      simp [identity, h]
      rfl
    rw [← hsrc]
    exact (seamStep_glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
      (identitySeamCompat P dir) (.inr p)).trans htgt

theorem seamStep_identity_inr (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir)
    (p : P) :
    seamStep (identity P dir) (identity P dir) (OrderIso.refl P) (identitySeamCompat P dir)
      (.inr p) = .inl (identityGlueTgtEquiv P dir p) := by
  cases h : dir p
  · have hsrc : glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inr p) = .inr p := by
      refine glueSrcEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inr, unclassifySrcPort, seamSrcPort]
      rw [outDir_identity]
      simp [identity, h]
      rfl
    have htgt : glueTgtEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inr p) = .inl (identityGlueTgtEquiv P dir p) := by
      refine glueTgtEquiv_eq_of_unclassify ?_
      dsimp only [unclassifyTgtPort, Sum.map_inr]
      rw [val_identityGlueTgtEquiv, h]
      simp [identity, h]
      rfl
    rw [← hsrc]
    exact (seamStep_glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
      (identitySeamCompat P dir) (.inr p)).trans htgt
  · have hsrc : glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inl p) = .inr p := by
      refine glueSrcEquiv_eq_of_unclassify ?_
      dsimp only [Sum.map_inl, unclassifySrcPort, seamSrcPort]
      rw [outDir_identity]
      simp [identity, h]
    have htgt : glueTgtEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
        (identitySeamCompat P dir) (.inl p) = .inl (identityGlueTgtEquiv P dir p) := by
      refine glueTgtEquiv_eq_of_unclassify ?_
      dsimp only [unclassifyTgtPort, Sum.map_inl]
      rw [val_identityGlueTgtEquiv, h]
      simp [identity, h]
      rfl
    rw [← hsrc]
    exact (seamStep_glueSrcEquiv (identity P dir) (identity P dir) (OrderIso.refl P)
      (identitySeamCompat P dir) (.inl p)).trans htgt

/-- Gluing `identity P dir` vertically to itself suppresses the intermediate seam vertices and
returns `identity P dir`. -/
def identityGlueIdentityIso (P : Type u) [Fintype P] [LinearOrder P] (dir : P → StrandDir) :
    ((identity P dir).glue (identity P dir) (OrderIso.refl P) (identitySeamCompat P dir)).Iso
      (identity P dir) :=
  let S := seamStep (identity P dir) (identity P dir) (OrderIso.refl P) (identitySeamCompat P dir)
  letI : IsEmpty S.TraceLoop := S.isEmpty_traceLoop_of_forall_isOpenSeam fun p =>
    ⟨identityGlueTgtEquiv P dir p, 0, Equiv.traceStep_zero_iff.mpr (seamStep_identity_inr P dir p)⟩
  { inPort := OrderIso.refl P
    outPort := OrderIso.refl P
    coupon := Equiv.sumEmpty PEmpty PEmpty
    couponIn
      | .inl c => c.elim
      | .inr c => c.elim
    couponOut
      | .inl c => c.elim
      | .inr c => c.elim
    edge := (identityGlueSrcEquiv P dir).symm
    circle := ((Equiv.sumEmpty PEmpty PEmpty).sumCongr (Equiv.refl _)).trans
      (Equiv.sumEmpty PEmpty _)
    map_src e := by
      obtain ⟨p, rfl⟩ := (identityGlueSrcEquiv P dir).surjective e
      dsimp only [glue, identity]
      erw [(identityGlueSrcEquiv P dir).symm_apply_apply p, val_identityGlueSrcEquiv]
      cases dir p <;> rfl
    map_tgt e := by
      obtain ⟨p, rfl⟩ := (identityGlueSrcEquiv P dir).surjective e
      have htr : S.trace (identityGlueSrcEquiv P dir p) = identityGlueTgtEquiv P dir p :=
        S.trace_apply_eq_iff.mpr ⟨1, .succ (seamStep_identity_inl P dir p)
          (Equiv.traceStep_zero_iff.mpr (seamStep_identity_inr P dir p))⟩
      dsimp only [glue, identity]
      erw [(identityGlueSrcEquiv P dir).symm_apply_apply p, htr, val_identityGlueTgtEquiv]
      cases dir p <;> rfl }

/-- Gluing two matching single-interval strands suppresses the interior seam vertex and yields a
single interval strand rather than two subdivided edges. -/
def singleIntervalGlueIso (d : StrandDir) :
    ((singleInterval.{u} d).glue (singleInterval.{u} d) (OrderIso.refl PUnit)
      (identitySeamCompat PUnit (fun _ => d))).Iso (singleInterval.{u} d) :=
  identityGlueIdentityIso PUnit (fun _ => d)

@[simp]
theorem edgeCount_glue_singleInterval (d : StrandDir) :
    ((singleInterval.{u} d).glue (singleInterval.{u} d) (OrderIso.refl PUnit)
      (identitySeamCompat PUnit (fun _ => d))).edgeCount = 1 :=
  (singleIntervalGlueIso d).edgeCount_eq.trans (edgeCount_singleInterval d)

@[simp]
theorem circleCount_glue_singleInterval (d : StrandDir) :
    ((singleInterval.{u} d).glue (singleInterval.{u} d) (OrderIso.refl PUnit)
      (identitySeamCompat PUnit (fun _ => d))).circleCount = 0 :=
  (singleIntervalGlueIso d).circleCount_eq.trans (circleCount_singleInterval d)

@[simp]
theorem componentCount_glue_singleInterval (d : StrandDir) :
    ((singleInterval.{u} d).glue (singleInterval.{u} d) (OrderIso.refl PUnit)
      (identitySeamCompat PUnit (fun _ => d))).componentCount = 1 :=
  (singleIntervalGlueIso d).componentCount_eq.trans (componentCount_singleInterval d)

@[simp]
theorem componentCount_disjointUnion_singleInterval (d₁ d₂ : StrandDir) :
    ((singleInterval.{u} d₁).disjointUnion (singleInterval.{u} d₂)).componentCount = 2 := by
  rw [componentCount_disjointUnion, componentCount_singleInterval, componentCount_singleInterval]

end IdentityGlue

end DiagramIncidence

end TauCeti
