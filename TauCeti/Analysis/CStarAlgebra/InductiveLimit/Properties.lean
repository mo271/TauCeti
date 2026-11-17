/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.RingTheory.SimpleRing.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Basic
public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Functionals, separability, ideal structure, and simplicity of C⋆-inductive limits

This file establishes the structural properties of `TauCeti.CStarInductiveLimit` following
Blackadar, Section II.8.2:

* **Positive functionals, states, and traces** (`liftPositiveFunctional`, `liftState`,
  `liftPositiveFunctional_mul_comm`, `liftState_mul_comm`): every uniformly norm-bounded compatible
  family of positive linear functionals extends uniquely to a positive functional on the C⋆-limit;
  compatible families of states (and tracial states) extend uniquely to a state (and tracial state)
  of the limit, even without unitality.
* **Separability** (`instSeparableSpace`): a countable directed system of separable C⋆-algebras
  has a separable C⋆-inductive limit.
* **Closed two-sided ideal structure** (`ideal_coe_eq_closure_inter`,
  `ideal_coe_eq_closure_iUnion`, `ideal_eq_of_comap_eq`, Blackadar II.8.2.4): every closed
  two-sided ideal `I` of `CStarInductiveLimit A f` is the closure of the union of the images of its
  stage preimages `TwoSidedIdeal.comap (of A f i) I`.
* **Simplicity preservation** (`isClosed_ideal_eq_bot_or_eq_top`, `isSimpleRing`, Blackadar
  II.8.2.5): if every stage has no nontrivial closed two-sided ideals, then neither does the
  C⋆-inductive limit; in the unital case, a C⋆-inductive limit of simple C⋆-algebras is simple
  (`IsSimpleRing`).
* **Non-vacuity examples**: collapsing noninjective systems (`subsingleton_of_eventually_zero`) and
  the `2^∞` UHF / CAR matrix C⋆-inductive limit (`carTransition`, `CARAlgebra`), verified to be
  nontrivial, separable, and simple.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Section II.8.2 (Proposition II.8.2.4 and Corollary II.8.2.5).
-/

public section

noncomputable section

open Filter Topology TopologicalSpace
open scoped CStarAlgebra ComplexOrder

namespace TauCeti.CStarInductiveLimit

section PositiveFunctionals

section NonUnitalPositive

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)] [∀ i, PartialOrder (A i)]
variable [∀ i, StarOrderedRing (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

variable (A f) in
/-- **Extension of compatible positive linear functionals.** A uniformly norm-bounded compatible
family of positive continuous linear functionals `ω i : A i →P[ℂ] ℂ` extends uniquely to a
positive continuous linear functional on `CStarInductiveLimit A f`. -/
def liftPositiveFunctional (ω : ∀ i, A i →P[ℂ] ℂ)
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    {C : ℝ} (hC : ∀ i, ‖(ω i : A i →L[ℂ] ℂ)‖ ≤ C) :
    CStarInductiveLimit A f →P[ℂ] ℂ :=
  let L : CStarInductiveLimit A f →L[ℂ] ℂ :=
    liftCLM A f (fun i => (ω i : A i →L[ℂ] ℂ)) (by intro i j hij a; exact hω hij a) hC
  PositiveContinuousLinearMap.mk₀ L fun x hx => by
    obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
    clear hx
    induction y using induction_on with
    | hp =>
      have hcl : IsClosed (Set.Ici (0 : ℂ)) := isClosed_Ici
      exact hcl.preimage (L.continuous.comp (continuous_star.mul continuous_id))
    | ih i a =>
      dsimp only [L]
      rw [← map_star, ← map_mul, liftCLM_of]
      exact (ω i).map_nonneg (star_mul_self_nonneg a)

/-- The underlying continuous linear map of `liftPositiveFunctional` is `liftCLM`. -/
@[simp]
theorem toContinuousLinearMap_liftPositiveFunctional (ω : ∀ i, A i →P[ℂ] ℂ)
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    {C : ℝ} (hC : ∀ i, ‖(ω i : A i →L[ℂ] ℂ)‖ ≤ C) :
    (liftPositiveFunctional A f ω hω hC : CStarInductiveLimit A f →L[ℂ] ℂ) =
      liftCLM A f (fun i => (ω i : A i →L[ℂ] ℂ)) (by intro i j hij a; exact hω hij a) hC :=
  PositiveContinuousLinearMap.toContinuousLinearMap_mk₀ _ _

/-- Evaluating `liftPositiveFunctional` on stage `i` recovers `ω i`. -/
@[simp]
theorem liftPositiveFunctional_of (ω : ∀ i, A i →P[ℂ] ℂ)
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    {C : ℝ} (hC : ∀ i, ‖(ω i : A i →L[ℂ] ℂ)‖ ≤ C) (i : ι) (a : A i) :
    liftPositiveFunctional A f ω hω hC (of A f i a) = ω i a := by
  rw [liftPositiveFunctional, PositiveContinuousLinearMap.mk₀_apply]
  exact liftCLM_of (f := f) (fun i => (ω i : A i →L[ℂ] ℂ))
    (by intro i j hij a; exact hω hij a) hC i a

/-- The operator norm of `liftPositiveFunctional` is bounded by the uniform stage bound `C`. -/
theorem opNorm_liftPositiveFunctional_le (ω : ∀ i, A i →P[ℂ] ℂ)
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    {C : ℝ} (hC : ∀ i, ‖(ω i : A i →L[ℂ] ℂ)‖ ≤ C) :
    ‖(liftPositiveFunctional A f ω hω hC : CStarInductiveLimit A f →L[ℂ] ℂ)‖ ≤ C := by
  rw [toContinuousLinearMap_liftPositiveFunctional]
  exact opNorm_liftCLM_le (fun i => (ω i : A i →L[ℂ] ℂ))
    (by intro i j hij a; exact hω hij a) hC

/-- Uniqueness of `liftPositiveFunctional`: any positive continuous linear functional agreeing with
`ω` on every stage equals `liftPositiveFunctional A f ω hω hC`. -/
theorem liftPositiveFunctional_unique (ω : ∀ i, A i →P[ℂ] ℂ)
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    {C : ℝ} (hC : ∀ i, ‖(ω i : A i →L[ℂ] ℂ)‖ ≤ C)
    {ψ : CStarInductiveLimit A f →P[ℂ] ℂ} (hψ : ∀ i (a : A i), ψ (of A f i a) = ω i a) :
    ψ = liftPositiveFunctional A f ω hω hC := by
  ext x
  have hclm : (ψ : CStarInductiveLimit A f →L[ℂ] ℂ) =
      (liftPositiveFunctional A f ω hω hC : CStarInductiveLimit A f →L[ℂ] ℂ) :=
    continuousLinearMap_ext fun i a => by
      change ψ (of A f i a) = liftPositiveFunctional A f ω hω hC (of A f i a)
      rw [hψ i a, liftPositiveFunctional_of]
  exact DFunLike.congr_fun hclm x

/-- **Traciality passes to the inductive limit.** If each stage functional `ω i` is tracial, then
`liftPositiveFunctional A f ω hω hC` is tracial on `CStarInductiveLimit A f`. -/
theorem liftPositiveFunctional_mul_comm (ω : ∀ i, A i →P[ℂ] ℂ)
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    {C : ℝ} (hC : ∀ i, ‖(ω i : A i →L[ℂ] ℂ)‖ ≤ C)
    (htr : ∀ i (a b : A i), ω i (a * b) = ω i (b * a)) (x y : CStarInductiveLimit A f) :
    liftPositiveFunctional A f ω hω hC (x * y) =
      liftPositiveFunctional A f ω hω hC (y * x) := by
  let L := (liftPositiveFunctional A f ω hω hC : CStarInductiveLimit A f →L[ℂ] ℂ)
  induction x, y using induction_on₂ with
  | hp =>
    exact isClosed_eq (L.continuous.comp continuous_mul)
      (L.continuous.comp (continuous_snd.mul continuous_fst))
  | ih i a b =>
    change liftPositiveFunctional A f ω hω hC (of A f i a * of A f i b) =
      liftPositiveFunctional A f ω hω hC (of A f i b * of A f i a)
    rw [← map_mul, ← map_mul, liftPositiveFunctional_of, liftPositiveFunctional_of]
    exact htr i a b

private def stageStatePositive (ω : ∀ i, WeakDual ℂ (A i))
    (hstate : ∀ i, ω i ∈ stateSpace (A i)) (i : ι) : A i →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.mk₀ (WeakDual.toStrongDual (ω i)) fun a ha => by
    rw [WeakDual.toStrongDual_apply]
    exact map_nonneg_of_mem_stateSpace (hstate i) ha

omit [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] in
private theorem stageStatePositive_apply (ω : ∀ i, WeakDual ℂ (A i))
    (hstate : ∀ i, ω i ∈ stateSpace (A i)) (i : ι) (a : A i) :
    stageStatePositive ω hstate i a = ω i a := by
  rw [stageStatePositive, PositiveContinuousLinearMap.mk₀_apply, WeakDual.toStrongDual_apply]

variable (A f) in
/-- **Extension of compatible states.** A compatible family of states `ω i ∈ stateSpace (A i)` on
a directed system of C⋆-algebras extends uniquely to a state on `CStarInductiveLimit A f`. -/
def liftState (ω : ∀ i, WeakDual ℂ (A i)) (hstate : ∀ i, ω i ∈ stateSpace (A i))
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a) :
    WeakDual ℂ (CStarInductiveLimit A f) :=
  let Φ := liftPositiveFunctional A f (stageStatePositive ω hstate)
    (fun _ _ hij a => by
      rw [stageStatePositive_apply, stageStatePositive_apply]
      exact hω hij a)
    (C := 1) fun i => by
      have hcoe : (stageStatePositive ω hstate i : A i →L[ℂ] ℂ) =
          WeakDual.toStrongDual (ω i) :=
        PositiveContinuousLinearMap.toContinuousLinearMap_mk₀ _ _
      rw [hcoe, norm_toStrongDual_of_mem_stateSpace (hstate i)]
  StrongDual.toWeakDual (Φ : CStarInductiveLimit A f →L[ℂ] ℂ)

/-- Evaluating `liftState` on stage `i` recovers `ω i`. -/
@[simp]
theorem liftState_of (ω : ∀ i, WeakDual ℂ (A i)) (hstate : ∀ i, ω i ∈ stateSpace (A i))
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    (i : ι) (a : A i) :
    liftState A f ω hstate hω (of A f i a) = ω i a := by
  unfold liftState
  rw [StrongDual.toWeakDual_apply]
  exact (liftPositiveFunctional_of _ _ _ i a).trans (stageStatePositive_apply ω hstate i a)

/-- `liftState` lies in the state space of `CStarInductiveLimit A f`. -/
theorem liftState_mem_stateSpace (ω : ∀ i, WeakDual ℂ (A i))
    (hstate : ∀ i, ω i ∈ stateSpace (A i))
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a) :
    liftState A f ω hstate hω ∈ stateSpace (CStarInductiveLimit A f) := by
  rw [mem_stateSpace_iff]
  refine ⟨fun x hx => ?_, le_antisymm ?_ ?_⟩
  · unfold liftState
    rw [StrongDual.toWeakDual_apply]
    exact PositiveContinuousLinearMap.map_nonneg _ hx
  · unfold liftState
    rw [StrongDual.toStrongDual_toWeakDual]
    exact opNorm_liftPositiveFunctional_le _ _ _
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    rw [← norm_toStrongDual_of_mem_stateSpace (hstate i₀)]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_
    calc
      ‖WeakDual.toStrongDual (ω i₀) a‖
          = ‖WeakDual.toStrongDual (liftState A f ω hstate hω) (of A f i₀ a)‖ := by
        rw [WeakDual.toStrongDual_apply, WeakDual.toStrongDual_apply, liftState_of]
      _ ≤ ‖WeakDual.toStrongDual (liftState A f ω hstate hω)‖ * ‖of A f i₀ a‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖WeakDual.toStrongDual (liftState A f ω hstate hω)‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le (of A f i₀) a) (norm_nonneg _)

/-- Pulling `liftState` back along the stage embedding `of A f i` recovers `ω i`. -/
@[simp]
theorem pullbackFunctional_liftState (ω : ∀ i, WeakDual ℂ (A i))
    (hstate : ∀ i, ω i ∈ stateSpace (A i))
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a) (i : ι) :
    pullbackFunctional (A i) (of A f i) (liftState A f ω hstate hω) = ω i :=
  DFunLike.ext _ _ fun a => by
    rw [pullbackFunctional_apply]
    exact liftState_of ω hstate hω i a

/-- Uniqueness of `liftState`: any weak-* continuous functional agreeing with `ω` on every stage
equals `liftState A f ω hstate hω`. -/
theorem liftState_unique (ω : ∀ i, WeakDual ℂ (A i))
    (hstate : ∀ i, ω i ∈ stateSpace (A i))
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    {ψ : WeakDual ℂ (CStarInductiveLimit A f)}
    (hψ : ∀ i (a : A i), ψ (of A f i a) = ω i a) :
    ψ = liftState A f ω hstate hω := by
  have hclm : WeakDual.toStrongDual ψ = WeakDual.toStrongDual (liftState A f ω hstate hω) :=
    continuousLinearMap_ext fun i a => by
      rw [WeakDual.toStrongDual_apply, WeakDual.toStrongDual_apply, hψ i a, liftState_of]
  exact DFunLike.ext _ _ fun x => DFunLike.congr_fun hclm x

/-- **Tracial state extension.** If each stage state `ω i` is tracial, then `liftState` is a
tracial state on `CStarInductiveLimit A f`. -/
theorem liftState_mul_comm (ω : ∀ i, WeakDual ℂ (A i))
    (hstate : ∀ i, ω i ∈ stateSpace (A i))
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    (htr : ∀ i (a b : A i), ω i (a * b) = ω i (b * a)) (x y : CStarInductiveLimit A f) :
    liftState A f ω hstate hω (x * y) = liftState A f ω hstate hω (y * x) := by
  unfold liftState
  rw [StrongDual.toWeakDual_apply, StrongDual.toWeakDual_apply]
  refine liftPositiveFunctional_mul_comm _ _ _ (fun i a b => ?_) x y
  rw [stageStatePositive_apply, stageStatePositive_apply]
  exact htr i a b

end NonUnitalPositive

section UnitalState

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, CStarAlgebra (A i)] [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable [∀ i j h, AlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- Evaluating `liftState` on the unital stage embedding `ofUnital A f i` recovers `ω i`. -/
theorem liftState_ofUnital (ω : ∀ i, WeakDual ℂ (A i))
    (hstate : ∀ i, ω i ∈ stateSpace (A i))
    (hω : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), ω j (f i j hij a) = ω i a)
    (i : ι) (a : A i) :
    liftState A f ω hstate hω (ofUnital A f i a) = ω i a := by
  rw [ofUnital_apply, liftState_of]

end UnitalState

end PositiveFunctionals

section Separability

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- **Separability of countable C⋆-inductive limits.** If `ι` is countable and every stage `A i`
is separable, then `CStarInductiveLimit A f` is separable. -/
instance instSeparableSpace [Countable ι] [∀ i, SeparableSpace (A i)] :
    SeparableSpace (CStarInductiveLimit A f) := by
  choose D hDc hDd using fun i => TopologicalSpace.exists_countable_dense (A i)
  refine ⟨⟨⋃ i, of A f i '' D i,
    Set.countable_iUnion fun i => (hDc i).image _, fun x => ?_⟩⟩
  induction x using induction_on with
  | hp => exact isClosed_closure
  | ih i a =>
    have ha : a ∈ closure (D i) := hDd i a
    have hmem : of A f i a ∈ closure (of A f i '' D i) :=
      image_closure_subset_closure_image (map_continuous (of A f i)) ⟨a, ha, rfl⟩
    exact closure_mono (Set.subset_iUnion (fun i => of A f i '' D i) i) hmem

end Separability

section IdealStructure

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- Helper: the closure of `(I : Set _) ∩ ⋃ i, Set.range (of A f i)` is a closed two-sided ideal
contained in `I`. -/
private def stageClosureIdeal (I : TwoSidedIdeal (CStarInductiveLimit A f)) :
    TwoSidedIdeal (CStarInductiveLimit A f) :=
  let S : Set (CStarInductiveLimit A f) := (I : Set _) ∩ ⋃ i, Set.range (of A f i)
  TwoSidedIdeal.mk' (closure S)
    (subset_closure <| by
      obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨I.zero_mem, Set.mem_iUnion.2 ⟨i, 0, map_zero (of A f i)⟩⟩)
    (fun hx hy => map_mem_closure₂ continuous_add hx hy fun _ ha _ hb => by
      rcases Set.mem_iUnion.1 ha.2 with ⟨i, a, rfl⟩
      rcases Set.mem_iUnion.1 hb.2 with ⟨j, b, rfl⟩
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      refine ⟨I.add_mem ha.1 hb.1, Set.mem_iUnion.2 ⟨k, f i k hik a + f j k hjk b, ?_⟩⟩
      rw [map_add, of_f hik, of_f hjk])
    (fun hx => map_mem_closure continuous_neg hx fun _ ha => by
      rcases Set.mem_iUnion.1 ha.2 with ⟨i, a, rfl⟩
      exact ⟨I.neg_mem ha.1, Set.mem_iUnion.2 ⟨i, -a, map_neg (of A f i) a⟩⟩)
    (fun {x y} hy => by
      induction x using induction_on with
      | hp => exact isClosed_closure.preimage (continuous_mul_const y)
      | ih j b =>
        refine map_mem_closure (continuous_const_mul (of A f j b)) hy fun _ ha => ?_
        rcases Set.mem_iUnion.1 ha.2 with ⟨i, a, rfl⟩
        obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
        refine ⟨I.mul_mem_left _ _ ha.1,
          Set.mem_iUnion.2 ⟨k, f j k hjk b * f i k hik a, ?_⟩⟩
        rw [map_mul, of_f hjk, of_f hik])
    (fun {x y} hx => by
      induction y using induction_on with
      | hp => exact isClosed_closure.preimage (continuous_const_mul x)
      | ih j b =>
        refine map_mem_closure (f := fun z => z * of A f j b)
          (continuous_mul_const (of A f j b)) hx fun _ ha => ?_
        rcases Set.mem_iUnion.1 ha.2 with ⟨i, a, rfl⟩
        obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
        refine ⟨I.mul_mem_right _ _ ha.1,
          Set.mem_iUnion.2 ⟨k, f i k hik a * f j k hjk b, ?_⟩⟩
        rw [map_mul, of_f hik, of_f hjk])

private theorem stage_quotient_norm_eq {I J : TwoSidedIdeal (CStarInductiveLimit A f)}
    (hI : IsClosed (I : Set (CStarInductiveLimit A f)))
    (hJ : IsClosed (J : Set (CStarInductiveLimit A f)))
    (hstage : ∀ i (a : A i), of A f i a ∈ J ↔ of A f i a ∈ I) (i : ι) (a : A i) :
    ‖TwoSidedIdeal.Quotient.mkStarAlgHom I (of A f i a)‖ =
      ‖TwoSidedIdeal.Quotient.mkStarAlgHom J (of A f i a)‖ := by
  let φ := TwoSidedIdeal.Quotient.mkStarAlgHom I
  let ψ := TwoSidedIdeal.Quotient.mkStarAlgHom J
  let K : TwoSidedIdeal (A i) := TwoSidedIdeal.ker (ψ.comp (of A f i))
  have hK_iff : ∀ b : A i, b ∈ K ↔ φ (of A f i b) = 0 := fun b => by
    rw [TwoSidedIdeal.mem_ker, NonUnitalStarAlgHom.comp_apply,
      TwoSidedIdeal.Quotient.mkStarAlgHom_apply, TwoSidedIdeal.Quotient.mkStarAlgHom_apply,
      TwoSidedIdeal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.Quotient.eq_zero_iff_mem, hstage]
  let θ : A i ⧸ K →⋆ₙₐ[ℂ] CStarInductiveLimit A f ⧸ I :=
    TwoSidedIdeal.Quotient.liftStarAlgHom K (φ.comp (of A f i)) fun b hb => (hK_iff b).mp hb
  have hθ_inj : Function.Injective θ :=
    TwoSidedIdeal.Quotient.liftStarAlgHom_injective_of_ker_le _ fun b hb =>
      (hK_iff b).mpr ((TwoSidedIdeal.mem_ker (φ.comp (of A f i))).mp hb)
  have h1 : ‖φ (of A f i a)‖ = ‖TwoSidedIdeal.Quotient.mk K a‖ := by
    rw [← NonUnitalStarAlgHom.comp_apply φ (of A f i),
      ← TwoSidedIdeal.Quotient.liftStarAlgHom_mk K (φ.comp (of A f i)) _ a]
    exact NonUnitalStarAlgHom.norm_map θ hθ_inj _
  have h2 : ‖ψ (of A f i a)‖ = ‖TwoSidedIdeal.Quotient.mk K a‖ := by
    rw [← NonUnitalStarAlgHom.comp_apply ψ (of A f i),
      ← (ψ.comp (of A f i)).quotientKerHom_mk a]
    exact NonUnitalStarAlgHom.norm_map _ (ψ.comp (of A f i)).quotientKerHom_injective _
  exact h1.trans h2.symm

/-- **Closed two-sided ideal structure (Blackadar II.8.2.4, intersection form).** Every closed
two-sided ideal `I` of `CStarInductiveLimit A f` is the closure of its intersection with the union
of the stage images. -/
theorem ideal_coe_eq_closure_inter (I : TwoSidedIdeal (CStarInductiveLimit A f))
    (hI : IsClosed (I : Set (CStarInductiveLimit A f))) :
    (I : Set (CStarInductiveLimit A f)) =
      closure ((I : Set (CStarInductiveLimit A f)) ∩ ⋃ i, Set.range (of A f i)) := by
  let J := stageClosureIdeal (A := A) (f := f) I
  have hJ_coe : (J : Set (CStarInductiveLimit A f)) =
      closure ((I : Set _) ∩ ⋃ i, Set.range (of A f i)) := by
    simp [J, stageClosureIdeal]
  have hJ_closed : IsClosed (J : Set (CStarInductiveLimit A f)) := by
    rw [hJ_coe]
    exact isClosed_closure
  have hJI : J ≤ I := fun x hx =>
    closure_minimal Set.inter_subset_left hI (hJ_coe ▸ SetLike.mem_coe.mpr hx)
  have hstage : ∀ i (a : A i), of A f i a ∈ J ↔ of A f i a ∈ I := fun i a =>
    ⟨fun h => hJI h, fun h => by
      rw [← SetLike.mem_coe, hJ_coe]
      exact subset_closure ⟨h, Set.mem_iUnion.2 ⟨i, a, rfl⟩⟩⟩
  let φ := TwoSidedIdeal.Quotient.mkStarAlgHom I
  let ψ := TwoSidedIdeal.Quotient.mkStarAlgHom J
  have hnorm : ∀ x : CStarInductiveLimit A f, ‖φ x‖ = ‖ψ x‖ := fun x => by
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_norm.comp (map_continuous φ))
        (continuous_norm.comp (map_continuous ψ))
    | ih i a => exact stage_quotient_norm_eq hI hJ_closed hstage i a
  have hIJ : I ≤ J := fun x hx => by
    rw [← TwoSidedIdeal.Quotient.eq_zero_iff_mem, ← TwoSidedIdeal.Quotient.mkStarAlgHom_apply,
      ← norm_eq_zero, ← hnorm x, norm_eq_zero, TwoSidedIdeal.Quotient.mkStarAlgHom_apply,
      TwoSidedIdeal.Quotient.eq_zero_iff_mem]
    exact hx
  exact (congrArg SetLike.coe (le_antisymm hIJ hJI)).trans hJ_coe

/-- **Closed two-sided ideal structure (Blackadar II.8.2.4, preimage form).** Every closed
two-sided ideal `I` of `CStarInductiveLimit A f` is the closure of the union of the stage images
of its preimages `TwoSidedIdeal.comap (of A f i) I`. -/
theorem ideal_coe_eq_closure_iUnion (I : TwoSidedIdeal (CStarInductiveLimit A f))
    (hI : IsClosed (I : Set (CStarInductiveLimit A f))) :
    (I : Set (CStarInductiveLimit A f)) =
      closure (⋃ i, of A f i '' (TwoSidedIdeal.comap (of A f i) I : Set (A i))) := by
  rw [ideal_coe_eq_closure_inter I hI]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_range, Set.mem_image, SetLike.mem_coe,
    TwoSidedIdeal.mem_comap]
  exact ⟨fun ⟨hx, i, a, ha⟩ => ⟨i, a, ha ▸ hx, ha⟩,
    fun ⟨i, a, ha, hxa⟩ => ⟨hxa ▸ ha, i, a, hxa⟩⟩

/-- Two closed two-sided ideals of `CStarInductiveLimit A f` with the same stage preimages are
equal. -/
theorem ideal_eq_of_comap_eq {I₁ I₂ : TwoSidedIdeal (CStarInductiveLimit A f)}
    (hI₁ : IsClosed (I₁ : Set (CStarInductiveLimit A f)))
    (hI₂ : IsClosed (I₂ : Set (CStarInductiveLimit A f)))
    (h : ∀ i, TwoSidedIdeal.comap (of A f i) I₁ = TwoSidedIdeal.comap (of A f i) I₂) :
    I₁ = I₂ := by
  apply SetLike.coe_injective
  rw [ideal_coe_eq_closure_iUnion I₁ hI₁, ideal_coe_eq_closure_iUnion I₂ hI₂]
  simp_rw [h]

end IdealStructure

section Simplicity

section NonUnitalSimplicity

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- **Topological simplicity passes to C⋆-inductive limits (Blackadar II.8.2.5).** If no stage
`A i` admits a nontrivial proper closed two-sided ideal, then neither does `CStarInductiveLimit A f`
(with no injectivity or unitality assumption on the transition maps). -/
theorem isClosed_ideal_eq_bot_or_eq_top
    (hsimple : ∀ i (J : TwoSidedIdeal (A i)), IsClosed (J : Set (A i)) → J = ⊥ ∨ J = ⊤)
    (I : TwoSidedIdeal (CStarInductiveLimit A f))
    (hI : IsClosed (I : Set (CStarInductiveLimit A f))) :
    I = ⊥ ∨ I = ⊤ := by
  by_cases hzero : ∀ i (a : A i), of A f i a ∈ I → of A f i a = 0
  · left
    apply le_bot_iff.mp
    rw [← SetLike.coe_subset_coe, ideal_coe_eq_closure_inter I hI]
    refine closure_minimal ?_ (by rw [TwoSidedIdeal.coe_bot]; exact isClosed_singleton)
    rintro x ⟨hxI, hxU⟩
    rcases Set.mem_iUnion.1 hxU with ⟨i, a, rfl⟩
    rw [TwoSidedIdeal.coe_bot, Set.mem_singleton_iff]
    exact hzero i a hxI
  · right
    push Not at hzero
    obtain ⟨i₀, a₀, ha₀I, ha₀ne⟩ := hzero
    rw [eq_top_iff, ← SetLike.coe_subset_coe, TwoSidedIdeal.coe_top,
      ← (dense_iUnion_range_of (A := A) (f := f)).closure_eq]
    refine closure_minimal (Set.iUnion_subset fun k => ?_) hI
    rintro _ ⟨c, rfl⟩
    obtain ⟨j, hi₀j, hkj⟩ := directed_of (· ≤ ·) i₀ k
    let Jj : TwoSidedIdeal (A j) := TwoSidedIdeal.comap (of A f j) I
    have hJj_closed : IsClosed (Jj : Set (A j)) := by
      have hset : (Jj : Set (A j)) = of A f j ⁻¹' (I : Set _) :=
        Set.ext fun _ => TwoSidedIdeal.mem_comap (of A f j)
      rw [hset]
      exact hI.preimage (map_continuous (of A f j))
    have hJj_ne_bot : Jj ≠ ⊥ := by
      intro hbot
      have hmem : f i₀ j hi₀j a₀ ∈ Jj := by
        rw [TwoSidedIdeal.mem_comap, of_f hi₀j]
        exact ha₀I
      rw [hbot, TwoSidedIdeal.mem_bot] at hmem
      exact ha₀ne (by rw [← of_f hi₀j, hmem, map_zero])
    have hJj_top : Jj = ⊤ := (hsimple j Jj hJj_closed).resolve_left hJj_ne_bot
    have hc_mem : f k j hkj c ∈ Jj := hJj_top ▸ trivial
    rw [TwoSidedIdeal.mem_comap, of_f hkj] at hc_mem
    exact hc_mem

end NonUnitalSimplicity

section UnitalSimplicity

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, CStarAlgebra (A i)]
variable [∀ i j h, AlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- **Simplicity of unital C⋆-inductive limits (Blackadar II.8.2.5).** A unital C⋆-inductive
limit of simple C⋆-algebras is a simple ring (`IsSimpleRing`). -/
theorem isSimpleRing [∀ i, IsSimpleRing (A i)] :
    IsSimpleRing (CStarInductiveLimit A f) := by
  have hnt : Nontrivial (CStarInductiveLimit A f) := instNontrivial
  have hntI : Nontrivial (TwoSidedIdeal (CStarInductiveLimit A f)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have h1 : (1 : CStarInductiveLimit A f) ∈ (⊥ : TwoSidedIdeal (CStarInductiveLimit A f)) :=
      h ▸ trivial
    exact one_ne_zero ((TwoSidedIdeal.mem_bot _).mp h1)
  refine ⟨⟨fun I => ?_⟩⟩
  by_cases hI : I = ⊤
  · exact Or.inr hI
  · left
    have hcl_ne_top : I.topologicalClosure ≠ ⊤ := by
      intro htop
      have h1 : (1 : CStarInductiveLimit A f) ∈ closure (I : Set (CStarInductiveLimit A f)) :=
        I.mem_topologicalClosure.mp (htop ▸ trivial)
      have hsub : (I : Set (CStarInductiveLimit A f)) ⊆ {x | IsUnit x}ᶜ := by
        rintro x hx ⟨u, rfl⟩
        have h1I : (1 : CStarInductiveLimit A f) ∈ I := by
          simpa using I.mul_mem_left (u⁻¹ : (CStarInductiveLimit A f)ˣ) u hx
        exact hI (eq_top_iff.mpr fun z _ => by simpa using I.mul_mem_left z 1 h1I)
      exact closure_minimal hsub Units.isOpen.isClosed_compl h1 isUnit_one
    have hstage_simple :
        ∀ i (J : TwoSidedIdeal (A i)), IsClosed (J : Set (A i)) → J = ⊥ ∨ J = ⊤ :=
      fun i J _ => IsSimpleOrder.eq_bot_or_eq_top J
    have hcl_bot : I.topologicalClosure = ⊥ :=
      (isClosed_ideal_eq_bot_or_eq_top hstage_simple I.topologicalClosure
        I.isClosed_topologicalClosure).resolve_right hcl_ne_top
    exact le_bot_iff.mp (I.le_topologicalClosure.trans hcl_bot.le)

end UnitalSimplicity

end Simplicity

section Examples

section Collapsing

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- **Collapsing noninjective systems.** If every stage eventually maps to `0`, then the
C⋆-inductive limit collapses to a subsingleton. -/
theorem subsingleton_of_eventually_zero
    (h0 : ∀ i, ∃ j, ∃ h : i ≤ j, ∀ a : A i, f i j h a = 0) :
    Subsingleton (CStarInductiveLimit A f) := by
  have hall : ∀ x : CStarInductiveLimit A f, x = 0 := fun x => by
    induction x using induction_on with
    | hp => exact isClosed_eq continuous_id continuous_const
    | ih i a =>
      obtain ⟨j, hij, hj⟩ := h0 i
      rw [← of_f hij a, hj a, map_zero]
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

end Collapsing

section CAR

private theorem car_eq_iff {m n : ℕ} (h : m ≤ n) (x y : Fin n → Bool) :
    ((∀ k : Fin n, m ≤ k.1 → x k = y k) ∧
      (fun k => x (Fin.castLE h k)) = (fun k => y (Fin.castLE h k))) ↔ x = y := by
  refine ⟨fun ⟨htail, hhead⟩ => funext fun k => ?_,
    fun hxy => hxy ▸ ⟨fun _ _ => rfl, rfl⟩⟩
  by_cases hk : m ≤ k.1
  · exact htail k hk
  · exact congrFun hhead ⟨k.1, Nat.lt_of_not_ge hk⟩

private def carEntry {m n : ℕ} (h : m ≤ n)
    (M : (Fin m → Bool) → (Fin m → Bool) → ℂ) (x y : Fin n → Bool) : ℂ :=
  if ∀ k : Fin n, m ≤ k.1 → x k = y k then
    M (fun k => x (Fin.castLE h k)) (fun k => y (Fin.castLE h k))
  else 0

private theorem carEntry_diag {m n : ℕ} (h : m ≤ n) (c : ℂ) (x y : Fin n → Bool) :
    carEntry h (fun u v => if u = v then c else 0) x y = if x = y then c else 0 := by
  unfold carEntry
  by_cases hxy : x = y
  · subst hxy; simp
  · simp only [hxy, ↓reduceIte]
    split_ifs with htail hhead
    · exact absurd ((car_eq_iff h x y).mp ⟨htail, hhead⟩) hxy
    · rfl
    · rfl

private theorem carEntry_star {m n : ℕ} (h : m ≤ n)
    (M : (Fin m → Bool) → (Fin m → Bool) → ℂ) (x y : Fin n → Bool) :
    carEntry h (fun u v => star (M v u)) x y = star (carEntry h M y x) := by
  unfold carEntry
  have heq : (∀ k : Fin n, m ≤ k.1 → x k = y k) ↔ (∀ k : Fin n, m ≤ k.1 → y k = x k) :=
    forall_congr' fun _ => imp_congr_right fun _ => eq_comm
  by_cases h1 : ∀ k : Fin n, m ≤ k.1 → x k = y k
  · simp only [eq_true h1, eq_true (heq.mp h1), ↓reduceIte]
  · simp only [eq_false h1, eq_false (mt heq.mpr h1), ↓reduceIte, star_zero]

private theorem carEntry_mul {m n : ℕ} (h : m ≤ n)
    (M N : (Fin m → Bool) → (Fin m → Bool) → ℂ) (x y : Fin n → Bool) :
    carEntry h (fun u v => ∑ w : Fin m → Bool, M u w * N w v) x y =
      ∑ z : Fin n → Bool, carEntry h M x z * carEntry h N z y := by
  by_cases hxy : ∀ k : Fin n, m ≤ k.1 → x k = y k
  · have hsub : ∑ z : Fin n → Bool, carEntry h M x z * carEntry h N z y =
        ∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => ∀ k : Fin n, m ≤ k.1 → x k = z k),
          carEntry h M x z * carEntry h N z y :=
      (Finset.sum_subset (Finset.filter_subset _ _) fun z _ hz => by
        have hxz : ¬ ∀ k : Fin n, m ≤ k.1 → x k = z k := fun hxz =>
          hz (Finset.mem_filter.2 ⟨Finset.mem_univ z, hxz⟩)
        simp only [carEntry, eq_false hxz, ↓reduceIte, zero_mul]).symm
    rw [hsub, carEntry]
    simp only [eq_true hxy, ↓reduceIte]
    symm
    refine Finset.sum_nbij'
      (fun z => fun k => z (Fin.castLE h k))
      (fun w => fun k => if hk : k.1 < m then w ⟨k.1, hk⟩ else x k)
      (fun _ _ => Finset.mem_univ _)
      (fun w _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k hk => by
        simp [Nat.not_lt.mpr hk]⟩)
      (fun z hz => funext fun k => by
        by_cases hk : k.1 < m
        · simp [hk]
        · simp [hk, (Finset.mem_filter.1 hz).2 k (Nat.le_of_not_lt hk)])
      (fun w _ => funext fun k => by simp [k.2])
      (fun z hz => by
        have hxz := (Finset.mem_filter.1 hz).2
        have hzy : ∀ k : Fin n, m ≤ k.1 → z k = y k := fun k hk =>
          (hxz k hk).symm.trans (hxy k hk)
        simp only [carEntry, eq_true hxz, eq_true hzy, ↓reduceIte])
  · simp only [carEntry, eq_false hxy, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hxz : ∀ k : Fin n, m ≤ k.1 → x k = z k
    · have hzy : ¬ ∀ k : Fin n, m ≤ k.1 → z k = y k := fun hzy =>
        hxy fun k hk => (hxz k hk).trans (hzy k hk)
      simp only [eq_false hzy, ↓reduceIte, mul_zero]
    · simp only [eq_false hxz, ↓reduceIte, zero_mul]

private theorem carEntry_self {n : ℕ}
    (M : (Fin n → Bool) → (Fin n → Bool) → ℂ) (x y : Fin n → Bool) :
    carEntry le_rfl M x y = M x y := by
  have hvac : ∀ k : Fin n, n ≤ k.1 → x k = y k := fun k hk => absurd hk (Nat.not_le.mpr k.2)
  unfold carEntry
  simp only [eq_true hvac, ↓reduceIte]
  rfl

private theorem carEntry_comp {m n p : ℕ} (h₁₂ : m ≤ n) (h₂₃ : n ≤ p)
    (M : (Fin m → Bool) → (Fin m → Bool) → ℂ) (x y : Fin p → Bool) :
    carEntry h₂₃ (carEntry h₁₂ M) x y = carEntry (h₁₂.trans h₂₃) M x y := by
  unfold carEntry
  have hiff : ((∀ k : Fin p, n ≤ k.1 → x k = y k) ∧
      ∀ k : Fin n, m ≤ k.1 → x (Fin.castLE h₂₃ k) = y (Fin.castLE h₂₃ k)) ↔
      ∀ k : Fin p, m ≤ k.1 → x k = y k := by
    refine ⟨fun ⟨h1, h2⟩ k hk => ?_, fun hall => ⟨fun k hk => hall k (h₁₂.trans hk),
      fun k hk => hall (Fin.castLE h₂₃ k) hk⟩⟩
    by_cases hkn : n ≤ k.1
    · exact h1 k hkn
    · exact h2 ⟨k.1, Nat.lt_of_not_ge hkn⟩ hk
  by_cases h1 : ∀ k : Fin p, n ≤ k.1 → x k = y k
  · by_cases h2 : ∀ k : Fin n, m ≤ k.1 → x (Fin.castLE h₂₃ k) = y (Fin.castLE h₂₃ k)
    · simp only [eq_true h1, eq_true h2, eq_true (hiff.mp ⟨h1, h2⟩), ↓reduceIte]
      rfl
    · have hnot : ¬ ∀ k : Fin p, m ≤ k.1 → x k = y k := fun hall => h2 (hiff.mpr hall).2
      simp only [eq_true h1, eq_false h2, eq_false hnot, ↓reduceIte]
  · have hnot : ¬ ∀ k : Fin p, m ≤ k.1 → x k = y k := fun hall => h1 (hiff.mpr hall).1
    simp only [eq_false h1, eq_false hnot, ↓reduceIte]

private def carMatrixTransition (m n : ℕ) (h : m ≤ n) :
    Matrix (Fin m → Bool) (Fin m → Bool) ℂ →⋆ₐ[ℂ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ where
  toFun M := Matrix.of (carEntry h (Matrix.of.symm M))
  map_one' := by
    ext x y
    have h1 : Matrix.of.symm (1 : Matrix (Fin m → Bool) (Fin m → Bool) ℂ) =
        fun u v => if u = v then 1 else 0 := funext fun _ => funext fun _ => Matrix.one_apply
    rw [Matrix.of_apply, h1, Matrix.one_apply]
    exact carEntry_diag h 1 x y
  map_mul' M N := by
    ext x y
    rw [Matrix.of_apply, Matrix.mul_apply]
    have hmul : Matrix.of.symm (M * N) = fun u v =>
        ∑ w : Fin m → Bool, Matrix.of.symm M u w * Matrix.of.symm N w v :=
      funext fun _ => funext fun _ => Matrix.mul_apply
    rw [hmul]
    exact (carEntry_mul h (Matrix.of.symm M) (Matrix.of.symm N) x y).trans
      (Finset.sum_congr rfl fun _ _ => by rw [Matrix.of_apply, Matrix.of_apply])
  map_zero' := by
    ext x y
    have hz : ∀ u v, Matrix.of.symm (0 : Matrix (Fin m → Bool) (Fin m → Bool) ℂ) u v = 0 :=
      fun _ _ => rfl
    simp only [Matrix.of_apply, carEntry, Matrix.zero_apply, hz, ite_self]
  map_add' M N := by
    ext x y
    have hadd : ∀ u v, Matrix.of.symm (M + N) u v =
        Matrix.of.symm M u v + Matrix.of.symm N u v := fun _ _ => rfl
    rw [Matrix.of_apply, Matrix.add_apply, Matrix.of_apply, Matrix.of_apply,
      carEntry, carEntry, carEntry, hadd]
    split_ifs <;> simp
  commutes' c := by
    ext x y
    have halg : ∀ {p} (u v : Fin p → Bool),
        (algebraMap ℂ (Matrix (Fin p → Bool) (Fin p → Bool) ℂ) c) u v =
          if u = v then c else 0 := fun u v => by
      rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
      rfl
    have hL : Matrix.of.symm (algebraMap ℂ (Matrix (Fin m → Bool) (Fin m → Bool) ℂ) c) =
        fun u v => if u = v then c else 0 := funext fun u => funext fun v => halg u v
    rw [Matrix.of_apply, hL, halg x y]
    exact carEntry_diag h c x y
  map_star' M := by
    ext x y
    have hst : Matrix.of.symm (star M) = fun u v => star (Matrix.of.symm M v u) := rfl
    change carEntry h (Matrix.of.symm (star M)) x y = star (carEntry h (Matrix.of.symm M) y x)
    rw [hst]
    exact carEntry_star h (Matrix.of.symm M) x y

private theorem carMatrixTransition_self (n : ℕ)
    (M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    carMatrixTransition n n le_rfl M = M := by
  ext x y
  change carEntry le_rfl (Matrix.of.symm M) x y = Matrix.of.symm M x y
  exact carEntry_self (Matrix.of.symm M) x y

private theorem carMatrixTransition_comp {m n p : ℕ} (h₁₂ : m ≤ n) (h₂₃ : n ≤ p)
    (M : Matrix (Fin m → Bool) (Fin m → Bool) ℂ) :
    carMatrixTransition n p h₂₃ (carMatrixTransition m n h₁₂ M) =
      carMatrixTransition m p (h₁₂.trans h₂₃) M := by
  ext x y
  change carEntry h₂₃ (carEntry h₁₂ (Matrix.of.symm M)) x y =
    carEntry (h₁₂.trans h₂₃) (Matrix.of.symm M) x y
  exact carEntry_comp h₁₂ h₂₃ (Matrix.of.symm M) x y

/-- The unital block-diagonal embedding `M_{2^m}(ℂ) →⋆ₐ[ℂ] M_{2^n}(ℂ)` indexed by binary words
`Fin n → Bool`. -/
def carTransition (m n : ℕ) (h : m ≤ n) :
    CStarMatrix (Fin m → Bool) (Fin m → Bool) ℂ →⋆ₐ[ℂ]
      CStarMatrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp (carMatrixTransition m n h)).comp
    CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom

/-- The `carTransition` embeddings form a directed system on `ℕ`. -/
instance instDirectedSystemCarTransition :
    DirectedSystem (fun n => CStarMatrix (Fin n → Bool) (Fin n → Bool) ℂ)
      (fun m n h => ⇑(carTransition m n h)) where
  map_self n M := by
    simp only [carTransition, StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply,
      carMatrixTransition_self, StarAlgEquiv.apply_symm_apply]
  map_map p n m h₁₂ h₂₃ M := by
    simp only [carTransition, StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply,
      StarAlgEquiv.symm_apply_apply, carMatrixTransition_comp]

/-- The UHF `2^∞` (CAR) C⋆-algebra, realized as the C⋆-inductive limit of `M_{2^n}(ℂ)` along
the block-diagonal embeddings `carTransition`. -/
abbrev CARAlgebra : Type :=
  CStarInductiveLimit (fun n => CStarMatrix (Fin n → Bool) (Fin n → Bool) ℂ) carTransition

/-- The UHF `2^∞` (CAR) C⋆-algebra is nontrivial. -/
theorem nontrivial_carAlgebra : Nontrivial CARAlgebra :=
  instNontrivial

/-- The UHF `2^∞` (CAR) C⋆-algebra is separable. -/
theorem separableSpace_carAlgebra : SeparableSpace CARAlgebra := by
  have : ∀ n, SeparableSpace (CStarMatrix (Fin n → Bool) (Fin n → Bool) ℂ) := fun n => by
    have : SeparableSpace (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
      inferInstanceAs (SeparableSpace ((Fin n → Bool) → (Fin n → Bool) → ℂ))
    exact (CStarMatrix.ofMatrixL (m := Fin n → Bool) (n := Fin n → Bool) (A := ℂ)).surjective
      |>.denseRange.separableSpace CStarMatrix.ofMatrixL.continuous
  exact instSeparableSpace

/-- The UHF `2^∞` (CAR) C⋆-algebra is a simple ring (`IsSimpleRing`). -/
theorem isSimpleRing_carAlgebra : IsSimpleRing CARAlgebra := by
  have : ∀ n, IsSimpleRing (CStarMatrix (Fin n → Bool) (Fin n → Bool) ℂ) := fun n =>
    IsSimpleRing.of_ringEquiv CStarMatrix.ofMatrixRingEquiv inferInstance
  exact isSimpleRing

end CAR

end Examples

end TauCeti.CStarInductiveLimit
