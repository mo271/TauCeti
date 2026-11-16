/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.Algebra.Ring.Periodic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Continuous antiperiodic functions and quotient descent to `AddCircle`

A continuous `c`-periodic function `f : G → Y` on a group with a topology descends to a continuous
function on the quotient `G ⧸ AddSubgroup.zmultiples c` (`Function.Periodic.continuous_lift` and
`Function.Periodic.liftContinuousMap`); for `G = ℝ` this target is `AddCircle c`. On `ℝ`, every
continuous real-valued `p`-antiperiodic function (`0 ≤ p`) vanishes somewhere in `[a, a + p]`
(`Function.Antiperiodic.exists_mem_Icc_eq_zero`).

For `p : ℝ` and a topological space `E` with negation, `TauCeti.ContinuousAntiperiodicMap p E`
bundles continuous functions `v : ℝ → E` satisfying `Function.Antiperiodic v p`, that is,
`v (t + p) = -v t` for all `t`. When `E` is a topological module over a topological ring `R`,
continuous functions `f : C(AddCircle p, R)` act pointwise via the quotient projection
`ℝ → AddCircle p`, on both the left (`(f • v) t = f (t : AddCircle p) • v t`) and the right through
`(C(AddCircle p, R))ᵐᵒᵖ` (`(MulOpposite.op f • v) t = MulOpposite.op (f (t : AddCircle p)) • v t`,
so `(v · f) t = v t * f (t : AddCircle p)` when `E = R`). Over a topological star ring `𝕜`, the
pointwise product `t ↦ star (v t) * w t` of two `p`-antiperiodic functions is `p`-periodic because
the two signs cancel, descending to the `C(AddCircle p, 𝕜)`-valued sesquilinear pairing
`TauCeti.ContinuousAntiperiodicMap.innerContinuousMap`.

When `E` is a (semi)normed additive commutative group and `0 < p` (`[Fact (0 < p)]`), the norm
`t ↦ ‖v t‖` is `p`-periodic, so every `v : ContinuousAntiperiodicMap p E` is bounded and embeds
into `ℝ →ᵇ E` (`TauCeti.ContinuousAntiperiodicMap.toBCF`). Its supremum norm equals
`sSup ((fun t ↦ ‖v t‖) '' Set.Icc a (a + p))` independently of the chosen interval `[a, a + p]`
(`TauCeti.ContinuousAntiperiodicMap.norm_eq_sSup_Icc`), in particular on `[0, p]`, and agrees with
the norm of the descended function `v.normContinuousMap : C(AddCircle p, ℝ)`. When `E` is complete,
`ContinuousAntiperiodicMap p E` is complete (`CompleteSpace`), as its image in `ℝ →ᵇ E` is closed.

For `p = 1` and `E = ℝ` or `ℂ`, `ContinuousAntiperiodicMap 1 E` is the continuous section module of
the Möbius line bundle over the unit circle `AddCircle (1 : ℝ)`.

## Main definitions

* `Function.Periodic.liftContinuousMap`: bundled quotient descent of a continuous `c`-periodic map
  `G → Y` to `C(G ⧸ AddSubgroup.zmultiples c, Y)`.
* `TauCeti.ContinuousAntiperiodicMap p E`: continuous `p`-antiperiodic maps `ℝ → E`, equipped with
  additive-group, constant-scalar, `C(AddCircle p, R)`-module, and (for `0 < p`) normed-group,
  normed-space, bounded-module, and complete-space structures.
* `TauCeti.ContinuousAntiperiodicMap.innerContinuousMap`: the `C(AddCircle p, 𝕜)`-valued pointwise
  sesquilinear pairing `t ↦ star (v t) * w t` descended to `AddCircle p`.
* `TauCeti.ContinuousAntiperiodicMap.toBCF` and
  `TauCeti.ContinuousAntiperiodicMap.normContinuousMap`: the isometric embedding into `ℝ →ᵇ E` and
  the descended norm function in `C(AddCircle p, ℝ)`.

## Main results

* `Function.Antiperiodic.exists_mem_Icc_eq_zero`: every real function continuous on `[a, a + p]`
  (`0 ≤ p`) and `p`-antiperiodic has a zero in `[a, a + p]`.
* `TauCeti.ContinuousAntiperiodicMap.isBounded_range`: every continuous `p`-antiperiodic map into a
  seminormed group (`0 < p`) has bounded range.
* `TauCeti.ContinuousAntiperiodicMap.norm_eq_sSup_Icc` and
  `TauCeti.ContinuousAntiperiodicMap.norm_eq_sSup_Icc_zero`: the norm equals
  `sSup ((fun t ↦ ‖v t‖) '' Set.Icc a (a + p))` independently of `a : ℝ`, and in particular on
  `[0, p]`.
* `TauCeti.ContinuousAntiperiodicMap.instCompleteSpace`: `ContinuousAntiperiodicMap p E` is a
  complete metric space whenever `E` is complete and `0 < p`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, (4.9.1).
-/

public section

open scoped BoundedContinuousFunction

namespace Function

section QuotientDescent

variable {G Y : Type*} [AddGroup G] [TopologicalSpace G] [TopologicalSpace Y] {f : G → Y} {c : G}

/-- The quotient descent `Function.Periodic.lift` of a continuous `c`-periodic function on an
additive group with a topology is continuous. -/
theorem Periodic.continuous_lift (hf : Periodic f c) (hcont : Continuous f) :
    Continuous hf.lift :=
  (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hcont

/-- A continuous `c`-periodic function `f : G → Y` bundled as a continuous map
`C(G ⧸ AddSubgroup.zmultiples c, Y)`. For `G = ℝ` the domain is `AddCircle c`. -/
def Periodic.liftContinuousMap (hf : Periodic f c) (hcont : Continuous f) :
    C(G ⧸ AddSubgroup.zmultiples c, Y) :=
  ⟨hf.lift, hf.continuous_lift hcont⟩

@[simp]
theorem Periodic.coe_liftContinuousMap (hf : Periodic f c) (hcont : Continuous f) :
    ⇑(hf.liftContinuousMap hcont) = hf.lift :=
  (rfl)

@[simp]
theorem Periodic.liftContinuousMap_coe (hf : Periodic f c) (hcont : Continuous f) (x : G) :
    hf.liftContinuousMap hcont (x : G ⧸ AddSubgroup.zmultiples c) = f x :=
  hf.lift_coe x

end QuotientDescent

section RealIntervals

/-- The pointwise norm of a `c`-antiperiodic map into a seminormed group is `c`-periodic. -/
theorem Antiperiodic.periodic_norm {α E : Type*} [Add α] [SeminormedAddCommGroup E]
    {f : α → E} {c : α} (hf : Antiperiodic f c) : Periodic (fun x ↦ ‖f x‖) c :=
  hf.comp_even norm_neg

/-- **Intermediate-value zero theorem for antiperiodic functions.** Every real-valued
`p`-antiperiodic function (`0 ≤ p`) continuous on `[a, a + p]` vanishes at some point of
`[a, a + p]`. -/
theorem Antiperiodic.exists_mem_Icc_eq_zero {f : ℝ → ℝ} {p : ℝ} (hf : Antiperiodic f p)
    {a : ℝ} (hp : 0 ≤ p) (hcont : ContinuousOn f (Set.Icc a (a + p))) :
    ∃ t ∈ Set.Icc a (a + p), f t = 0 := by
  have hab : a ≤ a + p := le_add_of_nonneg_right hp
  have hend : f (a + p) = -f a := hf a
  rcases le_total (f a) 0 with hfa | hfa
  · exact intermediate_value_Icc hab hcont ⟨hfa, hend ▸ neg_nonneg.2 hfa⟩
  · exact intermediate_value_Icc' hab hcont ⟨hend ▸ neg_nonpos.2 hfa, hfa⟩

/-- Every continuous real `1`-antiperiodic function has a zero in `[0, 1]`. -/
theorem Antiperiodic.exists_mem_unitInterval_eq_zero {f : ℝ → ℝ} (hf : Antiperiodic f 1)
    (hcont : Continuous f) : ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
  simpa only [zero_add] using
    hf.exists_mem_Icc_eq_zero (a := 0) zero_le_one hcont.continuousOn

end RealIntervals

end Function

namespace TauCeti

/-- Continuous `p`-antiperiodic maps `v : ℝ → E`, satisfying `v (t + p) = -v t` for all `t : ℝ`. -/
structure ContinuousAntiperiodicMap (p : ℝ) (E : Type*) [TopologicalSpace E] [Neg E]
    extends C(ℝ, E) where
  /-- A `ContinuousAntiperiodicMap` is `p`-antiperiodic. -/
  antiperiodic' : Function.Antiperiodic toFun p

namespace ContinuousAntiperiodicMap

section Basic

variable {p : ℝ} {E : Type*} [TopologicalSpace E] [Neg E]

instance instFunLike : FunLike (ContinuousAntiperiodicMap p E) ℝ E where
  coe v := v.toFun
  coe_injective v w h := by
    cases v
    cases w
    congr
    exact ContinuousMap.ext (congrFun h)

instance instContinuousMapClass : ContinuousMapClass (ContinuousAntiperiodicMap p E) ℝ E where
  map_continuous v := v.continuous_toFun

@[simp]
theorem coe_toContinuousMap (v : ContinuousAntiperiodicMap p E) :
    ⇑v.toContinuousMap = ⇑v :=
  (rfl)

@[simp]
theorem coe_mk (f : C(ℝ, E)) (hf : Function.Antiperiodic f p) :
    ⇑(mk f hf) = ⇑f :=
  (rfl)

@[simp]
theorem mk_apply (f : C(ℝ, E)) (hf : Function.Antiperiodic f p) (t : ℝ) :
    (mk f hf) t = f t :=
  (rfl)

@[ext]
theorem ext {v w : ContinuousAntiperiodicMap p E} (h : ∀ t, v t = w t) : v = w :=
  DFunLike.ext v w h

/-- The underlying function of `v : ContinuousAntiperiodicMap p E` is `p`-antiperiodic. -/
protected theorem antiperiodic (v : ContinuousAntiperiodicMap p E) :
    Function.Antiperiodic v p :=
  v.antiperiodic'

/-- Shifting the argument by the antiperiod `p` negates the value. -/
theorem apply_add_period (v : ContinuousAntiperiodicMap p E) (t : ℝ) :
    v (t + p) = -v t :=
  v.antiperiodic t

/-- Shifting the argument of a `1`-antiperiodic map by `1` negates the value. -/
theorem apply_add_one {E : Type*} [TopologicalSpace E] [Neg E]
    (v : ContinuousAntiperiodicMap 1 E) (t : ℝ) : v (t + 1) = -v t :=
  v.antiperiodic t

/-- Subtracting the antiperiod `p` negates the value when negation is involutive. -/
theorem apply_sub_period {E : Type*} [TopologicalSpace E] [InvolutiveNeg E]
    (v : ContinuousAntiperiodicMap p E) (t : ℝ) : v (t - p) = -v t :=
  v.antiperiodic.sub_eq t

/-- Every continuous real `p`-antiperiodic map (`0 ≤ p`) vanishes somewhere in `[a, a + p]`. -/
theorem exists_mem_Icc_eq_zero {p : ℝ} (v : ContinuousAntiperiodicMap p ℝ) (a : ℝ) (hp : 0 ≤ p) :
    ∃ t ∈ Set.Icc a (a + p), v t = 0 :=
  v.antiperiodic.exists_mem_Icc_eq_zero hp (map_continuous v).continuousOn

/-- Every continuous real `1`-antiperiodic map vanishes somewhere in `[0, 1]`. -/
theorem exists_mem_unitInterval_eq_zero (v : ContinuousAntiperiodicMap 1 ℝ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, v t = 0 :=
  v.antiperiodic.exists_mem_unitInterval_eq_zero (map_continuous v)

end Basic

section Algebra

variable {p : ℝ} {R E : Type*}

instance instZero [TopologicalSpace E] [NegZeroClass E] : Zero (ContinuousAntiperiodicMap p E) :=
  ⟨⟨0, Function.antiperiodic_zero p⟩⟩

instance instInhabited [TopologicalSpace E] [NegZeroClass E] :
    Inhabited (ContinuousAntiperiodicMap p E) :=
  ⟨0⟩

@[simp]
theorem coe_zero [TopologicalSpace E] [NegZeroClass E] :
    ⇑(0 : ContinuousAntiperiodicMap p E) = 0 :=
  (rfl)

@[simp]
theorem zero_apply [TopologicalSpace E] [NegZeroClass E] (t : ℝ) :
    (0 : ContinuousAntiperiodicMap p E) t = 0 :=
  (rfl)

instance instNeg [TopologicalSpace E] [Neg E] [ContinuousNeg E] :
    Neg (ContinuousAntiperiodicMap p E) :=
  ⟨fun v ↦ ⟨-v.toContinuousMap, v.antiperiodic.fun_neg⟩⟩

@[simp]
theorem coe_neg [TopologicalSpace E] [Neg E] [ContinuousNeg E] (v : ContinuousAntiperiodicMap p E) :
    ⇑(-v) = -⇑v :=
  (rfl)

@[simp]
theorem neg_apply [TopologicalSpace E] [Neg E] [ContinuousNeg E]
    (v : ContinuousAntiperiodicMap p E) (t : ℝ) : (-v) t = -v t :=
  (rfl)

section AddCommGroup

variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]

instance instAdd : Add (ContinuousAntiperiodicMap p E) :=
  ⟨fun v w ↦ ⟨v.toContinuousMap + w.toContinuousMap, v.antiperiodic.fun_add w.antiperiodic⟩⟩

@[simp]
theorem coe_add (v w : ContinuousAntiperiodicMap p E) : ⇑(v + w) = ⇑v + ⇑w :=
  (rfl)

@[simp]
theorem add_apply (v w : ContinuousAntiperiodicMap p E) (t : ℝ) :
    (v + w) t = v t + w t :=
  (rfl)

instance instSub : Sub (ContinuousAntiperiodicMap p E) :=
  ⟨fun v w ↦ ⟨v.toContinuousMap - w.toContinuousMap, v.antiperiodic.fun_sub w.antiperiodic⟩⟩

@[simp]
theorem coe_sub (v w : ContinuousAntiperiodicMap p E) : ⇑(v - w) = ⇑v - ⇑w :=
  (rfl)

@[simp]
theorem sub_apply (v w : ContinuousAntiperiodicMap p E) (t : ℝ) :
    (v - w) t = v t - w t :=
  (rfl)

instance instSMulConst [Monoid R] [DistribMulAction R E] [ContinuousConstSMul R E] :
    SMul R (ContinuousAntiperiodicMap p E) :=
  ⟨fun r v ↦ ⟨r • v.toContinuousMap, v.antiperiodic.smul r⟩⟩

omit [IsTopologicalAddGroup E] in
@[simp]
theorem coe_smul_const [Monoid R] [DistribMulAction R E] [ContinuousConstSMul R E]
    (r : R) (v : ContinuousAntiperiodicMap p E) : ⇑(r • v) = r • ⇑v :=
  (rfl)

omit [IsTopologicalAddGroup E] in
@[simp]
theorem smul_const_apply [Monoid R] [DistribMulAction R E] [ContinuousConstSMul R E]
    (r : R) (v : ContinuousAntiperiodicMap p E) (t : ℝ) : (r • v) t = r • v t :=
  (rfl)

instance instAddCommGroup : AddCommGroup (ContinuousAntiperiodicMap p E) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Coercion to `C(ℝ, E)` as an additive monoid homomorphism. -/
def toContinuousMapAddMonoidHom : ContinuousAntiperiodicMap p E →+ C(ℝ, E) where
  toFun := toContinuousMap
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem toContinuousMapAddMonoidHom_apply (v : ContinuousAntiperiodicMap p E) :
    toContinuousMapAddMonoidHom v = v.toContinuousMap :=
  (rfl)

@[simp]
theorem coe_sum {ι : Type*} (s : Finset ι) (v : ι → ContinuousAntiperiodicMap p E) :
    ⇑(∑ i ∈ s, v i) = ∑ i ∈ s, ⇑(v i) := by
  simpa only [toContinuousMapAddMonoidHom_apply, coe_toContinuousMap, ContinuousMap.coe_sum] using
    congrArg DFunLike.coe (map_sum (toContinuousMapAddMonoidHom (p := p) (E := E)) v s)

@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (v : ι → ContinuousAntiperiodicMap p E) (t : ℝ) :
    (∑ i ∈ s, v i) t = ∑ i ∈ s, v i t := by
  rw [coe_sum, Finset.sum_apply]

instance instModuleConst [Semiring R] [Module R E] [ContinuousConstSMul R E] :
    Module R (ContinuousAntiperiodicMap p E) :=
  Function.Injective.module R
    { toFun := fun v ↦ (v : ℝ → E), map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    DFunLike.coe_injective fun _ _ ↦ rfl

/-- Pointwise left action of `C(AddCircle p, R)` on `ContinuousAntiperiodicMap p E`:
`(f • v) t = f (t : AddCircle p) • v t`. Since `t ↦ f (t : AddCircle p)` is continuous and
`p`-periodic, `f • v` is again continuous and `p`-antiperiodic. -/
instance instSMulCircle [Semiring R] [TopologicalSpace R] [Module R E] [ContinuousSMul R E] :
    SMul C(AddCircle p, R) (ContinuousAntiperiodicMap p E) where
  smul f v :=
    ⟨⟨fun t ↦ f (t : AddCircle p) • v t,
        (f.continuous.comp (AddCircle.continuous_mk' p)).smul (map_continuous v)⟩,
      Function.Periodic.smul_antiperiodic
        (fun t ↦ congrArg f (AddCircle.coe_add_period p t)) v.antiperiodic⟩

omit [IsTopologicalAddGroup E] in
@[simp]
theorem smul_circle_apply [Semiring R] [TopologicalSpace R] [Module R E] [ContinuousSMul R E]
    (f : C(AddCircle p, R)) (v : ContinuousAntiperiodicMap p E) (t : ℝ) :
    (f • v) t = f (t : AddCircle p) • v t :=
  (rfl)

instance instModuleCircle [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [Module R E]
    [ContinuousSMul R E] : Module C(AddCircle p, R) (ContinuousAntiperiodicMap p E) where
  one_smul v := ext fun t ↦ one_smul R (v t)
  mul_smul f g v := ext fun t ↦ mul_smul (f (t : AddCircle p)) (g (t : AddCircle p)) (v t)
  smul_zero f := ext fun t ↦ smul_zero (f (t : AddCircle p))
  smul_add f v w := ext fun t ↦ smul_add (f (t : AddCircle p)) (v t) (w t)
  add_smul f g v := ext fun t ↦ add_smul (f (t : AddCircle p)) (g (t : AddCircle p)) (v t)
  zero_smul _ := ext fun _ ↦ zero_smul R _

/-- Pointwise right action of `C(AddCircle p, R)` (expressed as a left `(C(AddCircle p, R))ᵐᵒᵖ`
action) on `ContinuousAntiperiodicMap p E`:
`(MulOpposite.op f • v) t = MulOpposite.op (f (t : AddCircle p)) • v t`. For `E = R` this is
`(v · f) t = v t * f (t : AddCircle p)`. -/
instance instSMulCircleOpposite [Semiring R] [TopologicalSpace R] [Module Rᵐᵒᵖ E]
    [ContinuousSMul Rᵐᵒᵖ E] : SMul (C(AddCircle p, R))ᵐᵒᵖ (ContinuousAntiperiodicMap p E) where
  smul f v :=
    ⟨⟨fun t ↦ MulOpposite.op (f.unop (t : AddCircle p)) • v t,
        ((MulOpposite.continuous_op.comp
          (f.unop.continuous.comp (AddCircle.continuous_mk' p)))).smul (map_continuous v)⟩,
      Function.Periodic.smul_antiperiodic
        (fun t ↦ congrArg (fun r ↦ MulOpposite.op (f.unop r)) (AddCircle.coe_add_period p t))
        v.antiperiodic⟩

omit [IsTopologicalAddGroup E] in
@[simp]
theorem op_smul_circle_apply [Semiring R] [TopologicalSpace R] [Module Rᵐᵒᵖ E]
    [ContinuousSMul Rᵐᵒᵖ E] (f : C(AddCircle p, R)) (v : ContinuousAntiperiodicMap p E) (t : ℝ) :
    (MulOpposite.op f • v) t = MulOpposite.op (f (t : AddCircle p)) • v t :=
  (rfl)

/-- For scalar-valued continuous antiperiodic functions `v : ContinuousAntiperiodicMap p R`, the
right `C(AddCircle p, R)`-action is `(v · f) t = v t * f (t : AddCircle p)`. -/
theorem op_smul_self_apply {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (f : C(AddCircle p, R)) (v : ContinuousAntiperiodicMap p R) (t : ℝ) :
    (MulOpposite.op f • v) t = v t * f (t : AddCircle p) :=
  (rfl)

instance instModuleCircleOpposite [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
    [Module Rᵐᵒᵖ E] [ContinuousSMul Rᵐᵒᵖ E] :
    Module (C(AddCircle p, R))ᵐᵒᵖ (ContinuousAntiperiodicMap p E) where
  one_smul v := ext fun t ↦ one_smul Rᵐᵒᵖ (v t)
  mul_smul f g v := ext fun t ↦
    mul_smul (MulOpposite.op (f.unop (t : AddCircle p)))
      (MulOpposite.op (g.unop (t : AddCircle p))) (v t)
  smul_zero f := ext fun t ↦ smul_zero (MulOpposite.op (f.unop (t : AddCircle p)))
  smul_add f v w := ext fun t ↦ smul_add (MulOpposite.op (f.unop (t : AddCircle p))) (v t) (w t)
  add_smul f g v := ext fun t ↦
    add_smul (MulOpposite.op (f.unop (t : AddCircle p)))
      (MulOpposite.op (g.unop (t : AddCircle p))) (v t)
  zero_smul _ := ext fun _ ↦ zero_smul Rᵐᵒᵖ _

instance instIsCentralScalarCircle [Semiring R] [TopologicalSpace R] [Module R E]
    [ContinuousSMul R E] [Module Rᵐᵒᵖ E] [ContinuousSMul Rᵐᵒᵖ E] [IsCentralScalar R E] :
    IsCentralScalar C(AddCircle p, R) (ContinuousAntiperiodicMap p E) where
  op_smul_eq_smul f v := ext fun t ↦ op_smul_eq_smul (f (t : AddCircle p)) (v t)

instance instIsScalarTowerConstCircle [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
    [Module R E] [ContinuousSMul R E] :
    IsScalarTower R C(AddCircle p, R) (ContinuousAntiperiodicMap p E) where
  smul_assoc r f v := ext fun t ↦ mul_smul r (f (t : AddCircle p)) (v t)

end AddCommGroup

end Algebra

section InnerProduct

variable {p : ℝ} {𝕜 : Type*} [Ring 𝕜] [StarRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [ContinuousStar 𝕜]

omit [IsTopologicalRing 𝕜] [ContinuousStar 𝕜] in
/-- For `p`-antiperiodic `v, w : ContinuousAntiperiodicMap p 𝕜`, the pointwise sesquilinear pairing
`t ↦ star (v t) * w t` is `p`-periodic (`star (-v t) * (-w t) = star (v t) * w t`). -/
theorem periodic_star_mul (v w : ContinuousAntiperiodicMap p 𝕜) :
    Function.Periodic (fun t ↦ star (v t) * w t) p :=
  (v.antiperiodic.comp_odd star_neg).mul w.antiperiodic

/-- The pointwise sesquilinear product `t ↦ star (v t) * w t` (`conj(v(t)) w(t)` for `𝕜 = ℝ, ℂ`),
descended along the quotient map `ℝ → AddCircle p` to an element of `C(AddCircle p, 𝕜)`. -/
def innerContinuousMap (v w : ContinuousAntiperiodicMap p 𝕜) : C(AddCircle p, 𝕜) :=
  (periodic_star_mul v w).liftContinuousMap
    ((continuous_star.comp (map_continuous v)).mul (map_continuous w))

@[simp]
theorem innerContinuousMap_coe (v w : ContinuousAntiperiodicMap p 𝕜) (t : ℝ) :
    innerContinuousMap v w (t : AddCircle p) = star (v t) * w t :=
  (periodic_star_mul v w).lift_coe t

@[simp]
theorem innerContinuousMap_zero_left (w : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap 0 w = 0 := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp

@[simp]
theorem innerContinuousMap_zero_right (v : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap v 0 = 0 := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp

theorem innerContinuousMap_add_left (v₁ v₂ w : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap (v₁ + v₂) w = innerContinuousMap v₁ w + innerContinuousMap v₂ w := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp [add_mul]

theorem innerContinuousMap_add_right (v w₁ w₂ : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap v (w₁ + w₂) = innerContinuousMap v w₁ + innerContinuousMap v w₂ := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp [mul_add]

theorem innerContinuousMap_symm (v w : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap w v = star (innerContinuousMap v w) := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp

theorem innerContinuousMap_smul_right {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜]
    [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [ContinuousStar 𝕜]
    (f : C(AddCircle p, 𝕜)) (v w : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap v (f • w) = f * innerContinuousMap v w := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp [mul_left_comm]

theorem innerContinuousMap_smul_left {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜]
    [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [ContinuousStar 𝕜]
    (f : C(AddCircle p, 𝕜)) (v w : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap (f • v) w = star f * innerContinuousMap v w := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp [mul_assoc]

@[simp]
theorem innerContinuousMap_self_eq_zero_iff [NoZeroDivisors 𝕜]
    (v : ContinuousAntiperiodicMap p 𝕜) :
    innerContinuousMap v v = 0 ↔ v = 0 := by
  refine ⟨fun h ↦ ext fun t ↦ ?_, fun h ↦ h ▸ innerContinuousMap_zero_left 0⟩
  have ht : star (v t) * v t = 0 := by
    simpa only [innerContinuousMap_coe, ContinuousMap.zero_apply] using
      congrArg (fun g : C(AddCircle p, 𝕜) ↦ g (t : AddCircle p)) h
  exact (mul_eq_zero.1 ht).elim star_eq_zero.1 id

end InnerProduct

section Normed

variable {p : ℝ} [hp : Fact (0 < p)] {E : Type*}

section Seminormed

variable [SeminormedAddCommGroup E]

omit hp in
/-- For `v : ContinuousAntiperiodicMap p E`, `t ↦ ‖v t‖` is `p`-periodic. -/
theorem periodic_norm (v : ContinuousAntiperiodicMap p E) :
    Function.Periodic (fun t ↦ ‖v t‖) p :=
  v.antiperiodic.periodic_norm

/-- The pointwise norms of `v : ContinuousAntiperiodicMap p E` (`0 < p`) are bounded above on
`ℝ`. -/
theorem bddAbove_range_norm (v : ContinuousAntiperiodicMap p E) :
    BddAbove (Set.range fun t ↦ ‖v t‖) :=
  (v.periodic_norm.compact_of_continuous hp.out.ne'
    (continuous_norm.comp (map_continuous v))).bddAbove

/-- Every continuous `p`-antiperiodic map (`0 < p`) into a seminormed group has bounded range. -/
theorem isBounded_range (v : ContinuousAntiperiodicMap p E) :
    Bornology.IsBounded (Set.range v) :=
  v.antiperiodic.periodic_two_mul.isBounded_of_continuous
    (mul_ne_zero two_ne_zero hp.out.ne') (map_continuous v)

/-- Embedding of `ContinuousAntiperiodicMap p E` (`0 < p`) into `ℝ →ᵇ E`. -/
noncomputable def toBCF (v : ContinuousAntiperiodicMap p E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup v (map_continuous v)
    v.bddAbove_range_norm.some (fun t ↦ v.bddAbove_range_norm.choose_spec ⟨t, rfl⟩)

@[simp]
theorem coe_toBCF (v : ContinuousAntiperiodicMap p E) : ⇑v.toBCF = ⇑v :=
  (rfl)

@[simp]
theorem toBCF_apply (v : ContinuousAntiperiodicMap p E) (t : ℝ) : v.toBCF t = v t :=
  (rfl)

@[simp]
theorem toBCF_zero : (0 : ContinuousAntiperiodicMap p E).toBCF = 0 :=
  BoundedContinuousFunction.ext fun _ ↦ rfl

@[simp]
theorem toBCF_add (v w : ContinuousAntiperiodicMap p E) : (v + w).toBCF = v.toBCF + w.toBCF :=
  BoundedContinuousFunction.ext fun _ ↦ rfl

@[simp]
theorem toBCF_smul_const {R : Type*} [PseudoMetricSpace R] [Zero R] [Monoid R]
    [DistribMulAction R E] [IsBoundedSMul R E]
    (r : R) (v : ContinuousAntiperiodicMap p E) : (r • v).toBCF = r • v.toBCF :=
  BoundedContinuousFunction.ext fun _ ↦ rfl

theorem toBCF_injective : Function.Injective (toBCF (p := p) (E := E)) :=
  fun _ _ h ↦ ext fun t ↦ congrArg (fun f : ℝ →ᵇ E ↦ f t) h

/-- `toBCF` as an additive monoid homomorphism into `ℝ →ᵇ E`. -/
noncomputable def toBCFAddMonoidHom : ContinuousAntiperiodicMap p E →+ ℝ →ᵇ E :=
  ⟨⟨toBCF, toBCF_zero⟩, toBCF_add⟩

@[simp]
theorem toBCFAddMonoidHom_apply (v : ContinuousAntiperiodicMap p E) :
    toBCFAddMonoidHom v = v.toBCF :=
  (rfl)

noncomputable instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup (ContinuousAntiperiodicMap p E) :=
  SeminormedAddCommGroup.induced _ _
    (⟨⟨toBCF, toBCF_zero⟩, toBCF_add⟩ : ContinuousAntiperiodicMap p E →+ ℝ →ᵇ E)

@[simp]
theorem norm_toBCF (v : ContinuousAntiperiodicMap p E) : ‖v.toBCF‖ = ‖v‖ :=
  (rfl)

@[simp]
theorem dist_toBCF (v w : ContinuousAntiperiodicMap p E) : dist v.toBCF w.toBCF = dist v w :=
  (rfl)

theorem isometry_toBCF : Isometry (toBCF (p := p) (E := E)) :=
  fun _ _ ↦ rfl

/-- Pointwise norm bound `‖v t‖ ≤ ‖v‖` at every `t : ℝ`. -/
theorem norm_apply_le (v : ContinuousAntiperiodicMap p E) (t : ℝ) : ‖v t‖ ≤ ‖v‖ :=
  v.toBCF.norm_coe_le_norm t

/-- **Interval independence of the supremum norm.** For any starting point `a : ℝ`, the norm of
`v : ContinuousAntiperiodicMap p E` (`0 < p`) equals the supremum of `‖v t‖` over the unit-period
interval `[a, a + p]`. -/
theorem norm_eq_sSup_Icc (v : ContinuousAntiperiodicMap p E) (a : ℝ) :
    ‖v‖ = sSup ((fun t ↦ ‖v t‖) '' Set.Icc a (a + p)) := by
  rw [← norm_toBCF, BoundedContinuousFunction.norm_eq_iSup_norm, iSup]
  simp only [toBCF_apply, ← v.periodic_norm.image_Icc hp.out a]

/-- The norm of `v : ContinuousAntiperiodicMap p E` (`0 < p`) equals `sup_{0 ≤ t ≤ p} ‖v t‖`. -/
theorem norm_eq_sSup_Icc_zero (v : ContinuousAntiperiodicMap p E) :
    ‖v‖ = sSup ((fun t ↦ ‖v t‖) '' Set.Icc 0 p) := by
  simpa only [zero_add] using v.norm_eq_sSup_Icc 0

/-- A bound `‖v t‖ ≤ C` (`0 ≤ C`) on any single fundamental interval `[a, a + p]` bounds `‖v‖`. -/
theorem norm_le_of_forall_mem_Icc (v : ContinuousAntiperiodicMap p E) {a C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t ∈ Set.Icc a (a + p), ‖v t‖ ≤ C) : ‖v‖ ≤ C := by
  rw [← norm_toBCF, BoundedContinuousFunction.norm_le hC]
  intro t
  obtain ⟨s, hs, hst⟩ := v.periodic_norm.exists_mem_Ico hp.out t a
  exact hst ▸ h s (Set.Ico_subset_Icc_self hs)

omit hp in
/-- The `p`-periodic norm `t ↦ ‖v t‖` descended to `C(AddCircle p, ℝ)`. -/
def normContinuousMap (v : ContinuousAntiperiodicMap p E) : C(AddCircle p, ℝ) :=
  v.periodic_norm.liftContinuousMap (continuous_norm.comp (map_continuous v))

omit hp in
@[simp]
theorem normContinuousMap_coe (v : ContinuousAntiperiodicMap p E) (t : ℝ) :
    v.normContinuousMap (t : AddCircle p) = ‖v t‖ :=
  v.periodic_norm.lift_coe t

/-- The supremum norm of the descended function `v.normContinuousMap : C(AddCircle p, ℝ)` coincides
with `‖v‖`. -/
@[simp]
theorem norm_normContinuousMap (v : ContinuousAntiperiodicMap p E) :
    ‖v.normContinuousMap‖ = ‖v‖ := by
  refine le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg v)).2 fun x ↦ ?_) ?_
  · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simpa only [normContinuousMap_coe, Real.norm_of_nonneg (norm_nonneg (v t))] using
      v.norm_apply_le t
  · refine v.norm_le_of_forall_mem_Icc (a := 0) (norm_nonneg _) fun t _ ↦ ?_
    simpa only [normContinuousMap_coe, Real.norm_of_nonneg (norm_nonneg (v t))] using
      v.normContinuousMap.norm_coe_le_norm (t : AddCircle p)

noncomputable instance instNormedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] :
    NormedSpace 𝕜 (ContinuousAntiperiodicMap p E) where
  norm_smul_le c v := by
    rw [← norm_toBCF, toBCF_smul_const]
    exact norm_smul_le c v.toBCF

noncomputable instance instIsBoundedSMulCircle {R : Type*} [SeminormedRing R] [Module R E]
    [IsBoundedSMul R E] : IsBoundedSMul C(AddCircle p, R) (ContinuousAntiperiodicMap p E) where
  dist_smul_pair' f v w := by
    simp only [dist_eq_norm, sub_zero]
    refine norm_le_of_forall_mem_Icc (f • v - f • w) (a := 0)
      (mul_nonneg (norm_nonneg f) (norm_nonneg (v - w))) fun t _ ↦ ?_
    rw [sub_apply, smul_circle_apply, smul_circle_apply, ← smul_sub]
    exact (norm_smul_le (f (t : AddCircle p)) ((v - w) t)).trans
      (mul_le_mul (f.norm_coe_le_norm (t : AddCircle p)) ((v - w).norm_apply_le t)
        (norm_nonneg _) (norm_nonneg f))
  dist_pair_smul' f g v := by
    simp only [dist_eq_norm, sub_zero]
    refine norm_le_of_forall_mem_Icc (f • v - g • v) (a := 0)
      (mul_nonneg (norm_nonneg (f - g)) (norm_nonneg v)) fun t _ ↦ ?_
    rw [sub_apply, smul_circle_apply, smul_circle_apply, ← sub_smul]
    exact (norm_smul_le ((f - g) (t : AddCircle p)) (v t)).trans
      (mul_le_mul ((f - g).norm_coe_le_norm (t : AddCircle p)) (v.norm_apply_le t)
        (norm_nonneg _) (norm_nonneg (f - g)))

/-- The image of `toBCF : ContinuousAntiperiodicMap p E → ℝ →ᵇ E` is the set of `p`-antiperiodic
bounded continuous functions. -/
theorem range_toBCF :
    Set.range (toBCF (p := p) (E := E)) = {f : ℝ →ᵇ E | Function.Antiperiodic f p} := by
  ext f
  refine ⟨fun ⟨v, hv⟩ ↦ hv ▸ v.antiperiodic, fun hf ↦ ⟨⟨f.toContinuousMap, hf⟩, ?_⟩⟩
  ext t
  rfl

/-- The range of `toBCF` is closed in `ℝ →ᵇ E`, since evaluation at each point is continuous. -/
theorem isClosed_range_toBCF [T2Space E] :
    IsClosed (Set.range (toBCF (p := p) (E := E))) := by
  rw [range_toBCF]
  have hset : {f : ℝ →ᵇ E | Function.Antiperiodic f p} =
      ⋂ t : ℝ, {f : ℝ →ᵇ E | f (t + p) = -f t} := by
    ext f
    simp [Function.Antiperiodic]
  rw [hset]
  exact isClosed_iInter fun t ↦
    isClosed_eq (continuous_eval_const (t + p)) (continuous_neg.comp (continuous_eval_const t))

/-- When `E` is complete and separated (`T2Space`) and `0 < p`, `ContinuousAntiperiodicMap p E` is
complete, as an isometric copy of a closed additive subgroup of `ℝ →ᵇ E`. -/
instance instCompleteSpace [T2Space E] [CompleteSpace E] :
    CompleteSpace (ContinuousAntiperiodicMap p E) :=
  (completeSpace_iff_isComplete_range isometry_toBCF.isUniformInducing).2
    isClosed_range_toBCF.isComplete

end Seminormed

noncomputable instance instNormedAddCommGroup [NormedAddCommGroup E] :
    NormedAddCommGroup (ContinuousAntiperiodicMap p E) :=
  NormedAddCommGroup.induced _ _
    (⟨⟨toBCF, toBCF_zero⟩, toBCF_add⟩ : ContinuousAntiperiodicMap p E →+ ℝ →ᵇ E)
    toBCF_injective

end Normed

end ContinuousAntiperiodicMap

end TauCeti
