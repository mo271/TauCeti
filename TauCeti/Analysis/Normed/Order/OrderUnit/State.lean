/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Order.PositiveLinearMap
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Positive maps, states, and Kadison norm detection on order-unit spaces

Let `(E, e)` be a real order-unit normed space (`TauCeti.OrderUnit.IsOrderUnitNorm e`). Because the
closed unit ball of `E` is the order interval `[-e, e]`, every positive linear map `T : E →ₚ[ℝ] F`
into another order-unit normed space `(F, f)` satisfies `‖T a‖ ≤ ‖T e‖ * ‖a‖`, hence is
automatically Lipschitz and continuous with operator norm `‖T e‖`. In particular, positive real
linear functionals on `E` are continuous, and a continuous real linear functional `ψ : E →L[ℝ] ℝ`
is monotone if and only if `‖ψ‖ = ψ e`.

A **state** of `(E, e)` is a monotone continuous linear functional `φ ∈ WeakDual ℝ E` normalized by
`φ e = 1`. Equivalently, `φ` is a functional of norm one taking the value `1` at `e`. We define the
**state space** `TauCeti.OrderUnit.stateSpace e : Set (WeakDual ℝ E)` with its weak-* subspace
topology and establish:

* **Automatic boundedness of positive maps**: `PositiveLinearMap.norm_apply_le_norm_orderUnit_mul`,
  `PositiveLinearMap.toPositiveContinuousLinearMapOfOrderUnit`, and
  `PositiveContinuousLinearMap.opNorm_eq_norm_orderUnit`.
* **Norm characterization of states**: `ContinuousLinearMap.monotone_iff_opNorm_eq_apply_orderUnit`
  and `TauCeti.OrderUnit.mem_stateSpace_iff_norm_eq_one_and_apply`, together with equivalences
  identifying `stateSpace e` with normalized `E →P[ℝ] ℝ` and `E →ₚ[ℝ] ℝ`.
* **Existence, compactness, and extreme points**: `TauCeti.OrderUnit.stateSpace_nonempty` (by
  Hahn–Banach), `TauCeti.OrderUnit.convex_stateSpace`, `TauCeti.OrderUnit.isClosed_stateSpace`,
  `TauCeti.OrderUnit.isCompact_stateSpace` (by Banach–Alaoglu), and Krein–Milman recovery of
  `stateSpace e` from pure states.
* **Functoriality, subspace extension, and completion invariance**: weak-* continuous affine
  pullback along positive maps (`TauCeti.OrderUnit.pullbackFunctional`), Hahn–Banach state
  extension along unital linear isometries (`TauCeti.OrderUnit.exists_mem_stateSpace_comp_eq`) and
  unital submodules (`TauCeti.OrderUnit.exists_mem_stateSpace_forall_apply_coe_eq`), and the
  weak-* homeomorphism `TauCeti.OrderUnit.completionStateHomeomorph` between the state spaces of
  `UniformSpace.Completion E` and `E`.
* **Order separation, norm detection, and Kadison's isometric embedding**:
  `TauCeti.OrderUnit.nonneg_iff_forall_stateSpace`, `TauCeti.OrderUnit.norm_eq_iSup_states`,
  `TauCeti.OrderUnit.nnNorm_eq_iSup_states`, attainment of the supremum, and the unital linear
  isometric order embedding `TauCeti.OrderUnit.kadisonEmbedding : E →ₗᵢ[ℝ] C(stateSpace e, ℝ)`.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. 7 (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600.
* M. A. Rieffel, *Gromov–Hausdorff distance for quantum metric spaces*, Mem. Amer. Math. Soc. 168
  (2004), no. 796.
-/

public section

open Set WeakDual UniformSpace
open scoped NNReal Topology

/-! ### Automatic boundedness and operator norm of positive maps -/

section PositiveMaps

open TauCeti.OrderUnit

namespace PositiveLinearMap

section MapClass

variable {M E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
  [FunLike M E F] [LinearMapClass M ℝ E F] [OrderHomClass M E F]
  {e : E} {f : F}

/-- A positive linear map between order-unit normed spaces satisfies `‖T a‖ ≤ ‖T e‖ * ‖a‖` for
every `a`. -/
theorem norm_apply_le_norm_orderUnit_mul (T : M) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (a : E) :
    ‖T a‖ ≤ ‖T e‖ * ‖a‖ := by
  have := hf.posSMulMono
  rw [hf.norm_le_iff (T a) (‖T e‖ * ‖a‖) (by positivity)]
  have hlow : -(‖a‖ • T e) ≤ T a := by
    simpa [neg_smul] using map_rel T (he.neg_norm_smul_le a)
  have hupp : T a ≤ ‖a‖ • T e := by
    simpa using map_rel T (he.le_norm_smul a)
  have hTe : ‖a‖ • T e ≤ (‖T e‖ * ‖a‖) • f := by
    calc
      ‖a‖ • T e ≤ ‖a‖ • (‖T e‖ • f) :=
        smul_le_smul_of_nonneg_left (hf.le_norm_smul (T e)) (norm_nonneg a)
      _ = (‖T e‖ * ‖a‖) • f := by rw [smul_smul, mul_comm]
  refine ⟨?_, hupp.trans hTe⟩
  calc
    -(‖T e‖ * ‖a‖) • f = -((‖T e‖ * ‖a‖) • f) := neg_smul _ _
    _ ≤ -(‖a‖ • T e) := neg_le_neg hTe
    _ ≤ T a := hlow

/-- A unital positive linear map (`T e = f`) between order-unit normed spaces is contractive. -/
theorem norm_apply_le_of_map_orderUnit (T : M) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (hTe : T e = f) (a : E) :
    ‖T a‖ ≤ ‖a‖ := by
  simpa [hTe, hf.norm_e] using norm_apply_le_norm_orderUnit_mul T he hf a

theorem nnNorm_apply_le_nnNorm_orderUnit_mul (T : M) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (a : E) :
    ‖T a‖₊ ≤ ‖T e‖₊ * ‖a‖₊ := by
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm, coe_nnNorm]
  exact norm_apply_le_norm_orderUnit_mul T he hf a

/-- A positive linear map between order-unit normed spaces is `‖T e‖₊`-Lipschitz. -/
theorem lipschitzWith_of_isOrderUnitNorm (T : M) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) :
    LipschitzWith ‖T e‖₊ T :=
  AddMonoidHomClass.lipschitz_of_bound_nnNorm T ‖T e‖₊
    (nnNorm_apply_le_nnNorm_orderUnit_mul T he hf)

/-- A positive linear map between order-unit normed spaces is automatically continuous. -/
theorem continuous_of_isOrderUnitNorm (T : M) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) :
    Continuous T :=
  (lipschitzWith_of_isOrderUnitNorm T he hf).continuous

end MapClass

section ToContinuous

variable {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
  {e : E} {f : F}

/-- Upgrade an algebraic positive linear map `T : E →ₚ[ℝ] F` between order-unit normed spaces to a
`PositiveContinuousLinearMap` (`E →P[ℝ] F`) using automatic continuity. -/
def toPositiveContinuousLinearMapOfOrderUnit (T : E →ₚ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) : E →P[ℝ] F where
  toPositiveLinearMap := T
  cont := continuous_of_isOrderUnitNorm T he hf

@[simp]
theorem toPositiveContinuousLinearMapOfOrderUnit_apply (T : E →ₚ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (a : E) :
    T.toPositiveContinuousLinearMapOfOrderUnit he hf a = T a :=
  (rfl)

@[simp]
theorem toPositiveLinearMap_toPositiveContinuousLinearMapOfOrderUnit (T : E →ₚ[ℝ] F)
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) :
    (T.toPositiveContinuousLinearMapOfOrderUnit he hf).toPositiveLinearMap = T :=
  (rfl)

end ToContinuous

end PositiveLinearMap

namespace PositiveContinuousLinearMap

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
  {e : E} {f : F}

/-- **Operator norm of a positive map.** For a positive continuous linear map `T : E →P[ℝ] F`
between order-unit normed spaces, `‖T‖ = ‖T e‖`. -/
theorem opNorm_eq_norm_orderUnit (T : E →P[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) :
    ‖(T : E →L[ℝ] F)‖ = ‖T e‖ := by
  apply le_antisymm
  · exact (T : E →L[ℝ] F).opNorm_le_bound (norm_nonneg (T e))
      (PositiveLinearMap.norm_apply_le_norm_orderUnit_mul T he hf)
  · calc
      ‖T e‖ ≤ ‖(T : E →L[ℝ] F)‖ * ‖e‖ := (T : E →L[ℝ] F).le_opNorm e
      _ = ‖(T : E →L[ℝ] F)‖ := by rw [he.norm_e, mul_one]

/-- A unital positive continuous linear map (`T e = f`) between order-unit normed spaces has
operator norm `1`. -/
theorem opNorm_eq_one_of_map_orderUnit (T : E →P[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (hTe : T e = f) :
    ‖(T : E →L[ℝ] F)‖ = 1 := by
  rw [T.opNorm_eq_norm_orderUnit he hf, hTe, hf.norm_e]

end PositiveContinuousLinearMap

namespace PositiveLinearMap

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
  {e : E} {f : F}

@[simp]
theorem opNorm_toPositiveContinuousLinearMapOfOrderUnit (T : E →ₚ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) :
    ‖((T.toPositiveContinuousLinearMapOfOrderUnit he hf : E →P[ℝ] F) : E →L[ℝ] F)‖ = ‖T e‖ :=
  (T.toPositiveContinuousLinearMapOfOrderUnit he hf).opNorm_eq_norm_orderUnit he hf

end PositiveLinearMap

namespace LinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- A real linear functional `ψ : E →ₗ[ℝ] ℝ` on an order-unit normed space satisfying
`|ψ a| ≤ ψ e * ‖a‖` for all `a` is monotone. -/
theorem monotone_of_abs_apply_le_mul_norm (ψ : E →ₗ[ℝ] ℝ) (he : IsOrderUnitNorm e)
    (hψ : ∀ a : E, |ψ a| ≤ ψ e * ‖a‖) :
    Monotone ψ :=
  (monotone_iff_map_nonneg ψ).mpr fun _ ha =>
    ψ.apply_nonneg_of_abs_apply_le_mul_norm hψ (he.nonneg_iff_norm_smul_sub_le.mp ha)

end LinearMap

namespace ContinuousLinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- **Norm characterization of positive functionals.** On an order-unit normed space `(E, e)`, a
continuous real linear functional `ψ : E →L[ℝ] ℝ` is monotone if and only if `‖ψ‖ = ψ e`. -/
theorem monotone_iff_opNorm_eq_apply_orderUnit (ψ : E →L[ℝ] ℝ) (he : IsOrderUnitNorm e) :
    Monotone ψ ↔ ‖ψ‖ = ψ e := by
  refine ⟨fun hψ => ψ.opNorm_eq_apply_of_monotone hψ he.le_norm_smul he.norm_e.le, fun hnorm => ?_⟩
  refine ψ.toLinearMap.monotone_of_abs_apply_le_mul_norm he fun a => ?_
  calc
    |ψ a| = ‖ψ a‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖ψ‖ * ‖a‖ := ψ.le_opNorm a
    _ = ψ e * ‖a‖ := by rw [hnorm]

/-- A continuous real linear functional is monotone and normalized at `e` if and only if
`‖ψ‖ = 1` and `ψ e = 1`. -/
theorem monotone_and_apply_eq_one_iff (ψ : E →L[ℝ] ℝ) (he : IsOrderUnitNorm e) :
    Monotone ψ ∧ ψ e = 1 ↔ ‖ψ‖ = 1 ∧ ψ e = 1 := by
  rw [ψ.monotone_iff_opNorm_eq_apply_orderUnit he]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.trans h2, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.trans h2.symm, h2⟩⟩

end ContinuousLinearMap

end PositiveMaps

/-! ### The state space of an order-unit space -/

namespace TauCeti.OrderUnit

section Preorder

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [Preorder E]
  {e : E} {φ : WeakDual ℝ E}

/-- The **state space** of `(E, e)`: the monotone continuous real linear functionals normalized by
`φ e = 1`, viewed as a subset of `WeakDual ℝ E` with its weak-* subspace topology. -/
def stateSpace (e : E) : Set (WeakDual ℝ E) :=
  {φ | Monotone φ ∧ φ e = 1}

/-- Membership in `stateSpace e` unfolds to monotonicity and normalization at `e`. -/
theorem mem_stateSpace_iff :
    φ ∈ stateSpace e ↔ Monotone φ ∧ φ e = 1 :=
  (Iff.rfl)

theorem monotone_of_mem_stateSpace (hφ : φ ∈ stateSpace e) : Monotone φ :=
  hφ.1

theorem apply_orderUnit_of_mem_stateSpace (hφ : φ ∈ stateSpace e) : φ e = 1 :=
  hφ.2

@[simp]
theorem coe_apply_orderUnit (φ : stateSpace e) : φ.1 e = 1 :=
  φ.2.2

theorem map_nonneg_of_mem_stateSpace (hφ : φ ∈ stateSpace e) {a : E} (ha : 0 ≤ a) :
    0 ≤ φ a := by
  simpa using hφ.1 ha

/-- **Convexity of the state space.** Convex combinations of states are states. -/
theorem convex_stateSpace (e : E) : Convex ℝ (stateSpace e) := by
  intro φ hφ ψ hψ s t hs ht hst
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp only [add_apply, smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hφ.1 hab) hs)
      (mul_le_mul_of_nonneg_left (hψ.1 hab) ht)
  · simp [hφ.2, hψ.2, hst]

/-- **Weak-* closedness of the state space.** The state space is closed in `WeakDual ℝ E`. -/
theorem isClosed_stateSpace (e : E) : IsClosed (stateSpace e) := by
  have h : stateSpace e =
      (⋂ (a : E) (b : E) (_ : a ≤ b), {φ : WeakDual ℝ E | φ a ≤ φ b}) ∩ {φ | φ e = 1} := by
    ext φ
    simp [mem_stateSpace_iff, Monotone]
  rw [h]
  refine (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_).inter
    (isClosed_eq (eval_continuous e) continuous_const)
  exact isClosed_le (eval_continuous a) (eval_continuous b)

/-- The only state of `(ℝ, 1)` is the identity functional. -/
theorem stateSpace_real :
    stateSpace (1 : ℝ) = {StrongDual.toWeakDual (ContinuousLinearMap.id ℝ ℝ)} := by
  ext φ
  rw [mem_stateSpace_iff, mem_singleton_iff]
  refine ⟨fun ⟨_, h1⟩ => DFunLike.ext _ _ fun r => ?_, ?_⟩
  · simpa [h1] using (toStrongDual φ).map_smul r 1
  · rintro rfl
    exact ⟨monotone_id, rfl⟩

end Preorder

/-- A positive continuous linear functional `ω : E →P[ℝ] ℝ` defines a state in `WeakDual ℝ E` if
and only if `ω e = 1`. -/
@[simp]
theorem _root_.PositiveContinuousLinearMap.toWeakDual_mem_orderUnitStateSpace_iff
    {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [PartialOrder E]
    {e : E} (ω : E →P[ℝ] ℝ) :
    StrongDual.toWeakDual (ω : E →L[ℝ] ℝ) ∈ stateSpace e ↔ ω e = 1 := by
  simp only [mem_stateSpace_iff, StrongDual.toWeakDual_apply,
    PositiveContinuousLinearMap.coe_toContinuousLinearMap, and_iff_right_iff_imp]
  exact fun _ _ _ hab => map_rel ω hab

section OrderedAddGroup

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} {φ : WeakDual ℝ E}

/-- On an ordered additive group, `φ ∈ stateSpace e` if and only if `φ` is nonnegative on the
positive cone and `φ e = 1`. -/
theorem mem_stateSpace_iff_map_nonneg :
    φ ∈ stateSpace e ↔ (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ φ e = 1 := by
  refine and_congr_left' ⟨fun h a ha => ?_, fun h a b hab => ?_⟩
  · simpa using h ha
  · simpa [sub_nonneg] using h (b - a) (sub_nonneg.mpr hab)

/-- Equivalence between `stateSpace e` and positive continuous linear functionals `E →P[ℝ] ℝ`
normalized at `e`. -/
noncomputable def stateSpaceEquivPositiveContinuousLinearMap (e : E) :
    stateSpace e ≃ {ω : E →P[ℝ] ℝ // ω e = 1} where
  toFun φ := ⟨.mk₀ (toStrongDual φ.1) fun _ ha => map_nonneg_of_mem_stateSpace φ.2 ha, φ.2.2⟩
  invFun ω := ⟨StrongDual.toWeakDual (ω.1 : E →L[ℝ] ℝ),
    ω.1.toWeakDual_mem_orderUnitStateSpace_iff.mpr ω.2⟩
  left_inv φ := Subtype.ext (toWeakDual_toStrongDual φ.1)
  right_inv _ := Subtype.ext <| PositiveContinuousLinearMap.ext fun _ => rfl

@[simp]
theorem stateSpaceEquivPositiveContinuousLinearMap_apply (φ : stateSpace e) (a : E) :
    (stateSpaceEquivPositiveContinuousLinearMap e φ).1 a = φ.1 a :=
  (rfl)

@[simp]
theorem stateSpaceEquivPositiveContinuousLinearMap_symm_apply
    (ω : {ω : E →P[ℝ] ℝ // ω e = 1}) (a : E) :
    ((stateSpaceEquivPositiveContinuousLinearMap e).symm ω).1 a = ω.1 a :=
  (rfl)

end OrderedAddGroup

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  {e : E} {φ : WeakDual ℝ E}

/-- Every state of an order-unit normed space has operator norm `1`. -/
theorem norm_toStrongDual_of_mem_stateSpace (he : IsOrderUnitNorm e) (hφ : φ ∈ stateSpace e) :
    ‖toStrongDual φ‖ = 1 :=
  ((toStrongDual φ).opNorm_eq_apply_of_monotone hφ.1 he.le_norm_smul he.norm_e.le).trans hφ.2

/-- Every state is contractive: `|φ a| ≤ ‖a‖`. -/
theorem abs_apply_le_norm_of_mem_stateSpace (he : IsOrderUnitNorm e) (hφ : φ ∈ stateSpace e)
    (a : E) :
    |φ a| ≤ ‖a‖ := by
  simpa [Real.norm_eq_abs, norm_toStrongDual_of_mem_stateSpace he hφ] using
    (toStrongDual φ).le_opNorm a

theorem nnNorm_apply_le_of_mem_stateSpace (he : IsOrderUnitNorm e) (hφ : φ ∈ stateSpace e)
    (a : E) :
    ‖φ a‖₊ ≤ ‖a‖₊ := by
  rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, Real.norm_eq_abs]
  exact abs_apply_le_norm_of_mem_stateSpace he hφ a

/-- **Weak-* compactness of the state space.** By Banach–Alaoglu, `stateSpace e` is weak-* compact
as a closed subset of the unit ball of `WeakDual ℝ E`. -/
theorem isCompact_stateSpace (he : IsOrderUnitNorm e) :
    IsCompact (stateSpace e) := by
  refine (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset (isClosed_stateSpace e)
    fun φ hφ => ?_
  simp [norm_toStrongDual_of_mem_stateSpace he hφ]

/-- `CompactSpace` witness on the subtype `stateSpace e`. -/
theorem compactSpace_stateSpace (he : IsOrderUnitNorm e) :
    CompactSpace (stateSpace e) :=
  isCompact_iff_compactSpace.mp (isCompact_stateSpace he)

/-- **Krein–Milman for the state space.** `stateSpace e` is the weak-* closed convex hull of its
extreme points (pure states). -/
theorem closure_convexHull_extremePoints_stateSpace (he : IsOrderUnitNorm e) :
    closure (convexHull ℝ (extremePoints ℝ (stateSpace e))) = stateSpace e :=
  closure_convexHull_extremePoints (isCompact_stateSpace he) (convex_stateSpace e)

end Seminormed

section NormedOrderUnit

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} {φ : WeakDual ℝ E}

/-- **Norm-and-value characterization of states.** On an order-unit normed space `(E, e)`, a
functional `φ ∈ WeakDual ℝ E` is a state if and only if `‖φ‖ = 1` and `φ e = 1`; positivity follows
automatically. -/
theorem mem_stateSpace_iff_norm_eq_one_and_apply (he : IsOrderUnitNorm e) :
    φ ∈ stateSpace e ↔ ‖toStrongDual φ‖ = 1 ∧ φ e = 1 :=
  (toStrongDual φ).monotone_and_apply_eq_one_iff he

/-- Equivalence between `stateSpace e` and algebraic positive linear functionals `E →ₚ[ℝ] ℝ`
normalized at `e`, using automatic continuity on an order-unit normed space. -/
noncomputable def stateSpaceEquivPositiveLinearMap (he : IsOrderUnitNorm e) :
    stateSpace e ≃ {ω : E →ₚ[ℝ] ℝ // ω e = 1} where
  toFun φ := ⟨.mk₀ (toStrongDual φ.1).toLinearMap
    fun _ ha => map_nonneg_of_mem_stateSpace φ.2 ha, φ.2.2⟩
  invFun ω :=
    ⟨StrongDual.toWeakDual
      ((ω.1.toPositiveContinuousLinearMapOfOrderUnit he IsOrderUnitNorm.one_real : E →P[ℝ] ℝ) :
        E →L[ℝ] ℝ),
      (ω.1.toPositiveContinuousLinearMapOfOrderUnit he
        IsOrderUnitNorm.one_real).toWeakDual_mem_orderUnitStateSpace_iff.mpr ω.2⟩
  left_inv _ := Subtype.ext (DFunLike.ext _ _ fun _ => rfl)
  right_inv _ := Subtype.ext (PositiveLinearMap.ext fun _ => rfl)

@[simp]
theorem stateSpaceEquivPositiveLinearMap_apply (he : IsOrderUnitNorm e) (φ : stateSpace e)
    (a : E) :
    (stateSpaceEquivPositiveLinearMap he φ).1 a = φ.1 a :=
  (rfl)

@[simp]
theorem stateSpaceEquivPositiveLinearMap_symm_apply (he : IsOrderUnitNorm e)
    (ω : {ω : E →ₚ[ℝ] ℝ // ω e = 1}) (a : E) :
    ((stateSpaceEquivPositiveLinearMap he).symm ω).1 a = ω.1 a :=
  (rfl)

/-- **Existence of states.** Every space satisfying `IsOrderUnitNorm e` admits at least one state,
constructed by Hahn–Banach extension of `r • e ↦ r` with norm `1` and automatic positivity. -/
theorem stateSpace_nonempty (he : IsOrderUnitNorm e) :
    (stateSpace e).Nonempty := by
  have he_norm_ne : ‖e‖ ≠ 0 := by simp [he.norm_e]
  obtain ⟨g, hg_norm, hge⟩ := exists_dual_vector ℝ e he_norm_ne
  refine ⟨StrongDual.toWeakDual g, (mem_stateSpace_iff_norm_eq_one_and_apply he).mpr ⟨hg_norm, ?_⟩⟩
  simpa [he.norm_e] using hge

/-- **Existence of pure states.** Every order-unit normed space has at least one extreme state. -/
theorem extremePoints_stateSpace_nonempty (he : IsOrderUnitNorm e) :
    (extremePoints ℝ (stateSpace e)).Nonempty :=
  (isCompact_stateSpace he).extremePoints_nonempty (stateSpace_nonempty he)

end NormedOrderUnit

/-! ### Functoriality, Hahn–Banach state extension, and completion invariance -/

section Functoriality

section Pullback

variable {E F G : Type*}
  [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
  [SeminormedAddCommGroup G] [NormedSpace ℝ G] [PartialOrder G] [IsOrderedAddMonoid G]
  {e : E} {f : F} {g : G}

/-- Precomposition of functionals in `WeakDual ℝ F` with a positive linear map `T : E →ₚ[ℝ] F`
between order-unit normed spaces, as a weak-* continuous real linear map
`WeakDual ℝ F →L[ℝ] WeakDual ℝ E`. -/
noncomputable def pullbackFunctional (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : E →ₚ[ℝ] F) : WeakDual ℝ F →L[ℝ] WeakDual ℝ E where
  toFun φ := StrongDual.toWeakDual
    ((toStrongDual φ).comp (T.toPositiveContinuousLinearMapOfOrderUnit he hf : E →L[ℝ] F))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_of_continuous_eval fun a => eval_continuous (T a)

@[simp]
theorem pullbackFunctional_apply (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : E →ₚ[ℝ] F) (φ : WeakDual ℝ F) (a : E) :
    pullbackFunctional he hf T φ a = φ (T a) :=
  (rfl)

@[simp]
theorem pullbackFunctional_id [IsOrderedAddMonoid E] (he : IsOrderUnitNorm e) :
    pullbackFunctional he he (.id ℝ E) = ContinuousLinearMap.id ℝ (WeakDual ℝ E) :=
  ContinuousLinearMap.ext fun _ => DFunLike.ext _ _ fun _ => rfl

theorem pullbackFunctional_comp (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (hg : IsOrderUnitNorm g) (S : F →ₚ[ℝ] G) (T : E →ₚ[ℝ] F) :
    pullbackFunctional he hg (S.comp T) =
      (pullbackFunctional he hf T).comp (pullbackFunctional hf hg S) :=
  ContinuousLinearMap.ext fun _ => DFunLike.ext _ _ fun _ => rfl

/-- **Pullback of states along a unital positive map.** If `T : E →ₚ[ℝ] F` satisfies `T e = f`,
precomposing with `T` carries `stateSpace f` into `stateSpace e`. -/
theorem mapsTo_pullbackFunctional_stateSpace (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : E →ₚ[ℝ] F) (hTe : T e = f) :
    MapsTo (pullbackFunctional he hf T) (stateSpace f) (stateSpace e) := by
  intro φ hφ
  refine ⟨fun a b hab => hφ.1 (map_rel T hab), ?_⟩
  simpa [hTe] using hφ.2

end Pullback

section Extension

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
  {e : E} {f : F}

/-- **Hahn–Banach extension of states along a unital linear isometry.** If `i : E →ₗᵢ[ℝ] F` maps the
order unit `e` of `E` to the order unit `f` of `F`, every state `φ ∈ stateSpace e` extends to a
state `ψ ∈ stateSpace f` satisfying `ψ (i a) = φ a` for all `a : E`. -/
theorem exists_mem_stateSpace_comp_eq (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (i : E →ₗᵢ[ℝ] F) (hie : i e = f) {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e) :
    ∃ ψ ∈ stateSpace f, ∀ a : E, ψ (i a) = φ a := by
  obtain ⟨g, hgi, hgnorm⟩ := i.exists_extension_norm_eq (toStrongDual φ)
  have hnorm : ‖g‖ = 1 := hgnorm.trans (norm_toStrongDual_of_mem_stateSpace he hφ)
  have hgf : g f = 1 := by
    have h := DFunLike.congr_fun hgi e
    simpa [hie] using h.trans hφ.2
  refine ⟨StrongDual.toWeakDual g,
    (mem_stateSpace_iff_norm_eq_one_and_apply hf).mpr ⟨hnorm, hgf⟩, fun a => ?_⟩
  exact DFunLike.congr_fun hgi a

/-- Every unital positive linear isometric embedding `i : E →ₗᵢ[ℝ] F` induces a surjection from
`stateSpace f` onto `stateSpace e` via `pullbackFunctional`. -/
theorem surjOn_pullbackFunctional_stateSpace
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (i : E →ₗᵢ[ℝ] F)
    (hmono : Monotone i) (hie : i e = f) :
    SurjOn (pullbackFunctional he hf ⟨i.toLinearMap, hmono⟩) (stateSpace f) (stateSpace e) := by
  intro φ hφ
  obtain ⟨ψ, hψ, hcomp⟩ := exists_mem_stateSpace_comp_eq he hf i hie hφ
  exact ⟨ψ, hψ, DFunLike.ext _ _ hcomp⟩

end Extension

section Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- **Hahn–Banach extension of states from a unital submodule.** For any real submodule
`S : Submodule ℝ E` with `heS : e ∈ S`, every state `φ ∈ stateSpace (⟨e, heS⟩ : S)` extends to a
state `ψ ∈ stateSpace e` agreeing with `φ` on `S`. -/
theorem exists_mem_stateSpace_forall_apply_coe_eq (he : IsOrderUnitNorm e)
    (S : Submodule ℝ E) (heS : e ∈ S)
    {φ : WeakDual ℝ S} (hφ : φ ∈ stateSpace (⟨e, heS⟩ : S)) :
    ∃ ψ ∈ stateSpace e, ∀ a : S, ψ a = φ a :=
  exists_mem_stateSpace_comp_eq (he.submodule S heS) he S.subtypeₗᵢ rfl hφ

/-- Restriction of states from `(E, e)` to a unital submodule `S` containing `e`, as a continuous
map `stateSpace e → stateSpace (⟨e, heS⟩ : S)`. -/
noncomputable def restrictState (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (heS : e ∈ S) :
    C(stateSpace e, stateSpace (⟨e, heS⟩ : S)) where
  toFun ψ := ⟨pullbackFunctional (he.submodule S heS) he
      ⟨S.subtype, fun _ _ h => h⟩ ψ.1,
    mapsTo_pullbackFunctional_stateSpace (he.submodule S heS) he
      ⟨S.subtype, fun _ _ h => h⟩ rfl ψ.2⟩
  continuous_toFun :=
    ((pullbackFunctional (he.submodule S heS) he
      ⟨S.subtype, fun _ _ h => h⟩).continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem restrictState_apply (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (heS : e ∈ S)
    (ψ : stateSpace e) (a : S) :
    (restrictState he S heS ψ).1 a = ψ.1 a :=
  (rfl)

theorem restrictState_surjective (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (heS : e ∈ S) :
    Function.Surjective (restrictState he S heS) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨ψ, hψ, h⟩ := exists_mem_stateSpace_forall_apply_coe_eq he S heS hφ
  exact ⟨⟨ψ, hψ⟩, Subtype.ext (DFunLike.ext _ _ h)⟩

end Submodule

section Completion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- **Extension of a state to the completion.** Every state `φ ∈ stateSpace e` extends uniquely by
uniform continuity to a state on `UniformSpace.Completion E` equipped with
`he.completionPartialOrder`. -/
noncomputable def extendStateToCompletion (he : IsOrderUnitNorm e) (φ : stateSpace e) :
    letI := he.completionPartialOrder
    stateSpace (e : Completion E) :=
  letI := he.completionPartialOrder
  haveI := he.completionIsOrderedAddMonoid
  ⟨StrongDual.toWeakDual (toStrongDual φ.1).fromCompletion, by
    rw [mem_stateSpace_iff_map_nonneg]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [he.completion_nonneg_iff, mem_completionNonnegCone_def] at hx
      have hclosed : IsClosed {y : Completion E | 0 ≤ (toStrongDual φ.1).fromCompletion y} :=
        isClosed_Ici.preimage (toStrongDual φ.1).fromCompletion.continuous
      refine hclosed.closure_subset_iff.mpr ?_ hx
      rintro _ ⟨a, ha, rfl⟩
      rw [Set.mem_ofPred, ContinuousLinearMap.fromCompletion_apply_coe]
      exact map_nonneg_of_mem_stateSpace φ.2 ha
    · simp [φ.2.2]⟩

@[simp]
theorem extendStateToCompletion_apply_coe (he : IsOrderUnitNorm e) (φ : stateSpace e) (a : E) :
    letI := he.completionPartialOrder
    (extendStateToCompletion he φ).1 (a : Completion E) = φ.1 a :=
  ContinuousLinearMap.fromCompletion_apply_coe (toStrongDual φ.1) a

/-- **State space invariance under completion.** Restricting states along `E → Completion E` gives
a weak-* homeomorphism between `stateSpace (e : Completion E)` and `stateSpace e`, with inverse
`extendStateToCompletion he`. -/
noncomputable def completionStateHomeomorph (he : IsOrderUnitNorm e) :
    letI := he.completionPartialOrder
    stateSpace (e : Completion E) ≃ₜ stateSpace e := by
  letI := he.completionPartialOrder
  haveI := he.completionIsOrderedAddMonoid
  haveI : CompactSpace (stateSpace (e : Completion E)) := compactSpace_stateSpace he.completion
  let restrictL : WeakDual ℝ (Completion E) →L[ℝ] WeakDual ℝ E :=
    pullbackFunctional he he.completion
      ⟨Completion.toComplL.toLinearMap, fun a b hab => (he.completion_coe_le_coe).mpr hab⟩
  have hmaps : MapsTo restrictL (stateSpace (e : Completion E)) (stateSpace e) :=
    mapsTo_pullbackFunctional_stateSpace he he.completion _ rfl
  let eqv : stateSpace (e : Completion E) ≃ stateSpace e :=
    { toFun := fun ψ => ⟨restrictL ψ.1, hmaps ψ.2⟩
      invFun := extendStateToCompletion he
      left_inv := fun ψ => Subtype.ext <| WeakDual.toStrongDual.injective <|
        (toStrongDual (restrictL ψ.1)).fromCompletion_unique (toStrongDual ψ.1) fun _ => rfl
      right_inv := fun φ =>
        Subtype.ext (DFunLike.ext _ _ fun a => extendStateToCompletion_apply_coe he φ a) }
  have hcont : Continuous eqv :=
    (restrictL.continuous.comp continuous_subtype_val).subtype_mk _
  exact hcont.homeoOfEquivCompactToT2

@[simp]
theorem completionStateHomeomorph_apply (he : IsOrderUnitNorm e)
    (ψ : letI := he.completionPartialOrder; stateSpace (e : Completion E)) (a : E) :
    letI := he.completionPartialOrder
    (completionStateHomeomorph he ψ).1 a = ψ.1 (a : Completion E) :=
  (rfl)

@[simp]
theorem completionStateHomeomorph_symm_apply_coe (he : IsOrderUnitNorm e)
    (φ : stateSpace e) (a : E) :
    letI := he.completionPartialOrder
    ((completionStateHomeomorph he).symm φ).1 (a : Completion E) = φ.1 a :=
  extendStateToCompletion_apply_coe he φ a

end Completion

end Functoriality

/-! ### Cone separation, norm detection by states, and Kadison's isometric order embedding -/

section Kadison

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- **Order detection by states.** An element `a` of an order-unit normed space is nonnegative if
and only if `0 ≤ φ a` for every state `φ ∈ stateSpace e`. -/
theorem nonneg_iff_forall_stateSpace (he : IsOrderUnitNorm e) {a : E} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace e, 0 ≤ φ a := by
  refine ⟨fun ha _ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  have := he.posSMulMono
  have := he.orderClosedTopology
  by_contra ha
  have haC : a ∉ ProperCone.positive ℝ E := ha
  obtain ⟨f, hf_pos, hfa⟩ := (ProperCone.positive ℝ E).hyperplane_separation_point haC
  have hfe : 0 < f e := by
    by_contra! hfe_le
    have hbound : 0 ≤ ‖a‖ • e + a := by
      have hneg : -(‖a‖ • e) ≤ a := by simpa [neg_smul] using he.neg_norm_smul_le a
      exact neg_le_iff_add_nonneg'.mp hneg
    have hf_bound : 0 ≤ f (‖a‖ • e + a) := hf_pos (‖a‖ • e + a) hbound
    rw [map_add, map_smul, smul_eq_mul] at hf_bound
    have hmul : ‖a‖ * f e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg a) hfe_le
    linarith
  let φ : WeakDual ℝ E := StrongDual.toWeakDual ((f e)⁻¹ • f)
  have hφ : φ ∈ stateSpace e := by
    rw [mem_stateSpace_iff_map_nonneg]
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [φ, StrongDual.toWeakDual_apply, smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hfe.le) (hf_pos x hx)
    · simp [φ, hfe.ne']
  have hφa : 0 ≤ φ a := h φ hφ
  simp only [φ, StrongDual.toWeakDual_apply, smul_apply, smul_eq_mul] at hφa
  have hpos_inv : 0 < (f e)⁻¹ := inv_pos.mpr hfe
  have hfa_nonneg : 0 ≤ f a := nonneg_of_mul_nonneg_right hφa hpos_inv
  linarith

/-- States detect the partial order: `a ≤ b ↔ ∀ φ ∈ stateSpace e, φ a ≤ φ b`. -/
theorem le_iff_forall_stateSpace (he : IsOrderUnitNorm e) {a b : E} :
    a ≤ b ↔ ∀ φ ∈ stateSpace e, φ a ≤ φ b := by
  rw [← sub_nonneg, nonneg_iff_forall_stateSpace he]
  simp [sub_nonneg]

/-- States separate points of an order-unit normed space. -/
theorem eq_of_forall_stateSpace (he : IsOrderUnitNorm e) {a b : E}
    (h : ∀ φ ∈ stateSpace e, φ a = φ b) :
    a = b :=
  le_antisymm ((le_iff_forall_stateSpace he).mpr fun φ hφ => (h φ hφ).le)
    ((le_iff_forall_stateSpace he).mpr fun φ hφ => (h φ hφ).ge)

/-- **Norm detection by states.** For every `a` in an order-unit normed space `(E, e)`,
`‖a‖ = ⨆ φ : stateSpace e, |φ.1 a|`; neither completeness nor separability is required. -/
theorem norm_eq_iSup_states (he : IsOrderUnitNorm e) (a : E) :
    ‖a‖ = ⨆ φ : stateSpace e, |φ.1 a| := by
  have : Nonempty (stateSpace e) := (stateSpace_nonempty he).to_subtype
  have hbdd : BddAbove (range fun φ : stateSpace e => |φ.1 a|) :=
    ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact abs_apply_le_norm_of_mem_stateSpace he φ.2 a⟩
  set r := ⨆ φ : stateSpace e, |φ.1 a|
  apply le_antisymm
  · obtain ⟨φ₀⟩ := ‹Nonempty (stateSpace e)›
    have hr : 0 ≤ r := (abs_nonneg _).trans (le_ciSup hbdd φ₀)
    rw [he.norm_le_iff a r hr, le_iff_forall_stateSpace he, le_iff_forall_stateSpace he]
    refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
    · have hle : -r ≤ φ a := (abs_le.mp (le_ciSup hbdd ⟨φ, hφ⟩)).1
      simpa [hφ.2] using hle
    · have hle : φ a ≤ r := (abs_le.mp (le_ciSup hbdd ⟨φ, hφ⟩)).2
      simpa [hφ.2] using hle
  · exact ciSup_le fun φ => abs_apply_le_norm_of_mem_stateSpace he φ.2 a

/-- `ℝ≥0`-valued norm detection by states: `‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.1 a‖₊`. -/
theorem nnNorm_eq_iSup_states (he : IsOrderUnitNorm e) (a : E) :
    ‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.1 a‖₊ := by
  have : Nonempty (stateSpace e) := (stateSpace_nonempty he).to_subtype
  apply NNReal.eq
  rw [coe_nnNorm, norm_eq_iSup_states he a, NNReal.coe_iSup]
  simp [coe_nnNorm, Real.norm_eq_abs]

/-- By weak-* compactness of `stateSpace e`, every `a : E` attains its norm `|φ a| = ‖a‖` at some
state `φ ∈ stateSpace e`. -/
theorem exists_mem_stateSpace_abs_apply_eq_norm (he : IsOrderUnitNorm e) (a : E) :
    ∃ φ ∈ stateSpace e, |φ a| = ‖a‖ := by
  obtain ⟨φ, hφ, hmax⟩ := (isCompact_stateSpace he).exists_isMaxOn (stateSpace_nonempty he)
    (eval_continuous a).abs.continuousOn
  refine ⟨φ, hφ, le_antisymm (abs_apply_le_norm_of_mem_stateSpace he hφ a) ?_⟩
  rw [norm_eq_iSup_states he a]
  have : Nonempty (stateSpace e) := ⟨⟨φ, hφ⟩⟩
  exact ciSup_le fun ψ => hmax ψ.2

/-- **Kadison's isometric unital order embedding.** Evaluation of elements of `E` on `stateSpace e`
defines a linear isometric order embedding `E →ₗᵢ[ℝ] C(stateSpace e, ℝ)` sending `e` to `1`. -/
noncomputable def kadisonEmbedding (he : IsOrderUnitNorm e) :
    letI := compactSpace_stateSpace he
    E →ₗᵢ[ℝ] C(stateSpace e, ℝ) := by
  haveI : Nonempty (stateSpace e) := (stateSpace_nonempty he).to_subtype
  letI : CompactSpace (stateSpace e) := compactSpace_stateSpace he
  let L : E →ₗ[ℝ] C(stateSpace e, ℝ) :=
    { toFun := fun a => ⟨fun φ => φ.1 a, (eval_continuous a).comp continuous_subtype_val⟩
      map_add' := fun a b => by ext φ; exact map_add φ.1 a b
      map_smul' := fun r a => by ext φ; exact map_smul φ.1 r a }
  exact L.toLinearIsometryOfOrderUnit he IsOrderUnitNorm.one_continuousMap
    (by ext φ; exact φ.2.2)
    (fun a b => by
      rw [ContinuousMap.le_def, le_iff_forall_stateSpace he]
      exact ⟨fun h φ hφ => h ⟨φ, hφ⟩, fun h φ => h φ.1 φ.2⟩)

@[simp]
theorem kadisonEmbedding_apply (he : IsOrderUnitNorm e) (a : E) (φ : stateSpace e) :
    letI := compactSpace_stateSpace he
    kadisonEmbedding he a φ = φ.1 a := by
  let := compactSpace_stateSpace he
  unfold kadisonEmbedding
  rw [LinearMap.toLinearIsometryOfOrderUnit_apply]
  rfl

@[simp]
theorem kadisonEmbedding_orderUnit (he : IsOrderUnitNorm e) :
    letI := compactSpace_stateSpace he
    kadisonEmbedding he e = 1 := by
  let := compactSpace_stateSpace he
  ext φ
  simp

@[simp]
theorem kadisonEmbedding_le_iff (he : IsOrderUnitNorm e) {a b : E} :
    (letI := compactSpace_stateSpace he; kadisonEmbedding he a ≤ kadisonEmbedding he b) ↔
      a ≤ b := by
  let := compactSpace_stateSpace he
  rw [ContinuousMap.le_def, le_iff_forall_stateSpace he]
  simp only [kadisonEmbedding_apply]
  exact ⟨fun h φ hφ => h ⟨φ, hφ⟩, fun h φ => h φ.1 φ.2⟩

@[simp]
theorem kadisonEmbedding_nonneg_iff (he : IsOrderUnitNorm e) {a : E} :
    (letI := compactSpace_stateSpace he; 0 ≤ kadisonEmbedding he a) ↔ 0 ≤ a := by
  let := compactSpace_stateSpace he
  rw [← map_zero (kadisonEmbedding he), kadisonEmbedding_le_iff]

end Kadison

end TauCeti.OrderUnit
