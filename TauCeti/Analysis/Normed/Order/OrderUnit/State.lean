/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.Analysis.Normed.Module.Quotient
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Convex.Cone.PositiveDual
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.Dual.Quotient
import TauCeti.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Order.PositiveLinearMap
import TauCeti.MeasureTheory.Integral.RieszMarkovKakutani.Signed

/-!
# States, Kadison's affine representation, and the dual-ball identity

On a real ordered normed space `E` with distinguished order unit `e`, the **state space**
`TauCeti.OrderUnit.stateSpace e` is the set of monotone functionals `φ : WeakDual ℝ E` normalized by
`φ e = 1`, equipped with the inherited weak-star topology. When `e` satisfies
`TauCeti.OrderUnit.IsOrderUnitNorm e`:

1. **States and geometry (`stateSpace`):** Every state has operator norm `1`, and conversely any
   continuous linear functional `φ` with `‖φ‖ ≤ 1` and `φ e = 1` is automatically monotone (hence a
   state). Every algebraic positive linear functional `E →ₚ[ℝ] ℝ` normalized at `e` is automatically
   continuous and gives a state. By Hahn–Banach and Banach–Alaoglu, `stateSpace e` is nonempty,
   convex, weak-star closed, and weak-star compact, hence equals the weak-star closed convex hull of
   its extreme points. States pull back along unital positive linear maps and extend by Hahn–Banach
   from unital subspaces.
2. **Kadison's representation (`kadisonEval`):** States detect nonnegativity, the partial order,
   equality, and the norm (`‖a‖ = ⨆ φ : stateSpace e, |φ.1 a|`). Pointwise evaluation defines an
   isometric unital order embedding `kadisonEval : E →ₗᵢ[ℝ] C(stateSpace e, ℝ)` whose range is
   uniformly dense in the space of continuous affine functions on `stateSpace e`, and equal to it
   whenever `E` is complete.
3. **Scalar-line quotient and Rieffel's dual-ball identity (`scalarLine`):** For `scalarLine e =
   ℝ ∙ e`, the quotient norm on `E ⧸ scalarLine e` is half the spread of `a` across `stateSpace e`,
   `‖Submodule.Quotient.mk a‖ = (stateMax he a - stateMin he a) / 2`, attained at the midpoint
   multiple `((stateMax he a + stateMin he a) / 2) • e`. Identifying
   `StrongDual ℝ (E ⧸ scalarLine e)` with `{λ : StrongDual ℝ E // λ e = 0}` via
   `Submodule.quotientDualEquivAnnihilator`, the centered dual ball
   `{λ : StrongDual ℝ E | λ e = 0 ∧ ‖λ‖ ≤ 2}` coincides with the set of differences of two
   states `{toStrongDual φ - toStrongDual ψ | (φ ∈ stateSpace e) (ψ ∈ stateSpace e)}`.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. **7** (1951).
* E. M. Alfsen, *Compact Convex Sets and Boundary Integrals*, Springer, 1971, Theorem II.1.8.
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. **4** (1999), 559–600, §1.
-/

public section

open Set Filter WeakDual
open scoped NNReal Topology CompactlySupported

namespace TauCeti.OrderUnit

/-! ### The state space of an order-unit normed space -/

section StateSpace

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]

/-- The **state space** of a real ordered seminormed space `E` with distinguished unit `e`, as a
subset of the weak-star dual `WeakDual ℝ E`: the monotone functionals normalized by `φ e = 1`. -/
def stateSpace (e : E) : Set (WeakDual ℝ E) :=
  {φ | Monotone φ ∧ φ e = 1}

/-- Membership in `stateSpace e` unfolds to monotonicity and normalization at `e`. -/
theorem mem_stateSpace_iff {e : E} {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ Monotone φ ∧ φ e = 1 :=
  Iff.rfl

/-- A state is monotone. -/
theorem monotone_of_mem_stateSpace {e : E} {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e) :
    Monotone φ :=
  hφ.1

/-- A state evaluates to `1` at the order unit `e`. -/
theorem map_unit_of_mem_stateSpace {e : E} {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e) :
    φ e = 1 :=
  hφ.2

/-- The state space is convex. -/
theorem convex_stateSpace (e : E) : Convex ℝ (stateSpace e) := by
  intro φ hφ ψ hψ s t hs ht hst
  refine ⟨fun a b hab => ?_, ?_⟩
  · simpa using add_le_add (smul_le_smul_of_nonneg_left (hφ.1 hab) hs)
      (smul_le_smul_of_nonneg_left (hψ.1 hab) ht)
  · simp [hφ.2, hψ.2, hst]

section Ordered

variable [IsOrderedAddMonoid E]

/-- In an ordered additive group, `φ ∈ stateSpace e` iff `φ` is nonnegative on `{a | 0 ≤ a}` and
`φ e = 1`. -/
theorem mem_stateSpace_iff_map_nonneg {e : E} {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ (∀ a : E, 0 ≤ a → 0 ≤ φ a) ∧ φ e = 1 := by
  refine and_congr_left' ?_
  change Monotone (toStrongDual φ) ↔ _
  exact monotone_iff_map_nonneg (toStrongDual φ)

/-- A state maps nonnegative elements to nonnegative reals. -/
theorem map_nonneg_of_mem_stateSpace {e : E} {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e)
    {a : E} (ha : 0 ≤ a) : 0 ≤ φ a :=
  (mem_stateSpace_iff_map_nonneg.1 hφ).1 a ha

/-- The state space is weak-star closed. -/
theorem isClosed_stateSpace (e : E) : IsClosed (stateSpace e) := by
  have h : stateSpace e = {φ : WeakDual ℝ E | ∀ a, 0 ≤ a → 0 ≤ φ a} ∩ {φ | φ e = 1} :=
    Set.ext fun _ => mem_stateSpace_iff_map_nonneg
  rw [h]
  exact WeakDual.isClosed_setOf_map_nonneg.inter (isClosed_eq (eval_continuous e) continuous_const)

end Ordered

end StateSpace

namespace IsOrderUnitNorm

section States

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}

/-- Every state of an order-unit normed space has operator norm `1`. -/
theorem norm_toStrongDual_of_mem_stateSpace (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E}
    (hφ : φ ∈ stateSpace e) : ‖toStrongDual φ‖ = 1 :=
  (ContinuousLinearMap.opNorm_eq_apply_of_monotone (toStrongDual φ) hφ.1 he.le_norm_smul
    he.norm_eq_one.le).trans hφ.2

/-- Every state is contractive: `|φ a| ≤ ‖a‖`. -/
theorem abs_apply_le_norm_of_mem_stateSpace (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E}
    (hφ : φ ∈ stateSpace e) (a : E) : |φ a| ≤ ‖a‖ := by
  simpa [Real.norm_eq_abs, he.norm_toStrongDual_of_mem_stateSpace hφ] using
    (toStrongDual φ).le_opNorm a

/-- **Weak-star compactness of the state space.** By Banach–Alaoglu, `stateSpace e` is weak-star
compact whenever `[IsOrderedAddMonoid E]` and `IsOrderUnitNorm e`. -/
theorem isCompact_stateSpace [IsOrderedAddMonoid E] (he : IsOrderUnitNorm e) :
    IsCompact (stateSpace e) :=
  (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset (isClosed_stateSpace e) fun φ hφ => by
    simp [he.norm_toStrongDual_of_mem_stateSpace hφ]

/-- `stateSpace e` as a compact topological space under `IsOrderUnitNorm e`. -/
theorem compactSpace_stateSpace [IsOrderedAddMonoid E] (he : IsOrderUnitNorm e) :
    CompactSpace (stateSpace e) :=
  isCompact_iff_compactSpace.1 he.isCompact_stateSpace

/-- **Krein–Milman for the state space.** `stateSpace e` is the weak-star closed convex hull of its
extreme points (pure states). -/
theorem closure_convexHull_extremePoints_stateSpace [IsOrderedAddMonoid E]
    (he : IsOrderUnitNorm e) :
    closure (convexHull ℝ (extremePoints ℝ (stateSpace e))) = stateSpace e :=
  closure_convexHull_extremePoints he.isCompact_stateSpace (convex_stateSpace e)

/-- Promote an algebraic positive linear functional `ω : E →ₚ[ℝ] ℝ` on an order-unit normed space
to an element of `WeakDual ℝ E`. -/
def positiveLinearMapToWeakDual (he : IsOrderUnitNorm e) (ω : E →ₚ[ℝ] ℝ) : WeakDual ℝ E :=
  StrongDual.toWeakDual
    { toLinearMap := ω.toLinearMap
      cont := PositiveLinearMap.continuous_of_forall_le_norm_smul ω he.le_norm_smul }

/-- `he.positiveLinearMapToWeakDual ω` evaluates as `ω`. -/
@[simp]
theorem positiveLinearMapToWeakDual_apply (he : IsOrderUnitNorm e) (ω : E →ₚ[ℝ] ℝ) (a : E) :
    he.positiveLinearMapToWeakDual ω a = ω a :=
  (rfl)

/-- An algebraic positive linear functional defines a state iff it sends `e` to `1`. -/
@[simp]
theorem positiveLinearMapToWeakDual_mem_stateSpace_iff (he : IsOrderUnitNorm e) (ω : E →ₚ[ℝ] ℝ) :
    he.positiveLinearMapToWeakDual ω ∈ stateSpace e ↔ ω e = 1 :=
  ⟨fun h => h.2, fun h1 => ⟨ω.monotone, h1⟩⟩

/-- States are precisely the weak-star functionals arising from algebraic positive linear maps
normalized at `e`. -/
theorem mem_stateSpace_iff_exists_positiveLinearMap (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ ∃ ω : E →ₚ[ℝ] ℝ, ω e = 1 ∧ he.positiveLinearMapToWeakDual ω = φ := by
  refine ⟨fun hφ => ?_, fun ⟨ω, h1, hω⟩ =>
    hω ▸ (he.positiveLinearMapToWeakDual_mem_stateSpace_iff ω).2 h1⟩
  exact ⟨{ toLinearMap := (toStrongDual φ).toLinearMap, monotone' := hφ.1 }, hφ.2,
    DFunLike.ext _ _ fun _ => rfl⟩

variable [IsOrderedAddMonoid E] [PosSMulMono ℝ E]

/-- **Automatic positivity from norm one.** On an order-unit normed space, a continuous linear
functional is a state iff `‖φ‖ ≤ 1` and `φ e = 1`. -/
theorem mem_stateSpace_iff_norm_le_one (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ ‖toStrongDual φ‖ ≤ 1 ∧ φ e = 1 := by
  refine ⟨fun hφ => ⟨(he.norm_toStrongDual_of_mem_stateSpace hφ).le, hφ.2⟩,
    fun ⟨hnorm, h1⟩ => mem_stateSpace_iff_map_nonneg.2 ⟨fun a ha => ?_, h1⟩⟩
  have hbound (g : E) :
      |(toStrongDual φ : E →ₗ[ℝ] ℝ) g| ≤ (toStrongDual φ : E →ₗ[ℝ] ℝ) e * ‖g‖ := by
    calc |φ g| = ‖(toStrongDual φ) g‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖toStrongDual φ‖ * ‖g‖ := (toStrongDual φ).le_opNorm g
      _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg g)
      _ = φ e * ‖g‖ := by rw [h1]
  exact LinearMap.apply_nonneg_of_abs_apply_le_mul_norm (toStrongDual φ : E →ₗ[ℝ] ℝ) hbound
    ((he.nonneg_iff_norm_sub_le a).1 ha)

/-- On an order-unit normed space, `φ ∈ stateSpace e` iff `‖φ‖ = 1` and `φ e = 1`. -/
theorem mem_stateSpace_iff_norm_eq_one (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ ‖toStrongDual φ‖ = 1 ∧ φ e = 1 :=
  ⟨fun hφ => ⟨he.norm_toStrongDual_of_mem_stateSpace hφ, hφ.2⟩,
    fun ⟨hnorm, h1⟩ => he.mem_stateSpace_iff_norm_le_one.2 ⟨hnorm.le, h1⟩⟩

/-- **Existence of states.** Every order-unit normed space admits a state, obtained by extending
the coordinate functional on `ℝ ∙ e` via Hahn–Banach. -/
theorem stateSpace_nonempty (he : IsOrderUnitNorm e) : (stateSpace e).Nonempty := by
  obtain ⟨g, hg, hge⟩ := exists_dual_vector ℝ e (by simp [he.norm_eq_one])
  refine ⟨StrongDual.toWeakDual g, he.mem_stateSpace_iff_norm_eq_one.2 ⟨hg, ?_⟩⟩
  simpa [he.norm_eq_one] using hge

/-- Nonemptiness of the subtype `stateSpace e`. -/
theorem nonempty_stateSpace (he : IsOrderUnitNorm e) : Nonempty (stateSpace e) :=
  he.stateSpace_nonempty.to_subtype

/-- Every order-unit normed space has at least one pure (extreme) state. -/
theorem extremePoints_stateSpace_nonempty (he : IsOrderUnitNorm e) :
    (extremePoints ℝ (stateSpace e)).Nonempty :=
  he.isCompact_stateSpace.extremePoints_nonempty he.stateSpace_nonempty

end States

/-! ### Pullback along unital positive maps and Hahn–Banach extension of states -/

section PullbackAndExtension

variable {E F M : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
  [IsOrderedAddMonoid F] [PosSMulMono ℝ F]
  [FunLike M E F] [LinearMapClass M ℝ E F] [OrderHomClass M E F]
  {e : E} {f : F}

/-- Weak-star continuous linear pullback of functionals along a positive linear map between
order-unit normed spaces. -/
noncomputable def pullbackWeakDual (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M) :
    WeakDual ℝ F →L[ℝ] WeakDual ℝ E where
  toFun φ := StrongDual.toWeakDual
    ((toStrongDual φ).comp (he.toPositiveContinuousLinearMap hf T : E →L[ℝ] F))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.continuous_of_continuous_eval fun a => by
    simpa [toPositiveContinuousLinearMap_apply] using eval_continuous (T a)

/-- The pullback functional evaluates by precomposition with `T`. -/
@[simp]
theorem pullbackWeakDual_apply (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M)
    (φ : WeakDual ℝ F) (a : E) :
    he.pullbackWeakDual hf T φ a = φ (T a) := by
  change φ ((he.toPositiveContinuousLinearMap hf T) a) = φ (T a)
  rw [toPositiveContinuousLinearMap_apply]

/-- Unital positive linear maps pull states back to states. -/
theorem mapsTo_pullbackWeakDual_stateSpace (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : M) (hunit : T e = f) :
    MapsTo (he.pullbackWeakDual hf T) (stateSpace f) (stateSpace e) := by
  intro φ hφ
  refine ⟨fun a b hab => ?_, ?_⟩
  · simpa using hφ.1 (map_rel T hab)
  · simp [hunit, hφ.2]

/-- **Extension of states along a unital linear isometry.** Every state on `(E, e)` extends along a
linear isometry `i : E →ₗᵢ[ℝ] F` sending `e` to `f` to a state on `(F, f)`. -/
theorem exists_mem_stateSpace_comp_linearIsometry
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (i : E →ₗᵢ[ℝ] F) (hunit : i e = f)
    {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e) :
    ∃ ψ ∈ stateSpace f, ∀ a : E, ψ (i a) = φ a := by
  let _ := he.normedAddCommGroup
  obtain ⟨ψ, hψ, hnorm⟩ := i.exists_extension_norm_eq (toStrongDual φ)
  have hrestrict (a : E) : ψ (i a) = φ a := DFunLike.congr_fun hψ a
  have h1 : ψ f = 1 := by simpa [hunit] using (hrestrict e).trans hφ.2
  refine ⟨StrongDual.toWeakDual ψ, hf.mem_stateSpace_iff_norm_eq_one.2
    ⟨hnorm.trans (he.norm_toStrongDual_of_mem_stateSpace hφ), h1⟩, fun a => hrestrict a⟩

/-- **Hahn–Banach extension of states from a unital subspace.** Every state on a submodule
`S : Submodule ℝ E` containing `e` extends to a state on `E`. -/
theorem exists_mem_stateSpace_forall_apply_coe_eq {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}
    (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (heS : e ∈ S) {φ : WeakDual ℝ S}
    (hφ : φ ∈ stateSpace (⟨e, heS⟩ : S)) :
    ∃ ψ ∈ stateSpace e, ∀ x : S, ψ x = φ x :=
  exists_mem_stateSpace_comp_linearIsometry (he.submodule S heS) he S.subtypeₗᵢ rfl hφ

end PullbackAndExtension

/-! ### Kadison's order detection, norm formula, and affine representation -/

section Kadison

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}

/-- **Positivity detection by states.** In an order-unit normed space, `0 ≤ a` iff `0 ≤ φ a` for
every state `φ ∈ stateSpace e`. -/
theorem nonneg_iff_forall_stateSpace (he : IsOrderUnitNorm e) {a : E} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace e, 0 ≤ φ a := by
  refine ⟨fun ha _ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  have := he.orderClosedTopology
  refine (TauCeti.le_iff_forall_monotone_dual_le (x := 0) (y := a)).2 fun f hf => ?_
  rw [map_zero]
  let fpos : E →ₚ[ℝ] ℝ := { toLinearMap := f.toLinearMap, monotone' := hf }
  have hfe : 0 ≤ f e := PositiveLinearMap.apply_nonneg_of_forall_le_norm_smul fpos he.le_norm_smul
  rcases hfe.eq_or_lt with h0 | hpos
  · have habs : |f a| ≤ f e * ‖a‖ :=
      PositiveLinearMap.abs_apply_le_mul_norm fpos he.le_norm_smul a
    have hfa0 : |f a| ≤ 0 := by simpa [← h0] using habs
    exact (abs_nonpos_iff.1 hfa0).symm.le
  · let φ : WeakDual ℝ E := StrongDual.toWeakDual ((f e)⁻¹ • f)
    have hφ : φ ∈ stateSpace e := by
      refine ⟨fun x y hxy => ?_, ?_⟩
      · exact mul_le_mul_of_nonneg_left (hf hxy) (inv_pos.2 hpos).le
      · simp [φ, inv_mul_cancel₀ hpos.ne']
    have hφa : 0 ≤ (f e)⁻¹ * f a := h φ hφ
    exact nonneg_of_mul_nonneg_right hφa (inv_pos.2 hpos)

/-- **Order detection by states.** `a ≤ b` iff `φ a ≤ φ b` for every `φ ∈ stateSpace e`. -/
theorem le_iff_forall_stateSpace (he : IsOrderUnitNorm e) {a b : E} :
    a ≤ b ↔ ∀ φ ∈ stateSpace e, φ a ≤ φ b := by
  rw [← sub_nonneg, he.nonneg_iff_forall_stateSpace]
  simp [sub_nonneg]

/-- **Point separation by states.** `a = b` iff `φ a = φ b` for every `φ ∈ stateSpace e`. -/
theorem eq_iff_forall_stateSpace (he : IsOrderUnitNorm e) {a b : E} :
    a = b ↔ ∀ φ ∈ stateSpace e, φ a = φ b := by
  refine ⟨fun h _ _ => h ▸ rfl, fun h => le_antisymm ?_ ?_⟩
  · exact he.le_iff_forall_stateSpace.2 fun φ hφ => (h φ hφ).le
  · exact he.le_iff_forall_stateSpace.2 fun φ hφ => (h φ hφ).ge

/-- For `r ≥ 0`, `‖a‖ ≤ r` iff `|φ a| ≤ r` for every `φ ∈ stateSpace e`. -/
theorem norm_le_iff_forall_stateSpace (he : IsOrderUnitNorm e) (a : E) {r : ℝ} (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ ∀ φ ∈ stateSpace e, |φ a| ≤ r := by
  rw [he.norm_le_iff a r hr, he.le_iff_forall_stateSpace, he.le_iff_forall_stateSpace]
  refine ⟨fun ⟨h1, h2⟩ φ hφ => abs_le.2 ⟨?_, ?_⟩, fun h => ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩⟩
  · simpa [hφ.2] using h1 φ hφ
  · simpa [hφ.2] using h2 φ hφ
  · simpa [hφ.2] using (abs_le.1 (h φ hφ)).1
  · simpa [hφ.2] using (abs_le.1 (h φ hφ)).2

/-- **Norm detection by states.** For every `a : E`, `‖a‖ = ⨆ φ : stateSpace e, |φ.1 a|`. -/
theorem norm_eq_iSup_stateSpace (he : IsOrderUnitNorm e) (a : E) :
    ‖a‖ = ⨆ φ : stateSpace e, |φ.1 a| := by
  have := he.nonempty_stateSpace
  have hbdd : BddAbove (range fun φ : stateSpace e => |φ.1 a|) :=
    ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact he.abs_apply_le_norm_of_mem_stateSpace φ.2 a⟩
  have hnonneg : 0 ≤ ⨆ φ : stateSpace e, |φ.1 a| :=
    let ⟨φ₀⟩ := he.nonempty_stateSpace
    (abs_nonneg (φ₀.1 a)).trans (le_ciSup hbdd φ₀)
  refine le_antisymm ?_ (ciSup_le fun φ => he.abs_apply_le_norm_of_mem_stateSpace φ.2 a)
  exact (he.norm_le_iff_forall_stateSpace a hnonneg).2 fun φ hφ =>
    le_ciSup (f := fun ψ : stateSpace e => |ψ.1 a|) hbdd ⟨φ, hφ⟩

/-- `NNReal` form of norm detection by states: `‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.1 a‖₊`. -/
theorem nnnorm_eq_iSup_stateSpace (he : IsOrderUnitNorm e) (a : E) :
    ‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.1 a‖₊ := by
  have := he.nonempty_stateSpace
  apply NNReal.eq
  have : BddAbove (range fun φ : stateSpace e => ‖φ.1 a‖₊) :=
    ⟨‖a‖₊, by rintro _ ⟨φ, rfl⟩; exact_mod_cast he.abs_apply_le_norm_of_mem_stateSpace φ.2 a⟩
  rw [coe_nnNorm, he.norm_eq_iSup_stateSpace a, NNReal.coe_iSup]
  refine iSup_congr fun φ => ?_
  simp [Real.norm_eq_abs]

/-- For every `a : E`, some state `φ ∈ stateSpace e` attains `|φ a| = ‖a‖`. -/
theorem exists_mem_stateSpace_abs_apply_eq_norm (he : IsOrderUnitNorm e) (a : E) :
    ∃ φ ∈ stateSpace e, |φ a| = ‖a‖ := by
  obtain ⟨φ, hφ, hmax⟩ := he.isCompact_stateSpace.exists_isMaxOn he.stateSpace_nonempty
    ((eval_continuous a).abs.continuousOn)
  refine ⟨φ, hφ, le_antisymm (he.abs_apply_le_norm_of_mem_stateSpace hφ a) ?_⟩
  exact (he.norm_le_iff_forall_stateSpace a (abs_nonneg (φ a))).2 fun ψ hψ => hmax hψ

/-- **Kadison's evaluation map**: the linear isometry sending `a : E` to the continuous function
`φ ↦ φ.1 a` on `stateSpace e`. -/
noncomputable def kadisonEval (he : IsOrderUnitNorm e) :
    letI := he.compactSpace_stateSpace
    E →ₗᵢ[ℝ] C(stateSpace e, ℝ) :=
  letI := he.compactSpace_stateSpace
  { toFun a := ⟨fun φ => φ.1 a, (eval_continuous a).comp continuous_subtype_val⟩
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    norm_map' a := by
      refine le_antisymm ?_ ?_
      · rw [ContinuousMap.norm_le _ (norm_nonneg a)]
        intro φ
        simpa [Real.norm_eq_abs] using he.abs_apply_le_norm_of_mem_stateSpace φ.2 a
      · obtain ⟨φ, hφ, hφa⟩ := he.exists_mem_stateSpace_abs_apply_eq_norm a
        rw [← hφa, ← Real.norm_eq_abs]
        exact ContinuousMap.norm_coe_le_norm
          (⟨fun ψ : stateSpace e => ψ.1 a, (eval_continuous a).comp continuous_subtype_val⟩ :
            C(stateSpace e, ℝ))
          ⟨φ, hφ⟩ }

/-- `he.kadisonEval a` evaluates at `φ : stateSpace e` as `φ.1 a`. -/
@[simp]
theorem kadisonEval_apply (he : IsOrderUnitNorm e) (a : E) (φ : stateSpace e) :
    he.kadisonEval a φ = φ.1 a :=
  (rfl)

/-- `he.kadisonEval` sends the order unit `e` to the constant function `1`. -/
@[simp]
theorem kadisonEval_unit (he : IsOrderUnitNorm e) : he.kadisonEval e = 1 :=
  ContinuousMap.ext fun φ => φ.2.2

/-- `he.kadisonEval` is an order embedding: `he.kadisonEval a ≤ he.kadisonEval b ↔ a ≤ b`. -/
@[simp]
theorem kadisonEval_le_iff (he : IsOrderUnitNorm e) {a b : E} :
    he.kadisonEval a ≤ he.kadisonEval b ↔ a ≤ b := by
  rw [ContinuousMap.le_def, he.le_iff_forall_stateSpace]
  exact ⟨fun h φ hφ => h ⟨φ, hφ⟩, fun h φ => h φ.1 φ.2⟩

/-- Nonnegativity under `he.kadisonEval`: `0 ≤ he.kadisonEval a ↔ 0 ≤ a`. -/
@[simp]
theorem kadisonEval_nonneg_iff (he : IsOrderUnitNorm e) {a : E} :
    0 ≤ he.kadisonEval a ↔ 0 ≤ a := by
  rw [ContinuousMap.le_def, he.nonneg_iff_forall_stateSpace]
  exact ⟨fun h φ hφ => h ⟨φ, hφ⟩, fun h φ => h φ.1 φ.2⟩

/-- Predicate that a function on `stateSpace e` respects real convex combinations of states. -/
def IsStateAffine {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    {e : E} (F : C(stateSpace e, ℝ)) : Prop :=
  ∀ (φ ψ : stateSpace e) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1),
    F ⟨s • φ.1 + t • ψ.1, convex_stateSpace e φ.2 ψ.2 hs ht hst⟩ = s * F φ + t * F ψ

/-- Every evaluation function `he.kadisonEval a` is affine on `stateSpace e`. -/
theorem isStateAffine_kadisonEval (he : IsOrderUnitNorm e) (a : E) :
    IsStateAffine (he.kadisonEval a) := by
  intro φ ψ s t _ _ _
  simp

/-- The set of continuous affine functions on `stateSpace e` is closed in `C(stateSpace e, ℝ)`. -/
theorem isClosed_setOf_isStateAffine {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] (e : E) :
    IsClosed {F : C(stateSpace e, ℝ) | IsStateAffine F} := by
  simp only [IsStateAffine, Set.ofPred_forall]
  refine isClosed_iInter fun φ => isClosed_iInter fun ψ => isClosed_iInter fun s =>
    isClosed_iInter fun t => isClosed_iInter fun hs => isClosed_iInter fun ht =>
      isClosed_iInter fun hst => isClosed_eq (continuous_eval_const _) ?_
  exact (continuous_const.mul (continuous_eval_const φ)).add
    (continuous_const.mul (continuous_eval_const ψ))

/-- **Kadison's uniform approximation theorem.** Every continuous affine function on `stateSpace e`
can be approximated within any `ε > 0` in supremum norm by `he.kadisonEval a` for some `a : E`. -/
theorem exists_norm_sub_kadisonEval_le (he : IsOrderUnitNorm e) {F : C(stateSpace e, ℝ)}
    (hF : IsStateAffine F) {ε : ℝ} (hε : 0 < ε) :
    letI := he.compactSpace_stateSpace
    ∃ a : E, ‖F - he.kadisonEval a‖ ≤ ε := by
  have := he.compactSpace_stateSpace
  have := he.nonempty_stateSpace
  -- Separate `(0, 0)` from the compact convex set `{(φ - ψ, F φ - F ψ - ε)}` in `WeakDual × ℝ`.
  let g : stateSpace e × stateSpace e → WeakDual ℝ E × ℝ :=
    fun p => (p.1.1 - p.2.1, F p.1 - F p.2 - ε)
  have hg_cont : Continuous g :=
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).prodMk
      (((F.continuous.comp continuous_fst).sub (F.continuous.comp continuous_snd)).sub
        continuous_const)
  let D : Set (WeakDual ℝ E × ℝ) := range g
  have hD_compact : IsCompact D := isCompact_range hg_cont
  have hD_conv : Convex ℝ D := by
    rintro _ ⟨⟨φ₁, ψ₁⟩, rfl⟩ _ ⟨⟨φ₂, ψ₂⟩, rfl⟩ s t hs ht hst
    let φ' : stateSpace e := ⟨s • φ₁.1 + t • φ₂.1, convex_stateSpace e φ₁.2 φ₂.2 hs ht hst⟩
    let ψ' : stateSpace e := ⟨s • ψ₁.1 + t • ψ₂.1, convex_stateSpace e ψ₁.2 ψ₂.2 hs ht hst⟩
    refine ⟨(φ', ψ'), Prod.ext ?_ ?_⟩
    · refine DFunLike.ext _ _ fun x => ?_
      change s * φ₁.1 x + t * φ₂.1 x - (s * ψ₁.1 x + t * ψ₂.1 x) =
        s * (φ₁.1 x - ψ₁.1 x) + t * (φ₂.1 x - ψ₂.1 x)
      ring
    · change F φ' - F ψ' - ε = s * (F φ₁ - F ψ₁ - ε) + t * (F φ₂ - F ψ₂ - ε)
      rw [hF φ₁ φ₂ hs ht hst, hF ψ₁ ψ₂ hs ht hst]
      calc s * F φ₁ + t * F φ₂ - (s * F ψ₁ + t * F ψ₂) - ε
          = s * (F φ₁ - F ψ₁ - ε) + t * (F φ₂ - F ψ₂ - ε) - (1 - (s + t)) * ε := by ring
        _ = s * (F φ₁ - F ψ₁ - ε) + t * (F φ₂ - F ψ₂ - ε) := by rw [hst]; ring
  have h0D : ((0 : WeakDual ℝ E), (0 : ℝ)) ∉ D := by
    rintro ⟨⟨φ, ψ⟩, h⟩
    have h1 : φ = ψ := Subtype.ext (sub_eq_zero.1 (congrArg Prod.fst h))
    have h2 : F φ - F ψ - ε = 0 := congrArg Prod.snd h
    subst h1
    linarith
  obtain ⟨L, u, hu0, huD⟩ := geometric_hahn_banach_point_closed hD_conv hD_compact.isClosed h0D
  have hu_pos : 0 < u := by
    have h00 : ((0 : WeakDual ℝ E), (0 : ℝ)) = 0 := rfl
    rwa [h00, map_zero] at hu0
  obtain ⟨x, hx⟩ := WeakDual.exists_forall_apply_eq_apply
    (L.comp (ContinuousLinearMap.inl ℝ (WeakDual ℝ E) ℝ))
  let c : ℝ := L (0, 1)
  have hL (ξ : WeakDual ℝ E) (r : ℝ) : L (ξ, r) = ξ x + r * c := by
    have hsplit : (ξ, r) = (ξ, 0) + r • ((0 : WeakDual ℝ E), (1 : ℝ)) := by simp
    rw [hsplit, map_add, map_smul, smul_eq_mul]
    exact congrArg (· + r * c) (hx ξ)
  obtain ⟨φ₀⟩ := he.nonempty_stateSpace
  have hc_neg : c < 0 := by
    have hmem : g (φ₀, φ₀) ∈ D := ⟨(φ₀, φ₀), rfl⟩
    have hlt := hu_pos.trans (huD _ hmem)
    have h0x : (0 : WeakDual ℝ E) x = 0 := rfl
    have heval0 : L (g (φ₀, φ₀)) = -ε * c := by simp [g, hL, h0x]
    rw [heval0] at hlt
    nlinarith
  have hnegc : 0 < -c := neg_pos.2 hc_neg
  let a₀ : E := (-c)⁻¹ • x
  have hspread (φ ψ : stateSpace e) : F φ - φ.1 a₀ < F ψ - ψ.1 a₀ + ε := by
    have hlt := hu_pos.trans (huD _ ⟨(φ, ψ), rfl⟩)
    rw [hL] at hlt
    have hx_sub : (φ.1 - ψ.1) x = φ.1 x - ψ.1 x := rfl
    rw [hx_sub] at hlt
    have hdiv : (-c) * (F φ - F ψ - ε) < φ.1 x - ψ.1 x := by linarith
    have hinv := mul_lt_mul_of_pos_left hdiv (inv_pos.2 hnegc)
    rw [inv_mul_cancel_left₀ hnegc.ne'] at hinv
    have ha₀φ : φ.1 a₀ = (-c)⁻¹ * φ.1 x := by simp [a₀]
    have ha₀ψ : ψ.1 a₀ = (-c)⁻¹ * ψ.1 x := by simp [a₀]
    linarith
  obtain ⟨ψ₀, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (F - he.kadisonEval a₀).continuous.continuousOn
  let m : ℝ := F ψ₀ - ψ₀.1 a₀
  refine ⟨a₀ + m • e, (ContinuousMap.norm_le _ hε.le).2 fun φ => ?_⟩
  rw [Real.norm_eq_abs, abs_le]
  have hminφ : m ≤ F φ - φ.1 a₀ := hmin (mem_univ φ)
  have hmaxφ : F φ - φ.1 a₀ < m + ε := hspread φ ψ₀
  have heval : (F - he.kadisonEval (a₀ + m • e)) φ = F φ - φ.1 a₀ - m := by
    change F φ - φ.1 (a₀ + m • e) = F φ - φ.1 a₀ - m
    rw [map_add, map_smul φ.1 m e, smul_eq_mul, φ.2.2]
    ring
  rw [heval]
  exact ⟨by linarith, by linarith⟩

/-- The closure of the range of `he.kadisonEval` in `C(stateSpace e, ℝ)` is the set of continuous
affine functions on `stateSpace e`. -/
theorem closure_range_kadisonEval (he : IsOrderUnitNorm e) :
    closure (range he.kadisonEval) = {F : C(stateSpace e, ℝ) | IsStateAffine F} := by
  have := he.compactSpace_stateSpace
  refine Subset.antisymm (closure_minimal ?_ (isClosed_setOf_isStateAffine e)) fun F hF => ?_
  · rintro _ ⟨a, rfl⟩
    exact he.isStateAffine_kadisonEval a
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨a, ha⟩ := he.exists_norm_sub_kadisonEval_le hF (half_pos hε)
    refine ⟨he.kadisonEval a, ⟨a, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    exact ha.trans_lt (half_lt_self hε)

/-- **Kadison's representation theorem.** When `E` is complete, `he.kadisonEval` maps `E`
isometrically and order-isomorphically onto the space of continuous affine functions on
`stateSpace e`. -/
theorem range_kadisonEval [CompleteSpace E] (he : IsOrderUnitNorm e) :
    range he.kadisonEval = {F : C(stateSpace e, ℝ) | IsStateAffine F} := by
  have := he.compactSpace_stateSpace
  let _ := he.normedAddCommGroup
  rw [← he.closure_range_kadisonEval, IsClosed.closure_eq]
  exact he.kadisonEval.isometry.isUniformInducing.isComplete_range.isClosed

end Kadison

end IsOrderUnitNorm

/-! ### Scalar-line quotient norm and Rieffel's dual-ball identity -/

section ScalarLine

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **scalar line** `ℝ ∙ e` spanned by the order unit `e`, whose quotient `E ⧸ scalarLine e`
carries the quotient seminorm controlling Lip-norm compactness criteria. -/
def scalarLine (e : E) : Submodule ℝ E :=
  Submodule.span ℝ {e}

/-- Membership in `scalarLine e` means being a real scalar multiple of `e`. -/
theorem mem_scalarLine_iff {e a : E} : a ∈ scalarLine e ↔ ∃ c : ℝ, c • e = a :=
  Submodule.mem_span_singleton

/-- The order unit belongs to `scalarLine e`. -/
@[simp]
theorem unit_mem_scalarLine (e : E) : e ∈ scalarLine e :=
  Submodule.mem_span_singleton_self e

/-- A continuous linear functional belongs to the annihilator of `scalarLine e` iff it vanishes at
`e`. -/
theorem mem_orthogonal_scalarLine_iff {e : E} {f : StrongDual ℝ E} :
    f ∈ (scalarLine e).orthogonalBilin (topDualPairing ℝ E).flip ↔ f e = 0 := by
  rw [Submodule.mem_orthogonalBilin]
  refine ⟨fun h => h e (unit_mem_scalarLine e), fun he0 x hx => ?_⟩
  obtain ⟨c, rfl⟩ := mem_scalarLine_iff.1 hx
  simp [he0]

end ScalarLine

namespace IsOrderUnitNorm

section QuotientAndDualBall

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}

/-- The scalar line `scalarLine e` is norm-closed in `E`. -/
theorem isClosed_scalarLine (he : IsOrderUnitNorm e) : IsClosed (scalarLine e : Set E) := by
  let _ := he.normedAddCommGroup
  let ι : ℝ →ₗᵢ[ℝ] E :=
    { toLinearMap := LinearMap.toSpanSingleton ℝ E e
      norm_map' c := by simp [norm_smul, he.norm_eq_one] }
  have hrange : (scalarLine e : Set E) = range ι := by
    ext a
    simp [scalarLine, Submodule.mem_span_singleton, ι]
  rw [hrange]
  exact ι.isometry.isUniformInducing.isComplete_range.isClosed

/-- Minimum value of `φ ↦ φ a` over `stateSpace e`. -/
noncomputable def stateMin (he : IsOrderUnitNorm e) (a : E) : ℝ :=
  let _ := he
  sInf ((fun φ : WeakDual ℝ E => φ a) '' stateSpace e)

/-- Maximum value of `φ ↦ φ a` over `stateSpace e`. -/
noncomputable def stateMax (he : IsOrderUnitNorm e) (a : E) : ℝ :=
  let _ := he
  sSup ((fun φ : WeakDual ℝ E => φ a) '' stateSpace e)

variable [IsOrderedAddMonoid E]

/-- Every state value `φ a` is bounded below by `he.stateMin a`. -/
theorem stateMin_le_apply (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e)
    (a : E) : he.stateMin a ≤ φ a :=
  csInf_le (he.isCompact_stateSpace.image (eval_continuous a)).bddBelow ⟨φ, hφ, rfl⟩

/-- Every state value `φ a` is bounded above by `he.stateMax a`. -/
theorem apply_le_stateMax (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e)
    (a : E) : φ a ≤ he.stateMax a :=
  le_csSup (he.isCompact_stateSpace.image (eval_continuous a)).bddAbove ⟨φ, hφ, rfl⟩

variable [PosSMulMono ℝ E]

/-- Some state attains `he.stateMin a`. -/
theorem exists_mem_stateSpace_eq_stateMin (he : IsOrderUnitNorm e) (a : E) :
    ∃ φ ∈ stateSpace e, φ a = he.stateMin a :=
  (he.isCompact_stateSpace.image (eval_continuous a)).sInf_mem
    (he.stateSpace_nonempty.image _)

/-- Some state attains `he.stateMax a`. -/
theorem exists_mem_stateSpace_eq_stateMax (he : IsOrderUnitNorm e) (a : E) :
    ∃ φ ∈ stateSpace e, φ a = he.stateMax a :=
  (he.isCompact_stateSpace.image (eval_continuous a)).sSup_mem
    (he.stateSpace_nonempty.image _)

/-- `he.stateMin a ≤ he.stateMax a` for every `a : E`. -/
theorem stateMin_le_stateMax (he : IsOrderUnitNorm e) (a : E) :
    he.stateMin a ≤ he.stateMax a := by
  obtain ⟨φ, hφ⟩ := he.stateSpace_nonempty
  exact (he.stateMin_le_apply hφ a).trans (he.apply_le_stateMax hφ a)

/-- Order lower bound `he.stateMin a • e ≤ a`. -/
theorem stateMin_smul_le (he : IsOrderUnitNorm e) (a : E) : he.stateMin a • e ≤ a :=
  he.le_iff_forall_stateSpace.2 fun φ hφ => by simpa [hφ.2] using he.stateMin_le_apply hφ a

/-- Order upper bound `a ≤ he.stateMax a • e`. -/
theorem le_stateMax_smul (he : IsOrderUnitNorm e) (a : E) : a ≤ he.stateMax a • e :=
  he.le_iff_forall_stateSpace.2 fun φ hφ => by simpa [hφ.2] using he.apply_le_stateMax hφ a

/-- Centering `a` by its state-midpoint scalar multiple achieves norm equal to half the state
spread `(he.stateMax a - he.stateMin a) / 2`. -/
theorem norm_sub_midpoint_smul (he : IsOrderUnitNorm e) (a : E) :
    ‖a - ((he.stateMax a + he.stateMin a) / 2) • e‖ = (he.stateMax a - he.stateMin a) / 2 := by
  let mid := (he.stateMax a + he.stateMin a) / 2
  let rad := (he.stateMax a - he.stateMin a) / 2
  have hrad : 0 ≤ rad := by
    have := he.stateMin_le_stateMax a
    dsimp only [rad]
    linarith
  refine le_antisymm ?_ ?_
  · refine (he.norm_le_iff_forall_stateSpace _ hrad).2 fun φ hφ => abs_le.2 ?_
    have hlo := he.stateMin_le_apply hφ a
    have hhi := he.apply_le_stateMax hφ a
    have hval : φ (a - mid • e) = φ a - mid := by simp [hφ.2]
    rw [hval]
    dsimp only [mid, rad]
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨φ, hφ, hφmax⟩ := he.exists_mem_stateSpace_eq_stateMax a
    have hval : φ (a - mid • e) = rad := by
      simp [hφ.2, hφmax, mid, rad]
      ring
    calc rad = φ (a - mid • e) := hval.symm
      _ ≤ |φ (a - mid • e)| := le_abs_self _
      _ ≤ ‖a - mid • e‖ := he.abs_apply_le_norm_of_mem_stateSpace hφ _

/-- Every scalar translate `a - c • e` has norm at least `(he.stateMax a - he.stateMin a) / 2`. -/
theorem half_stateSpread_le_norm_sub_smul (he : IsOrderUnitNorm e) (a : E) (c : ℝ) :
    (he.stateMax a - he.stateMin a) / 2 ≤ ‖a - c • e‖ := by
  obtain ⟨φ₁, hφ₁, hmax⟩ := he.exists_mem_stateSpace_eq_stateMax a
  obtain ⟨φ₂, hφ₂, hmin⟩ := he.exists_mem_stateSpace_eq_stateMin a
  have h1 : he.stateMax a - c ≤ ‖a - c • e‖ := by
    calc he.stateMax a - c = φ₁ (a - c • e) := by simp [hφ₁.2, hmax]
      _ ≤ |φ₁ (a - c • e)| := le_abs_self _
      _ ≤ ‖a - c • e‖ := he.abs_apply_le_norm_of_mem_stateSpace hφ₁ _
  have h2 : c - he.stateMin a ≤ ‖a - c • e‖ := by
    calc c - he.stateMin a = -φ₂ (a - c • e) := by simp [hφ₂.2, hmin]
      _ ≤ |φ₂ (a - c • e)| := neg_le_abs _
      _ ≤ ‖a - c • e‖ := he.abs_apply_le_norm_of_mem_stateSpace hφ₂ _
  linarith

/-- **Scalar-line quotient norm formula.** On `E ⧸ scalarLine e`, the quotient norm of `a` equals
half its spread over `stateSpace e`, `(he.stateMax a - he.stateMin a) / 2`, and is attained at the
midpoint scalar multiple of `e`. -/
theorem norm_quotient_scalarLine_eq (he : IsOrderUnitNorm e) (a : E) :
    ‖(Submodule.Quotient.mk a : E ⧸ scalarLine e)‖ = (he.stateMax a - he.stateMin a) / 2 := by
  set mid := (he.stateMax a + he.stateMin a) / 2
  refine le_antisymm ?_ ?_
  · have hmk : (Submodule.Quotient.mk (a - mid • e) : E ⧸ scalarLine e) =
        Submodule.Quotient.mk a := by
      rw [Submodule.Quotient.mk_sub,
        (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem _ mid (unit_mem_scalarLine e)),
        sub_zero]
    rw [← hmk, ← he.norm_sub_midpoint_smul a]
    exact Submodule.Quotient.norm_mk_le (scalarLine e) (a - mid • e)
  · refine QuotientAddGroup.le_norm_iff.2 fun y hy => ?_
    have hsub : a - y ∈ scalarLine e :=
      (Submodule.Quotient.eq (scalarLine e)).1 hy.symm
    obtain ⟨c, hc⟩ := mem_scalarLine_iff.1 hsub
    have hy_eq : y = a - c • e := by
      rw [hc]
      abel
    rw [hy_eq]
    exact he.half_stateSpread_le_norm_sub_smul a c

/-- Equivalently, `‖(Submodule.Quotient.mk a : E ⧸ scalarLine e)‖` is half the supremum of
`|φ a - ψ a|` over pairs of states `φ, ψ ∈ stateSpace e`. -/
theorem two_mul_norm_quotient_scalarLine_eq_iSup (he : IsOrderUnitNorm e) (a : E) :
    2 * ‖(Submodule.Quotient.mk a : E ⧸ scalarLine e)‖ =
      ⨆ p : stateSpace e × stateSpace e, |p.1.1 a - p.2.1 a| := by
  have := he.nonempty_stateSpace
  rw [he.norm_quotient_scalarLine_eq a, mul_div_cancel₀ _ two_ne_zero]
  have hbdd : BddAbove (range fun p : stateSpace e × stateSpace e => |p.1.1 a - p.2.1 a|) := by
    refine ⟨he.stateMax a - he.stateMin a, ?_⟩
    rintro _ ⟨⟨φ, ψ⟩, rfl⟩
    exact abs_sub_le_iff.2
      ⟨by linarith [he.apply_le_stateMax φ.2 a, he.stateMin_le_apply ψ.2 a],
       by linarith [he.apply_le_stateMax ψ.2 a, he.stateMin_le_apply φ.2 a]⟩
  refine le_antisymm ?_ (ciSup_le fun p => abs_sub_le_iff.2
    ⟨by linarith [he.apply_le_stateMax p.1.2 a, he.stateMin_le_apply p.2.2 a],
     by linarith [he.apply_le_stateMax p.2.2 a, he.stateMin_le_apply p.1.2 a]⟩)
  obtain ⟨φ, hφ, hmax⟩ := he.exists_mem_stateSpace_eq_stateMax a
  obtain ⟨ψ, hψ, hmin⟩ := he.exists_mem_stateSpace_eq_stateMin a
  calc he.stateMax a - he.stateMin a
      = φ a - ψ a := by rw [hmax, hmin]
    _ ≤ |φ a - ψ a| := le_abs_self _
    _ ≤ ⨆ p : stateSpace e × stateSpace e, |p.1.1 a - p.2.1 a| :=
        le_ciSup (f := fun p : stateSpace e × stateSpace e => |p.1.1 a - p.2.1 a|) hbdd
          (⟨φ, hφ⟩, ⟨ψ, hψ⟩)

/-- **Rieffel's dual-ball identity.** On an order-unit normed space, the centered dual ball of
radius `2` equals the set of differences of two states:
`{λ : StrongDual ℝ E | λ e = 0 ∧ ‖λ‖ ≤ 2} =`
`{toStrongDual φ - toStrongDual ψ | (φ ∈ stateSpace e) (ψ ∈ stateSpace e)}`.
No completeness of `E` is required. -/
theorem centeredDualBall_eq_sub_stateSpace (he : IsOrderUnitNorm e) :
    {l : StrongDual ℝ E | l e = 0 ∧ ‖l‖ ≤ 2} =
      {l | ∃ φ ∈ stateSpace e, ∃ ψ ∈ stateSpace e, toStrongDual φ - toStrongDual ψ = l} := by
  have := he.compactSpace_stateSpace
  have := he.nonempty_stateSpace
  let _ := he.normedAddCommGroup
  ext l
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hle0, hlnorm⟩
    -- Extend `l` norm-preservingly along `he.kadisonEval` to `C(stateSpace e, ℝ)`.
    obtain ⟨Λ, hΛext, hΛnorm⟩ := he.kadisonEval.exists_extension_norm_eq l
    have hΛeval (a : E) : Λ (he.kadisonEval a) = l a := DFunLike.congr_fun hΛext a
    have hΛ1 : Λ 1 = 0 := by simpa [he.kadisonEval_unit] using (hΛeval e).trans hle0
    -- Transfer `Λ` to `C_c(stateSpace e, ℝ)` and decompose into positive and negative parts.
    let Λc : C_c(stateSpace e, ℝ) →ₗ[ℝ] ℝ :=
      { toFun h := Λ h.toContinuousMap
        map_add' h₁ h₂ := map_add Λ h₁.toContinuousMap h₂.toContinuousMap
        map_smul' c h := map_smul Λ c h.toContinuousMap }
    have hΛbdd : ∀ f : C_c(stateSpace e, ℝ), BddAbove (Λc '' Icc 0 f) := fun f => by
      refine ⟨‖Λ‖ * ‖f.toContinuousMap‖, ?_⟩
      rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
      have hgnorm : ‖g.toContinuousMap‖ ≤ ‖f.toContinuousMap‖ := by
        rw [ContinuousMap.norm_le _ (norm_nonneg _)]
        intro φ
        rw [Real.norm_eq_abs, CompactlySupportedContinuousMap.coe_toContinuousMap,
          abs_of_nonneg (hg0 φ)]
        exact (hgf φ).trans (le_trans (le_abs_self _) (by
          simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f.toContinuousMap φ))
      calc Λc g ≤ |Λ g.toContinuousMap| := le_abs_self _
        _ = ‖Λ g.toContinuousMap‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖Λ‖ * ‖g.toContinuousMap‖ := Λ.le_opNorm _
        _ ≤ ‖Λ‖ * ‖f.toContinuousMap‖ := mul_le_mul_of_nonneg_left hgnorm (norm_nonneg Λ)
    let P := TauCeti.RealRMK.posPart Λc hΛbdd
    let N := TauCeti.RealRMK.negPart Λc hΛbdd
    let oneC : C_c(stateSpace e, ℝ) := CompactlySupportedContinuousMap.continuousMapEquiv 1
    have honeC_nonneg : 0 ≤ oneC := fun _ => zero_le_one
    have hPN_diff : P oneC - N oneC = 0 :=
      (TauCeti.RealRMK.posPart_sub_negPart_apply hΛbdd oneC).trans hΛ1
    have hPN_eq : N oneC = P oneC := by linarith
    -- Bound `P 1 + N 1 ≤ ‖Λ‖ ≤ 2` by pairing arbitrary `g₁, g₂ ∈ [0, 1]`.
    have hPN_sum : P oneC + N oneC ≤ 2 := by
      rw [← le_sub_iff_add_le]
      refine TauCeti.RealRMK.posPart_apply_le hΛbdd honeC_nonneg fun g₁ hg₁0 hg₁1 => ?_
      rw [le_sub_comm]
      refine TauCeti.RealRMK.negPart_apply_le hΛbdd honeC_nonneg fun g₂ hg₂0 hg₂1 => ?_
      have hdiff_norm : ‖g₁.toContinuousMap - g₂.toContinuousMap‖ ≤ 1 := by
        rw [ContinuousMap.norm_le _ zero_le_one]
        intro φ
        rw [Real.norm_eq_abs, ContinuousMap.sub_apply, abs_le]
        simp only [CompactlySupportedContinuousMap.coe_toContinuousMap]
        have h10 : 0 ≤ g₁ φ := hg₁0 φ
        have h11 : g₁ φ ≤ 1 := hg₁1 φ
        have h20 : 0 ≤ g₂ φ := hg₂0 φ
        have h21 : g₂ φ ≤ 1 := hg₂1 φ
        exact ⟨by linarith, by linarith⟩
      have hval : -Λc g₂ ≤ 2 - Λc g₁ := by
        have hsub : Λc g₁ - Λc g₂ = Λ (g₁.toContinuousMap - g₂.toContinuousMap) :=
          (map_sub Λ g₁.toContinuousMap g₂.toContinuousMap).symm
        have hle : Λ (g₁.toContinuousMap - g₂.toContinuousMap) ≤ 2 := by
          calc Λ (g₁.toContinuousMap - g₂.toContinuousMap)
              ≤ ‖Λ (g₁.toContinuousMap - g₂.toContinuousMap)‖ := Real.le_norm_self _
            _ ≤ ‖Λ‖ * ‖g₁.toContinuousMap - g₂.toContinuousMap‖ := Λ.le_opNorm _
            _ ≤ ‖Λ‖ * 1 := mul_le_mul_of_nonneg_left hdiff_norm (norm_nonneg Λ)
            _ = ‖l‖ := by rw [mul_one, hΛnorm]
            _ ≤ 2 := hlnorm
        linarith
      exact hval
    have ht_le_one : P oneC ≤ 1 := by linarith
    -- Pull `P` and `N` back to `E` and pad both by `(1 - P 1) • ω` for any state `ω`.
    let pull : E →ₚ[ℝ] C_c(stateSpace e, ℝ) :=
      PositiveLinearMap.mk₀
        { toFun a := CompactlySupportedContinuousMap.continuousMapEquiv (he.kadisonEval a)
          map_add' a b := by ext φ; simp
          map_smul' c a := by ext φ; simp }
        fun a ha φ => (he.kadisonEval_nonneg_iff.2 ha) φ
    let p : WeakDual ℝ E := he.positiveLinearMapToWeakDual (P.comp pull)
    let n : WeakDual ℝ E := he.positiveLinearMapToWeakDual (N.comp pull)
    obtain ⟨ω, hω⟩ := he.stateSpace_nonempty
    let φ : WeakDual ℝ E := p + (1 - P oneC) • ω
    let ψ : WeakDual ℝ E := n + (1 - P oneC) • ω
    have hpad_nonneg : 0 ≤ 1 - P oneC := sub_nonneg.2 ht_le_one
    have hpe : p e = P oneC := by
      change P (CompactlySupportedContinuousMap.continuousMapEquiv (he.kadisonEval e)) = P oneC
      rw [he.kadisonEval_unit]
    have hne : n e = P oneC := by
      change N (CompactlySupportedContinuousMap.continuousMapEquiv (he.kadisonEval e)) = P oneC
      rw [he.kadisonEval_unit, hPN_eq]
    have hφ : φ ∈ stateSpace e := by
      refine mem_stateSpace_iff_map_nonneg.2 ⟨fun a ha => ?_, ?_⟩
      · exact add_nonneg (map_nonneg (P.comp pull) ha)
          (mul_nonneg hpad_nonneg (map_nonneg_of_mem_stateSpace hω ha))
      · simp [φ, hpe, hω.2]
    have hψ : ψ ∈ stateSpace e := by
      refine mem_stateSpace_iff_map_nonneg.2 ⟨fun a ha => ?_, ?_⟩
      · exact add_nonneg (map_nonneg (N.comp pull) ha)
          (mul_nonneg hpad_nonneg (map_nonneg_of_mem_stateSpace hω ha))
      · simp [ψ, hne, hω.2]
    refine ⟨φ, hφ, ψ, hψ, ?_⟩
    ext a
    have hsub : p a - n a = l a := by
      change P (pull a) - N (pull a) = l a
      exact (TauCeti.RealRMK.posPart_sub_negPart_apply hΛbdd (pull a)).trans (hΛeval a)
    calc (toStrongDual φ - toStrongDual ψ) a
        = (p a + (1 - P oneC) * ω a) - (n a + (1 - P oneC) * ω a) := rfl
      _ = p a - n a := by ring
      _ = l a := hsub
  · rintro ⟨φ, hφ, ψ, hψ, rfl⟩
    refine ⟨by simp [hφ.2, hψ.2], ?_⟩
    calc ‖toStrongDual φ - toStrongDual ψ‖
        ≤ ‖toStrongDual φ‖ + ‖toStrongDual ψ‖ := norm_sub_le _ _
      _ = 2 := by rw [he.norm_toStrongDual_of_mem_stateSpace hφ,
          he.norm_toStrongDual_of_mem_stateSpace hψ]; norm_num

/-- Quotient-dual form of **Rieffel's dual-ball identity**: a functional
`μ : StrongDual ℝ (E ⧸ scalarLine e)` has operator norm at most `2` iff it is induced by the
difference of two states on `E`. -/
theorem norm_quotientDual_le_two_iff_exists_stateSpace (he : IsOrderUnitNorm e)
    (μ : StrongDual ℝ (E ⧸ scalarLine e)) :
    ‖μ‖ ≤ 2 ↔ ∃ φ ∈ stateSpace e, ∃ ψ ∈ stateSpace e,
      ∀ a : E, μ (Submodule.Quotient.mk a) = φ a - ψ a := by
  let l := ((scalarLine e).quotientDualEquivAnnihilator μ : StrongDual ℝ E)
  have hlnorm : ‖l‖ = ‖μ‖ := (scalarLine e).quotientDualEquivAnnihilator.norm_map μ
  have hle0 : l e = 0 :=
    mem_orthogonal_scalarLine_iff.1 ((scalarLine e).quotientDualEquivAnnihilator μ).2
  constructor
  · intro hμ
    have hl_mem : l ∈ {l : StrongDual ℝ E | l e = 0 ∧ ‖l‖ ≤ 2} := ⟨hle0, hlnorm.trans_le hμ⟩
    rw [he.centeredDualBall_eq_sub_stateSpace] at hl_mem
    obtain ⟨φ, hφ, ψ, hψ, hl_eq⟩ := hl_mem
    refine ⟨φ, hφ, ψ, hψ, fun a => ?_⟩
    have := DFunLike.congr_fun hl_eq a
    simpa [l] using this.symm
  · rintro ⟨φ, hφ, ψ, hψ, hμ_eq⟩
    have hl_eq : toStrongDual φ - toStrongDual ψ = l := by
      ext a
      simpa [l] using (hμ_eq a).symm
    have hl_mem : l ∈ {l : StrongDual ℝ E | l e = 0 ∧ ‖l‖ ≤ 2} := by
      rw [he.centeredDualBall_eq_sub_stateSpace]
      exact ⟨φ, hφ, ψ, hψ, hl_eq⟩
    exact hlnorm ▸ hl_mem.2

end QuotientAndDualBall

end IsOrderUnitNorm

end TauCeti.OrderUnit
