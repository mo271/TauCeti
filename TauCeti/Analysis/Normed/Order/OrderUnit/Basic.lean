/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Order.Basic

/-!
# Archimedean order-unit spaces and the order-unit norm

An **Archimedean order-unit space** is a real partially ordered vector space `E` whose order is
compatible with addition and with multiplication by nonnegative real scalars, equipped with a
nonzero element `e` such that every `a : E` lies in some interval `[-r • e, r • e]` (`r > 0`) and
such that `(∀ ε > 0, a ≤ ε • e) → a ≤ 0`. Its **order-unit norm** is

```text
orderUnitNorm e a = sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}.
```

This file constructs the norm induced by an Archimedean order unit, introduces the compatibility
predicate `TauCeti.OrderUnit.IsOrderUnitNorm e` on spaces already carrying a norm and a partial
order (`‖e‖ = 1` and `‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for `0 ≤ r`), and develops the resulting
cone geometry and permanence constructions.

## Main definitions and results

* `TauCeti.OrderUnit.IsArchimedeanOrderUnit e`: `e ≠ 0`, order-unit domination, and the Archimedean
  implication `(∀ ε > 0, a ≤ ε • e) → a ≤ 0`.
* `TauCeti.OrderUnit.orderUnitNorm e a`: the infimum `sInf {r ≥ 0 | -r • e ≤ a ∧ a ≤ r • e}`, shown
  to satisfy `orderUnitNorm_le_iff`, definiteness, `orderUnitNorm e e = 1`, subadditivity, and
  absolute homogeneity; packaged as `IsArchimedeanOrderUnit.normedAddCommGroup` and
  `IsArchimedeanOrderUnit.normedSpace`, which satisfy `IsOrderUnitNorm e`.
* `TauCeti.OrderUnit.IsOrderUnitNorm e`: compatibility of a given norm and partial order with `e`.
  Recovers the order from the norm via `0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`, proves that the positive cone
  is norm closed with `e` in its interior, and deduces the Archimedean property.
* Permanence under unital real subspaces (`IsOrderUnitNorm.submodule`), binary and finite products
  with the supremum norm (`IsOrderUnitNorm.prod`, `IsOrderUnitNorm.pi`), unital linear order
  embeddings and equivalences, which are automatically isometric
  (`LinearMap.norm_map_of_isOrderUnitNorm`, `LinearEquiv.toLinearIsometryEquivOfOrderUnit`), and
  the norm completion `UniformSpace.Completion E` equipped with the norm closure of the positive
  cone (`IsOrderUnitNorm.completionPartialOrder`, `IsOrderUnitNorm.completion`).
* Concrete instances for `ℝ`, finite function spaces `ι → ℝ`, bounded continuous functions `K →ᵇ ℝ`,
  and `C(K, ℝ)` on nonempty compact spaces.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. 7 (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, §1.
* M. A. Rieffel, *Gromov–Hausdorff distance for quantum metric spaces*, Mem. Amer. Math. Soc. 168
  (2004), no. 796.
-/

public section

noncomputable section

open Set Metric
open scoped BoundedContinuousFunction

namespace TauCeti.OrderUnit

section Archimedean

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]

/-- An **Archimedean order unit** in a partially ordered real vector space: a nonzero element `e`
whose positive scalar multiples bound every element above and below, and for which
`∀ ε > 0, a ≤ ε • e` implies `a ≤ 0`. -/
structure IsArchimedeanOrderUnit (e : E) : Prop where
  ne_zero : e ≠ 0
  exists_bounds : ∀ a : E, ∃ r : ℝ, 0 < r ∧ -r • e ≤ a ∧ a ≤ r • e
  archimedean : ∀ a : E, (∀ ε : ℝ, 0 < ε → a ≤ ε • e) → a ≤ 0

/-- The **order-unit norm** `‖a‖ = inf {r ≥ 0 : -r • e ≤ a ∧ a ≤ r • e}` associated with an element
`e : E`. -/
def orderUnitNorm (e : E) (a : E) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}

theorem orderUnitNorm_def (e : E) (a : E) :
    orderUnitNorm e a = sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} :=
  (rfl)

/-- The order-unit norm is nonnegative. -/
theorem orderUnitNorm_nonneg (e : E) (a : E) : 0 ≤ orderUnitNorm e a :=
  Real.sInf_nonneg fun _ hr => hr.1

namespace IsArchimedeanOrderUnit

variable {e : E}

theorem nontrivial (he : IsArchimedeanOrderUnit e) : Nontrivial E :=
  ⟨⟨e, 0, he.ne_zero⟩⟩

/-- Every Archimedean order unit is nonnegative: bounding `0` in `[-r • e, r • e]` with `r > 0`
gives `0 ≤ r • e`, hence `0 ≤ e`. -/
theorem nonneg [PosSMulMono ℝ E] (he : IsArchimedeanOrderUnit e) : 0 ≤ e := by
  obtain ⟨r, hr, -, h0⟩ := he.exists_bounds 0
  have := smul_le_smul_of_nonneg_left h0 (inv_nonneg.mpr hr.le)
  simpa [smul_smul, inv_mul_cancel₀ hr.ne'] using this

theorem le_iff_forall_pos_le_add [IsOrderedAddMonoid E] [PosSMulMono ℝ E]
    (he : IsArchimedeanOrderUnit e) {a b : E} : a ≤ b ↔ ∀ ε : ℝ, 0 < ε → a ≤ b + ε • e := by
  refine ⟨fun hab ε hε => ?_, fun h => sub_nonpos.mp <| he.archimedean (a - b) fun ε hε => ?_⟩
  · obtain ⟨r, hr, -, h0⟩ := he.exists_bounds 0
    have he0 : 0 ≤ ε • e := by
      have : (0 : E) ≤ (ε * r⁻¹) • (r • e) :=
        smul_nonneg (mul_nonneg hε.le (inv_nonneg.mpr hr.le)) h0
      simpa [smul_smul, div_mul_cancel₀ ε hr.ne', ← div_eq_mul_inv] using this
    exact hab.trans (le_add_of_nonneg_right he0)
  · exact sub_le_iff_le_add'.mpr (h ε hε)

private theorem boundsSet_nonempty (he : IsArchimedeanOrderUnit e) (a : E) :
    {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}.Nonempty := by
  obtain ⟨r, hr, h1, h2⟩ := he.exists_bounds a
  exact ⟨r, hr.le, h1, h2⟩

private theorem bddBelow_boundsSet (e : E) (a : E) :
    BddBelow {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} :=
  ⟨0, fun _ hr => hr.1⟩

variable [IsOrderedAddMonoid E] [PosSMulMono ℝ E]

/-- **Closed-interval characterization of the order-unit norm.** For `0 ≤ r`, we have
`orderUnitNorm e a ≤ r` if and only if `-r • e ≤ a ∧ a ≤ r • e`. The forward implication uses the
Archimedean axiom to pass to the infimum. -/
theorem orderUnitNorm_le_iff (he : IsArchimedeanOrderUnit e) {a : E} {r : ℝ} (hr : 0 ≤ r) :
    orderUnitNorm e a ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e := by
  refine ⟨fun h => ?_, fun h => csInf_le (bddBelow_boundsSet e a) ⟨hr, h⟩⟩
  have hupper : a ≤ r • e := by
    rw [he.le_iff_forall_pos_le_add]
    intro ε hε
    obtain ⟨s, ⟨-, -, has⟩, hsr⟩ :=
      (csInf_lt_iff (bddBelow_boundsSet e a) (he.boundsSet_nonempty a)).mp
        (lt_add_of_le_of_pos h hε)
    refine has.trans ?_
    rw [← add_smul]
    exact smul_le_smul_of_nonneg_right hsr.le he.nonneg
  have hlower : -r • e ≤ a := by
    rw [neg_smul, neg_le]
    rw [he.le_iff_forall_pos_le_add]
    intro ε hε
    obtain ⟨s, ⟨-, hsa, -⟩, hsr⟩ :=
      (csInf_lt_iff (bddBelow_boundsSet e a) (he.boundsSet_nonempty a)).mp
        (lt_add_of_le_of_pos h hε)
    have hna : -a ≤ s • e := neg_le.mp (by simpa [neg_smul] using hsa)
    refine hna.trans ?_
    rw [← add_smul]
    exact smul_le_smul_of_nonneg_right hsr.le he.nonneg
  exact ⟨hlower, hupper⟩

theorem neg_orderUnitNorm_smul_le (he : IsArchimedeanOrderUnit e) (a : E) :
    -(orderUnitNorm e a) • e ≤ a :=
  ((he.orderUnitNorm_le_iff (orderUnitNorm_nonneg e a)).mp le_rfl).1

theorem le_orderUnitNorm_smul (he : IsArchimedeanOrderUnit e) (a : E) :
    a ≤ (orderUnitNorm e a) • e :=
  ((he.orderUnitNorm_le_iff (orderUnitNorm_nonneg e a)).mp le_rfl).2

/-- Definiteness of the order-unit norm, from the Archimedean closed-interval characterization at
`r = 0`. -/
@[simp]
theorem orderUnitNorm_eq_zero_iff (he : IsArchimedeanOrderUnit e) {a : E} :
    orderUnitNorm e a = 0 ↔ a = 0 := by
  rw [le_antisymm_iff, and_iff_left (orderUnitNorm_nonneg e a), he.orderUnitNorm_le_iff le_rfl]
  exact ⟨fun ⟨h1, h2⟩ => le_antisymm (by simpa using h2) (by simpa using h1), fun h => by simp [h]⟩

@[simp]
theorem orderUnitNorm_zero (he : IsArchimedeanOrderUnit e) : orderUnitNorm e 0 = 0 :=
  he.orderUnitNorm_eq_zero_iff.mpr rfl

/-- The order-unit norm of the order unit itself is `1`. -/
@[simp]
theorem orderUnitNorm_self (he : IsArchimedeanOrderUnit e) : orderUnitNorm e e = 1 := by
  apply le_antisymm
  · rw [he.orderUnitNorm_le_iff zero_le_one]
    exact ⟨by simpa using (neg_nonpos.mpr he.nonneg).trans he.nonneg, by simp⟩
  · by_contra! hlt
    have hle : e ≤ (orderUnitNorm e e) • e := he.le_orderUnitNorm_smul e
    have hsub : (1 - orderUnitNorm e e) • e ≤ 0 := by
      simpa [sub_smul] using sub_nonpos.mpr hle
    have hpos : 0 < 1 - orderUnitNorm e e := sub_pos.mpr hlt
    have he0 : e ≤ 0 := by
      simpa [smul_smul, inv_mul_cancel₀ hpos.ne'] using
        smul_le_smul_of_nonneg_left hsub (inv_nonneg.mpr hpos.le)
    exact he.ne_zero (le_antisymm he0 he.nonneg)

@[simp]
theorem orderUnitNorm_neg (he : IsArchimedeanOrderUnit e) (a : E) :
    orderUnitNorm e (-a) = orderUnitNorm e a := by
  have haux (x : E) : orderUnitNorm e (-x) ≤ orderUnitNorm e x := by
    rw [he.orderUnitNorm_le_iff (orderUnitNorm_nonneg e x)]
    exact ⟨by simpa [neg_smul] using neg_le_neg (he.le_orderUnitNorm_smul x),
      by simpa [neg_smul] using neg_le_neg (he.neg_orderUnitNorm_smul_le x)⟩
  exact le_antisymm (haux a) (by simpa using haux (-a))

/-- Triangle inequality for the order-unit norm. -/
theorem orderUnitNorm_add_le (he : IsArchimedeanOrderUnit e) (a b : E) :
    orderUnitNorm e (a + b) ≤ orderUnitNorm e a + orderUnitNorm e b := by
  rw [he.orderUnitNorm_le_iff (add_nonneg (orderUnitNorm_nonneg e a) (orderUnitNorm_nonneg e b))]
  refine ⟨?_, ?_⟩
  · calc
      -(orderUnitNorm e a + orderUnitNorm e b) • e
        = -(orderUnitNorm e a) • e + -(orderUnitNorm e b) • e := by rw [neg_add_rev, add_smul]; abel
      _ ≤ a + b := add_le_add (he.neg_orderUnitNorm_smul_le a) (he.neg_orderUnitNorm_smul_le b)
  · calc
      a + b ≤ (orderUnitNorm e a) • e + (orderUnitNorm e b) • e :=
        add_le_add (he.le_orderUnitNorm_smul a) (he.le_orderUnitNorm_smul b)
      _ = (orderUnitNorm e a + orderUnitNorm e b) • e := (add_smul _ _ _).symm

/-- Absolute homogeneity of the order-unit norm. -/
theorem orderUnitNorm_smul (he : IsArchimedeanOrderUnit e) (c : ℝ) (a : E) :
    orderUnitNorm e (c • a) = |c| * orderUnitNorm e a := by
  have hpos_smul {t : ℝ} (ht : 0 < t) (x : E) :
      orderUnitNorm e (t • x) ≤ t * orderUnitNorm e x := by
    rw [he.orderUnitNorm_le_iff (mul_nonneg ht.le (orderUnitNorm_nonneg e x))]
    refine ⟨?_, ?_⟩
    · simpa [neg_mul, smul_smul] using
        smul_le_smul_of_nonneg_left (he.neg_orderUnitNorm_smul_le x) ht.le
    · simpa [smul_smul] using smul_le_smul_of_nonneg_left (he.le_orderUnitNorm_smul x) ht.le
  have hpos_eq {t : ℝ} (ht : 0 < t) (x : E) :
      orderUnitNorm e (t • x) = t * orderUnitNorm e x := by
    refine le_antisymm (hpos_smul ht x) ?_
    have hinv := hpos_smul (inv_pos.mpr ht) (t • x)
    rw [inv_smul_smul₀ ht.ne'] at hinv
    simpa [← mul_assoc, mul_inv_cancel₀ ht.ne'] using mul_le_mul_of_nonneg_left hinv ht.le
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · calc
      orderUnitNorm e (c • a) = orderUnitNorm e ((-c) • (-a)) := by rw [neg_smul_neg]
      _ = (-c) * orderUnitNorm e (-a) := hpos_eq (neg_pos.mpr hc) (-a)
      _ = |c| * orderUnitNorm e a := by rw [abs_of_neg hc, he.orderUnitNorm_neg]
  · simp [he.orderUnitNorm_zero]
  · rw [abs_of_pos hc, hpos_eq hc a]

/-- The `Norm` structure given by `orderUnitNorm e`. Defined as a reducible non-instance (`abbrev`)
because `e` is an explicit choice of unit. -/
abbrev norm (e : E) : Norm E :=
  ⟨orderUnitNorm e⟩

/-- The `NormedSpace.Core ℝ E` witness for `orderUnitNorm e`. -/
theorem normedSpaceCore (he : IsArchimedeanOrderUnit e) :
    letI := norm e
    NormedSpace.Core ℝ E :=
  let := norm e
  { norm_nonneg := orderUnitNorm_nonneg e
    norm_smul := fun c x =>
      (he.orderUnitNorm_smul c x).trans (congrArg (· * orderUnitNorm e x) (Real.norm_eq_abs c).symm)
    norm_triangle := he.orderUnitNorm_add_le
    norm_eq_zero_iff := fun _ => he.orderUnitNorm_eq_zero_iff }

/-- The `NormedAddCommGroup` structure induced on `E` by an Archimedean order unit `e`, preserving
the existing `AddCommGroup E` structure. Defined as a reducible non-instance (`abbrev`) so its
`toAddCommGroup` projection is definitionally the ambient `AddCommGroup E`. -/
abbrev normedAddCommGroup (he : IsArchimedeanOrderUnit e) : NormedAddCommGroup E :=
  letI := norm e
  NormedAddCommGroup.ofCore he.normedSpaceCore

/-- The real `NormedSpace` structure associated with `IsArchimedeanOrderUnit.normedAddCommGroup`. -/
abbrev normedSpace (he : IsArchimedeanOrderUnit e) :
    letI := he.normedAddCommGroup
    NormedSpace ℝ E :=
  letI := he.normedAddCommGroup
  NormedSpace.ofCore he.normedSpaceCore

end IsArchimedeanOrderUnit

end Archimedean

/-! ### Compatibility of a given norm and partial order with an order unit -/

section IsOrderUnitNorm

/-- Compatibility of an existing seminorm and partial order on a real vector space `E` with a
distinguished order unit `e`: `‖e‖ = 1` and `‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for every `0 ≤ r`.
On a `PartialOrder` the `r = 0` case forces definiteness (`‖a‖ = 0 → a = 0`), and the equivalence
excludes non-Archimedean cones. -/
structure IsOrderUnitNorm {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
    (e : E) : Prop where
  norm_e : ‖e‖ = 1
  norm_le_iff : ∀ (a : E) (r : ℝ), 0 ≤ r → (‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e)

/-- The norm constructed from an Archimedean order unit satisfies `IsOrderUnitNorm`. -/
theorem IsArchimedeanOrderUnit.isOrderUnitNorm {E : Type*} [AddCommGroup E] [Module ℝ E]
    [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}
    (he : IsArchimedeanOrderUnit e) :
    letI := he.normedAddCommGroup
    IsOrderUnitNorm e :=
  let := he.normedAddCommGroup
  { norm_e := he.orderUnitNorm_self
    norm_le_iff := fun _ _ hr => he.orderUnitNorm_le_iff hr }

namespace IsOrderUnitNorm

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E] {e : E}

theorem ne_zero (he : IsOrderUnitNorm e) : e ≠ 0 := by
  intro h
  have := he.norm_e
  simp [h] at this

theorem nontrivial (he : IsOrderUnitNorm e) : Nontrivial E :=
  ⟨⟨e, 0, he.ne_zero⟩⟩

theorem smul_nonneg_of_nonneg (he : IsOrderUnitNorm e) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ r • e :=
  ((he.norm_le_iff 0 r hr).mp (by simpa using hr)).2

theorem neg_smul_nonpos_of_nonneg (he : IsOrderUnitNorm e) {r : ℝ} (hr : 0 ≤ r) : -r • e ≤ 0 :=
  ((he.norm_le_iff 0 r hr).mp (by simpa using hr)).1

/-- In an order-unit normed space, `0 ≤ e`. -/
theorem nonneg (he : IsOrderUnitNorm e) : 0 ≤ e := by
  simpa using he.smul_nonneg_of_nonneg zero_le_one

theorem neg_norm_smul_le (he : IsOrderUnitNorm e) (a : E) : -‖a‖ • e ≤ a :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).mp le_rfl).1

theorem le_norm_smul (he : IsOrderUnitNorm e) (a : E) : a ≤ ‖a‖ • e :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).mp le_rfl).2

/-- Monotonicity of the norm on the positive cone: `0 ≤ a ≤ b → ‖a‖ ≤ ‖b‖`. -/
theorem norm_le_norm_of_nonneg_of_le (he : IsOrderUnitNorm e) {a b : E}
    (ha : 0 ≤ a) (hab : a ≤ b) : ‖a‖ ≤ ‖b‖ := by
  rw [he.norm_le_iff a ‖b‖ (norm_nonneg b)]
  exact ⟨(he.neg_smul_nonpos_of_nonneg (norm_nonneg b)).trans ha, hab.trans (he.le_norm_smul b)⟩

/-- Any seminorm satisfying `IsOrderUnitNorm` on a `PartialOrder` is definite. -/
theorem eq_zero_of_norm_eq_zero (he : IsOrderUnitNorm e) {a : E} (ha : ‖a‖ = 0) : a = 0 := by
  have h := (he.norm_le_iff a 0 le_rfl).mp ha.le
  exact le_antisymm (by simpa using h.2) (by simpa using h.1)

/-- The ambient norm agrees with the order-unit infimum `orderUnitNorm e`. -/
theorem norm_eq_orderUnitNorm (he : IsOrderUnitNorm e) (a : E) :
    ‖a‖ = orderUnitNorm e a := by
  apply le_antisymm
  · exact le_csInf ⟨‖a‖, norm_nonneg a, he.neg_norm_smul_le a, he.le_norm_smul a⟩
      fun r ⟨hr, h1, h2⟩ => (he.norm_le_iff a r hr).mpr ⟨h1, h2⟩
  · exact csInf_le ⟨0, fun _ hr => hr.1⟩
      ⟨norm_nonneg a, he.neg_norm_smul_le a, he.le_norm_smul a⟩

end Seminormed

section OrderedAddMonoid

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- **Order recovery from the norm and order unit.** An element `a` is nonnegative if and only if
`‖‖a‖ • e - a‖ ≤ ‖a‖`. -/
theorem nonneg_iff_norm_smul_sub_le (he : IsOrderUnitNorm e) {a : E} :
    0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖ := by
  rw [he.norm_le_iff (‖a‖ • e - a) ‖a‖ (norm_nonneg a)]
  refine ⟨fun ha => ⟨?_, sub_le_self _ ha⟩, fun ⟨_, h⟩ => sub_nonneg.mp ?_⟩
  · exact (he.neg_smul_nonpos_of_nonneg (norm_nonneg a)).trans
      (sub_nonneg.mpr (he.le_norm_smul a))
  · simpa using h

/-- Dual norm characterization of nonpositivity: `a ≤ 0 ↔ ‖a + ‖a‖ • e‖ ≤ ‖a‖`. -/
theorem nonpos_iff_norm_add_smul_le (he : IsOrderUnitNorm e) {a : E} :
    a ≤ 0 ↔ ‖a + ‖a‖ • e‖ ≤ ‖a‖ := by
  rw [← neg_nonneg, he.nonneg_iff_norm_smul_sub_le, norm_neg, sub_neg_eq_add, add_comm]

/-- **Archimedean property of an order-unit norm.** If `a ≤ ε • e` for every `ε > 0`, then
`‖a + ‖a‖ • e‖ ≤ ‖a‖`, hence `a ≤ 0`. -/
theorem le_zero_of_forall_pos_le (he : IsOrderUnitNorm e) {a : E}
    (ha : ∀ ε : ℝ, 0 < ε → a ≤ ε • e) : a ≤ 0 := by
  rw [he.nonpos_iff_norm_add_smul_le]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [he.norm_le_iff (a + ‖a‖ • e) (‖a‖ + ε) (add_nonneg (norm_nonneg a) hε.le)]
  refine ⟨?_, ?_⟩
  · have h1 : (0 : E) ≤ a + ‖a‖ • e := by
      simpa [neg_smul] using add_le_add_left (he.neg_norm_smul_le a) (‖a‖ • e)
    exact (he.neg_smul_nonpos_of_nonneg (add_nonneg (norm_nonneg a) hε.le)).trans h1
  · calc
      a + ‖a‖ • e ≤ ε • e + ‖a‖ • e := add_le_add_left (ha ε hε) _
      _ = (‖a‖ + ε) • e := by rw [add_comm, add_smul]

/-- Every space satisfying `IsOrderUnitNorm e` has `e` as an Archimedean order unit. -/
theorem isArchimedeanOrderUnit (he : IsOrderUnitNorm e) :
    IsArchimedeanOrderUnit e where
  ne_zero := he.ne_zero
  exists_bounds a := by
    refine ⟨‖a‖ + 1, by positivity, ?_⟩
    exact (he.norm_le_iff a (‖a‖ + 1) (by positivity)).mp (by linarith)
  archimedean _ ha := he.le_zero_of_forall_pos_le ha

theorem le_iff_forall_pos_le_add (he : IsOrderUnitNorm e) {a b : E} :
    a ≤ b ↔ ∀ ε : ℝ, 0 < ε → a ≤ b + ε • e :=
  ⟨fun hab _ hε => hab.trans (le_add_of_nonneg_right (he.smul_nonneg_of_nonneg hε.le)),
    fun h => sub_nonpos.mp <| he.le_zero_of_forall_pos_le fun ε hε =>
      sub_le_iff_le_add'.mpr (h ε hε)⟩

/-- The closed ball of radius `1` around `e` lies inside the positive cone. -/
theorem closedBall_subset_nonneg (he : IsOrderUnitNorm e) :
    closedBall e 1 ⊆ {a : E | 0 ≤ a} := by
  intro a ha
  rw [mem_closedBall, dist_comm, dist_eq_norm] at ha
  have h := ((he.norm_le_iff (e - a) 1 zero_le_one).mp ha).2
  simpa using sub_nonneg.mp (by simpa using h)

/-- The order unit `e` is an interior point of the positive cone. -/
theorem mem_interior_nonneg (he : IsOrderUnitNorm e) :
    e ∈ interior {a : E | 0 ≤ a} :=
  mem_interior.mpr ⟨ball e 1, ball_subset_closedBall.trans he.closedBall_subset_nonneg,
    isOpen_ball, mem_ball_self zero_lt_one⟩

end OrderedAddMonoid

section NormedSpace

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- Compatibility with an order-unit norm implies monotonicity of nonnegative scalar
multiplication. -/
theorem posSMulMono (he : IsOrderUnitNorm e) : PosSMulMono ℝ E where
  smul_le_smul_of_nonneg_left c hc a b hab := by
    rw [← sub_nonneg, ← smul_sub, he.nonneg_iff_norm_smul_sub_le]
    have hd : ‖‖b - a‖ • e - (b - a)‖ ≤ ‖b - a‖ :=
      he.nonneg_iff_norm_smul_sub_le.mp (sub_nonneg.mpr hab)
    rw [norm_smul, Real.norm_of_nonneg hc, mul_smul, ← smul_sub, norm_smul,
      Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hd hc

/-- The positive cone `{a : E | 0 ≤ a}` is norm closed. -/
theorem isClosed_nonneg (he : IsOrderUnitNorm e) :
    IsClosed {a : E | 0 ≤ a} := by
  have h : {a : E | 0 ≤ a} = {a : E | ‖‖a‖ • e - a‖ ≤ ‖a‖} :=
    Set.ext fun _ => he.nonneg_iff_norm_smul_sub_le
  rw [h]
  exact isClosed_le (((continuous_norm.smul continuous_const).sub continuous_id).norm)
    continuous_norm

/-- An order-unit norm induces an `OrderClosedTopology`. -/
theorem orderClosedTopology (he : IsOrderUnitNorm e) :
    OrderClosedTopology E where
  isClosed_le' := by
    have h : {p : E × E | p.1 ≤ p.2} = (fun p : E × E => p.2 - p.1) ⁻¹' {a : E | 0 ≤ a} := by
      ext ⟨a, b⟩
      simp [sub_nonneg]
    rw [h]
    exact he.isClosed_nonneg.preimage (continuous_snd.sub continuous_fst)

end NormedSpace

/-! ### Subspaces, products, and unital order embeddings -/

/-- Restriction to a real submodule containing `e` inherits `IsOrderUnitNorm`. -/
theorem submodule {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
    {e : E} (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (heS : e ∈ S) :
    IsOrderUnitNorm (⟨e, heS⟩ : S) where
  norm_e := he.norm_e
  norm_le_iff a r hr := he.norm_le_iff a.1 r hr

/-- Binary product of order-unit spaces with the coordinatewise order and the maximum norm. -/
theorem prod {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
    [SeminormedAddCommGroup F] [Module ℝ F] [PartialOrder F] {e : E} {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) :
    IsOrderUnitNorm (e, f) where
  norm_e := by simp [Prod.norm_def, he.norm_e, hf.norm_e]
  norm_le_iff x r hr := by
    rw [Prod.norm_def, max_le_iff, he.norm_le_iff x.1 r hr, hf.norm_le_iff x.2 r hr]
    exact ⟨fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩,
      fun ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩ => ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩⟩

/-- Finite product of a nonempty family of order-unit spaces with the coordinatewise order and the
supremum norm. -/
theorem pi {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, PartialOrder (E i)]
    {e : ∀ i, E i} (he : ∀ i, IsOrderUnitNorm (e i)) :
    IsOrderUnitNorm e where
  norm_e := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      exact (he i).norm_e.le
    · obtain ⟨i₀⟩ := ‹Nonempty ι›
      exact (he i₀).norm_e.symm.trans_le (norm_le_pi_norm e i₀)
  norm_le_iff a r hr := by
    rw [pi_norm_le_iff_of_nonneg hr]
    simp only [fun i => (he i).norm_le_iff (a i) r hr, forall_and]
    rfl

/-- Transport of `IsOrderUnitNorm` along a linear isometric equivalence that is also an order
isomorphism. -/
theorem map_linearIsometryEquiv {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [PartialOrder E] [SeminormedAddCommGroup F] [Module ℝ F] [PartialOrder F] {e : E}
    (he : IsOrderUnitNorm e) (T : E ≃ₗᵢ[ℝ] F) (hord : ∀ a b : E, T a ≤ T b ↔ a ≤ b) :
    IsOrderUnitNorm (T e) where
  norm_e := (T.norm_map e).trans he.norm_e
  norm_le_iff b r hr := by
    obtain ⟨a, rfl⟩ := T.surjective b
    rw [T.norm_map, he.norm_le_iff a r hr]
    have h1 : -r • T e ≤ T a ↔ -r • e ≤ a := by
      rw [← map_smul T (-r) e, hord]
    have h2 : T a ≤ r • T e ↔ a ≤ r • e := by
      rw [← map_smul T r e, hord]
    rw [h1, h2]

end IsOrderUnitNorm

end IsOrderUnitNorm

end TauCeti.OrderUnit

/-! ### Automatic isometry of unital linear order embeddings -/

section OrderEmbeddings

open TauCeti.OrderUnit

namespace LinearMap

variable {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [Module ℝ F] [PartialOrder F] {e : E} {f : F}

/-- A unital linear order embedding between order-unit normed spaces is automatically isometric. -/
theorem norm_map_of_isOrderUnitNorm (T : E →ₗ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (hTe : T e = f) (hord : ∀ a b : E, T a ≤ T b ↔ a ≤ b) (a : E) :
    ‖T a‖ = ‖a‖ := by
  apply le_antisymm
  · rw [hf.norm_le_iff (T a) ‖a‖ (norm_nonneg a), ← hTe, ← map_smul, ← map_smul, hord, hord]
    exact ⟨he.neg_norm_smul_le a, he.le_norm_smul a⟩
  · rw [he.norm_le_iff a ‖T a‖ (norm_nonneg (T a)), ← hord, ← hord, map_smul, map_smul, hTe]
    exact ⟨hf.neg_norm_smul_le (T a), hf.le_norm_smul (T a)⟩

/-- Package a unital linear order embedding between order-unit normed spaces as a
`LinearIsometry`. -/
def toLinearIsometryOfOrderUnit (T : E →ₗ[ℝ] F) (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (hTe : T e = f) (hord : ∀ a b : E, T a ≤ T b ↔ a ≤ b) : E →ₗᵢ[ℝ] F where
  toLinearMap := T
  norm_map' := T.norm_map_of_isOrderUnitNorm he hf hTe hord

@[simp]
theorem toLinearIsometryOfOrderUnit_apply (T : E →ₗ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (hTe : T e = f) (hord : ∀ a b : E, T a ≤ T b ↔ a ≤ b) (a : E) :
    T.toLinearIsometryOfOrderUnit he hf hTe hord a = T a :=
  (rfl)

end LinearMap

namespace LinearEquiv

variable {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [Module ℝ F] [PartialOrder F] {e : E} {f : F}

/-- A unital linear order isomorphism between order-unit normed spaces is automatically a linear
isometric equivalence. -/
def toLinearIsometryEquivOfOrderUnit (T : E ≃ₗ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (hTe : T e = f) (hord : ∀ a b : E, T a ≤ T b ↔ a ≤ b) :
    E ≃ₗᵢ[ℝ] F where
  toLinearEquiv := T
  norm_map' := T.toLinearMap.norm_map_of_isOrderUnitNorm he hf hTe hord

@[simp]
theorem toLinearIsometryEquivOfOrderUnit_apply (T : E ≃ₗ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (hTe : T e = f) (hord : ∀ a b : E, T a ≤ T b ↔ a ≤ b) (a : E) :
    T.toLinearIsometryEquivOfOrderUnit he hf hTe hord a = T a :=
  (rfl)

@[simp]
theorem toLinearIsometryEquivOfOrderUnit_symm_apply (T : E ≃ₗ[ℝ] F) (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (hTe : T e = f) (hord : ∀ a b : E, T a ≤ T b ↔ a ≤ b) (b : F) :
    (T.toLinearIsometryEquivOfOrderUnit he hf hTe hord).symm b = T.symm b :=
  (rfl)

end LinearEquiv

end OrderEmbeddings

/-! ### Norm completion of an order-unit space -/

namespace TauCeti.OrderUnit

section Completion

open UniformSpace

/-- The closed positive cone in `UniformSpace.Completion E`: the norm closure of the image of the
positive cone of `E`. -/
def completionNonnegCone (E : Type*) [UniformSpace E] [Zero E] [LE E] : Set (Completion E) :=
  closure (((↑) : E → Completion E) '' {a : E | 0 ≤ a})

theorem mem_completionNonnegCone_def {E : Type*} [UniformSpace E] [Zero E] [LE E]
    {x : Completion E} :
    x ∈ completionNonnegCone E ↔ x ∈ closure (((↑) : E → Completion E) '' {a : E | 0 ≤ a}) :=
  (Iff.rfl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

/-- An element `x` of `UniformSpace.Completion E` lies in the closure of the positive cone of `E`
if and only if `‖‖x‖ • e - x‖ ≤ ‖x‖`. -/
theorem IsOrderUnitNorm.mem_completionNonnegCone_iff (he : IsOrderUnitNorm e)
    {x : Completion E} :
    x ∈ completionNonnegCone E ↔ ‖‖x‖ • (e : Completion E) - x‖ ≤ ‖x‖ := by
  rw [mem_completionNonnegCone_def]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hclosed : IsClosed {b : Completion E | ‖‖b‖ • (e : Completion E) - b‖ ≤ ‖b‖} :=
      isClosed_le (((continuous_norm.smul continuous_const).sub continuous_id).norm)
        continuous_norm
    refine hclosed.closure_subset_iff.mpr ?_ hx
    rintro _ ⟨a, ha, rfl⟩
    rw [Set.mem_ofPred]
    have ha' := he.nonneg_iff_norm_smul_sub_le.mp ha
    have hiso : ‖‖(a : Completion E)‖ • (e : Completion E) - (a : Completion E)‖ =
        ‖‖a‖ • e - a‖ := by
      rw [Completion.norm_coe, ← Completion.coe_smul, ← Completion.coe_sub, Completion.norm_coe]
    rwa [hiso, Completion.norm_coe]
  · rw [Metric.mem_closure_iff]
    intro ε hε
    set δ := ε / 3
    have hδ : 0 < δ := by positivity
    obtain ⟨b, hb⟩ :=
      Metric.mem_closure_range_iff.mp (Completion.denseRange_coe x) δ hδ
    have hrb : ‖(‖x‖ • e - b : E)‖ ≤ ‖x‖ + δ := by
      rw [← Completion.norm_coe, Completion.coe_sub, Completion.coe_smul]
      calc
        ‖‖x‖ • (e : Completion E) - (b : Completion E)‖
          = ‖(‖x‖ • (e : Completion E) - x) + (x - (b : Completion E))‖ := by abel_nf
        _ ≤ ‖‖x‖ • (e : Completion E) - x‖ + ‖x - (b : Completion E)‖ := norm_add_le _ _
        _ ≤ ‖x‖ + δ := add_le_add hx (by simpa [dist_eq_norm] using hb.le)
    have hle : ‖x‖ • e - b ≤ (‖x‖ + δ) • e :=
      ((he.norm_le_iff (‖x‖ • e - b) (‖x‖ + δ) (by positivity)).mp hrb).2
    have ha_nonneg : 0 ≤ b + δ • e := by
      have h1 : ‖x‖ • e - (‖x‖ + δ) • e ≤ b := sub_le_comm.mp hle
      have h2 : -(δ • e) ≤ b := by simpa [add_smul, sub_eq_add_neg] using h1
      simpa [add_comm] using neg_le_iff_add_nonneg.mp h2
    refine ⟨((b + δ • e : E) : Completion E), ⟨b + δ • e, ha_nonneg, rfl⟩, ?_⟩
    rw [dist_eq_norm, Completion.coe_add, Completion.coe_smul]
    calc
      ‖x - ((b : Completion E) + δ • (e : Completion E))‖
        = ‖(x - (b : Completion E)) - δ • (e : Completion E)‖ := by abel_nf
      _ ≤ ‖x - (b : Completion E)‖ + ‖δ • (e : Completion E)‖ := norm_sub_le _ _
      _ < δ + δ := by
        refine add_lt_add_of_lt_of_le (by simpa [dist_eq_norm] using hb) ?_
        rw [norm_smul, Real.norm_of_nonneg hδ.le, Completion.norm_coe, he.norm_e, mul_one]
      _ < ε := by dsimp [δ]; linarith

namespace IsOrderUnitNorm

omit [NormedSpace ℝ E] [IsOrderedAddMonoid E] in
private theorem zero_mem_completionNonnegCone : (0 : Completion E) ∈ completionNonnegCone E :=
  mem_completionNonnegCone_def.mpr <| subset_closure ⟨0, le_rfl, Completion.coe_zero⟩

omit [NormedSpace ℝ E] in
private theorem add_mem_completionNonnegCone {x y : Completion E}
    (hx : x ∈ completionNonnegCone E) (hy : y ∈ completionNonnegCone E) :
    x + y ∈ completionNonnegCone E := by
  rw [mem_completionNonnegCone_def, Metric.mem_closure_iff] at hx hy ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨_, ⟨a, ha, rfl⟩, hxa⟩ := hx (ε / 2) hε2
  obtain ⟨_, ⟨b, hb, rfl⟩, hyb⟩ := hy (ε / 2) hε2
  refine ⟨((a + b : E) : Completion E), ⟨a + b, add_nonneg ha hb, rfl⟩, ?_⟩
  rw [dist_eq_norm, Completion.coe_add]
  calc
    ‖(x + y) - ((a : Completion E) + (b : Completion E))‖
      = ‖(x - (a : Completion E)) + (y - (b : Completion E))‖ := by abel_nf
    _ ≤ ‖x - (a : Completion E)‖ + ‖y - (b : Completion E)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa [dist_eq_norm] using hxa)
        (by simpa [dist_eq_norm] using hyb)
    _ = ε := add_halves ε

private theorem smul_mem_completionNonnegCone (he : IsOrderUnitNorm e) {c : ℝ} (hc : 0 ≤ c)
    {x : Completion E} (hx : x ∈ completionNonnegCone E) :
    c • x ∈ completionNonnegCone E := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · simpa using zero_mem_completionNonnegCone
  · have := he.posSMulMono
    rw [mem_completionNonnegCone_def, Metric.mem_closure_iff] at hx ⊢
    intro ε hε
    obtain ⟨_, ⟨a, ha, rfl⟩, hxa⟩ := hx (ε / c) (div_pos hε hc_pos)
    refine ⟨((c • a : E) : Completion E), ⟨c • a, smul_nonneg hc_pos.le ha, rfl⟩, ?_⟩
    rw [dist_eq_norm, Completion.coe_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hc_pos.le]
    calc
      c * ‖x - (a : Completion E)‖ < c * (ε / c) :=
        mul_lt_mul_of_pos_left (by simpa [dist_eq_norm] using hxa) hc_pos
      _ = ε := mul_div_cancel₀ ε hc_pos.ne'

private theorem eq_zero_of_mem_and_neg_mem_completionNonnegCone (he : IsOrderUnitNorm e)
    {x : Completion E} (hx : x ∈ completionNonnegCone E) (hnx : -x ∈ completionNonnegCone E) :
    x = 0 := by
  rw [mem_completionNonnegCone_def, Metric.mem_closure_iff] at hx hnx
  suffices ‖x‖ ≤ 0 from norm_le_zero_iff.mp this
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  set δ := ε / 4
  have hδ : 0 < δ := by positivity
  obtain ⟨_, ⟨a₁, ha₁, rfl⟩, h1⟩ := hx δ hδ
  obtain ⟨_, ⟨a₂, ha₂, rfl⟩, h2⟩ := hnx δ hδ
  rw [dist_eq_norm] at h1 h2
  have hsum : ‖a₁ + a₂‖ ≤ 2 * δ := by
    rw [← Completion.norm_coe, Completion.coe_add]
    calc
      ‖(a₁ : Completion E) + (a₂ : Completion E)‖
        = ‖-((x - (a₁ : Completion E)) + (-x - (a₂ : Completion E)))‖ := by abel_nf
      _ = ‖(x - (a₁ : Completion E)) + (-x - (a₂ : Completion E))‖ := norm_neg _
      _ ≤ ‖x - (a₁ : Completion E)‖ + ‖-x - (a₂ : Completion E)‖ := norm_add_le _ _
      _ ≤ δ + δ := add_le_add h1.le h2.le
      _ = 2 * δ := by ring
  have ha₁_le : a₁ ≤ a₁ + a₂ := le_add_of_nonneg_right ha₂
  have ha₁_norm : ‖a₁‖ ≤ 2 * δ :=
    (he.norm_le_norm_of_nonneg_of_le ha₁ ha₁_le).trans hsum
  calc
    ‖x‖ ≤ ‖(a₁ : Completion E)‖ + ‖x - (a₁ : Completion E)‖ := norm_le_insert' x a₁
    _ ≤ 2 * δ + δ := add_le_add (by simpa [Completion.norm_coe] using ha₁_norm) h1.le
    _ ≤ ε := by dsimp [δ]; linarith

/-- The partial order on `UniformSpace.Completion E` whose positive cone is the norm closure of the
image of `{a : E | 0 ≤ a}`. -/
@[instance_reducible]
def completionPartialOrder (he : IsOrderUnitNorm e) : PartialOrder (Completion E) where
  le x y := y - x ∈ completionNonnegCone E
  le_refl x := by simp [zero_mem_completionNonnegCone]
  le_trans x y z hxy hyz := by
    have h := add_mem_completionNonnegCone hyz hxy
    rwa [sub_add_sub_cancel] at h
  le_antisymm x y hxy hyx := by
    have h := eq_zero_of_mem_and_neg_mem_completionNonnegCone he hxy (by simpa using hyx)
    exact (sub_eq_zero.mp h).symm

theorem completion_le_iff (he : IsOrderUnitNorm e) {x y : Completion E} :
    (letI := he.completionPartialOrder; x ≤ y) ↔ y - x ∈ completionNonnegCone E :=
  (Iff.rfl)

theorem completion_nonneg_iff (he : IsOrderUnitNorm e) {x : Completion E} :
    (letI := he.completionPartialOrder; 0 ≤ x) ↔ x ∈ completionNonnegCone E := by
  rw [he.completion_le_iff, sub_zero]

/-- Embedding `E` into `UniformSpace.Completion E` preserves and reflects the order. -/
@[simp]
theorem completion_coe_le_coe (he : IsOrderUnitNorm e) {a b : E} :
    (letI := he.completionPartialOrder; (a : Completion E) ≤ (b : Completion E)) ↔ a ≤ b := by
  rw [he.completion_le_iff, ← Completion.coe_sub, he.mem_completionNonnegCone_iff]
  have hiso : ‖‖((b - a : E) : Completion E)‖ • (e : Completion E) - ((b - a : E) : Completion E)‖ =
      ‖‖b - a‖ • e - (b - a)‖ := by
    rw [Completion.norm_coe, ← Completion.coe_smul, ← Completion.coe_sub, Completion.norm_coe]
  rw [hiso, Completion.norm_coe, ← he.nonneg_iff_norm_smul_sub_le, sub_nonneg]

@[simp]
theorem completion_coe_nonneg (he : IsOrderUnitNorm e) {a : E} :
    (letI := he.completionPartialOrder; 0 ≤ (a : Completion E)) ↔ 0 ≤ a := by
  simpa using he.completion_coe_le_coe (a := 0) (b := a)

/-- Addition on `UniformSpace.Completion E` is monotone with respect to `completionPartialOrder`. -/
theorem completionIsOrderedAddMonoid (he : IsOrderUnitNorm e) :
    letI := he.completionPartialOrder
    IsOrderedAddMonoid (Completion E) :=
  let := he.completionPartialOrder
  { add_le_add_left := fun a b hab c => by
      rw [he.completion_le_iff] at hab ⊢
      simpa [sub_add_add_cancel] using hab }

/-- Multiplication by nonnegative real scalars is monotone on `UniformSpace.Completion E`. -/
theorem completionPosSMulMono (he : IsOrderUnitNorm e) :
    letI := he.completionPartialOrder
    PosSMulMono ℝ (Completion E) :=
  let := he.completionPartialOrder
  { smul_le_smul_of_nonneg_left := fun c hc a b hab => by
      rw [he.completion_le_iff] at hab ⊢
      rw [← smul_sub]
      exact smul_mem_completionNonnegCone he hc hab }

/-- **Completion of an order-unit space.** The norm completion `UniformSpace.Completion E`, equipped
with the closed positive cone `completionNonnegCone E` and the order unit `(e : Completion E)`, is a
complete order-unit space with its inherited norm. -/
theorem completion (he : IsOrderUnitNorm e) :
    letI := he.completionPartialOrder
    IsOrderUnitNorm (e : Completion E) := by
  let := he.completionPartialOrder
  refine ⟨by rw [Completion.norm_coe, he.norm_e], fun x r hr => ⟨fun hxr => ?_, fun ⟨h1, h2⟩ => ?_⟩⟩
  · refine ⟨?_, ?_⟩
    · rw [he.completion_le_iff, mem_completionNonnegCone_def, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨b, hb⟩ :=
        Metric.mem_closure_range_iff.mp (Completion.denseRange_coe x) (ε / 3) (by positivity)
      have hbx : ‖(b : Completion E) - x‖ ≤ ε / 3 := by
        rw [← dist_eq_norm, dist_comm]
        exact hb.le
      set s := max r ‖b‖
      have hs : 0 ≤ s := le_max_of_le_left hr
      have hb_pos : 0 ≤ b + s • e := by
        have h : -(s • e) ≤ b := by
          simpa [neg_smul] using ((he.norm_le_iff b s hs).mp (le_max_right r ‖b‖)).1
        simpa [add_comm] using neg_le_iff_add_nonneg.mp h
      have hs_sub : s - r ≤ ε / 3 := by
        have hbn : ‖b‖ ≤ r + ε / 3 := by
          rw [← Completion.norm_coe]
          exact (norm_le_insert' (b : Completion E) x).trans (add_le_add hxr hbx)
        exact sub_le_iff_le_add'.mpr (max_le (by linarith) hbn)
      refine ⟨((b + s • e : E) : Completion E), ⟨b + s • e, hb_pos, rfl⟩, ?_⟩
      rw [dist_eq_norm, Completion.coe_add, Completion.coe_smul]
      calc
        ‖(x - (-r • (e : Completion E))) - ((b : Completion E) + s • (e : Completion E))‖
          = ‖(x - (b : Completion E)) - (s - r) • (e : Completion E)‖ := by
              rw [sub_smul, neg_smul]; abel_nf
        _ ≤ ‖x - (b : Completion E)‖ + ‖(s - r) • (e : Completion E)‖ := norm_sub_le _ _
        _ ≤ ε / 3 + ε / 3 := by
          refine add_le_add (by simpa [dist_eq_norm] using hb.le) ?_
          have hsr0 : 0 ≤ s - r := sub_nonneg.mpr (le_max_left r ‖b‖)
          rw [norm_smul, Real.norm_of_nonneg hsr0, Completion.norm_coe, he.norm_e, mul_one]
          exact hs_sub
        _ < ε := by linarith
    · rw [he.completion_le_iff, mem_completionNonnegCone_def, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨b, hb⟩ :=
        Metric.mem_closure_range_iff.mp (Completion.denseRange_coe x) (ε / 3) (by positivity)
      have hbx : ‖(b : Completion E) - x‖ ≤ ε / 3 := by
        rw [← dist_eq_norm, dist_comm]
        exact hb.le
      set s := max r ‖b‖
      have hs : 0 ≤ s := le_max_of_le_left hr
      have hb_pos : 0 ≤ s • e - b :=
        sub_nonneg.mpr (((he.norm_le_iff b s hs).mp (le_max_right r ‖b‖)).2)
      have hs_sub : s - r ≤ ε / 3 := by
        have hbn : ‖b‖ ≤ r + ε / 3 := by
          rw [← Completion.norm_coe]
          exact (norm_le_insert' (b : Completion E) x).trans (add_le_add hxr hbx)
        exact sub_le_iff_le_add'.mpr (max_le (by linarith) hbn)
      refine ⟨((s • e - b : E) : Completion E), ⟨s • e - b, hb_pos, rfl⟩, ?_⟩
      rw [dist_eq_norm, Completion.coe_sub, Completion.coe_smul]
      calc
        ‖(r • (e : Completion E) - x) - (s • (e : Completion E) - (b : Completion E))‖
          = ‖((b : Completion E) - x) - (s - r) • (e : Completion E)‖ := by
              rw [sub_smul]; abel_nf
        _ ≤ ‖(b : Completion E) - x‖ + ‖(s - r) • (e : Completion E)‖ := norm_sub_le _ _
        _ ≤ ε / 3 + ε / 3 := by
          refine add_le_add hbx ?_
          have hsr0 : 0 ≤ s - r := sub_nonneg.mpr (le_max_left r ‖b‖)
          rw [norm_smul, Real.norm_of_nonneg hsr0, Completion.norm_coe, he.norm_e, mul_one]
          exact hs_sub
        _ < ε := by linarith
  · rw [he.completion_le_iff, mem_completionNonnegCone_def, Metric.mem_closure_iff] at h1 h2
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ := ε / 3
    have hδ : 0 < δ := by positivity
    obtain ⟨_, ⟨u, hu, rfl⟩, hu_dist⟩ := h1 δ hδ
    obtain ⟨_, ⟨v, hv, rfl⟩, hv_dist⟩ := h2 δ hδ
    rw [dist_eq_norm] at hu_dist hv_dist
    have huv_sum : ‖(u + v) - (2 * r) • e‖ ≤ 2 * δ := by
      rw [← Completion.norm_coe, Completion.coe_sub, Completion.coe_add, Completion.coe_smul]
      calc
        ‖((u : Completion E) + (v : Completion E)) - (2 * r) • (e : Completion E)‖
          = ‖-(((x - (-r • (e : Completion E))) - (u : Completion E)) +
              ((r • (e : Completion E) - x) - (v : Completion E)))‖ := by
                rw [mul_smul, two_smul, neg_smul]; abel_nf
        _ = ‖((x - (-r • (e : Completion E))) - (u : Completion E)) +
              ((r • (e : Completion E) - x) - (v : Completion E))‖ := norm_neg _
        _ ≤ ‖(x - (-r • (e : Completion E))) - (u : Completion E)‖ +
            ‖(r • (e : Completion E) - x) - (v : Completion E)‖ := norm_add_le _ _
        _ ≤ δ + δ := add_le_add hu_dist.le hv_dist.le
        _ = 2 * δ := by ring
    have huv_upper : u + v ≤ (2 * r + 2 * δ) • e := by
      have h := ((he.norm_le_iff ((u + v) - (2 * r) • e) (2 * δ) (by positivity)).mp huv_sum).2
      calc
        u + v = ((u + v) - (2 * r) • e) + (2 * r) • e := by abel
        _ ≤ (2 * δ) • e + (2 * r) • e := add_le_add_left h _
        _ = (2 * r + 2 * δ) • e := by rw [add_comm, add_smul]
    have huv_diff_norm : ‖u - v‖ ≤ 2 * r + 2 * δ := by
      rw [he.norm_le_iff (u - v) (2 * r + 2 * δ) (by positivity)]
      refine ⟨?_, ?_⟩
      · have hlower : -(u + v) ≤ u - v := by
          calc
            -(u + v) = -u - v := by abel
            _ ≤ u - v := sub_le_sub_right ((neg_nonpos.mpr hu).trans hu) v
        have hneg : -(2 * r + 2 * δ) • e ≤ -(u + v) := by
          rw [neg_smul]
          exact neg_le_neg huv_upper
        exact hneg.trans hlower
      · calc
          u - v = u + -v := sub_eq_add_neg u v
          _ ≤ u + v := add_le_add_right ((neg_nonpos.mpr hv).trans hv) u
          _ ≤ (2 * r + 2 * δ) • e := huv_upper
    set b : E := (2⁻¹ : ℝ) • (u - v)
    have hb_norm : ‖b‖ ≤ r + δ := by
      dsimp [b]
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      linarith
    have hxb : ‖x - (b : Completion E)‖ ≤ δ := by
      dsimp [b]
      rw [Completion.coe_smul, Completion.coe_sub]
      calc
        ‖x - (2⁻¹ : ℝ) • ((u : Completion E) - (v : Completion E))‖
          = ‖(2⁻¹ : ℝ) • (((x - (-r • (e : Completion E))) - (u : Completion E)) -
              ((r • (e : Completion E) - x) - (v : Completion E)))‖ := by
                congr 1
                rw [neg_smul, smul_sub]
                module
        _ = (2⁻¹ : ℝ) * ‖((x - (-r • (e : Completion E))) - (u : Completion E)) -
              ((r • (e : Completion E) - x) - (v : Completion E))‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        _ ≤ (2⁻¹ : ℝ) * (δ + δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact (norm_sub_le _ _).trans (add_le_add hu_dist.le hv_dist.le)
        _ = δ := by ring
    calc
      ‖x‖ ≤ ‖(b : Completion E)‖ + ‖x - (b : Completion E)‖ := norm_le_insert' x b
      _ ≤ (r + δ) + δ := add_le_add (by simpa [Completion.norm_coe] using hb_norm) hxb
      _ ≤ r + ε := by dsimp [δ]; linarith

end IsOrderUnitNorm

end Completion

/-! ### Concrete order-unit normed spaces -/

section Examples

namespace IsOrderUnitNorm

/-- The real line `ℝ` with order unit `1` satisfies `IsOrderUnitNorm`. -/
theorem one_real : IsOrderUnitNorm (1 : ℝ) where
  norm_e := norm_one
  norm_le_iff a r _ := by simp [Real.norm_eq_abs, abs_le]

/-- Every finite nonempty product `ι → ℝ` with order unit `1` and the supremum norm satisfies
`IsOrderUnitNorm`. -/
theorem one_pi {ι : Type*} [Fintype ι] [Nonempty ι] : IsOrderUnitNorm (1 : ι → ℝ) :=
  IsOrderUnitNorm.pi fun _ => one_real

/-- The space `K →ᵇ ℝ` of bounded continuous real functions on a nonempty topological space `K`,
with the supremum norm and constant function `1`, satisfies `IsOrderUnitNorm`. -/
theorem one_boundedContinuousFunction {K : Type*} [TopologicalSpace K] [Nonempty K] :
    IsOrderUnitNorm (1 : K →ᵇ ℝ) where
  norm_e := norm_one
  norm_le_iff f r hr := by
    rw [BoundedContinuousFunction.norm_le hr]
    refine ⟨fun h =>
        ⟨fun x => by simpa using (abs_le.mp (by simpa [Real.norm_eq_abs] using h x)).1,
         fun x => by simpa using (abs_le.mp (by simpa [Real.norm_eq_abs] using h x)).2⟩,
      fun ⟨h1, h2⟩ x => ?_⟩
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by simpa using h1 x, by simpa using h2 x⟩

/-- The Banach space `C(K, ℝ)` of continuous real functions on a nonempty compact space `K`, with
the uniform norm and constant function `1`, satisfies `IsOrderUnitNorm`. -/
theorem one_continuousMap {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K] :
    IsOrderUnitNorm (1 : C(K, ℝ)) where
  norm_e := by
    apply le_antisymm
    · rw [ContinuousMap.norm_le (1 : C(K, ℝ)) zero_le_one]
      intro x
      simp
    · simp
  norm_le_iff f r hr := by
    rw [ContinuousMap.norm_le f hr, ContinuousMap.le_def, ContinuousMap.le_def]
    refine ⟨fun h =>
        ⟨fun x => by simpa using (abs_le.mp (by simpa [Real.norm_eq_abs] using h x)).1,
         fun x => by simpa using (abs_le.mp (by simpa [Real.norm_eq_abs] using h x)).2⟩,
      fun ⟨h1, h2⟩ x => ?_⟩
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by simpa using h1 x, by simpa using h2 x⟩

end IsOrderUnitNorm

end Examples

end TauCeti.OrderUnit
