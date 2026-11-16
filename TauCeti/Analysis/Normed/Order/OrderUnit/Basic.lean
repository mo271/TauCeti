/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Order-unit normed spaces

An element `e` of a real ordered vector space `E` is an **Archimedean order unit**
(`TauCeti.OrderUnit.IsArchimedeanOrderUnit`) if `e ≠ 0`, every element of `E` lies in a symmetric
order interval `[-r • e, r • e]` for some `r > 0`, and `a ≤ ε • e` for all `ε > 0` implies
`a ≤ 0`. Such an order unit induces a genuine norm on `E`,
`TauCeti.OrderUnit.orderUnitNorm e a = sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}`, whose
closed balls of radius `r ≥ 0` are precisely the order intervals `[-r • e, r • e]`.

To allow existing normed ordered spaces (`ℝ`, `C(K, ℝ)` for compact nonempty `K`, the self-adjoint
part of a unital C⋆-algebra, unital subspaces, and finite `ℓ^∞` products) to participate without
norm diamonds, we formulate the compatibility predicate `TauCeti.OrderUnit.IsOrderUnitNorm e` on an
already seminormed ordered space: `‖e‖ = 1` and `‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e` for every
`r ≥ 0`.

## Main definitions and results

* `TauCeti.OrderUnit.IsArchimedeanOrderUnit`: Archimedean order-unit predicate on a real ordered
  vector space, together with `orderUnitNorm` and the induced `NormedAddCommGroup` and
  `NormedSpace ℝ` constructors (`toNormedAddCommGroup`, `toNormedSpace`).
* `TauCeti.OrderUnit.IsOrderUnitNorm`: compatibility between an existing norm and an order unit `e`.
* `TauCeti.OrderUnit.IsOrderUnitNorm.nonneg_iff_norm_sub_le`: positivity is recovered from the norm
  and `e` via `0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`.
* `TauCeti.OrderUnit.IsOrderUnitNorm.isClosed_nonneg`, `orderClosedTopology`, and
  `closedBall_subset_nonneg`: the positive cone `{a | 0 ≤ a}` is norm-closed and contains the unit
  ball `Metric.closedBall e 1`, making `e` an interior point of `{a | 0 ≤ a}`.
* `TauCeti.OrderUnit.IsOrderUnitNorm.submodule`, `prod`, `pi`, and `linearIsometryEquivOfOrderIso`:
  preservation under unital subspaces, binary and finite products, and unital linear order
  isomorphisms (which are automatically linear isometries).
* `TauCeti.OrderUnit.isOrderUnitNorm_one_real` and
  `TauCeti.OrderUnit.isOrderUnitNorm_one_continuousMap`: `(1 : ℝ)` and `(1 : C(K, ℝ))` for compact
  nonempty `K` carry order-unit norms.
* `TauCeti.OrderUnit.IsOrderUnitNorm.toPositiveContinuousLinearMap` and
  `opNorm_toPositiveContinuousLinearMap`: every positive linear map `E →ₚ[ℝ] F` between order-unit
  normed spaces is automatically continuous with operator norm `‖T e‖` (hence norm `1` when unital).

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. **7** (1951).
* E. M. Alfsen, *Compact Convex Sets and Boundary Integrals*, Springer, 1971, Chapter II.
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. **4** (1999), 559–600.
-/

public section

open Set
open scoped NNReal

namespace TauCeti.OrderUnit

section Archimedean

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [Module ℝ E]

/-- An element `e` of a real ordered vector space `E` is an **Archimedean order unit** if it is
nonzero, absorbs every element into a symmetric order interval `[-r • e, r • e]` for some `r > 0`,
and satisfies the Archimedean property that `a ≤ ε • e` for all `ε > 0` forces `a ≤ 0`. -/
structure IsArchimedeanOrderUnit (e : E) : Prop where
  /-- The order unit is nonzero. -/
  ne_zero : e ≠ 0
  /-- Every element lies in `[-r • e, r • e]` for some positive scalar `r`. -/
  exists_pos_le : ∀ a : E, ∃ r : ℝ, 0 < r ∧ -r • e ≤ a ∧ a ≤ r • e
  /-- The Archimedean property: `a ≤ ε • e` for all `ε > 0` implies `a ≤ 0`. -/
  le_zero_of_forall_pos_smul_le : ∀ a : E, (∀ ε : ℝ, 0 < ε → a ≤ ε • e) → a ≤ 0

/-- The **order-unit norm** (gauge of `[-e, e]`) associated with `e : E`, defined as the infimum of
nonnegative scalars `r` such that `-r • e ≤ a ∧ a ≤ r • e`. -/
noncomputable def orderUnitNorm (e a : E) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}

namespace IsArchimedeanOrderUnit

/-- An Archimedean order unit makes the ambient space nontrivial. -/
theorem nontrivial {e : E} (he : IsArchimedeanOrderUnit e) : Nontrivial E :=
  ⟨⟨e, 0, he.ne_zero⟩⟩

private lemma bddBelow_intervalSet (e a : E) :
    BddBelow {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e} :=
  ⟨0, fun _ hr => hr.1⟩

private lemma nonempty_intervalSet {e : E} (he : IsArchimedeanOrderUnit e) (a : E) :
    {r : ℝ | 0 ≤ r ∧ -r • e ≤ a ∧ a ≤ r • e}.Nonempty := by
  obtain ⟨r, hr, h1, h2⟩ := he.exists_pos_le a
  exact ⟨r, hr.le, h1, h2⟩

/-- The order-unit norm is nonnegative. -/
theorem orderUnitNorm_nonneg (e a : E) : 0 ≤ orderUnitNorm e a :=
  Real.sInf_nonneg fun _ hr => hr.1

/-- An Archimedean order unit is nonnegative. -/
theorem nonneg [PosSMulMono ℝ E] {e : E} (he : IsArchimedeanOrderUnit e) : 0 ≤ e := by
  obtain ⟨r, hr, -, hr0⟩ := he.exists_pos_le 0
  have := smul_le_smul_of_nonneg_left hr0 (inv_pos.2 hr).le
  rwa [smul_zero, inv_smul_smul₀ hr.ne'] at this

section Ordered

variable [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}

/-- Every element `a` is bounded above by `orderUnitNorm e a • e`. -/
theorem le_orderUnitNorm_smul (he : IsArchimedeanOrderUnit e) (a : E) :
    a ≤ orderUnitNorm e a • e := by
  rw [← sub_nonpos]
  refine he.le_zero_of_forall_pos_smul_le (a - orderUnitNorm e a • e) fun ε hε => ?_
  obtain ⟨r, ⟨-, -, har⟩, hrlt⟩ := exists_lt_of_csInf_lt (he.nonempty_intervalSet a)
    (lt_add_of_pos_right (orderUnitNorm e a) hε)
  have hre : r • e ≤ (orderUnitNorm e a + ε) • e :=
    smul_le_smul_of_nonneg_right hrlt.le he.nonneg
  rw [add_smul] at hre
  exact sub_le_iff_le_add'.2 (har.trans hre)

/-- Every element `a` is bounded below by `-orderUnitNorm e a • e`. -/
theorem neg_orderUnitNorm_smul_le (he : IsArchimedeanOrderUnit e) (a : E) :
    -orderUnitNorm e a • e ≤ a := by
  rw [neg_smul]
  suffices -a - orderUnitNorm e a • e ≤ 0 by
    exact neg_le.1 (by simpa [sub_eq_add_neg, add_comm] using sub_nonpos.1 this)
  refine he.le_zero_of_forall_pos_smul_le (-a - orderUnitNorm e a • e) fun ε hε => ?_
  obtain ⟨r, ⟨-, hlar, -⟩, hrlt⟩ := exists_lt_of_csInf_lt (he.nonempty_intervalSet a)
    (lt_add_of_pos_right (orderUnitNorm e a) hε)
  have hre : r • e ≤ (orderUnitNorm e a + ε) • e :=
    smul_le_smul_of_nonneg_right hrlt.le he.nonneg
  rw [add_smul] at hre
  exact sub_le_iff_le_add'.2 ((neg_le.2 (by simpa [neg_smul] using hlar)).trans hre)

/-- **Closed-interval law for `orderUnitNorm`.** For `r ≥ 0`, `orderUnitNorm e a ≤ r` if and only
if `a ∈ [-r • e, r • e]`. -/
theorem orderUnitNorm_le_iff (he : IsArchimedeanOrderUnit e) (a : E) {r : ℝ} (hr : 0 ≤ r) :
    orderUnitNorm e a ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e := by
  refine ⟨fun h => ?_, fun h => csInf_le (bddBelow_intervalSet e a) ⟨hr, h⟩⟩
  have hse : orderUnitNorm e a • e ≤ r • e := smul_le_smul_of_nonneg_right h he.nonneg
  refine ⟨?_, (he.le_orderUnitNorm_smul a).trans hse⟩
  rw [neg_smul]
  exact (neg_le_neg hse).trans (by simpa [neg_smul] using he.neg_orderUnitNorm_smul_le a)

/-- The order-unit norm vanishes only at `0`. -/
@[simp]
theorem orderUnitNorm_eq_zero_iff (he : IsArchimedeanOrderUnit e) {a : E} :
    orderUnitNorm e a = 0 ↔ a = 0 := by
  rw [le_antisymm_iff, and_iff_left (orderUnitNorm_nonneg e a), he.orderUnitNorm_le_iff a le_rfl]
  simp [le_antisymm_iff, and_comm]

/-- The order-unit norm of `0` is `0`. -/
@[simp]
theorem orderUnitNorm_zero (he : IsArchimedeanOrderUnit e) : orderUnitNorm e 0 = 0 :=
  he.orderUnitNorm_eq_zero_iff.2 rfl

/-- The order-unit norm of the unit `e` itself is `1`. -/
@[simp]
theorem orderUnitNorm_self (he : IsArchimedeanOrderUnit e) : orderUnitNorm e e = 1 := by
  refine le_antisymm ?_ ?_
  · rw [he.orderUnitNorm_le_iff e zero_le_one, neg_smul, one_smul]
    exact ⟨(neg_nonpos.2 he.nonneg).trans he.nonneg, le_rfl⟩
  · by_contra! hlt
    have hle := he.le_orderUnitNorm_smul e
    have hpos : 0 < 1 - orderUnitNorm e e := sub_pos.2 hlt
    have hsub : (1 - orderUnitNorm e e) • e ≤ 0 := by
      rw [sub_smul, one_smul, sub_nonpos]
      exact hle
    have he0 : e ≤ 0 := by
      have := smul_le_smul_of_nonneg_left hsub (inv_pos.2 hpos).le
      rwa [smul_zero, inv_smul_smul₀ hpos.ne'] at this
    exact he.ne_zero (le_antisymm he0 he.nonneg)

/-- The order-unit norm is symmetric under negation. -/
@[simp]
theorem orderUnitNorm_neg (he : IsArchimedeanOrderUnit e) (a : E) :
    orderUnitNorm e (-a) = orderUnitNorm e a := by
  refine le_antisymm ?_ ?_
  · rw [he.orderUnitNorm_le_iff (-a) (orderUnitNorm_nonneg e a)]
    exact ⟨by simpa [neg_smul] using neg_le_neg (he.le_orderUnitNorm_smul a),
      by simpa [neg_smul] using neg_le_neg (he.neg_orderUnitNorm_smul_le a)⟩
  · rw [he.orderUnitNorm_le_iff a (orderUnitNorm_nonneg e (-a))]
    exact ⟨by simpa [neg_smul] using neg_le_neg (he.le_orderUnitNorm_smul (-a)),
      by simpa [neg_smul] using neg_le_neg (he.neg_orderUnitNorm_smul_le (-a))⟩

/-- Triangle inequality for the order-unit norm. -/
theorem orderUnitNorm_add_le (he : IsArchimedeanOrderUnit e) (a b : E) :
    orderUnitNorm e (a + b) ≤ orderUnitNorm e a + orderUnitNorm e b := by
  rw [he.orderUnitNorm_le_iff (a + b)
    (add_nonneg (orderUnitNorm_nonneg e a) (orderUnitNorm_nonneg e b))]
  refine ⟨?_, ?_⟩
  · calc -(orderUnitNorm e a + orderUnitNorm e b) • e
        = -orderUnitNorm e a • e + -orderUnitNorm e b • e := by
            rw [neg_smul, add_smul, neg_add_rev, add_comm, neg_smul, neg_smul]
      _ ≤ a + b := add_le_add (he.neg_orderUnitNorm_smul_le a) (he.neg_orderUnitNorm_smul_le b)
  · calc a + b ≤ orderUnitNorm e a • e + orderUnitNorm e b • e :=
          add_le_add (he.le_orderUnitNorm_smul a) (he.le_orderUnitNorm_smul b)
      _ = (orderUnitNorm e a + orderUnitNorm e b) • e := (add_smul _ _ e).symm

/-- Scalar homogeneity of the order-unit norm. -/
theorem orderUnitNorm_smul (he : IsArchimedeanOrderUnit e) (c : ℝ) (a : E) :
    orderUnitNorm e (c • a) = |c| * orderUnitNorm e a := by
  have hmul : ∀ (t : ℝ) (x : E), 0 ≤ t →
      orderUnitNorm e (t • x) ≤ t * orderUnitNorm e x := fun t x ht => by
    rw [he.orderUnitNorm_le_iff (t • x) (mul_nonneg ht (orderUnitNorm_nonneg e x))]
    refine ⟨?_, ?_⟩
    · have := smul_le_smul_of_nonneg_left (he.neg_orderUnitNorm_smul_le x) ht
      rwa [neg_smul, smul_neg, smul_smul, ← neg_smul] at this
    · have := smul_le_smul_of_nonneg_left (he.le_orderUnitNorm_smul x) ht
      rwa [smul_smul] at this
  have habs : ∀ (t : ℝ) (x : E), orderUnitNorm e (t • x) ≤ |t| * orderUnitNorm e x := fun t x => by
    rcases le_total 0 t with ht | ht
    · simpa [abs_of_nonneg ht] using hmul t x ht
    · have h1 := hmul (-t) (-x) (neg_nonneg.2 ht)
      simpa [neg_smul_neg, abs_of_nonpos ht, he.orderUnitNorm_neg] using h1
  rcases eq_or_ne c 0 with rfl | hc
  · simp [he.orderUnitNorm_zero]
  · refine le_antisymm (habs c a) ?_
    have h2 := habs c⁻¹ (c • a)
    rw [inv_smul_smul₀ hc, abs_inv] at h2
    exact (le_inv_mul_iff₀ (abs_pos.2 hc)).1 h2

/-- The `Norm E` structure induced by an order unit `e`. Defined as an `abbrev` rather than a
global `instance` so types that already carry a norm do not incur diamonds. -/
noncomputable abbrev toNorm (e : E) : Norm E := ⟨orderUnitNorm e⟩

/-- The `NormedSpace.Core ℝ E` axioms verified for `orderUnitNorm e`. -/
theorem normedSpaceCore (he : IsArchimedeanOrderUnit e) :
    @NormedSpace.Core ℝ E _ _ _ (toNorm e) :=
  letI := toNorm e
  { norm_nonneg := orderUnitNorm_nonneg e
    norm_smul := fun c a => (he.orderUnitNorm_smul c a).trans (by rw [Real.norm_eq_abs]; rfl)
    norm_triangle := he.orderUnitNorm_add_le
    norm_eq_zero_iff := fun _ => he.orderUnitNorm_eq_zero_iff }

/-- Package the `NormedAddCommGroup` structure induced on `E` by an Archimedean order unit `e`.
Defined as an `abbrev` rather than a global `instance` so types that already carry a norm do not
incur typeclass diamonds. -/
noncomputable abbrev toNormedAddCommGroup (he : IsArchimedeanOrderUnit e) : NormedAddCommGroup E :=
  letI := toNorm e
  NormedAddCommGroup.ofCore he.normedSpaceCore

/-- Package the `NormedSpace ℝ` structure associated with `he.toNormedAddCommGroup`. -/
noncomputable abbrev toNormedSpace (he : IsArchimedeanOrderUnit e) :
    @NormedSpace ℝ E _ he.toNormedAddCommGroup.toSeminormedAddCommGroup :=
  letI := he.toNormedAddCommGroup
  NormedSpace.ofCore he.normedSpaceCore

end Ordered

end IsArchimedeanOrderUnit

end Archimedean

/-! ### Compatibility between an existing norm and an order unit -/

/-- On a real seminormed ordered space `E`, `IsOrderUnitNorm e` asserts that `e` has norm `1` and
that the closed balls of radius `r ≥ 0` are precisely the symmetric order intervals
`[-r • e, r • e]`. -/
structure IsOrderUnitNorm {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] (e : E) : Prop where
  /-- The order unit has norm one. -/
  norm_eq_one : ‖e‖ = 1
  /-- For `r ≥ 0`, `‖a‖ ≤ r` if and only if `-r • e ≤ a ∧ a ≤ r • e`. -/
  norm_le_iff : ∀ (a : E) (r : ℝ), 0 ≤ r → (‖a‖ ≤ r ↔ -r • e ≤ a ∧ a ≤ r • e)

namespace IsOrderUnitNorm

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}

/-- Every element `a` is bounded below by `-‖a‖ • e`. -/
theorem neg_norm_smul_le (he : IsOrderUnitNorm e) (a : E) : -‖a‖ • e ≤ a :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).1 le_rfl).1

/-- Every element `a` is bounded above by `‖a‖ • e`. -/
theorem le_norm_smul (he : IsOrderUnitNorm e) (a : E) : a ≤ ‖a‖ • e :=
  ((he.norm_le_iff a ‖a‖ (norm_nonneg a)).1 le_rfl).2

/-- An order-unit seminorm automatically separates points: `‖a‖ = 0` implies `a = 0`. -/
theorem eq_zero_of_norm_eq_zero (he : IsOrderUnitNorm e) {a : E} (ha : ‖a‖ = 0) : a = 0 := by
  have h := (he.norm_le_iff a 0 le_rfl).1 ha.le
  simp only [zero_smul, neg_zero] at h
  exact le_antisymm h.2 h.1

/-- Under `IsOrderUnitNorm e`, `‖a‖ = 0` if and only if `a = 0`. -/
theorem norm_eq_zero_iff (he : IsOrderUnitNorm e) {a : E} : ‖a‖ = 0 ↔ a = 0 :=
  ⟨he.eq_zero_of_norm_eq_zero, fun h => by simp [h]⟩

/-- Upgrade `SeminormedAddCommGroup E` to `NormedAddCommGroup E` using `he.eq_zero_of_norm_eq_zero`,
preserving the underlying `SeminormedAddCommGroup` definitionally. -/
noncomputable abbrev normedAddCommGroup (he : IsOrderUnitNorm e) : NormedAddCommGroup E :=
  { ‹SeminormedAddCommGroup E› with
    eq_of_dist_eq_zero := fun h => sub_eq_zero.1 <| he.eq_zero_of_norm_eq_zero <| by
      rwa [← dist_eq_norm] }

/-- The order unit is nonzero. -/
theorem ne_zero (he : IsOrderUnitNorm e) : e ≠ 0 := by
  intro h
  have := he.norm_eq_one
  simp [h] at this

/-- A space admitting an order-unit norm is nontrivial. -/
theorem nontrivial (he : IsOrderUnitNorm e) : Nontrivial E :=
  ⟨⟨e, 0, he.ne_zero⟩⟩

end Seminormed

section Ordered

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}

/-- The order unit is nonnegative. -/
theorem nonneg (he : IsOrderUnitNorm e) : 0 ≤ e := by
  have h : -e ≤ e := by
    simpa using ((he.norm_le_iff e 1 zero_le_one).1 he.norm_eq_one.le).1
  have h2 : 0 ≤ (2 : ℝ) • e := by
    rw [show (2 : ℝ) • e = e + e by rw [← one_add_one_eq_two, add_smul, one_smul]]
    exact neg_le_iff_add_nonneg.1 h
  have := smul_le_smul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2⁻¹)
  simpa using this

/-- **Norm recovery of positivity.** In an order-unit normed space, `0 ≤ a` if and only if
`‖‖a‖ • e - a‖ ≤ ‖a‖`. Thus the norm together with `e` completely determines the order. -/
theorem nonneg_iff_norm_sub_le (he : IsOrderUnitNorm e) (a : E) :
    0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖ := by
  rw [he.norm_le_iff _ _ (norm_nonneg a), sub_le_self_iff]
  refine ⟨fun ha => ⟨?_, ha⟩, And.right⟩
  rw [neg_smul]
  exact (neg_nonpos.2 (smul_nonneg (norm_nonneg a) he.nonneg)).trans
    (sub_nonneg.2 (he.le_norm_smul a))

/-- For `0 ≤ a`, the norm of `a` is the least scalar `r ≥ 0` with `a ≤ r • e`. -/
theorem norm_le_iff_of_nonneg (he : IsOrderUnitNorm e) {a : E} (ha : 0 ≤ a) {r : ℝ}
    (hr : 0 ≤ r) : ‖a‖ ≤ r ↔ a ≤ r • e := by
  rw [he.norm_le_iff a r hr]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rw [neg_smul]
  exact (neg_nonpos.2 (smul_nonneg hr he.nonneg)).trans ha

/-- Monotonicity of the norm on the positive cone: `0 ≤ a ≤ b` implies `‖a‖ ≤ ‖b‖`. -/
theorem norm_le_norm_of_nonneg (he : IsOrderUnitNorm e) {a b : E} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ :=
  (he.norm_le_iff_of_nonneg ha (norm_nonneg b)).2 (hab.trans (he.le_norm_smul b))

/-- The positive cone `{a : E | 0 ≤ a}` of an order-unit normed space is closed. -/
theorem isClosed_nonneg (he : IsOrderUnitNorm e) : IsClosed {a : E | 0 ≤ a} := by
  have h : {a : E | 0 ≤ a} = {a : E | ‖‖a‖ • e - a‖ ≤ ‖a‖} :=
    Set.ext fun a => he.nonneg_iff_norm_sub_le a
  rw [h]
  exact isClosed_le (((continuous_norm.smul continuous_const).sub continuous_id).norm)
    continuous_norm

/-- Every order-unit normed space has an `OrderClosedTopology`. -/
theorem orderClosedTopology (he : IsOrderUnitNorm e) : OrderClosedTopology E where
  isClosed_le' := by
    have h : {p : E × E | p.1 ≤ p.2} = (fun p : E × E => p.2 - p.1) ⁻¹' {a : E | 0 ≤ a} :=
      Set.ext fun p => sub_nonneg.symm
    rw [h]
    exact he.isClosed_nonneg.preimage (continuous_snd.sub continuous_fst)

omit [PosSMulMono ℝ E] in
/-- The closed ball of radius `1` centered at `e` is contained in the positive cone. -/
theorem closedBall_subset_nonneg (he : IsOrderUnitNorm e) :
    Metric.closedBall e 1 ⊆ {a : E | 0 ≤ a} := by
  intro a ha
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, he.norm_le_iff _ _ zero_le_one,
    one_smul] at ha
  exact (sub_le_self_iff e).1 ha.2

omit [PosSMulMono ℝ E] in
/-- The order unit `e` belongs to the topological interior of the positive cone. -/
theorem mem_interior_nonneg (he : IsOrderUnitNorm e) : e ∈ interior {a : E | 0 ≤ a} :=
  mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (Metric.closedBall_mem_nhds e one_pos) he.closedBall_subset_nonneg

/-- **Archimedean consequence of `IsOrderUnitNorm`.** If `a ≤ ε • e` for every `ε > 0`, then
`a ≤ 0`. -/
theorem le_zero_of_forall_pos_smul_le (he : IsOrderUnitNorm e) {a : E}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ε • e) : a ≤ 0 := by
  have := he.orderClosedTopology
  have htend : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • e) Filter.atTop (nhds (0 : E)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using h0.smul_const e
  exact ge_of_tendsto htend (Filter.Eventually.of_forall fun n => h _ (by positivity))

/-- Every element satisfying `IsOrderUnitNorm` is an Archimedean order unit. -/
theorem isArchimedeanOrderUnit (he : IsOrderUnitNorm e) : IsArchimedeanOrderUnit e where
  ne_zero := he.ne_zero
  exists_pos_le a := by
    refine ⟨‖a‖ + 1, by positivity, ?_, ?_⟩
    · have hle : (‖a‖ : ℝ) • e ≤ (‖a‖ + 1) • e :=
        smul_le_smul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) he.nonneg
      have hneg : -(‖a‖ + 1) • e ≤ -‖a‖ • e := by
        rw [neg_smul, neg_smul]
        exact neg_le_neg hle
      exact hneg.trans (he.neg_norm_smul_le a)
    · exact (he.le_norm_smul a).trans
        (smul_le_smul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) he.nonneg)
  le_zero_of_forall_pos_smul_le _ h := he.le_zero_of_forall_pos_smul_le h

/-- On an order-unit normed space, the ambient norm agrees with `orderUnitNorm e`. -/
theorem norm_eq_orderUnitNorm (he : IsOrderUnitNorm e) (a : E) : ‖a‖ = orderUnitNorm e a := by
  have ha := he.isArchimedeanOrderUnit
  refine le_antisymm ?_ ?_
  · exact (he.norm_le_iff a _ (IsArchimedeanOrderUnit.orderUnitNorm_nonneg e a)).2
      ⟨ha.neg_orderUnitNorm_smul_le a, ha.le_orderUnitNorm_smul a⟩
  · exact (ha.orderUnitNorm_le_iff a (norm_nonneg a)).2
      ⟨he.neg_norm_smul_le a, he.le_norm_smul a⟩

end Ordered

end IsOrderUnitNorm

/-- The norm constructed from an Archimedean order unit `e` satisfies `IsOrderUnitNorm e`. -/
theorem IsArchimedeanOrderUnit.isOrderUnitNorm {E : Type*} [AddCommGroup E] [PartialOrder E]
    [Module ℝ E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}
    (he : IsArchimedeanOrderUnit e) :
    @IsOrderUnitNorm E he.toNormedAddCommGroup.toSeminormedAddCommGroup he.toNormedSpace _ e := by
  let _ := he.toNormedAddCommGroup
  let _ := he.toNormedSpace
  exact
    { norm_eq_one := he.orderUnitNorm_self
      norm_le_iff := fun a _ hr => he.orderUnitNorm_le_iff a hr }

/-! ### Constructions preserving `IsOrderUnitNorm` -/

namespace IsOrderUnitNorm

/-- A submodule containing the order unit `e` inherits an order-unit norm with unit `⟨e, heS⟩`. -/
theorem submodule {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    {e : E} (he : IsOrderUnitNorm e) (S : Submodule ℝ E) (heS : e ∈ S) :
    IsOrderUnitNorm (⟨e, heS⟩ : S) where
  norm_eq_one := he.norm_eq_one
  norm_le_iff a r hr := he.norm_le_iff (a : E) r hr

/-- The binary product of two order-unit normed spaces carries an order-unit norm with unit
`(e, f)` under the `max` product norm and coordinatewise order. -/
theorem prod {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] {e : E} {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) :
    IsOrderUnitNorm (e, f) where
  norm_eq_one := by simp [Prod.norm_def, he.norm_eq_one, hf.norm_eq_one]
  norm_le_iff a r hr := by
    rw [Prod.norm_def, max_le_iff, he.norm_le_iff a.1 r hr, hf.norm_le_iff a.2 r hr,
      Prod.le_def, Prod.le_def]
    simp [and_assoc, and_left_comm]

/-- A finite nonempty `ℓ^∞` product of order-unit normed spaces carries an order-unit norm with
coordinatewise unit `fun i => e i`. -/
theorem pi {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, PartialOrder (E i)]
    {e : ∀ i, E i} (he : ∀ i, IsOrderUnitNorm (e i)) :
    IsOrderUnitNorm e where
  norm_eq_one := by
    have hnn : ∀ i, ‖e i‖₊ = 1 := fun i => NNReal.eq ((he i).norm_eq_one)
    simp [Pi.norm_def, hnn, Finset.sup_const Finset.univ_nonempty]
  norm_le_iff a r hr := by
    rw [Pi.norm_def]
    lift r to ℝ≥0 using hr
    rw [NNReal.coe_le_coe, Finset.sup_le_iff]
    simp only [Finset.mem_univ, forall_true_left, ← NNReal.coe_le_coe, coe_nnNorm,
      fun i => (he i).norm_le_iff (a i) r r.2, Pi.le_def]
    exact forall_and

/-- An isometric linear order equivalence transports `IsOrderUnitNorm` along the unit. -/
theorem map_linearIsometryEquiv {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
    {e : E} (he : IsOrderUnitNorm e) (L : E ≃ₗᵢ[ℝ] F) (hL : ∀ a b : E, L a ≤ L b ↔ a ≤ b) :
    IsOrderUnitNorm (L e) where
  norm_eq_one := (L.norm_map e).trans he.norm_eq_one
  norm_le_iff b r hr := by
    have hb : ‖b‖ = ‖L.symm b‖ := by rw [← L.norm_map (L.symm b), L.apply_symm_apply]
    rw [hb, he.norm_le_iff (L.symm b) r hr, ← hL, ← hL, map_smul, map_smul, L.apply_symm_apply]

/-- Every unital linear order isomorphism between order-unit normed spaces is norm-preserving. -/
theorem norm_map_of_orderIso {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (L : E ≃ₗ[ℝ] F)
    (hmono : ∀ a b : E, L a ≤ L b ↔ a ≤ b) (hunit : L e = f) (a : E) :
    ‖L a‖ = ‖a‖ := by
  refine le_antisymm ?_ ?_
  · rw [hf.norm_le_iff (L a) ‖a‖ (norm_nonneg a), ← hunit, ← map_smul, ← map_smul, hmono, hmono]
    exact ⟨he.neg_norm_smul_le a, he.le_norm_smul a⟩
  · rw [he.norm_le_iff a ‖L a‖ (norm_nonneg (L a)), ← hmono, ← hmono, map_smul, map_smul, hunit]
    exact ⟨hf.neg_norm_smul_le (L a), hf.le_norm_smul (L a)⟩

/-- Upgrade a unital linear order isomorphism between order-unit normed spaces to a
`LinearIsometryEquiv`. -/
def linearIsometryEquivOfOrderIso {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (L : E ≃ₗ[ℝ] F)
    (hmono : ∀ a b : E, L a ≤ L b ↔ a ≤ b) (hunit : L e = f) :
    E ≃ₗᵢ[ℝ] F :=
  { L with norm_map' := he.norm_map_of_orderIso hf L hmono hunit }

/-- Applying `he.linearIsometryEquivOfOrderIso` evaluates the underlying linear equivalence. -/
@[simp]
theorem linearIsometryEquivOfOrderIso_apply {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [PartialOrder F] {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (L : E ≃ₗ[ℝ] F) (hmono : ∀ a b : E, L a ≤ L b ↔ a ≤ b) (hunit : L e = f) (a : E) :
    he.linearIsometryEquivOfOrderIso hf L hmono hunit a = L a :=
  (rfl)

/-- Applying `(he.linearIsometryEquivOfOrderIso …).symm` evaluates `L.symm`. -/
@[simp]
theorem linearIsometryEquivOfOrderIso_symm_apply {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [PartialOrder F] {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (L : E ≃ₗ[ℝ] F) (hmono : ∀ a b : E, L a ≤ L b ↔ a ≤ b) (hunit : L e = f) (b : F) :
    (he.linearIsometryEquivOfOrderIso hf L hmono hunit).symm b = L.symm b :=
  (rfl)

end IsOrderUnitNorm

/-! ### Concrete order-unit normed spaces -/

/-- The real line `ℝ` with unit `1` is an order-unit normed space. -/
theorem isOrderUnitNorm_one_real : IsOrderUnitNorm (1 : ℝ) where
  norm_eq_one := norm_one
  norm_le_iff a r _ := by simp [Real.norm_eq_abs, abs_le]

/-- On a compact nonempty space `K`, `C(K, ℝ)` with constant function `1` and supremum norm is an
order-unit normed space. -/
theorem isOrderUnitNorm_one_continuousMap {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [Nonempty K] : IsOrderUnitNorm (1 : C(K, ℝ)) where
  norm_eq_one := norm_one
  norm_le_iff f r hr := by
    rw [ContinuousMap.norm_le _ hr]
    simp only [Real.norm_eq_abs, abs_le, ContinuousMap.le_def, ContinuousMap.coe_smul,
      ContinuousMap.coe_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, forall_and]

/-! ### Automatic continuity and norm of positive linear maps between order-unit spaces -/

namespace IsOrderUnitNorm

section PositiveMaps

variable {E F M : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
  [IsOrderedAddMonoid F] [PosSMulMono ℝ F]
  [FunLike M E F] [LinearMapClass M ℝ E F] [OrderHomClass M E F]
  {e : E} {f : F}

/-- Every positive linear map `T` between order-unit normed spaces satisfies
`‖T a‖ ≤ ‖T e‖ * ‖a‖`. -/
theorem norm_map_le_mul_norm (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M) (a : E) :
    ‖T a‖ ≤ ‖T e‖ * ‖a‖ := by
  rw [hf.norm_le_iff (T a) (‖T e‖ * ‖a‖) (mul_nonneg (norm_nonneg (T e)) (norm_nonneg a))]
  have h1 : -‖a‖ • T e ≤ T a := by
    simpa [map_neg, map_smul] using map_rel T (he.neg_norm_smul_le a)
  have h2 : T a ≤ ‖a‖ • T e := by
    simpa [map_smul] using map_rel T (he.le_norm_smul a)
  refine ⟨?_, ?_⟩
  · have hneg : -(‖T e‖ • f) ≤ -T e := neg_le_neg (hf.le_norm_smul (T e))
    calc -(‖T e‖ * ‖a‖) • f
        = ‖a‖ • -(‖T e‖ • f) := by rw [neg_smul, mul_comm, ← smul_smul, smul_neg]
      _ ≤ ‖a‖ • -T e := smul_le_smul_of_nonneg_left hneg (norm_nonneg a)
      _ = -‖a‖ • T e := by rw [smul_neg, neg_smul]
      _ ≤ T a := h1
  · calc T a ≤ ‖a‖ • T e := h2
      _ ≤ ‖a‖ • (‖T e‖ • f) := smul_le_smul_of_nonneg_left (hf.le_norm_smul (T e)) (norm_nonneg a)
      _ = (‖T e‖ * ‖a‖) • f := by rw [smul_smul, mul_comm]

/-- Every positive linear map `T` between order-unit normed spaces is `‖T e‖₊`-Lipschitz. -/
theorem lipschitzWith_of_orderHom (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M) :
    LipschitzWith ‖T e‖₊ T :=
  AddMonoidHomClass.lipschitz_of_bound_nnNorm T ‖T e‖₊ fun a => he.norm_map_le_mul_norm hf T a

/-- Every positive linear map `T` between order-unit normed spaces is automatically continuous. -/
theorem continuous_of_orderHom (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M) :
    Continuous T :=
  (he.lipschitzWith_of_orderHom hf T).continuous

/-- Promote a positive linear map between order-unit normed spaces to a
`PositiveContinuousLinearMap`. -/
def toPositiveContinuousLinearMap (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M) :
    E →P[ℝ] F where
  toPositiveLinearMap := .ofClass T
  cont := he.continuous_of_orderHom hf T

/-- Coercing `he.toPositiveContinuousLinearMap hf T` to a function recovers `T`. -/
@[simp]
theorem coe_toPositiveContinuousLinearMap (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : M) : ⇑(he.toPositiveContinuousLinearMap hf T) = T :=
  (rfl)

/-- Applying `he.toPositiveContinuousLinearMap hf T` evaluates `T`. -/
@[simp]
theorem toPositiveContinuousLinearMap_apply (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : M) (a : E) : he.toPositiveContinuousLinearMap hf T a = T a :=
  (rfl)

/-- The operator norm of a positive linear map `T` between order-unit normed spaces is `‖T e‖`. -/
theorem opNorm_toPositiveContinuousLinearMap (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : M) : ‖(he.toPositiveContinuousLinearMap hf T : E →L[ℝ] F)‖ = ‖T e‖ := by
  let T' : E →L[ℝ] F := he.toPositiveContinuousLinearMap hf T
  refine le_antisymm (T'.opNorm_le_bound (norm_nonneg (T e)) (he.norm_map_le_mul_norm hf T)) ?_
  simpa [T', he.norm_eq_one] using T'.le_opNorm e

/-- Every unital positive linear map (`T e = f`) between order-unit normed spaces has operator
norm `1` (in particular, it is contractive). -/
theorem opNorm_toPositiveContinuousLinearMap_of_map_unit (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : M) (hunit : T e = f) :
    ‖(he.toPositiveContinuousLinearMap hf T : E →L[ℝ] F)‖ = 1 := by
  rw [he.opNorm_toPositiveContinuousLinearMap hf T, hunit, hf.norm_eq_one]

end PositiveMaps

end IsOrderUnitNorm

end TauCeti.OrderUnit
