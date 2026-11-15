/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Map
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.GroupLike

/-!
# Completed bialgebra operations, primitive elements, and group-like elements

Let `A` be a bialgebra over a commutative ring `R` equipped with a multiplicative decreasing
filtration `F : AlgFiltration A`. When the counit vanishes on `F.ideal 1` and comultiplication
preserves filtration orders into `F.tensorProduct R F`, both maps extend to algebra homomorphisms
on the completion `F.completion`:

* `TauCeti.AlgFiltration.completedCounit`: the completed counit `F.completion →ₐ[R] R`, factoring
  through the order-`0` quotient `A ⧸ F.ideal 1`.
* `TauCeti.AlgFiltration.completedComul`: the completed comultiplication
  `F.completion →ₐ[R] (F.tensorProduct R F).completion`.
* `TauCeti.AlgFiltration.IsCompletedPrimitive`: elements `x` with completed comultiplication
  `includeLeftCompletion x + includeRightCompletion x`. Completed primitive elements form an
  `R`-submodule closed under associative commutators and have completed counit `0`.
* `TauCeti.AlgFiltration.IsCompletedGroupLike`: elements `u` with completed counit `1` and
  completed comultiplication `completedTensor u u`. Completed group-like elements form a
  submonoid closed under two-sided inverses.

When `A` is also a `ℚ`-algebra (possibly noncommutative, with no scalar-tower assumption relating
`ℚ` and `R`), `completedExp` and `completedLog` restrict to inverse bijections between completed
primitive elements of `F.completionIdeal 1` and completed group-like elements congruent to `1`
modulo `F.completionIdeal 1`. In particular, for completed primitive `x, y ∈ F.completionIdeal 1`,
`completedLog (completedExp x * completedExp y)` is again completed primitive.

## References

Formal dependencies: `TauCeti.AlgFiltration.completedExp`, `TauCeti.AlgFiltration.completedTensor`,
`Bialgebra.IsPrimitiveElem`, and `IsGroupLikeElem`.

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6, for primitive and group-like elements
  in completed bialgebras and their exponential correspondence.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

section Bialgebra

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  (F : TauCeti.AlgFiltration A)

/-- If the bialgebra counit vanishes on `F.ideal 1`, it descends from the order-`0` quotient to an
`R`-algebra homomorphism on the completion. -/
def completedCounit
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0) :
    F.completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (F.ideal 1) (Bialgebra.counitAlgHom R A) hcounit).comp
    (F.projectionₐ (R := R) 0)

/-- The completed counit agrees with the ordinary counit on any order-`0` representative. -/
theorem completedCounit_eq_of_mk_eq_projection
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    {x : F.completion} {a : A}
    (ha : Ideal.Quotient.mk (F.ideal 1) a = F.projection 0 x) :
    F.completedCounit R hcounit x = Coalgebra.counit (R := R) a := by
  simp only [completedCounit, AlgHom.comp_apply, projectionₐ_apply, ← ha]
  rfl

/-- On canonical images from `A`, the completed counit agrees with `Coalgebra.counit`. -/
@[simp]
theorem completedCounit_toCompletion
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0) (a : A) :
    F.completedCounit R hcounit (F.toCompletion a) = Coalgebra.counit (R := R) a :=
  F.completedCounit_eq_of_mk_eq_projection R hcounit (F.projection_toCompletion 0 a).symm

/-- The completed counit vanishes on the first completion ideal. -/
theorem completedCounit_eq_zero_of_mem_completionIdeal_one
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    {x : F.completion} (hx : x ∈ F.completionIdeal 1) :
    F.completedCounit R hcounit x = 0 := by
  have hx0 : F.projection 0 x = 0 := by
    simpa only [completionIdeal_succ, RingHom.mem_ker] using hx
  simp [completedCounit, hx0]

/-- Elements congruent to `1` modulo the first completion ideal have completed counit `1`. -/
theorem completedCounit_eq_one_of_sub_one_mem_completionIdeal_one
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    {u : F.completion} (hu : u - 1 ∈ F.completionIdeal 1) :
    F.completedCounit R hcounit u = 1 := by
  have h0 := F.completedCounit_eq_zero_of_mem_completionIdeal_one R hcounit hu
  rw [map_sub, map_one, sub_eq_zero] at h0
  exact h0

/-- When `F.ideal 1` contains the kernel of the counit, `F.completionIdeal 1` is precisely the
kernel of `completedCounit`. -/
theorem mem_completionIdeal_one_iff_completedCounit_eq_zero
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hker : ∀ a : A, Coalgebra.counit (R := R) a = 0 → a ∈ F.ideal 1)
    (x : F.completion) :
    x ∈ F.completionIdeal 1 ↔ F.completedCounit R hcounit x = 0 := by
  refine ⟨F.completedCounit_eq_zero_of_mem_completionIdeal_one R hcounit, fun hx => ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  rw [F.completedCounit_eq_of_mk_eq_projection R hcounit ha] at hx
  rw [completionIdeal_succ, RingHom.mem_ker, ← ha, Ideal.Quotient.eq_zero_iff_mem]
  exact hker a hx

/-- When `F.ideal 1` contains the kernel of the counit, congruence to `1` modulo
`F.completionIdeal 1` is equivalent to having completed counit `1`. -/
theorem sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hker : ∀ a : A, Coalgebra.counit (R := R) a = 0 → a ∈ F.ideal 1)
    (u : F.completion) :
    u - 1 ∈ F.completionIdeal 1 ↔ F.completedCounit R hcounit u = 1 := by
  rw [F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hcounit hker,
    map_sub, map_one, sub_eq_zero]

/-- If comultiplication preserves filtration orders into the total-degree filtration on
`A ⊗[R] A`, it extends to an `R`-algebra homomorphism into the completed tensor product. -/
noncomputable def completedComul
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)) :
    F.completion →ₐ[R] (F.tensorProduct R F).completion :=
  F.mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    fun k => hcomul (k + 1)

/-- Forgetting scalars in `completedComul` gives the underlying ring completion map. -/
@[simp]
theorem coe_completedComul
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)) :
    (F.completedComul R hcomul : F.completion →+* (F.tensorProduct R F).completion) =
      F.mapCompletion (F.tensorProduct R F) (Bialgebra.comulAlgHom R A : A →+* A ⊗[R] A)
        id monotone_id (fun k => hcomul (k + 1)) :=
  F.coe_mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    fun k => hcomul (k + 1)

/-- The order-`k` component of `completedComul` is induced by `Bialgebra.comulAlgHom`. -/
@[simp]
theorem projection_completedComul
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (k : ℕ) (x : F.completion) :
    (F.tensorProduct R F).projection k (F.completedComul R hcomul x) =
      Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
        (hcomul (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ _ _ _ monotone_id _ k x

/-- On canonical images from `A`, `completedComul` agrees with ordinary comultiplication. -/
@[simp]
theorem completedComul_toCompletion
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (a : A) :
    F.completedComul R hcomul (F.toCompletion a) =
      (F.tensorProduct R F).toCompletion (Coalgebra.comul (R := R) a) :=
  F.mapCompletionₐ_toCompletion _ _ _ monotone_id _ a

/-- Completed comultiplication preserves every completion filtration ideal. -/
theorem completedComul_mem_completionIdeal
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    {k : ℕ} {x : F.completion} (hx : x ∈ F.completionIdeal k) :
    F.completedComul R hcomul x ∈ (F.tensorProduct R F).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k => exact F.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

/-- When `A` is cocommutative, `completedComul` is invariant under completed factor exchange. -/
@[simp]
theorem completedTensorComm_completedComul [Coalgebra.IsCocomm R A]
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) :
    F.completedTensorComm R F (F.completedComul R hcomul x) = F.completedComul R hcomul x := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  rw [projection_completedTensorComm, projection_completedComul, ← ha]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply,
    AlgEquiv.coe_toAlgHom]
  congr 1
  rw [← AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.comm_toLinearEquiv,
    Coalgebra.comm_comul]

-- Multiplication of counits on `A ⊗[R] A`.
private def tensorCounit : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A)
    fun _ _ => Commute.all _ _

private theorem tensorCounit_tmul (a b : A) :
    tensorCounit R (a ⊗ₜ[R] b) = Coalgebra.counit (R := R) a * Coalgebra.counit (R := R) b := by
  simp [tensorCounit]

private theorem tensorCounit_comul (a : A) :
    tensorCounit R (Coalgebra.comul (R := R) a) = Coalgebra.counit (R := R) a := by
  have hlin : (tensorCounit R (A := A)).toLinearMap =
      (Coalgebra.counit (R := R)).comp
        ((TensorProduct.lid R A).toLinearMap.comp
          ((Coalgebra.counit (R := R)).rTensor A)) := by
    apply TensorProduct.ext'
    intro x y
    simp [tensorCounit_tmul, smul_eq_mul]
  have happ := congrArg (fun f : A ⊗[R] A →ₗ[R] R => f (Coalgebra.comul (R := R) a)) hlin
  simpa only [AlgHom.toLinearMap_apply, LinearMap.comp_apply,
    Coalgebra.rTensor_counit_comul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]
    using happ

private theorem tensorCounit_eq_zero_of_mem_tensorProduct_ideal_one
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (t : A ⊗[R] A) (ht : t ∈ (F.tensorProduct R F).ideal 1) :
    tensorCounit R t = 0 := by
  have hle : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
      (fun n => (F.ideal n).restrictScalars R) 1 ≤
      LinearMap.ker (tensorCounit R (A := A)).toLinearMap := by
    refine (tensorFiltrationTail_le_iff _ _).mpr fun p q hpq a ha b hb => ?_
    simp only [LinearMap.mem_ker, AlgHom.toLinearMap_apply, tensorCounit_tmul]
    rcases (by omega : 1 ≤ p ∨ 1 ≤ q) with hp | hq
    · rw [hcounit a (F.antitone hp ha), zero_mul]
    · rw [hcounit b (F.antitone hq hb), mul_zero]
  exact hle ((F.mem_tensorProduct_ideal_iff R F).mp ht)

-- Completed counit on `(F.tensorProduct R F).completion`.
private noncomputable def completedTensorCounit
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0) :
    (F.tensorProduct R F).completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ ((F.tensorProduct R F).ideal 1) (tensorCounit R)
    (F.tensorCounit_eq_zero_of_mem_tensorProduct_ideal_one R hcounit)).comp
    ((F.tensorProduct R F).projectionₐ (R := R) 0)

private theorem completedTensorCounit_completedComul
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) :
    F.completedTensorCounit R hcounit (F.completedComul R hcomul x) =
      F.completedCounit R hcounit x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  rw [F.completedCounit_eq_of_mk_eq_projection R hcounit ha]
  simp only [completedTensorCounit, AlgHom.comp_apply, projectionₐ_apply,
    projection_completedComul, ← ha, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    Bialgebra.comulAlgHom_apply]
  exact tensorCounit_comul R a

private theorem completedTensorCounit_includeLeftCompletion
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (x : F.completion) :
    F.completedTensorCounit R hcounit (F.includeLeftCompletion R F x) =
      F.completedCounit R hcounit x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  rw [F.completedCounit_eq_of_mk_eq_projection R hcounit ha]
  simp only [completedTensorCounit, AlgHom.comp_apply, projectionₐ_apply,
    projection_includeLeftCompletion, ← ha, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    Algebra.TensorProduct.includeLeft_apply]
  exact (tensorCounit_tmul R a 1).trans (by simp)

private theorem completedTensorCounit_includeRightCompletion
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (x : F.completion) :
    F.completedTensorCounit R hcounit (F.includeRightCompletion R F x) =
      F.completedCounit R hcounit x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  rw [F.completedCounit_eq_of_mk_eq_projection R hcounit ha]
  simp only [completedTensorCounit, AlgHom.comp_apply, projectionₐ_apply,
    projection_includeRightCompletion, ← ha, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    Algebra.TensorProduct.includeRight_apply]
  exact (tensorCounit_tmul R 1 a).trans (by simp)

/-- An element of the completed algebra is primitive if its completed comultiplication equals the
sum of its left and right completed tensor inclusions. -/
def IsCompletedPrimitive
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) : Prop :=
  F.completedComul R hcomul x =
    F.includeLeftCompletion R F x + F.includeRightCompletion R F x

/-- Defining characterization of `IsCompletedPrimitive`. -/
theorem isCompletedPrimitive_iff
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) :
    F.IsCompletedPrimitive R hcomul x ↔
      F.completedComul R hcomul x =
        F.includeLeftCompletion R F x + F.includeRightCompletion R F x :=
  Iff.rfl

/-- Characterization of `IsCompletedPrimitive` in terms of `completedTensor`. -/
theorem isCompletedPrimitive_iff_completedTensor
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) :
    F.IsCompletedPrimitive R hcomul x ↔
      F.completedComul R hcomul x =
        F.completedTensor R F x 1 + F.completedTensor R F 1 x := by
  simp [IsCompletedPrimitive]

namespace IsCompletedPrimitive

variable {R F}
variable {hcomul :
  ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)}

/-- Zero is completed primitive. -/
@[simp]
theorem zero : F.IsCompletedPrimitive R hcomul 0 := by
  simp [IsCompletedPrimitive]

/-- Canonical images of primitive elements of `A` are completed primitive. -/
theorem toCompletion {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    F.IsCompletedPrimitive R hcomul (F.toCompletion a) := by
  rw [isCompletedPrimitive_iff, completedComul_toCompletion, ha.comul_eq_tmul_add_tmul, map_add,
    includeLeftCompletion_toCompletion, includeRightCompletion_toCompletion, add_comm]

/-- Completed primitive elements are closed under addition. -/
theorem add {x y : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) (hy : F.IsCompletedPrimitive R hcomul y) :
    F.IsCompletedPrimitive R hcomul (x + y) := by
  rw [isCompletedPrimitive_iff] at hx hy ⊢
  rw [map_add, hx, hy, map_add, map_add, add_add_add_comm]

/-- Completed primitive elements are closed under negation. -/
theorem neg {x : F.completion} (hx : F.IsCompletedPrimitive R hcomul x) :
    F.IsCompletedPrimitive R hcomul (-x) := by
  rw [isCompletedPrimitive_iff] at hx ⊢
  rw [map_neg, hx, map_neg, map_neg, neg_add]

/-- Completed primitive elements are closed under subtraction. -/
theorem sub {x y : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) (hy : F.IsCompletedPrimitive R hcomul y) :
    F.IsCompletedPrimitive R hcomul (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

/-- Completed primitive elements are closed under `R`-scalar multiplication. -/
theorem smul (r : R) {x : F.completion} (hx : F.IsCompletedPrimitive R hcomul x) :
    F.IsCompletedPrimitive R hcomul (r • x) := by
  rw [isCompletedPrimitive_iff] at hx ⊢
  rw [map_smul, hx, map_smul, map_smul, smul_add]

/-- Completed primitive elements are closed under the associative commutator `x * y - y * x`. -/
theorem commutator {x y : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) (hy : F.IsCompletedPrimitive R hcomul y) :
    F.IsCompletedPrimitive R hcomul (x * y - y * x) := by
  rw [isCompletedPrimitive_iff] at hx hy ⊢
  have hxy := (F.commute_includeLeftCompletion_includeRightCompletion R F y x).eq
  have hyx := (F.commute_includeLeftCompletion_includeRightCompletion R F x y).eq
  rw [map_sub, map_mul, map_mul, hx, hy, map_sub, map_mul, map_mul,
    map_sub, map_mul, map_mul]
  simp only [add_mul, mul_add]
  rw [← hxy, ← hyx]
  abel

/-- Every completed primitive element has completed counit `0`. -/
theorem completedCounit_eq_zero
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    {x : F.completion} (hx : F.IsCompletedPrimitive R hcomul x) :
    F.completedCounit R hcounit x = 0 := by
  have h := congrArg (F.completedTensorCounit R hcounit) hx
  rw [completedTensorCounit_completedComul, map_add,
    completedTensorCounit_includeLeftCompletion,
    completedTensorCounit_includeRightCompletion] at h
  simpa only [add_sub_cancel_right, sub_self] using
    congrArg (· - F.completedCounit R hcounit x) h.symm

/-- Over a nontrivial base ring, no completed primitive element equals `1`. -/
theorem ne_one [Nontrivial R]
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    {x : F.completion} (hx : F.IsCompletedPrimitive R hcomul x) :
    x ≠ 1 := by
  rintro rfl
  simpa using hx.completedCounit_eq_zero hcounit

/-- When `F.ideal 1` contains the kernel of the counit, every completed primitive element lies in
`F.completionIdeal 1`. -/
theorem mem_completionIdeal_one
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hker : ∀ a : A, Coalgebra.counit (R := R) a = 0 → a ∈ F.ideal 1)
    {x : F.completion} (hx : F.IsCompletedPrimitive R hcomul x) :
    x ∈ F.completionIdeal 1 :=
  (F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hcounit hker x).mpr
    (hx.completedCounit_eq_zero hcounit)

end IsCompletedPrimitive

/-- Negation preserves and reflects `IsCompletedPrimitive`. -/
@[simp]
theorem isCompletedPrimitive_neg
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) :
    F.IsCompletedPrimitive R hcomul (-x) ↔ F.IsCompletedPrimitive R hcomul x :=
  ⟨fun hx => neg_neg x ▸ hx.neg, IsCompletedPrimitive.neg⟩

/-- The `R`-submodule of completed primitive elements in `F.completion`. -/
def completedPrimitiveSubmodule
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)) :
    Submodule R F.completion where
  carrier := {x | F.IsCompletedPrimitive R hcomul x}
  zero_mem' := IsCompletedPrimitive.zero
  add_mem' hx hy := hx.add hy
  smul_mem' r _ hx := hx.smul r

/-- Membership in `completedPrimitiveSubmodule` is `IsCompletedPrimitive`. -/
@[simp]
theorem mem_completedPrimitiveSubmodule
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) :
    x ∈ F.completedPrimitiveSubmodule R hcomul ↔ F.IsCompletedPrimitive R hcomul x :=
  Iff.rfl

/-- An element of the completed algebra is group-like if its completed counit is `1` and its
completed comultiplication equals the completed pure tensor with itself. -/
@[mk_iff]
structure IsCompletedGroupLike
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : F.completion) : Prop where
  /-- A completed group-like element has completed counit `1`. -/
  completedCounit_eq_one : F.completedCounit R hcounit u = 1
  /-- A completed group-like element has completed comultiplication `completedTensor u u`. -/
  completedComul_eq_completedTensor_self :
    F.completedComul R hcomul u = F.completedTensor R F u u

namespace IsCompletedGroupLike

variable {R F}
variable {hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0}
variable {hcomul :
  ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)}

/-- For an element congruent to `1` modulo `F.completionIdeal 1`, the counit condition in
`IsCompletedGroupLike` holds automatically. -/
theorem of_sub_one_mem_completionIdeal_one
    {u : F.completion} (hu₁ : u - 1 ∈ F.completionIdeal 1)
    (hu : F.completedComul R hcomul u = F.completedTensor R F u u) :
    F.IsCompletedGroupLike R hcounit hcomul u :=
  ⟨F.completedCounit_eq_one_of_sub_one_mem_completionIdeal_one R hcounit hu₁, hu⟩

/-- `1` is completed group-like. -/
@[simp]
theorem one : F.IsCompletedGroupLike R hcounit hcomul 1 where
  completedCounit_eq_one := map_one _
  completedComul_eq_completedTensor_self := by simp [completedTensor_apply]

/-- Over a nontrivial base ring, no completed group-like element is zero. -/
theorem ne_zero [Nontrivial R] {u : F.completion}
    (hu : F.IsCompletedGroupLike R hcounit hcomul u) : u ≠ 0 := by
  rintro rfl
  simpa using hu.completedCounit_eq_one

/-- Canonical images of group-like elements of `A` are completed group-like. -/
theorem toCompletion {a : A} (ha : IsGroupLikeElem R a) :
    F.IsCompletedGroupLike R hcounit hcomul (F.toCompletion a) where
  completedCounit_eq_one := by
    rw [completedCounit_toCompletion, ha.counit_eq_one]
  completedComul_eq_completedTensor_self := by
    rw [completedComul_toCompletion, ha.comul_eq_tmul_self, completedTensor_toCompletion]

/-- Completed group-like elements are closed under multiplication. -/
theorem mul {u v : F.completion}
    (hu : F.IsCompletedGroupLike R hcounit hcomul u)
    (hv : F.IsCompletedGroupLike R hcounit hcomul v) :
    F.IsCompletedGroupLike R hcounit hcomul (u * v) where
  completedCounit_eq_one := by
    rw [map_mul, hu.completedCounit_eq_one, hv.completedCounit_eq_one, mul_one]
  completedComul_eq_completedTensor_self := by
    rw [map_mul, hu.completedComul_eq_completedTensor_self,
      hv.completedComul_eq_completedTensor_self, completedTensor_mul]

/-- Completed group-like elements are closed under natural powers. -/
theorem pow {u : F.completion} (hu : F.IsCompletedGroupLike R hcounit hcomul u) (n : ℕ) :
    F.IsCompletedGroupLike R hcounit hcomul (u ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using one
  | succ n ih => simpa only [pow_succ] using ih.mul hu

/-- Two-sided inverses of completed group-like elements are completed group-like. -/
theorem of_mul_eq_one {u v : F.completion} (huv : u * v = 1) (hvu : v * u = 1)
    (hu : F.IsCompletedGroupLike R hcounit hcomul u) :
    F.IsCompletedGroupLike R hcounit hcomul v where
  completedCounit_eq_one :=
    left_inv_eq_right_inv (a := F.completedCounit R hcounit u)
      (by rw [← map_mul, hvu, map_one])
      (by rw [hu.completedCounit_eq_one, one_mul])
  completedComul_eq_completedTensor_self :=
    left_inv_eq_right_inv (a := F.completedComul R hcomul u)
      (by rw [← map_mul, hvu, map_one])
      (by
        rw [hu.completedComul_eq_completedTensor_self, ← completedTensor_mul, huv]
        simp [completedTensor_apply])

/-- When `F.ideal 1` contains the kernel of the counit, every completed group-like element is
congruent to `1` modulo `F.completionIdeal 1`. -/
theorem sub_one_mem_completionIdeal_one
    (hker : ∀ a : A, Coalgebra.counit (R := R) a = 0 → a ∈ F.ideal 1)
    {u : F.completion} (hu : F.IsCompletedGroupLike R hcounit hcomul u) :
    u - 1 ∈ F.completionIdeal 1 :=
  (F.sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one R hcounit hker u).mpr
    hu.completedCounit_eq_one

end IsCompletedGroupLike

/-- On elements congruent to `1` modulo `F.completionIdeal 1`, being completed group-like reduces
to the comultiplication equation. -/
theorem isCompletedGroupLike_iff_of_sub_one_mem_completionIdeal_one
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    {u : F.completion} (hu₁ : u - 1 ∈ F.completionIdeal 1) :
    F.IsCompletedGroupLike R hcounit hcomul u ↔
      F.completedComul R hcomul u = F.completedTensor R F u u :=
  ⟨IsCompletedGroupLike.completedComul_eq_completedTensor_self,
    IsCompletedGroupLike.of_sub_one_mem_completionIdeal_one hu₁⟩

/-- Two-sided inverses preserve and reflect `IsCompletedGroupLike`. -/
theorem isCompletedGroupLike_iff_of_mul_eq_one
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    {u v : F.completion} (huv : u * v = 1) (hvu : v * u = 1) :
    F.IsCompletedGroupLike R hcounit hcomul u ↔ F.IsCompletedGroupLike R hcounit hcomul v :=
  ⟨.of_mul_eq_one huv hvu, .of_mul_eq_one hvu huv⟩

/-- Unit inversion preserves and reflects `IsCompletedGroupLike`. -/
@[simp]
theorem isCompletedGroupLike_unitsInv
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : F.completionˣ) :
    F.IsCompletedGroupLike R hcounit hcomul (↑u⁻¹ : F.completion) ↔
      F.IsCompletedGroupLike R hcounit hcomul (u : F.completion) :=
  F.isCompletedGroupLike_iff_of_mul_eq_one R hcounit hcomul (by simp) (by simp)

/-- The submonoid of completed group-like elements in `F.completion`. -/
def completedGroupLikeSubmonoid
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)) :
    Submonoid F.completion where
  carrier := {u | F.IsCompletedGroupLike R hcounit hcomul u}
  one_mem' := .one
  mul_mem' := .mul

/-- Membership in `completedGroupLikeSubmonoid` is `IsCompletedGroupLike`. -/
@[simp]
theorem mem_completedGroupLikeSubmonoid
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : F.completion) :
    u ∈ F.completedGroupLikeSubmonoid R hcounit hcomul ↔
      F.IsCompletedGroupLike R hcounit hcomul u :=
  Iff.rfl

end Bialgebra

section Exp

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] [Algebra ℚ A]
  (F : TauCeti.AlgFiltration A)

/-- The completed left tensor inclusion commutes with `completedExp`. -/
@[simp]
theorem includeLeftCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeLeftCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeLeftCompletion R F x,
          F.includeLeftCompletion_mem_completionIdeal R F x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_includeLeftCompletion, projection_completedExp, projection_completedExp,
    projection_includeLeftCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp
    (Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1))
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A)
      (F.ideal_le_comap_includeLeft R F (k + 1))).toRingHom

/-- The completed right tensor inclusion commutes with `completedExp`. -/
@[simp]
theorem includeRightCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeRightCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeRightCompletion R F x,
          F.includeRightCompletion_mem_completionIdeal R F x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_includeRightCompletion, projection_completedExp, projection_completedExp,
    projection_includeRightCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp
    (Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1))
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)
      (F.ideal_le_comap_includeRight R F (k + 1))).toRingHom

/-- The completed pure tensor of two exponentials is the exponential of the sum of their left and
right completed inclusions. -/
theorem completedTensor_completedExp (x y : F.completionIdeal 1) :
    F.completedTensor R F (F.completedExp x) (F.completedExp y) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeLeftCompletion R F x + F.includeRightCompletion R F y,
          add_mem (F.includeLeftCompletion_mem_completionIdeal R F x.property)
            (F.includeRightCompletion_mem_completionIdeal R F y.property)⟩ := by
  rw [completedTensor_apply, includeLeftCompletion_completedExp,
    includeRightCompletion_completedExp]
  exact ((F.tensorProduct R F).completedExp_add
    ⟨F.includeLeftCompletion R F x,
      F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
    ⟨F.includeRightCompletion R F y,
      F.includeRightCompletion_mem_completionIdeal R F y.property⟩
    (F.commute_includeLeftCompletion_includeRightCompletion R F x y)).symm

/-- Completed comultiplication commutes with `completedExp`. -/
@[simp]
theorem completedComul_completedExp
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completionIdeal 1) :
    F.completedComul R hcomul (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.completedComul R hcomul x,
          F.completedComul_mem_completionIdeal R hcomul x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_completedComul, projection_completedExp, projection_completedExp,
    projection_completedComul]
  exact (F.isNilpotent_projection x.property k).map_exp
    (Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
      (hcomul (k + 1))).toRingHom

/-- Completed comultiplication commutes with `completedLog` on elements congruent to `1`. -/
@[simp]
theorem completedComul_completedLog
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.completedComul R hcomul (F.completedLog u) =
      (F.tensorProduct R F).completedLog
        ⟨F.completedComul R hcomul u, by
          simpa only [map_sub, map_one] using
            F.completedComul_mem_completionIdeal R hcomul u.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_completedComul, projection_completedLog, projection_completedLog,
    projection_completedComul]
  have hu : IsNilpotent (F.projection k u - 1) := by
    simpa only [map_sub, map_one] using F.isNilpotent_projection u.property k
  exact hu.map_log
    (Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
      (hcomul (k + 1))).toRingHom

/-- For `x ∈ F.completionIdeal 1`, `completedComul (completedExp x)` equals
`completedTensor (completedExp x) (completedExp x)` if and only if `x` is completed primitive. -/
theorem completedComul_completedExp_eq_completedTensor_iff
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completionIdeal 1) :
    F.completedComul R hcomul (F.completedExp x) =
        F.completedTensor R F (F.completedExp x) (F.completedExp x) ↔
      F.IsCompletedPrimitive R hcomul (x : F.completion) := by
  rw [completedComul_completedExp, completedTensor_completedExp, isCompletedPrimitive_iff]
  constructor
  · intro h
    have hlog := congrArg
      (fun t : {t : (F.tensorProduct R F).completion //
          t - 1 ∈ (F.tensorProduct R F).completionIdeal 1} =>
        (F.tensorProduct R F).completedLog t)
      (Subtype.ext h :
        (⟨(F.tensorProduct R F).completedExp _,
            (F.tensorProduct R F).completedExp_sub_one_mem _⟩ :
          {t : (F.tensorProduct R F).completion //
            t - 1 ∈ (F.tensorProduct R F).completionIdeal 1}) =
        ⟨(F.tensorProduct R F).completedExp _,
          (F.tensorProduct R F).completedExp_sub_one_mem _⟩)
    simpa only [completedLog_completedExp] using hlog
  · intro hx
    congr 1
    exact Subtype.ext hx

/-- For `x ∈ F.completionIdeal 1`, `completedExp x` is completed group-like if and only if `x` is
completed primitive. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completionIdeal 1) :
    F.IsCompletedGroupLike R hcounit hcomul (F.completedExp x) ↔
      F.IsCompletedPrimitive R hcomul (x : F.completion) :=
  (F.isCompletedGroupLike_iff_of_sub_one_mem_completionIdeal_one R hcounit hcomul
    (F.completedExp_sub_one_mem x)).trans
    (F.completedComul_completedExp_eq_completedTensor_iff R hcomul x)

/-- For `u` congruent to `1` modulo `F.completionIdeal 1`, `completedLog u` is completed primitive
if and only if `completedComul u = completedTensor u u`. -/
theorem isCompletedPrimitive_completedLog_iff_completedComul_eq
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.IsCompletedPrimitive R hcomul (F.completedLog u) ↔
      F.completedComul R hcomul u = F.completedTensor R F u u := by
  simpa only [completedExp_completedLog, Subtype.coe_mk] using
    (F.completedComul_completedExp_eq_completedTensor_iff R hcomul
      ⟨F.completedLog u, F.completedLog_mem u⟩).symm

/-- For `u` congruent to `1` modulo `F.completionIdeal 1`, `completedLog u` is completed primitive
if and only if `u` is completed group-like. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.IsCompletedPrimitive R hcomul (F.completedLog u) ↔
      F.IsCompletedGroupLike R hcounit hcomul (u : F.completion) :=
  (F.isCompletedPrimitive_completedLog_iff_completedComul_eq R hcomul u).trans
    (F.isCompletedGroupLike_iff_of_sub_one_mem_completionIdeal_one R hcounit hcomul
      u.property).symm

/-- Exponential coordinates restrict to an equivalence between completed primitive elements of
`F.completionIdeal 1` and completed group-like elements congruent to `1` modulo
`F.completionIdeal 1`. -/
noncomputable def completedExpPrimitiveEquiv
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)) :
    {x : F.completion // x ∈ F.completionIdeal 1 ∧ F.IsCompletedPrimitive R hcomul x} ≃
      {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧
        F.IsCompletedGroupLike R hcounit hcomul u} where
  toFun x :=
    ⟨F.completedExp ⟨x.1, x.2.1⟩, F.completedExp_sub_one_mem ⟨x.1, x.2.1⟩,
      (F.isCompletedGroupLike_completedExp_iff R hcounit hcomul ⟨x.1, x.2.1⟩).mpr x.2.2⟩
  invFun u :=
    ⟨F.completedLog ⟨u.1, u.2.1⟩, F.completedLog_mem ⟨u.1, u.2.1⟩,
      (F.isCompletedPrimitive_completedLog_iff R hcounit hcomul ⟨u.1, u.2.1⟩).mpr u.2.2⟩
  left_inv x := Subtype.ext (F.completedLog_completedExp ⟨x.1, x.2.1⟩)
  right_inv u := Subtype.ext (F.completedExp_completedLog ⟨u.1, u.2.1⟩)

/-- The forward map of `completedExpPrimitiveEquiv` is `completedExp`. -/
@[simp]
theorem coe_completedExpPrimitiveEquiv
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : {x : F.completion // x ∈ F.completionIdeal 1 ∧ F.IsCompletedPrimitive R hcomul x}) :
    (F.completedExpPrimitiveEquiv R hcounit hcomul x : F.completion) =
      F.completedExp ⟨x.1, x.2.1⟩ := (rfl)

/-- The inverse map of `completedExpPrimitiveEquiv` is `completedLog`. -/
@[simp]
theorem coe_completedExpPrimitiveEquiv_symm
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧
      F.IsCompletedGroupLike R hcounit hcomul u}) :
    ((F.completedExpPrimitiveEquiv R hcounit hcomul).symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.1⟩ := (rfl)

/-- When `F.ideal 1` contains the kernel of the counit, `completedExp` and `completedLog` identify
all completed primitive elements with all completed group-like elements. -/
noncomputable def completedExpPrimitiveEquivOfKer
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hker : ∀ a : A, Coalgebra.counit (R := R) a = 0 → a ∈ F.ideal 1)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)) :
    {x : F.completion // F.IsCompletedPrimitive R hcomul x} ≃
      {u : F.completion // F.IsCompletedGroupLike R hcounit hcomul u} where
  toFun x :=
    let hx := x.2.mem_completionIdeal_one hcounit hker
    ⟨F.completedExp ⟨x.1, hx⟩,
      (F.isCompletedGroupLike_completedExp_iff R hcounit hcomul ⟨x.1, hx⟩).mpr x.2⟩
  invFun u :=
    let hu := u.2.sub_one_mem_completionIdeal_one hker
    ⟨F.completedLog ⟨u.1, hu⟩,
      (F.isCompletedPrimitive_completedLog_iff R hcounit hcomul ⟨u.1, hu⟩).mpr u.2⟩
  left_inv x := Subtype.ext
    (F.completedLog_completedExp ⟨x.1, x.2.mem_completionIdeal_one hcounit hker⟩)
  right_inv u := Subtype.ext
    (F.completedExp_completedLog ⟨u.1, u.2.sub_one_mem_completionIdeal_one hker⟩)

/-- The forward map of `completedExpPrimitiveEquivOfKer` is `completedExp`. -/
@[simp]
theorem coe_completedExpPrimitiveEquivOfKer
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hker : ∀ a : A, Coalgebra.counit (R := R) a = 0 → a ∈ F.ideal 1)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : {x : F.completion // F.IsCompletedPrimitive R hcomul x}) :
    (F.completedExpPrimitiveEquivOfKer R hcounit hker hcomul x : F.completion) =
      F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hcounit hker⟩ := (rfl)

/-- The inverse map of `completedExpPrimitiveEquivOfKer` is `completedLog`. -/
@[simp]
theorem coe_completedExpPrimitiveEquivOfKer_symm
    (hcounit : ∀ a ∈ F.ideal 1, Coalgebra.counit (R := R) a = 0)
    (hker : ∀ a : A, Coalgebra.counit (R := R) a = 0 → a ∈ F.ideal 1)
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (u : {u : F.completion // F.IsCompletedGroupLike R hcounit hcomul u}) :
    ((F.completedExpPrimitiveEquivOfKer R hcounit hker hcomul).symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.sub_one_mem_completionIdeal_one hker⟩ := (rfl)

/-- The product of two completed exponentials is congruent to `1` modulo `F.completionIdeal 1`. -/
theorem completedExp_mul_completedExp_sub_one_mem (x y : F.completionIdeal 1) :
    F.completedExp x * F.completedExp y - 1 ∈ F.completionIdeal 1 := by
  simpa only [mul_sub, mul_one, sub_add_sub_cancel] using
    add_mem ((F.completionIdeal 1).mul_mem_left (F.completedExp x) (F.completedExp_sub_one_mem y))
      (F.completedExp_sub_one_mem x)

/-- Baker–Campbell–Hausdorff closure in a completed filtered bialgebra: if `x` and `y` are
completed primitive elements of `F.completionIdeal 1`, then
`completedLog (completedExp x * completedExp y)` is again completed primitive. -/
theorem isCompletedPrimitive_completedLog_completedExp_mul
    (hcomul :
      ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    {x y : F.completionIdeal 1}
    (hx : F.IsCompletedPrimitive R hcomul (x : F.completion))
    (hy : F.IsCompletedPrimitive R hcomul (y : F.completion)) :
    F.IsCompletedPrimitive R hcomul
      (F.completedLog ⟨F.completedExp x * F.completedExp y,
        F.completedExp_mul_completedExp_sub_one_mem x y⟩) := by
  rw [F.isCompletedPrimitive_completedLog_iff_completedComul_eq R hcomul]
  simp only [map_mul, (F.completedComul_completedExp_eq_completedTensor_iff R hcomul x).mpr hx,
    (F.completedComul_completedExp_eq_completedTensor_iff R hcomul y).mpr hy, completedTensor_mul]

end Exp

end TauCeti.AlgFiltration
