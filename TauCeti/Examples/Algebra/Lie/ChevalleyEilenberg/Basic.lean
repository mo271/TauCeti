/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.LowDegree
public import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# Explicit Chevalley–Eilenberg cohomology computations: abelian line and `sl₂`

This file computes the Chevalley–Eilenberg cohomology of two standard Lie algebras with trivial
coefficients using `TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.Basic` and
`TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.LowDegree`:

1. **One-dimensional abelian Lie algebra.** For any abelian Lie algebra `L` over a commutative ring
   `R` admitting a single-element basis `b : Basis (Fin 1) R L`, and any trivial `L`-module `M`,
   `H⁰(L, M) ≃ₗ[R] M`, `H¹(L, M) ≃ₗ[R] M`, and `H^q(L, M) = 0` (`Subsingleton`) for all `q ≥ 2`.
   We also instantiate this on the concrete one-dimensional abelian Lie algebra `AbelianLine R`
   with trivial coefficients `TrivialLieModule R (AbelianLine R) R`.

2. **Three-dimensional simple Lie algebra `sl₂(R)`.** Over any commutative ring `R` in which `2`
   is a unit, and for any trivial `sl (Fin 2) R`-module `M`:
   * `sl (Fin 2) R` is perfect (`derived_sl2_eq_top`): `⁅⊤, ⊤⁆ = ⊤`.
   * The degree-`1` differential `d R (sl (Fin 2) R) M 1` is bijective (`dOne_sl2_bijective`),
     and consequently `d R (sl (Fin 2) R) M 2 = 0` (`dTwo_sl2_eq_zero`).
   * `H⁰(sl₂, M) ≃ₗ[R] M`, `Subsingleton (H¹(sl₂, M))`, `Subsingleton (H²(sl₂, M))`,
     `H³(sl₂, M) ≃ₗ[R] M`, and `Subsingleton (H^q(sl₂, M))` for all `q ≥ 4`.

For the relative cohomology of `(sl₂(ℝ), so(2), SO(2))` with coefficients `ℂ`, see
`TauCeti.Examples.Algebra.Lie.ChevalleyEilenberg.RelativeSl2`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), §22–§28.
-/

public section

open CategoryTheory LieAlgebra Module

namespace TauCeti.Examples.ChevalleyEilenberg

open TauCeti.LieModule.Cohomology

/-! ### Top-degree and vanishing helpers for alternating maps on a free finite module -/

section AlternatingHelpers

variable {R V M : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]

/-- Evaluation at a basis identifies top-degree alternating maps `V [⋀^Fin n]→ₗ[R] M` with `M`. -/
noncomputable def alternatingMapTopEquiv {n : ℕ} (b : Basis (Fin n) R V) :
    (V [⋀^Fin n]→ₗ[R] M) ≃ₗ[R] M where
  toFun ω := ω b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := b.det.smulRight m
  left_inv ω := by
    refine Basis.ext_alternating b fun i hi ↦ ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change (b.det.smulRight (ω b)) (b ∘ σ) = ω (b ∘ σ)
    have hdet : b.det (b ∘ σ) = Equiv.Perm.sign σ • (1 : R) := by
      rw [AlternatingMap.map_perm, Basis.det_self]
    rw [AlternatingMap.smulRight_apply, hdet, AlternatingMap.map_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  right_inv m := by
    simp [AlternatingMap.smulRight_apply, Basis.det_self]

@[simp]
theorem alternatingMapTopEquiv_apply {n : ℕ} (b : Basis (Fin n) R V) (ω : V [⋀^Fin n]→ₗ[R] M) :
    alternatingMapTopEquiv b ω = ω b := (rfl)

/-- Every alternating `q`-map vanishes when `V` has a basis of size `n < q`. -/
theorem subsingleton_alternatingMap_of_basis_lt {n q : ℕ} (b : Basis (Fin n) R V) (h : n < q) :
    Subsingleton (V [⋀^Fin q]→ₗ[R] M) :=
  ⟨fun f g ↦ Basis.ext_alternating b fun i hi ↦ by
    have hcard := Fintype.card_le_of_injective i hi
    simp only [Fintype.card_fin] at hcard
    omega⟩

end AlternatingHelpers

/-! ### Example 1: One-dimensional abelian Lie algebra -/

section AbelianOneDim

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [LieModule.IsTrivial L M]

/-- For an abelian Lie algebra `L` and trivial `L`-module `M`, `H⁰(L, M) ≃ₗ[R] M`. -/
noncomputable def abelianCohomologyZeroEquiv : cohomology R L M 0 ≃ₗ[R] M :=
  cohomologyZeroEquivOfIsTrivial R L M

/-- For a one-dimensional abelian Lie algebra `L` with basis `b : Basis (Fin 1) R L` and trivial
`L`-module `M`, `H¹(L, M) ≃ₗ[R] M`. -/
noncomputable def abelianOneDimCohomologyOneEquiv (b : Basis (Fin 1) R L) :
    cohomology R L M 1 ≃ₗ[R] M := by
  have hd1 : d R L M 1 = 0 := by
    ext ω v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, LinearMap.zero_apply, zero_apply, d_one_apply_of_isTrivial,
      LieModule.IsTrivial.trivial (v 0) (v 1)]
    rw [ω.map_coord_zero (0 : Fin 1) (m := ![(0 : L)]) rfl, neg_zero]
  have hker : LinearMap.ker (d R L M 1) = ⊤ := LinearMap.ker_eq_top.mpr hd1
  have hrange : LinearMap.range (dToCycles R L M 0) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨ω, rfl⟩
    rw [Submodule.mem_bot]
    apply Subtype.ext
    rw [dToCycles_coe, d_zero_eq_zero_of_isTrivial]
    rfl
  exact (cohomologySuccEquiv R L M 0) ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ hrange) ≪≫ₗ
    (LinearEquiv.ofTop _ hker) ≪≫ₗ
    alternatingMapTopEquiv b

omit [IsLieAbelian L] [LieModule.IsTrivial L M] in
/-- For a Lie algebra `L` with basis `b : Basis (Fin 1) R L`, `H^q(L, M)` is subsingleton for
every `q ≥ 2`. -/
theorem abelianOneDim_subsingleton_cohomology (b : Basis (Fin 1) R L) {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (cohomology R L M q) := by
  have : Subsingleton (L [⋀^Fin q]→ₗ[R] M) :=
    subsingleton_alternatingMap_of_basis_lt b (by omega)
  exact subsingleton_cohomology_of_subsingleton

end AbelianOneDim

/-- Wrapper giving `R` the structure of a one-dimensional abelian Lie algebra over itself without
creating any global `LieRing` diamond on `R`. -/
@[ext]
structure AbelianLine (R : Type*) where
  /-- The underlying scalar in `R`. -/
  val : R

namespace AbelianLine

variable (R : Type*) [CommRing R]

instance : AddCommGroup (AbelianLine R) where
  add x y := ⟨x.val + y.val⟩
  add_assoc _ _ _ := AbelianLine.ext (add_assoc _ _ _)
  zero := ⟨0⟩
  zero_add _ := AbelianLine.ext (zero_add _)
  add_zero _ := AbelianLine.ext (add_zero _)
  neg x := ⟨-x.val⟩
  neg_add_cancel _ := AbelianLine.ext (neg_add_cancel _)
  add_comm _ _ := AbelianLine.ext (add_comm _ _)
  sub x y := ⟨x.val - y.val⟩
  sub_eq_add_neg _ _ := AbelianLine.ext (sub_eq_add_neg _ _)
  nsmul n x := ⟨n • x.val⟩
  nsmul_zero x := AbelianLine.ext (AddMonoid.nsmul_zero x.val)
  nsmul_succ n x := AbelianLine.ext (AddMonoid.nsmul_succ n x.val)
  zsmul z x := ⟨z • x.val⟩
  zsmul_zero' x := AbelianLine.ext (SubNegMonoid.zsmul_zero' x.val)
  zsmul_succ' n x := AbelianLine.ext (SubNegMonoid.zsmul_succ' n x.val)
  zsmul_neg' n x := AbelianLine.ext (SubNegMonoid.zsmul_neg' n x.val)

instance : Module R (AbelianLine R) where
  smul r x := ⟨r * x.val⟩
  one_smul _ := AbelianLine.ext (one_mul _)
  mul_smul _ _ _ := AbelianLine.ext (mul_assoc _ _ _)
  smul_zero _ := AbelianLine.ext (mul_zero _)
  smul_add _ _ _ := AbelianLine.ext (mul_add _ _ _)
  add_smul _ _ _ := AbelianLine.ext (add_mul _ _ _)
  zero_smul _ := AbelianLine.ext (zero_mul _)

instance : Bracket (AbelianLine R) (AbelianLine R) := ⟨fun _ _ ↦ 0⟩

instance : LieRing (AbelianLine R) where
  add_lie _ _ _ := by change (0 : AbelianLine R) = 0 + 0; simp
  lie_add _ _ _ := by change (0 : AbelianLine R) = 0 + 0; simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by change (0 : AbelianLine R) = 0 + 0; simp

instance : LieAlgebra R (AbelianLine R) where
  lie_smul _ _ _ := by change (0 : AbelianLine R) = _ • 0; simp

instance : IsLieAbelian (AbelianLine R) := ⟨fun _ _ ↦ rfl⟩

/-- The canonical basis of `AbelianLine R` indexed by `Fin 1`. -/
noncomputable def basis : Basis (Fin 1) R (AbelianLine R) :=
  Basis.ofEquivFun
    { toFun := fun x _ ↦ x.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun v ↦ ⟨v 0⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun v ↦ by ext i; fin_cases i; rfl }

/-- `H⁰(AbelianLine R, R) ≃ₗ[R] R`. -/
noncomputable def cohomologyZeroEquiv :
    cohomology R (AbelianLine R) (TrivialLieModule R (AbelianLine R) R) 0 ≃ₗ[R] R :=
  abelianCohomologyZeroEquiv ≪≫ₗ TrivialLieModule.equiv R (AbelianLine R) R

/-- `H¹(AbelianLine R, R) ≃ₗ[R] R`. -/
noncomputable def cohomologyOneEquiv :
    cohomology R (AbelianLine R) (TrivialLieModule R (AbelianLine R) R) 1 ≃ₗ[R] R :=
  abelianOneDimCohomologyOneEquiv (basis R) ≪≫ₗ TrivialLieModule.equiv R (AbelianLine R) R

/-- `H^q(AbelianLine R, R) = 0` (`Subsingleton`) for all `q ≥ 2`. -/
theorem subsingleton_cohomology {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (cohomology R (AbelianLine R) (TrivialLieModule R (AbelianLine R) R) q) :=
  abelianOneDim_subsingleton_cohomology (basis R) hq

end AbelianLine

/-! ### Example 2: `sl₂(R)` with trivial coefficients (`2` invertible) -/

section Sl2

variable (R : Type*) [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [LieRingModule (SpecialLinear.sl (Fin 2) R) M]
variable [LieModule R (SpecialLinear.sl (Fin 2) R) M]
variable [LieModule.IsTrivial (SpecialLinear.sl (Fin 2) R) M]

/-- When `2` is a unit in `R`, `sl (Fin 2) R` is perfect: every element lies in the derived ideal
`⁅⊤, ⊤⁆`. -/
theorem derived_sl2_eq_top (h2 : IsUnit (2 : R)) :
    ⁅(⊤ : LieIdeal R (SpecialLinear.sl (Fin 2) R)),
      (⊤ : LieIdeal R (SpecialLinear.sl (Fin 2) R))⁆ = ⊤ := by
  obtain ⟨u, hu⟩ := h2
  have hu2 : (u⁻¹ : Rˣ).val * 2 = 1 := by
    rw [← hu]
    exact u.inv_mul
  rw [eq_top_iff]
  intro A _
  have hmem : ∀ k : Fin 3, slFinTwoBasis R k ∈
      ⁅(⊤ : LieIdeal R (SpecialLinear.sl (Fin 2) R)),
        (⊤ : LieIdeal R (SpecialLinear.sl (Fin 2) R))⁆ := by
    intro k
    fin_cases k
    · change slFinTwoBasis R 0 ∈ _
      have h0 : slFinTwoBasis R 0 = (u⁻¹ : Rˣ).val • ⁅slFinTwoBasis R 2, slFinTwoBasis R 0⁆ := by
        rw [lie_slFinTwoBasis_two_zero, smul_smul, hu2, one_smul]
      rw [h0]
      exact Submodule.smul_mem _ _ (LieSubmodule.lie_mem_lie trivial trivial)
    · change slFinTwoBasis R 1 ∈ _
      have h1 : slFinTwoBasis R 1 =
          -((u⁻¹ : Rˣ).val • ⁅slFinTwoBasis R 2, slFinTwoBasis R 1⁆) := by
        rw [lie_slFinTwoBasis_two_one, smul_neg, smul_smul, hu2, one_smul, neg_neg]
      rw [h1]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (LieSubmodule.lie_mem_lie trivial trivial))
    · change slFinTwoBasis R 2 ∈ _
      rw [← lie_slFinTwoBasis_zero_one]
      exact LieSubmodule.lie_mem_lie trivial trivial
  rw [← (slFinTwoBasis R).sum_repr A]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hmem k)

private noncomputable def sl2InvLinear (h2 : IsUnit (2 : R))
    (ω : SpecialLinear.sl (Fin 2) R [⋀^Fin 2]→ₗ[R] M) :
    SpecialLinear.sl (Fin 2) R →ₗ[R] M :=
  (slFinTwoBasis R).constr R
    ![-((h2.unit⁻¹ : Rˣ).val • ω ![slFinTwoBasis R 2, slFinTwoBasis R 0]),
      (h2.unit⁻¹ : Rˣ).val • ω ![slFinTwoBasis R 2, slFinTwoBasis R 1],
      -ω ![slFinTwoBasis R 0, slFinTwoBasis R 1]]

variable (M) in
/-- Explicit inverse to the degree-`1` Chevalley–Eilenberg differential `d 1` of `sl (Fin 2) R`
with trivial coefficients when `2` is a unit in `R`. -/
noncomputable def dOneSl2Inv (h2 : IsUnit (2 : R)) :
    (SpecialLinear.sl (Fin 2) R [⋀^Fin 2]→ₗ[R] M) →ₗ[R]
      (SpecialLinear.sl (Fin 2) R [⋀^Fin 1]→ₗ[R] M) where
  toFun ω :=
    { toFun := fun v ↦ sl2InvLinear R h2 ω (v 0)
      map_update_add' := fun _ i x y ↦ by
        fin_cases i
        simp [map_add]
      map_update_smul' := fun _ i c x ↦ by
        fin_cases i
        simp [map_smul]
      map_eq_zero_of_eq' := fun _ i j _ hne ↦ by
        fin_cases i; fin_cases j; exact (hne rfl).elim }
  map_add' ω₁ ω₂ := by
    refine AlternatingMap.ext fun v ↦ ?_
    have heq : sl2InvLinear R h2 (ω₁ + ω₂) = sl2InvLinear R h2 ω₁ + sl2InvLinear R h2 ω₂ := by
      refine (slFinTwoBasis R).ext fun k ↦ ?_
      simp only [sl2InvLinear, LinearMap.add_apply, Basis.constr_basis]
      fin_cases k
      · change -((h2.unit⁻¹ : Rˣ).val • (ω₁ + ω₂) _) =
          -((h2.unit⁻¹ : Rˣ).val • ω₁ _) + -((h2.unit⁻¹ : Rˣ).val • ω₂ _)
        rw [add_apply, smul_add, neg_add]
      · change (h2.unit⁻¹ : Rˣ).val • (ω₁ + ω₂) _ =
          (h2.unit⁻¹ : Rˣ).val • ω₁ _ + (h2.unit⁻¹ : Rˣ).val • ω₂ _
        rw [add_apply, smul_add]
      · change -(ω₁ + ω₂) _ = -ω₁ _ + -ω₂ _
        rw [add_apply, neg_add]
    exact congrArg (fun f : SpecialLinear.sl (Fin 2) R →ₗ[R] M ↦ f (v 0)) heq
  map_smul' r ω := by
    refine AlternatingMap.ext fun v ↦ ?_
    have heq : sl2InvLinear R h2 (r • ω) = r • sl2InvLinear R h2 ω := by
      refine (slFinTwoBasis R).ext fun k ↦ ?_
      simp only [sl2InvLinear, LinearMap.smul_apply, Basis.constr_basis]
      fin_cases k
      · change -((h2.unit⁻¹ : Rˣ).val • (r • ω) _) = r • -((h2.unit⁻¹ : Rˣ).val • ω _)
        rw [smul_apply, smul_neg, smul_comm]
      · change (h2.unit⁻¹ : Rˣ).val • (r • ω) _ = r • ((h2.unit⁻¹ : Rˣ).val • ω _)
        rw [smul_apply, smul_comm]
      · change -(r • ω) _ = r • -ω _
        rw [smul_apply, smul_neg]
    exact congrArg (fun f : SpecialLinear.sl (Fin 2) R →ₗ[R] M ↦ f (v 0)) heq

/-- When `2` is a unit in `R`, the degree-`1` differential `d 1 : C¹(sl₂, M) → C²(sl₂, M)` is
bijective for every trivial `sl₂`-module `M`. -/
theorem dOne_sl2_bijective (h2 : IsUnit (2 : R)) :
    Function.Bijective (d R (SpecialLinear.sl (Fin 2) R) M 1) := by
  have hu2 : (h2.unit⁻¹ : Rˣ).val * (2 : R) = 1 := by
    simp
  have h2u : (2 : R) * (h2.unit⁻¹ : Rˣ).val = 1 := by rw [mul_comm, hu2]
  have hsmul1 (α : SpecialLinear.sl (Fin 2) R [⋀^Fin 1]→ₗ[R] M) (c : R)
      (x : SpecialLinear.sl (Fin 2) R) : α ![c • x] = c • α ![x] := by
    have hupd : Function.update ![x] 0 (c • x) = ![c • x] := by ext k; fin_cases k; rfl
    rw [← hupd, α.map_update_smul]
    have hupd' : Function.update ![x] 0 x = ![x] := by ext k; fin_cases k; rfl
    rw [hupd']
  have hleft : Function.LeftInverse (dOneSl2Inv R M h2)
      (d R (SpecialLinear.sl (Fin 2) R) M 1) := by
    intro α
    refine Basis.ext_alternating (slFinTwoBasis R) fun i _ ↦ ?_
    have hi : (fun k : Fin 1 ↦ slFinTwoBasis R (i k)) = ![slFinTwoBasis R (i 0)] := by
      ext t; fin_cases t; rfl
    rw [hi]
    change sl2InvLinear R h2 (d R (SpecialLinear.sl (Fin 2) R) M 1 α) (slFinTwoBasis R (i 0)) =
      α ![slFinTwoBasis R (i 0)]
    rw [sl2InvLinear, Basis.constr_basis]
    generalize i 0 = k
    fin_cases k
    · change -((h2.unit⁻¹ : Rˣ).val •
          d R (SpecialLinear.sl (Fin 2) R) M 1 α ![slFinTwoBasis R 2, slFinTwoBasis R 0]) =
        α ![slFinTwoBasis R 0]
      rw [d_one_apply_of_isTrivial, lie_slFinTwoBasis_two_zero, hsmul1, smul_neg, neg_neg,
        smul_smul, hu2, one_smul]
    · change (h2.unit⁻¹ : Rˣ).val •
          d R (SpecialLinear.sl (Fin 2) R) M 1 α ![slFinTwoBasis R 2, slFinTwoBasis R 1] =
        α ![slFinTwoBasis R 1]
      rw [d_one_apply_of_isTrivial, lie_slFinTwoBasis_two_one, ← neg_smul (2 : R), hsmul1,
        neg_smul, neg_neg, smul_smul, hu2, one_smul]
    · change -(d R (SpecialLinear.sl (Fin 2) R) M 1 α ![slFinTwoBasis R 0, slFinTwoBasis R 1]) =
        α ![slFinTwoBasis R 2]
      rw [d_one_apply_of_isTrivial, lie_slFinTwoBasis_zero_one, neg_neg]
  have hright : Function.RightInverse (dOneSl2Inv R M h2)
      (d R (SpecialLinear.sl (Fin 2) R) M 1) := by
    intro ω
    refine Basis.ext_alternating (slFinTwoBasis R) fun i hi ↦ ?_
    have hi_vec : (fun k : Fin 2 ↦ slFinTwoBasis R (i k)) =
        ![slFinTwoBasis R (i 0), slFinTwoBasis R (i 1)] := by
      ext t; fin_cases t <;> rfl
    rw [hi_vec, d_one_apply_of_isTrivial]
    have h01 : i 0 ≠ i 1 := fun h ↦ by
      have := hi h
      exact absurd this (by decide)
    have hcases : (i 0 = 0 ∧ i 1 = 1) ∨ (i 0 = 1 ∧ i 1 = 0) ∨ (i 0 = 2 ∧ i 1 = 0) ∨
        (i 0 = 0 ∧ i 1 = 2) ∨ (i 0 = 2 ∧ i 1 = 1) ∨ (i 0 = 1 ∧ i 1 = 2) := by
      have h : ∀ a b : Fin 3, a ≠ b →
          (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 0) ∨
          (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by decide
      exact h (i 0) (i 1) h01
    have hswap (x y : SpecialLinear.sl (Fin 2) R) : ω ![y, x] = -ω ![x, y] := by
      have hs := ω.map_swap ![x, y] (show (0 : Fin 2) ≠ 1 by decide)
      have hcomp : ![x, y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
        ext k; fin_cases k <;> rfl
      rwa [hcomp] at hs
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb]
    · rw [lie_slFinTwoBasis_zero_one]
      change -(sl2InvLinear R h2 ω (slFinTwoBasis R 2)) = _
      rw [sl2InvLinear, Basis.constr_basis]; simp
    · rw [← lie_skew (slFinTwoBasis R 1), lie_slFinTwoBasis_zero_one,
        show -slFinTwoBasis R 2 = (-1 : R) • slFinTwoBasis R 2 by simp, hsmul1]
      change -((-1 : R) • sl2InvLinear R h2 ω (slFinTwoBasis R 2)) = _
      rw [sl2InvLinear, Basis.constr_basis, hswap (slFinTwoBasis R 0) (slFinTwoBasis R 1)]
      simp
    · rw [lie_slFinTwoBasis_two_zero, hsmul1]
      change -((2 : R) • sl2InvLinear R h2 ω (slFinTwoBasis R 0)) = _
      rw [sl2InvLinear, Basis.constr_basis]
      simp [smul_neg, smul_smul, h2u]
    · rw [← lie_skew (slFinTwoBasis R 0), lie_slFinTwoBasis_two_zero, ← neg_smul (2 : R), hsmul1]
      change -((-2 : R) • sl2InvLinear R h2 ω (slFinTwoBasis R 0)) = _
      rw [sl2InvLinear, Basis.constr_basis, hswap (slFinTwoBasis R 2) (slFinTwoBasis R 0)]
      simp [neg_smul, smul_neg, smul_smul, h2u]
    · rw [lie_slFinTwoBasis_two_one, ← neg_smul (2 : R), hsmul1]
      change -((-2 : R) • sl2InvLinear R h2 ω (slFinTwoBasis R 1)) = _
      rw [sl2InvLinear, Basis.constr_basis]
      simp [neg_smul, smul_smul, h2u]
    · rw [← lie_skew (slFinTwoBasis R 1), lie_slFinTwoBasis_two_one, neg_neg, hsmul1]
      change -((2 : R) • sl2InvLinear R h2 ω (slFinTwoBasis R 1)) = _
      rw [sl2InvLinear, Basis.constr_basis, hswap (slFinTwoBasis R 2) (slFinTwoBasis R 1)]
      simp [smul_smul, h2u]
  exact ⟨hleft.injective, hright.surjective⟩

/-- Because `d 2 ∘ d 1 = 0` and `d 1` is surjective, `d 2 = 0` for `sl (Fin 2) R` with trivial
coefficients when `2` is a unit. -/
theorem dTwo_sl2_eq_zero (h2 : IsUnit (2 : R)) :
    d R (SpecialLinear.sl (Fin 2) R) M 2 = 0 := by
  ext ω
  obtain ⟨α, rfl⟩ := (dOne_sl2_bijective R h2).2 ω
  rw [d_d, LinearMap.zero_apply]

/-- `H⁰(sl (Fin 2) R, M) ≃ₗ[R] M` for any trivial `sl₂`-module `M`. -/
noncomputable def sl2CohomologyZeroEquiv :
    cohomology R (SpecialLinear.sl (Fin 2) R) M 0 ≃ₗ[R] M :=
  cohomologyZeroEquivOfIsTrivial R (SpecialLinear.sl (Fin 2) R) M

/-- `H¹(sl (Fin 2) R, M) = 0` (`Subsingleton`) when `2` is a unit in `R` (reflecting
`[sl₂, sl₂] = sl₂`). -/
theorem sl2_subsingleton_cohomology_one (h2 : IsUnit (2 : R)) :
    Subsingleton (cohomology R (SpecialLinear.sl (Fin 2) R) M 1) := by
  have hker : LinearMap.ker (d R (SpecialLinear.sl (Fin 2) R) M 1) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (dOne_sl2_bijective R h2).1
  have : Subsingleton (LinearMap.ker (d R (SpecialLinear.sl (Fin 2) R) M 1)) := by
    rw [hker]
    infer_instance
  exact (cohomologySuccEquiv R (SpecialLinear.sl (Fin 2) R) M 0).toEquiv.subsingleton

/-- `H²(sl (Fin 2) R, M) = 0` (`Subsingleton`) when `2` is a unit in `R`. -/
theorem sl2_subsingleton_cohomology_two (h2 : IsUnit (2 : R)) :
    Subsingleton (cohomology R (SpecialLinear.sl (Fin 2) R) M 2) := by
  have hrange : LinearMap.range (dToCycles R (SpecialLinear.sl (Fin 2) R) M 1) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨ω, hω⟩ _
    obtain ⟨α, rfl⟩ := (dOne_sl2_bijective R h2).2 ω
    exact ⟨α, Subtype.ext (dToCycles_coe R _ M 1 α)⟩
  have : Subsingleton
      (LinearMap.ker (d R (SpecialLinear.sl (Fin 2) R) M 2) ⧸
        LinearMap.range (dToCycles R (SpecialLinear.sl (Fin 2) R) M 1)) := by
    rw [hrange]
    exact Submodule.Quotient.subsingleton_iff.mpr rfl
  exact (cohomologySuccEquiv R (SpecialLinear.sl (Fin 2) R) M 1).toEquiv.subsingleton

/-- `H³(sl (Fin 2) R, M) ≃ₗ[R] M` when `2` is a unit in `R`. -/
noncomputable def sl2CohomologyThreeEquiv (h2 : IsUnit (2 : R)) :
    cohomology R (SpecialLinear.sl (Fin 2) R) M 3 ≃ₗ[R] M := by
  have hsub4 : Subsingleton (SpecialLinear.sl (Fin 2) R [⋀^Fin 4]→ₗ[R] M) :=
    subsingleton_alternatingMap_of_basis_lt (slFinTwoBasis R) (by decide)
  have hker : LinearMap.ker (d R (SpecialLinear.sl (Fin 2) R) M 3) = ⊤ :=
    LinearMap.ker_eq_top.mpr (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)
  have hrange : LinearMap.range (dToCycles R (SpecialLinear.sl (Fin 2) R) M 2) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨ω, rfl⟩
    rw [Submodule.mem_bot]
    apply Subtype.ext
    rw [dToCycles_coe, dTwo_sl2_eq_zero R h2]
    rfl
  exact (cohomologySuccEquiv R (SpecialLinear.sl (Fin 2) R) M 2) ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ hrange) ≪≫ₗ
    (LinearEquiv.ofTop _ hker) ≪≫ₗ
    alternatingMapTopEquiv (slFinTwoBasis R)

omit [LieModule.IsTrivial (SpecialLinear.sl (Fin 2) R) M] in
/-- `H^q(sl (Fin 2) R, M) = 0` (`Subsingleton`) for all `q ≥ 4`. -/
theorem sl2_subsingleton_cohomology_ge_four {q : ℕ} (hq : 4 ≤ q) :
    Subsingleton (cohomology R (SpecialLinear.sl (Fin 2) R) M q) := by
  have : Subsingleton (SpecialLinear.sl (Fin 2) R [⋀^Fin q]→ₗ[R] M) :=
    subsingleton_alternatingMap_of_basis_lt (slFinTwoBasis R) (by omega)
  exact subsingleton_cohomology_of_subsingleton

end Sl2

end TauCeti.Examples.ChevalleyEilenberg
