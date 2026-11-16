/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TauCeti.RingTheory.DeRham.Presentation

/-!
# The algebraic de Rham differential and cochain complex

For any commutative `A`-algebra `B`, this file constructs the algebraic exterior derivative
`DeRham.d A B n : Forms A B n →ₗ[A] Forms A B (n + 1)` in every degree `n ≥ 0`, proves `d ∘ d = 0`
and the graded Leibniz rule with respect to the wedge product, and packages the modules of
differential forms into the `ℕ`-indexed cochain complex
`DeRham.complex A B : CochainComplex (ModuleCat A) ℕ`.

Because `Forms A B n = ⋀[B]^n Ω[B⁄A]` is presented over `A` as the quotient
`Symbols A B n ⧸ symbolRelations A B n` (`DeRham.quotSymbolRelationsEquiv`), the exterior derivative
is constructed by descending the `A`-linear free differential
`[c; v₀, …, vₙ₋₁] ↦ D c ∧ D v₀ ∧ ⋯ ∧ D vₙ₋₁` along `symbolRelations`.
No characteristic assumption or smoothness hypothesis is used anywhere: both the vanishing of the
relation submodule under `freeDifferential` and the graded Leibniz rule hold over arbitrary
commutative rings, including in characteristic two.

We also compute `d` explicitly on univariate and multivariate polynomial algebras `A[X]` and
`MvPolynomial σ A`, establishing non-vanishing of `d X ∈ Ω¹_{A[X]/A}` and
`d(X₀ dX₁) = dX₀ ∧ dX₁ ∈ Ω²_{A[X₀, X₁]/A}` over every nontrivial base ring `A` (such as `ℤ` or
`ZMod 2`).

## Main definitions

* `TauCeti.DeRham.freeDifferential A B n`: the `A`-linear map from `Symbols A B n` to
  `Forms A B (n + 1)` sending `[c; v]` to `D c ∧ D v₀ ∧ ⋯ ∧ D vₙ₋₁`.
* `TauCeti.DeRham.d A B n`: the `A`-linear algebraic exterior derivative
  `Forms A B n →ₗ[A] Forms A B (n + 1)`.
* `TauCeti.DeRham.complex A B`: the algebraic de Rham cochain complex
  `Ω^•_{B/A} : CochainComplex (ModuleCat A) ℕ`.

## Main results

* `TauCeti.DeRham.freeDifferential_relations`: `symbolRelations A B n` lies in the kernel of
  `freeDifferential A B n`.
* `TauCeti.DeRham.d_elementary` and `TauCeti.DeRham.d_unique`: `d` sends `c • (D v₀ ∧ ⋯ ∧ D vₙ₋₁)`
  to `D c ∧ D v₀ ∧ ⋯ ∧ D vₙ₋₁` and is uniquely determined as an `A`-linear map by this formula.
* `TauCeti.DeRham.d_comp_d` and `TauCeti.DeRham.d_d`: `d ∘ d = 0`.
* `TauCeti.DeRham.d_leibniz` and `TauCeti.DeRham.d_smul`: the graded Leibniz rule
  `d (α ∧ β) = d α ∧ β + (-1) ^ m • (α ∧ d β)` and its `B`-scalar specialization
  `d (b • ω) = D b ∧ ω + b • d ω`.
* `TauCeti.DeRham.d_zeroForm_polynomial_X_ne_zero` and
  `TauCeti.DeRham.d_mvPolynomial_X_smul_D_X_ne_zero`: non-vanishing of algebraic de Rham
  differentials on polynomial algebras over any nontrivial commutative ring.

## References

* [The Stacks Project, *The de Rham complex*, Section 10.132 (Tag 0FKF)](https://stacks.math.columbia.edu/tag/0FKF).
-/

public section

noncomputable section

open CategoryTheory KaehlerDifferential

namespace TauCeti.DeRham

universe u v

section Differential

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-! ### The free differential on formal symbols -/

/-- The `A`-linear map `Symbols A B n →ₗ[A] Forms A B (n + 1)` sending each formal symbol `[c; v]`
to `D c ∧ D v₀ ∧ ⋯ ∧ D vₙ₋₁`. -/
def freeDifferential (n : ℕ) : Symbols A B n →ₗ[A] Forms A B (n + 1) :=
  Finsupp.linearCombination A fun p : B × (Fin n → B) ↦
    elementary A B (n + 1) 1 (Fin.cons p.1 p.2)

variable {A B}

@[simp]
theorem freeDifferential_single (n : ℕ) (c : B) (v : Fin n → B) (a : A) :
    freeDifferential A B n (Finsupp.single (c, v) a) =
      a • elementary A B (n + 1) 1 (Fin.cons c v) := by
  simp [freeDifferential]

@[simp]
theorem freeDifferential_sym (n : ℕ) (c : B) (v : Fin n → B) :
    freeDifferential A B n (sym A B n c v) = elementary A B (n + 1) 1 (Fin.cons c v) := by
  rw [sym_def, freeDifferential_single, one_smul]

theorem freeDifferential_add (n : ℕ) (s t : Symbols A B n) :
    freeDifferential A B n (s + t) = freeDifferential A B n s + freeDifferential A B n t :=
  map_add (freeDifferential A B n) s t

theorem freeDifferential_smul (n : ℕ) (a : A) (s : Symbols A B n) :
    freeDifferential A B n (a • s) = a • freeDifferential A B n s :=
  map_smul (freeDifferential A B n) a s

private theorem D_comp_cons {n : ℕ} (c : B) (v : Fin n → B) :
    D A B ∘ Fin.cons c v = Fin.cons (D A B c) (D A B ∘ v) := by
  ext j
  cases j using Fin.cases <;> rfl

theorem freeDifferential_sym_eq_ιMulti (n : ℕ) (c : B) (v : Fin n → B) :
    freeDifferential A B n (sym A B n c v) =
      exteriorPower.ιMulti B (n + 1) (Fin.cons (D A B c) (D A B ∘ v)) := by
  rw [freeDifferential_sym, elementary_def, one_smul, D_comp_cons]

theorem freeDifferential_sym_eq_wedgeLeft (n : ℕ) (c : B) (v : Fin n → B) :
    freeDifferential A B n (sym A B n c v) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D A B c) n (exteriorPower.ιMulti B n (D A B ∘ v)) := by
  rw [freeDifferential_sym_eq_ιMulti, TauCeti.ExteriorAlgebra.wedgeLeft_ιMulti]

theorem freeDifferential_one_coeff (n : ℕ) (v : Fin n → B) :
    freeDifferential A B n (sym A B n 1 v) = 0 := by
  rw [freeDifferential_sym_eq_wedgeLeft, ← map_one (algebraMap A B), Derivation.map_algebraMap]
  ext
  simp

theorem oneEquiv_freeDifferential_zero (c : B) (v : Fin 0 → B) :
    exteriorPower.oneEquiv B Ω[B⁄A] (freeDifferential A B 0 (sym A B 0 c v)) = D A B c := by
  rw [freeDifferential_sym, elementary_one_deg, Fin.cons_zero, one_smul, oneEquiv_oneForm]

/-! ### Vanishing of the symbol relations under `freeDifferential` -/

private theorem coe_base_smul {k : ℕ} (a : A) (ω : Forms A B k) :
    ((a • ω : Forms A B k) : _root_.ExteriorAlgebra B Ω[B⁄A]) =
      a • (ω : _root_.ExteriorAlgebra B Ω[B⁄A]) := by
  rw [← IsScalarTower.algebraMap_smul B a ω, SetLike.val_smul, IsScalarTower.algebraMap_smul]

private theorem cons_update_comp_swap {n : ℕ} (u₀ : Fin n → Ω[B⁄A]) (i : Fin n)
    (w₁ w₂ : Ω[B⁄A]) :
    (Fin.cons w₁ (Function.update u₀ i w₂) : Fin (n + 1) → Ω[B⁄A]) ∘ Equiv.swap 0 i.succ =
      Fin.cons w₂ (Function.update u₀ i w₁) := by
  let u : Fin (n + 1) → Ω[B⁄A] := Fin.cons w₁ (Function.update u₀ i w₂)
  let u' : Fin (n + 1) → Ω[B⁄A] := Fin.cons w₂ (Function.update u₀ i w₁)
  ext j
  cases j using Fin.cases with
  | zero =>
    change u (Equiv.swap 0 i.succ 0) = u' 0
    rw [Equiv.swap_apply_left]
    simp only [u, u', Fin.cons_succ, Fin.cons_zero, Function.update_self]
  | succ k =>
    by_cases hki : k = i
    · subst hki
      change u (Equiv.swap 0 k.succ k.succ) = u' k.succ
      rw [Equiv.swap_apply_right]
      simp only [u, u', Fin.cons_zero, Fin.cons_succ, Function.update_self]
    · have hne : k.succ ≠ i.succ := fun h ↦ hki (Fin.succ_inj.mp h)
      change u (Equiv.swap 0 i.succ k.succ) = u' k.succ
      rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k) hne]
      simp only [u, u', Fin.cons_succ, Function.update_of_ne hki]

private theorem freeDifferential_slot_mul_zero {n : ℕ} (c : B) (v : Fin n → B) (i : Fin n)
    (x y : B) :
    freeDifferential A B n
        (sym A B n c (Function.update v i (x * y)) -
          sym A B n (c * x) (Function.update v i y) -
          sym A B n (c * y) (Function.update v i x)) = 0 := by
  rw [map_sub, map_sub, freeDifferential_sym_eq_ιMulti, freeDifferential_sym_eq_ιMulti,
    freeDifferential_sym_eq_ιMulti]
  have hupd (z : B) :
      Fin.cons (D A B c) (D A B ∘ Function.update v i z) =
        Function.update (Fin.cons (D A B c) (D A B ∘ v) : Fin (n + 1) → Ω[B⁄A])
          i.succ (D A B z) := by
    rw [Function.comp_update, Fin.cons_update]
  have h0 (u : Fin n → Ω[B⁄A]) (w : Ω[B⁄A]) :
      Fin.cons w u = Function.update (Fin.cons 0 u : Fin (n + 1) → Ω[B⁄A]) 0 w := by
    ext j; cases j using Fin.cases <;> rfl
  rw [hupd (x * y), Derivation.leibniz (D A B) x y,
    AlternatingMap.map_update_add, AlternatingMap.map_update_smul, AlternatingMap.map_update_smul]
  rw [Derivation.leibniz (D A B) c x, h0 _ (c • D A B x + x • D A B c),
    AlternatingMap.map_update_add, AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
    ← h0 _ (D A B x), ← h0 _ (D A B c), hupd y]
  rw [Derivation.leibniz (D A B) c y, h0 _ (c • D A B y + y • D A B c),
    AlternatingMap.map_update_add, AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
    ← h0 _ (D A B y), ← h0 _ (D A B c), hupd x]
  rw [Function.comp_update, Function.comp_update]
  let u : Fin (n + 1) → Ω[B⁄A] := Fin.cons (D A B x) (Function.update (D A B ∘ v) i (D A B y))
  let u' : Fin (n + 1) → Ω[B⁄A] := Fin.cons (D A B y) (Function.update (D A B ∘ v) i (D A B x))
  have halt : exteriorPower.ιMulti B (n + 1) (u ∘ Equiv.swap 0 i.succ) +
      exteriorPower.ιMulti B (n + 1) u = 0 :=
    (exteriorPower.ιMulti B (n + 1)).map_swap_add u (Fin.succ_ne_zero i).symm
  rw [cons_update_comp_swap] at halt
  have hcsum : c • exteriorPower.ιMulti B (n + 1) u +
      c • exteriorPower.ιMulti B (n + 1) u' = 0 := by
    rw [← smul_add, add_comm (exteriorPower.ιMulti B (n + 1) u), halt, smul_zero]
  have key : ∀ (p q r s : Forms A B (n + 1)),
      r + s = 0 → (p + q) - (r + p) - (s + q) = 0 := fun p q r s h ↦ by
    rw [sub_sub, show (r + p) + (s + q) = (r + s) + (p + q) by abel, h, zero_add, sub_self]
  exact key _ _ _ _ hcsum

variable (A B) in
/-- Every generator of `symbolRelations A B n` lies in the kernel of `freeDifferential A B n`. -/
theorem freeDifferential_relations (n : ℕ) :
    symbolRelations A B n ≤ LinearMap.ker (freeDifferential A B n) := by
  rw [symbolRelations_le_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c e v
    rw [LinearMap.mem_ker, map_sub, map_sub, freeDifferential_sym_eq_wedgeLeft,
      freeDifferential_sym_eq_wedgeLeft, freeDifferential_sym_eq_wedgeLeft]
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_sub, TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply,
      TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply,
      map_add (D A B), map_add, add_mul, sub_sub, sub_self, Submodule.coe_zero]
  · intro a c v
    rw [LinearMap.mem_ker, map_sub, map_smul, freeDifferential_sym_eq_wedgeLeft,
      freeDifferential_sym_eq_wedgeLeft, (D A B).map_smul]
    apply Subtype.ext
    rw [Submodule.coe_sub, coe_base_smul, TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply,
      TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, ← IsScalarTower.algebraMap_smul B a (D A B c),
      LinearMap.map_smul, smul_mul_assoc, IsScalarTower.algebraMap_smul, sub_self,
      Submodule.coe_zero]
  · intro c v i x y
    rw [LinearMap.mem_ker, map_sub, map_sub, freeDifferential_sym_eq_ιMulti,
      freeDifferential_sym_eq_ιMulti, freeDifferential_sym_eq_ιMulti]
    have hupd (z : B) : Fin.cons (D A B c) (D A B ∘ Function.update v i z) =
        Function.update (Fin.cons (D A B c) (D A B ∘ v) : Fin (n + 1) → Ω[B⁄A])
          i.succ (D A B z) := by
      rw [Function.comp_update, Fin.cons_update]
    rw [hupd, hupd, hupd, map_add (D A B), AlternatingMap.map_update_add, sub_sub, sub_self]
  · intro c v i x y
    exact freeDifferential_slot_mul_zero c v i x y
  · intro c v i a
    rw [LinearMap.mem_ker, freeDifferential_sym_eq_ιMulti]
    have hupd : Fin.cons (D A B c) (D A B ∘ Function.update v i (algebraMap A B a)) =
        Function.update (Fin.cons (D A B c) (D A B ∘ v) : Fin (n + 1) → Ω[B⁄A]) i.succ 0 := by
      rw [Function.comp_update, Fin.cons_update, Derivation.map_algebraMap]
    rw [hupd, AlternatingMap.map_update_zero]
  · intro c v i j hij hv
    rw [LinearMap.mem_ker, freeDifferential_sym]
    exact elementary_eq_zero_of_eq A B 1 (v := Fin.cons c v) (i := i.succ) (j := j.succ)
      (fun h ↦ hij (Fin.succ_inj.mp h)) (by simpa using hv)

/-! ### The exterior derivative `DeRham.d` -/

variable (A B) in
/-- The algebraic exterior derivative `Forms A B n →ₗ[A] Forms A B (n + 1)`, descended from
`freeDifferential A B n` along `quotSymbolRelationsEquiv A B n`. -/
def d (n : ℕ) : Forms A B n →ₗ[A] Forms A B (n + 1) :=
  ((symbolRelations A B n).liftQ (freeDifferential A B n) (freeDifferential_relations A B n)).comp
    (quotSymbolRelationsEquiv A B n).symm.toLinearMap

@[simp]
theorem d_symbolMap (n : ℕ) (s : Symbols A B n) :
    d A B n (symbolMap A B n s) = freeDifferential A B n s := by
  rw [d, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ← quotSymbolRelationsEquiv_mkQ,
    LinearEquiv.symm_apply_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- **Action of `d` on elementary forms.** The exterior derivative sends `c • (D v₀ ∧ ⋯ ∧ D vₙ₋₁)`
to `D c ∧ D v₀ ∧ ⋯ ∧ D vₙ₋₁`. -/
@[simp]
theorem d_elementary (n : ℕ) (c : B) (v : Fin n → B) :
    d A B n (elementary A B n c v) = elementary A B (n + 1) 1 (Fin.cons c v) := by
  rw [← symbolMap_sym, d_symbolMap, freeDifferential_sym]

theorem d_elementary_eq_wedgeLeft (n : ℕ) (c : B) (v : Fin n → B) :
    d A B n (elementary A B n c v) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D A B c) n (exteriorPower.ιMulti B n (D A B ∘ v)) := by
  rw [← symbolMap_sym, d_symbolMap, freeDifferential_sym_eq_wedgeLeft]

@[simp]
theorem d_ιMulti_D (n : ℕ) (v : Fin n → B) :
    d A B n (exteriorPower.ιMulti B n (D A B ∘ v)) = 0 := by
  rw [← one_smul B (exteriorPower.ιMulti B n (D A B ∘ v)), ← elementary_def, d_elementary,
    ← freeDifferential_sym, freeDifferential_one_coeff]

theorem d_add (n : ℕ) (ω₁ ω₂ : Forms A B n) :
    d A B n (ω₁ + ω₂) = d A B n ω₁ + d A B n ω₂ :=
  map_add (d A B n) ω₁ ω₂

theorem d_base_smul (n : ℕ) (a : A) (ω : Forms A B n) :
    d A B n (a • ω) = a • d A B n ω :=
  map_smul (d A B n) a ω

/-- In degree zero, `d` sends `zeroForm A B b` to `oneForm A B (D A B b)`. -/
@[simp]
theorem d_zeroForm (b : B) :
    d A B 0 (zeroForm A B b) = oneForm A B (D A B b) := by
  rw [← elementary_zero_deg A B b Fin.elim0, d_elementary, elementary_one_deg A B, Fin.cons_zero,
    one_smul]

theorem oneEquiv_d_zeroForm (b : B) :
    exteriorPower.oneEquiv B Ω[B⁄A] (d A B 0 (zeroForm A B b)) = D A B b := by
  rw [d_zeroForm, oneEquiv_oneForm]

/-- Identifying `Forms A B 0 ≃ B` and `Forms A B 1 ≃ Ω[B⁄A]`, the degree-zero exterior derivative
is the universal Kähler derivation `D A B`. -/
theorem d_zero_comp_zeroForm :
    ((exteriorPower.oneEquiv B Ω[B⁄A]).toLinearMap.restrictScalars A).comp
        ((d A B 0).comp ((zeroForm A B).toLinearMap.restrictScalars A)) =
      (D A B).toLinearMap := by
  ext b
  exact oneEquiv_d_zeroForm b

theorem d_algebraMap_zeroForm (a : A) :
    d A B 0 (zeroForm A B (algebraMap A B a)) = 0 := by
  rw [d_zeroForm, Derivation.map_algebraMap, map_zero]

/-- Two `A`-linear maps out of `Forms A B n` that agree on all elementary forms are equal. -/
theorem ext_of_elementary {n : ℕ} {M : Type*} [AddCommGroup M] [Module A M]
    {f g : Forms A B n →ₗ[A] M}
    (h : ∀ (c : B) (v : Fin n → B), f (elementary A B n c v) = g (elementary A B n c v)) :
    f = g :=
  LinearMap.ext_on_range (span_elementary_eq_top A B n) fun p ↦ h p.1 p.2

/-- **Uniqueness of the exterior derivative.** Any `A`-linear map
`Forms A B n →ₗ[A] Forms A B (n + 1)` that sends `c • (D v₀ ∧ ⋯ ∧ D vₙ₋₁)` to
`D c ∧ D v₀ ∧ ⋯ ∧ D vₙ₋₁` equals `DeRham.d A B n`. -/
theorem d_unique {n : ℕ} (f : Forms A B n →ₗ[A] Forms A B (n + 1))
    (hf : ∀ (c : B) (v : Fin n → B),
      f (elementary A B n c v) = elementary A B (n + 1) 1 (Fin.cons c v)) :
    f = d A B n :=
  ext_of_elementary fun c v ↦ (hf c v).trans (d_elementary n c v).symm

/-! ### `d ∘ d = 0` and the graded Leibniz rule -/

/-- Applying the algebraic exterior derivative twice gives zero. -/
@[simp]
theorem d_comp_d (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    (d A B (n + 1)).comp (d A B n) = 0 := by
  refine ext_of_elementary fun c v ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, d_elementary, d_elementary,
    ← freeDifferential_sym, freeDifferential_one_coeff]

@[simp]
theorem d_d (n : ℕ) (ω : Forms A B n) : d A B (n + 1) (d A B n ω) = 0 :=
  LinearMap.congr_fun (d_comp_d A B n) ω

private theorem coe_d_wedge_elementary {m n : ℕ} (c e : B) (u : Fin m → B) (v : Fin n → B) :
    (d A B (m + n) (wedge A B (elementary A B m c u) (elementary A B n e v)) :
        _root_.ExteriorAlgebra B Ω[B⁄A]) =
      (d A B m (elementary A B m c u) : _root_.ExteriorAlgebra B Ω[B⁄A]) *
          (elementary A B n e v : _root_.ExteriorAlgebra B Ω[B⁄A]) +
        (-1 : A) ^ m •
          ((elementary A B m c u : _root_.ExteriorAlgebra B Ω[B⁄A]) *
            (d A B n (elementary A B n e v) : _root_.ExteriorAlgebra B Ω[B⁄A])) := by
  have happ : D A B ∘ Fin.append u v = Fin.append (D A B ∘ u) (D A B ∘ v) := by
    ext i
    exact Fin.addCases (fun _ ↦ by simp) (fun _ ↦ by simp) i
  rw [wedge_elementary, d_elementary_eq_wedgeLeft, d_elementary_eq_wedgeLeft,
    d_elementary_eq_wedgeLeft, TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply,
    TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply,
    elementary_def, elementary_def, SetLike.val_smul, SetLike.val_smul, happ,
    ← exteriorPower.wedge_ιMulti, exteriorPower.coe_wedge, Derivation.leibniz (D A B) c e,
    map_add, map_smul, map_smul, add_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, ← mul_assoc, ← mul_assoc]
  have hcomm : _root_.ExteriorAlgebra.ι B (D A B e) *
        (exteriorPower.ιMulti B m (D A B ∘ u) : _root_.ExteriorAlgebra B Ω[B⁄A]) =
      (-1 : B) ^ m •
        ((exteriorPower.ιMulti B m (D A B ∘ u) : _root_.ExteriorAlgebra B Ω[B⁄A]) *
          _root_.ExteriorAlgebra.ι B (D A B e)) := by
    simpa using TauCeti.ExteriorAlgebra.mul_eq_neg_one_pow_smul_mul_of_mem
      (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one (D A B e))
      (exteriorPower.ιMulti B m (D A B ∘ u)).2
  rw [hcomm, smul_mul_assoc, mul_assoc, ← IsScalarTower.algebraMap_smul B ((-1 : A) ^ m),
    map_pow, map_neg, map_one, smul_comm c ((-1 : B) ^ m), add_comm]

/-- Inside `ExteriorAlgebra B Ω[B⁄A]`, the exterior derivative satisfies the graded Leibniz rule
`d (α ∧ β) = d α ∧ β + (-1) ^ m • (α ∧ d β)`. -/
theorem coe_d_wedge {m n : ℕ} (α : Forms A B m) (β : Forms A B n) :
    (d A B (m + n) (wedge A B α β) : _root_.ExteriorAlgebra B Ω[B⁄A]) =
      (d A B m α : _root_.ExteriorAlgebra B Ω[B⁄A]) *
          (β : _root_.ExteriorAlgebra B Ω[B⁄A]) +
        (-1 : A) ^ m •
          ((α : _root_.ExteriorAlgebra B Ω[B⁄A]) *
            (d A B n β : _root_.ExteriorAlgebra B Ω[B⁄A])) := by
  obtain ⟨sα, rfl⟩ := symbolMap_surjective A B m α
  induction sα using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, wedge_add_left, map_add, map_add, Submodule.coe_add, Submodule.coe_add,
      Submodule.coe_add, hx, hy, add_mul, add_mul, smul_add, add_add_add_comm]
  | single p a =>
    rcases p with ⟨c, u⟩
    obtain ⟨sβ, rfl⟩ := symbolMap_surjective A B n β
    induction sβ using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, wedge_add_right, map_add, map_add, Submodule.coe_add, Submodule.coe_add,
        Submodule.coe_add, hx, hy, mul_add, mul_add, smul_add, add_add_add_comm]
    | single q r =>
      rcases q with ⟨e, v⟩
      rw [symbolMap_single, symbolMap_single, wedge_base_smul_left, wedge_base_smul_right,
        map_smul, map_smul, map_smul, map_smul, coe_base_smul, coe_base_smul, coe_base_smul,
        coe_base_smul, coe_base_smul, coe_base_smul, smul_mul_assoc, mul_smul_comm,
        smul_mul_assoc, mul_smul_comm, smul_comm ((-1 : A) ^ m) a, smul_comm ((-1 : A) ^ m) r,
        ← smul_add, ← smul_add, coe_d_wedge_elementary]

/-- **Graded Leibniz rule for the algebraic exterior derivative.** For `α ∈ Forms A B m` and
`β ∈ Forms A B n`,
`d (α ∧ β) = Forms.cast (Nat.succ_add m n) (d α ∧ β) + (-1) ^ m • (α ∧ d β)`. -/
theorem d_leibniz {m n : ℕ} (α : Forms A B m) (β : Forms A B n) :
    d A B (m + n) (wedge A B α β) =
      Forms.cast (Nat.succ_add m n) (wedge A B (d A B m α) β) +
        (-1 : A) ^ m • wedge A B α (d A B n β) :=
  Subtype.ext <| by
    rw [coe_d_wedge, Submodule.coe_add, Forms.coe_cast, coe_wedge, coe_base_smul, coe_wedge]

/-- Leibniz rule for `B`-scalar multiplication of `n`-forms:
`d (b • ω) = D b ∧ ω + b • d ω`. -/
theorem d_smul (n : ℕ) (b : B) (ω : Forms A B n) :
    d A B n (b • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D A B b) n ω + b • d A B n ω := by
  let lhs : Forms A B n →ₗ[A] Forms A B (n + 1) :=
    (d A B n).comp ((LinearMap.lsmul B (Forms A B n) b).restrictScalars A)
  let rhs : Forms A B n →ₗ[A] Forms A B (n + 1) :=
    (TauCeti.ExteriorAlgebra.wedgeLeft (D A B b) n).restrictScalars A +
      ((LinearMap.lsmul B (Forms A B (n + 1)) b).restrictScalars A).comp (d A B n)
  have heq : lhs = rhs := ext_of_elementary fun c v ↦ by
    change d A B n (b • elementary A B n c v) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D A B b) n (elementary A B n c v) +
        b • d A B n (elementary A B n c v)
    rw [← elementary_smul_coeff, d_elementary_eq_wedgeLeft, d_elementary_eq_wedgeLeft]
    apply Subtype.ext
    rw [Submodule.coe_add, TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply,
      TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, SetLike.val_smul,
      TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, Derivation.leibniz (D A B) b c,
      map_add, map_smul, map_smul, add_mul, smul_mul_assoc, smul_mul_assoc, elementary_def,
      SetLike.val_smul, mul_smul_comm, add_comm]
  exact LinearMap.congr_fun heq ω

/-- When `algebraMap A B` is surjective, the algebraic exterior derivative vanishes in every
degree. -/
theorem d_eq_zero_of_surjective (h : Function.Surjective (algebraMap A B)) (n : ℕ) :
    d A B n = 0 := by
  refine ext_of_elementary fun c v ↦ ?_
  obtain ⟨a, rfl⟩ := h c
  rw [LinearMap.zero_apply, d_elementary_eq_wedgeLeft, Derivation.map_algebraMap]
  ext
  simp

/-! ### The algebraic de Rham cochain complex -/

/-- **The algebraic de Rham cochain complex** `Ω^•_{B/A}` of a commutative `A`-algebra `B`, with
degree-`n` object `ModuleCat.of A (Forms A B n)` and differential `DeRham.d A B n`.

The body is exposed so that `(complex A B).X n` is definitionally `ModuleCat.of A (Forms A B n)` and
differentials and chain maps act directly on elements of `Forms A B n`. -/
@[expose]
def complex (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    CochainComplex (ModuleCat.{v} A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (Forms A B n))
    (fun n ↦ ModuleCat.ofHom (d A B n))
    (fun n ↦ ModuleCat.hom_ext (d_comp_d A B n))

@[simp]
theorem complex_X (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    (complex A B).X n = ModuleCat.of A (Forms A B n) :=
  (rfl)

theorem complex_d (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    (complex A B).d n (n + 1) = ModuleCat.ofHom (d A B n) := by
  simp [complex]

@[simp]
theorem complex_d_apply (n : ℕ) (ω : Forms A B n) :
    ((complex A B).d n (n + 1)).hom ω = d A B n ω :=
  congr($(complex_d A B n).hom ω)

theorem complex_d_ne (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    {i j : ℕ} (h : i + 1 ≠ j) :
    (complex A B).d i j = 0 :=
  CochainComplex.of_d_ne (fun k ↦ ModuleCat.of A (Forms A B k))
    (fun k ↦ ModuleCat.ofHom (d A B k)) h

theorem complex_d_eq_zero_of_surjective (h : Function.Surjective (algebraMap A B)) (i j : ℕ) :
    (complex A B).d i j = 0 := by
  by_cases hij : i + 1 = j
  · subst hij
    rw [complex_d, d_eq_zero_of_surjective h i]
    rfl
  · exact complex_d_ne A B hij

end Differential

/-! ### Polynomial differentials and non-vanishing -/

section Polynomial

variable (A : Type u) [CommRing A]

/-- Under `Ω¹_{A[X]/A} ≃ A[X]`, the exterior derivative of a degree-zero polynomial form `P` is the
formal derivative `Polynomial.derivative P`. -/
theorem polynomialEquiv_oneEquiv_d_zeroForm (P : Polynomial A) :
    KaehlerDifferential.polynomialEquiv A
        (exteriorPower.oneEquiv (Polynomial A) Ω[Polynomial A⁄A]
          (d A (Polynomial A) 0 (zeroForm A (Polynomial A) P))) =
      Polynomial.derivative P := by
  rw [oneEquiv_d_zeroForm, KaehlerDifferential.polynomialEquiv_D]

/-- Over any nontrivial commutative ring `A` (including `ℤ` and `ZMod 2`), the differential
`d X ∈ Forms A A[X] 1` is nonzero. -/
theorem d_zeroForm_polynomial_X_ne_zero [Nontrivial A] :
    d A (Polynomial A) 0 (zeroForm A (Polynomial A) Polynomial.X) ≠ 0 := by
  intro h
  have h1 := polynomialEquiv_oneEquiv_d_zeroForm A Polynomial.X
  rw [h, map_zero, map_zero, Polynomial.derivative_X] at h1
  exact zero_ne_one h1

/-- In `MvPolynomial σ A`, the exterior derivative of the `1`-form `Xᵢ • D Xⱼ` is the `2`-form
`D Xᵢ ∧ D Xⱼ`. -/
theorem d_mvPolynomial_X_smul_D_X {σ : Type v} (i j : σ) :
    d A (MvPolynomial σ A) 1
        (oneForm A (MvPolynomial σ A)
          ((MvPolynomial.X i : MvPolynomial σ A) •
            D A (MvPolynomial σ A) (MvPolynomial.X j))) =
      exteriorPower.ιMulti (MvPolynomial σ A) 2
        ![D A (MvPolynomial σ A) (MvPolynomial.X i),
          D A (MvPolynomial σ A) (MvPolynomial.X j)] := by
  have helem : oneForm A (MvPolynomial σ A)
        ((MvPolynomial.X i : MvPolynomial σ A) •
          D A (MvPolynomial σ A) (MvPolynomial.X j)) =
      elementary A (MvPolynomial σ A) 1 (MvPolynomial.X i) (fun _ ↦ MvPolynomial.X j) := by
    rw [elementary_one_deg]
  rw [helem, d_elementary, elementary_def, one_smul]
  congr 1
  ext k
  fin_cases k <;> rfl

/-- Over any nontrivial commutative ring `A` (including `ℤ` and `ZMod 2`),
`d (X₀ • D X₁) = D X₀ ∧ D X₁ ∈ Forms A (MvPolynomial (Fin 2) A) 2` is nonzero. -/
theorem d_mvPolynomial_X_smul_D_X_ne_zero [Nontrivial A] :
    d A (MvPolynomial (Fin 2) A) 1
        (oneForm A (MvPolynomial (Fin 2) A)
          ((MvPolynomial.X 0 : MvPolynomial (Fin 2) A) •
            D A (MvPolynomial (Fin 2) A) (MvPolynomial.X 1))) ≠ 0 := by
  rw [d_mvPolynomial_X_smul_D_X]
  let b := KaehlerDifferential.mvPolynomialBasis A (Fin 2)
  have hb : ![D A (MvPolynomial (Fin 2) A) (MvPolynomial.X 0),
        D A (MvPolynomial (Fin 2) A) (MvPolynomial.X 1)] = ⇑b := by
    ext k
    fin_cases k <;> simp [b]
  rw [hb]
  intro h
  have hdet := congrArg b.exteriorPowerTopEquiv h
  rw [map_zero, Module.Basis.exteriorPowerTopEquiv_apply_ιMulti, Module.Basis.det_self] at hdet
  exact one_ne_zero hdet

end Polynomial

end TauCeti.DeRham
