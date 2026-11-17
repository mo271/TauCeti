/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import TauCeti.Algebra.Cluster.CoefficientSemifield.WithZero
public import TauCeti.Algebra.MonoidAlgebra.ZeroSumFree
public import TauCeti.RingTheory.Localization.TotalQuotient
import Mathlib.Algebra.MvPolynomial.Variables
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.MvPolynomial.ZeroSumFree
import TauCeti.Data.Nat.Cast.ZeroSumFree
import TauCeti.RingTheory.Localization.Defs

/-!
# Positive subtraction-free rational functions with formal coefficients

For a commutative monoid `P` and an index type `K`, `TauCeti.PosZero P K` is the total quotient of
the polynomial semiring `MvPolynomial K (MonoidAlgebra ℕ P)`. The coefficients live in the monoid
semiring `ℕ[P]`, using only the multiplication of `P` together with formal addition (not any
auxiliary addition that `P` may carry). Its group of units is `TauCeti.Pos P K`.

When `P` has unique products — in particular whenever `P` is a `TauCeti.CoefficientSemifield` —
the polynomial semiring `MvPolynomial K (MonoidAlgebra ℕ P)` is a zero-sum-free domain, so
`PosZero P K` is a zero-sum-free `Semifield` and `Pos P K` is a `TauCeti.CoefficientSemifield`.

## Main definitions

* `TauCeti.PosZero`: the total quotient `TotalQuotient (MvPolynomial K (MonoidAlgebra ℕ P))`.
* `TauCeti.Pos`: the unit group `(PosZero P K)ˣ`, which is a coefficient semifield whenever
  `UniqueProds P` holds.
* `TauCeti.PosZero.coeff`, `TauCeti.PosZero.X`, `TauCeti.Pos.coeff`, `TauCeti.Pos.X`: the
  coefficient and variable generators.
* `TauCeti.PosZero.eval`, `TauCeti.PosZero.evalEquiv`, `TauCeti.Pos.eval`, `TauCeti.Pos.evalEquiv`:
  evaluation of positive subtraction-free rational functions at a multiplicative map `φ : P →* Sˣ`
  (or `P →* Q`) and a family `a : K → Sˣ` (or `K → Q`), establishing the universal property.
* `TauCeti.PosZero.evalAlong`: evaluation into an ambient semiring `R` by composing with a
  multiplicative and additive map `Q →* R` from a coefficient semifield `Q` (such as the inclusion
  of an addition-closed subgroup of `Rˣ`).
* `TauCeti.PosZero.renameEquiv`, `TauCeti.PosZero.rename`, `TauCeti.Pos.rename`,
  `TauCeti.PosZero.mapCoeff`, `TauCeti.Pos.mapCoeff`: functoriality in the index type and in the
  coefficient monoid.

## Main results

* `TauCeti.PosZero.hom_ext`, `TauCeti.Pos.hom_ext`: homomorphisms are determined by their values on
  coefficients and variables.
* `TauCeti.PosZero.exists_finset_rename`, `TauCeti.PosZero.exists_finset_eval_eq`,
  `TauCeti.Pos.exists_finset_rename`, `TauCeti.Pos.exists_finset_eval_eq`: finite-support laws.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  §2, where subtraction-free rational functions with coefficients in a semifield govern the
  separation formulas and specialization of cluster variables.
-/

public section

noncomputable section

namespace TauCeti

open CoefficientSemifield

/-- The semiring of subtraction-free rational functions in variables indexed by `K` with formal
natural-number combinations of `P` as coefficients, together with zero: the total quotient of
`MvPolynomial K (MonoidAlgebra ℕ P)`. -/
abbrev PosZero (P K : Type*) [CommMonoid P] :=
  TotalQuotient (MvPolynomial K (MonoidAlgebra ℕ P))

/-- The group of units of `PosZero P K`. When `UniqueProds P` holds (in particular for every
`CoefficientSemifield P`), this is a coefficient semifield. -/
abbrev Pos (P K : Type*) [CommMonoid P] :=
  (PosZero P K)ˣ

section Generators

variable {P K : Type*} [CommMonoid P]

namespace PosZero

/-- The coefficient generator indexed by `p : P`, as a monoid homomorphism `P →* PosZero P K`. -/
def coeff : P →* PosZero P K :=
  (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) :
      MvPolynomial K (MonoidAlgebra ℕ P) →* PosZero P K).comp
    ((MvPolynomial.C : MonoidAlgebra ℕ P →+* MvPolynomial K (MonoidAlgebra ℕ P)).toMonoidHom.comp
      (MonoidAlgebra.of ℕ P))

@[simp]
theorem algebraMap_C_single (p : P) :
    algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K)
        (MvPolynomial.C (MonoidAlgebra.single p 1)) =
      coeff p :=
  (rfl)

@[simp]
theorem coeff_ne_zero (p : P) : (coeff p : PosZero P K) ≠ 0 := by
  rw [← algebraMap_C_single, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
    MvPolynomial.C_eq_zero]
  exact MonoidAlgebra.single_ne_zero.mpr one_ne_zero

/-- For a cancellative commutative monoid `P`, every coefficient generator is a unit in
`PosZero P K`. -/
theorem isUnit_coeff [IsCancelMul P] (p : P) : IsUnit (coeff p : PosZero P K) := by
  rw [← algebraMap_C_single]
  have hreg : IsRegular (MvPolynomial.C (MonoidAlgebra.single p (1 : ℕ)) :
      MvPolynomial K (MonoidAlgebra ℕ P)) := by
    rw [← MvPolynomial.monomial_zero']
    exact (MonoidAlgebra.isRegular_single p (isRegular_one (R := ℕ))).monomial
  exact IsLocalization.map_units (PosZero P K) ⟨_, mem_regulars.mpr hreg⟩

/-- The variable generator indexed by `i : K`. -/
def X (i : K) : PosZero P K :=
  algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) (MvPolynomial.X i)

@[simp]
theorem algebraMap_X (i : K) :
    algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) (MvPolynomial.X i) = X i :=
  (rfl)

@[simp]
theorem X_ne_zero (i : K) : (X i : PosZero P K) ≠ 0 := by
  rw [← algebraMap_X, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  exact MvPolynomial.X_ne_zero i

/-- Every variable generator is a unit in `PosZero P K`. -/
theorem isUnit_X (i : K) : IsUnit (X i : PosZero P K) :=
  IsLocalization.map_units (PosZero P K)
    ⟨MvPolynomial.X i, mem_regulars.mpr MvPolynomial.isRegular_X⟩

end PosZero

namespace Pos

/-- The coefficient generator indexed by `p : P`, as a unit in `Pos P K`. -/
def coeff [UniqueProds P] : P →* Pos P K where
  toFun p := Units.mk0 (PosZero.coeff p) (PosZero.coeff_ne_zero p)
  map_one' := Units.ext (map_one PosZero.coeff)
  map_mul' p q := Units.ext (map_mul PosZero.coeff p q)

@[simp]
theorem val_coeff [UniqueProds P] (p : P) :
    ((coeff p : Pos P K) : PosZero P K) = PosZero.coeff p :=
  (rfl)

/-- The variable generator indexed by `i : K`, as a unit in `Pos P K`. -/
def X (i : K) : Pos P K :=
  (PosZero.isUnit_X i).unit

@[simp]
theorem val_X (i : K) : ((X i : Pos P K) : PosZero P K) = PosZero.X i :=
  (PosZero.isUnit_X i).unit_spec

end Pos

end Generators

namespace PosZero

variable {P P' P'' K L M : Type*} [CommMonoid P]

/-- Semiring homomorphisms out of `MvPolynomial K (MonoidAlgebra ℕ P)` agree when they agree on
monoid-algebra basis elements and polynomial variables. -/
private theorem mvPoly_ringHom_ext {A : Type*} [Semiring A]
    {f g : MvPolynomial K (MonoidAlgebra ℕ P) →+* A}
    (hcoeff : ∀ p : P, f (MvPolynomial.C (MonoidAlgebra.single p 1)) =
      g (MvPolynomial.C (MonoidAlgebra.single p 1)))
    (hX : ∀ i : K, f (MvPolynomial.X i) = g (MvPolynomial.X i)) : f = g := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) hX
  have hring : f.comp MvPolynomial.C = g.comp MvPolynomial.C := by
    refine MonoidAlgebra.ringHom_ext (fun n ↦ ?_) fun p ↦ by simpa using hcoeff p
    have h1 : (MonoidAlgebra.single (1 : P) n : MonoidAlgebra ℕ P) = (n : MonoidAlgebra ℕ P) := by
      simp [MonoidAlgebra.natCast_def]
    simp [h1]
  exact DFunLike.congr_fun hring r

/-! ### Evaluation in semifields -/

section Eval

variable {S T : Type*} [Semifield S] [Subsingleton (AddUnits S)] [Semifield T]
  [Subsingleton (AddUnits T)]

/-- Polynomial evaluation of `MvPolynomial K (MonoidAlgebra ℕ P)` at a monoid homomorphism
`φ : P →* Sˣ` and a family of units `a : K → Sˣ`. -/
private def evalPoly (φ : P →* Sˣ) (a : K → Sˣ) :
    MvPolynomial K (MonoidAlgebra ℕ P) →+* S :=
  MvPolynomial.eval₂Hom (MonoidAlgebra.lift ℕ S P ((Units.coeHom S).comp φ)).toRingHom
    fun i ↦ (a i : S)

/-- Every regular polynomial in `MvPolynomial K (MonoidAlgebra ℕ P)` takes a unit value when
evaluated at units of a zero-sum-free semifield. -/
private theorem isUnit_evalPoly (φ : P →* Sˣ) (a : K → Sˣ)
    (p : regulars (MvPolynomial K (MonoidAlgebra ℕ P))) :
    IsUnit (evalPoly φ a (p : MvPolynomial K (MonoidAlgebra ℕ P))) := by
  have hp_ne : (p : MvPolynomial K (MonoidAlgebra ℕ P)) ≠ 0 := by
    intro h0
    have hreg : IsRegular (0 : MvPolynomial K (MonoidAlgebra ℕ P)) := h0 ▸ mem_regulars.mp p.2
    exact zero_ne_one (hreg.left (by simp))
  refine isUnit_iff_ne_zero.mpr fun h ↦ hp_ne ?_
  have hcoeff : ∀ r : MonoidAlgebra ℕ P,
      (MonoidAlgebra.lift ℕ S P ((Units.coeHom S).comp φ)).toRingHom r = 0 → r = 0 := by
    intro r hr
    have hne : ∀ (m : P) (n : ℕ), (algebraMap ℕ S) n * ((Units.coeHom S).comp φ) m = 0 → n = 0 := by
      intro m n hmn
      have hn : (n : S) = 0 := (mul_eq_zero.mp (by simpa using hmn)).resolve_right (φ m).ne_zero
      exact natCast_eq_zero_iff.mp hn
    exact (MonoidAlgebra.liftNC_eq_zero_iff hne).mp hr
  exact (MvPolynomial.eval₂_eq_zero_iff hcoeff
    (fun i ↦ (a i).isUnit.mem_nonZeroDivisors)).mp h

/-- Evaluation of positive subtraction-free rational functions at a multiplicative map
`φ : P →* Sˣ` and a family of units `a : K → Sˣ` of a zero-sum-free semifield `S`. -/
def eval (φ : P →* Sˣ) (a : K → Sˣ) : PosZero P K →+* S :=
  IsLocalization.lift (g := evalPoly φ a) (isUnit_evalPoly φ a)

@[simp]
theorem eval_algebraMap (φ : P →* Sˣ) (a : K → Sˣ) (p : MvPolynomial K (MonoidAlgebra ℕ P)) :
    eval φ a (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) p) =
      MvPolynomial.eval₂ (MonoidAlgebra.lift ℕ S P ((Units.coeHom S).comp φ)).toRingHom
        (fun i ↦ (a i : S)) p :=
  IsLocalization.lift_eq _ p

@[simp]
theorem eval_coeff (φ : P →* Sˣ) (a : K → Sˣ) (p : P) : eval φ a (coeff p) = φ p := by
  simp [← algebraMap_C_single]

@[simp]
theorem eval_X (φ : P →* Sˣ) (a : K → Sˣ) (i : K) : eval φ a (X i) = a i := by
  simp [← algebraMap_X]

/-- Evaluation of a fraction is the quotient of the values of its numerator and denominator. -/
theorem eval_mk' (φ : P →* Sˣ) (a : K → Sˣ) (p : MvPolynomial K (MonoidAlgebra ℕ P))
    (q : regulars (MvPolynomial K (MonoidAlgebra ℕ P))) :
    eval φ a (IsLocalization.mk' (PosZero P K) p q) =
      MvPolynomial.eval₂ (MonoidAlgebra.lift ℕ S P ((Units.coeHom S).comp φ)).toRingHom
          (fun i ↦ (a i : S)) p /
        MvPolynomial.eval₂ (MonoidAlgebra.lift ℕ S P ((Units.coeHom S).comp φ)).toRingHom
          (fun i ↦ (a i : S)) (q : MvPolynomial K (MonoidAlgebra ℕ P)) := by
  have hq : MvPolynomial.eval₂ (MonoidAlgebra.lift ℕ S P ((Units.coeHom S).comp φ)).toRingHom
      (fun i ↦ (a i : S)) (q : MvPolynomial K (MonoidAlgebra ℕ P)) ≠ 0 :=
    (isUnit_evalPoly φ a q).ne_zero
  rw [eq_div_iff hq, ← eval_algebraMap φ a q, ← map_mul, IsLocalization.mk'_spec, eval_algebraMap]

/-- Semiring maps out of `PosZero P K` agree when they agree on the coefficient and variable
generators. -/
@[ext]
theorem hom_ext {A : Type*} [Semiring A] {f g : PosZero P K →+* A}
    (hcoeff : ∀ p, f (coeff p) = g (coeff p)) (hX : ∀ i, f (X i) = g (X i)) : f = g :=
  IsLocalization.ringHom_ext (regulars (MvPolynomial K (MonoidAlgebra ℕ P))) <|
    mvPoly_ringHom_ext (fun p ↦ by simpa using hcoeff p) fun i ↦ by simpa using hX i

/-- Evaluation at the canonical coefficient and variable generators is the identity. -/
@[simp]
theorem eval_coeff_X_left [UniqueProds P] :
    eval (Pos.coeff : P →* Pos P K) (Pos.X : K → Pos P K) = RingHom.id (PosZero P K) := by
  ext p <;> simp

/-- A semiring map applied to an evaluation is evaluation at the images of the values. -/
@[simp]
theorem map_eval (f : S →+* T) (φ : P →* Sˣ) (a : K → Sˣ) (x : PosZero P K) :
    f (eval φ a x) = eval ((Units.map f).comp φ) (fun i ↦ Units.map f (a i)) x := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _ _) (fun p ↦ by simp) fun i ↦ by simp) x

theorem comp_eval (f : S →+* T) (φ : P →* Sˣ) (a : K → Sˣ) :
    f.comp (eval φ a) = eval ((Units.map f).comp φ) fun i ↦ Units.map f (a i) :=
  RingHom.ext (map_eval f φ a)

/-- **Universal property of `PosZero P K`.** For a cancellative commutative monoid `P`, semiring
maps from `PosZero P K` into a zero-sum-free semifield `S` correspond to pairs `(φ, a)` of a
monoid homomorphism `P →* Sˣ` and a family `K → Sˣ`, by evaluation. -/
def evalEquiv [IsCancelMul P] : ((P →* Sˣ) × (K → Sˣ)) ≃ (PosZero P K →+* S) where
  toFun pa := eval pa.1 pa.2
  invFun f :=
    ({ toFun p := ((isUnit_coeff (K := K) p).map f).unit
       map_one' := Units.ext <| by simp
       map_mul' p q := Units.ext <| by simp },
     fun i ↦ Units.map f (Pos.X (P := P) i))
  left_inv pa :=
    Prod.ext (MonoidHom.ext fun p ↦ Units.ext <| by simp) (funext fun i ↦ Units.ext <| by simp)
  right_inv f := by ext p <;> simp

@[simp]
theorem evalEquiv_apply [IsCancelMul P] (φ : P →* Sˣ) (a : K → Sˣ) :
    evalEquiv (φ, a) = eval φ a :=
  (rfl)

@[simp]
theorem evalEquiv_symm_fst_val [IsCancelMul P] (f : PosZero P K →+* S) (p : P) :
    (((evalEquiv.symm f).1 p : Sˣ) : S) = f (coeff p) :=
  ((isUnit_coeff (K := K) p).map f).unit_spec

@[simp]
theorem evalEquiv_symm_snd [IsCancelMul P] (f : PosZero P K →+* S) (i : K) :
    (evalEquiv.symm f).2 i = Units.map f (Pos.X (P := P) i) :=
  (rfl)

/-- Evaluate `PosZero P K` in an ambient non-associative semiring `R` by composing evaluation into
`WithZero Q` with a multiplicative and additive map `ι : Q →* R` (for example, the inclusion of an
addition-closed subgroup `Q ≤ Rˣ`). -/
def evalAlong {Q R : Type*} [CoefficientSemifield Q] [NonAssocSemiring R]
    (ι : Q →* R) (hadd : ∀ x y : Q, ι (x + y) = ι x + ι y) (φ : P →* Q) (a : K → Q) :
    PosZero P K →+* R :=
  (withZeroLift ι hadd).comp
    (eval (WithZero.unitsWithZeroEquiv.symm.toMonoidHom.comp φ)
      fun i ↦ WithZero.unitsWithZeroEquiv.symm (a i))

@[simp]
theorem evalAlong_coeff {Q R : Type*} [CoefficientSemifield Q] [NonAssocSemiring R]
    (ι : Q →* R) (hadd : ∀ x y : Q, ι (x + y) = ι x + ι y) (φ : P →* Q) (a : K → Q) (p : P) :
    evalAlong ι hadd φ a (coeff p) = ι (φ p) := by
  simp [evalAlong]

@[simp]
theorem evalAlong_X {Q R : Type*} [CoefficientSemifield Q] [NonAssocSemiring R]
    (ι : Q →* R) (hadd : ∀ x y : Q, ι (x + y) = ι x + ι y) (φ : P →* Q) (a : K → Q) (i : K) :
    evalAlong ι hadd φ a (X i) = ι (a i) := by
  simp [evalAlong]

/-- Uniqueness of evaluation into an ambient semiring `R`. -/
theorem evalAlong_unique {Q R : Type*} [CoefficientSemifield Q] [Semiring R]
    (ι : Q →* R) (hadd : ∀ x y : Q, ι (x + y) = ι x + ι y) (φ : P →* Q) (a : K → Q)
    (g : PosZero P K →+* R) (hcoeff : ∀ p, g (coeff p) = ι (φ p))
    (hX : ∀ i, g (X i) = ι (a i)) : g = evalAlong ι hadd φ a := by
  ext p
  · simp [hcoeff]
  · simp [hX]

theorem comp_evalAlong {Q R R' : Type*} [CoefficientSemifield Q] [NonAssocSemiring R]
    [NonAssocSemiring R'] (f : R →+* R') (ι : Q →* R) (hadd : ∀ x y : Q, ι (x + y) = ι x + ι y)
    (φ : P →* Q) (a : K → Q) :
    f.comp (evalAlong ι hadd φ a) =
      evalAlong (f.toMonoidHom.comp ι) (fun x y ↦ by simp [hadd]) φ a := by
  rw [evalAlong, evalAlong, ← RingHom.comp_assoc]
  congr 1
  exact withZeroLift_unique _ _ _ fun p ↦ by simp

end Eval

/-! ### Renaming the variables and changing coefficients -/

section Functoriality

/-- Reindex the variables of `PosZero P K` along an equivalence `e : K ≃ L`, as a
`MonoidAlgebra ℕ P`-algebra isomorphism. -/
def renameEquiv (e : K ≃ L) : PosZero P K ≃ₐ[MonoidAlgebra ℕ P] PosZero P L :=
  TotalQuotient.algEquivOfAlgEquiv (MvPolynomial.renameEquiv (MonoidAlgebra ℕ P) e)

@[simp]
theorem renameEquiv_algebraMap (e : K ≃ L) (p : MvPolynomial K (MonoidAlgebra ℕ P)) :
    renameEquiv e (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) p) =
      algebraMap (MvPolynomial L (MonoidAlgebra ℕ P)) (PosZero P L) (MvPolynomial.rename e p) :=
  TotalQuotient.algEquivOfAlgEquiv_algebraMap _ p

@[simp]
theorem renameEquiv_coeff (e : K ≃ L) (p : P) :
    renameEquiv e (coeff p : PosZero P K) = coeff p := by
  simp [← algebraMap_C_single]

@[simp]
theorem renameEquiv_X (e : K ≃ L) (i : K) :
    renameEquiv e (X i : PosZero P K) = X (e i) := by
  simp [← algebraMap_X]

@[simp]
theorem renameEquiv_refl :
    renameEquiv (P := P) (Equiv.refl K) = AlgEquiv.refl := by
  ext x
  obtain ⟨⟨p, q⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (regulars (MvPolynomial K (MonoidAlgebra ℕ P))) x
  simp [renameEquiv]

@[simp]
theorem renameEquiv_symm (e : K ≃ L) :
    (renameEquiv (P := P) e).symm = renameEquiv e.symm :=
  TotalQuotient.algEquivOfAlgEquiv_symm _

@[simp]
theorem renameEquiv_trans (e : K ≃ L) (f : L ≃ M) :
    (renameEquiv (P := P) e).trans (renameEquiv f) = renameEquiv (e.trans f) := by
  ext x
  obtain ⟨⟨p, q⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (regulars (MvPolynomial K (MonoidAlgebra ℕ P))) x
  simp [renameEquiv]

/-- Rename the variables of `PosZero P K` along any function `r : K → L`. -/
def rename [UniqueProds P] (r : K → L) : PosZero P K →+* PosZero P L :=
  eval Pos.coeff fun i ↦ Pos.X (r i)

@[simp]
theorem rename_coeff [UniqueProds P] (r : K → L) (p : P) :
    rename r (coeff p) = coeff p := by
  simp [rename]

@[simp]
theorem rename_X [UniqueProds P] (r : K → L) (i : K) :
    rename (P := P) r (X i) = X (r i) := by
  simp [rename]

@[simp]
theorem rename_algebraMap [UniqueProds P] (r : K → L) (p : MvPolynomial K (MonoidAlgebra ℕ P)) :
    rename r (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) p) =
      algebraMap (MvPolynomial L (MonoidAlgebra ℕ P)) (PosZero P L) (MvPolynomial.rename r p) :=
  DFunLike.congr_fun
    (mvPoly_ringHom_ext
      (f := (rename (P := P) r).comp (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) _))
      (g := (algebraMap (MvPolynomial L (MonoidAlgebra ℕ P)) _).comp
        (MvPolynomial.rename r).toRingHom)
      (fun p ↦ by simp) fun i ↦ by simp) p

theorem renameEquiv_apply [UniqueProds P] (e : K ≃ L) (x : PosZero P K) :
    renameEquiv e x = rename e x :=
  DFunLike.congr_fun
    (hom_ext (f := (renameEquiv e).toRingHom) (g := rename e) (fun p ↦ by simp) fun i ↦ by simp) x

@[simp]
theorem rename_id [UniqueProds P] : rename (id : K → K) = RingHom.id (PosZero P K) := by
  ext p <;> simp

@[simp]
theorem rename_rename [UniqueProds P] (r : K → L) (s : L → M) (x : PosZero P K) :
    rename s (rename r x) = rename (s ∘ r) x := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := rename _) (fun p ↦ by simp) fun i ↦ by simp) x

theorem rename_comp_rename [UniqueProds P] (r : K → L) (s : L → M) :
    (rename s).comp (rename r) = rename (P := P) (s ∘ r) :=
  RingHom.ext (rename_rename r s)

@[simp]
theorem eval_rename [UniqueProds P] {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]
    (r : K → L) (φ : P →* Sˣ) (a : L → Sˣ) (x : PosZero P K) :
    eval φ a (rename r x) = eval φ (a ∘ r) x := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _ _) (fun p ↦ by simp) fun i ↦ by simp) x

/-- Renaming along an injective function is injective. -/
theorem rename_injective [UniqueProds P] {r : K → L} (hr : Function.Injective r) :
    Function.Injective (rename (P := P) r) := by
  refine IsLocalization.lift_injective_of_injective _ ?_
  have hcomp : evalPoly (Pos.coeff : P →* Pos P L) (fun i ↦ Pos.X (r i)) =
      (algebraMap (MvPolynomial L (MonoidAlgebra ℕ P)) (PosZero P L)).comp
        (MvPolynomial.rename r).toRingHom :=
    mvPoly_ringHom_ext (fun p ↦ by simp [evalPoly]) fun i ↦ by simp [evalPoly]
  rw [hcomp, RingHom.coe_comp]
  exact (FaithfulSMul.algebraMap_injective _ _).comp (MvPolynomial.rename_injective r hr)

/-- Push coefficients forward along a monoid homomorphism `ψ : P →* P'`. -/
def mapCoeff [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') :
    PosZero P K →+* PosZero P' K :=
  eval (Pos.coeff.comp ψ) Pos.X

@[simp]
theorem mapCoeff_coeff [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') (p : P) :
    mapCoeff (K := K) ψ (coeff p) = coeff (ψ p) := by
  simp [mapCoeff]

@[simp]
theorem mapCoeff_X [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') (i : K) :
    mapCoeff ψ (X i) = X i := by
  simp [mapCoeff]

@[simp]
theorem mapCoeff_algebraMap [CommMonoid P'] [UniqueProds P'] (ψ : P →* P')
    (p : MvPolynomial K (MonoidAlgebra ℕ P)) :
    mapCoeff ψ (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) p) =
      algebraMap (MvPolynomial K (MonoidAlgebra ℕ P')) (PosZero P' K)
        (MvPolynomial.map (MonoidAlgebra.mapDomainRingHom ℕ ψ) p) :=
  DFunLike.congr_fun
    (mvPoly_ringHom_ext
      (f := (mapCoeff (K := K) ψ).comp (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) _))
      (g := (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P')) _).comp
        (MvPolynomial.map (MonoidAlgebra.mapDomainRingHom ℕ ψ)))
      (fun p ↦ by simp) fun i ↦ by simp) p

@[simp]
theorem mapCoeff_id [UniqueProds P] :
    mapCoeff (K := K) (MonoidHom.id P) = RingHom.id (PosZero P K) := by
  ext p <;> simp

@[simp]
theorem mapCoeff_mapCoeff [CommMonoid P'] [UniqueProds P'] [CommMonoid P''] [UniqueProds P'']
    (ψ : P →* P') (χ : P' →* P'') (x : PosZero P K) :
    mapCoeff χ (mapCoeff ψ x) = mapCoeff (χ.comp ψ) x := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := mapCoeff _) (fun p ↦ by simp) fun i ↦ by simp) x

theorem mapCoeff_comp_mapCoeff [CommMonoid P'] [UniqueProds P'] [CommMonoid P''] [UniqueProds P'']
    (ψ : P →* P') (χ : P' →* P'') :
    (mapCoeff (K := K) χ).comp (mapCoeff ψ) = mapCoeff (χ.comp ψ) :=
  RingHom.ext (mapCoeff_mapCoeff ψ χ)

@[simp]
theorem eval_mapCoeff [CommMonoid P'] [UniqueProds P'] {S : Type*} [Semifield S]
    [Subsingleton (AddUnits S)] (ψ : P →* P') (φ : P' →* Sˣ) (a : K → Sˣ) (x : PosZero P K) :
    eval φ a (mapCoeff ψ x) = eval (φ.comp ψ) a x := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _ _) (fun p ↦ by simp) fun i ↦ by simp) x

theorem mapCoeff_rename [UniqueProds P] [CommMonoid P'] [UniqueProds P']
    (ψ : P →* P') (r : K → L) (x : PosZero P K) :
    mapCoeff ψ (rename r x) = rename r (mapCoeff ψ x) := by
  rw [← RingHom.comp_apply, ← RingHom.comp_apply]
  exact DFunLike.congr_fun
    (hom_ext (f := (mapCoeff ψ).comp (rename r)) (g := (rename r).comp (mapCoeff ψ))
      (fun p ↦ by simp) fun i ↦ by simp) x

/-- Pushing coefficients forward along an injective monoid homomorphism is injective. -/
theorem mapCoeff_injective [CommMonoid P'] [UniqueProds P'] {ψ : P →* P'}
    (hψ : Function.Injective ψ) : Function.Injective (mapCoeff (K := K) ψ) := by
  refine IsLocalization.lift_injective_of_injective _ ?_
  have hcomp : evalPoly (Pos.coeff.comp ψ : P →* Pos P' K) (Pos.X : K → Pos P' K) =
      (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P')) (PosZero P' K)).comp
        (MvPolynomial.map (MonoidAlgebra.mapDomainRingHom ℕ ψ)) :=
    mvPoly_ringHom_ext (fun p ↦ by simp [evalPoly]) fun i ↦ by simp [evalPoly]
  rw [hcomp, RingHom.coe_comp]
  exact (FaithfulSMul.algebraMap_injective _ _).comp
    (MvPolynomial.map_injective _ (MonoidAlgebra.mapDomain_injective hψ))

end Functoriality

/-! ### Finite-support laws -/

section FiniteSupport

/-- Every element of `PosZero P K` involves only finitely many variables, so it lies in the image
of `rename Subtype.val` for some finite subset `s : Finset K`. -/
theorem exists_finset_rename [UniqueProds P] (x : PosZero P K) :
    ∃ (s : Finset K) (x' : PosZero P s), rename Subtype.val x' = x := by
  obtain ⟨⟨p, q⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (regulars (MvPolynomial K (MonoidAlgebra ℕ P))) x
  obtain ⟨s, p', q', hp', hq_eq⟩ :=
    MvPolynomial.exists_finset_rename₂ p (q : MvPolynomial K (MonoidAlgebra ℕ P))
  have hq' : q' ∈ regulars (MvPolynomial s (MonoidAlgebra ℕ P)) := by
    rw [mem_regulars_iff_ne_zero]
    intro h0
    have hq0 : (q : MvPolynomial K (MonoidAlgebra ℕ P)) = 0 := by rw [hq_eq, h0, map_zero]
    exact mem_regulars_iff_ne_zero.mp q.2 hq0
  refine ⟨s, IsLocalization.mk' (PosZero P s) p' ⟨q', hq'⟩, ?_⟩
  apply (IsLocalization.map_units (PosZero P K) q).mul_right_inj.mp
  have hspec : algebraMap (MvPolynomial s (MonoidAlgebra ℕ P)) (PosZero P s) q' *
      IsLocalization.mk' (PosZero P s) p' ⟨q', hq'⟩ =
      algebraMap (MvPolynomial s (MonoidAlgebra ℕ P)) (PosZero P s) p' :=
    IsLocalization.mk'_spec' (PosZero P s) p' ⟨q', hq'⟩
  rw [IsLocalization.mk'_spec', hq_eq, ← rename_algebraMap Subtype.val q', ← map_mul, hspec,
    rename_algebraMap, ← hp']

/-- Auxiliary finite-support congruence for polynomial evaluation `evalPoly`. -/
private theorem evalPoly_congr {S : Type*} [Semifield S]
    (r : MvPolynomial K (MonoidAlgebra ℕ P)) {φ₁ φ₂ : P →* Sˣ} {a₁ a₂ : K → Sˣ}
    (hφ : ∀ m ∈ r.support, ∀ p ∈ (r.coeff m).coeff.support, φ₁ p = φ₂ p)
    (ha : ∀ i ∈ r.vars, a₁ i = a₂ i) :
    evalPoly φ₁ a₁ r = evalPoly φ₂ a₂ r := by
  simp only [evalPoly, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  refine congrArg₂ (· * ·) ?_ ?_
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    simp [hφ m hm p hp]
  · refine Finset.prod_congr rfl fun i hi ↦ ?_
    simp [ha i (MvPolynomial.support_subset_vars_of_mem_support hm hi)]

universe u

/-- Evaluation of any element of `PosZero P K` depends on the coefficient map and variable family
only on finite subsets of `P` and `K`. -/
theorem exists_finset_eval_eq (x : PosZero P K) :
    ∃ (t : Finset P) (s : Finset K),
      ∀ {S : Type u} [Semifield S] [Subsingleton (AddUnits S)]
        {φ₁ φ₂ : P →* Sˣ} {a₁ a₂ : K → Sˣ},
        (∀ p ∈ t, φ₁ p = φ₂ p) → (∀ i ∈ s, a₁ i = a₂ i) →
          eval φ₁ a₁ x = eval φ₂ a₂ x := by
  classical
  obtain ⟨⟨p, q⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (regulars (MvPolynomial K (MonoidAlgebra ℕ P))) x
  refine ⟨(p.support.biUnion fun m ↦ (p.coeff m).coeff.support) ∪
      ((q : MvPolynomial K (MonoidAlgebra ℕ P)).support.biUnion fun m ↦
        ((q : MvPolynomial K (MonoidAlgebra ℕ P)).coeff m).coeff.support),
    p.vars ∪ (q : MvPolynomial K (MonoidAlgebra ℕ P)).vars, ?_⟩
  intro S _ _ φ₁ φ₂ a₁ a₂ hφ ha
  rw [eval_mk', eval_mk']
  have hp : evalPoly φ₁ a₁ p = evalPoly φ₂ a₂ p := by
    apply evalPoly_congr
    · intro m hm c hc
      exact hφ c (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, hm, hc⟩))
    · intro i hi
      exact ha i (Finset.mem_union_left _ hi)
  have hq : evalPoly φ₁ a₁ (q : MvPolynomial K (MonoidAlgebra ℕ P)) =
      evalPoly φ₂ a₂ (q : MvPolynomial K (MonoidAlgebra ℕ P)) := by
    apply evalPoly_congr
    · intro m hm c hc
      exact hφ c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m, hm, hc⟩))
    · intro i hi
      exact ha i (Finset.mem_union_right _ hi)
  simpa only [evalPoly, MvPolynomial.coe_eval₂Hom] using congrArg₂ (· / ·) hp hq

end FiniteSupport

end PosZero

namespace Pos

/-! ### The positive coefficient semifield -/

variable {P P' P'' K L M : Type*} [CommMonoid P] [UniqueProds P]
variable {Q R : Type*} [CoefficientSemifield Q] [CoefficientSemifield R]

/-- Evaluation of positive subtraction-free rational functions in a coefficient semifield `Q`,
sending `coeff p` to `φ p` and `X i` to `a i`. -/
def eval (φ : P →* Q) (a : K → Q) : CoefficientSemifieldHom (Pos P K) Q :=
  unitsWithZeroRingEquiv.toCoefficientSemifieldHom.comp
    (PosZero.eval (WithZero.unitsWithZeroEquiv.symm.toMonoidHom.comp φ)
      fun i ↦ WithZero.unitsWithZeroEquiv.symm (a i)).mapUnits

/-- Evaluation in a coefficient semifield is evaluation in the semifield obtained by adjoining
zero. -/
theorem coe_eval_apply (φ : P →* Q) (a : K → Q) (x : Pos P K) :
    (eval φ a x : WithZero Q) =
      PosZero.eval (WithZero.unitsWithZeroEquiv.symm.toMonoidHom.comp φ)
        (fun i ↦ WithZero.unitsWithZeroEquiv.symm (a i)) (x : PosZero P K) := by
  simp [eval]

@[simp]
theorem eval_coeff (φ : P →* Q) (a : K → Q) (p : P) : eval φ a (coeff p) = φ p :=
  WithZero.coe_injective <| by simp [coe_eval_apply]

@[simp]
theorem eval_X (φ : P →* Q) (a : K → Q) (i : K) : eval φ a (X i) = a i :=
  WithZero.coe_injective <| by simp [coe_eval_apply]

/-- Homomorphisms out of `Pos P K` agree when they agree on the coefficient and variable
generators. -/
@[ext]
theorem hom_ext {f g : CoefficientSemifieldHom (Pos P K) Q}
    (hcoeff : ∀ p, f (coeff p) = g (coeff p)) (hX : ∀ i, f (X i) = g (X i)) : f = g := by
  refine CoefficientSemifieldHom.withZeroMap_injective ?_
  have h : f.withZeroMap.comp (withZeroUnitsRingEquiv (PosZero P K)).symm.toRingHom =
      g.withZeroMap.comp (withZeroUnitsRingEquiv (PosZero P K)).symm.toRingHom :=
    PosZero.hom_ext
      (fun p ↦ by simpa [← val_coeff] using congrArg WithZero.coe (hcoeff p))
      (fun i ↦ by simpa [← val_X] using congrArg WithZero.coe (hX i))
  simpa [RingHom.comp_assoc] using
    congrArg (·.comp (withZeroUnitsRingEquiv (PosZero P K)).toRingHom) h

/-- **Universal property of `Pos P K`.** Homomorphisms from `Pos P K` to a coefficient semifield
`Q` correspond to pairs `(φ, a)` of a monoid homomorphism `P →* Q` and a family `K → Q`, by
evaluation. -/
def evalEquiv : ((P →* Q) × (K → Q)) ≃ CoefficientSemifieldHom (Pos P K) Q where
  toFun pa := eval pa.1 pa.2
  invFun f := (f.toMonoidHom.comp coeff, fun i ↦ f (X i))
  left_inv pa := Prod.ext (MonoidHom.ext (eval_coeff pa.1 pa.2)) (funext (eval_X pa.1 pa.2))
  right_inv f := by ext p <;> simp

@[simp]
theorem evalEquiv_apply (φ : P →* Q) (a : K → Q) : evalEquiv (φ, a) = eval φ a :=
  (rfl)

@[simp]
theorem evalEquiv_symm_fst (f : CoefficientSemifieldHom (Pos P K) Q) :
    (evalEquiv.symm f).1 = f.toMonoidHom.comp coeff :=
  (rfl)

@[simp]
theorem evalEquiv_symm_snd (f : CoefficientSemifieldHom (Pos P K) Q) (i : K) :
    (evalEquiv.symm f).2 i = f (X i) :=
  (rfl)

/-- Evaluation at the canonical coefficient and variable generators is the identity. -/
@[simp]
theorem eval_coeff_X_left :
    eval (coeff : P →* Pos P K) (X : K → Pos P K) = CoefficientSemifieldHom.id (Pos P K) := by
  ext p <;> simp

/-- A homomorphism applied to an evaluation is evaluation at the images of the values. -/
@[simp]
theorem map_eval (f : CoefficientSemifieldHom Q R) (φ : P →* Q) (a : K → Q) (x : Pos P K) :
    f (eval φ a x) = eval (f.toMonoidHom.comp φ) (f ∘ a) x := by
  rw [← CoefficientSemifieldHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _ _) (fun p ↦ by simp) fun i ↦ by simp) x

theorem comp_eval (f : CoefficientSemifieldHom Q R) (φ : P →* Q) (a : K → Q) :
    f.comp (eval φ a) = eval (f.toMonoidHom.comp φ) (f ∘ a) :=
  CoefficientSemifieldHom.ext fun x ↦ (f.comp_apply _ x).trans (map_eval f φ a x)

section Semifield

variable {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]

/-- Restricting evaluation in a semifield to the units is evaluation in its coefficient semifield
of units. -/
theorem mapUnits_eval (φ : P →* Sˣ) (a : K → Sˣ) : (PosZero.eval φ a).mapUnits = eval φ a := by
  ext p <;> simp

/-- Evaluation in the coefficient semifield of units of a semifield is evaluation in the
semifield. -/
@[simp]
theorem val_eval (φ : P →* Sˣ) (a : K → Sˣ) (x : Pos P K) :
    (eval φ a x : S) = PosZero.eval φ a x := by
  rw [← mapUnits_eval, RingHom.val_mapUnits]

end Semifield

/-- Evaluating a unit of `PosZero P K` in an ambient non-associative semiring `R` along `ι : Q →* R`
agrees with evaluating it in `Q` and then applying `ι`. -/
@[simp]
theorem evalAlong_val {R : Type*} [NonAssocSemiring R]
    (ι : Q →* R) (hadd : ∀ x y : Q, ι (x + y) = ι x + ι y) (φ : P →* Q) (a : K → Q)
    (x : Pos P K) :
    PosZero.evalAlong ι hadd φ a (x : PosZero P K) = ι (eval φ a x) := by
  rw [PosZero.evalAlong, RingHom.comp_apply, ← coe_eval_apply, withZeroLift_coe]

/-! ### Renaming the variables and changing coefficients -/

/-- Rename the variables of `Pos P K` along a function `r : K → L`. -/
def rename (r : K → L) : CoefficientSemifieldHom (Pos P K) (Pos P L) :=
  (PosZero.rename r).mapUnits

@[simp]
theorem val_rename (r : K → L) (x : Pos P K) :
    (rename r x : PosZero P L) = PosZero.rename r x :=
  RingHom.val_mapUnits _ x

/-- Renaming is evaluation at the renamed variables. -/
theorem rename_eq_eval (r : K → L) :
    rename r = eval (coeff : P →* Pos P L) fun i ↦ X (r i) :=
  mapUnits_eval _ _

@[simp]
theorem rename_coeff (r : K → L) (p : P) : rename r (coeff p) = coeff p :=
  Units.ext <| by simp

@[simp]
theorem rename_X (r : K → L) (i : K) : rename (P := P) r (X i) = X (r i) :=
  Units.ext <| by simp

@[simp]
theorem rename_id : rename (id : K → K) = CoefficientSemifieldHom.id (Pos P K) := by
  ext p <;> simp

@[simp]
theorem rename_rename (r : K → L) (s : L → M) (x : Pos P K) :
    rename s (rename r x) = rename (s ∘ r) x :=
  Units.ext <| by simp

theorem rename_comp_rename (r : K → L) (s : L → M) :
    (rename (P := P) s).comp (rename r) = rename (s ∘ r) :=
  CoefficientSemifieldHom.ext fun x ↦ by simp

@[simp]
theorem eval_rename (r : K → L) (φ : P →* Q) (a : L → Q) (x : Pos P K) :
    eval φ a (rename r x) = eval φ (a ∘ r) x := by
  rw [← CoefficientSemifieldHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _ _) (fun p ↦ by simp) fun i ↦ by simp) x

/-- Renaming along an injective function is injective. -/
theorem rename_injective {r : K → L} (hr : Function.Injective r) :
    Function.Injective (rename (P := P) r) := fun _ _ h ↦
  Units.ext <| PosZero.rename_injective hr <| by simpa using congrArg Units.val h

/-- Push coefficients forward along a monoid homomorphism `ψ : P →* P'`. -/
def mapCoeff [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') :
    CoefficientSemifieldHom (Pos P K) (Pos P' K) :=
  (PosZero.mapCoeff ψ).mapUnits

@[simp]
theorem val_mapCoeff [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') (x : Pos P K) :
    (mapCoeff ψ x : PosZero P' K) = PosZero.mapCoeff ψ x :=
  RingHom.val_mapUnits _ x

/-- Pushing coefficients forward is evaluation at `coeff.comp ψ` and `X`. -/
theorem mapCoeff_eq_eval [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') :
    mapCoeff (K := K) ψ = eval (coeff.comp ψ) X :=
  mapUnits_eval _ _

@[simp]
theorem mapCoeff_coeff [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') (p : P) :
    mapCoeff (K := K) ψ (coeff p) = coeff (ψ p) :=
  Units.ext <| by simp

@[simp]
theorem mapCoeff_X [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') (i : K) :
    mapCoeff ψ (X i) = X i :=
  Units.ext <| by simp

@[simp]
theorem mapCoeff_id :
    mapCoeff (K := K) (MonoidHom.id P) = CoefficientSemifieldHom.id (Pos P K) := by
  ext p <;> simp

@[simp]
theorem mapCoeff_mapCoeff [CommMonoid P'] [UniqueProds P'] [CommMonoid P''] [UniqueProds P'']
    (ψ : P →* P') (χ : P' →* P'') (x : Pos P K) :
    mapCoeff χ (mapCoeff ψ x) = mapCoeff (χ.comp ψ) x :=
  Units.ext <| by simp

theorem mapCoeff_comp_mapCoeff [CommMonoid P'] [UniqueProds P'] [CommMonoid P''] [UniqueProds P'']
    (ψ : P →* P') (χ : P' →* P'') :
    (mapCoeff (K := K) χ).comp (mapCoeff ψ) = mapCoeff (χ.comp ψ) :=
  CoefficientSemifieldHom.ext fun x ↦
    ((mapCoeff χ).comp_apply _ x).trans (mapCoeff_mapCoeff ψ χ x)

@[simp]
theorem eval_mapCoeff [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') (φ : P' →* Q)
    (a : K → Q) (x : Pos P K) :
    eval φ a (mapCoeff ψ x) = eval (φ.comp ψ) a x := by
  rw [← CoefficientSemifieldHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _ _) (fun p ↦ by simp) fun i ↦ by simp) x

theorem mapCoeff_rename [CommMonoid P'] [UniqueProds P'] (ψ : P →* P') (r : K → L) (x : Pos P K) :
    mapCoeff ψ (rename r x) = rename r (mapCoeff ψ x) :=
  Units.ext <| by simpa using PosZero.mapCoeff_rename ψ r x

/-- Pushing coefficients forward along an injective monoid homomorphism is injective. -/
theorem mapCoeff_injective [CommMonoid P'] [UniqueProds P'] {ψ : P →* P'}
    (hψ : Function.Injective ψ) : Function.Injective (mapCoeff (K := K) ψ) := fun _ _ h ↦
  Units.ext <| PosZero.mapCoeff_injective hψ <| by simpa using congrArg Units.val h

/-! ### Finite-support laws -/

/-- Every element of `Pos P K` involves only finitely many variables, so it lies in the image of
`rename Subtype.val` for some finite subset `s : Finset K`. -/
theorem exists_finset_rename (x : Pos P K) :
    ∃ (s : Finset K) (x' : Pos P s), rename Subtype.val x' = x := by
  obtain ⟨s, y, hy⟩ := PosZero.exists_finset_rename (x : PosZero P K)
  have hy_ne : y ≠ 0 := by
    intro h0
    exact x.ne_zero (by rw [← hy, h0, map_zero])
  exact ⟨s, Units.mk0 y hy_ne, Units.ext (by simpa using hy)⟩

universe u

/-- Evaluation of any element of `Pos P K` depends on the coefficient homomorphism and variable
family only on finite subsets of `P` and `K`. -/
theorem exists_finset_eval_eq (x : Pos P K) :
    ∃ (t : Finset P) (s : Finset K),
      ∀ {Q : Type u} [CoefficientSemifield Q] {φ₁ φ₂ : P →* Q} {a₁ a₂ : K → Q},
        (∀ p ∈ t, φ₁ p = φ₂ p) → (∀ i ∈ s, a₁ i = a₂ i) →
          eval φ₁ a₁ x = eval φ₂ a₂ x := by
  obtain ⟨t, s, h⟩ := PosZero.exists_finset_eval_eq.{u} (x : PosZero P K)
  refine ⟨t, s, fun hφ ha ↦ WithZero.coe_injective ?_⟩
  rw [coe_eval_apply, coe_eval_apply]
  exact h (fun p hp ↦ congrArg WithZero.unitsWithZeroEquiv.symm (hφ p hp))
    (fun i hi ↦ congrArg WithZero.unitsWithZeroEquiv.symm (ha i hi))

end Pos

end TauCeti
