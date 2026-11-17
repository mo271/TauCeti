/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.Geometry.Variational.PolynomialJet.Basic
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.ExteriorAlgebra.BaseChange
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Relative vertical forms and unsigned horizontal differential on polynomial jets

This file develops the vertical and unsigned horizontal differential calculus on
`TauCeti.PolynomialJet R ι α` over an arbitrary commutative ring `R` (and commutative semiring
for the coordinate partial-derivative commutators), without characteristic restrictions or
choices of coordinate orderings.

First, we prove the commutator identities between coordinate partial derivatives and total
derivatives `PolynomialJet.totalDeriv`, together with stage preservation for partial derivatives.

Next, we introduce the constant horizontal and contact exterior algebras
`PolynomialJet.HorizAlgebra R ι` and `PolynomialJet.ContactAlgebra R ι α`, and the relative
vertical exterior algebra `PolynomialJet.VerticalForm R ι α` of polynomial jets tensored with
constant contact forms. Its differential `PolynomialJet.verticalAlgDeriv` (`d_alg`) is a
degree-one graded derivation squaring to zero, and under `PolynomialJet.verticalKaehlerEquiv` it
matches Mathlib's relative Kähler differentials over `PolynomialJet.baseSubalgebra`.

Each total derivative lifts to an even derivation `PolynomialJet.liftedTotalDeriv i` sending
`θᵃ_I` to `θᵃ_(I+eᵢ)`, constructed on homogeneous contact exterior powers via
`exteriorPower.lieMap`. These lifted total derivatives commute pairwise and commute with
`verticalAlgDeriv`. Over a finite base index type `ι`, they assemble into the unsigned horizontal
differential `PolynomialJet.unsignedHorizDeriv` (`D_H⁰`) on
`VerticalForm R ι α ⊗[R] HorizAlgebra R ι`, which squares to zero and commutes (without sign)
with `verticalAlgDeriv ⊗ id`.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, for the jet-coordinate
  commutator (Lemma 1.3) and vertical exterior calculus.
* R. E. Borcherds, *Quantum Field Theory* lecture notes, p. 49, for the commuting relative
  vertical differential `d_alg` and unsigned horizontal differential `D_H⁰`.
-/

public section

open scoped TensorProduct BigOperators

namespace TauCeti
namespace PolynomialJet

open MvPolynomial

noncomputable section

/-! ### Partial derivatives and jet commutators -/

section PDeriv

variable {R ι α : Type*} [CommSemiring R]

/-- Base partial derivatives commute with total derivatives. -/
theorem pderiv_base_totalDeriv (i j : ι) (p : PolynomialJet R ι α) :
    pderiv (Sum.inl j) (totalDeriv i p) = totalDeriv i (pderiv (Sum.inl j) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    have hv : pderiv (R := R) (Sum.inl j) (totalDeriv i (X v)) =
        totalDeriv i (pderiv (Sum.inl j) (X v)) := by
      rcases v with k | ⟨a, I⟩
      · simp only [totalDeriv_X_base, pderiv_X, Pi.single_apply, Sum.inl.injEq]
        have h1 : pderiv (Sum.inl j : ι ⊕ (α × (ι →₀ ℕ)))
            (if i = k then (1 : PolynomialJet R ι α) else 0) = 0 := by
          split_ifs <;> simp
        have h2 : totalDeriv i
            (if k = j then (1 : PolynomialJet R ι α) else 0) = 0 := by
          split_ifs <;> simp
        rw [h1, h2]
      · simp
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, hv]
    ring

/-- **Fundamental jet commutator (Anderson, Lemma 1.3)**: differentiating a total derivative with
respect to a field jet coordinate `uᵃ_J` adds the lower-order partial derivative `∂/∂uᵃ_(J-eᵢ)`
whenever `J i ≠ 0`. -/
theorem pderiv_field_totalDeriv (i : ι) (a : α) (J : ι →₀ ℕ) (p : PolynomialJet R ι α) :
    pderiv (Sum.inr (a, J)) (totalDeriv i p) =
      totalDeriv i (pderiv (Sum.inr (a, J)) p) +
        if J i = 0 then 0 else pderiv (Sum.inr (a, J - Finsupp.single i 1)) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    split_ifs <;> ring
  | mul_X p v hp =>
    have hv : pderiv (R := R) (Sum.inr (a, J)) (totalDeriv i (X v)) =
        totalDeriv i (pderiv (Sum.inr (a, J)) (X v)) +
          if J i = 0 then 0 else pderiv (Sum.inr (a, J - Finsupp.single i 1)) (X v) := by
      rcases v with j | ⟨b, K⟩
      · simp only [totalDeriv_X_base, pderiv_X, Pi.single_apply, reduceCtorEq, ite_false,
          map_zero, zero_add, ite_self]
        split_ifs <;> simp
      · simp only [totalDeriv_X_field, pderiv_X, Pi.single_apply, Sum.inr.injEq, Prod.mk.injEq]
        have hD : totalDeriv i
            (if b = a ∧ K = J then (1 : PolynomialJet R ι α) else 0) = 0 := by
          split_ifs <;> simp
        rw [hD, zero_add]
        by_cases hJ : J i = 0
        · simp only [hJ, ↓reduceIte]
          have hne : K + Finsupp.single i 1 ≠ J := by
            intro h
            have hi := congrArg (fun f : ι →₀ ℕ ↦ f i) h
            simp [hJ] at hi
          simp [hne]
        · simp only [hJ, ↓reduceIte]
          have hiff : (b = a ∧ K + Finsupp.single i 1 = J) ↔
              (b = a ∧ K = J - Finsupp.single i 1) := by
            constructor
            · rintro ⟨rfl, rfl⟩
              exact ⟨rfl, (add_tsub_cancel_right K _).symm⟩
            · rintro ⟨rfl, rfl⟩
              exact ⟨rfl, Finsupp.sub_add_single_one_cancel hJ⟩
          simp [hiff]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, hv]
    split_ifs <;> ring

/-- When `J i = 0`, the partial derivative `∂/∂uᵃ_J` commutes with `totalDeriv i`. -/
theorem pderiv_field_totalDeriv_of_eq_zero (i : ι) (a : α) {J : ι →₀ ℕ} (hJ : J i = 0)
    (p : PolynomialJet R ι α) :
    pderiv (Sum.inr (a, J)) (totalDeriv i p) = totalDeriv i (pderiv (Sum.inr (a, J)) p) := by
  simpa [hJ] using pderiv_field_totalDeriv i a J p

/-- Differentiating `totalDeriv i p` with respect to `uᵃ_(I+eᵢ)` yields
`totalDeriv i (∂p/∂uᵃ_(I+eᵢ)) + ∂p/∂uᵃ_I`. -/
theorem pderiv_field_add_single_totalDeriv (i : ι) (a : α) (I : ι →₀ ℕ)
    (p : PolynomialJet R ι α) :
    pderiv (Sum.inr (a, I + Finsupp.single i 1)) (totalDeriv i p) =
      totalDeriv i (pderiv (Sum.inr (a, I + Finsupp.single i 1)) p) +
        pderiv (Sum.inr (a, I)) p := by
  have hne : (I + Finsupp.single i 1 : ι →₀ ℕ) i ≠ 0 := by simp
  have hsub : (I + Finsupp.single i 1) - Finsupp.single i 1 = I := add_tsub_cancel_right I _
  rw [pderiv_field_totalDeriv, ite_eq_right_iff.mpr fun h ↦ (hne h).elim, hsub]

/-- Partial differentiation does not raise the finite jet stage. -/
theorem pderiv_mem_stage (v : ι ⊕ (α × (ι →₀ ℕ))) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : pderiv v p ∈ stage R ι α r := by
  classical
  rw [mem_stage_iff] at hp ⊢
  intro a I hmem
  rw [MvPolynomial.mem_vars_iff_mem_support] at hmem
  obtain ⟨m, hm, hsupp⟩ := hmem
  rw [MvPolynomial.mem_support_iff, coeff_pderiv] at hm
  have hcoeff : p.coeff (m + Finsupp.single v 1) ≠ 0 := left_ne_zero_of_mul hm
  have hmemp : Sum.inr (a, I) ∈ p.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    refine ⟨m + Finsupp.single v 1, MvPolynomial.mem_support_iff.mpr hcoeff, ?_⟩
    rw [Finsupp.mem_support_iff] at hsupp ⊢
    simp [hsupp]
  exact hp a I hmemp

/-- A stage-`r` jet polynomial has vanishing partial derivative with respect to every field
coordinate of order strictly greater than `r`. -/
theorem pderiv_field_eq_zero_of_stage_lt {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) (a : α) {I : ι →₀ ℕ} (hI : r < I.degree) :
    pderiv (Sum.inr (a, I)) p = 0 :=
  pderiv_eq_zero_of_notMem_vars fun hmem ↦ hI.not_ge ((mem_stage_iff p r).mp hp a I hmem)

end PDeriv

/-! ### Horizontal, contact, and relative vertical exterior algebras -/

section Vertical

variable {R ι α : Type*} [CommRing R]

/-- The constant-coefficient horizontal exterior algebra `⋀(ι →₀ R)`. -/
abbrev HorizAlgebra (R ι : Type*) [CommRing R] :=
  ExteriorAlgebra R (ι →₀ R)

/-- The constant-coefficient contact exterior algebra `⋀((α × (ι →₀ ℕ)) →₀ R)`. -/
abbrev ContactAlgebra (R ι α : Type*) [CommRing R] :=
  ExteriorAlgebra R ((α × (ι →₀ ℕ)) →₀ R)

/-- The relative vertical exterior algebra `PolynomialJet R ι α ⊗[R] ContactAlgebra R ι α`
(`Ω_alg`), carrying polynomial jet coefficients and constant contact form generators. -/
abbrev VerticalForm (R ι α : Type*) [CommRing R] :=
  PolynomialJet R ι α ⊗[R] ContactAlgebra R ι α

/-- The constant horizontal coordinate `1`-form `dxⁱ` in `HorizAlgebra R ι`. -/
def horizGen (i : ι) : HorizAlgebra R ι :=
  ExteriorAlgebra.ι R (Finsupp.single i 1)

theorem horizGen_eq_ι (i : ι) :
    horizGen (R := R) i = ExteriorAlgebra.ι R (Finsupp.single i 1) :=
  (rfl)

/-- The constant contact `1`-form generator `θᵃ_I` in `ContactAlgebra R ι α`. -/
def contactGen (a : α) (I : ι →₀ ℕ) : ContactAlgebra R ι α :=
  ExteriorAlgebra.ι R (Finsupp.single (a, I) 1)

theorem contactGen_eq_ι (a : α) (I : ι →₀ ℕ) :
    contactGen (R := R) a I = ExteriorAlgebra.ι R (Finsupp.single (a, I) 1) :=
  (rfl)

@[simp]
theorem horizGen_mul_self (i : ι) : horizGen (R := R) i * horizGen i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem horizGen_mul_add_swap (i j : ι) :
    horizGen (R := R) i * horizGen j + horizGen j * horizGen i = 0 :=
  ExteriorAlgebra.ι_add_mul_swap _ _

theorem horizGen_mem_exteriorPower_one (i : ι) :
    horizGen (R := R) i ∈ ⋀[R]^1 (ι →₀ R) :=
  TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _

@[simp]
theorem contactGen_mul_self (a : α) (I : ι →₀ ℕ) :
    contactGen (R := R) a I * contactGen a I = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem contactGen_mul_add_swap (a b : α) (I J : ι →₀ ℕ) :
    contactGen (R := R) a I * contactGen b J + contactGen b J * contactGen a I = 0 :=
  ExteriorAlgebra.ι_add_mul_swap _ _

theorem contactGen_mem_exteriorPower_one (a : α) (I : ι →₀ ℕ) :
    contactGen (R := R) a I ∈ ⋀[R]^1 ((α × (ι →₀ ℕ)) →₀ R) :=
  TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _

/-- Homogeneous forms of vertical degree `q` in `VerticalForm R ι α`. -/
def verticalDegree (q : ℕ) : Submodule (PolynomialJet R ι α) (VerticalForm R ι α) :=
  LinearMap.range ((⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R)).subtype.baseChange (PolynomialJet R ι α))

theorem tmul_mem_verticalDegree {q : ℕ} (f : PolynomialJet R ι α)
    {η : ContactAlgebra R ι α} (hη : η ∈ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R)) :
    f ⊗ₜ[R] η ∈ verticalDegree q :=
  ⟨f ⊗ₜ[R] ⟨η, hη⟩, by simp⟩

theorem tmul_one_mem_verticalDegree_zero (f : PolynomialJet R ι α) :
    f ⊗ₜ[R] (1 : ContactAlgebra R ι α) ∈ verticalDegree 0 :=
  tmul_mem_verticalDegree f (SetLike.one_mem_graded _)

theorem one_tmul_contactGen_mem_verticalDegree_one (a : α) (I : ι →₀ ℕ) :
    (1 : PolynomialJet R ι α) ⊗ₜ[R] contactGen a I ∈ verticalDegree 1 :=
  tmul_mem_verticalDegree 1 (contactGen_mem_exteriorPower_one a I)

/-- Induction principle for homogeneous elements of `verticalDegree q`. -/
theorem verticalDegree_induction {q : ℕ} {P : VerticalForm R ι α → Prop}
    (hadd : ∀ u v, P u → P v → P (u + v))
    (htmul : ∀ (f : PolynomialJet R ι α) (η : ContactAlgebra R ι α),
      η ∈ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R) → P (f ⊗ₜ[R] η))
    {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q) : P u := by
  obtain ⟨t, rfl⟩ := hu
  induction t using TensorProduct.inductionOn with
  | tmul f η => simpa using htmul f η.1 η.2
  | add x y hx hy => simpa [map_add] using hadd _ _ hx hy

theorem verticalDegree_mul {q₁ q₂ : ℕ} {u v : VerticalForm R ι α}
    (hu : u ∈ verticalDegree q₁) (hv : v ∈ verticalDegree q₂) :
    u * v ∈ verticalDegree (q₁ + q₂) := by
  refine verticalDegree_induction (P := fun x ↦ x * v ∈ verticalDegree (q₁ + q₂))
    (fun u₁ u₂ h₁ h₂ ↦ by rw [add_mul]; exact add_mem h₁ h₂) (fun f η hη ↦ ?_) hu
  refine verticalDegree_induction (P := fun y ↦ (f ⊗ₜ[R] η) * y ∈ verticalDegree (q₁ + q₂))
    (fun v₁ v₂ h₁ h₂ ↦ by rw [mul_add]; exact add_mem h₁ h₂) (fun g ξ hξ ↦ ?_) hv
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tmul_mem_verticalDegree (f * g) (SetLike.mul_mem_graded hη hξ)

theorem mul_eq_neg_one_pow_smul_mul_of_mem_verticalDegree {q₁ q₂ : ℕ} {u v : VerticalForm R ι α}
    (hu : u ∈ verticalDegree q₁) (hv : v ∈ verticalDegree q₂) :
    u * v = (-1 : R) ^ (q₂ * q₁) • (v * u) := by
  refine verticalDegree_induction (P := fun x ↦ x * v = (-1 : R) ^ (q₂ * q₁) • (v * x))
    (fun u₁ u₂ h₁ h₂ ↦ by rw [add_mul, mul_add, smul_add, h₁, h₂]) (fun f η hη ↦ ?_) hu
  refine verticalDegree_induction
    (P := fun y ↦ (f ⊗ₜ[R] η) * y = (-1 : R) ^ (q₂ * q₁) • (y * (f ⊗ₜ[R] η)))
    (fun v₁ v₂ h₁ h₂ ↦ by rw [mul_add, add_mul, smul_add, h₁, h₂]) (fun g ξ hξ ↦ ?_) hv
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    TauCeti.ExteriorAlgebra.mul_eq_neg_one_pow_smul_mul_of_mem hη hξ,
    TensorProduct.tmul_smul, mul_comm f g]

/-- The degree-zero-to-one vertical exterior derivation on jet polynomials. -/
private def verticalAlgDeriv₀ :
    Derivation R (PolynomialJet R ι α) (VerticalForm R ι α) :=
  MvPolynomial.mkDerivation R
    (Sum.elim (fun _ ↦ 0) (fun aI ↦ (1 : PolynomialJet R ι α) ⊗ₜ[R] contactGen aI.1 aI.2))

private theorem verticalAlgDeriv₀_mem_verticalDegree_one (f : PolynomialJet R ι α) :
    verticalAlgDeriv₀ f ∈ verticalDegree 1 := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [verticalAlgDeriv₀]
  | add f g hf hg => simpa [map_add] using add_mem hf hg
  | mul_X f v hf =>
    rw [Derivation.leibniz]
    refine add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ hf)
    rcases v with j | ⟨a, I⟩
    · simp [verticalAlgDeriv₀]
    · simpa [verticalAlgDeriv₀] using one_tmul_contactGen_mem_verticalDegree_one (R := R) a I

/-- The relative vertical exterior differential `d_alg` on `VerticalForm R ι α`, sending a
polynomial `f` to `∑ (a, I), (∂f/∂uᵃ_I) ⊗ θᵃ_I` and vanishing on constant contact forms. -/
def verticalAlgDeriv : VerticalForm R ι α →ₗ[R] VerticalForm R ι α :=
  TensorProduct.lift <|
    LinearMap.mk₂ R (fun f η ↦ verticalAlgDeriv₀ f * ((1 : PolynomialJet R ι α) ⊗ₜ[R] η))
      (fun f₁ f₂ η ↦ by simp [add_mul])
      (fun r f η ↦ by simp [smul_mul_assoc])
      (fun f η₁ η₂ ↦ by simp [TensorProduct.tmul_add, mul_add])
      (fun r f η ↦ by simp [TensorProduct.tmul_smul, mul_smul_comm])

private theorem verticalAlgDeriv_tmul_one_eq (f : PolynomialJet R ι α) :
    verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) = verticalAlgDeriv₀ f := by
  simp [verticalAlgDeriv, ← Algebra.TensorProduct.one_def]

theorem verticalAlgDeriv_tmul (f : PolynomialJet R ι α) (η : ContactAlgebra R ι α) :
    verticalAlgDeriv (f ⊗ₜ[R] η) =
      verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) *
        ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) := by
  rw [verticalAlgDeriv_tmul_one_eq]
  simp [verticalAlgDeriv]

@[simp]
theorem verticalAlgDeriv_tmul_one_X_base (j : ι) :
    verticalAlgDeriv ((X (Sum.inl j) : PolynomialJet R ι α) ⊗ₜ[R]
      (1 : ContactAlgebra R ι α)) = 0 := by
  rw [verticalAlgDeriv_tmul_one_eq]
  simp [verticalAlgDeriv₀]

@[simp]
theorem verticalAlgDeriv_tmul_one_X_field (a : α) (I : ι →₀ ℕ) :
    verticalAlgDeriv ((X (Sum.inr (a, I)) : PolynomialJet R ι α) ⊗ₜ[R]
      (1 : ContactAlgebra R ι α)) =
      (1 : PolynomialJet R ι α) ⊗ₜ[R] contactGen a I := by
  rw [verticalAlgDeriv_tmul_one_eq]
  simp [verticalAlgDeriv₀]

@[simp]
theorem verticalAlgDeriv_tmul_one_C (c : R) :
    verticalAlgDeriv ((C c : PolynomialJet R ι α) ⊗ₜ[R] (1 : ContactAlgebra R ι α)) = 0 := by
  rw [verticalAlgDeriv_tmul_one_eq]
  simp [verticalAlgDeriv₀]

@[simp]
theorem verticalAlgDeriv_one_tmul (η : ContactAlgebra R ι α) :
    verticalAlgDeriv ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) = 0 := by
  simp [verticalAlgDeriv, verticalAlgDeriv₀]

/-- Explicit expansion of `d_alg (f ⊗ 1)` in terms of field partial derivatives over any finite
set containing the field variables of `f`. -/
theorem verticalAlgDeriv_tmul_one_eq_sum (f : PolynomialJet R ι α)
    (s : Finset (α × (ι →₀ ℕ)))
    (hs : ∀ a I, Sum.inr (a, I) ∈ f.vars → (a, I) ∈ s) :
    verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) =
      ∑ aI ∈ s, pderiv (Sum.inr aI) f ⊗ₜ[R] contactGen aI.1 aI.2 := by
  classical
  rw [verticalAlgDeriv_tmul_one_eq]
  let D : Derivation R (PolynomialJet R ι α) (VerticalForm R ι α) :=
    ∑ aI ∈ s,
      (LinearMap.toSpanSingleton (PolynomialJet R ι α) (VerticalForm R ι α)
        ((1 : PolynomialJet R ι α) ⊗ₜ[R] contactGen aI.1 aI.2)).compDer (pderiv (Sum.inr aI))
  have hD (g : PolynomialJet R ι α) :
      D g = ∑ aI ∈ s, pderiv (Sum.inr aI) g ⊗ₜ[R] contactGen aI.1 aI.2 := by
    simp [D, TensorProduct.smul_tmul']
  rw [← hD f]
  refine MvPolynomial.derivation_eq_of_forall_mem_vars fun v hv ↦ ?_
  rw [hD]
  rcases v with j | ⟨a, I⟩
  · simp [verticalAlgDeriv₀]
  · simp only [verticalAlgDeriv₀, mkDerivation_X, Sum.elim_inr, pderiv_X, Pi.single_apply]
    rw [Finset.sum_eq_single (a, I)]
    · simp
    · intro b _ hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (hs a I hv)).elim

/-- `verticalAlgDeriv` raises the vertical exterior degree by one. -/
theorem verticalAlgDeriv_mem_verticalDegree {q : ℕ} {u : VerticalForm R ι α}
    (hu : u ∈ verticalDegree q) :
    verticalAlgDeriv u ∈ verticalDegree (q + 1) := by
  refine verticalDegree_induction (P := fun x ↦ verticalAlgDeriv x ∈ verticalDegree (q + 1))
    (fun u₁ u₂ h₁ h₂ ↦ by simpa [map_add] using add_mem h₁ h₂) (fun f η hη ↦ ?_) hu
  have h1 : verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) ∈ verticalDegree 1 := by
    rw [verticalAlgDeriv_tmul_one_eq]
    exact verticalAlgDeriv₀_mem_verticalDegree_one f
  rw [verticalAlgDeriv_tmul, add_comm]
  exact verticalDegree_mul h1 (tmul_mem_verticalDegree 1 hη)

private theorem smul_eq_tmul_one_mul (a : PolynomialJet R ι α) (w : VerticalForm R ι α) :
    a • w = (a ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * w := by
  induction w using TensorProduct.inductionOn with
  | tmul p ζ => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add w₁ w₂ h₁ h₂ => simp [smul_add, mul_add, h₁, h₂]

private theorem tmul_one_mul_comm (a : PolynomialJet R ι α) (w : VerticalForm R ι α) :
    (a ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * w = w * (a ⊗ₜ[R] (1 : ContactAlgebra R ι α)) := by
  induction w using TensorProduct.inductionOn with
  | tmul p ζ => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add w₁ w₂ h₁ h₂ => simp [mul_add, add_mul, h₁, h₂]

/-- **Graded Leibniz rule for `d_alg`**: on a form of vertical degree `q`,
`d_alg (u * v) = d_alg u * v + (-1) ^ q • (u * d_alg v)`. -/
theorem verticalAlgDeriv_mul {q : ℕ} {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q)
    (v : VerticalForm R ι α) :
    verticalAlgDeriv (u * v) =
      verticalAlgDeriv u * v + (-1 : R) ^ q • (u * verticalAlgDeriv v) := by
  refine verticalDegree_induction
    (P := fun x ↦ verticalAlgDeriv (x * v) =
      verticalAlgDeriv x * v + (-1 : R) ^ q • (x * verticalAlgDeriv v))
    (fun u₁ u₂ h₁ h₂ ↦ by simp only [add_mul, map_add, h₁, h₂, smul_add]; abel)
    (fun f η hη ↦ ?_) hu
  induction v using TensorProduct.inductionOn with
  | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, smul_add]; abel
  | tmul g ξ =>
    have hcomm : verticalAlgDeriv₀ g * ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) =
        (-1 : R) ^ q • (((1 : PolynomialJet R ι α) ⊗ₜ[R] η) * verticalAlgDeriv₀ g) := by
      simpa [one_mul] using mul_eq_neg_one_pow_smul_mul_of_mem_verticalDegree
        (verticalAlgDeriv₀_mem_verticalDegree_one g) (tmul_mem_verticalDegree 1 hη)
    have hηξ : ((1 : PolynomialJet R ι α) ⊗ₜ[R] (η * ξ)) =
        ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) * ((1 : PolynomialJet R ι α) ⊗ₜ[R] ξ) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, verticalAlgDeriv, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, Derivation.leibniz, smul_eq_tmul_one_mul, add_mul]
    rw [hηξ]
    have h1 : (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * verticalAlgDeriv₀ g *
        (((1 : PolynomialJet R ι α) ⊗ₜ[R] η) * ((1 : PolynomialJet R ι α) ⊗ₜ[R] ξ)) =
        (-1 : R) ^ q • ((f ⊗ₜ[R] η) *
          (verticalAlgDeriv₀ g * ((1 : PolynomialJet R ι α) ⊗ₜ[R] ξ))) := by
      rw [← mul_assoc (f ⊗ₜ[R] (1 : ContactAlgebra R ι α) * verticalAlgDeriv₀ g),
        mul_assoc (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)), hcomm, mul_smul_comm, smul_mul_assoc,
        ← mul_assoc (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)),
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]
    have h2 : (g ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * verticalAlgDeriv₀ f *
        (((1 : PolynomialJet R ι α) ⊗ₜ[R] η) * ((1 : PolynomialJet R ι α) ⊗ₜ[R] ξ)) =
        verticalAlgDeriv₀ f * ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) * (g ⊗ₜ[R] ξ) := by
      rw [← mul_assoc (g ⊗ₜ[R] (1 : ContactAlgebra R ι α) * verticalAlgDeriv₀ f),
        mul_assoc (g ⊗ₜ[R] (1 : ContactAlgebra R ι α)), tmul_one_mul_comm]
      simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [h1, h2, add_comm]

/-- The relative vertical differential `d_alg` squares to zero on all of `VerticalForm R ι α`. -/
@[simp]
theorem verticalAlgDeriv_verticalAlgDeriv (u : VerticalForm R ι α) :
    verticalAlgDeriv (verticalAlgDeriv u) = 0 := by
  have hpoly (f : PolynomialJet R ι α) :
      verticalAlgDeriv (verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α))) = 0 := by
    induction f using MvPolynomial.induction_on with
    | C c => simp
    | add f g hf hg => simp [TensorProduct.add_tmul, hf, hg]
    | mul_X f v hf =>
      have hmul : (f * X v) ⊗ₜ[R] (1 : ContactAlgebra R ι α) =
          (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * (X v ⊗ₜ[R] (1 : ContactAlgebra R ι α)) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have hv : verticalAlgDeriv
          (verticalAlgDeriv (X v ⊗ₜ[R] (1 : ContactAlgebra R ι α))) = 0 := by
        rcases v with j | ⟨a, I⟩ <;> simp
      have hdeg1 := verticalAlgDeriv_mem_verticalDegree (tmul_one_mem_verticalDegree_zero f)
      rw [hmul, verticalAlgDeriv_mul (tmul_one_mem_verticalDegree_zero f), pow_zero, one_smul,
        map_add, verticalAlgDeriv_mul hdeg1,
        verticalAlgDeriv_mul (tmul_one_mem_verticalDegree_zero f), hf, hv]
      simp only [zero_mul, mul_zero, smul_zero, zero_add, add_zero, pow_one]
      have h0 : ((-1 : R) + 1) • (verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) *
          verticalAlgDeriv (X v ⊗ₜ[R] (1 : ContactAlgebra R ι α))) = 0 := by
        rw [neg_add_cancel, zero_smul]
      rwa [add_smul, one_smul] at h0
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp [h₁, h₂]
  | tmul f η =>
    have hdeg1 := verticalAlgDeriv_mem_verticalDegree (tmul_one_mem_verticalDegree_zero f)
    rw [verticalAlgDeriv_tmul, verticalAlgDeriv_mul hdeg1, hpoly f, verticalAlgDeriv_one_tmul]
    simp

/-- The coordinate shift endomorphism on contact `1`-form generators sending `θᵃ_I` to
`θᵃ_(I+eᵢ)`. -/
def contactShift (i : ι) : Module.End R ((α × (ι →₀ ℕ)) →₀ R) :=
  Finsupp.lmapDomain R R fun aI ↦ (aI.1, aI.2 + Finsupp.single i 1)

@[simp]
theorem contactShift_single (i : ι) (a : α) (I : ι →₀ ℕ) (r : R) :
    contactShift (R := R) i (Finsupp.single (a, I) r) =
      Finsupp.single (a, I + Finsupp.single i 1) r := by
  simp [contactShift]

theorem contactShift_comm (i j : ι) :
    contactShift (R := R) (α := α) i * contactShift j = contactShift j * contactShift i := by
  ext ⟨a, I⟩
  simp [add_right_comm I]

/-- The even algebra derivation on `ContactAlgebra R ι α` extending `contactShift i`,
constructed from `exteriorPower.lieMap` on each homogeneous exterior power. -/
def contactDeriv (i : ι) : Module.End R (ContactAlgebra R ι α) :=
  (DirectSum.decomposeLinearEquiv (fun d : ℕ ↦ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R))).symm.toLinearMap ∘ₗ
    DirectSum.lmap (fun d ↦ exteriorPower.lieMap d (contactShift (R := R) i)) ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun d : ℕ ↦ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R))).toLinearMap

theorem contactDeriv_of_mem {d : ℕ} (i : ι) (η : ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R)) :
    contactDeriv i (η : ContactAlgebra R ι α) =
      (exteriorPower.lieMap d (contactShift (R := R) i) η : ContactAlgebra R ι α) := by
  simp only [contactDeriv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe, DirectSum.lmap_of,
    DirectSum.decomposeLinearEquiv_symm_apply, DirectSum.decompose_symm_of]

theorem contactDeriv_mem_exteriorPower {d : ℕ} (i : ι) {η : ContactAlgebra R ι α}
    (hη : η ∈ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R)) :
    contactDeriv i η ∈ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R) := by
  simpa only [contactDeriv_of_mem i ⟨η, hη⟩] using
    (exteriorPower.lieMap d (contactShift (R := R) i) ⟨η, hη⟩).2

@[simp]
theorem contactDeriv_contactGen (i : ι) (a : α) (I : ι →₀ ℕ) :
    contactDeriv (R := R) i (contactGen a I) = contactGen a (I + Finsupp.single i 1) := by
  let x : ⋀[R]^1 ((α × (ι →₀ ℕ)) →₀ R) :=
    exteriorPower.ιMulti R 1 ![Finsupp.single (a, I) 1]
  have hx : (x : ContactAlgebra R ι α) = contactGen a I := by
    simp [x, contactGen, ExteriorAlgebra.ιMulti_succ_apply]
  rw [← hx, contactDeriv_of_mem, exteriorPower.lieMap_apply_ιMulti, Fin.sum_univ_one]
  simp [contactGen, ExteriorAlgebra.ιMulti_succ_apply]

@[simp]
theorem contactDeriv_one (i : ι) :
    contactDeriv (R := R) (α := α) i 1 = 0 := by
  let x : ⋀[R]^0 ((α × (ι →₀ ℕ)) →₀ R) := exteriorPower.ιMulti R 0 Fin.elim0
  have hx : (x : ContactAlgebra R ι α) = 1 := by
    simp [x, ExteriorAlgebra.ιMulti_zero_apply]
  rw [← hx, contactDeriv_of_mem, exteriorPower.lieMap_apply_ιMulti]
  simp

/-- `contactDeriv i` is an even algebra derivation of `ContactAlgebra R ι α`. -/
theorem contactDeriv_mul (i : ι) (η₁ η₂ : ContactAlgebra R ι α) :
    contactDeriv i (η₁ * η₂) = contactDeriv i η₁ * η₂ + η₁ * contactDeriv i η₂ := by
  induction η₁ using DirectSum.Decomposition.inductionOn
      (fun d : ℕ ↦ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R)) with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy]; abel
  | @homogeneous k x =>
    induction η₂ using DirectSum.Decomposition.inductionOn
        (fun d : ℕ ↦ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R)) with
    | zero => simp
    | add y z hy hz => simp [mul_add, hy, hz]; abel
    | @homogeneous l y =>
      have hw : (x : ContactAlgebra R ι α) * (y : ContactAlgebra R ι α) =
          (exteriorPower.wedge R ((α × (ι →₀ ℕ)) →₀ R) k l x y : ContactAlgebra R ι α) :=
        (exteriorPower.coe_wedge x y).symm
      rw [hw, contactDeriv_of_mem, exteriorPower.lieMap_wedge, Submodule.coe_add,
        exteriorPower.coe_wedge, exteriorPower.coe_wedge, contactDeriv_of_mem, contactDeriv_of_mem]

section ContactDerivComm

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Contact derivations in different base directions commute. -/
theorem contactDeriv_comm (i j : ι) (η : ContactAlgebra R ι α) :
    contactDeriv i (contactDeriv j η) = contactDeriv j (contactDeriv i η) := by
  induction η using DirectSum.Decomposition.inductionOn
      (fun d : ℕ ↦ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R)) with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous d x =>
    have hmap := (exteriorPower.lieMap d).map_lie
      (contactShift (R := R) (α := α) i) (contactShift (R := R) (α := α) j)
    rw [Ring.lie_def, Ring.lie_def, contactShift_comm, sub_self, map_zero, eq_comm,
      sub_eq_zero] at hmap
    have hx := LinearMap.congr_fun hmap x
    rw [contactDeriv_of_mem, contactDeriv_of_mem, contactDeriv_of_mem, contactDeriv_of_mem]
    exact congrArg Subtype.val hx

end ContactDerivComm

/-- The lifted total derivative `Lᵢ` on `VerticalForm R ι α`, acting by `totalDeriv i` on
polynomial coefficients and by `contactDeriv i` on contact generators. -/
def liftedTotalDeriv (i : ι) : VerticalForm R ι α →ₗ[R] VerticalForm R ι α :=
  TensorProduct.map (totalDeriv i).toLinearMap LinearMap.id +
    TensorProduct.map LinearMap.id (contactDeriv i)

@[simp]
theorem liftedTotalDeriv_tmul (i : ι) (f : PolynomialJet R ι α) (η : ContactAlgebra R ι α) :
    liftedTotalDeriv i (f ⊗ₜ[R] η) =
      totalDeriv i f ⊗ₜ[R] η + f ⊗ₜ[R] contactDeriv i η := by
  simp [liftedTotalDeriv]

@[simp]
theorem liftedTotalDeriv_one (i : ι) :
    liftedTotalDeriv (R := R) (α := α) i 1 = 0 := by
  rw [Algebra.TensorProduct.one_def, liftedTotalDeriv_tmul, Derivation.map_one_eq_zero,
    contactDeriv_one]
  simp

/-- `liftedTotalDeriv i` is an even algebra derivation of `VerticalForm R ι α`. -/
theorem liftedTotalDeriv_mul (i : ι) (u v : VerticalForm R ι α) :
    liftedTotalDeriv i (u * v) = liftedTotalDeriv i u * v + u * liftedTotalDeriv i v := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; abel
  | tmul f η =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; abel
    | tmul g ξ =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, liftedTotalDeriv_tmul, Derivation.leibniz,
        smul_eq_mul, contactDeriv_mul, TensorProduct.add_tmul, TensorProduct.tmul_add,
        add_mul, mul_add]
      rw [mul_comm g (totalDeriv i f)]
      abel

/-- `liftedTotalDeriv i` preserves every vertical exterior degree. -/
theorem liftedTotalDeriv_mem_verticalDegree (i : ι) {q : ℕ} {u : VerticalForm R ι α}
    (hu : u ∈ verticalDegree q) :
    liftedTotalDeriv i u ∈ verticalDegree q := by
  refine verticalDegree_induction (P := fun x ↦ liftedTotalDeriv i x ∈ verticalDegree q)
    (fun u₁ u₂ h₁ h₂ ↦ by simpa [map_add] using add_mem h₁ h₂) (fun f η hη ↦ ?_) hu
  rw [liftedTotalDeriv_tmul]
  exact add_mem (tmul_mem_verticalDegree _ hη)
    (tmul_mem_verticalDegree _ (contactDeriv_mem_exteriorPower i hη))

/-- Lifted total derivatives in different base directions commute. -/
theorem liftedTotalDeriv_comm (i j : ι) (u : VerticalForm R ι α) :
    liftedTotalDeriv i (liftedTotalDeriv j u) = liftedTotalDeriv j (liftedTotalDeriv i u) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp [h₁, h₂]
  | tmul f η =>
    simp only [liftedTotalDeriv_tmul, map_add, totalDeriv_comm i j f, contactDeriv_comm i j η]
    abel

/-- The relative vertical differential `d_alg` commutes with every lifted total derivative `Lᵢ`. -/
theorem verticalAlgDeriv_liftedTotalDeriv (i : ι) (u : VerticalForm R ι α) :
    verticalAlgDeriv (liftedTotalDeriv i u) = liftedTotalDeriv i (verticalAlgDeriv u) := by
  have hpoly (f : PolynomialJet R ι α) :
      verticalAlgDeriv (liftedTotalDeriv i (f ⊗ₜ[R] (1 : ContactAlgebra R ι α))) =
        liftedTotalDeriv i (verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α))) := by
    classical
    induction f using MvPolynomial.induction_on with
    | C c => simp
    | add f g hf hg =>
      rw [TensorProduct.add_tmul, map_add, map_add, map_add, map_add, hf, hg]
    | mul_X f v hf =>
      have hmul : (f * X v) ⊗ₜ[R] (1 : ContactAlgebra R ι α) =
          (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * (X v ⊗ₜ[R] (1 : ContactAlgebra R ι α)) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have hv : verticalAlgDeriv (liftedTotalDeriv i (X v ⊗ₜ[R] (1 : ContactAlgebra R ι α))) =
          liftedTotalDeriv i (verticalAlgDeriv (X v ⊗ₜ[R] (1 : ContactAlgebra R ι α))) := by
        rcases v with j | ⟨a, I⟩
        · simp only [liftedTotalDeriv_tmul, totalDeriv_X_base, contactDeriv_one,
            TensorProduct.tmul_zero, add_zero, verticalAlgDeriv_tmul_one_X_base, map_zero]
          split_ifs <;> simp
        · simp
      have hLf := liftedTotalDeriv_mem_verticalDegree i (tmul_one_mem_verticalDegree_zero f)
      rw [hmul, liftedTotalDeriv_mul, map_add, verticalAlgDeriv_mul hLf,
        verticalAlgDeriv_mul (tmul_one_mem_verticalDegree_zero f),
        verticalAlgDeriv_mul (tmul_one_mem_verticalDegree_zero f)]
      simp only [pow_zero, one_smul, map_add, liftedTotalDeriv_mul, hf, hv]
      abel
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp [h₁, h₂]
  | tmul f η =>
    have hsplit : f ⊗ₜ[R] η =
        (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    have hLf := liftedTotalDeriv_mem_verticalDegree i (tmul_one_mem_verticalDegree_zero f)
    have hLη : liftedTotalDeriv i ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) =
        (1 : PolynomialJet R ι α) ⊗ₜ[R] contactDeriv i η := by
      simp
    rw [hsplit, liftedTotalDeriv_mul, map_add, verticalAlgDeriv_mul hLf,
      verticalAlgDeriv_mul (tmul_one_mem_verticalDegree_zero f),
      verticalAlgDeriv_mul (tmul_one_mem_verticalDegree_zero f)]
    simp only [pow_zero, one_smul, verticalAlgDeriv_one_tmul, mul_zero, add_zero, hLη,
      hpoly f, liftedTotalDeriv_mul]

end Vertical

/-! ### Relative Kähler comparison -/

section RelativeKaehler

variable {R ι α : Type*}

/-- The base-coordinate polynomial subalgebra `R[x]` inside `PolynomialJet R ι α`. -/
def baseSubalgebra (R ι α : Type*) [CommSemiring R] :
    Subalgebra R (PolynomialJet R ι α) :=
  MvPolynomial.supported R (Set.range Sum.inl)

theorem X_base_mem_baseSubalgebra [CommSemiring R] (j : ι) :
    (X (Sum.inl j) : PolynomialJet R ι α) ∈ baseSubalgebra R ι α :=
  Algebra.subset_adjoin ⟨Sum.inl j, ⟨j, rfl⟩, rfl⟩

variable [CommRing R]

private def relVertDerivation :
    Derivation (baseSubalgebra R ι α) (PolynomialJet R ι α)
      ((α × (ι →₀ ℕ)) →₀ PolynomialJet R ι α) :=
  let D : Derivation R (PolynomialJet R ι α) ((α × (ι →₀ ℕ)) →₀ PolynomialJet R ι α) :=
    MvPolynomial.mkDerivation R (Sum.elim (fun _ ↦ 0) (fun aI ↦ Finsupp.single aI 1))
  have hbase (b : baseSubalgebra R ι α) : D (b : PolynomialJet R ι α) = 0 := by
    refine MvPolynomial.derivation_eqOn_supported (D₁ := D) (D₂ := 0) ?_ b.2
    rintro _ ⟨j, rfl⟩
    simp [D]
  { toFun := D
    map_add' := D.map_add
    map_smul' := fun b f ↦ by
      simp only [Algebra.smul_def, D.leibniz, Subalgebra.algebraMap_apply,
        RingHom.id_apply, hbase, smul_zero, add_zero]
      exact (IsScalarTower.algebraMap_smul (PolynomialJet R ι α) b (D f)).symm
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }

private theorem kaehlerD_base_X_base (j : ι) :
    KaehlerDifferential.D (baseSubalgebra R ι α) (PolynomialJet R ι α) (X (Sum.inl j)) = 0 := by
  have hj : (X (Sum.inl j) : PolynomialJet R ι α) =
      algebraMap (baseSubalgebra R ι α) (PolynomialJet R ι α)
        ⟨X (Sum.inl j), X_base_mem_baseSubalgebra j⟩ := rfl
  rw [hj, Derivation.map_algebraMap]

/-- The relative Kähler differential module `Ω[PolynomialJet R ι α ⁄ baseSubalgebra R ι α]` is
freely generated by the field-jet differentials `duᵃ_I`. -/
def relativeKaehlerEquiv :
    Ω[PolynomialJet R ι α ⁄ baseSubalgebra R ι α] ≃ₗ[PolynomialJet R ι α]
      ((α × (ι →₀ ℕ)) →₀ PolynomialJet R ι α) :=
  LinearEquiv.ofLinearMap
    relVertDerivation.liftKaehlerDifferential
    (Finsupp.linearCombination (PolynomialJet R ι α)
      fun aI ↦ KaehlerDifferential.D (baseSubalgebra R ι α) (PolynomialJet R ι α)
        (X (Sum.inr aI)))
    (by
      ext aI
      simp [relVertDerivation])
    (by
      apply Derivation.liftKaehlerDifferential_unique
      apply Derivation.ext
      intro f
      simp only [Derivation.coe_comp, Derivation.coeFn_coe, LinearMap.restrictScalars_apply,
        LinearMap.comp_apply, LinearMap.id_apply, Derivation.liftKaehlerDifferential_comp_D]
      induction f using MvPolynomial.induction_on with
      | C c =>
        have hc : (C c : PolynomialJet R ι α) =
            algebraMap (baseSubalgebra R ι α) (PolynomialJet R ι α)
              (algebraMap R (baseSubalgebra R ι α) c) := rfl
        rw [hc, Derivation.map_algebraMap, Derivation.map_algebraMap, map_zero]
      | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
      | mul_X f v hf =>
        rw [Derivation.leibniz, Derivation.leibniz, map_add, map_smul, map_smul, hf]
        congr 2
        rcases v with j | ⟨a, I⟩
        · rw [kaehlerD_base_X_base]
          simp [relVertDerivation]
        · simp [relVertDerivation])

@[simp]
theorem relativeKaehlerEquiv_D_X_field (a : α) (I : ι →₀ ℕ) :
    relativeKaehlerEquiv (R := R)
      (KaehlerDifferential.D (baseSubalgebra R ι α) (PolynomialJet R ι α) (X (Sum.inr (a, I)))) =
      Finsupp.single (a, I) 1 := by
  simp [relativeKaehlerEquiv, relVertDerivation]

@[simp]
theorem relativeKaehlerEquiv_symm_single (a : α) (I : ι →₀ ℕ) (f : PolynomialJet R ι α) :
    (relativeKaehlerEquiv (R := R)).symm (Finsupp.single (a, I) f) =
      f • KaehlerDifferential.D (baseSubalgebra R ι α) (PolynomialJet R ι α)
        (X (Sum.inr (a, I))) := by
  simp [relativeKaehlerEquiv]

/-- Algebra equivalence identifying the exterior algebra of the relative Kähler differentials
`Ω[PolynomialJet R ι α ⁄ baseSubalgebra R ι α]` with `VerticalForm R ι α`. -/
def verticalKaehlerEquiv :
    ExteriorAlgebra (PolynomialJet R ι α)
        Ω[PolynomialJet R ι α ⁄ baseSubalgebra R ι α] ≃ₐ[PolynomialJet R ι α]
      VerticalForm R ι α := by
  classical
  let e : Ω[PolynomialJet R ι α ⁄ baseSubalgebra R ι α] ≃ₗ[PolynomialJet R ι α]
      PolynomialJet R ι α ⊗[R] ((α × (ι →₀ ℕ)) →₀ R) :=
    relativeKaehlerEquiv.trans
      (TensorProduct.finsuppScalarRight R (PolynomialJet R ι α) (PolynomialJet R ι α)
        (α × (ι →₀ ℕ))).symm
  exact (AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap)
      (ExteriorAlgebra.map e.symm.toLinearMap)
      (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id])
      (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id])).trans
    (ExteriorAlgebra.baseChangeEquiv R ((α × (ι →₀ ℕ)) →₀ R) (PolynomialJet R ι α)).symm

/-- Under `verticalKaehlerEquiv`, the universal relative Kähler differential `D f` corresponds to
`verticalAlgDeriv (f ⊗ 1)`. -/
theorem verticalKaehlerEquiv_ι_D (f : PolynomialJet R ι α) :
    verticalKaehlerEquiv
        (ExteriorAlgebra.ι (PolynomialJet R ι α)
          (KaehlerDifferential.D (baseSubalgebra R ι α) (PolynomialJet R ι α) f)) =
      verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    have hc : (C c : PolynomialJet R ι α) =
        algebraMap (baseSubalgebra R ι α) (PolynomialJet R ι α)
          (algebraMap R (baseSubalgebra R ι α) c) := rfl
    rw [hc, Derivation.map_algebraMap, map_zero, map_zero, ← hc, verticalAlgDeriv_tmul_one_C]
  | add f g hf hg => simp [TensorProduct.add_tmul, hf, hg]
  | mul_X f v hf =>
    have hmul : (f * X v) ⊗ₜ[R] (1 : ContactAlgebra R ι α) =
        (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) * (X v ⊗ₜ[R] (1 : ContactAlgebra R ι α)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [Derivation.leibniz, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hf,
      hmul, verticalAlgDeriv_mul (tmul_one_mem_verticalDegree_zero f), pow_zero, one_smul,
      smul_eq_tmul_one_mul, smul_eq_tmul_one_mul, tmul_one_mul_comm (X v), add_comm]
    congr 2
    rcases v with j | ⟨a, I⟩
    · rw [kaehlerD_base_X_base, map_zero, map_zero, verticalAlgDeriv_tmul_one_X_base]
    · simp [verticalKaehlerEquiv, contactGen]

@[simp]
theorem verticalKaehlerEquiv_symm_one_tmul_contactGen (a : α) (I : ι →₀ ℕ) :
    (verticalKaehlerEquiv (R := R)).symm ((1 : PolynomialJet R ι α) ⊗ₜ[R] contactGen a I) =
      ExteriorAlgebra.ι (PolynomialJet R ι α)
        (KaehlerDifferential.D (baseSubalgebra R ι α) (PolynomialJet R ι α)
          (X (Sum.inr (a, I)))) := by
  apply (verticalKaehlerEquiv (R := R) (ι := ι) (α := α)).injective
  rw [AlgEquiv.apply_symm_apply, verticalKaehlerEquiv_ι_D, verticalAlgDeriv_tmul_one_X_field]

end RelativeKaehler

/-! ### Unsigned horizontal differential -/

section UnsignedHoriz

variable {R ι α : Type*} [CommRing R] [Fintype ι]

/-- The unsigned horizontal differential `D_H⁰` on `VerticalForm R ι α ⊗[R] HorizAlgebra R ι`,
sending `u ⊗ β` to `∑ i, Lᵢ u ⊗ (dxⁱ ∧ β)`. -/
def unsignedHorizDeriv :
    VerticalForm R ι α ⊗[R] HorizAlgebra R ι →ₗ[R]
      VerticalForm R ι α ⊗[R] HorizAlgebra R ι :=
  ∑ i : ι, TensorProduct.map (liftedTotalDeriv i) (LinearMap.mulLeft R (horizGen i))

@[simp]
theorem unsignedHorizDeriv_tmul (u : VerticalForm R ι α) (β : HorizAlgebra R ι) :
    unsignedHorizDeriv (u ⊗ₜ[R] β) =
      ∑ i : ι, liftedTotalDeriv i u ⊗ₜ[R] (horizGen i * β) := by
  simp [unsignedHorizDeriv]

/-- The unsigned horizontal differential `D_H⁰` squares to zero. -/
@[simp]
theorem unsignedHorizDeriv_unsignedHorizDeriv (z : VerticalForm R ι α ⊗[R] HorizAlgebra R ι) :
    unsignedHorizDeriv (unsignedHorizDeriv z) = 0 := by
  classical
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
  | tmul u β =>
    simp only [unsignedHorizDeriv_tmul, map_sum]
    have hsum : ∀ s : Finset ι,
        ∑ i ∈ s, ∑ j ∈ s,
          liftedTotalDeriv j (liftedTotalDeriv i u) ⊗ₜ[R] (horizGen j * (horizGen i * β)) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hdiag : liftedTotalDeriv a (liftedTotalDeriv a u) ⊗ₜ[R]
            (horizGen a * (horizGen a * β)) = 0 := by
          rw [← mul_assoc, horizGen_mul_self, zero_mul, TensorProduct.tmul_zero]
        simp only [Finset.sum_insert ha, hdiag, zero_add]
        rw [Finset.sum_add_distrib, ih, add_zero, ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [liftedTotalDeriv_comm a j u, ← TensorProduct.tmul_add, ← mul_assoc, ← mul_assoc,
          ← add_mul, horizGen_mul_add_swap, zero_mul, TensorProduct.tmul_zero]
    exact hsum Finset.univ

/-- On `VerticalForm R ι α ⊗[R] HorizAlgebra R ι`, the relative vertical differential `d_alg ⊗ id`
commutes (without sign) with the unsigned horizontal differential `D_H⁰`. -/
theorem verticalAlgDeriv_unsignedHorizDeriv (z : VerticalForm R ι α ⊗[R] HorizAlgebra R ι) :
    TensorProduct.map verticalAlgDeriv LinearMap.id (unsignedHorizDeriv z) =
      unsignedHorizDeriv (TensorProduct.map verticalAlgDeriv LinearMap.id z) := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
  | tmul u β =>
    simp only [unsignedHorizDeriv_tmul, map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      verticalAlgDeriv_liftedTotalDeriv]

end UnsignedHoriz

end
end PolynomialJet
end TauCeti
