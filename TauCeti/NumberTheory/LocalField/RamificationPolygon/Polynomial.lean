/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.FieldTheory.Separable
public import TauCeti.Data.Nat.Choose.Factorization
public import TauCeti.NumberTheory.LocalField.AddValuation
public import TauCeti.NumberTheory.LocalField.Discriminant.Height

/-!
# The ramification polynomial of a local-field polynomial

Given a polynomial `φ : 𝒪[K][X]` of degree `n` and an element `α : L` of a field extension `L/K`,
the **ramification polynomial**

`φ.ramificationPolynomial α = α ^ (-n) * φ(α X + α) : L[X]`

shifts `α` to `0` and normalizes by `α ^ n` so that a monic `φ` with `α ≠ 0` produces a monic
polynomial of the same degree `n` whose nonzero roots in any extension `M/L` are the normalized
conjugate differences `(α' - α) / α` for the roots `α' ≠ α` of `φ`.

When `K` and `L` are compatible nonarchimedean local fields and `ξ : 𝒪[L]` is a root of a monic
Eisenstein polynomial `φ` generating `L = K(ξ)`:

* the powers `(ξ : L) ^ h` (`1 ≤ i ≤ h ≤ n`) have pairwise distinct residues modulo `n`, so no two
  terms in the binomial expansion of `coeff i` can share a valuation; the valuation of `coeff i` is
  therefore the exact minimum over `h ∈ [i, n]` of `n * v_K(choose h i * φ_h) + h - n`;
* every coefficient of `φ.ramificationPolynomial (ξ : L)` lies in `𝒪[L]`;
* when `L/K` is separable, `coeff 1` is nonzero of normalized valuation `ramificationHeight K L`,
  and `natTrailingDegree = 1`;
* at `i = p ^ w` (`p = ringChar 𝓀[K]`, `w = wildRamificationExponent K L`), `coeff (p ^ w)` has
  valuation `0`, while for `1 ≤ i < p ^ w` every `coeff i` has valuation at least `1`;
* on each prime-power block `p ^ r ≤ i < p ^ (r + 1)`, Kummer's carry domination bounds the
  valuation of `coeff i` below by that of `coeff (p ^ r)`.

## Main definitions

* `Polynomial.ramificationPolynomial φ α`: the polynomial `α ^ (-deg φ) * φ(α X + α) : L[X]`.

## Main results

* `Polynomial.coeff_ramificationPolynomial`: unconditional binomial formula for every coefficient.
* `Polynomial.aeval_ramificationPolynomial`, `Polynomial.eval_zero_ramificationPolynomial`,
  `Polynomial.coeff_zero_ramificationPolynomial_of_aeval_eq_zero`,
  `Polynomial.aeval_ramificationPolynomial_eq_zero_iff`: evaluation and root bijection
  `y ↦ (y - α) / α`.
* `Polynomial.natDegree_ramificationPolynomial`, `Polynomial.Monic.ramificationPolynomial`,
  `Polynomial.Separable.ramificationPolynomial`: degree, monicity and separability.
* `Polynomial.pow_mul_coeff_one_ramificationPolynomial`: `α ^ (n - 1) * ρ.coeff 1 = φ'(α)`.
* `Polynomial.normalizedAddValuation_coeff_ramificationPolynomial`: exact infimum formula for the
  valuation of `coeff i` (`1 ≤ i`) at an Eisenstein generator.
* `Polynomial.coeff_ramificationPolynomial_mem_integer`: integrality of all coefficients.
* `Polynomial.normalizedAddValuation_coeff_one_ramificationPolynomial`,
  `Polynomial.addValInt_coeff_one_ramificationPolynomial` and
  `Polynomial.natTrailingDegree_ramificationPolynomial`: `coeff 1` has valuation
  `ramificationHeight K L` and `natTrailingDegree = 1`.
* `Polynomial.normalizedAddValuation_coeff_pow_wildRamificationExponent_ramificationPolynomial` and
  `Polynomial.one_le_normalizedAddValuation_coeff_ramificationPolynomial`: valuation `0` at `p ^ w`
  and valuation `≥ 1` on `[1, p ^ w)`.
* `Polynomial.normalizedAddValuation_coeff_pow_le_ramificationPolynomial`: prime-power domination
  `v_L(ρ_{p ^ r}) ≤ v_L(ρ_i)` for `p ^ r ≤ i < p ^ (r + 1)`.

## References

* Ø. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928),
  84–117.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–2.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory **8** (2012), 1401–1424.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing TauCeti
open scoped IntermediateField

namespace Polynomial

section Algebraic

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]

/-- The ramification polynomial `α ^ (-deg φ) * φ(α X + α)` of `φ : 𝒪[K][X]` at `α : L`. -/
def ramificationPolynomial (φ : 𝒪[K][X]) (α : L) : L[X] :=
  C (α⁻¹ ^ φ.natDegree) *
    (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α)

/-- Defining formula for `ramificationPolynomial`. -/
theorem ramificationPolynomial_def (φ : 𝒪[K][X]) (α : L) :
    φ.ramificationPolynomial α =
      C (α⁻¹ ^ φ.natDegree) *
        (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α) := by
  rw [ramificationPolynomial]

/-- Evaluation of `φ.ramificationPolynomial α` in any `L`-algebra `M` forming a scalar tower over
`K`. -/
theorem aeval_ramificationPolynomial {M : Type*} [CommRing M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (φ : 𝒪[K][X]) (α : L) (x : M) :
    aeval x (φ.ramificationPolynomial α) =
      algebraMap L M (α⁻¹ ^ φ.natDegree) *
        aeval (algebraMap L M α * x + algebraMap L M α) (φ.map (algebraMap 𝒪[K] K)) := by
  rw [ramificationPolynomial_def, map_mul, aeval_C, ← Polynomial.map_map, aeval_comp,
    aeval_map_algebraMap]
  simp

/-- At `X = 0`, `φ.ramificationPolynomial α` evaluates to `α ^ (-deg φ) * φ(α)`. -/
theorem eval_zero_ramificationPolynomial (φ : 𝒪[K][X]) (α : L) :
    (φ.ramificationPolynomial α).eval 0 =
      α⁻¹ ^ φ.natDegree * aeval α (φ.map (algebraMap 𝒪[K] K)) := by
  simpa using aeval_ramificationPolynomial (M := L) φ α 0

/-- If `α` is a root of `φ` in `L`, the constant term of `φ.ramificationPolynomial α` vanishes. -/
theorem coeff_zero_ramificationPolynomial_of_aeval_eq_zero {φ : 𝒪[K][X]} {α : L}
    (hroot : aeval α (φ.map (algebraMap 𝒪[K] K)) = 0) :
    (φ.ramificationPolynomial α).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_zero_ramificationPolynomial, hroot, mul_zero]

/-- In any field extension `M/L` with `α ≠ 0`, `x : M` is a root of `φ.ramificationPolynomial α` if
and only if `α * x + α` is a root of `φ`. -/
theorem aeval_ramificationPolynomial_eq_zero_iff {M : Type*} [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] {φ : 𝒪[K][X]} {α : L} (hα : α ≠ 0) (x : M) :
    aeval x (φ.ramificationPolynomial α) = 0 ↔
      aeval (algebraMap L M α * x + algebraMap L M α) (φ.map (algebraMap 𝒪[K] K)) = 0 := by
  have h0 : algebraMap L M (α⁻¹ ^ φ.natDegree) ≠ 0 :=
    (_root_.map_ne_zero (algebraMap L M)).mpr (pow_ne_zero _ (inv_ne_zero hα))
  rw [aeval_ramificationPolynomial, mul_eq_zero, or_iff_right h0]

/-- In any field extension `M/L` with `α ≠ 0`, `(y - α) / α` is a root of
`φ.ramificationPolynomial α` if and only if `y` is a root of `φ`. -/
theorem aeval_div_sub_ramificationPolynomial_eq_zero_iff {M : Type*} [Field M] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] {φ : 𝒪[K][X]} {α : L} (hα : α ≠ 0) (y : M) :
    aeval ((y - algebraMap L M α) / algebraMap L M α) (φ.ramificationPolynomial α) = 0 ↔
      aeval y (φ.map (algebraMap 𝒪[K] K)) = 0 := by
  have hαM : algebraMap L M α ≠ 0 := (_root_.map_ne_zero (algebraMap L M)).mpr hα
  rw [aeval_ramificationPolynomial_eq_zero_iff hα, mul_div_cancel₀ _ hαM, sub_add_cancel]

/-- **Binomial expansion of the ramification polynomial.** Every coefficient `i` of
`φ.ramificationPolynomial α` is `α ^ (-deg φ) * ∑_{h = i}^{deg φ} (h choose i) φ_h α ^ h`. -/
theorem coeff_ramificationPolynomial (φ : 𝒪[K][X]) (α : L) (i : ℕ) :
    (φ.ramificationPolynomial α).coeff i =
      α⁻¹ ^ φ.natDegree *
        ∑ h ∈ Finset.Icc i φ.natDegree,
          (h.choose i : L) * algebraMap K L (φ.coeff h) * α ^ h := by
  set ι : 𝒪[K] →+* L := (algebraMap K L).comp (algebraMap 𝒪[K] K)
  have hcomp : (φ.map ι).comp (C α * X + C α) =
      ∑ h ∈ Finset.range (φ.natDegree + 1), C (ι (φ.coeff h) * α ^ h) * (X + 1) ^ h := by
    conv_lhs => rw [as_sum_range_C_mul_X_pow (φ.map ι)]
    have hdeg : (φ.map ι).natDegree ≤ φ.natDegree := natDegree_map_le
    rw [sum_comp]
    have hvan : ∀ h ∈ Finset.range (φ.natDegree + 1), h ∉ Finset.range ((φ.map ι).natDegree + 1) →
        C ((φ.map ι).coeff h) * (C α * X + C α) ^ h = 0 := by
      intro h _ hh
      rw [Finset.mem_range, not_lt] at hh
      rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul]
    have hlin : C α * X + C α = C α * (X + 1 : L[X]) := by rw [mul_add, mul_one]
    have hsum := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdeg)) hvan
    simp only [mul_comp, C_comp, X_pow_comp] at hsum ⊢
    rw [hsum]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [coeff_map, hlin, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
  rw [ramificationPolynomial_def, hcomp, coeff_C_mul]
  congr 1
  rw [finsetSum_coeff]
  have hsub : Finset.Icc i φ.natDegree ⊆ Finset.range (φ.natDegree + 1) := fun h hh ↦
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hh).2)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [coeff_C_mul, coeff_X_add_one_pow]
    simp only [ι, RingHom.coe_comp, Function.comp_apply]
    have hcoe : algebraMap 𝒪[K] K (φ.coeff h) = (φ.coeff h : K) := rfl
    rw [hcoe]
    ring
  · intro h hh hnot
    have hhi : h < i := by
      rw [Finset.mem_range] at hh
      rw [Finset.mem_Icc, not_and_or] at hnot
      omega
    rw [coeff_C_mul, coeff_X_add_one_pow, Nat.choose_eq_zero_of_lt hhi, Nat.cast_zero, mul_zero]

/-- For `i > deg φ`, the `i`-th coefficient of `φ.ramificationPolynomial α` vanishes. -/
theorem coeff_ramificationPolynomial_of_natDegree_lt {φ : 𝒪[K][X]} {α : L} {i : ℕ}
    (hi : φ.natDegree < i) : (φ.ramificationPolynomial α).coeff i = 0 := by
  rw [coeff_ramificationPolynomial, Finset.Icc_eq_empty (by omega), Finset.sum_empty, mul_zero]

/-- The degree of `φ.ramificationPolynomial α` is at most `deg φ`. -/
theorem natDegree_ramificationPolynomial_le (φ : 𝒪[K][X]) (α : L) :
    (φ.ramificationPolynomial α).natDegree ≤ φ.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hi ↦ coeff_ramificationPolynomial_of_natDegree_lt hi

/-- When `φ` is monic and `α ≠ 0`, the `deg φ`-th coefficient of `φ.ramificationPolynomial α` is
`1`. -/
theorem coeff_natDegree_ramificationPolynomial {φ : 𝒪[K][X]} (hφ : φ.Monic) {α : L}
    (hα : α ≠ 0) : (φ.ramificationPolynomial α).coeff φ.natDegree = 1 := by
  rw [coeff_ramificationPolynomial, Finset.Icc_self, Finset.sum_singleton, Nat.choose_self,
    Nat.cast_one, coeff_natDegree, hφ.leadingCoeff, OneMemClass.coe_one, map_one, one_mul, one_mul,
    inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hα)]

/-- When `φ` is monic and `α ≠ 0`, `φ.ramificationPolynomial α` has degree `deg φ`. -/
theorem natDegree_ramificationPolynomial {φ : 𝒪[K][X]} (hφ : φ.Monic) {α : L} (hα : α ≠ 0) :
    (φ.ramificationPolynomial α).natDegree = φ.natDegree :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_ramificationPolynomial_le φ α) <| by
    rw [coeff_natDegree_ramificationPolynomial hφ hα]
    exact one_ne_zero

/-- When `φ` is monic and `α ≠ 0`, `φ.ramificationPolynomial α` is monic. -/
theorem Monic.ramificationPolynomial {φ : 𝒪[K][X]} (hφ : φ.Monic) {α : L} (hα : α ≠ 0) :
    (φ.ramificationPolynomial α).Monic :=
  Monic.def.mpr <| Polynomial.coeff_natDegree.symm.trans <|
    (congrArg _ (natDegree_ramificationPolynomial hφ hα)).trans
      (coeff_natDegree_ramificationPolynomial hφ hα)

/-- Relation between the linear coefficient of `φ.ramificationPolynomial α` and `φ'(α)`: for
`α ≠ 0` and `1 ≤ deg φ`, `α ^ (deg φ - 1) * (φ.ramificationPolynomial α).coeff 1 = φ'(α)`. -/
theorem pow_mul_coeff_one_ramificationPolynomial {φ : 𝒪[K][X]} (hdeg : 1 ≤ φ.natDegree) {α : L}
    (hα : α ≠ 0) :
    α ^ (φ.natDegree - 1) * (φ.ramificationPolynomial α).coeff 1 =
      aeval α (φ.derivative.map (algebraMap 𝒪[K] K)) := by
  have h1 : (φ.ramificationPolynomial α).coeff 1 =
      (φ.ramificationPolynomial α).derivative.eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simp
  set ι : 𝒪[K] →+* L := (algebraMap K L).comp (algebraMap 𝒪[K] K)
  have hder : (φ.ramificationPolynomial α).derivative.eval 0 =
      α⁻¹ ^ φ.natDegree * (aeval α (φ.derivative.map (algebraMap 𝒪[K] K)) * α) := by
    rw [ramificationPolynomial_def, derivative_C_mul, derivative_comp]
    have hq : derivative (C α * X + C α) = C α := by simp
    have hp : (φ.map ι).derivative = (φ.derivative.map (algebraMap 𝒪[K] K)).map (algebraMap K L) :=
      by rw [← Polynomial.map_map, derivative_map, derivative_map]
    rw [hq, hp, eval_mul, eval_C, eval_mul, eval_C, eval_comp, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, zero_add, eval_map_algebraMap]
    ring
  calc
    α ^ (φ.natDegree - 1) * (φ.ramificationPolynomial α).coeff 1
        = (α ^ (φ.natDegree - 1) * α) * α⁻¹ ^ φ.natDegree *
            aeval α (φ.derivative.map (algebraMap 𝒪[K] K)) := by
          rw [h1, hder]; ring
    _ = aeval α (φ.derivative.map (algebraMap 𝒪[K] K)) := by
          rw [← pow_succ, Nat.sub_add_cancel hdeg, inv_pow,
            mul_inv_cancel₀ (pow_ne_zero _ hα), one_mul]

/-- If `φ` is separable over `K` and `α ≠ 0`, then `φ.ramificationPolynomial α` is separable over
`L`. -/
theorem Separable.ramificationPolynomial {φ : 𝒪[K][X]}
    (hsep : (φ.map (algebraMap 𝒪[K] K)).Separable) {α : L} (hα : α ≠ 0) :
    (φ.ramificationPolynomial α).Separable := by
  set p : L[X] := φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))
  have hp : p.Separable := by
    rw [show p = (φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L) from (Polynomial.map_map ..).symm]
    exact hsep.map
  obtain ⟨a, b, hab⟩ := (separable_def' p).mp hp
  set q : L[X] := C α * X + C α
  have hqder : derivative (p.comp q) = p.derivative.comp q * C α := by
    rw [derivative_comp]
    simp [q]
    ring
  have hcomp : (p.comp q).Separable := by
    rw [separable_def']
    refine ⟨a.comp q, C α⁻¹ * b.comp q, ?_⟩
    have h := congrArg (·.comp q) hab
    simp only [add_comp, mul_comp, one_comp] at h
    calc
      a.comp q * p.comp q + C α⁻¹ * b.comp q * derivative (p.comp q)
          = a.comp q * p.comp q + b.comp q * p.derivative.comp q * (C α⁻¹ * C α) := by
            rw [hqder]; ring
      _ = a.comp q * p.comp q + b.comp q * p.derivative.comp q := by
            rw [← C_mul, inv_mul_cancel₀ hα, C_1, mul_one]
      _ = 1 := h
  exact Separable.unit_mul
    (isUnit_C.mpr (IsUnit.mk0 _ (pow_ne_zero _ (inv_ne_zero hα)))) hcomp

end Algebraic

section Eisenstein

variable {K L : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem aeval_map_algebraMap_eq_coe (p : 𝒪[K][X]) (ξ : 𝒪[L]) :
    aeval (ξ : L) (p.map (algebraMap 𝒪[K] K)) = (aeval ξ p : L) := by
  have hcomp : (algebraMap K L).comp (algebraMap 𝒪[K] K) =
      (algebraMap 𝒪[L] L).comp (algebraMap 𝒪[K] 𝒪[L]) := by
    ext x
    exact (Valuation.HasExtension.val_algebraMap (vR := valuation K) (vA := valuation L) x).symm
  rw [aeval_def, eval₂_map, hcomp, aeval_def]
  exact (hom_eval₂ p (algebraMap 𝒪[K] 𝒪[L]) (algebraMap 𝒪[L] L) ξ).symm

private theorem eq_of_int_mul_add_eq_of_mem_Icc {i n h₁ h₂ : ℕ} {a₁ a₂ : ℤ} (_hi1 : 1 ≤ i)
    (hh₁ : h₁ ∈ Finset.Icc i n) (hh₂ : h₂ ∈ Finset.Icc i n) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (heq : (n : ℤ) * a₁ + h₁ = (n : ℤ) * a₂ + h₂) : h₁ = h₂ := by
  lift a₁ to ℕ using ha₁
  lift a₂ to ℕ using ha₂
  have hnat : n * a₁ + h₁ = n * a₂ + h₂ := by exact_mod_cast heq
  have hmod := congrArg (· % n) hnat
  rw [Nat.mul_add_mod] at hmod
  conv_rhs at hmod => rw [Nat.mul_add_mod]
  obtain ⟨hh₁i, hh₁n⟩ := Finset.mem_Icc.mp hh₁
  obtain ⟨hh₂i, hh₂n⟩ := Finset.mem_Icc.mp hh₂
  rcases eq_or_lt_of_le hh₁n with rfl | hlt₁ <;> rcases eq_or_lt_of_le hh₂n with rfl | hlt₂
  · rfl
  · rw [Nat.mod_self, Nat.mod_eq_of_lt hlt₂] at hmod; omega
  · rw [Nat.mod_eq_of_lt hlt₁, Nat.mod_self] at hmod; omega
  · rwa [Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at hmod

private theorem normalizedAddValuation_binomialTerm {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K])
    {ξ : 𝒪[L]} (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤)
    (i h : ℕ) :
    normalizedAddValuation L ((ξ : L)⁻¹ ^ φ.natDegree *
        ((h.choose i : L) * algebraMap K L (φ.coeff h) * (ξ : L) ^ h)) =
      (normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K))).map
        fun v ↦ (φ.natDegree : ℝ) * v + (h : ℝ) - φ.natDegree := by
  have hξirr : Irreducible ξ := irreducible_of_eisenstein_adjoin_eq_top φ hφ ξ hroot hgen
  have he : ramificationIndex K L = φ.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ hroot hgen
  have hξ0 : (ξ : L) ≠ 0 := fun h0 ↦ hξirr.ne_zero (Subtype.ext h0)
  have hinv : normalizedAddValuation L ((ξ : L)⁻¹ ^ φ.natDegree) =
      ((-(φ.natDegree : ℝ) : ℝ) : WithTop ℝ) := by
    rw [normalizedAddValuation_of_ne_zero (pow_ne_zero _ (inv_ne_zero hξ0)),
      addValInt_pow (inv_ne_zero hξ0), addValInt_inv, addValInt_irreducible hξirr,
      WithTop.coe_eq_coe]
    push_cast; ring
  rw [show (ξ : L)⁻¹ ^ φ.natDegree *
        ((h.choose i : L) * algebraMap K L (φ.coeff h) * (ξ : L) ^ h) =
      (ξ : L)⁻¹ ^ φ.natDegree *
        (algebraMap K L ((h.choose i : K) * (φ.coeff h : K)) * (ξ : L) ^ h) by simp,
    AddValuation.map_mul, hinv, AddValuation.map_mul, normalizedAddValuation_algebraMap, he,
    AddValuation.map_pow, normalizedAddValuation_irreducible hξirr, nsmul_one]
  cases normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) with
  | top => simp
  | coe v =>
    rw [WithTop.map_coe, WithTop.map_coe, ← WithTop.coe_natCast, ← WithTop.coe_add,
      ← WithTop.coe_add, WithTop.coe_eq_coe]
    ring

/-- **Exact valuation of the coefficients of the ramification polynomial.** Let `φ : 𝒪[K][X]` be an
Eisenstein polynomial and `ξ : 𝒪[L]` a root of `φ` with `L = K(ξ)`. For every `i` with
`1 ≤ i`, the terms in the binomial sum for `(φ.ramificationPolynomial (ξ : L)).coeff i`
have pairwise distinct valuation residues modulo `deg φ`, so its normalized additive valuation is
the infimum over `h ∈ [i, deg φ]` of `deg φ * v_K((h choose i) * φ_h) + h - deg φ`. -/
theorem normalizedAddValuation_coeff_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]} (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) {i : ℕ} (hi1 : 1 ≤ i) :
    normalizedAddValuation L ((φ.ramificationPolynomial (ξ : L)).coeff i) =
      (Finset.Icc i φ.natDegree).inf fun h ↦
        (normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K))).map
          fun v ↦ (φ.natDegree : ℝ) * v + (h : ℝ) - φ.natDegree := by
  classical
  set t : ℕ → L := fun h ↦
    (ξ : L)⁻¹ ^ φ.natDegree * ((h.choose i : L) * algebraMap K L (φ.coeff h) * (ξ : L) ^ h)
  have hterm (h : ℕ) := normalizedAddValuation_binomialTerm hφ hroot hgen i h
  have hne : ∀ h₁ ∈ Finset.Icc i φ.natDegree, ∀ h₂ ∈ Finset.Icc i φ.natDegree, h₁ ≠ h₂ →
      normalizedAddValuation L (t h₁) ≠ ⊤ → normalizedAddValuation L (t h₂) ≠ ⊤ →
      normalizedAddValuation L (t h₁) ≠ normalizedAddValuation L (t h₂) := by
    intro h₁ hh₁ h₂ hh₂ hhne ht₁ ht₂ heq
    rw [hterm h₁] at ht₁
    rw [hterm h₂] at ht₂
    rw [hterm h₁, hterm h₂] at heq
    have hc₁0 : ((h₁.choose i : K) * (φ.coeff h₁ : K)) ≠ 0 := fun h0 ↦ ht₁ (by simp [h0])
    have hc₂0 : ((h₂.choose i : K) * (φ.coeff h₂ : K)) ≠ 0 := fun h0 ↦ ht₂ (by simp [h0])
    rw [normalizedAddValuation_of_ne_zero hc₁0, normalizedAddValuation_of_ne_zero hc₂0,
      WithTop.map_coe, WithTop.map_coe, WithTop.coe_eq_coe] at heq
    have heq' : (φ.natDegree : ℝ) * (addValInt K ((h₁.choose i : K) * (φ.coeff h₁ : K)) : ℝ) + h₁ =
        (φ.natDegree : ℝ) * (addValInt K ((h₂.choose i : K) * (φ.coeff h₂ : K)) : ℝ) + h₂ := by
      linarith
    exact hhne (eq_of_int_mul_add_eq_of_mem_Icc hi1 hh₁ hh₂
      ((mem_integer_iff_addValInt_nonneg hc₁0).mp (mul_mem (natCast_mem 𝒪[K] _) (φ.coeff h₁).2))
      ((mem_integer_iff_addValInt_nonneg hc₂0).mp (mul_mem (natCast_mem 𝒪[K] _) (φ.coeff h₂).2))
      (by exact_mod_cast heq'))
  rw [coeff_ramificationPolynomial, Finset.mul_sum,
    show (∑ x ∈ Finset.Icc i φ.natDegree,
        (ξ : L)⁻¹ ^ φ.natDegree *
          ((x.choose i : L) * algebraMap K L (φ.coeff x) * (ξ : L) ^ x)) =
      ∑ h ∈ Finset.Icc i φ.natDegree, t h from rfl,
    AddValuation.map_sum_eq_inf_of_ne _ _ _ hne]
  exact Finset.inf_congr rfl fun h _ ↦ hterm h

/-- Every coefficient of `φ.ramificationPolynomial (ξ : L)` at an Eisenstein generator `ξ` lies in
`𝒪[L]`. -/
theorem coeff_ramificationPolynomial_mem_integer {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K])
    {ξ : 𝒪[L]} (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤)
    (i : ℕ) : (φ.ramificationPolynomial (ξ : L)).coeff i ∈ 𝒪[L] := by
  rcases eq_or_ne i 0 with rfl | hi0
  · have hrootK : aeval (ξ : L) (φ.map (algebraMap 𝒪[K] K)) = 0 := by
      rw [aeval_map_algebraMap_eq_coe, ← eval_map_algebraMap, hroot.eq_zero, ZeroMemClass.coe_zero]
    rw [coeff_zero_ramificationPolynomial_of_aeval_eq_zero hrootK]
    exact zero_mem 𝒪[L]
  rw [mem_integer_iff_normalizedAddValuation_nonneg,
    normalizedAddValuation_coeff_ramificationPolynomial hφ hroot hgen
      (Nat.one_le_iff_ne_zero.mpr hi0), Finset.le_inf_iff]
  intro h hh
  obtain ⟨hhi, hhn⟩ := Finset.mem_Icc.mp hh
  rcases eq_or_lt_of_le hhn with heq | hlt
  · have hv0 : 0 ≤ normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) :=
      mem_integer_iff_normalizedAddValuation_nonneg.mp
        (mul_mem (natCast_mem 𝒪[K] _) (φ.coeff h).2)
    cases hv : normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) with
    | top => simp
    | coe v =>
      rw [hv, ← WithTop.coe_zero, WithTop.coe_le_coe] at hv0
      rw [WithTop.map_coe, ← WithTop.coe_zero, WithTop.coe_le_coe, heq]
      nlinarith
  · have hv : 1 ≤ normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) := by
      rw [AddValuation.map_mul]
      exact (zero_add (1 : WithTop ℝ)) ▸ add_le_add
        (mem_integer_iff_normalizedAddValuation_nonneg.mp (natCast_mem 𝒪[K] _))
        (mem_maximalIdeal_iff_one_le_normalizedAddValuation.mp (hφ.mem hlt))
    cases hval : normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) with
    | top => simp
    | coe v =>
      rw [hval, ← WithTop.coe_one, WithTop.coe_le_coe] at hv
      rw [WithTop.map_coe, ← WithTop.coe_zero, WithTop.coe_le_coe]
      have : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hi0).trans hhi
      nlinarith

/-- At an Eisenstein generator `ξ` of a separable extension `L/K`, the linear coefficient of
`φ.ramificationPolynomial (ξ : L)` has normalized valuation `ramificationHeight K L`. -/
theorem normalizedAddValuation_coeff_one_ramificationPolynomial [Algebra.IsSeparable K L]
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]}
    (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤) :
    normalizedAddValuation L ((φ.ramificationPolynomial (ξ : L)).coeff 1) =
      ((ramificationHeight K L : ℝ) : WithTop ℝ) := by
  have hξirr : Irreducible ξ := irreducible_of_eisenstein_adjoin_eq_top φ hφ ξ hroot hgen
  have he : ramificationIndex K L = φ.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ hroot hgen
  have hn1 : 1 ≤ φ.natDegree := he ▸ ramificationIndex_pos (K := K) (L := L)
  have hξ0 : (ξ : L) ≠ 0 := fun h ↦ hξirr.ne_zero (Subtype.ext h)
  have hder := pow_mul_coeff_one_ramificationPolynomial (L := L) hn1 hξ0
  have hd := natCast_differentExponent_eq_addVal_aeval_derivative_of_eisenstein_adjoin_eq_top
    φ hφ ξ hroot hgen
  have hvder : normalizedAddValuation L (aeval (ξ : L) (φ.derivative.map (algebraMap 𝒪[K] K))) =
      ((differentExponent K L : ℝ) : WithTop ℝ) := by
    rw [aeval_map_algebraMap_eq_coe, normalizedAddValuation_coe_integer, ← hd]
    rfl
  have hmul := congrArg (normalizedAddValuation L) hder
  rw [AddValuation.map_mul, AddValuation.map_pow, normalizedAddValuation_irreducible hξirr,
    nsmul_one, hvder, differentExponent_eq_ramificationIndex_sub_one_add_ramificationHeight K L,
    he] at hmul
  cases hc : normalizedAddValuation L ((φ.ramificationPolynomial (ξ : L)).coeff 1) with
  | top =>
    rw [hc, add_top] at hmul
    exact absurd hmul WithTop.top_ne_coe
  | coe v =>
    rw [hc] at hmul
    have hreal : ((φ.natDegree - 1 : ℕ) : ℝ) + v =
        ((φ.natDegree - 1 + ramificationHeight K L : ℕ) : ℝ) :=
      WithTop.coe_injective (by simpa using hmul)
    push_cast at hreal
    exact WithTop.coe_eq_coe.mpr (by linarith)

/-- At an Eisenstein generator `ξ` of a separable extension `L/K`, the linear coefficient of
`φ.ramificationPolynomial (ξ : L)` is nonzero. -/
theorem coeff_one_ramificationPolynomial_ne_zero [Algebra.IsSeparable K L] {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]}
    (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤) :
    (φ.ramificationPolynomial (ξ : L)).coeff 1 ≠ 0 := by
  intro h0
  have h := normalizedAddValuation_coeff_one_ramificationPolynomial hφ hroot hgen
  simp [h0] at h

/-- Integer-valued form of `normalizedAddValuation_coeff_one_ramificationPolynomial`. -/
theorem addValInt_coeff_one_ramificationPolynomial [Algebra.IsSeparable K L] {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]}
    (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤) :
    addValInt L ((φ.ramificationPolynomial (ξ : L)).coeff 1) = ramificationHeight K L := by
  have h := normalizedAddValuation_coeff_one_ramificationPolynomial hφ hroot hgen
  rw [normalizedAddValuation_of_ne_zero (coeff_one_ramificationPolynomial_ne_zero hφ hroot hgen),
    WithTop.coe_eq_coe] at h
  exact_mod_cast h

/-- At an Eisenstein generator `ξ` of a separable extension `L/K`, the trailing degree of
`φ.ramificationPolynomial (ξ : L)` is `1`. -/
theorem natTrailingDegree_ramificationPolynomial [Algebra.IsSeparable K L] {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]}
    (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤) :
    (φ.ramificationPolynomial (ξ : L)).natTrailingDegree = 1 := by
  have hrootK : aeval (ξ : L) (φ.map (algebraMap 𝒪[K] K)) = 0 := by
    rw [aeval_map_algebraMap_eq_coe, ← eval_map_algebraMap, hroot.eq_zero, ZeroMemClass.coe_zero]
  refine le_antisymm
    (natTrailingDegree_le_of_ne_zero (coeff_one_ramificationPolynomial_ne_zero hφ hroot hgen)) ?_
  by_contra! hlt
  have h0 : (φ.ramificationPolynomial (ξ : L)).natTrailingDegree = 0 := Nat.lt_one_iff.mp hlt
  have hne : φ.ramificationPolynomial (ξ : L) ≠ 0 := fun hz ↦
    coeff_one_ramificationPolynomial_ne_zero hφ hroot hgen (by simp [hz])
  have ht := trailingCoeff_ne_zero.mpr hne
  rw [trailingCoeff, h0, coeff_zero_ramificationPolynomial_of_aeval_eq_zero hrootK] at ht
  exact ht rfl

/-- At `i = p ^ w` (`p = ringChar 𝓀[K]`, `w = wildRamificationExponent K L`), the coefficient of a
monic Eisenstein ramification polynomial has valuation `0` (hence is a unit of `𝒪[L]`). -/
theorem normalizedAddValuation_coeff_pow_wildRamificationExponent_ramificationPolynomial
    {φ : 𝒪[K][X]} (hmon : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]}
    (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤) :
    normalizedAddValuation L
        ((φ.ramificationPolynomial (ξ : L)).coeff
          (ringChar 𝓀[K] ^ wildRamificationExponent K L)) = 0 := by
  set p := ringChar 𝓀[K]
  set w := wildRamificationExponent K L
  have hp : p.Prime := CharP.prime_ringChar 𝓀[K]
  have he : ramificationIndex K L = φ.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ hroot hgen
  have hfac := tameRamificationIndex_mul_pow_wildRamificationExponent K L
  have hle_n : p ^ w ≤ φ.natDegree := by
    rw [← he, ← hfac]
    exact Nat.le_mul_of_pos_left _ (tameRamificationIndex_pos K L)
  refine le_antisymm ?_
    (mem_integer_iff_normalizedAddValuation_nonneg.mp
      (coeff_ramificationPolynomial_mem_integer hφ hroot hgen (p ^ w)))
  rw [normalizedAddValuation_coeff_ramificationPolynomial hφ hroot hgen (one_le_pow₀ hp.one_le)]
  refine (Finset.inf_le (Finset.mem_Icc.mpr ⟨hle_n, le_rfl⟩)).trans ?_
  have hndvd : ¬ p ∣ φ.natDegree.choose (p ^ w) := by
    rw [← he, ← hfac, hp.dvd_choose_mul_pow_iff]
    exact not_ringChar_dvd_tameRamificationIndex K L
  have hu : IsUnit ((φ.natDegree.choose (p ^ w) : ℕ) : 𝒪[K]) :=
    IsLocalRing.isUnit_natCast_iff_not_dvd.mpr hndvd
  have hv0 : normalizedAddValuation K (φ.natDegree.choose (p ^ w) : K) = 0 := by
    rw [show (φ.natDegree.choose (p ^ w) : K) =
        (((φ.natDegree.choose (p ^ w) : ℕ) : 𝒪[K]) : K) by simp,
      normalizedAddValuation_coe_integer, IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu]
    simp
  rw [coeff_natDegree, hmon.leadingCoeff, OneMemClass.coe_one, mul_one, hv0, ← WithTop.coe_zero,
    WithTop.map_coe, WithTop.coe_le_coe]
  linarith

/-- For `1 ≤ i < p ^ w` (`p = ringChar 𝓀[K]`, `w = wildRamificationExponent K L`), the `i`-th
coefficient of an Eisenstein ramification polynomial lies in `𝓂[L]`: its normalized valuation is at
least `1`. -/
theorem one_le_normalizedAddValuation_coeff_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]}
    (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤) {i : ℕ}
    (hi1 : 1 ≤ i) (hiw : i < ringChar 𝓀[K] ^ wildRamificationExponent K L) :
    1 ≤ normalizedAddValuation L ((φ.ramificationPolynomial (ξ : L)).coeff i) := by
  set p := ringChar 𝓀[K]
  set w := wildRamificationExponent K L
  have hp : p.Prime := CharP.prime_ringChar 𝓀[K]
  have he : ramificationIndex K L = φ.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ hroot hgen
  have hdvdn : p ^ w ∣ φ.natDegree := by
    rw [← he, ← tameRamificationIndex_mul_pow_wildRamificationExponent K L]
    exact dvd_mul_left _ _
  rw [normalizedAddValuation_coeff_ramificationPolynomial hφ hroot hgen hi1, Finset.le_inf_iff]
  intro h hh
  obtain ⟨hhi, hhn⟩ := Finset.mem_Icc.mp hh
  have hv1 : 1 ≤ normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) := by
    rw [AddValuation.map_mul]
    rcases eq_or_lt_of_le hhn with rfl | hlt
    · have hmem : ((φ.natDegree.choose i : ℕ) : 𝒪[K]) ∈ 𝓂[K] := by
        rw [mem_maximalIdeal, mem_nonunits_iff, IsLocalRing.isUnit_natCast_iff_not_dvd, not_not]
        exact hp.dvd_choose_of_pow_dvd hdvdn hi1 hiw
      have h1 : 1 ≤ normalizedAddValuation K (φ.natDegree.choose i : K) := by
        simpa using mem_maximalIdeal_iff_one_le_normalizedAddValuation.mp hmem
      exact (add_zero (1 : WithTop ℝ)) ▸ add_le_add h1
        (mem_integer_iff_normalizedAddValuation_nonneg.mp (φ.coeff φ.natDegree).2)
    · exact (zero_add (1 : WithTop ℝ)) ▸ add_le_add
        (mem_integer_iff_normalizedAddValuation_nonneg.mp (natCast_mem 𝒪[K] _))
        (mem_maximalIdeal_iff_one_le_normalizedAddValuation.mp (hφ.mem hlt))
  cases hval : normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) with
  | top => simp
  | coe v =>
    rw [hval, ← WithTop.coe_one, WithTop.coe_le_coe] at hv1
    rw [WithTop.map_coe, ← WithTop.coe_one, WithTop.coe_le_coe]
    have : (1 : ℝ) ≤ h := by exact_mod_cast hi1.trans hhi
    nlinarith

/-- **Prime-power coefficient domination.** On each prime-power interval
`p ^ r ≤ i < p ^ (r + 1)` (`p = ringChar 𝓀[K]`), the `p ^ r`-th coefficient of an Eisenstein
ramification polynomial has normalized valuation at most that of the `i`-th coefficient.
Consequently only prime powers can be vertices of the ramification polygon. -/
theorem normalizedAddValuation_coeff_pow_le_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {ξ : 𝒪[L]}
    (hroot : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤) {r i : ℕ}
    (hri : ringChar 𝓀[K] ^ r ≤ i) (hir : i < ringChar 𝓀[K] ^ (r + 1)) :
    normalizedAddValuation L ((φ.ramificationPolynomial (ξ : L)).coeff (ringChar 𝓀[K] ^ r)) ≤
      normalizedAddValuation L ((φ.ramificationPolynomial (ξ : L)).coeff i) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.prime_ringChar 𝓀[K]
  have hp1 : 1 ≤ p ^ r := one_le_pow₀ hp.one_le
  rw [normalizedAddValuation_coeff_ramificationPolynomial hφ hroot hgen hp1,
    normalizedAddValuation_coeff_ramificationPolynomial hφ hroot hgen (hp1.trans hri),
    Finset.le_inf_iff]
  intro h hh
  obtain ⟨hhi, hhn⟩ := Finset.mem_Icc.mp hh
  refine (Finset.inf_le (Finset.mem_Icc.mpr ⟨hri.trans hhi, hhn⟩)).trans ?_
  have hchoose : normalizedAddValuation K (h.choose (p ^ r) : K) ≤
      normalizedAddValuation K (h.choose i : K) :=
    normalizedAddValuation_natCast_le_of_factorization_le
      (Nat.choose_pos (hri.trans hhi)).ne' (Nat.choose_pos hhi).ne'
      (hp.factorization_choose_pow_le hri hir hhi)
  have hprod : normalizedAddValuation K ((h.choose (p ^ r) : K) * (φ.coeff h : K)) ≤
      normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) := by
    rw [AddValuation.map_mul, AddValuation.map_mul]
    exact add_le_add hchoose le_rfl
  cases hv₁ : normalizedAddValuation K ((h.choose (p ^ r) : K) * (φ.coeff h : K)) with
  | top =>
    rw [hv₁, top_le_iff] at hprod
    simp [hprod]
  | coe v₁ =>
    cases hv₂ : normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K)) with
    | top => simp
    | coe v₂ =>
      rw [hv₁, hv₂, WithTop.coe_le_coe] at hprod
      rw [WithTop.map_coe, WithTop.map_coe, WithTop.coe_le_coe]
      nlinarith

end Eisenstein

end Polynomial

end
