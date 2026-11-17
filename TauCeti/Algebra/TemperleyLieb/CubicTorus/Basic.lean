/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Algebra.TemperleyLieb.Star
-- Private: trace of a projection for the dimension of the inversion-fixed subalgebra and weighted
-- norm-squared sums for Parseval positivity are used only inside proofs.
import Mathlib.LinearAlgebra.Trace
import TauCeti.Basic.Complex.BigOperators

/-!
# The cubic quantum torus and its inversion-fixed Temperley–Lieb representation at `δ = √3`

At the loop parameter `δ = √3 = 2 cos (π / 6)` — corresponding to Jones index `δ² = 3` — the
Temperley–Lieb algebra `TemperleyLieb ℂ (√3 : ℂ) m` maps into the inversion-fixed subalgebra
`cubicFixed (m - 1)` of the cubic quantum torus `CubicTorus (m - 1)` via a `ℂ`-algebra homomorphism
`cubicFixedHom m` that intertwines the Temperley–Lieb analytic adjoint with the positive-trace
adjoint `cubicAdjoint (m - 1)`.

Concretely, on `Fin N → ZMod 3` let `chainForm N` be the alternating biadditive chain form

  `B(a, b) = ∑_{j < N - 1} (a_j b_{j + 1} - b_j a_{j + 1})`,

let `ω = exp (2 π i / 3)` be `cubeRootOfUnity`, and form the twisted monoid algebra
`CubicTorus N = twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)` with
factor set `α(a, b) = ω ^ (2 * B(a, b))`. Its Weyl basis `W(a) = weyl N a` satisfies
`W(a) * W(b) = α(a, b) • W(a * b)`, `W(a) ^ 3 = 1`, and `W(a) * W(b) = ω ^ B(a, b) • (W(b) * W(a))`,
so the site unitaries `U_j = cubicSite N j = W(e_j)` obey `U_j ^ 3 = 1`,
`U_j * U_{j + 1} = ω • (U_{j + 1} * U_j)`, and commute at distance at least two.

* **Analytic adjoint and Parseval positivity**: the conjugate-linear map
  `cubicAdjoint N : CubicTorus N →ₗ⋆[ℂ] CubicTorus N` sending `W(a) ↦ W(a⁻¹)` is involutive and
  product-reversing. The scalar-part trace `s_N = cubicScalarCoefficient N` extracting the `W(1)`
  coefficient satisfies the sesquilinear and quadratic Parseval identities
  `s_N (x† * y) = ∑_a conj x_a * y_a` and `s_N (x† * x) = ∑_a |x_a|² ≥ 0`, vanishing only at
  `x = 0`.
* **Inversion-fixed subalgebra**: the algebra involution `θ_N = cubicInversion N` sending
  `W(a) ↦ W(a⁻¹)` commutes with `cubicAdjoint N`. Its fixed-point subalgebra `cubicFixed N` is the
  range of the projection `2⁻¹ • (id + θ_N)`, whose trace is `(3 ^ N + 1) / 2`, yielding
  `Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* **Site projections and Temperley–Lieb map**: the elements
  `p_j = cubicProjection N j = 3⁻¹ • (1 + U_j + U_j ^ 2)` lie in `cubicFixed N`, are self-adjoint
  idempotents, satisfy `p_i * p_j * p_i = 3⁻¹ • p_i` for `|i - j| = 1`, and commute for
  `|i - j| ≥ 2`. Rescaling by `√3` defines
  `cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending `e (√3 : ℂ) j`
  to `(√3 : ℂ) • p_j` and intertwining `star` with `cubicFixedAdjoint (m - 1)`.

Surjectivity of `cubicFixedHom m`, the tower inclusions, the Markov trace identity, and the
identification of the Jones quotient at `δ = √3` with `cubicFixed (m - 1)` are established in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`. The Gaussian braid representation and its
finiteness are established in `TauCeti.Algebra.TemperleyLieb.CubicTorus.Braid`.

## Main definitions

* `TauCeti.TemperleyLieb.chainForm`: the alternating biadditive chain form on `Fin N → ZMod 3`.
* `TauCeti.TemperleyLieb.cubicRadicalVec`: the alternating vector `(1, 0, 1, 0, …)` spanning the
  radical of `chainForm N` when `N` is odd.
* `TauCeti.TemperleyLieb.cubeRootOfUnity`, `TauCeti.TemperleyLieb.cubeRootPow`, and
  `TauCeti.TemperleyLieb.cubicFactor`: the primitive cube root `ω = exp (2 π i / 3)`, its
  `ZMod 3`-indexed powers, and the normalized factor set `α(a, b) = ω ^ (2 * B(a, b))`.
* `TauCeti.TemperleyLieb.CubicTorus`, `TauCeti.TemperleyLieb.weyl`, and
  `TauCeti.TemperleyLieb.weylBasis`: the cubic quantum torus `G_N` and its Weyl basis `W(a)`.
* `TauCeti.TemperleyLieb.cubicAdjoint` and `TauCeti.TemperleyLieb.cubicFixedAdjoint`: the
  conjugate-linear analytic adjoint `W(a) ↦ W(a⁻¹)` on `CubicTorus N` and its restriction to
  `cubicFixed N`.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient`: the normalized scalar-part trace `s_N`.
* `TauCeti.TemperleyLieb.cubicInversion` and `TauCeti.TemperleyLieb.cubicFixed`: the algebra
  involution `θ_N : W(a) ↦ W(a⁻¹)` and its fixed-point subalgebra `C_N`.
* `TauCeti.TemperleyLieb.cubicSite`, `TauCeti.TemperleyLieb.cubicProjection`, and
  `TauCeti.TemperleyLieb.cubicFixedHom`: the site unitaries `U_j`, the projections
  `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)`, and the comparison homomorphism
  `TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.eq_zero_of_forall_chainForm_eq_zero_of_even` and
  `TauCeti.TemperleyLieb.exists_smul_cubicRadicalVec_of_forall_chainForm_eq_zero_of_odd`:
  classification of the radical of `chainForm N` by the parity of `N`.
* `TauCeti.TemperleyLieb.finrank_cubicTorus` and `TauCeti.TemperleyLieb.finrank_cubicFixed`:
  `Module.finrank ℂ (CubicTorus N) = 3 ^ N` and
  `Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicAdjoint_mul`,
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicAdjoint_mul_self`,
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicAdjoint_mul_self_nonneg`, and
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff`: Parseval
  identities, positivity, and faithfulness of `s_N (x† * x)`.
* `TauCeti.TemperleyLieb.cubicFixedHom_star`: star compatibility of `cubicFixedHom`.

## Implementation notes

`CubicTorus N` is an abbreviation for a `Subalgebra ℂ (Module.End ℂ _)` produced by
`TauCeti.twistedMonoidAlgebra`. To avoid installing an orphan `StarRing` instance on a subtype of
linear endomorphisms, the conjugate-linear analytic adjoint is exposed as the conjugate-linear
maps `cubicAdjoint N` and `cubicFixedAdjoint N`, matching the convention of
`TauCeti.TemperleyLieb.cliffordAdjoint` and `TauCeti.TemperleyLieb.evenCliffordAdjoint`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, §11.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702, Proposition 3.6.
-/

public section

open scoped ComplexConjugate ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Arithmetic helpers for `√3` in `ℂ` -/

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint instances
`TemperleyLieb.instStarRing` and `TemperleyLieb.instStarModule`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

private theorem sqrt_three_coe_mul_self :
    (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-! ### The alternating chain form on `Fin N → ZMod 3` and its radical -/

/-- The alternating biadditive **chain form**
`B(a, b) = ∑_{j < N - 1} (a_j b_{j + 1} - b_j a_{j + 1})` on `Fin N → ZMod 3`. -/
def chainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0

/-- Unfolding `chainForm` as a double sum over adjacent index pairs. -/
theorem chainForm_def (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b =
      ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0 :=
  (rfl)

/-- `chainForm` is additive in its first argument. -/
theorem chainForm_add_left (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N (a + b) c = chainForm N a c + chainForm N b c := by
  simp only [chainForm_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring

/-- `chainForm` is additive in its second argument. -/
theorem chainForm_add_right (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N a (b + c) = chainForm N a b + chainForm N a c := by
  simp only [chainForm_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring

/-- `chainForm` vanishes when its first argument is zero. -/
@[simp]
theorem chainForm_zero_left (N : ℕ) (b : Fin N → ZMod 3) :
    chainForm N 0 b = 0 := by
  simp [chainForm_def]

/-- `chainForm` vanishes when its second argument is zero. -/
@[simp]
theorem chainForm_zero_right (N : ℕ) (a : Fin N → ZMod 3) :
    chainForm N a 0 = 0 := by
  simp [chainForm_def]

/-- `chainForm` is homogeneous in its first argument. -/
theorem chainForm_smul_left (N : ℕ) (c : ZMod 3) (a b : Fin N → ZMod 3) :
    chainForm N (c • a) b = c * chainForm N a b := by
  simp only [chainForm_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `chainForm` is homogeneous in its second argument. -/
theorem chainForm_smul_right (N : ℕ) (c : ZMod 3) (a b : Fin N → ZMod 3) :
    chainForm N a (c • b) = c * chainForm N a b := by
  simp only [chainForm_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Negating the first argument negates `chainForm`. -/
@[simp]
theorem chainForm_neg_left (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) b = -chainForm N a b := by
  simpa using chainForm_smul_left N (-1) a b

/-- Negating the second argument negates `chainForm`. -/
@[simp]
theorem chainForm_neg_right (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a (-b) = -chainForm N a b := by
  simpa using chainForm_smul_right N (-1) a b

/-- `chainForm` is alternating: `B(a, a) = 0`. -/
@[simp]
theorem chainForm_self (N : ℕ) (a : Fin N → ZMod 3) :
    chainForm N a a = 0 := by
  simp only [chainForm_def]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  split_ifs <;> ring

/-- `chainForm` is skew-symmetric: `B(b, a) = -B(a, b)`. -/
theorem chainForm_swap (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N b a = -chainForm N a b := by
  simp only [chainForm_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- Pairing `a` with the `k`-th standard basis vector extracts `a (k - 1) - a (k + 1)`
(with out-of-range terms taken to be `0`). -/
theorem chainForm_single_right (N : ℕ) (a : Fin N → ZMod 3) (k : Fin N) :
    chainForm N a (Pi.single k 1) =
      (if h : 0 < k.1 then a ⟨k.1 - 1, by omega⟩ else 0) -
        (if h : k.1 + 1 < N then a ⟨k.1 + 1, h⟩ else 0) := by
  have h1 : (∑ i : Fin N, ∑ j : Fin N,
      if (i : ℕ) + 1 = j then a i * (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) j else 0) =
      if h : 0 < k.1 then a ⟨k.1 - 1, by omega⟩ else 0 := by
    have hinner (i : Fin N) :
        (∑ j : Fin N,
            if (i : ℕ) + 1 = j then a i * (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) j else 0) =
          if (i : ℕ) + 1 = k then a i else 0 := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        simp [Pi.single_eq_of_ne hjk]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    simp_rw [hinner]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨k.1 - 1, by omega⟩]
      · simp [Nat.sub_add_cancel h]
      · intro i _ hi
        exact ite_eq_right_iff.mpr fun heq ↦ absurd (Fin.ext (by dsimp; omega)) hi
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right_iff.mpr fun heq ↦ by omega
  have h2 : (∑ i : Fin N, ∑ j : Fin N,
      if (i : ℕ) + 1 = j then (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) i * a j else 0) =
      if h : k.1 + 1 < N then a ⟨k.1 + 1, h⟩ else 0 := by
    rw [Finset.sum_eq_single k]
    · split_ifs with h
      · rw [Finset.sum_eq_single ⟨k.1 + 1, h⟩]
        · simp
        · intro j _ hj
          exact ite_eq_right_iff.mpr fun heq ↦ absurd (Fin.ext (by dsimp; omega)) hj
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right_iff.mpr fun heq ↦ by omega
    · intro i _ hik
      exact Finset.sum_eq_zero fun j _ ↦ by simp [Pi.single_eq_of_ne hik]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [chainForm_def, ← h1, ← h2]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- Value of `chainForm N` on pairs of standard basis vectors. -/
theorem chainForm_single_single (N : ℕ) (i j : Fin N) :
    chainForm N (Pi.single i 1) (Pi.single j 1) =
      if (i : ℕ) + 1 = j then 1 else if (j : ℕ) + 1 = i then -1 else 0 := by
  rw [chainForm_single_right]
  by_cases h1 : (i : ℕ) + 1 = j
  · have hj0 : 0 < j.1 := by omega
    have heq1 : (⟨j.1 - 1, by omega⟩ : Fin N) = i := Fin.ext (by dsimp; omega)
    by_cases hjN : j.1 + 1 < N
    · have hne2 : (⟨j.1 + 1, hjN⟩ : Fin N) ≠ i := ne_of_apply_ne Fin.val (by dsimp; omega)
      simp [h1, hj0, heq1, hjN, Pi.single_eq_of_ne hne2]
    · simp [h1, hj0, heq1, hjN]
  · by_cases h2 : (j : ℕ) + 1 = i
    · by_cases hj0 : 0 < j.1
      · have hne1 : (⟨j.1 - 1, by omega⟩ : Fin N) ≠ i := ne_of_apply_ne Fin.val (by dsimp; omega)
        simp [h1, h2, hj0, Pi.single_eq_of_ne hne1]
      · simp [h1, h2, hj0]
    · have ht1 :
          (if h : 0 < j.1 then
            (Pi.single i (1 : ZMod 3) : Fin N → ZMod 3) ⟨j.1 - 1, by omega⟩ else 0) = 0 := by
        split_ifs with hj0
        · exact Pi.single_eq_of_ne (ne_of_apply_ne Fin.val (by dsimp; omega)) _
        · rfl
      have ht2 :
          (if h : j.1 + 1 < N then
            (Pi.single i (1 : ZMod 3) : Fin N → ZMod 3) ⟨j.1 + 1, h⟩ else 0) = 0 := by
        split_ifs with hjN
        · exact Pi.single_eq_of_ne (ne_of_apply_ne Fin.val (by dsimp; omega)) _
        · rfl
      simp [h1, h2, ht1, ht2]

/-- The alternating vector `(1, 0, 1, 0, …)` in `Fin N → ZMod 3`, which spans the radical of
`chainForm N` when `N` is odd. -/
def cubicRadicalVec (N : ℕ) : Fin N → ZMod 3 :=
  fun i ↦ if Even (i : ℕ) then 1 else 0

/-- Entrywise formula for `cubicRadicalVec N`. -/
@[simp]
theorem cubicRadicalVec_apply (N : ℕ) (i : Fin N) :
    cubicRadicalVec N i = if Even (i : ℕ) then 1 else 0 :=
  (rfl)

/-- For odd `N`, `cubicRadicalVec N` lies in the radical of `chainForm N`. -/
theorem chainForm_cubicRadicalVec_left_of_odd {N : ℕ} (hN : Odd N) (b : Fin N → ZMod 3) :
    chainForm N (cubicRadicalVec N) b = 0 := by
  have hsingle (k : Fin N) : chainForm N (cubicRadicalVec N) (Pi.single k 1) = 0 := by
    rw [chainForm_single_right]
    rcases Nat.even_or_odd k.1 with hk | hk
    · have ht1 :
          (if h : 0 < k.1 then cubicRadicalVec N ⟨k.1 - 1, by omega⟩ else 0) = 0 := by
        split_ifs with h
        · obtain ⟨t, ht⟩ := hk
          have hodd : ¬ Even (k.1 - 1) := Nat.not_even_iff_odd.mpr ⟨t - 1, by omega⟩
          simp [hodd]
        · rfl
      have ht2 :
          (if h : k.1 + 1 < N then cubicRadicalVec N ⟨k.1 + 1, h⟩ else 0) = 0 := by
        split_ifs with h
        · have hodd : ¬ Even (k.1 + 1) := Nat.not_even_iff_odd.mpr hk.add_one
          simp [hodd]
        · rfl
      rw [ht1, ht2, sub_self]
    · obtain ⟨t, ht⟩ := hk
      obtain ⟨m, hm⟩ := hN
      have hpos : 0 < k.1 := by omega
      have hlt : k.1 + 1 < N := by omega
      have he1 : Even (k.1 - 1) := ⟨t, by omega⟩
      have he2 : Even (k.1 + 1) := ⟨t + 1, by omega⟩
      simp [hpos, hlt, he1, he2]
  have hsum : b = ∑ k : Fin N, b k • Pi.single k (1 : ZMod 3) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  induction (Finset.univ : Finset (Fin N)) using Finset.cons_induction with
  | empty => simp
  | cons k s hks ih =>
    rw [Finset.sum_cons, chainForm_add_right, chainForm_smul_right, hsingle, mul_zero, zero_add, ih]

/-- Every vector in the radical of `chainForm N` (for `0 < N`) is a scalar multiple of
`cubicRadicalVec N`. -/
private theorem eq_smul_cubicRadicalVec_of_forall_chainForm_eq_zero {N : ℕ} (hN : 0 < N)
    {a : Fin N → ZMod 3} (ha : ∀ b, chainForm N a b = 0) :
    a = a ⟨0, hN⟩ • cubicRadicalVec N := by
  have hstep : ∀ (i : ℕ) (hi : i < N),
      a ⟨i, hi⟩ = if Even i then a ⟨0, hN⟩ else 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      match i with
      | 0 => simp
      | 1 =>
        have h0 := ha (Pi.single ⟨0, hN⟩ 1)
        rw [chainForm_single_right] at h0
        simp [hi] at h0
        simp [h0]
      | j + 2 =>
        have hmid := ha (Pi.single ⟨j + 1, by omega⟩ 1)
        rw [chainForm_single_right] at hmid
        have hpos : 0 < j + 1 := by omega
        have hlt : j + 1 + 1 < N := hi
        simp only [hpos, hlt, dite_true, Nat.add_sub_cancel] at hmid
        have heq : a ⟨j + 2, hi⟩ = a ⟨j, by omega⟩ := (sub_eq_zero.mp hmid).symm
        rw [heq, ih j (by omega) (by omega)]
        simp [Nat.even_add]
  ext i
  rw [Pi.smul_apply, smul_eq_mul, cubicRadicalVec_apply]
  simpa [mul_ite] using hstep i.1 i.2

/-- For even `N`, `chainForm N` is nondegenerate: its radical is `{0}`. -/
theorem eq_zero_of_forall_chainForm_eq_zero_of_even {N : ℕ} (hN : Even N)
    {a : Fin N → ZMod 3} (ha : ∀ b, chainForm N a b = 0) : a = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · exact Subsingleton.elim a 0
  · have hrad := eq_smul_cubicRadicalVec_of_forall_chainForm_eq_zero hpos ha
    obtain ⟨m, hm⟩ := hN
    have hlast := ha (Pi.single ⟨N - 1, by omega⟩ 1)
    rw [chainForm_single_right] at hlast
    have hlt1 : 0 < N - 1 := by omega
    have hlt2 : ¬ (N - 1) + 1 < N := by omega
    simp only [hlt1, hlt2, dite_true, dite_false, sub_zero] at hlast
    have hev : Even (N - 1 - 1) := ⟨m - 1, by omega⟩
    have h0 : a ⟨0, hpos⟩ = 0 := by
      have := congrFun hrad ⟨N - 1 - 1, by omega⟩
      simp only [Pi.smul_apply, smul_eq_mul, cubicRadicalVec_apply, hev, ↓reduceIte,
        mul_one] at this
      rw [← this, hlast]
    rw [hrad, h0, zero_smul]

/-- For odd `N`, the radical of `chainForm N` is spanned by `cubicRadicalVec N`. -/
theorem exists_smul_cubicRadicalVec_of_forall_chainForm_eq_zero_of_odd {N : ℕ} (hN : Odd N)
    {a : Fin N → ZMod 3} (ha : ∀ b, chainForm N a b = 0) :
    ∃ c : ZMod 3, a = c • cubicRadicalVec N := by
  obtain ⟨m, hm⟩ := hN
  exact ⟨a ⟨0, by omega⟩, eq_smul_cubicRadicalVec_of_forall_chainForm_eq_zero (by omega) ha⟩

/-! ### Cube root of unity `ω = exp (2 π i / 3)` and the cubic factor set -/

/-- The primitive cube root of unity `ω = exp (2 π i / 3)`, as a unit of `ℂ`. -/
noncomputable def cubeRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi / 3 * Complex.I)) (Complex.exp_ne_zero _)

/-- Coercion of `cubeRootOfUnity` to `ℂ`. -/
theorem cubeRootOfUnity_val :
    (cubeRootOfUnity : ℂ) = Complex.exp (2 * Real.pi / 3 * Complex.I) :=
  (rfl)

/-- Rectangular form `ω = -1 / 2 + (√3 / 2) i`. -/
theorem cubeRootOfUnity_val_eq :
    (cubeRootOfUnity : ℂ) = -(1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℂ) * Complex.I := by
  rw [cubeRootOfUnity_val]
  have harg : (2 * (Real.pi : ℂ) / 3) * Complex.I = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  push_cast
  ring

/-- `ω ^ 3 = 1` in `ℂˣ`. -/
@[simp]
theorem cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, cubeRootOfUnity_val, Units.val_one]
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  push_cast
  ring

/-- `ω ^ 3 = 1` in `ℂ`. -/
@[simp]
theorem cubeRootOfUnity_val_pow_three : (cubeRootOfUnity : ℂ) ^ 3 = 1 := by
  rw [← Units.val_pow_eq_pow_val, cubeRootOfUnity_pow_three, Units.val_one]

/-- `ω ≠ 1` in `ℂ`. -/
theorem cubeRootOfUnity_val_ne_one : (cubeRootOfUnity : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [cubeRootOfUnity_val_eq] at hre
  simp at hre
  norm_num at hre

/-- `ω ≠ 1` in `ℂˣ`. -/
theorem cubeRootOfUnity_ne_one : cubeRootOfUnity ≠ 1 :=
  fun h ↦ cubeRootOfUnity_val_ne_one (congrArg Units.val h)

/-- Minimal polynomial relation `1 + ω + ω² = 0`. -/
@[simp]
theorem one_add_cubeRootOfUnity_add_sq :
    (1 : ℂ) + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 := by
  have hmul : ((cubeRootOfUnity : ℂ) - 1) *
      (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) = 0 := by
    calc
      ((cubeRootOfUnity : ℂ) - 1) *
          (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2)
          = (cubeRootOfUnity : ℂ) ^ 3 - 1 := by ring
      _ = 0 := by rw [cubeRootOfUnity_val_pow_three, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr cubeRootOfUnity_val_ne_one)

/-- `ω⁻¹ = ω²` in `ℂˣ`. -/
theorem cubeRootOfUnity_inv : cubeRootOfUnity⁻¹ = cubeRootOfUnity ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', cubeRootOfUnity_pow_three]

/-- `ω⁻¹ = ω²` in `ℂ`. -/
theorem cubeRootOfUnity_inv_val :
    ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) = (cubeRootOfUnity : ℂ) ^ 2 := by
  rw [cubeRootOfUnity_inv, Units.val_pow_eq_pow_val]

/-- Complex conjugation maps `ω` to `ω⁻¹`. -/
@[simp]
theorem conj_cubeRootOfUnity :
    conj (cubeRootOfUnity : ℂ) = ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by rw [sq, sqrt_three_coe_mul_self]
  rw [cubeRootOfUnity_inv_val, cubeRootOfUnity_val_eq]
  simp only [map_add, map_neg, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring_nf
  rw [Complex.I_sq, hsq]
  ring

/-- `ω ^ x` for an exponent `x : ZMod 3`, read through `ZMod.val`. -/
noncomputable def cubeRootPow (x : ZMod 3) : ℂˣ :=
  cubeRootOfUnity ^ x.val

/-- `cubeRootPow 0 = 1`. -/
@[simp]
theorem cubeRootPow_zero : cubeRootPow 0 = 1 := by
  simp [cubeRootPow]

/-- `cubeRootPow 1 = cubeRootOfUnity`. -/
@[simp]
theorem cubeRootPow_one : cubeRootPow 1 = cubeRootOfUnity := by
  rw [cubeRootPow, ZMod.val_one, pow_one]

/-- `cubeRootPow` converts addition in `ZMod 3` to multiplication in `ℂˣ`. -/
theorem cubeRootPow_add (x y : ZMod 3) :
    cubeRootPow (x + y) = cubeRootPow x * cubeRootPow y := by
  simp only [cubeRootPow, ZMod.val_add]
  rw [← pow_add, ← pow_eq_pow_mod _ cubeRootOfUnity_pow_three]

/-- `cubeRootPow` converts negation in `ZMod 3` to inversion in `ℂˣ`. -/
@[simp]
theorem cubeRootPow_neg (x : ZMod 3) :
    cubeRootPow (-x) = (cubeRootPow x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← cubeRootPow_add, neg_add_cancel, cubeRootPow_zero]

/-- `cubeRootPow` converts subtraction in `ZMod 3` to division in `ℂˣ`. -/
theorem cubeRootPow_sub (x y : ZMod 3) :
    cubeRootPow (x - y) = cubeRootPow x * (cubeRootPow y)⁻¹ := by
  rw [sub_eq_add_neg, cubeRootPow_add, cubeRootPow_neg]

/-- `cubeRootPow 2 = cubeRootOfUnity⁻¹`. -/
@[simp]
theorem cubeRootPow_two : cubeRootPow 2 = cubeRootOfUnity⁻¹ := by
  have h : (2 : ZMod 3) = -1 := by decide
  rw [h, cubeRootPow_neg, cubeRootPow_one]

/-- Complex conjugation maps `cubeRootPow x` to `cubeRootPow (-x)`. -/
@[simp]
theorem conj_cubeRootPow (x : ZMod 3) :
    conj (cubeRootPow x : ℂ) = (cubeRootPow (-x) : ℂ) := by
  -- `fin_cases` on `ZMod 3` produces raw `Fin 3` literals; `change` displays them as numerals.
  fin_cases x
  · change conj (cubeRootPow 0 : ℂ) = (cubeRootPow (-0) : ℂ)
    simp
  · change conj (cubeRootPow 1 : ℂ) = (cubeRootPow (-1) : ℂ)
    simp
  · change conj (cubeRootPow 2 : ℂ) = (cubeRootPow (-2) : ℂ)
    rw [cubeRootPow_two, cubeRootPow_neg, cubeRootPow_two, inv_inv, cubeRootOfUnity_inv_val,
      map_pow, conj_cubeRootOfUnity, ← Units.val_pow_eq_pow_val, inv_pow, ← cubeRootOfUnity_inv,
      inv_inv]

/-- `cubeRootPow x = 1` if and only if `x = 0`. -/
@[simp]
theorem cubeRootPow_eq_one_iff {x : ZMod 3} : cubeRootPow x = 1 ↔ x = 0 := by
  -- `fin_cases` on `ZMod 3` produces raw `Fin 3` literals; `change` displays them as numerals.
  fin_cases x
  · change cubeRootPow 0 = 1 ↔ (0 : ZMod 3) = 0
    simp
  · change cubeRootPow 1 = 1 ↔ (1 : ZMod 3) = 0
    simp [cubeRootOfUnity_ne_one]
  · change cubeRootPow 2 = 1 ↔ (2 : ZMod 3) = 0
    simp [cubeRootOfUnity_ne_one, show (2 : ZMod 3) ≠ 0 by decide]

/-- Every power `cubeRootPow x` satisfies `(cubeRootPow x) ^ 3 = 1`. -/
@[simp]
theorem cubeRootPow_pow_three (x : ZMod 3) : cubeRootPow x ^ 3 = 1 := by
  rw [cubeRootPow, pow_right_comm, cubeRootOfUnity_pow_three, one_pow]

/-- `cubeRootPow` is injective. -/
theorem cubeRootPow_injective : Function.Injective cubeRootPow := by
  intro x y hxy
  have h0 : cubeRootPow (x - y) = 1 := by rw [cubeRootPow_sub, hxy, mul_inv_cancel]
  exact sub_eq_zero.mp (cubeRootPow_eq_one_iff.mp h0)

/-- The normalized factor set `α(a, b) = ω ^ (2 * B(a, b))` of the cubic quantum torus `G_N`. -/
noncomputable def cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  cubeRootPow (2 * chainForm N a.toAdd b.toAdd)

/-- Unfolding `cubicFactor`. -/
theorem cubicFactor_def (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) :=
  (rfl)

/-- `cubicFactor N` is a normalized factor set on `Multiplicative (Fin N → ZMod 3)`. -/
instance cubicFactor_isFactorSet (N : ℕ) : IsFactorSet (cubicFactor N) where
  cocycle g h j := by
    simp only [cubicFactor_def, toAdd_mul, ← cubeRootPow_add]
    congr 1
    rw [chainForm_add_left, chainForm_add_right]
    ring
  one_left g := by
    simp [cubicFactor_def]

/-- `cubicFactor N` is trivial on the diagonal: `α(a, a) = 1`. -/
@[simp]
theorem cubicFactor_self (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a = 1 := by
  simp [cubicFactor_def]

/-- `cubicFactor N` is trivial on inverse pairs: `α(a, a⁻¹) = 1`. -/
@[simp]
theorem cubicFactor_inv_right (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a⁻¹ = 1 := by
  simp [cubicFactor_def]

/-- `cubicFactor N` is trivial on inverse pairs: `α(a⁻¹, a) = 1`. -/
@[simp]
theorem cubicFactor_inv_left (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ a = 1 := by
  simp [cubicFactor_def]

/-- Swapping arguments inverts `cubicFactor N`: `α(b, a) = α(a, b)⁻¹`. -/
theorem cubicFactor_swap (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N b a = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor_def, cubicFactor_def, chainForm_swap, mul_neg, cubeRootPow_neg]

/-- `cubicFactor N` is invariant under simultaneous inversion: `α(a⁻¹, b⁻¹) = α(a, b)`. -/
@[simp]
theorem cubicFactor_inv_inv (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b⁻¹ = cubicFactor N a b := by
  simp [cubicFactor_def]

/-- Complex conjugation swaps the arguments of `cubicFactor N`. -/
@[simp]
theorem conj_cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    conj (cubicFactor N a b : ℂ) = (cubicFactor N b a : ℂ) := by
  rw [cubicFactor_def, conj_cubeRootPow, cubicFactor_def, chainForm_swap, mul_neg, neg_neg]

/-- The commutator cocycle ratio `α(a, b) * α(b, a)⁻¹ = ω ^ B(a, b)`. -/
theorem cubicFactor_mul_inv_swap (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b * (cubicFactor N b a)⁻¹ = cubeRootPow (chainForm N a.toAdd b.toAdd) := by
  rw [cubicFactor_swap N a b, inv_inv, cubicFactor_def, ← cubeRootPow_add]
  congr 1
  have h4 : (2 : ZMod 3) + 2 = 1 := by decide
  rw [← add_mul, h4, one_mul]

/-! ### The cubic quantum torus `CubicTorus N` and its Weyl basis -/

/-- The **cubic quantum torus** `G_N`: the twisted monoid algebra of `(ZMod 3) ^ N` over `ℂ` for
the factor set `cubicFactor N`, of complex dimension `3 ^ N`. -/
noncomputable abbrev CubicTorus (N : ℕ) :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- The Weyl basis element `W(a) = TwistedMonoidAlgebra.of a` of `CubicTorus N`. -/
noncomputable def weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  TwistedMonoidAlgebra.of a

/-- Unfolding `weyl` as `TwistedMonoidAlgebra.of`. -/
theorem weyl_def (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a = TwistedMonoidAlgebra.of a :=
  (rfl)

/-- The Weyl basis `a ↦ weyl N a` of `CubicTorus N`. -/
noncomputable def weylBasis (N : ℕ) :
    Module.Basis (Multiplicative (Fin N → ZMod 3)) ℂ (CubicTorus N) :=
  TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- `weylBasis N` evaluates to `weyl N`. -/
@[simp]
theorem weylBasis_apply (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weylBasis N a = weyl N a :=
  TwistedMonoidAlgebra.basis_apply ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N) a

/-- `W(1) = 1`. -/
@[simp]
theorem weyl_one (N : ℕ) : weyl N 1 = 1 :=
  TwistedMonoidAlgebra.of_one

/-- Multiplication table of the Weyl basis: `W(a) * W(b) = α(a, b) • W(a * b)`. -/
@[simp]
theorem weyl_mul_weyl (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b = (cubicFactor N a b : ℂ) • weyl N (a * b) :=
  TwistedMonoidAlgebra.of_mul_of a b

/-- `W(a) * W(a⁻¹) = 1`. -/
theorem weyl_mul_weyl_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N a⁻¹ = 1 := by
  simp

/-- `W(a⁻¹) * W(a) = 1`. -/
theorem weyl_inv_mul_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a⁻¹ * weyl N a = 1 := by
  simp

/-- Every Weyl basis element satisfies `W(a) ^ 2 = W(a⁻¹)` (since `2 = -1` in `ZMod 3`). -/
@[simp]
theorem weyl_sq (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 2 = weyl N a⁻¹ := by
  have hmul : a * a = a⁻¹ := by
    apply Multiplicative.toAdd.injective
    ext i
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
    generalize a.toAdd i = t
    fin_cases t <;> decide
  rw [sq, weyl_mul_weyl, cubicFactor_self, Units.val_one, one_smul, hmul]

/-- Every Weyl basis element has cube `1`: `W(a) ^ 3 = 1`. -/
@[simp]
theorem weyl_pow_three (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 3 = 1 := by
  rw [pow_succ, weyl_sq, weyl_inv_mul_weyl]

/-- Commutation relation of Weyl basis elements:
`W(a) * W(b) = ω ^ B(a, b) • (W(b) * W(a))`. -/
theorem weyl_mul_weyl_comm (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b =
      (cubeRootPow (chainForm N a.toAdd b.toAdd) : ℂ) • (weyl N b * weyl N a) := by
  rw [weyl_mul_weyl, weyl_mul_weyl, smul_smul, mul_comm b a, ← Units.val_mul,
    ← cubicFactor_mul_inv_swap, mul_assoc, inv_mul_cancel, mul_one]

/-- `CubicTorus N` is finite-dimensional over `ℂ`. -/
instance (N : ℕ) : Module.Finite ℂ (CubicTorus N) :=
  Module.Finite.of_basis (weylBasis N)

/-- The complex dimension of `CubicTorus N` is `3 ^ N`. -/
@[simp]
theorem finrank_cubicTorus (N : ℕ) :
    Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [TwistedMonoidAlgebra.finrank_eq_natCard, Nat.card_eq_fintype_card]
  simp [Fintype.card_pi]

/-! ### The analytic adjoint and scalar-part trace on `CubicTorus N` -/

/-- The **analytic adjoint** `x ↦ x†` on `CubicTorus N`: the conjugate-linear, product-reversing
involution sending each Weyl basis element `W(a)` to `W(a⁻¹)`. -/
noncomputable def cubicAdjoint (N : ℕ) : CubicTorus N →ₗ⋆[ℂ] CubicTorus N where
  toFun x := ∑ a, conj ((weylBasis N).repr x a) • weyl N a⁻¹
  map_add' x y := by
    simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z x := by
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ← smul_smul, Finset.smul_sum]

/-- `cubicAdjoint` sends each Weyl basis element `W(a)` to `W(a⁻¹)`. -/
@[simp]
theorem cubicAdjoint_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicAdjoint N (weyl N a) = weyl N a⁻¹ := by
  dsimp only [cubicAdjoint, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← weylBasis_apply N a, Finset.sum_eq_single a]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, one_smul]
  · intro b _ hba
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne hba, map_zero, zero_smul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Coordinates of `cubicAdjoint N x` in the Weyl basis: `(x†)_a = conj (x_{a⁻¹})`. -/
@[simp]
theorem weylBasis_repr_cubicAdjoint (N : ℕ) (x : CubicTorus N)
    (a : Multiplicative (Fin N → ZMod 3)) :
    (weylBasis N).repr (cubicAdjoint N x) a = conj ((weylBasis N).repr x a⁻¹) := by
  let coord : CubicTorus N →ₗ[ℂ] ℂ :=
    (Finsupp.lapply a).comp (weylBasis N).repr.toLinearMap
  change coord (cubicAdjoint N x) = conj ((weylBasis N).repr x a⁻¹)
  dsimp only [cubicAdjoint, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single a⁻¹]
  · change conj ((weylBasis N).repr x a⁻¹) * (weylBasis N).repr (weyl N a⁻¹⁻¹) a =
      conj ((weylBasis N).repr x a⁻¹)
    rw [inv_inv, ← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
  · intro b _ hba
    change conj ((weylBasis N).repr x b) * (weylBasis N).repr (weyl N b⁻¹) a = 0
    have hne : a ≠ b⁻¹ := fun h ↦ hba (by rw [h, inv_inv])
    rw [← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne, mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a⁻¹) ha

/-- `cubicAdjoint` fixes `1`. -/
@[simp]
theorem cubicAdjoint_one (N : ℕ) : cubicAdjoint N 1 = 1 := by
  rw [← weyl_one, cubicAdjoint_weyl, inv_one, weyl_one]

/-- `cubicAdjoint` acts on scalars by complex conjugation. -/
@[simp]
theorem cubicAdjoint_algebraMap (N : ℕ) (z : ℂ) :
    cubicAdjoint N (algebraMap ℂ (CubicTorus N) z) =
      algebraMap ℂ (CubicTorus N) (conj z) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, cubicAdjoint_one,
    Algebra.algebraMap_eq_smul_one]

/-- `cubicAdjoint` is involutive. -/
@[simp]
theorem cubicAdjoint_cubicAdjoint (N : ℕ) (x : CubicTorus N) :
    cubicAdjoint N (cubicAdjoint N x) = x := by
  apply (weylBasis N).repr.injective
  ext a
  simp

/-- `cubicAdjoint` reverses products. -/
@[simp]
theorem cubicAdjoint_mul (N : ℕ) (x y : CubicTorus N) :
    cubicAdjoint N (x * y) = cubicAdjoint N y * cubicAdjoint N x := by
  rw [← (weylBasis N).sum_repr x, ← (weylBasis N).sum_repr y]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_smul_comm, map_smulₛₗ,
    weylBasis_apply, weyl_mul_weyl, cubicAdjoint_weyl]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  rw [smul_smul, smul_smul, map_mul, conj_cubicFactor, mul_inv_rev, mul_comm (conj _),
    cubicFactor_inv_inv]

/-- The **scalar-part trace** `s_N : CubicTorus N →ₗ[ℂ] ℂ`, extracting the coefficient of
`W(1) = 1` in the Weyl basis. -/
noncomputable def cubicScalarCoefficient (N : ℕ) : CubicTorus N →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (1 : Multiplicative (Fin N → ZMod 3))).comp (weylBasis N).repr.toLinearMap

/-- Evaluation formula for `cubicScalarCoefficient N`. -/
theorem cubicScalarCoefficient_apply (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N x = (weylBasis N).repr x 1 :=
  (rfl)

/-- `s_N (W(a)) = 1` if `a = 1`, and `0` otherwise. -/
@[simp]
theorem cubicScalarCoefficient_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicScalarCoefficient N (weyl N a) = if a = 1 then 1 else 0 := by
  rw [cubicScalarCoefficient_apply, ← weylBasis_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

/-- `s_N (1) = 1`. -/
@[simp]
theorem cubicScalarCoefficient_one (N : ℕ) :
    cubicScalarCoefficient N 1 = 1 := by
  rw [← weyl_one, cubicScalarCoefficient_weyl, ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]

/-- Basis-coordinate formula for `s_N (x * y)`: `∑ a, x_a * y_{a⁻¹}`. -/
theorem cubicScalarCoefficient_mul (N : ℕ) (x y : CubicTorus N) :
    cubicScalarCoefficient N (x * y) =
      ∑ a, (weylBasis N).repr x a * (weylBasis N).repr y a⁻¹ := by
  conv_lhs => rw [← (weylBasis N).sum_repr x, ← (weylBasis N).sum_repr y]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum, smul_mul_smul_comm, map_smul, weylBasis_apply,
    weyl_mul_weyl, cubicScalarCoefficient_weyl, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single a⁻¹]
  · simp
  · intro b _ hba
    have hne : a * b ≠ 1 := fun h ↦ hba (eq_inv_of_mul_eq_one_right h)
    simp [hne]
  · intro ha
    exact absurd (Finset.mem_univ a⁻¹) ha

/-- `cubicScalarCoefficient N` is tracial: `s_N (x * y) = s_N (y * x)`. -/
theorem cubicScalarCoefficient_mul_comm (N : ℕ) (x y : CubicTorus N) :
    cubicScalarCoefficient N (x * y) = cubicScalarCoefficient N (y * x) := by
  rw [cubicScalarCoefficient_mul, cubicScalarCoefficient_mul]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun a ↦ ?_
  simp [mul_comm]

/-- `cubicScalarCoefficient N` intertwines `cubicAdjoint N` with complex conjugation. -/
@[simp]
theorem cubicScalarCoefficient_cubicAdjoint (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicAdjoint N x) = conj (cubicScalarCoefficient N x) := by
  simp [cubicScalarCoefficient_apply]

/-- **Sesquilinear Parseval identity** for `cubicScalarCoefficient N`:
`s_N (x† * y) = ∑ a, conj x_a * y_a`. -/
theorem cubicScalarCoefficient_cubicAdjoint_mul (N : ℕ) (x y : CubicTorus N) :
    cubicScalarCoefficient N (cubicAdjoint N x * y) =
      ((weylBasis N).repr x).sum fun a z ↦ conj z * (weylBasis N).repr y a := by
  rw [cubicScalarCoefficient_mul]
  trans ∑ a, conj ((weylBasis N).repr x a) * (weylBasis N).repr y a
  · refine Fintype.sum_equiv (Equiv.inv _) _ _ fun a ↦ ?_
    simp
  · rw [Finsupp.sum_fintype]
    intro a
    simp

/-- **Quadratic Parseval identity** for `cubicScalarCoefficient N`:
`s_N (x† * x) = ∑ a, |x_a|²`. -/
theorem cubicScalarCoefficient_cubicAdjoint_mul_self (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicAdjoint N x * x) =
      ((((weylBasis N).repr x).sum fun _ z ↦ Complex.normSq z) : ℝ) := by
  rw [cubicScalarCoefficient_cubicAdjoint_mul]
  simpa using (Finsupp.ofReal_sum_normSq_mul ((weylBasis N).repr x) 1).symm

/-- **Positivity of `cubicScalarCoefficient N`**: `0 ≤ s_N (x† * x)` for every `x`. -/
theorem cubicScalarCoefficient_cubicAdjoint_mul_self_nonneg (N : ℕ) (x : CubicTorus N) :
    0 ≤ cubicScalarCoefficient N (cubicAdjoint N x * x) := by
  rw [cubicScalarCoefficient_cubicAdjoint_mul_self, Complex.zero_le_real]
  simpa using Finsupp.sum_normSq_mul_nonneg ((weylBasis N).repr x) (w := 1) fun _ ↦ zero_le_one

/-- **Faithfulness of `cubicScalarCoefficient N`**: `s_N (x† * x) = 0` if and only if `x = 0`. -/
@[simp]
theorem cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff (N : ℕ) {x : CubicTorus N} :
    cubicScalarCoefficient N (cubicAdjoint N x * x) = 0 ↔ x = 0 := by
  rw [cubicScalarCoefficient_cubicAdjoint_mul_self, Complex.ofReal_eq_zero]
  constructor
  · intro h
    let w : Multiplicative (Fin N → ZMod 3) → ℝ := fun _ ↦ 1
    have h1 : (((weylBasis N).repr x).sum fun a z ↦ Complex.normSq z * w a) = 0 := by
      simpa [w] using h
    rw [Finsupp.sum_normSq_mul_eq_zero_iff _ fun _ ↦ zero_le_one] at h1
    apply (weylBasis N).repr.injective
    ext a
    rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact h1 a one_ne_zero
  · rintro rfl
    rw [LinearEquiv.map_zero, Finsupp.sum_zero_index]

/-! ### The inversion automorphism `cubicInversion` and fixed subalgebra `cubicFixed` -/

/-- The **inversion automorphism** `θ_N : W(a) ↦ W(a⁻¹)` of `CubicTorus N`. -/
noncomputable def cubicInversion (N : ℕ) : CubicTorus N →ₐ[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.lift (fun a ↦ weyl N a⁻¹) (by simp) fun g h ↦ by
    rw [weyl_mul_weyl, cubicFactor_inv_inv, mul_inv]

/-- Action of `cubicInversion N` on the Weyl basis. -/
@[simp]
theorem cubicInversion_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicInversion N (weyl N a) = weyl N a⁻¹ :=
  TwistedMonoidAlgebra.lift_of _ _ _ a

/-- `cubicInversion N` is an involution. -/
@[simp]
theorem cubicInversion_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x := by
  have h : (cubicInversion N).comp (cubicInversion N) = AlgHom.id ℂ (CubicTorus N) := by
    apply TwistedMonoidAlgebra.algHom_ext
    intro a
    change cubicInversion N (cubicInversion N (weyl N a)) = weyl N a
    simp
  exact AlgHom.congr_fun h x

/-- `cubicInversion N` commutes with `cubicAdjoint N`. -/
@[simp]
theorem cubicInversion_cubicAdjoint (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicAdjoint N x) = cubicAdjoint N (cubicInversion N x) := by
  conv_lhs => rw [← (weylBasis N).sum_repr x]
  conv_rhs => rw [← (weylBasis N).sum_repr x]
  simp [map_sum, map_smul, map_smulₛₗ, weylBasis_apply]

/-- `cubicInversion N` preserves `cubicScalarCoefficient N`. -/
@[simp]
theorem cubicScalarCoefficient_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicInversion N x) = cubicScalarCoefficient N x := by
  conv_lhs => rw [← (weylBasis N).sum_repr x]
  conv_rhs => rw [← (weylBasis N).sum_repr x]
  simp [map_sum, map_smul, weylBasis_apply]

/-- The **inversion-fixed subalgebra** `C_N = {x ∈ G_N : θ_N x = x}` of `CubicTorus N`. -/
noncomputable def cubicFixed (N : ℕ) : Subalgebra ℂ (CubicTorus N) :=
  AlgHom.equalizer (cubicInversion N) (AlgHom.id ℂ (CubicTorus N))

/-- Membership in `cubicFixed N` is invariance under `cubicInversion N`. -/
@[simp]
theorem mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    x ∈ cubicFixed N ↔ cubicInversion N x = x :=
  Iff.rfl

/-- Every symmetric sum `W(a) + W(a⁻¹)` lies in `cubicFixed N`. -/
theorem weyl_add_weyl_inv_mem_cubicFixed (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a + weyl N a⁻¹ ∈ cubicFixed N := by
  rw [mem_cubicFixed_iff, map_add, cubicInversion_weyl, cubicInversion_weyl, inv_inv, add_comm]

/-- `cubicFixed N` is stable under `cubicAdjoint N`. -/
theorem cubicAdjoint_mem_cubicFixed (N : ℕ) {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicAdjoint N x ∈ cubicFixed N := by
  rw [mem_cubicFixed_iff] at hx ⊢
  rw [cubicInversion_cubicAdjoint, hx]

/-- `x†` lies in `cubicFixed N` if and only if `x` does. -/
theorem cubicAdjoint_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicAdjoint N x ∈ cubicFixed N ↔ x ∈ cubicFixed N :=
  ⟨fun h ↦ cubicAdjoint_cubicAdjoint N x ▸ cubicAdjoint_mem_cubicFixed N h,
    cubicAdjoint_mem_cubicFixed N⟩

/-- Restriction of `cubicAdjoint N` to the inversion-fixed subalgebra `cubicFixed N`. -/
noncomputable def cubicFixedAdjoint (N : ℕ) : cubicFixed N →ₗ⋆[ℂ] cubicFixed N where
  toFun x := ⟨cubicAdjoint N x, cubicAdjoint_mem_cubicFixed N x.2⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

/-- Coercing `cubicFixedAdjoint N x` to `CubicTorus N` yields `cubicAdjoint N x`. -/
@[simp]
theorem coe_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    (cubicFixedAdjoint N x : CubicTorus N) = cubicAdjoint N x :=
  (rfl)

/-- `cubicFixedAdjoint` fixes `1`. -/
@[simp]
theorem cubicFixedAdjoint_one (N : ℕ) : cubicFixedAdjoint N 1 = 1 :=
  Subtype.ext (cubicAdjoint_one N)

/-- `cubicFixedAdjoint` reverses products. -/
@[simp]
theorem cubicFixedAdjoint_mul (N : ℕ) (x y : cubicFixed N) :
    cubicFixedAdjoint N (x * y) = cubicFixedAdjoint N y * cubicFixedAdjoint N x :=
  Subtype.ext (cubicAdjoint_mul N x y)

/-- `cubicFixedAdjoint` is involutive. -/
@[simp]
theorem cubicFixedAdjoint_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    cubicFixedAdjoint N (cubicFixedAdjoint N x) = x :=
  Subtype.ext (cubicAdjoint_cubicAdjoint N x)

/-- Nondegeneracy of the scalar-trace multiplication pairing on `cubicFixed N`. -/
theorem forall_cubicFixed_cubicScalarCoefficient_mul_eq_zero_iff (N : ℕ) {x : cubicFixed N} :
    (∀ y : cubicFixed N, cubicScalarCoefficient N ((x : CubicTorus N) * y) = 0) ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h y ↦ by simp [h]⟩
  have hzero := h (cubicFixedAdjoint N x)
  rw [coe_cubicFixedAdjoint, cubicScalarCoefficient_mul_comm,
    cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff] at hzero
  exact Subtype.ext hzero

/-- Coordinates of `cubicInversion N x` in the Weyl basis: `(θ_N x)_a = x_{a⁻¹}`. -/
@[simp]
theorem weylBasis_repr_cubicInversion (N : ℕ) (x : CubicTorus N)
    (a : Multiplicative (Fin N → ZMod 3)) :
    (weylBasis N).repr (cubicInversion N x) a = (weylBasis N).repr x a⁻¹ := by
  let coord : CubicTorus N →ₗ[ℂ] ℂ :=
    (Finsupp.lapply a).comp (weylBasis N).repr.toLinearMap
  change coord (cubicInversion N x) = (weylBasis N).repr x a⁻¹
  conv_lhs => rw [← (weylBasis N).sum_repr x]
  simp only [map_sum, map_smul, weylBasis_apply, cubicInversion_weyl, smul_eq_mul]
  rw [Finset.sum_eq_single a⁻¹]
  · change (weylBasis N).repr x a⁻¹ * (weylBasis N).repr (weyl N a⁻¹⁻¹) a =
      (weylBasis N).repr x a⁻¹
    rw [inv_inv, ← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
  · intro b _ hba
    change (weylBasis N).repr x b * (weylBasis N).repr (weyl N b⁻¹) a = 0
    have hne : a ≠ b⁻¹ := fun h ↦ hba (by rw [h, inv_inv])
    rw [← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne, mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a⁻¹) ha

private theorem inv_eq_self_iff_eq_one {N : ℕ} (a : Multiplicative (Fin N → ZMod 3)) :
    a⁻¹ = a ↔ a = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  apply Multiplicative.toAdd.injective
  ext i
  have hi := congrFun (congrArg Multiplicative.toAdd h) i
  simp only [toAdd_inv, Pi.neg_apply, toAdd_one, Pi.zero_apply] at hi ⊢
  have h2 : (2 : ZMod 3) * a.toAdd i = 0 := by
    rw [two_mul]
    exact add_eq_zero_iff_neg_eq.mpr hi
  calc
    a.toAdd i = ((2 : ZMod 3) * 2) * a.toAdd i := by
      rw [show (2 : ZMod 3) * 2 = 1 by decide, one_mul]
    _ = 2 * (2 * a.toAdd i) := by ring
    _ = 0 := by rw [h2, mul_zero]

/-- The complex dimension of the inversion-fixed subalgebra `cubicFixed N` is `(3 ^ N + 1) / 2`. -/
@[simp]
theorem finrank_cubicFixed (N : ℕ) :
    Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  -- 1. Build the projection `P = 2⁻¹ • (id + invLin)` onto the inversion-fixed subspace `q`.
  let G := Multiplicative (Fin N → ZMod 3)
  let invLin : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f a ↦ f a⁻¹
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let P : (G → ℂ) →ₗ[ℂ] (G → ℂ) := (2 : ℂ)⁻¹ • (LinearMap.id + invLin)
  let q : Submodule ℂ (G → ℂ) :=
    { carrier := {f | ∀ a, f a⁻¹ = f a}
      add_mem' := fun hx hy a ↦ by simp [hx a, hy a]
      zero_mem' := fun _ ↦ rfl
      smul_mem' := fun c _ hx a ↦ by simp [hx a] }
  have hP : LinearMap.IsProj q P := by
    refine ⟨fun f a ↦ ?_, fun f hf ↦ ?_⟩
    · simp only [P, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, invLin,
        LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply, inv_inv, add_comm]
    · ext a
      simp only [P, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, invLin,
        LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply, hf a, smul_eq_mul]
      ring
  -- 2. Compute `trace invLin = 1` in the standard basis, hence `trace P = (3 ^ N + 1) / 2`.
  have htr_inv : LinearMap.trace ℂ (G → ℂ) invLin = 1 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace]
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    rw [Finset.sum_eq_single (1 : G)]
    · simp [invLin]
    · intro a _ ha
      have hne : a⁻¹ ≠ a := fun h ↦ ha ((inv_eq_self_iff_eq_one a).mp h)
      simpa [invLin] using Pi.single_eq_of_ne (M := fun _ : G ↦ ℂ) hne (1 : ℂ)
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  have hcard : Module.finrank ℂ (G → ℂ) = 3 ^ N := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [G, Fintype.card_pi]
  have htr : LinearMap.trace ℂ (G → ℂ) P = (Module.finrank ℂ q : ℂ) := hP.trace
  have htr2 : LinearMap.trace ℂ (G → ℂ) P = (2 : ℂ)⁻¹ * ((3 ^ N : ℂ) + 1) := by
    simp only [P, map_smul, map_add, LinearMap.trace_id, hcard, htr_inv, smul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
  -- 3. Transport along the linear equivalence `cubicFixed N ≃ₗ[ℂ] q` to deduce `finrank`.
  have hequiv : cubicFixed N ≃ₗ[ℂ] q :=
    { toFun := fun x ↦ ⟨fun a ↦ (weylBasis N).repr x.1 a, fun a ↦ by
        dsimp only
        rw [← weylBasis_repr_cubicInversion, (mem_cubicFixed_iff N).mp x.2]⟩
      invFun := fun f ↦ ⟨(weylBasis N).equivFun.symm f.1, by
        rw [mem_cubicFixed_iff]
        apply (weylBasis N).repr.injective
        ext a
        rw [weylBasis_repr_cubicInversion]
        have hrepr (b : G) : (weylBasis N).repr ((weylBasis N).equivFun.symm f.1) b = f.1 b :=
          congrFun ((weylBasis N).equivFun.apply_symm_apply f.1) b
        rw [hrepr, hrepr]
        exact f.2 a⟩
      left_inv := fun x ↦ Subtype.ext <| by
        exact (weylBasis N).equivFun.symm_apply_apply x.1
      right_inv := fun f ↦ Subtype.ext <| by
        ext a
        exact congrFun ((weylBasis N).equivFun.apply_symm_apply f.1) a
      map_add' := fun x y ↦ Subtype.ext <| by ext a; simp
      map_smul' := fun c x ↦ Subtype.ext <| by ext a; simp }
  have hdim : Module.finrank ℂ (cubicFixed N) = Module.finrank ℂ q :=
    hequiv.finrank_eq
  have hcast : (2 * Module.finrank ℂ (cubicFixed N) : ℂ) = ((3 ^ N + 1 : ℕ) : ℂ) := by
    have h := htr.symm.trans htr2
    rw [← hdim] at h
    push_cast
    linear_combination 2 * h
  have hnat : 2 * Module.finrank ℂ (cubicFixed N) = 3 ^ N + 1 := by
    exact_mod_cast hcast
  omega

/-! ### Site unitaries, projections, and the Temperley–Lieb comparison homomorphism -/

/-- The `j`-th **site unitary** `U_j = W(e_j)` of `CubicTorus N`. -/
noncomputable def cubicSite (N : ℕ) (j : Fin N) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd (Pi.single j 1))

/-- Unfolding `cubicSite`. -/
theorem cubicSite_def (N : ℕ) (j : Fin N) :
    cubicSite N j = weyl N (Multiplicative.ofAdd (Pi.single j 1)) :=
  (rfl)

/-- Every site unitary has cube `1`: `U_j ^ 3 = 1`. -/
@[simp]
theorem cubicSite_pow_three (N : ℕ) (j : Fin N) : cubicSite N j ^ 3 = 1 :=
  weyl_pow_three N _

/-- `U_j ^ 2 = W(-e_j)`. -/
theorem cubicSite_sq (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 = weyl N (Multiplicative.ofAdd (Pi.single j 1))⁻¹ :=
  weyl_sq N _

/-- `U_j * U_j ^ 2 = 1`. -/
@[simp]
theorem cubicSite_mul_sq (N : ℕ) (j : Fin N) : cubicSite N j * cubicSite N j ^ 2 = 1 := by
  rw [← pow_succ', cubicSite_pow_three]

/-- `U_j ^ 2 * U_j = 1`. -/
@[simp]
theorem cubicSite_sq_mul (N : ℕ) (j : Fin N) : cubicSite N j ^ 2 * cubicSite N j = 1 := by
  rw [← pow_succ, cubicSite_pow_three]

/-- `U_j ^ 2 * U_j ^ 2 = U_j`. -/
@[simp]
theorem cubicSite_sq_mul_sq (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 * cubicSite N j ^ 2 = cubicSite N j := by
  calc
    cubicSite N j ^ 2 * cubicSite N j ^ 2
        = cubicSite N j ^ 3 * cubicSite N j := by rw [← pow_add, ← pow_succ]
    _ = cubicSite N j := by rw [cubicSite_pow_three, one_mul]

/-- The analytic adjoint sends `U_j` to `U_j ^ 2`. -/
@[simp]
theorem cubicAdjoint_cubicSite (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicSite N j) = cubicSite N j ^ 2 := by
  conv_lhs => rw [cubicSite_def]
  rw [cubicAdjoint_weyl, ← cubicSite_sq]

/-- The inversion sends `U_j` to `U_j ^ 2`. -/
@[simp]
theorem cubicInversion_cubicSite (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  conv_lhs => rw [cubicSite_def]
  rw [cubicInversion_weyl, ← cubicSite_sq]

/-- Scalar part of a site unitary is `0`. -/
@[simp]
theorem cubicScalarCoefficient_cubicSite (N : ℕ) (j : Fin N) :
    cubicScalarCoefficient N (cubicSite N j) = 0 := by
  rw [cubicSite_def, cubicScalarCoefficient_weyl]
  refine ite_eq_right_iff.mpr fun h ↦ ?_
  have h1 := congrFun (congrArg Multiplicative.toAdd h) j
  simp at h1

/-- Scalar part of the square of a site unitary is `0`. -/
@[simp]
theorem cubicScalarCoefficient_cubicSite_sq (N : ℕ) (j : Fin N) :
    cubicScalarCoefficient N (cubicSite N j ^ 2) = 0 := by
  rw [cubicSite_sq, cubicScalarCoefficient_weyl]
  refine ite_eq_right_iff.mpr fun h ↦ ?_
  have h1 := congrFun (congrArg Multiplicative.toAdd h) j
  simp at h1

/-- Adjacent site unitaries satisfy `U_i * U_j = ω • (U_j * U_i)` when `i + 1 = j`. -/
theorem cubicSite_mul_cubicSite_of_succ {N : ℕ} {i j : Fin N} (h : (i : ℕ) + 1 = j) :
    cubicSite N i * cubicSite N j =
      (cubeRootOfUnity : ℂ) • (cubicSite N j * cubicSite N i) := by
  rw [cubicSite_def, cubicSite_def, weyl_mul_weyl_comm]
  simp [toAdd_ofAdd, chainForm_single_single, h]

/-- Adjacent site unitaries satisfy `U_i * U_j = ω⁻¹ • (U_j * U_i)` when `j + 1 = i`. -/
theorem cubicSite_mul_cubicSite_of_pred {N : ℕ} {i j : Fin N} (h : (j : ℕ) + 1 = i) :
    cubicSite N i * cubicSite N j =
      ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) • (cubicSite N j * cubicSite N i) := by
  have hne : ¬ (i : ℕ) + 1 = j := by omega
  rw [cubicSite_def, cubicSite_def, weyl_mul_weyl_comm]
  simp [toAdd_ofAdd, chainForm_single_single, hne, h]

/-- Site unitaries at distance at least two commute. -/
theorem commute_cubicSite {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cubicSite N i) (cubicSite N j) := by
  have h1 : ¬ (i : ℕ) + 1 = j := by omega
  have h2 : ¬ (j : ℕ) + 1 = i := by omega
  unfold Commute SemiconjBy
  rw [cubicSite_def, cubicSite_def, weyl_mul_weyl_comm]
  simp [toAdd_ofAdd, chainForm_single_single, h1, h2]

/-- The `j`-th **cubic projection** `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)` in `CubicTorus N`. -/
noncomputable def cubicProjection (N : ℕ) (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)

/-- Unfolding `cubicProjection`. -/
theorem cubicProjection_def (N : ℕ) (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) :=
  (rfl)

/-- Every cubic projection lies in the inversion-fixed subalgebra `cubicFixed N`. -/
theorem cubicProjection_mem_cubicFixed (N : ℕ) (j : Fin N) :
    cubicProjection N j ∈ cubicFixed N := by
  rw [mem_cubicFixed_iff, cubicProjection_def]
  simp only [map_smul, map_add, map_one, map_pow, cubicInversion_cubicSite]
  have h4 : (cubicSite N j ^ 2) ^ 2 = cubicSite N j := by
    rw [sq, cubicSite_sq_mul_sq]
  rw [h4]
  congr 1
  abel

/-- Every cubic projection is self-adjoint for `cubicAdjoint N`. -/
@[simp]
theorem cubicAdjoint_cubicProjection (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicProjection N j) = cubicProjection N j := by
  rw [cubicProjection_def, map_smulₛₗ, map_add, map_add, cubicAdjoint_one, cubicAdjoint_cubicSite,
    sq, cubicAdjoint_mul, cubicAdjoint_cubicSite, cubicSite_sq_mul_sq]
  simp only [map_inv₀, map_ofNat]
  congr 1
  abel

/-- Every cubic projection has scalar part `3⁻¹`. -/
@[simp]
theorem cubicScalarCoefficient_cubicProjection (N : ℕ) (j : Fin N) :
    cubicScalarCoefficient N (cubicProjection N j) = (3 : ℂ)⁻¹ := by
  simp [cubicProjection_def]

/-- `U_j` absorbs `p_j` on the left: `U_j * p_j = p_j`. -/
@[simp]
theorem cubicSite_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j * cubicProjection N j = cubicProjection N j := by
  rw [cubicProjection_def, mul_smul_comm]
  congr 1
  calc
    cubicSite N j * (1 + cubicSite N j + cubicSite N j ^ 2)
        = cubicSite N j + cubicSite N j ^ 2 + cubicSite N j ^ 3 := by
          simp only [mul_add, mul_one, ← sq, ← pow_succ']
    _ = 1 + cubicSite N j + cubicSite N j ^ 2 := by rw [cubicSite_pow_three]; abel

/-- `U_j` absorbs `p_j` on the right: `p_j * U_j = p_j`. -/
@[simp]
theorem cubicProjection_mul_cubicSite (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicSite N j = cubicProjection N j := by
  rw [cubicProjection_def, smul_mul_assoc]
  congr 1
  calc
    (1 + cubicSite N j + cubicSite N j ^ 2) * cubicSite N j
        = cubicSite N j + cubicSite N j ^ 2 + cubicSite N j ^ 3 := by
          simp only [add_mul, one_mul, ← sq, ← pow_succ]
    _ = 1 + cubicSite N j + cubicSite N j ^ 2 := by rw [cubicSite_pow_three]; abel

/-- Every cubic projection is idempotent: `p_j * p_j = p_j`. -/
@[simp]
theorem cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  calc
    cubicProjection N j * cubicProjection N j
        = (3 : ℂ)⁻¹ • (cubicProjection N j +
            cubicSite N j * cubicProjection N j +
            cubicSite N j * (cubicSite N j * cubicProjection N j)) := by
          nth_rw 1 [cubicProjection_def]
          simp only [smul_mul_assoc, add_mul, one_mul, sq, mul_assoc]
    _ = (3 : ℂ)⁻¹ • ((3 : ℂ) • cubicProjection N j) := by
          simp only [cubicSite_mul_cubicProjection]
          module
    _ = cubicProjection N j := by
          rw [smul_smul]
          norm_num

/-- If `U_i` `ξ`-commutes with `x` for a primitive cube root `ξ` (`1 + ξ + ξ ^ 2 = 0`), then
`p_i * x * p_i = 0`. -/
private theorem cubicProjection_mul_mul_cubicProjection_eq_zero {N : ℕ} {i : Fin N}
    {x : CubicTorus N} {ξ : ℂ} (hcomm : cubicSite N i * x = ξ • (x * cubicSite N i))
    (hξ : 1 + ξ + ξ ^ 2 = 0) :
    cubicProjection N i * x * cubicProjection N i = 0 := by
  have h1 : cubicSite N i * x * cubicProjection N i = ξ • (x * cubicProjection N i) := by
    rw [hcomm, smul_mul_assoc, mul_assoc, cubicSite_mul_cubicProjection]
  have h2 : cubicSite N i ^ 2 * x * cubicProjection N i =
      (ξ ^ 2) • (x * cubicProjection N i) := by
    calc
      cubicSite N i ^ 2 * x * cubicProjection N i
          = cubicSite N i * (cubicSite N i * x * cubicProjection N i) := by
            rw [sq]; simp only [mul_assoc]
      _ = ξ • (cubicSite N i * x * cubicProjection N i) := by
            conv_lhs => arg 2; rw [h1]
            rw [mul_smul_comm, ← mul_assoc]
      _ = (ξ ^ 2) • (x * cubicProjection N i) := by
            rw [h1, smul_smul, ← sq]
  calc
    cubicProjection N i * x * cubicProjection N i
        = (3 : ℂ)⁻¹ • (x * cubicProjection N i +
            cubicSite N i * x * cubicProjection N i +
            cubicSite N i ^ 2 * x * cubicProjection N i) := by
          nth_rw 1 [cubicProjection_def]
          simp only [smul_mul_assoc, add_mul, one_mul]
    _ = (3 : ℂ)⁻¹ • ((1 + ξ + ξ ^ 2) • (x * cubicProjection N i)) := by
          rw [h1, h2]
          module
    _ = 0 := by rw [hξ, zero_smul, smul_zero]

/-- Adjacent cubic projections satisfy `p_i * p_j * p_i = 3⁻¹ • p_i`. -/
theorem cubicProjection_mul_cubicProjection_mul_cubicProjection {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cubicProjection N i * cubicProjection N j * cubicProjection N i =
      (3 : ℂ)⁻¹ • cubicProjection N i := by
  have hsq : ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) ^ 2 = (cubeRootOfUnity : ℂ) := by
    rw [cubeRootOfUnity_inv_val]
    calc
      ((cubeRootOfUnity : ℂ) ^ 2) ^ 2 = (cubeRootOfUnity : ℂ) ^ 3 * (cubeRootOfUnity : ℂ) := by
        ring
      _ = (cubeRootOfUnity : ℂ) := by rw [cubeRootOfUnity_val_pow_three, one_mul]
  have hinv_poly :
      (1 : ℂ) + ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) + ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) ^ 2 = 0 := by
    rw [hsq, cubeRootOfUnity_inv_val]
    linear_combination one_add_cubeRootOfUnity_add_sq
  obtain ⟨ξ, hcomm, hξ, hξ2⟩ :
      ∃ ξ : ℂ, cubicSite N i * cubicSite N j = ξ • (cubicSite N j * cubicSite N i) ∧
        1 + ξ + ξ ^ 2 = 0 ∧ 1 + ξ ^ 2 + (ξ ^ 2) ^ 2 = 0 := by
    rcases h with hij | hji
    · refine ⟨cubeRootOfUnity, cubicSite_mul_cubicSite_of_succ hij,
        one_add_cubeRootOfUnity_add_sq, ?_⟩
      simpa [← cubeRootOfUnity_inv_val] using hinv_poly
    · refine ⟨((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ), cubicSite_mul_cubicSite_of_pred hji, hinv_poly, ?_⟩
      rw [hsq]
      exact one_add_cubeRootOfUnity_add_sq
  have hcomm2 :
      cubicSite N i * cubicSite N j ^ 2 = (ξ ^ 2) • (cubicSite N j ^ 2 * cubicSite N i) := by
    calc
      cubicSite N i * cubicSite N j ^ 2
          = (cubicSite N i * cubicSite N j) * cubicSite N j := by rw [sq, mul_assoc]
      _ = ξ • (cubicSite N j * (cubicSite N i * cubicSite N j)) := by
            conv_lhs => arg 1; rw [hcomm]
            rw [smul_mul_assoc, mul_assoc]
      _ = (ξ ^ 2) • (cubicSite N j ^ 2 * cubicSite N i) := by
            rw [hcomm, mul_smul_comm, smul_smul, ← sq, ← mul_assoc, ← sq]
  have ht1 : cubicProjection N i * cubicSite N j * cubicProjection N i = 0 :=
    cubicProjection_mul_mul_cubicProjection_eq_zero hcomm hξ
  have ht2 : cubicProjection N i * cubicSite N j ^ 2 * cubicProjection N i = 0 :=
    cubicProjection_mul_mul_cubicProjection_eq_zero hcomm2 hξ2
  conv_lhs => rw [cubicProjection_def N j]
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one,
    cubicProjection_mul_self, ht1, ht2, add_zero]

/-- Cubic projections at distance at least two commute. -/
theorem commute_cubicProjection {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cubicProjection N i) (cubicProjection N j) := by
  unfold Commute SemiconjBy
  rw [cubicProjection_def, cubicProjection_def, smul_mul_smul_comm, smul_mul_smul_comm]
  congr 1
  have hc := commute_cubicSite h
  have h1 : cubicSite N i * cubicSite N j = cubicSite N j * cubicSite N i := hc.eq
  have h2 : cubicSite N i * cubicSite N j ^ 2 = cubicSite N j ^ 2 * cubicSite N i :=
    (hc.pow_right 2).eq
  have h3 : cubicSite N i ^ 2 * cubicSite N j = cubicSite N j * cubicSite N i ^ 2 :=
    (hc.pow_left 2).eq
  have h4 : cubicSite N i ^ 2 * cubicSite N j ^ 2 = cubicSite N j ^ 2 * cubicSite N i ^ 2 :=
    ((hc.pow_left 2).pow_right 2).eq
  simp only [add_mul, mul_add, one_mul, mul_one, h1, h2, h3, h4]
  abel

/-- The `j`-th Temperley–Lieb generator `(√3 : ℂ) • cubicProjection (m - 1) j`, bundled as an
element of `cubicFixed (m - 1)`. -/
private noncomputable def cubicFixedGenerator (m : ℕ) (j : Fin (m - 1)) : cubicFixed (m - 1) :=
  ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
    Subalgebra.smul_mem _ (cubicProjection_mem_cubicFixed (m - 1) j) _⟩

/-- The **cubic-torus comparison homomorphism**
`TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`, sending `e (√3 : ℂ) j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
  lift (cubicFixedGenerator m)
    (fun i ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, SetLike.val_smul, cubicFixedGenerator, smul_mul_smul_comm,
        cubicProjection_mul_self, smul_smul])
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, cubicFixedGenerator, smul_mul_assoc, mul_smul_comm,
        cubicProjection_mul_cubicProjection_mul_cubicProjection h, smul_smul]
      rw [sqrt_three_coe_mul_self]
      norm_num)
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, cubicFixedGenerator]
      exact ((commute_cubicProjection h).smul_left (Real.sqrt 3 : ℂ) |>.smul_right
        (Real.sqrt 3 : ℂ)).eq)

/-- Action of `cubicFixedHom` on the `j`-th Temperley–Lieb generator, coerced to
`CubicTorus (m - 1)`. -/
@[simp]
theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by
  simp [cubicFixedHom, cubicFixedGenerator]

/-- `cubicFixedHom` intertwines the Temperley–Lieb analytic adjoint with `cubicAdjoint`. -/
theorem coe_cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicFixedHom m (star x) : CubicTorus (m - 1)) =
      cubicAdjoint (m - 1) (cubicFixedHom m x) := by
  let F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
    (cubicFixed (m - 1)).val.comp (cubicFixedHom m)
  change F (star x) = cubicAdjoint (m - 1) (F x)
  induction x using TemperleyLieb.induction with
  | e j =>
    change (cubicFixedHom m (star (e (Real.sqrt 3 : ℂ) j)) : CubicTorus (m - 1)) =
      cubicAdjoint (m - 1) (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j))
    rw [star_e, coe_cubicFixedHom_e, map_smulₛₗ, cubicAdjoint_cubicProjection]
    simp [Complex.conj_ofReal]
  | algebraMap z =>
    have hstar : star (algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) z) =
        algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) (conj z) := by
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, ← Algebra.algebraMap_eq_smul_one,
        Complex.star_def]
    rw [hstar, F.commutes, F.commutes, cubicAdjoint_algebraMap]
  | add x y hx hy =>
    rw [star_add, map_add, map_add, hx, hy, map_add]
  | mul x y hx hy =>
    rw [star_mul, map_mul, map_mul, hx, hy, cubicAdjoint_mul]

/-- `cubicFixedHom` intertwines the Temperley–Lieb analytic adjoint with `cubicFixedAdjoint`. -/
@[simp]
theorem cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedHom m (star x) = cubicFixedAdjoint (m - 1) (cubicFixedHom m x) :=
  Subtype.ext (coe_cubicFixedHom_star x)

end TauCeti.TemperleyLieb
