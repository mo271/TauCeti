/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.RingTheory.DividedPowers.Basic

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.DividedPowers.RatAlgebra

/-!
# Divided powers from identities on generators

Let `I` be an ideal of a commutative semiring `A`. Constructing a divided power structure
`DividedPowers I` directly requires checking both the multiplication identity
`δₘ(x) * δₙ(x) = ((m + n).choose m) * δₘ₊ₙ(x)` and the iteration identity
`δₘ(δₙ(x)) = uniformBell m n * δₘₙ(x)` (`n ≠ 0`) on every element of `I`. Following Roby (1965),
Berthelot (1974, I.1.3), and [Stacks Lemma 07GP](https://stacks.math.columbia.edu/tag/07GP), this
file isolates the linear and additive part of the divided power axioms in a bundled candidate
structure `TauCeti.AdditivePowers I` and proves that if `I = Ideal.span S`, it suffices to check
the multiplication and positive-inner-degree iteration identities on the generators `s ∈ S`.

The key nontrivial step is sum-stability of the iteration identity (`AdditivePowers.dpow_comp_add`):
expanding `δₘ(δₙ(x + y))` via the multinomial formula, homogeneity, and the multiplication law at
`x` and `y` expresses `δₘ(δₙ(x + y))` as a universal `ℕ`-linear combination of the divided
monomials `δₐ(x) * δᵦ(y)` (`a + b = m * n`), with coefficients independent of `(A, I, δ, x, y)`.
Evaluating the same universal expansion in the polynomial `ℚ`-algebra `MvPolynomial (Fin 2) ℚ`
equipped with `DividedPowers.RatAlgebra.dividedPowers` identifies every universal coefficient with
`uniformBell m n`, without assuming any map from `A` to a `ℚ`-algebra or any subtraction in `A`.

## Main declarations

* `TauCeti.AdditivePowers`: additive divided-power candidates on an ideal `I` of a commutative
  semiring `A` (total functions vanishing outside `I`, satisfying degree-`0`, degree-`1`,
  ideal-membership, addition, and scalar-homogeneity laws).
* `DividedPowers.toAdditivePowers`: every `DividedPowers I` structure gives an `AdditivePowers I`
  with the same underlying operation.
* `DividedPowers.dpow_sum_piAntidiag` and `TauCeti.AdditivePowers.dpow_sum_piAntidiag`: the
  multinomial expansion of `dpow n (∑ i ∈ s, x i)` indexed by `Finset.piAntidiag s n`.
* `TauCeti.AdditivePowers.mul_dpow_add`: the multiplication identity is stable under sums.
* `TauCeti.AdditivePowers.dpow_comp_add`: when the multiplication identity holds at `x` and `y`,
  the positive-inner-degree iteration identity is stable under sums.
* `TauCeti.AdditivePowers.toDividedPowers`: constructs `DividedPowers I` from an
  `AdditivePowers I` whose multiplication and positive-inner-degree iteration identities hold on a
  generating set `S` of `I`.
* `TauCeti.AdditivePowers.exists_not_exists_dividedPowers`: there exists an `AdditivePowers`
  structure on an ideal of a commutative ring (`DualNumber (ZMod 2)`) whose operations come from no
  `DividedPowers` structure, showing that the generator hypotheses cannot be omitted.

## References

* [Stacks: Divided power algebra, Lemma 07GP](https://stacks.math.columbia.edu/tag/07GP).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*, Lecture Notes in
  Mathematics 407, Springer (1974), Chapitre I, §1.3.
* N. Roby, *Les algèbres à puissances dividées*, Bull. Sci. Math. (2) 89 (1965), 75–91.
* Mathlib's `DividedPowers` formalization by A. Chambert-Loir and M. I. de Frutos-Fernández.
-/

public section

open Finset Nat

namespace TauCeti

section Definition

variable {A : Type*} [CommSemiring A] (I : Ideal A)

/-- An **additive divided-power candidate** on an ideal `I` of a commutative semiring `A`: a family
of total maps `dpow : ℕ → A → A` vanishing outside `I` in all degrees (matching Mathlib's
`DividedPowers` convention) and satisfying the degree-`0`, degree-`1`, ideal-membership, addition,
and scalar-homogeneity axioms, without assuming the multiplication or iteration identities. -/
structure AdditivePowers where
  /-- The underlying family of candidate divided-power maps `ℕ → A → A`. -/
  dpow : ℕ → A → A
  /-- Outside `I`, every candidate operation vanishes (including degree `0`). -/
  dpow_null : ∀ {n x} (_ : x ∉ I), dpow n x = 0
  /-- On `I`, the degree-`0` operation is identically `1`. -/
  dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1
  /-- On `I`, the degree-`1` operation is the identity. -/
  dpow_one : ∀ {x} (_ : x ∈ I), dpow 1 x = x
  /-- Positive-degree candidate operations preserve `I`. -/
  dpow_mem : ∀ {n x} (_ : n ≠ 0) (_ : x ∈ I), dpow n x ∈ I
  /-- The divided-power binomial identity `δₙ(x + y) = ∑_{i + j = n} δᵢ(x) δⱼ(y)` on `I`. -/
  dpow_add : ∀ {n x y} (_ : x ∈ I) (_ : y ∈ I),
    dpow n (x + y) = ∑ k ∈ antidiagonal n, dpow k.1 x * dpow k.2 y
  /-- Scalar homogeneity `δₙ(a * x) = a ^ n * δₙ(x)` for `a : A` and `x ∈ I`. -/
  dpow_mul : ∀ {n} {a : A} {x} (_ : x ∈ I), dpow n (a * x) = a ^ n * dpow n x

instance : CoeFun (AdditivePowers I) fun _ ↦ ℕ → A → A := ⟨AdditivePowers.dpow⟩

variable {I}

@[ext]
theorem AdditivePowers.ext {δ₁ δ₂ : AdditivePowers I}
    (h : ∀ (n : ℕ) {x : A}, x ∈ I → δ₁.dpow n x = δ₂.dpow n x) :
    δ₁ = δ₂ := by
  obtain ⟨f₁, hnull₁, _, _, _, _, _⟩ := δ₁
  obtain ⟨f₂, hnull₂, _, _, _, _, _⟩ := δ₂
  simp only [AdditivePowers.mk.injEq]
  ext n x
  by_cases hx : x ∈ I
  · exact h n hx
  · rw [hnull₁ hx, hnull₂ hx]

theorem AdditivePowers.coe_injective :
    Function.Injective (fun (δ : AdditivePowers I) ↦ (δ : ℕ → A → A)) := fun _ _ h ↦ by
  ext n _
  exact congr_fun (congr_fun h n) _

end Definition

end TauCeti

namespace DividedPowers

variable {A : Type*} [CommSemiring A] {I : Ideal A}

/-- Every divided power structure on `I` yields an additive divided-power candidate with the same
operations. -/
def toAdditivePowers (hI : DividedPowers I) : TauCeti.AdditivePowers I where
  dpow := hI.dpow
  dpow_null := hI.dpow_null
  dpow_zero := hI.dpow_zero
  dpow_one := hI.dpow_one
  dpow_mem := hI.dpow_mem
  dpow_add := hI.dpow_add
  dpow_mul := hI.dpow_mul

@[simp]
theorem toAdditivePowers_dpow (hI : DividedPowers I) :
    hI.toAdditivePowers.dpow = hI.dpow :=
  (rfl)

theorem toAdditivePowers_injective :
    Function.Injective (toAdditivePowers (A := A) (I := I)) := fun _ _ h ↦ by
  ext n x
  exact congr_fun (congr_fun (congr_arg TauCeti.AdditivePowers.dpow h) n) x

end DividedPowers

private theorem dpow_sum_piAntidiag_aux {A M : Type*} [CommSemiring A] [AddCommMonoid M]
    {I : AddSubmonoid M} (dpow : ℕ → M → A)
    (dpow_zero : ∀ {x}, x ∈ I → dpow 0 x = 1)
    (dpow_add : ∀ {n x y}, x ∈ I → y ∈ I →
      dpow n (x + y) = ∑ k ∈ antidiagonal n, dpow k.1 x * dpow k.2 y)
    (dpow_eval_zero : ∀ {n : ℕ}, n ≠ 0 → dpow n 0 = 0)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → M}
    (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    dpow n (∑ i ∈ s, x i) = ∑ e ∈ piAntidiag s n, ∏ i ∈ s, dpow (e i) (x i) := by
  induction s using Finset.cons_induction generalizing n with
  | empty =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp [dpow_zero I.zero_mem]
    · simp [dpow_eval_zero hn, hn]
  | cons a s ha ih =>
    have hx_s : ∀ i ∈ s, x i ∈ I := fun i hi ↦ hx i (mem_cons_of_mem hi)
    rw [sum_cons, dpow_add (hx a (mem_cons_self a s)) (I.sum_mem hx_s),
      piAntidiag_cons ha n, sum_disjiUnion]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [ih hx_s p.2, mul_sum, sum_map]
    refine sum_congr rfl fun g hg ↦ ?_
    have hga : g a = 0 := by
      by_contra hne
      exact ha ((mem_piAntidiag.mp hg).2 a hne)
    rw [prod_cons]
    simp only [addRightEmbedding_apply, Pi.add_apply, hga, zero_add, ↓reduceIte]
    exact congrArg (_ * ·) (prod_congr rfl fun i hi ↦ by simp [show i ≠ a from fun h ↦ ha (h ▸ hi)])

/-- Multinomial expansion of `hI.dpow n (∑ i ∈ s, x i)` indexed by `Finset.piAntidiag s n`. -/
theorem DividedPowers.dpow_sum_piAntidiag {A : Type*} [CommSemiring A] {I : Ideal A}
    (hI : DividedPowers I) {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    hI.dpow n (∑ i ∈ s, x i) = ∑ e ∈ piAntidiag s n, ∏ i ∈ s, hI.dpow (e i) (x i) :=
  dpow_sum_piAntidiag_aux hI.dpow hI.dpow_zero hI.dpow_add hI.dpow_eval_zero hx n

namespace TauCeti.AdditivePowers

section Basic

variable {A : Type*} [CommSemiring A] {I : Ideal A} (δ : AdditivePowers I)

@[simp]
theorem dpow_zero_at_zero : δ.dpow 0 0 = 1 :=
  δ.dpow_zero I.zero_mem

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : δ.dpow n 0 = 0 := by
  rw [← mul_zero (0 : A), δ.dpow_mul I.zero_mem, zero_pow hn, zero_mul, zero_mul]

theorem dpow_smul {n : ℕ} {a x : A} (hx : x ∈ I) :
    δ.dpow n (a • x) = a ^ n • δ.dpow n x := by
  simp only [smul_eq_mul, δ.dpow_mul hx]

theorem dpow_mul_right {n : ℕ} {a x : A} (hx : x ∈ I) :
    δ.dpow n (x * a) = δ.dpow n x * a ^ n := by
  rw [mul_comm, δ.dpow_mul hx, mul_comm]

/-- Multinomial expansion of `δ.dpow n (∑ i ∈ s, x i)` over `s.sym n`. -/
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    δ.dpow n (∑ i ∈ s, x i) =
      ∑ k ∈ s.sym n, ∏ i ∈ s, δ.dpow (Multiset.count i k) (x i) :=
  DividedPowers.dpow_sum' δ.dpow δ.dpow_zero δ.dpow_add δ.dpow_eval_zero hx

/-- Multinomial expansion of `δ.dpow n (∑ i ∈ s, x i)` indexed by `Finset.piAntidiag s n`. -/
theorem dpow_sum_piAntidiag {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    δ.dpow n (∑ i ∈ s, x i) = ∑ e ∈ piAntidiag s n, ∏ i ∈ s, δ.dpow (e i) (x i) :=
  dpow_sum_piAntidiag_aux δ.dpow δ.dpow_zero δ.dpow_add δ.dpow_eval_zero hx n

/-- Repeated-product formula at an element `x ∈ I` satisfying the multiplication identity. -/
theorem prod_dpow_of_mul_dpow {x : A} (hx : x ∈ I)
    (hmul : ∀ m k, δ.dpow m x * δ.dpow k x = ((m + k).choose m : A) * δ.dpow (m + k) x)
    {ι : Type*} (s : Finset ι) (e : ι → ℕ) :
    ∏ i ∈ s, δ.dpow (e i) x = (multinomial s e : A) * δ.dpow (∑ i ∈ s, e i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [δ.dpow_zero hx]
  | insert i s hi ih =>
    rw [prod_insert hi, ih, ← mul_assoc, mul_comm (δ.dpow (e i) x),
      mul_assoc, hmul, ← sum_insert hi, ← mul_assoc]
    congr 1
    rw [multinomial_insert hi, mul_comm, Nat.cast_mul, sum_insert hi]

end Basic

section SumStability

variable {A : Type*} [CommSemiring A] {I : Ideal A} (δ : AdditivePowers I)

private theorem vandermonde_fiber_sum {m n : ℕ} {ab : ℕ × ℕ} (hab : ab ∈ antidiagonal (m + n)) :
    (∑ pq ∈ (antidiagonal m ×ˢ antidiagonal n).filter
        (fun pq ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) = ab),
      ab.1.choose pq.1.1 * ab.2.choose pq.1.2) = (m + n).choose m := by
  have hab_eq : ab.1 + ab.2 = m + n := mem_antidiagonal.mp hab
  rw [← hab_eq, Nat.add_choose_eq ab.1 ab.2 m,
    ← sum_filter_of_ne (p := fun ij : ℕ × ℕ ↦ ij.1 ≤ ab.1 ∧ ij.2 ≤ ab.2) fun ij _ hne ↦
      ⟨not_lt.mp fun h ↦ hne (by simp [Nat.choose_eq_zero_of_lt h]),
       not_lt.mp fun h ↦ hne (by simp [Nat.choose_eq_zero_of_lt h])⟩]
  refine sum_bij (fun pq _ ↦ pq.1) ?_ ?_ ?_ fun _ _ ↦ rfl
  · intro pq hpq
    rcases mem_filter.mp hpq with ⟨hpq_prod, hpair⟩
    rcases Prod.mk.inj hpair with ⟨h1, h2⟩
    exact mem_filter.mpr ⟨(mem_product.mp hpq_prod).1, by omega, by omega⟩
  · rintro ⟨⟨i₁, j₁⟩, ⟨k₁, l₁⟩⟩ hpq₁ ⟨⟨i₂, j₂⟩, ⟨k₂, l₂⟩⟩ hpq₂ heq
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    rcases Prod.mk.inj (mem_filter.mp hpq₁).2 with ⟨h1, h2⟩
    rcases Prod.mk.inj (mem_filter.mp hpq₂).2 with ⟨h3, h4⟩
    dsimp only at h1 h2 h3 h4
    ext <;> dsimp only <;> omega
  · rintro ⟨i, j⟩ hij
    rcases mem_filter.mp hij with ⟨hij_mem, hle₁, hle₂⟩
    dsimp only at hle₁ hle₂
    rw [mem_antidiagonal] at hij_mem
    exact ⟨((i, j), (ab.1 - i, ab.2 - j)), mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_antidiagonal.mpr hij_mem, mem_antidiagonal.mpr (by dsimp only; omega)⟩,
       Prod.ext (by dsimp only; omega) (by dsimp only; omega)⟩, rfl⟩

/-- **Sum-stability of the multiplication identity**
([Stacks Lemma 07GP](https://stacks.math.columbia.edu/tag/07GP)): if an additive divided-power
candidate satisfies the multiplication law at `x ∈ I` and at `y ∈ I`, then it satisfies the
multiplication law at `x + y`. -/
theorem mul_dpow_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmul_x : ∀ m n, δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x)
    (hmul_y : ∀ m n, δ.dpow m y * δ.dpow n y = ((m + n).choose m : A) * δ.dpow (m + n) y)
    (m n : ℕ) :
    δ.dpow m (x + y) * δ.dpow n (x + y) =
      ((m + n).choose m : A) * δ.dpow (m + n) (x + y) := by
  rw [δ.dpow_add hx hy, δ.dpow_add hx hy, δ.dpow_add hx hy, sum_mul_sum, mul_sum]
  have hterm (p q : ℕ × ℕ) :
      (δ.dpow p.1 x * δ.dpow p.2 y) * (δ.dpow q.1 x * δ.dpow q.2 y) =
        (((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) : A) *
          (δ.dpow (p.1 + q.1) x * δ.dpow (p.2 + q.2) y) := by
    calc (δ.dpow p.1 x * δ.dpow p.2 y) * (δ.dpow q.1 x * δ.dpow q.2 y)
        = (δ.dpow p.1 x * δ.dpow q.1 x) * (δ.dpow p.2 y * δ.dpow q.2 y) := by ring
      _ = (((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) : A) *
            (δ.dpow (p.1 + q.1) x * δ.dpow (p.2 + q.2) y) := by
          rw [hmul_x, hmul_y]; push_cast; ring
  simp_rw [hterm, ← sum_product']
  have hpart : ∀ pq ∈ antidiagonal m ×ˢ antidiagonal n,
      (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) ∈ antidiagonal (m + n) := fun pq hpq ↦ by
    rcases mem_product.mp hpq with ⟨hp, hq⟩
    rw [mem_antidiagonal] at hp hq ⊢; omega
  rw [← sum_fiberwise_of_maps_to hpart]
  refine sum_congr rfl fun ab hab ↦ ?_
  have halign :
      ∑ pq ∈ (antidiagonal m ×ˢ antidiagonal n).filter
          (fun pq ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) = ab),
        (((pq.1.1 + pq.2.1).choose pq.1.1 * (pq.1.2 + pq.2.2).choose pq.1.2 : ℕ) : A) *
          (δ.dpow (pq.1.1 + pq.2.1) x * δ.dpow (pq.1.2 + pq.2.2) y) =
      ∑ pq ∈ (antidiagonal m ×ˢ antidiagonal n).filter
          (fun pq ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) = ab),
        (((ab.1.choose pq.1.1 * ab.2.choose pq.1.2 : ℕ) : A) *
          (δ.dpow ab.1 x * δ.dpow ab.2 y)) :=
    sum_congr rfl fun pq hpq ↦ by
      rcases Prod.mk.inj (mem_filter.mp hpq).2 with ⟨h1, h2⟩; rw [h1, h2]
  rw [halign, ← sum_mul, ← Nat.cast_sum, vandermonde_fiber_sum hab]

/-- Universal natural coefficient appearing in `(δⱼ(y)) ^ k = powDpowCoeff j k * δₖⱼ(y)`. -/
private def powDpowCoeff (j : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => powDpowCoeff j k * (k * j + j).choose (k * j)

private theorem pow_dpow_eq_powDpowCoeff {y : A} (hy : y ∈ I)
    (hmul_y : ∀ m k, δ.dpow m y * δ.dpow k y = ((m + k).choose m : A) * δ.dpow (m + k) y)
    (j k : ℕ) :
    δ.dpow j y ^ k = (powDpowCoeff j k : A) * δ.dpow (k * j) y := by
  induction k with
  | zero =>
    simp [powDpowCoeff, δ.dpow_zero hy]
  | succ k ih =>
    rw [pow_succ, ih, mul_assoc, hmul_y, ← mul_assoc, ← Nat.cast_mul, add_one_mul]
    rfl

/-- Universal natural coefficient for `δₖ(δᵢ(x) * δⱼ(y))` when `i + j ≠ 0`. -/
private def factorIterCoeff (ij : ℕ × ℕ) (k : ℕ) : ℕ :=
  if ij.1 = 0 then uniformBell k ij.2 else powDpowCoeff ij.2 k * uniformBell k ij.1

private theorem dpow_mul_dpow_eq_factorIterCoeff {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmul_y : ∀ m k, δ.dpow m y * δ.dpow k y = ((m + k).choose m : A) * δ.dpow (m + k) y)
    (hcomp_x : ∀ m {k}, k ≠ 0 → δ.dpow m (δ.dpow k x) = (uniformBell m k : A) * δ.dpow (m * k) x)
    (hcomp_y : ∀ m {k}, k ≠ 0 → δ.dpow m (δ.dpow k y) = (uniformBell m k : A) * δ.dpow (m * k) y)
    {n : ℕ} (hn : n ≠ 0) {ij : ℕ × ℕ} (hij : ij ∈ antidiagonal n) (k : ℕ) :
    δ.dpow k (δ.dpow ij.1 x * δ.dpow ij.2 y) =
      (factorIterCoeff ij k : A) * (δ.dpow (k * ij.1) x * δ.dpow (k * ij.2) y) := by
  by_cases hi : ij.1 = 0
  · have hj : ij.2 ≠ 0 := by
      have hsum := mem_antidiagonal.mp hij
      omega
    simp only [factorIterCoeff, hi, ↓reduceIte, mul_zero, δ.dpow_zero hx, one_mul,
      hcomp_y k hj]
  · simp only [factorIterCoeff, hi, ↓reduceIte]
    rw [mul_comm (δ.dpow ij.1 x), δ.dpow_mul (δ.dpow_mem hi hx),
      pow_dpow_eq_powDpowCoeff δ hy hmul_y, hcomp_x k hi]
    push_cast
    ring

/-- Weighted bi-degree `(∑ e(i,j) i, ∑ e(i,j) j)` of a multi-index on `antidiagonal n`. -/
private def iterDegPair (n : ℕ) (e : ℕ × ℕ → ℕ) : ℕ × ℕ :=
  (∑ ij ∈ antidiagonal n, e ij * ij.1, ∑ ij ∈ antidiagonal n, e ij * ij.2)

private theorem iterDegPair_mem_antidiagonal {m n : ℕ} {e : ℕ × ℕ → ℕ}
    (he : e ∈ piAntidiag (antidiagonal n) m) :
    iterDegPair n e ∈ antidiagonal (m * n) := by
  rw [mem_antidiagonal, iterDegPair, ← sum_add_distrib]
  calc ∑ ij ∈ antidiagonal n, (e ij * ij.1 + e ij * ij.2)
      = ∑ ij ∈ antidiagonal n, e ij * n := by
          refine sum_congr rfl fun ij hij ↦ ?_
          rw [← mul_add, mem_antidiagonal.mp hij]
    _ = (∑ ij ∈ antidiagonal n, e ij) * n := (sum_mul _ _ _).symm
    _ = m * n := by rw [(mem_piAntidiag.mp he).1]

/-- Universal natural coefficient of `δₐ(x) * δᵦ(y)` in the expansion of `δₘ(δₙ(x + y))`. -/
private def iterSumCoeff (m n : ℕ) (ab : ℕ × ℕ) : ℕ :=
  ∑ e ∈ (piAntidiag (antidiagonal n) m).filter (fun e ↦ iterDegPair n e = ab),
    (∏ ij ∈ antidiagonal n, factorIterCoeff ij (e ij)) *
      multinomial (antidiagonal n) (fun ij ↦ e ij * ij.1) *
      multinomial (antidiagonal n) (fun ij ↦ e ij * ij.2)

private theorem dpow_comp_add_eq_sum_iterSumCoeff {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmul_x : ∀ m k, δ.dpow m x * δ.dpow k x = ((m + k).choose m : A) * δ.dpow (m + k) x)
    (hmul_y : ∀ m k, δ.dpow m y * δ.dpow k y = ((m + k).choose m : A) * δ.dpow (m + k) y)
    (hcomp_x : ∀ m {k}, k ≠ 0 → δ.dpow m (δ.dpow k x) = (uniformBell m k : A) * δ.dpow (m * k) x)
    (hcomp_y : ∀ m {k}, k ≠ 0 → δ.dpow m (δ.dpow k y) = (uniformBell m k : A) * δ.dpow (m * k) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) =
      ∑ ab ∈ antidiagonal (m * n),
        (iterSumCoeff m n ab : A) * (δ.dpow ab.1 x * δ.dpow ab.2 y) := by
  have hmem_term : ∀ ij ∈ antidiagonal n, δ.dpow ij.1 x * δ.dpow ij.2 y ∈ I := by
    intro ij hij
    by_cases hi : ij.1 = 0
    · have hj : ij.2 ≠ 0 := by
        have hsum := mem_antidiagonal.mp hij
        omega
      exact I.mul_mem_left _ (δ.dpow_mem hj hy)
    · exact I.mul_mem_right _ (δ.dpow_mem hi hx)
  rw [δ.dpow_add hx hy, δ.dpow_sum_piAntidiag hmem_term m]
  have hprod_eval : ∀ e ∈ piAntidiag (antidiagonal n) m,
      ∏ ij ∈ antidiagonal n, δ.dpow (e ij) (δ.dpow ij.1 x * δ.dpow ij.2 y) =
        (((∏ ij ∈ antidiagonal n, factorIterCoeff ij (e ij)) *
          multinomial (antidiagonal n) (fun ij ↦ e ij * ij.1) *
          multinomial (antidiagonal n) (fun ij ↦ e ij * ij.2) : ℕ) : A) *
          (δ.dpow (iterDegPair n e).1 x * δ.dpow (iterDegPair n e).2 y) := by
    intro e _
    have hcongr :
        ∏ ij ∈ antidiagonal n, δ.dpow (e ij) (δ.dpow ij.1 x * δ.dpow ij.2 y) =
          ∏ ij ∈ antidiagonal n,
            ((factorIterCoeff ij (e ij) : A) *
              (δ.dpow (e ij * ij.1) x * δ.dpow (e ij * ij.2) y)) :=
      prod_congr rfl fun ij hij ↦
        dpow_mul_dpow_eq_factorIterCoeff δ hx hy hmul_y hcomp_x hcomp_y hn hij (e ij)
    rw [hcongr, prod_mul_distrib, prod_mul_distrib,
      δ.prod_dpow_of_mul_dpow hx hmul_x, δ.prod_dpow_of_mul_dpow hy hmul_y, iterDegPair]
    push_cast
    ring
  rw [sum_congr rfl hprod_eval,
    ← sum_fiberwise_of_maps_to fun _ he ↦ iterDegPair_mem_antidiagonal he]
  refine sum_congr rfl fun ab _ ↦ ?_
  have h_align :
      ∑ e ∈ (piAntidiag (antidiagonal n) m).filter (fun e ↦ iterDegPair n e = ab),
          (((∏ ij ∈ antidiagonal n, factorIterCoeff ij (e ij)) *
            multinomial (antidiagonal n) (fun ij ↦ e ij * ij.1) *
            multinomial (antidiagonal n) (fun ij ↦ e ij * ij.2) : ℕ) : A) *
            (δ.dpow (iterDegPair n e).1 x * δ.dpow (iterDegPair n e).2 y) =
        ∑ e ∈ (piAntidiag (antidiagonal n) m).filter (fun e ↦ iterDegPair n e = ab),
          (((∏ ij ∈ antidiagonal n, factorIterCoeff ij (e ij)) *
            multinomial (antidiagonal n) (fun ij ↦ e ij * ij.1) *
            multinomial (antidiagonal n) (fun ij ↦ e ij * ij.2) : ℕ) : A) *
            (δ.dpow ab.1 x * δ.dpow ab.2 y) := by
    refine sum_congr rfl fun e he ↦ ?_
    rw [(mem_filter.mp he).2]
  rw [h_align, ← sum_mul, iterSumCoeff, Nat.cast_sum]

private noncomputable def ratBiMono (p q : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 p + Finsupp.single 1 q

private theorem ratBiMono_eq_iff {p₁ q₁ p₂ q₂ : ℕ} :
    ratBiMono p₁ q₁ = ratBiMono p₂ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨hp, hq⟩ ↦ by rw [hp, hq]⟩
  have h0 := Finsupp.ext_iff.mp h 0
  have h1 := Finsupp.ext_iff.mp h 1
  simp only [ratBiMono, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add] at h0 h1
  exact ⟨h0, h1⟩

private theorem lcoeff_ratDividedPowers_sum (N : ℕ) {ab : ℕ × ℕ} (hab : ab ∈ antidiagonal N)
    (c : ℕ × ℕ → ℕ) :
    open scoped Classical in
    let γ₀ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
      DividedPowers.RatAlgebra.dividedPowers ⊤
    MvPolynomial.lcoeff ℚ (ratBiMono ab.1 ab.2)
      (∑ pq ∈ antidiagonal N,
        (c pq : MvPolynomial (Fin 2) ℚ) *
          (γ₀.dpow pq.1 (MvPolynomial.X 0) * γ₀.dpow pq.2 (MvPolynomial.X 1))) =
      (c ab : ℚ) * ((ab.1 ! : ℚ)⁻¹ * (ab.2 ! : ℚ)⁻¹) := by
  classical
  intro γ₀
  rw [map_sum]
  have hsingle : ∀ pq ∈ antidiagonal N,
      (MvPolynomial.lcoeff ℚ (ratBiMono ab.1 ab.2))
        ((c pq : MvPolynomial (Fin 2) ℚ) *
          (γ₀.dpow pq.1 (MvPolynomial.X 0) * γ₀.dpow pq.2 (MvPolynomial.X 1))) =
        if pq = ab then (c ab : ℚ) * ((ab.1 ! : ℚ)⁻¹ * (ab.2 ! : ℚ)⁻¹) else 0 := by
    intro pq _
    have hmono : γ₀.dpow pq.1 (MvPolynomial.X 0) * γ₀.dpow pq.2 (MvPolynomial.X 1) =
        MvPolynomial.monomial (ratBiMono pq.1 pq.2) ((pq.1 ! : ℚ)⁻¹ * (pq.2 ! : ℚ)⁻¹) := by
      rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ γ₀ Submodule.mem_top,
        DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ γ₀ Submodule.mem_top]
      simp only [Ring.inverse_eq_inv']
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.smul_monomial, MvPolynomial.smul_monomial,
        smul_eq_mul, mul_one, smul_eq_mul, mul_one, MvPolynomial.monomial_mul_monomial]
      rfl
    rw [hmono, ← MvPolynomial.C_eq_natCast, MvPolynomial.C_mul_monomial]
    simp only [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
    by_cases hpq : pq = ab
    · subst hpq; simp
    · have hne : ratBiMono pq.1 pq.2 ≠ ratBiMono ab.1 ab.2 := fun h ↦
        hpq (Prod.ext (ratBiMono_eq_iff.mp h).1 (ratBiMono_eq_iff.mp h).2)
      simp [hpq, hne]
  rw [sum_congr rfl hsingle, sum_ite_eq' _ _ (fun _ ↦ _)]
  simp [hab]

/-- Universal evaluation in `MvPolynomial (Fin 2) ℚ` identifies `iterSumCoeff m n ab` with
`uniformBell m n`. -/
private theorem iterSumCoeff_eq_uniformBell (m : ℕ) {n : ℕ} (hn : n ≠ 0)
    {ab : ℕ × ℕ} (hab : ab ∈ antidiagonal (m * n)) :
    iterSumCoeff m n ab = uniformBell m n := by
  classical
  let γ₀ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
    DividedPowers.RatAlgebra.dividedPowers ⊤
  have h_univ := dpow_comp_add_eq_sum_iterSumCoeff γ₀.toAdditivePowers
    (Submodule.mem_top (x := MvPolynomial.X 0)) (Submodule.mem_top (x := MvPolynomial.X 1))
    (fun _ _ ↦ γ₀.mul_dpow Submodule.mem_top) (fun _ _ ↦ γ₀.mul_dpow Submodule.mem_top)
    (fun _ _ hk ↦ γ₀.dpow_comp hk Submodule.mem_top)
    (fun _ _ hk ↦ γ₀.dpow_comp hk Submodule.mem_top) m hn
  simp only [DividedPowers.toAdditivePowers_dpow] at h_univ
  have h_comp : γ₀.dpow m (γ₀.dpow n (MvPolynomial.X 0 + MvPolynomial.X 1)) =
      ∑ pq ∈ antidiagonal (m * n),
        (uniformBell m n : MvPolynomial (Fin 2) ℚ) *
          (γ₀.dpow pq.1 (MvPolynomial.X 0) * γ₀.dpow pq.2 (MvPolynomial.X 1)) := by
    rw [γ₀.dpow_comp hn Submodule.mem_top, γ₀.dpow_add Submodule.mem_top Submodule.mem_top, mul_sum]
  have h_eq_rat :
      (iterSumCoeff m n ab : ℚ) * ((ab.1 ! : ℚ)⁻¹ * (ab.2 ! : ℚ)⁻¹) =
        (uniformBell m n : ℚ) * ((ab.1 ! : ℚ)⁻¹ * (ab.2 ! : ℚ)⁻¹) := by
    rw [← lcoeff_ratDividedPowers_sum (m * n) hab (iterSumCoeff m n), ← h_univ, h_comp,
      lcoeff_ratDividedPowers_sum (m * n) hab (fun _ ↦ uniformBell m n)]
  have h_inv_ne : (ab.1 ! : ℚ)⁻¹ * (ab.2 ! : ℚ)⁻¹ ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
  exact Nat.cast_injective (mul_right_cancel₀ h_inv_ne h_eq_rat)

/-- **Sum-stability of the iteration identity**
([Stacks Lemma 07GP](https://stacks.math.columbia.edu/tag/07GP)): if an additive divided-power
candidate satisfies the multiplication law at `x ∈ I` and `y ∈ I` and the positive-inner-degree
iteration law at `x` and `y`, then it satisfies the positive-inner-degree iteration law at
`x + y`. -/
theorem dpow_comp_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmul_x : ∀ m k, δ.dpow m x * δ.dpow k x = ((m + k).choose m : A) * δ.dpow (m + k) x)
    (hmul_y : ∀ m k, δ.dpow m y * δ.dpow k y = ((m + k).choose m : A) * δ.dpow (m + k) y)
    (hcomp_x : ∀ m {k}, k ≠ 0 → δ.dpow m (δ.dpow k x) = (uniformBell m k : A) * δ.dpow (m * k) x)
    (hcomp_y : ∀ m {k}, k ≠ 0 → δ.dpow m (δ.dpow k y) = (uniformBell m k : A) * δ.dpow (m * k) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) = (uniformBell m n : A) * δ.dpow (m * n) (x + y) := by
  rw [dpow_comp_add_eq_sum_iterSumCoeff δ hx hy hmul_x hmul_y hcomp_x hcomp_y m hn,
    δ.dpow_add hx hy, mul_sum]
  refine sum_congr rfl fun ab hab ↦ ?_
  rw [iterSumCoeff_eq_uniformBell m hn hab]

end SumStability

section ToDividedPowers

variable {A : Type*} [CommSemiring A] {I : Ideal A} (δ : AdditivePowers I)

/-- Scalar propagation of the multiplication identity at an element `x ∈ I`. -/
theorem mul_dpow_mul {x : A} (hx : x ∈ I)
    (hmul : ∀ m n, δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x)
    (a : A) (m n : ℕ) :
    δ.dpow m (a * x) * δ.dpow n (a * x) = ((m + n).choose m : A) * δ.dpow (m + n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul hx, δ.dpow_mul hx]
  calc (a ^ m * δ.dpow m x) * (a ^ n * δ.dpow n x)
      = a ^ (m + n) * (δ.dpow m x * δ.dpow n x) := by rw [pow_add]; ring
    _ = a ^ (m + n) * (((m + n).choose m : A) * δ.dpow (m + n) x) := by rw [hmul]
    _ = ((m + n).choose m : A) * (a ^ (m + n) * δ.dpow (m + n) x) := by ring

/-- Scalar propagation of the positive-inner-degree iteration identity at an element `x ∈ I`. -/
theorem dpow_comp_mul {x : A} (hx : x ∈ I)
    (hcomp : ∀ m {n}, n ≠ 0 → δ.dpow m (δ.dpow n x) = (uniformBell m n : A) * δ.dpow (m * n) x)
    (a : A) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (a * x)) = (uniformBell m n : A) * δ.dpow (m * n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul (δ.dpow_mem hn hx), hcomp m hn, δ.dpow_mul hx, ← pow_mul,
    mul_comm n m]
  ring

/-- Propagation of the multiplication identity from a generating set `S` of `I` to all of `I`. -/
theorem mul_dpow_of_span {S : Set A} (hI : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    {x : A} (hx : x ∈ I) (m n : ℕ) :
    δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x := by
  subst hI
  induction hx using Submodule.span_induction generalizing m n with
  | mem s hs => exact hmul s hs m n
  | zero =>
    rcases eq_or_ne m 0 with rfl | hm
    · rcases eq_or_ne n 0 with rfl | hn
      · simp [δ.dpow_zero_at_zero]
      · simp [δ.dpow_eval_zero hn]
    · have hmn : m + n ≠ 0 := by omega
      simp [δ.dpow_eval_zero hm, δ.dpow_eval_zero hmn]
  | add x y hxS hyS ihx ihy =>
    exact δ.mul_dpow_add hxS hyS ihx ihy m n
  | smul a x hxS ihx =>
    simpa only [smul_eq_mul] using δ.mul_dpow_mul hxS ihx a m n

/-- Propagation of the iteration identity from a generating set `S` of `I` to all of `I`. -/
theorem dpow_comp_of_span {S : Set A} (hI : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = (uniformBell m n : A) * δ.dpow (m * n) s)
    {x : A} (hx : x ∈ I) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n x) = (uniformBell m n : A) * δ.dpow (m * n) x := by
  have hmul_all : ∀ {z : A}, z ∈ I → ∀ p q,
      δ.dpow p z * δ.dpow q z = ((p + q).choose p : A) * δ.dpow (p + q) z :=
    fun hz p q ↦ δ.mul_dpow_of_span hI hmul hz p q
  subst hI
  induction hx using Submodule.span_induction generalizing m n with
  | mem s hs => exact hcomp s hs m hn
  | zero =>
    rw [δ.dpow_eval_zero hn]
    rcases eq_or_ne m 0 with rfl | hm
    · simp [δ.dpow_zero_at_zero, uniformBell_zero_left]
    · simp [δ.dpow_eval_zero hm, δ.dpow_eval_zero (Nat.mul_ne_zero hm hn)]
  | add x y hxS hyS ihx ihy =>
    exact δ.dpow_comp_add hxS hyS (hmul_all hxS) (hmul_all hyS)
      (fun p _ hk ↦ ihx p hk) (fun p _ hk ↦ ihy p hk) m hn
  | smul a x hxS ihx =>
    simpa only [smul_eq_mul] using δ.dpow_comp_mul hxS (fun p _ hk ↦ ihx p hk) a m hn

/-- **Divided powers from identities on generators**
([Stacks Lemma 07GP](https://stacks.math.columbia.edu/tag/07GP)): if `δ : AdditivePowers I`
satisfies the multiplication and positive-inner-degree iteration identities on a generating set `S`
of `I`, then `δ` defines a `DividedPowers I` structure with the same underlying operations. -/
def toDividedPowers {S : Set A} (hI : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = (uniformBell m n : A) * δ.dpow (m * n) s) :
    DividedPowers I where
  dpow := δ.dpow
  dpow_null := δ.dpow_null
  dpow_zero := δ.dpow_zero
  dpow_one := δ.dpow_one
  dpow_mem := δ.dpow_mem
  dpow_add := δ.dpow_add
  dpow_mul := δ.dpow_mul
  mul_dpow hx := δ.mul_dpow_of_span hI hmul hx _ _
  dpow_comp hn hx := δ.dpow_comp_of_span hI hmul hcomp hx _ hn

@[simp]
theorem toDividedPowers_dpow {S : Set A} (hI : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = (uniformBell m n : A) * δ.dpow (m * n) s) :
    (δ.toDividedPowers hI hmul hcomp).dpow = δ.dpow :=
  (rfl)

@[simp]
theorem toAdditivePowers_toDividedPowers {S : Set A} (hI : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = (uniformBell m n : A) * δ.dpow (m * n) s) :
    (δ.toDividedPowers hI hmul hcomp).toAdditivePowers = δ := by
  ext n _ _
  rfl

theorem toDividedPowers_unique {S : Set A} (hI : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = (uniformBell m n : A) * δ.dpow (m * n) s)
    (γ : DividedPowers I) (hγ : ∀ n, ∀ x ∈ I, γ.dpow n x = δ.dpow n x) :
    γ = δ.toDividedPowers hI hmul hcomp :=
  DividedPowers.ext _ _ fun n _ hx ↦ hγ n _ hx

theorem toDividedPowers_congr {S S' : Set A} (hI : I = Ideal.span S) (hI' : I = Ideal.span S')
    (hmul : ∀ s ∈ S, ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = (uniformBell m n : A) * δ.dpow (m * n) s)
    (hmul' : ∀ s ∈ S', ∀ m n,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp' : ∀ s ∈ S', ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = (uniformBell m n : A) * δ.dpow (m * n) s) :
    δ.toDividedPowers hI hmul hcomp = δ.toDividedPowers hI' hmul' hcomp' :=
  DividedPowers.ext _ _ fun _ _ _ ↦ rfl

@[simp]
theorem _root_.DividedPowers.toDividedPowers_toAdditivePowers (γ : DividedPowers I) :
    γ.toAdditivePowers.toDividedPowers (S := I) (Ideal.span_eq I).symm
      (fun _ hs _ _ ↦ by simpa using γ.mul_dpow hs)
      (fun _ hs _ _ hn ↦ by simpa using γ.dpow_comp hn hs) = γ :=
  DividedPowers.ext _ _ fun _ _ _ ↦ rfl

end ToDividedPowers

section Counterexample

private abbrev dualIdeal : Ideal (DualNumber (ZMod 2)) :=
  RingHom.ker (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2) (ZMod 2))

private def dualCounterexampleDpow : ℕ → DualNumber (ZMod 2) → DualNumber (ZMod 2)
  | 0, z => if z.fst = 0 then 1 else 0
  | 1, z => if z.fst = 0 then z else 0
  | 3, z => if z.fst = 0 then z else 0
  | _, _ => 0

private theorem dualCounterexampleDpow_mem {n : ℕ} {z : DualNumber (ZMod 2)}
    (_ : n ≠ 0) (hz : z ∈ dualIdeal) : dualCounterexampleDpow n z ∈ dualIdeal := by
  have hz0 : z.fst = 0 := hz
  match n with
  | 1 | 3 => simp [dualCounterexampleDpow, hz0]
  | 2 | _ + 4 => exact dualIdeal.zero_mem

private theorem dualCounterexampleDpow_add {n : ℕ} {x y : DualNumber (ZMod 2)}
    (hx : x ∈ dualIdeal) (hy : y ∈ dualIdeal) :
    dualCounterexampleDpow n (x + y) =
      ∑ k ∈ antidiagonal n, dualCounterexampleDpow k.1 x * dualCounterexampleDpow k.2 y := by
  have hx0 : x.fst = 0 := hx
  have hy0 : y.fst = 0 := hy
  have hxy : (x + y).fst = 0 := dualIdeal.add_mem hx hy
  have hmul_zero : ∀ {u v : DualNumber (ZMod 2)}, u ∈ dualIdeal → v ∈ dualIdeal → u * v = 0 := by
    intro u v hu hv; ext <;> simp [show u.fst = 0 from hu, show v.fst = 0 from hv]
  match n with
  | 0 => simp [dualCounterexampleDpow, hx0, hy0, hxy]
  | 1 =>
    rw [show antidiagonal 1 = {(0, 1), (1, 0)} from rfl]
    simp [dualCounterexampleDpow, hx0, hy0, hxy, add_comm]
  | 2 =>
    rw [show antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} from rfl]
    simp [dualCounterexampleDpow, hx0, hy0, hmul_zero hx hy]
  | 3 =>
    rw [show antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
    simp [dualCounterexampleDpow, hx0, hy0, hxy, add_comm]
  | n + 4 =>
    simp only [dualCounterexampleDpow]
    refine (sum_eq_zero fun k hk ↦ ?_).symm
    have hsum : k.1 + k.2 = n + 4 := mem_antidiagonal.mp hk
    rcases eq_or_ne k.1 0 with hk1 | hk1
    · rw [hk1, show k.2 = n + 4 by omega]; exact mul_zero _
    · rcases eq_or_ne k.2 0 with hk2 | hk2
      · rw [hk2, show k.1 = n + 4 by omega]; exact zero_mul _
      · exact hmul_zero (dualCounterexampleDpow_mem hk1 hx) (dualCounterexampleDpow_mem hk2 hy)

private def dualCounterexample : AdditivePowers dualIdeal where
  dpow := dualCounterexampleDpow
  dpow_null {n z} hz := by
    have hfst : z.fst ≠ 0 := hz
    match n with
    | 0 | 1 | 3 => simp [dualCounterexampleDpow, hfst]
    | 2 | _ + 4 => rfl
  dpow_zero {z} hz := by simp [dualCounterexampleDpow, show z.fst = 0 from hz]
  dpow_one {z} hz := by simp [dualCounterexampleDpow, show z.fst = 0 from hz]
  dpow_mem := dualCounterexampleDpow_mem
  dpow_add := dualCounterexampleDpow_add
  dpow_mul {n a x} hx := by
    have hx0 : x.fst = 0 := hx
    have hax : (a * x).fst = 0 := dualIdeal.mul_mem_left a hx
    match n with
    | 0 | 1 => simp [dualCounterexampleDpow, hx0, hax]
    | 2 | _ + 4 => simp [dualCounterexampleDpow]
    | 3 =>
      simp only [dualCounterexampleDpow, hx0, hax, ↓reduceIte]
      have hpow : (a ^ 3).fst = a.fst :=
        (TrivSqZeroExt.fst_pow a 3).trans ((by decide : ∀ c : ZMod 2, c ^ 3 = c) a.fst)
      ext <;> simp [TrivSqZeroExt.snd_mul, hx0, hpow]

/-- An explicit additive divided-power candidate on the ideal `(ε)` of `DualNumber (ZMod 2)` whose
operations (`δ₀ = 1`, `δ₁ = δ₃ = id`, and `δₙ = 0` for `n = 2` and `n ≥ 4` on `(ε)`) violate the
multiplication identity `δ₁(ε) * δ₂(ε) = 3 * δ₃(ε)`, showing that `AdditivePowers` is strictly
weaker than `DividedPowers`. -/
theorem exists_not_exists_dividedPowers :
    ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (δ : AdditivePowers I),
      ¬ ∃ γ : DividedPowers I, γ.dpow = δ.dpow := by
  refine ⟨DualNumber (ZMod 2), inferInstance, dualIdeal, dualCounterexample, ?_⟩
  rintro ⟨γ, hγ⟩
  have heps : (DualNumber.eps : DualNumber (ZMod 2)) ∈ dualIdeal := by simp [dualIdeal]
  have hmul := γ.mul_dpow (m := 1) (n := 2) heps
  rw [hγ] at hmul
  have h0 : dualCounterexample.dpow 1 DualNumber.eps *
      dualCounterexample.dpow 2 DualNumber.eps = 0 := rfl
  have h1 : (((1 + 2).choose 1 : ℕ) : DualNumber (ZMod 2)) *
      dualCounterexample.dpow 3 DualNumber.eps = DualNumber.eps := by
    have hfst : (DualNumber.eps : DualNumber (ZMod 2)).fst = 0 := by simp
    simp only [dualCounterexample, dualCounterexampleDpow, hfst, ↓reduceIte]
    ext <;> decide
  rw [h0, h1] at hmul
  exact (fun h ↦ by simpa using congr_arg TrivSqZeroExt.snd h) hmul.symm

end Counterexample

end TauCeti.AdditivePowers
