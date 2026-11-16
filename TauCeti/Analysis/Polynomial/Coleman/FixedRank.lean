/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Algebra.Polynomial.Reverse
public import TauCeti.Analysis.Polynomial.Coleman.Entire
public import TauCeti.Analysis.Polynomial.GaussNorm
public import TauCeti.RingTheory.PowerSeries.Entire.Resultant
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.Matrix.Normed
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
import TauCeti.Topology.Instances.Matrix

/-!
# Coleman's transform at a fixed polynomial rank with entire functional input

For entire power series `B` and `F` with `B(0) = 0` and `F(0) = 1`, `PowerSeries.colemanDEntire B F`
passes to the limit in both the characteristic rank and the functional degree simultaneously; the
condition `B(0) = 0` is needed so that increasing the formal rank does not introduce extra factors
`1 - B(0) T` from zero eigenvalues.

When the characteristic input is a normalized polynomial `P` of formal rank `n ≥ deg P` (such as a
reversed characteristic polynomial `det (1 - X A)` on an `n`-dimensional summand), the rank `n` is
fixed and **no `B(0) = 0` hypothesis is needed**. Reducing `B` modulo the monic reversal
`P.reflect n` via entire division (`PowerSeries.modByMonic`) produces a polynomial remainder of
degree less than `n`, and `PowerSeries.colemanDFixedRank B P n` applies the finite spectral
transform `Polynomial.colemanDBounded` at degree bounds `(n, n)` to this remainder.

Over any complete normed commutative ring `R` — archimedean or nonarchimedean, possibly with
nilpotents, and without assuming `‖1‖ = 1` — the finite transforms
`Polynomial.colemanDBounded (trunc (N + 1) B) P n N` of the polynomial truncations of an entire
series `B` converge to `B.colemanDFixedRank P n` both coefficientwise and in the Gauss norm of
every radius `r : ℝ`. Because every approximant has degree at most `n`, coefficientwise convergence
upgrades directly to Gauss-norm convergence without ultrametric majorants. Passing algebraic
identities through this truncation limit yields:

* the exact zero-root padding law `D_(n+1)(B, P) = (1 - B(0) X) * D_n(B, P)`;
* multiplicativity `D_(n+m)(B, P * Q) = D_n(B, P) * D_m(B, Q)` in normalized polynomial factors;
* evaluation `D_1(B, 1 - a X) = 1 - B(a) X` on linear factors and finite products thereof;
* compatibility with continuous ring homomorphisms into Hausdorff commutative rings, and evaluation
  at `t : R` as the entire resultant `(P.reflect n).entireResultant (1 - C t * B)`;
* compatibility with `PowerSeries.colemanDEntire B (P : R⟦X⟧)` whenever `B(0) = 0`;
* **entire matrix spectral mapping** (`Matrix.colemanDFixedRank_charpolyRev`): for any square
  matrix `M` of size `n = Fintype.card ι` and any entire series `B` (including `B(0) ≠ 0`),
  `B.colemanDFixedRank M.charpolyRev n = (B.evalAt M).charpolyRev`.

Over a complete ultrametric ring with `‖1‖ = 1`, entire division is unique, so
`B.colemanDFixedRank P n` is also invariant under adding `(P.reflect n : R⟦X⟧) * G` for entire `G`.

## Main definitions

* `PowerSeries.colemanDFixedRank`: Coleman's spectral transform `D_n(B, P)` of a polynomial `P` at
  formal rank `n` along a power series `B`, defined via `B.modByMonic (P.reflect n)`.

## Main results

* `PowerSeries.colemanDFixedRank_coe_of_natDegree_le`: for a polynomial `B` of degree at most `m`,
  `colemanDFixedRank (B : R⟦X⟧) P n = Polynomial.colemanDBounded B P n m`.
* `PowerSeries.IsEntire.tendsto_coeff_colemanDBounded_trunc_left` and
  `PowerSeries.IsEntire.tendsto_gaussNorm_colemanDBounded_trunc_left_sub_colemanDFixedRank`:
  coefficientwise and all-radius Gauss-norm convergence of finite truncation transforms.
* `PowerSeries.IsEntire.tendsto_gaussNorm_colemanDBounded_trunc_diag_sub_colemanDFixedRank`:
  all-radius Gauss-norm convergence of simultaneous diagonal truncations when `B(0) = 0`.
* `PowerSeries.IsEntire.colemanDFixedRank_succ`, `PowerSeries.IsEntire.colemanDFixedRank_add`,
  `PowerSeries.IsEntire.colemanDFixedRank_mul`,
  `PowerSeries.IsEntire.colemanDFixedRank_prod_one_sub_C_mul_X`: padding, multiplicativity, and
  evaluation on split factors.
* `PowerSeries.IsEntire.map_colemanDFixedRank` and `PowerSeries.IsEntire.eval_colemanDFixedRank`:
  continuous base change and scalar evaluation via `Polynomial.entireResultant`.
* `PowerSeries.IsEntire.colemanDEntire_coe_right`: agreement with `PowerSeries.colemanDEntire` when
  `B(0) = 0`.
* `PowerSeries.IsEntire.colemanDFixedRank_add_coe_mul_reflect`: invariance modulo `P.reflect n`
  over complete ultrametric rings with `‖1‖ = 1`.
* `Matrix.colemanDFixedRank_charpolyRev`: `det (1 - X B(M))` equals `B.colemanDFixedRank` of
  `det (1 - X M)` at rank `Fintype.card ι` for arbitrary entire `B`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A3.
-/

public section

namespace PowerSeries

open Filter Finset
open scoped Topology Polynomial

section TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- **Coleman's spectral transform at fixed rank.** For a power series `B`, a polynomial `P`, and a
formal rank `n`, `B.colemanDFixedRank P n` reduces `B` modulo the reversed polynomial `P.reflect n`
by `PowerSeries.modByMonic` and applies `Polynomial.colemanDBounded` at degree bounds `(n, n)`.
When `B` is entire over a complete normed commutative ring, `P.coeff 0 = 1`, and `P.natDegree ≤ n`,
this computes the spectral transform of `P` along `B` at rank `n` without requiring `B(0) = 0`. -/
noncomputable def colemanDFixedRank (B : R⟦X⟧) (P : R[X]) (n : ℕ) : R[X] :=
  Polynomial.colemanDBounded (B.modByMonic (P.reflect n)) P n n

/-- Unfolding lemma for `PowerSeries.colemanDFixedRank`. -/
theorem colemanDFixedRank_def (B : R⟦X⟧) (P : R[X]) (n : ℕ) :
    B.colemanDFixedRank P n = Polynomial.colemanDBounded (B.modByMonic (P.reflect n)) P n n := by
  rw [colemanDFixedRank]

/-- The fixed-rank Coleman transform at rank `n` is a polynomial of degree at most `n`. -/
theorem natDegree_colemanDFixedRank_le (B : R⟦X⟧) (P : R[X]) (n : ℕ) :
    (B.colemanDFixedRank P n).natDegree ≤ n :=
  Polynomial.natDegree_colemanDBounded_le _ _ _ _

/-- Every remainder modulo `p` has natural degree bounded by `p.natDegree`. -/
private theorem natDegree_modByMonic_le (B : R⟦X⟧) (p : R[X]) :
    (B.modByMonic p).natDegree ≤ p.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_
  rw [coeff_modByMonic, ite_eq_right (by omega)]

/-- For normalized `P`, `B.colemanDFixedRank P n` has constant coefficient `1`. -/
@[simp]
theorem coeff_zero_colemanDFixedRank {P : R[X]} (hP0 : P.coeff 0 = 1) (B : R⟦X⟧) (n : ℕ) :
    (B.colemanDFixedRank P n).coeff 0 = 1 :=
  Polynomial.coeff_zero_colemanDBounded hP0 _ _ _

/-- At formal rank `0`, the fixed-rank Coleman transform is `1` for every `B` and `P`. -/
@[simp]
theorem colemanDFixedRank_zero_rank (B : R⟦X⟧) (P : R[X]) : B.colemanDFixedRank P 0 = 1 := by
  simp [colemanDFixedRank_def, Polynomial.colemanDBounded_def, Polynomial.resultant]

/-- Along the zero power series, the fixed-rank Coleman transform of normalized `P` is `1`. -/
@[simp]
theorem colemanDFixedRank_zero_left {P : R[X]} (hP0 : P.coeff 0 = 1) (n : ℕ) :
    colemanDFixedRank 0 P n = 1 := by
  rw [colemanDFixedRank_def, zero_modByMonic, Polynomial.colemanDBounded_zero_left hP0]

/-- At `P = 1`, all `n` formal inverse roots vanish, so the fixed-rank transform is
`(1 - B(0) X) ^ n` without any analyticity hypothesis on `B`. -/
@[simp]
theorem colemanDFixedRank_one_right (B : R⟦X⟧) (n : ℕ) :
    B.colemanDFixedRank 1 n = (1 - Polynomial.C (coeff 0 B) * Polynomial.X) ^ n := by
  nontriviality R
  rcases n with _ | n
  · simp
  · rw [colemanDFixedRank_def, Polynomial.colemanDBounded_one_right]
    congr 2
    rw [Polynomial.reflect_one, coeff_modByMonic, Polynomial.natDegree_X_pow,
      ite_eq_left (Nat.zero_lt_succ n), map_sub, Polynomial.coe_pow, Polynomial.coe_X,
      coeff_X_pow_mul', ite_eq_right (by omega), sub_zero]

/-- When `B(0) = 0`, the fixed-rank transform of `1` is `1` at every rank. -/
theorem colemanDFixedRank_one_right_of_coeff_zero {B : R⟦X⟧} (hB0 : coeff 0 B = 0) (n : ℕ) :
    B.colemanDFixedRank 1 n = 1 := by
  simp [hB0]

/-- **Agreement with the polynomial Coleman transform.** On a polynomial `B` of degree at most `m`,
`colemanDFixedRank` agrees with `Polynomial.colemanDBounded B P n m`. -/
theorem colemanDFixedRank_coe_of_natDegree_le {B P : R[X]} {n m : ℕ} (hP : P.natDegree ≤ n)
    (hP0 : P.coeff 0 = 1) (hB : B.natDegree ≤ m) :
    colemanDFixedRank (B : R⟦X⟧) P n = B.colemanDBounded P n m := by
  rw [colemanDFixedRank_def, modByMonic_coe B (Polynomial.monic_reflect_of_natDegree_le hP hP0),
    ← Polynomial.colemanDBounded_modByMonic hP hP0 hB]

/-- On a polynomial `B`, `colemanDFixedRank` agrees with `Polynomial.colemanDBounded` at
`B.natDegree`. -/
@[simp]
theorem colemanDFixedRank_coe {B P : R[X]} {n : ℕ} (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) :
    colemanDFixedRank (B : R⟦X⟧) P n = B.colemanDBounded P n B.natDegree :=
  colemanDFixedRank_coe_of_natDegree_le hP hP0 le_rfl

/-- Along a constant series `C c`, every formal inverse root is mapped to `c`, giving
`(1 - c X) ^ n`. -/
@[simp]
theorem colemanDFixedRank_C_left {P : R[X]} {n : ℕ} (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1)
    (c : R) : colemanDFixedRank (C c) P n = (1 - Polynomial.C c * Polynomial.X) ^ n := by
  have hC : 1 - Polynomial.C Polynomial.X * (Polynomial.C c).map Polynomial.C =
      Polynomial.C (1 - Polynomial.C c * Polynomial.X) := by
    rw [Polynomial.map_C, Polynomial.C_sub, Polynomial.C_1, Polynomial.C_mul, mul_comm]
  rw [← Polynomial.coe_C,
    colemanDFixedRank_coe_of_natDegree_le hP hP0 (Polynomial.natDegree_C c).le,
    Polynomial.colemanDBounded_def, hC, Polynomial.resultant_C_right, pow_zero, one_mul]

/-- Along the constant series `1`, the fixed-rank transform is `(1 - X) ^ n`. -/
@[simp]
theorem colemanDFixedRank_one_left {P : R[X]} {n : ℕ} (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) :
    colemanDFixedRank 1 P n = (1 - Polynomial.X) ^ n := by
  simpa using colemanDFixedRank_C_left hP hP0 (1 : R)

/-- Along the coordinate series `X`, the fixed-rank transform returns `P` unchanged. -/
@[simp]
theorem colemanDFixedRank_X_left {P : R[X]} {n : ℕ} (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) :
    colemanDFixedRank X P n = P := by
  rw [← Polynomial.coe_X, colemanDFixedRank_coe_of_natDegree_le hP hP0 Polynomial.natDegree_X_le,
    Polynomial.colemanDBounded_X_left hP]

end TopologicalRing

section Normed

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {B G : R⟦X⟧} {P Q : R[X]} {n m : ℕ}

omit [CompleteSpace R] in
/-- Coefficientwise convergence of polynomial families passes to their product. -/
private theorem tendsto_coeff_mul {α : Type*} {l : Filter α} {f g : α → R[X]} {f₀ g₀ : R[X]}
    (hf : ∀ j, Tendsto (fun a ↦ (f a).coeff j) l (𝓝 (f₀.coeff j)))
    (hg : ∀ j, Tendsto (fun a ↦ (g a).coeff j) l (𝓝 (g₀.coeff j))) (k : ℕ) :
    Tendsto (fun a ↦ (f a * g a).coeff k) l (𝓝 ((f₀ * g₀).coeff k)) := by
  simp only [Polynomial.coeff_mul]
  exact tendsto_finsetSum _ fun ij _ ↦ (hf ij.1).mul (hg ij.2)

/-- **Coefficient limits at fixed characteristic rank.** For an entire series `B` and a normalized
polynomial `P` of degree at most `n`, the `k`-th coefficient of the finite Coleman transform
`D_(n,N)(trunc (N + 1) B, P)` converges to that of `B.colemanDFixedRank P n` as `N → ∞`. -/
theorem IsEntire.tendsto_coeff_colemanDBounded_trunc_left (hB : B.IsEntire)
    (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) (k : ℕ) :
    Tendsto (fun N ↦ (Polynomial.colemanDBounded (trunc (N + 1) B) P n N).coeff k) atTop
      (𝓝 ((B.colemanDFixedRank P n).coeff k)) := by
  have hm : (P.reflect n).Monic := Polynomial.monic_reflect_of_natDegree_le hP hP0
  have hred (N : ℕ) : Polynomial.colemanDBounded (trunc (N + 1) B) P n N =
      Polynomial.colemanDBounded ((trunc (N + 1) B : R⟦X⟧).modByMonic (P.reflect n)) P n n := by
    rw [modByMonic_coe _ hm,
      ← Polynomial.colemanDBounded_modByMonic hP hP0 (Nat.lt_succ_iff.mp (natDegree_trunc_lt B N))]
  simp_rw [hred, colemanDFixedRank_def]
  exact Polynomial.tendsto_coeff_colemanDBounded
    (fun i _ ↦ (hB.tendsto_coeff_modByMonic_trunc (P.reflect n) i).comp (tendsto_add_atTop_nat 1))
    (fun _ _ ↦ tendsto_const_nhds) k

/-- `B.colemanDFixedRank P n` is uniquely determined by the coefficientwise limits of the finite
transforms of the polynomial truncations of `B`. -/
theorem colemanDFixedRank_eq_of_tendsto_coeff (hB : B.IsEntire) (hP : P.natDegree ≤ n)
    (hP0 : P.coeff 0 = 1) {H : R[X]}
    (hH : ∀ k, Tendsto (fun N ↦ (Polynomial.colemanDBounded (trunc (N + 1) B) P n N).coeff k)
      atTop (𝓝 (H.coeff k))) :
    B.colemanDFixedRank P n = H := by
  ext k
  exact tendsto_nhds_unique (hB.tendsto_coeff_colemanDBounded_trunc_left hP hP0 k) (hH k)

/-- **All-radius Gauss convergence at fixed characteristic rank.** For an entire series `B` and a
normalized polynomial `P` of degree at most `n`, the finite transforms
`D_(n,N)(trunc (N + 1) B, P)` converge to `B.colemanDFixedRank P n` in the Gauss norm of every
radius `r : ℝ`, with no `B(0) = 0` or ultrametric hypothesis. -/
theorem IsEntire.tendsto_gaussNorm_colemanDBounded_trunc_left_sub_colemanDFixedRank
    (hB : B.IsEntire) (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) (r : ℝ) :
    Tendsto (fun N ↦ (((Polynomial.colemanDBounded (trunc (N + 1) B) P n N -
        B.colemanDFixedRank P n : R[X]) : R⟦X⟧)).gaussNorm norm r) atTop (𝓝 0) :=
  Polynomial.tendsto_gaussNorm_coe_sub_of_natDegree_le
    (Eventually.of_forall fun _ ↦ Polynomial.natDegree_colemanDBounded_le _ _ _ _)
    (natDegree_colemanDFixedRank_le B P n)
    (fun k _ ↦ hB.tendsto_coeff_colemanDBounded_trunc_left hP hP0 k) r

/-- **Simultaneous diagonal truncation convergence.** When `B` is entire with `B(0) = 0` and `P` is
a normalized polynomial of degree at most `n`, the diagonal finite transforms
`D_(N,N)(trunc (N + 1) B, trunc (N + 1) P)` converge in every Gauss norm to
`B.colemanDFixedRank P n`. -/
theorem IsEntire.tendsto_gaussNorm_colemanDBounded_trunc_diag_sub_colemanDFixedRank
    (hB : B.IsEntire) (hB0 : coeff 0 B = 0) (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1)
    (r : ℝ) :
    Tendsto (fun N ↦ (((Polynomial.colemanDBounded (trunc (N + 1) B)
        (trunc (N + 1) (P : R⟦X⟧)) N N - B.colemanDFixedRank P n : R[X]) : R⟦X⟧)).gaussNorm norm r)
      atTop (𝓝 0) := by
  refine (hB.tendsto_gaussNorm_colemanDBounded_trunc_left_sub_colemanDFixedRank hP hP0 r).congr' ?_
  filter_upwards [eventually_ge_atTop n] with N hN
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  have htruncP : trunc (n + d + 1) (P : R⟦X⟧) = P :=
    trunc_coe_eq_self (Nat.lt_succ_of_le (hP.trans (Nat.le_add_right n d)))
  have htruncB0 : (trunc (n + d + 1) B).coeff 0 = 0 := by
    simp [coeff_trunc, hB0]
  rw [htruncP, Polynomial.colemanDBounded_add_of_coeff_zero hP htruncB0 d]

/-- **Exact zero-root padding law.** Increasing the formal rank by `1` multiplies the fixed-rank
Coleman transform along an entire series `B` by `1 - B(0) X`. -/
theorem IsEntire.colemanDFixedRank_succ (hB : B.IsEntire) (hP : P.natDegree ≤ n)
    (hP0 : P.coeff 0 = 1) :
    B.colemanDFixedRank P (n + 1) =
      (1 - Polynomial.C (coeff 0 B) * Polynomial.X) * B.colemanDFixedRank P n := by
  refine colemanDFixedRank_eq_of_tendsto_coeff hB (hP.trans n.le_succ) hP0 fun k ↦ ?_
  have hpad (N : ℕ) : Polynomial.colemanDBounded (trunc (N + 1) B) P (n + 1) N =
      (1 - Polynomial.C (coeff 0 B) * Polynomial.X) *
        Polynomial.colemanDBounded (trunc (N + 1) B) P n N := by
    simpa [coeff_trunc] using Polynomial.colemanDBounded_add (B := trunc (N + 1) B) hP 1
  simp_rw [hpad]
  exact tendsto_coeff_mul (fun _ ↦ tendsto_const_nhds)
    (hB.tendsto_coeff_colemanDBounded_trunc_left hP hP0) k

/-- Padding the formal rank by `d` multiplies the fixed-rank Coleman transform along an entire
series `B` by `(1 - B(0) X) ^ d`. -/
theorem IsEntire.colemanDFixedRank_add (hB : B.IsEntire) (hP : P.natDegree ≤ n)
    (hP0 : P.coeff 0 = 1) (d : ℕ) :
    B.colemanDFixedRank P (n + d) =
      (1 - Polynomial.C (coeff 0 B) * Polynomial.X) ^ d * B.colemanDFixedRank P n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, hB.colemanDFixedRank_succ (hP.trans (Nat.le_add_right n d)) hP0, ih,
      pow_succ', mul_assoc]

/-- When `B` is entire and `B(0) = 0`, the fixed-rank Coleman transform is independent of the
chosen formal rank `n ≥ deg P`. -/
theorem IsEntire.colemanDFixedRank_add_of_coeff_zero (hB : B.IsEntire) (hB0 : coeff 0 B = 0)
    (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) (d : ℕ) :
    B.colemanDFixedRank P (n + d) = B.colemanDFixedRank P n := by
  simp [hB.colemanDFixedRank_add hP hP0 d, hB0]

/-- **Multiplicativity in the polynomial input.** For an entire series `B` and normalized
polynomials `P` and `Q` of degrees at most `n` and `m`,
`D_(n+m)(B, P * Q) = D_n(B, P) * D_m(B, Q)`. -/
theorem IsEntire.colemanDFixedRank_mul (hB : B.IsEntire) (hP : P.natDegree ≤ n)
    (hP0 : P.coeff 0 = 1) (hQ : Q.natDegree ≤ m) (hQ0 : Q.coeff 0 = 1) :
    B.colemanDFixedRank (P * Q) (n + m) =
      B.colemanDFixedRank P n * B.colemanDFixedRank Q m := by
  have hPQ : (P * Q).natDegree ≤ n + m := Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP hQ)
  have hPQ0 : (P * Q).coeff 0 = 1 := by simp [Polynomial.mul_coeff_zero, hP0, hQ0]
  refine colemanDFixedRank_eq_of_tendsto_coeff hB hPQ hPQ0 fun k ↦ ?_
  have hmul (N : ℕ) : Polynomial.colemanDBounded (trunc (N + 1) B) (P * Q) (n + m) N =
      Polynomial.colemanDBounded (trunc (N + 1) B) P n N *
        Polynomial.colemanDBounded (trunc (N + 1) B) Q m N :=
    Polynomial.colemanDBounded_mul hP hQ (Nat.lt_succ_iff.mp (natDegree_trunc_lt B N))
  simp_rw [hmul]
  exact tendsto_coeff_mul (hB.tendsto_coeff_colemanDBounded_trunc_left hP hP0)
    (hB.tendsto_coeff_colemanDBounded_trunc_left hQ hQ0) k

/-- **Linear characteristic input evaluates the entire series.** For any entire series `B` and
`a : R` (including `a = 0`), `D_1(B, 1 - a X) = 1 - B(a) X`. -/
theorem IsEntire.colemanDFixedRank_one_sub_C_mul_X (hB : B.IsEntire) (a : R) :
    B.colemanDFixedRank (1 - Polynomial.C a * Polynomial.X) 1 =
      1 - Polynomial.C (B.evalAt a) * Polynomial.X := by
  have href : (1 - Polynomial.C a * Polynomial.X).reflect 1 = Polynomial.X - Polynomial.C a := by
    simp
  have hdeg : (B.modByMonic (Polynomial.X - Polynomial.C a)).natDegree ≤ 1 :=
    (natDegree_modByMonic_le B _).trans (Polynomial.natDegree_X_sub_C_le a)
  rw [colemanDFixedRank_def, href, Polynomial.colemanDBounded_one_sub_C_mul_X hdeg a,
    ← hB.evalAt_eq_eval_modByMonic (Polynomial.monic_X_sub_C a) (by simp)]

/-- On a product `∏ i ∈ s, (1 - αᵢ X)` of `s.card` linear factors, `colemanDFixedRank` replaces
each formal inverse root `αᵢ` by `B.evalAt (αᵢ)`. -/
theorem IsEntire.colemanDFixedRank_prod_one_sub_C_mul_X {ι : Type*} (hB : B.IsEntire)
    (s : Finset ι) (α : ι → R) :
    B.colemanDFixedRank (∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X)) s.card =
      ∏ i ∈ s, (1 - Polynomial.C (B.evalAt (α i)) * Polynomial.X) := by
  classical
  have hdeg1 (c : R) : (1 - Polynomial.C c * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le))
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hprod_deg : (∏ j ∈ s, (1 - Polynomial.C (α j) * Polynomial.X)).natDegree ≤ s.card :=
      (Polynomial.natDegree_prod_le _ _).trans (by simpa using sum_le_sum fun j _ ↦ hdeg1 (α j))
    have hprod0 : (∏ j ∈ s, (1 - Polynomial.C (α j) * Polynomial.X)).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
      simp
    rw [prod_insert hi, prod_insert hi, card_insert_of_notMem hi, add_comm s.card 1,
      hB.colemanDFixedRank_mul (hdeg1 (α i)) (by simp) hprod_deg hprod0,
      hB.colemanDFixedRank_one_sub_C_mul_X, ih]

/-- **Base change.** A continuous ring homomorphism into a Hausdorff commutative ring commutes with
`colemanDFixedRank`. -/
theorem IsEntire.map_colemanDFixedRank {S : Type*} [CommRing S] [TopologicalSpace S] [T2Space S]
    (hB : B.IsEntire) (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) (φ : R →+* S)
    (hφ : Continuous φ) :
    (B.colemanDFixedRank P n).map φ = (PowerSeries.map φ B).colemanDFixedRank (P.map φ) n := by
  nontriviality S
  have hm : (P.reflect n).Monic := Polynomial.monic_reflect_of_natDegree_le hP hP0
  rw [colemanDFixedRank_def, colemanDFixedRank_def, Polynomial.colemanDBounded_map,
    ← hB.map_modByMonic hm φ hφ, Polynomial.reflect_map]

/-- **Scalar evaluation via the entire resultant.** Evaluating `B.colemanDFixedRank P n` at `t : R`
computes the entire resultant `(P.reflect n).entireResultant (1 - C t * B)`. -/
theorem IsEntire.eval_colemanDFixedRank (hB : B.IsEntire) (hP : P.natDegree ≤ n)
    (hP0 : P.coeff 0 = 1) (t : R) :
    (B.colemanDFixedRank P n).eval t = (P.reflect n).entireResultant (1 - C t * B) := by
  nontriviality R
  have hQ := Polynomial.isMonicOfDegree_reflect hP hP0
  have hrem : (B.modByMonic (P.reflect n)).natDegree ≤ n :=
    (natDegree_modByMonic_le B _).trans hQ.natDegree_eq.le
  have hlin : (1 - C t * B : R⟦X⟧) = 1 + (-t) • B := by
    ext k
    simp [sub_eq_add_neg]
  have hmk :
      AdjoinRoot.mk (P.reflect n) ((1 : R[X]) %ₘ P.reflect n + (-t) • B.modByMonic (P.reflect n)) =
        AdjoinRoot.mk (P.reflect n) (1 - Polynomial.C t * B.modByMonic (P.reflect n)) := by
    have hsmul : ((-t) • B.modByMonic (P.reflect n) : R[X]) =
        -(Polynomial.C t * B.modByMonic (P.reflect n)) := by
      ext k
      simp
    rw [hsmul, AdjoinRoot.mk_eq_mk]
    exact ⟨-((1 : R[X]) /ₘ P.reflect n),
      by linear_combination Polynomial.modByMonic_add_div 1 (P.reflect n)⟩
  rw [colemanDFixedRank_def, Polynomial.eval_colemanDBounded_eq_norm_mk hP hP0 hrem t,
    Polynomial.entireResultant_def, hlin, isEntire_one.add_modByMonic (hB.smul (-t)),
    hB.smul_modByMonic (-t), ← Polynomial.coe_one, modByMonic_coe _ hQ.monic, hmk]

/-- **Compatibility with `PowerSeries.colemanDEntire`.** When `B` is entire with `B(0) = 0` and
`P` is a normalized polynomial of degree at most `n`, the two-sided entire transform
`colemanDEntire B (P : R⟦X⟧)` is the coercion of the polynomial `B.colemanDFixedRank P n`. -/
theorem IsEntire.colemanDEntire_coe_right (hB : B.IsEntire) (hB0 : coeff 0 B = 0)
    (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) :
    colemanDEntire B (P : R⟦X⟧) = (B.colemanDFixedRank P n : R⟦X⟧) := by
  apply colemanDEntire_eq_of_tendsto_coeff
  intro k
  rw [Polynomial.coeff_coe]
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop :=
    tendsto_atTop.mpr fun b ↦ (eventually_ge_atTop (0, b)).mono fun _ hp ↦ hp.2
  refine ((hB.tendsto_coeff_colemanDBounded_trunc_left hP hP0 k).comp hsnd).congr' ?_
  filter_upwards [eventually_ge_atTop (n, 0)] with p hp
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hp.1
  have htruncP : trunc (p.1 + 1) (P : R⟦X⟧) = P :=
    trunc_coe_eq_self (Nat.lt_succ_of_le (hP.trans hp.1))
  have htruncB0 : (trunc (p.2 + 1) B).coeff 0 = 0 := by
    simp [coeff_trunc, hB0]
  rw [Function.comp_apply, htruncP, hd,
    Polynomial.colemanDBounded_add_of_coeff_zero hP htruncB0 d]

end Normed

section Ultrametric

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R] [NormOneClass R]
  {B B₁ B₂ G : R⟦X⟧} {P : R[X]} {n : ℕ}

/-- Over a complete ultrametric ring with `‖1‖ = 1`, `B.colemanDFixedRank P n` depends on an entire
series `B` only through its image in `AdjoinRoot (P.reflect n)` under `IsEntire.mkAdjoinRoot`. -/
theorem IsEntire.colemanDFixedRank_eq_of_mkAdjoinRoot_eq (hB₁ : B₁.IsEntire) (hB₂ : B₂.IsEntire)
    (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1)
    (h : IsEntire.mkAdjoinRoot (Polynomial.monic_reflect_of_natDegree_le hP hP0)
        ⟨B₁, IsEntire.mem_subring.mpr hB₁⟩ =
      IsEntire.mkAdjoinRoot (Polynomial.monic_reflect_of_natDegree_le hP hP0)
        ⟨B₂, IsEntire.mem_subring.mpr hB₂⟩) :
    B₁.colemanDFixedRank P n = B₂.colemanDFixedRank P n := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hQ := Polynomial.isMonicOfDegree_reflect hP hP0
  rw [IsEntire.mkAdjoinRoot_apply, IsEntire.mkAdjoinRoot_apply] at h
  exact Polynomial.colemanDBounded_eq_of_mk_eq hP hP0
    ((natDegree_modByMonic_le B₁ _).trans hQ.natDegree_eq.le)
    ((natDegree_modByMonic_le B₂ _).trans hQ.natDegree_eq.le) h

/-- **Invariance modulo `P.reflect n`.** Over a complete ultrametric ring with `‖1‖ = 1`, adding an
entire multiple of `P.reflect n` to an entire series `B` leaves `B.colemanDFixedRank P n`
unchanged. -/
theorem IsEntire.colemanDFixedRank_add_coe_mul_reflect (hB : B.IsEntire) (hG : G.IsEntire)
    (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) :
    (B + (P.reflect n : R⟦X⟧) * G).colemanDFixedRank P n = B.colemanDFixedRank P n := by
  have hm : (P.reflect n).Monic := Polynomial.monic_reflect_of_natDegree_le hP hP0
  rw [colemanDFixedRank_def, colemanDFixedRank_def,
    hB.add_modByMonic ((isEntire_coe _).mul hG), hG.coe_mul_modByMonic hm, add_zero]

/-- Any entire multiple of the characteristic reversal `P.reflect n` has fixed-rank Coleman
transform `1`. -/
@[simp]
theorem IsEntire.colemanDFixedRank_coe_reflect_mul_left (hG : G.IsEntire)
    (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) :
    (((P.reflect n : R[X]) : R⟦X⟧) * G).colemanDFixedRank P n = 1 := by
  simpa [hP0] using isEntire_zero.colemanDFixedRank_add_coe_mul_reflect hG hP hP0

end Ultrametric

end PowerSeries

namespace Matrix

open Filter Polynomial PowerSeries
open scoped Topology

section OperatorNorm

open scoped Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- In the `L∞` operator norm topology (which agrees with the entrywise topology by
`Matrix.linftyOpTopologicalSpace_eq`), the polynomial truncations of an entire series evaluated at
`M` converge to `B.evalAt M`. -/
private theorem tendsto_aeval_trunc_op {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [NormedCommRing R] [CompleteSpace R] (M : Matrix ι ι R) {B : R⟦X⟧} (hB : B.IsEntire) :
    Tendsto (fun N ↦ Polynomial.aeval M (trunc N B)) atTop (𝓝 (B.evalAt M)) :=
  hB.tendsto_aeval_trunc M

end OperatorNorm

/-- **Entire matrix spectral mapping.** For any `n × n` matrix `M` over a complete normed
commutative ring `R` and any entire power series `B : R⟦X⟧` — with no restriction on the constant
term `B(0)` — the fixed-rank Coleman transform of `det (1 - X M)` at rank `n = Fintype.card ι` is
`det (1 - X B(M))`. -/
theorem colemanDFixedRank_charpolyRev {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [NormedCommRing R] [CompleteSpace R] (M : Matrix ι ι R) {B : R⟦X⟧} (hB : B.IsEntire) :
    B.colemanDFixedRank M.charpolyRev (Fintype.card ι) = (B.evalAt M).charpolyRev := by
  refine colemanDFixedRank_eq_of_tendsto_coeff hB M.natDegree_charpolyRev_le
    M.coeff_charpolyRev_zero fun k ↦ ?_
  have hfin (N : ℕ) :
      Polynomial.colemanDBounded (trunc (N + 1) B) M.charpolyRev (Fintype.card ι) N =
        (Polynomial.aeval M (trunc (N + 1) B)).charpolyRev :=
    M.colemanDBounded_charpolyRev (Nat.lt_succ_iff.mp (natDegree_trunc_lt B N))
  have hcont : Continuous fun A : Matrix ι ι R ↦ A.charpolyRev.coeff k := by
    simp_rw [charpolyRev_eq_reflect, coeff_reflect]
    exact Matrix.continuous_charpoly_coeff _
  have hlim : Tendsto (fun N ↦ Polynomial.aeval M (trunc N B)) atTop (𝓝 (B.evalAt M)) :=
    @Eq.ndrec (TopologicalSpace (Matrix ι ι R)) (Matrix.linftyOpTopologicalSpace ι ι R)
      (fun t ↦ Tendsto (fun N ↦ Polynomial.aeval M (trunc N B)) atTop
        (@nhds _ t (@PowerSeries.evalAt _ _ _ _ _ t B M)))
      (tendsto_aeval_trunc_op M hB) _ (Matrix.linftyOpTopologicalSpace_eq ι ι R)
  simp_rw [hfin]
  exact (hcont.tendsto (B.evalAt M)).comp (hlim.comp (tendsto_add_atTop_nat 1))

end Matrix
