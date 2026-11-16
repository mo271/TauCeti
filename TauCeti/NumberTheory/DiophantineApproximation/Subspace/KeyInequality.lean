/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Lemmas
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume
public import TauCeti.NumberTheory.Height.FundamentalInequality
public import TauCeti.NumberTheory.Height.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.Abv.Concentrated
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.BlockSubst

import Mathlib.Tactic.Linarith

/-!
# The key inequality in Schmidt's proof of the Subspace Theorem

In Steps IV and V of Schmidt's proof of the penultimate-minimum theorem (Bombieri–Gubler,
Theorem 7.5.13), a nonzero multihomogeneous polynomial `Q_poly` (a Hasse derivative of the
auxiliary polynomial `P` constructed by Siegel's lemma) is evaluated at a tuple of integer linear
combinations `g h = ∑ a, z h a • b h a` of points `b h a ∈ approxDomain S₀ L c (Q h)` along a
rapidly growing chain of levels `Q h`. Assuming `Q_poly(g) ≠ 0`, the product formula compares local
upper bounds at every place of `K`:

* **At an infinite place `v`**: changing coordinates in every block by
  `(LinearMap.toMatrix' (LinearMap.pi (L v)))⁻¹` expresses `Q_poly(g)` as a multihomogeneous
  polynomial `R v` evaluated at the small linear forms `L v i (g h)`, whose support is concentrated
  around `μ` with radius `Δ` relative to the initial multidegree `d`.
* **At a finite place `v ∈ S₀`**: the same coordinate change and concentration bound apply without
  support-cardinality or integer-grid factors by ultrametricity (`approxModule` is a `ℤ`-submodule).
* **At a finite place `v ∉ S₀`**: every coordinate of `g h` has `v`-adic absolute value at most `1`,
  so `v (Q_poly(g))` is bounded directly by the local sup norm `⨆ m, v (Q_poly.coeff m)` in
  standard coordinates.

Collecting the entries of all local inverse matrices `(LinearMap.toMatrix' (LinearMap.pi (L v)))⁻¹`
together with `1` into a single finite tuple `TauCeti.NumberField.refFamily S₀ L` reassembles all
local factors into global projective heights: `Q_poly.logHeight`,
`Height.logHeight (refFamily S₀ L)`, `approxWeight S₀ c`, and `approxAbsWeight S₀ c`.

## Main definitions

* `TauCeti.NumberField.refFamily S₀ L`: finite tuple packaging `1` and all entries of
  `(LinearMap.toMatrix' (LinearMap.pi (L v)))⁻¹` over the infinite places of `K` and `S₀`.

## Main results

* `MvPolynomial.eval_blockSubst_toMatrix'_pi` and
  `LinearIndependent.eval_blockSubst_toMatrix'_pi_inv`: block-substitution evaluation identities for
  local systems of linear forms.
* `MvPolynomial.hasFiniteMulSupport_iSup_coeff` and `MvPolynomial.mulHeight_eq_of_numberField`:
  finite multiplicative support and placewise product formula for the local sup norms of a nonzero
  multivariate polynomial.
* `TauCeti.NumberField.apply_sum_zsmul_le_of_mem_approxDomain_infinite`,
  `TauCeti.NumberField.apply_sum_zsmul_le_of_mem_approxDomain_finite`, and
  `TauCeti.NumberField.apply_sum_zsmul_le_one_of_mem_approxDomain_notMem`: local bounds on integer
  linear combinations of points of `approxDomain`.
* `TauCeti.NumberField.one_le_mulHeight_mul_exp_of_eval_ne_zero` and
  `TauCeti.NumberField.subspace_key_inequality`: multiplicative and logarithmic global product
  inequalities when `Q_poly(g) ≠ 0`.
* `TauCeti.NumberField.eval_eq_zero_of_subspace_key_inequality`: contrapositive vanishing criterion
  forcing `Q_poly(g) = 0` once the global logarithmic bound is strictly negative.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  proof of Theorem 7.5.13, Steps IV–V.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Springer (1980),
  Chapter VI, §9–§10.
-/

public section

open Finset Module MvPolynomial

/-! ### Block substitution by a system of linear forms and coefficient sup norms -/

namespace MvPolynomial

/-- Evaluating `blockSubst (LinearMap.toMatrix' (LinearMap.pi l)) Q` at `(h, j) ↦ x h j` evaluates
`Q` at the linear-form coordinates `(h, i) ↦ l i (x h)`. -/
theorem eval_blockSubst_toMatrix'_pi {R κ ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (l : ι → Dual R (ι → R)) (x : κ → ι → R) (Q : MvPolynomial (κ × ι) R) :
    eval (fun p ↦ x p.1 p.2) (blockSubst (LinearMap.toMatrix' (LinearMap.pi l)) Q) =
      eval (fun p ↦ l p.2 (x p.1)) Q := by
  have hpt : (fun p : κ × ι ↦ ∑ j, LinearMap.toMatrix' (LinearMap.pi l) p.2 j * x p.1 j) =
      fun p ↦ l p.2 (x p.1) := funext fun ⟨h, i⟩ ↦ by
    have hmul := congrArg (fun M : Matrix κ ι R ↦ M h i)
      (Matrix.of_apply_eq_mul_transpose_toMatrix'_pi l x)
    simpa [Matrix.mul_apply, mul_comm] using hmul.symm
  rw [eval_blockSubst, hpt]

/-- For any polynomial `P` and absolute value `v`, the values `v (P.coeff d)` form a bounded range
even when the variable index type is infinite, since `P` has finitely many distinct coefficients. -/
theorem bddAbove_range_abv_coeff {R σ : Type*} [CommSemiring R] (v : AbsoluteValue R ℝ)
    (P : MvPolynomial σ R) :
    BddAbove (Set.range fun d ↦ v (P.coeff d)) := by
  simpa only [Set.range_comp'] using ((AddMonoidAlgebra.coeff P).finite_range.image v).bddAbove

/-- Every coefficient of `P` is bounded under `v` by `⨆ m, v (P.coeff m)`. -/
theorem le_iSup_abv_coeff {R σ : Type*} [CommSemiring R] (v : AbsoluteValue R ℝ)
    (P : MvPolynomial σ R) (d : σ →₀ ℕ) :
    v (P.coeff d) ≤ ⨆ m, v (P.coeff m) :=
  le_ciSup (P.bddAbove_range_abv_coeff v) d

/-- For a nonzero polynomial `P`, the supremum of `v (P.coeff d)` over all exponent vectors equals
its supremum over `P.support`. -/
theorem iSup_abv_coeff_support {R σ : Type*} [CommSemiring R] (v : AbsoluteValue R ℝ)
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    (⨆ d : P.support, v (P.coeff d)) = ⨆ d, v (P.coeff d) := by
  have _ : Nonempty P.support := (support_nonempty.mpr hP).to_subtype
  refine le_antisymm (ciSup_le fun d ↦ P.le_iSup_abv_coeff v d.1) (ciSup_le fun d ↦ ?_)
  by_cases hd : d ∈ P.support
  · exact le_ciSup (f := fun m : P.support ↦ v (P.coeff m.1)) (Finite.bddAbove_range _) ⟨d, hd⟩
  · rw [notMem_support_iff.mp hd, v.map_zero]
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _

/-- For a nonzero polynomial over a number field, the local coefficient sup norm is `1` at all but
finitely many finite places. -/
theorem hasFiniteMulSupport_iSup_coeff {K σ : Type*} [Field K] [NumberField K]
    {P : MvPolynomial σ K} (hP : P ≠ 0) :
    (fun v : NumberField.FinitePlace K ↦ ⨆ d, v (P.coeff d)).HasFiniteMulSupport := by
  obtain ⟨d₀, hd₀⟩ := support_nonempty.mpr hP
  have hne : (fun d : P.support ↦ P.coeff d) ≠ 0 :=
    Function.ne_iff.mpr ⟨⟨d₀, hd₀⟩, mem_support_iff.mp hd₀⟩
  have heq : (fun v : NumberField.FinitePlace K ↦ ⨆ d, v (P.coeff d)) =
      fun v : NumberField.FinitePlace K ↦ ⨆ d : P.support, v (P.coeff d) :=
    funext fun v ↦ (P.iSup_abv_coeff_support v.1 hP).symm
  rw [heq]
  exact NumberField.FinitePlace.hasFiniteMulSupport_iSup hne

/-- Over a number field, the relative multiplicative height of a nonzero multivariate polynomial is
the product over all places of its local coefficient sup norms. -/
theorem mulHeight_eq_of_numberField {K σ : Type*} [Field K] [NumberField K]
    {P : MvPolynomial σ K} (hP : P ≠ 0) :
    P.mulHeight =
      (∏ v : NumberField.InfinitePlace K, (⨆ d, v (P.coeff d)) ^ v.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, ⨆ d, v (P.coeff d) := by
  have hx : (fun d ↦ P.coeff d) ≠ 0 := fun h ↦
    hP (MvPolynomial.ext _ _ fun d ↦ by simpa using congrFun h d)
  rw [mulHeight_eq_finsupp, Finsupp.mulHeight_eq_mulHeight_coe, NumberField.mulHeight_eq hx]

/-- A multihomogeneous polynomial of multidegree `e` in `card ι` variables per block has at most
`(2 ^ card ι) ^ ∑ h, e h` monomials in its support. -/
theorem IsMultiHomogeneous.card_support_le_two_pow {R κ ι : Type*} [CommSemiring R]
    [Fintype κ] [Fintype ι] [DecidableEq κ] {e : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : P.IsMultiHomogeneous e) :
    #P.support ≤ (2 ^ Fintype.card ι) ^ ∑ h, e h := by
  calc #P.support
      ≤ 2 ^ ∑ p : κ × ι, P.degreeOf p := P.card_support_le_two_pow
    _ ≤ 2 ^ (Fintype.card ι * ∑ h, e h) := by
        refine Nat.pow_le_pow_right two_pos ?_
        rw [Fintype.sum_prod_type]
        calc ∑ h, ∑ i, P.degreeOf (h, i)
            ≤ ∑ h, ∑ _i : ι, e h := sum_le_sum fun h _ ↦ sum_le_sum fun i _ ↦ hP.degreeOf_le h i
          _ = Fintype.card ι * ∑ h, e h := by simp [Finset.mul_sum, Nat.mul_comm]
    _ = (2 ^ Fintype.card ι) ^ ∑ h, e h := pow_mul 2 (Fintype.card ι) (∑ h, e h)

end MvPolynomial

namespace LinearIndependent

/-- **Inverting a linearly independent system of forms in every block.** When `l` is a linearly
independent family of `card ι` linear forms on `ι → K`, evaluating
`blockSubst (LinearMap.toMatrix' (LinearMap.pi l))⁻¹ P` at `(h, i) ↦ l i (x h)` recovers `P`
evaluated at `(h, j) ↦ x h j`. -/
theorem eval_blockSubst_toMatrix'_pi_inv {K κ ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) (x : κ → ι → K)
    (P : MvPolynomial (κ × ι) K) :
    eval (fun p ↦ l p.2 (x p.1)) (blockSubst (LinearMap.toMatrix' (LinearMap.pi l))⁻¹ P) =
      eval (fun p ↦ x p.1 p.2) P := by
  have hdet : IsUnit (LinearMap.toMatrix' (LinearMap.pi l)).det :=
    isUnit_iff_ne_zero.mpr (LinearMap.det_toMatrix' (LinearMap.pi l) ▸ hl.det_pi_ne_zero)
  rw [← eval_blockSubst_toMatrix'_pi, blockSubst_blockSubst_inv hdet]

end LinearIndependent

namespace TauCeti.NumberField

open _root_.NumberField

/-! ### Global reference tuple of inverse form-matrix entries -/

section RefFamily

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]

/-- **Reference tuple of inverse form-matrix entries** (Bombieri–Gubler, proof of Theorem 7.5.13,
Step IV): packages `1` together with all `(i, j)` entries of
`(LinearMap.toMatrix' (LinearMap.pi (L v)))⁻¹` across all infinite places `v` and all `v ∈ S₀`. -/
noncomputable def refFamily (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    Option ((InfinitePlace K ⊕ S₀) × ι × ι) → K
  | none => 1
  | some (Sum.inl v, i, j) => (LinearMap.toMatrix' (LinearMap.pi (L v.1)))⁻¹ i j
  | some (Sum.inr v, i, j) => (LinearMap.toMatrix' (LinearMap.pi (L v.1.1)))⁻¹ i j

@[simp]
theorem refFamily_none (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    refFamily S₀ L none = 1 :=
  (rfl)

@[simp]
theorem refFamily_some_inl (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (v : InfinitePlace K) (i j : ι) :
    refFamily S₀ L (some (Sum.inl v, i, j)) =
      (LinearMap.toMatrix' (LinearMap.pi (L v.1)))⁻¹ i j :=
  (rfl)

@[simp]
theorem refFamily_some_inr (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (v : S₀) (i j : ι) :
    refFamily S₀ L (some (Sum.inr v, i, j)) =
      (LinearMap.toMatrix' (LinearMap.pi (L v.1.1)))⁻¹ i j :=
  (rfl)

theorem refFamily_ne_zero (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    refFamily S₀ L ≠ 0 :=
  Function.ne_iff.mpr ⟨none, one_ne_zero⟩

/-- At every absolute value `v`, the local sup norm of `refFamily S₀ L` is at least `1`. -/
theorem one_le_iSup_refFamily (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (v : AbsoluteValue K ℝ) :
    1 ≤ ⨆ r, v (refFamily S₀ L r) := by
  simpa using le_ciSup (Finite.bddAbove_range fun r ↦ v (refFamily S₀ L r)) none

/-- Every entry of `(LinearMap.toMatrix' (LinearMap.pi (L v)))⁻¹` at an infinite place `v` is
bounded by the local sup norm of `refFamily S₀ L`. -/
theorem apply_inv_toMatrix'_le_iSup_refFamily_infinite (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (v : InfinitePlace K) (i j : ι) :
    v ((LinearMap.toMatrix' (LinearMap.pi (L v.1)))⁻¹ i j) ≤ ⨆ r, v (refFamily S₀ L r) :=
  le_ciSup (Finite.bddAbove_range fun r ↦ v (refFamily S₀ L r)) (some (Sum.inl v, i, j))

/-- Every entry of `(LinearMap.toMatrix' (LinearMap.pi (L v)))⁻¹` at `v ∈ S₀` is bounded by the
local sup norm of `refFamily S₀ L`. -/
theorem apply_inv_toMatrix'_le_iSup_refFamily_finite {S₀ : Finset (FinitePlace K)}
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) {v : FinitePlace K} (hv : v ∈ S₀) (i j : ι) :
    v ((LinearMap.toMatrix' (LinearMap.pi (L v.1)))⁻¹ i j) ≤ ⨆ r, v (refFamily S₀ L r) :=
  le_ciSup (Finite.bddAbove_range fun r ↦ v (refFamily S₀ L r)) (some (Sum.inr ⟨v, hv⟩, i, j))

/-- Multiplicative height of `refFamily S₀ L` as a product of local sup norms. -/
theorem mulHeight_refFamily_eq (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    Height.mulHeight (refFamily S₀ L) =
      (∏ v : InfinitePlace K, (⨆ r, v (refFamily S₀ L r)) ^ v.mult) *
        ∏ᶠ v : FinitePlace K, ⨆ r, v (refFamily S₀ L r) :=
  NumberField.mulHeight_eq (refFamily_ne_zero S₀ L)

/-- Logarithmic height of `refFamily S₀ L` as a weighted sum of local logarithmic sup norms. -/
theorem logHeight_refFamily_eq (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    Height.logHeight (refFamily S₀ L) =
      (∑ v : InfinitePlace K, v.mult * Real.log (⨆ r, v (refFamily S₀ L r))) +
        ∑ᶠ v : FinitePlace K, Real.log (⨆ r, v (refFamily S₀ L r)) := by
  have hi (v : InfinitePlace K) : 0 < ⨆ r, v (refFamily S₀ L r) :=
    zero_lt_one.trans_le (one_le_iSup_refFamily S₀ L v.1)
  have hf (v : FinitePlace K) : 0 < ⨆ r, v (refFamily S₀ L r) :=
    zero_lt_one.trans_le (one_le_iSup_refFamily S₀ L v.1)
  rw [Height.logHeight_eq_log_mulHeight, mulHeight_refFamily_eq,
    Real.log_mul (Finset.prod_pos fun v _ ↦ pow_pos (hi v) _).ne'
      (finprod_ne_zero fun v ↦ (hf v).ne'),
    Real.log_prod fun v _ ↦ (pow_pos (hi v) _).ne',
    Real.log_finprod hf]
  simp only [Real.log_pow]

end RefFamily

/-! ### Local bounds on integer linear combinations of points of an approximation domain -/

section ApproxGrid

variable {K ι τ : Type*} [Field K] [NumberField K] [Fintype τ]

/-- Any `ℤ`-linear combination of points of `approxDomain S₀ L c Q` lies in the finite part
`approxModule S₀ L c Q`. -/
theorem sum_zsmul_mem_approxModule_of_mem_approxDomain {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {b : τ → ι → K} (hb : ∀ a, b a ∈ approxDomain S₀ L c Q) (z : τ → ℤ) :
    (∑ a, z a • b a) ∈ approxModule S₀ L c Q := by
  refine Submodule.sum_mem _ fun a _ ↦ ?_
  obtain ⟨h1, h2⟩ := (mem_approxDomain.mp (hb a)).2
  have hmem : b a ∈ approxModule S₀ L c Q := mem_approxModule.mpr
    ⟨fun v hv i ↦ (h1 v hv i).trans ((le_abs_self _).trans (Real.abs_rpow_le_abs_rpow _ _)), h2⟩
  exact (approxModule S₀ L c Q).toAddSubgroup.zsmul_mem hmem (z a)

/-- At a finite place `v ∈ S₀`, an integer linear combination of points of `approxDomain S₀ L c Q`
(`0 ≤ Q`) satisfies the same ultrametric bound `Q ^ c v i` without any factor depending on `z`. -/
theorem apply_sum_zsmul_le_of_mem_approxDomain_finite {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    (hQ : 0 ≤ Q) {b : τ → ι → K} (hb : ∀ a, b a ∈ approxDomain S₀ L c Q) (z : τ → ℤ)
    {v : FinitePlace K} (hv : v ∈ S₀) (i : ι) :
    v (L v.1 i (∑ a, z a • b a)) ≤ Q ^ c v.1 i := by
  have hmem := (mem_approxModule.mp (sum_zsmul_mem_approxModule_of_mem_approxDomain hb z)).1
    v hv i
  rwa [abs_of_nonneg hQ] at hmem

/-- At a finite place `v ∉ S₀`, every coordinate of an integer linear combination of points of
`approxDomain S₀ L c Q` has `v`-adic absolute value at most `1`. -/
theorem apply_sum_zsmul_le_one_of_mem_approxDomain_notMem {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {b : τ → ι → K} (hb : ∀ a, b a ∈ approxDomain S₀ L c Q) (z : τ → ℤ)
    {v : FinitePlace K} (hv : v ∉ S₀) (j : ι) :
    v ((∑ a, z a • b a) j) ≤ 1 :=
  (mem_approxModule.mp (sum_zsmul_mem_approxModule_of_mem_approxDomain hb z)).2 v hv j

/-- At an infinite place `v`, if `b a ∈ approxDomain S₀ L c Q` (`0 ≤ Q`) and `|(z a : ℝ)| ≤ B_z`,
then `v (L v i (∑ a, z a • b a)) ≤ max 1 (card τ * B_z) * Q ^ c v i`. -/
theorem apply_sum_zsmul_le_of_mem_approxDomain_infinite {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    (hQ : 0 ≤ Q) {b : τ → ι → K} (hb : ∀ a, b a ∈ approxDomain S₀ L c Q)
    {z : τ → ℤ} {B_z : ℝ} (hz : ∀ a, |(z a : ℝ)| ≤ B_z)
    (v : InfinitePlace K) (i : ι) :
    v (L v.1 i (∑ a, z a • b a)) ≤ max 1 (Fintype.card τ * B_z) * Q ^ c v.1 i := by
  rcases isEmpty_or_nonempty τ with _ | hτ
  · simp only [univ_eq_empty, sum_empty, map_zero]
    positivity
  obtain ⟨a₀⟩ := hτ
  have hBz : 0 ≤ B_z := (abs_nonneg _).trans (hz a₀)
  have hmap : L v.1 i (∑ a, z a • b a) = ∑ a, (z a : K) * L v.1 i (b a) := by
    rw [map_sum]
    exact sum_congr rfl fun a _ ↦ by rw [map_zsmul, zsmul_eq_mul]
  rw [hmap]
  calc v (∑ a, (z a : K) * L v.1 i (b a))
      ≤ ∑ a, v ((z a : K) * L v.1 i (b a)) := v.1.sum_le _ _
    _ ≤ ∑ _a : τ, B_z * Q ^ c v.1 i := sum_le_sum fun a _ ↦ by
        have hza : v (z a : K) ≤ B_z := by
          change v.1 (z a : K) ≤ B_z
          rw [← v.1.apply_natAbs_eq]
          exact (v.1.apply_nat_le_self _).trans
            ((by rw [Nat.cast_natAbs, Int.cast_abs] : ((z a).natAbs : ℝ) = |(z a : ℝ)|).trans_le
              (hz a))
        rw [map_mul]
        exact mul_le_mul hza ((mem_approxDomain.mp (hb a)).1 v i) (apply_nonneg _ _) hBz
    _ = (Fintype.card τ * B_z) * Q ^ c v.1 i := by
        rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ max 1 (Fintype.card τ * B_z) * Q ^ c v.1 i :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hQ _)

/-- At a finite place `v ∉ S₀`, evaluating any polynomial `Q_poly` on integer linear combinations
of points of `approxDomain S₀ L c (Q h)` is bounded by `⨆ m, v (Q_poly.coeff m)`. -/
theorem apply_eval_le_of_notMem_S₀ {κ : Type*}
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : κ → ℝ}
    {b : κ → τ → ι → K} (hb : ∀ h a, b h a ∈ approxDomain S₀ L c (Q h)) (z : κ → τ → ℤ)
    (Q_poly : MvPolynomial (κ × ι) K) {v : FinitePlace K} (hv : v ∉ S₀) :
    v (eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly) ≤ ⨆ m, v (Q_poly.coeff m) := by
  have hv_na : IsNonarchimedean v.1 := fun x y ↦ v.add_le x y
  rcases Q_poly.support.eq_empty_or_nonempty with h0 | hne
  · rw [support_eq_empty.mp h0, map_zero, map_zero]
    exact Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  rw [eval_eq]
  refine (hv_na.apply_sum_le_sup hne).trans <| sup'_le _ _ fun m _ ↦ ?_
  have hprod : v (∏ p ∈ m.support, (∑ a, z p.1 a • b p.1 a) p.2 ^ m p) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ apply_nonneg _ _) fun p _ ↦ by
      rw [map_pow]
      exact pow_le_one₀ (apply_nonneg _ _)
        (apply_sum_zsmul_le_one_of_mem_approxDomain_notMem (hb p.1) (z p.1) hv p.2)
  rw [map_mul]
  exact (mul_le_of_le_one_right (apply_nonneg _ _) hprod).trans
    (Q_poly.le_iSup_abv_coeff v.1 m)

end ApproxGrid

/-! ### The global key inequality -/

section KeyInequality

variable {K κ ι τ : Type*} [Field K] [NumberField K] [Fintype κ] [Fintype ι] [Fintype τ]

private theorem sum_concentrated_weight_eq (S₀ : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (D μ Δ : ℝ) (E : κ → ℝ) :
    (∑ v : InfinitePlace K,
        (v.mult : ℝ) * (D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) +
          (∑ h, E h) * ∑ i, |c v.1 i|)) +
      (∑ v ∈ S₀,
        (D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) + (∑ h, E h) * ∑ i, |c v.1 i|)) =
      D * (μ * approxWeight S₀ c + Δ * approxAbsWeight S₀ c) +
        (∑ h, E h) * approxAbsWeight S₀ c := by
  have hexp (w : AbsoluteValue K ℝ) :
      D * (μ * ∑ i, c w i + Δ * ∑ i, |c w i|) + (∑ h, E h) * ∑ i, |c w i| =
        (D * μ) * (∑ i, c w i) + (D * Δ + ∑ h, E h) * ∑ i, |c w i| := by ring
  simp_rw [hexp, mul_add, sum_add_distrib]
  have h1 : ∀ v : InfinitePlace K,
      (v.mult : ℝ) * ((D * μ) * ∑ i, c v.1 i) = (D * μ) * ((v.mult : ℝ) * ∑ i, c v.1 i) :=
    fun _ ↦ by ring
  have h2 : ∀ v : InfinitePlace K,
      (v.mult : ℝ) * ((D * Δ + ∑ h, E h) * ∑ i, |c v.1 i|) =
        (D * Δ + ∑ h, E h) * ((v.mult : ℝ) * ∑ i, |c v.1 i|) :=
    fun _ ↦ by ring
  simp_rw [h1, h2, ← mul_sum]
  rw [approxWeight_def, approxAbsWeight_def]
  ring

variable [DecidableEq ι]

private theorem prod_arch_factor_eq (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (Q_poly : MvPolynomial (κ × ι) K)
    (e : κ → ℕ) (C B_z : ℝ) (W_inf : InfinitePlace K → ℝ) :
    (∏ v : InfinitePlace K,
      (((C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^ ∑ h, e h) *
        (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) *
        (⨆ m, v (Q_poly.coeff m)) *
        Real.exp (W_inf v)) ^ v.mult) =
    (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^
        ((∑ h, e h) * Module.finrank ℚ K) *
      (∏ v : InfinitePlace K, (⨆ r, v (refFamily S₀ L r)) ^ v.mult) ^ (∑ h, e h) *
      (∏ v : InfinitePlace K, (⨆ m, v (Q_poly.coeff m)) ^ v.mult) *
      Real.exp (∑ v : InfinitePlace K, (v.mult : ℝ) * W_inf v) := by
  have hpow (v : InfinitePlace K) :
      (((C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^ ∑ h, e h) *
        (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) *
        (⨆ m, v (Q_poly.coeff m)) *
        Real.exp (W_inf v)) ^ v.mult =
      ((C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^ ∑ h, e h) ^ v.mult *
        ((⨆ r, v (refFamily S₀ L r)) ^ v.mult) ^ (∑ h, e h) *
        (⨆ m, v (Q_poly.coeff m)) ^ v.mult *
        Real.exp ((v.mult : ℝ) * W_inf v) := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul (⨆ r, v (refFamily S₀ L r)),
      mul_comm (∑ h, e h) v.mult, pow_mul (⨆ r, v (refFamily S₀ L r)), ← Real.exp_nat_mul]
  rw [prod_congr rfl fun v _ ↦ hpow v, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib,
    prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul, prod_pow, ← Real.exp_sum]

variable [DecidableEq κ]

private theorem apply_eval_le_arch_factor {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {Q_poly : MvPolynomial (κ × ι) K} {R : AbsoluteValue K ℝ → MvPolynomial (κ × ι) K}
    {e d : κ → ℕ} (hed : ∀ h, e h ≤ d h) {C : ℝ}
    {μ Δ D B_z : ℝ} (hD0 : 0 ≤ D) {Q E : κ → ℝ} (hQ : ∀ h, 0 < Q h)
    (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    {b : κ → τ → ι → K} (hb : ∀ h a, b h a ∈ approxDomain S₀ L c (Q h))
    {z : κ → τ → ℤ} (hz : ∀ h a, |(z h a : ℝ)| ≤ B_z)
    (v : InfinitePlace K) (hR : (R v.1).IsMultiHomogeneous e)
    (heval : eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
      eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc : ∀ J, (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff : ∀ J, v ((R v.1).coeff J) ≤
      C ^ (∑ h, e h) * (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m)) :
    v (eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly) ≤
      (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^ (∑ h, e h) *
        (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) *
        (⨆ m, v (Q_poly.coeff m)) *
        Real.exp (D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) + (∑ h, E h) * ∑ i, |c v.1 i|) := by
  have hB0 : 0 ≤ C ^ (∑ h, e h) * (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) *
      ⨆ m, v (Q_poly.coeff m) :=
    (apply_nonneg _ _).trans (hcoeff 0)
  have hsupp : (#(R v.1).support : ℝ) ≤ ((2 : ℝ) ^ Fintype.card ι) ^ ∑ h, e h := by
    exact_mod_cast hR.card_support_le_two_pow
  rw [← heval]
  calc v (eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1))
      ≤ #(R v.1).support *
          (C ^ (∑ h, e h) * (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m)) *
          max 1 (Fintype.card τ * B_z) ^ (∑ h, e h) *
          Real.exp (D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) +
            (∑ h, E h) * ∑ i, |c v.1 i|) :=
        v.1.apply_eval_le_of_isMultiHomogeneous_concentrated hR hed hcoeff hconc hQ hD0 hD
          fun h i ↦ apply_sum_zsmul_le_of_mem_approxDomain_infinite (hQ h).le (hb h) (hz h) v i
    _ ≤ ((2 : ℝ) ^ Fintype.card ι) ^ (∑ h, e h) *
          (C ^ (∑ h, e h) * (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m)) *
          max 1 (Fintype.card τ * B_z) ^ (∑ h, e h) *
          Real.exp (D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) +
            (∑ h, E h) * ∑ i, |c v.1 i|) := by
        gcongr
    _ = (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^ (∑ h, e h) *
          (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) *
          (⨆ m, v (Q_poly.coeff m)) *
          Real.exp (D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) +
            (∑ h, E h) * ∑ i, |c v.1 i|) := by
        rw [mul_pow, mul_pow]
        ring

private theorem apply_eval_le_nonarch_factor [DecidableEq (FinitePlace K)]
    {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {Q_poly : MvPolynomial (κ × ι) K} {R : AbsoluteValue K ℝ → MvPolynomial (κ × ι) K}
    {e d : κ → ℕ} (hed : ∀ h, e h ≤ d h) {μ Δ D : ℝ} (hD0 : 0 ≤ D)
    {Q E : κ → ℝ} (hQ : ∀ h, 0 < Q h) (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    {b : κ → τ → ι → K} (hb : ∀ h a, b h a ∈ approxDomain S₀ L c (Q h)) (z : κ → τ → ℤ)
    (hR : ∀ v ∈ S₀, (R v.1).IsMultiHomogeneous e)
    (heval : ∀ v ∈ S₀, eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
      eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc : ∀ v ∈ S₀, ∀ J, (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff : ∀ v ∈ S₀, ∀ J, v ((R v.1).coeff J) ≤
      (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m))
    (v : FinitePlace K) :
    v (eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly) ≤
      (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * (⨆ m, v (Q_poly.coeff m)) *
        if v ∈ S₀ then
          Real.exp (D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) + (∑ h, E h) * ∑ i, |c v.1 i|)
        else 1 := by
  by_cases hv : v ∈ S₀
  · simp only [hv, ↓reduceIte, ← heval v hv]
    have hv_na : IsNonarchimedean v.1 := fun x y ↦ v.add_le x y
    exact hv_na.apply_eval_le_of_isMultiHomogeneous_concentrated_one (hR v hv) hed (hcoeff v hv)
      (hconc v hv) hQ hD0 hD fun h i ↦
        apply_sum_zsmul_le_of_mem_approxDomain_finite (hQ h).le (hb h) (z h) hv i
  · simp only [hv, ↓reduceIte, mul_one]
    have h1 : 1 ≤ (⨆ r, v (refFamily S₀ L r)) ^ ∑ h, e h :=
      one_le_pow₀ (one_le_iSup_refFamily S₀ L v.1)
    calc v (eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
        ≤ 1 * ⨆ m, v (Q_poly.coeff m) := by
          rw [one_mul]
          exact apply_eval_le_of_notMem_S₀ hb z Q_poly hv
      _ ≤ (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m) :=
          mul_le_mul_of_nonneg_right h1 (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)

/-- **Multiplicative key inequality in Schmidt's proof of the Subspace Theorem** (Bombieri–Gubler,
Theorem 7.5.13, Steps IV–V). If `Q_poly` does not vanish at the integer linear combinations
`h ↦ ∑ a, z h a • b h a` of points `b h a ∈ approxDomain S₀ L c (Q h)` and its local form-coordinate
representations `R v` are multihomogeneous of multidegree `e ≤ d` and concentrated within `Δ` of `μ`
relative to `d`, then the global product of height, reference-form, grid, and concentrated
exponential factors is at least `1`. -/
theorem one_le_mulHeight_mul_exp_of_eval_ne_zero {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {Q_poly : MvPolynomial (κ × ι) K} {R : AbsoluteValue K ℝ → MvPolynomial (κ × ι) K}
    {e d : κ → ℕ} (hed : ∀ h, e h ≤ d h) {C D μ Δ B_z : ℝ} {Q E : κ → ℝ}
    {b : κ → τ → ι → K} {z : κ → τ → ℤ}
    (hR_inf : ∀ v : InfinitePlace K, (R v.1).IsMultiHomogeneous e)
    (heval_inf : ∀ v : InfinitePlace K,
      eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
        eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc_inf : ∀ (v : InfinitePlace K) (J : κ × ι →₀ ℕ),
      (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff_inf : ∀ (v : InfinitePlace K) (J : κ × ι →₀ ℕ),
      v ((R v.1).coeff J) ≤
        C ^ (∑ h, e h) * (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m))
    (hR_fin : ∀ v ∈ S₀, (R v.1).IsMultiHomogeneous e)
    (heval_fin : ∀ v ∈ S₀,
      eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
        eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc_fin : ∀ v ∈ S₀, ∀ J : κ × ι →₀ ℕ,
      (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff_fin : ∀ v ∈ S₀, ∀ J : κ × ι →₀ ℕ,
      v ((R v.1).coeff J) ≤
        (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m))
    (hQ : ∀ h, 0 < Q h) (hD0 : 0 ≤ D)
    (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    (hb : ∀ h a, b h a ∈ approxDomain S₀ L c (Q h))
    (hz : ∀ h a, |(z h a : ℝ)| ≤ B_z)
    (hne : eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly ≠ 0) :
    1 ≤ (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^
          ((∑ h, e h) * Module.finrank ℚ K) *
        Height.mulHeight (refFamily S₀ L) ^ (∑ h, e h) *
        Q_poly.mulHeight *
        Real.exp (D * (μ * approxWeight S₀ c + Δ * approxAbsWeight S₀ c) +
          (∑ h, E h) * approxAbsWeight S₀ c) := by
  classical
  have hQ_ne : Q_poly ≠ 0 := fun h0 ↦ hne (by simp [h0])
  let W_inf (v : InfinitePlace K) : ℝ :=
    D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) + (∑ h, E h) * ∑ i, |c v.1 i|
  let W_fin (v : FinitePlace K) : ℝ :=
    D * (μ * ∑ i, c v.1 i + Δ * ∑ i, |c v.1 i|) + (∑ h, E h) * ∑ i, |c v.1 i|
  let f₁ (v : FinitePlace K) : ℝ := (⨆ r, v (refFamily S₀ L r)) ^ ∑ h, e h
  let f₂ (v : FinitePlace K) : ℝ := ⨆ m, v (Q_poly.coeff m)
  let f₃ (v : FinitePlace K) : ℝ := if v ∈ S₀ then Real.exp (W_fin v) else 1
  have hf₁ : Function.HasFiniteMulSupport f₁ :=
    (FinitePlace.hasFiniteMulSupport_iSup (refFamily_ne_zero S₀ L)).pow _
  have hf₂ : Function.HasFiniteMulSupport f₂ := Q_poly.hasFiniteMulSupport_iSup_coeff hQ_ne
  have hsub₃ : Function.mulSupport f₃ ⊆ (S₀ : Set (FinitePlace K)) := fun v hv ↦ by
    by_contra hnot; exact hv (by simp [f₃, Finset.mem_coe.not.mp hnot])
  have hf₃ : Function.HasFiniteMulSupport f₃ := S₀.finite_toSet.subset hsub₃
  have h1 := NumberField.one_le_of_forall_apply_le hne ((hf₁.mul hf₂).mul hf₃)
    (fun v ↦ apply_eval_le_arch_factor hed hD0 hQ hD hb hz v
      (hR_inf v) (heval_inf v) (hconc_inf v) (hcoeff_inf v))
    (fun v ↦ apply_eval_le_nonarch_factor hed hD0 hQ hD hb z hR_fin heval_fin hconc_fin
      hcoeff_fin v)
  have hfin : (∏ᶠ v, (f₁ * f₂ * f₃) v) =
      (∏ᶠ v : FinitePlace K, ⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) *
        (∏ᶠ v : FinitePlace K, ⨆ m, v (Q_poly.coeff m)) * ∏ v ∈ S₀, f₃ v := by
    change (∏ᶠ v, (f₁ * f₂) v * f₃ v) = _
    rw [finprod_mul_distrib (hf₁.mul hf₂) hf₃, show f₁ * f₂ = fun v ↦ f₁ v * f₂ v from rfl,
      finprod_mul_distrib hf₁ hf₂,
      finprod_pow (FinitePlace.hasFiniteMulSupport_iSup (refFamily_ne_zero S₀ L)),
      finprod_eq_prod_of_mulSupport_subset f₃ hsub₃]
  rw [hfin] at h1
  refine h1.trans_eq ?_
  have hS₀_prod : (∏ v ∈ S₀, f₃ v) = Real.exp (∑ v ∈ S₀, W_fin v) := by
    rw [Real.exp_sum]; exact prod_congr rfl fun v hv ↦ by simp [f₃, hv]
  change (∏ v : InfinitePlace K,
      (((C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^ ∑ h, e h) *
        (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * (⨆ m, v (Q_poly.coeff m)) *
        Real.exp (W_inf v)) ^ v.mult) *
    ((∏ᶠ v : FinitePlace K, ⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) *
      (∏ᶠ v : FinitePlace K, ⨆ m, v (Q_poly.coeff m)) * ∏ v ∈ S₀, f₃ v) = _
  rw [prod_arch_factor_eq, hS₀_prod, mulHeight_refFamily_eq,
    Q_poly.mulHeight_eq_of_numberField hQ_ne]
  dsimp only [W_inf, W_fin]
  rw [← sum_concentrated_weight_eq, Real.exp_add, mul_pow]
  ring

/-- **Logarithmic key inequality in Schmidt's proof of the Subspace Theorem** (Bombieri–Gubler,
Theorem 7.5.13, Steps IV–V). Under the hypotheses of
`TauCeti.NumberField.one_le_mulHeight_mul_exp_of_eval_ne_zero`, `0` is bounded above by the sum of
`Q_poly.logHeight`, `(∑ h, e h)` times the global form-matrix and grid constants, the concentrated
`D`-linear term `D * (μ * approxWeight S₀ c + Δ * approxAbsWeight S₀ c)`, and the degree-rounding
error `(∑ h, E h) * approxAbsWeight S₀ c`. -/
theorem subspace_key_inequality {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {Q_poly : MvPolynomial (κ × ι) K} {R : AbsoluteValue K ℝ → MvPolynomial (κ × ι) K}
    {e d : κ → ℕ} (hed : ∀ h, e h ≤ d h) {C D μ Δ B_z : ℝ} {Q E : κ → ℝ}
    {b : κ → τ → ι → K} {z : κ → τ → ℤ}
    (hR_inf : ∀ v : InfinitePlace K, (R v.1).IsMultiHomogeneous e)
    (heval_inf : ∀ v : InfinitePlace K,
      eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
        eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc_inf : ∀ (v : InfinitePlace K) (J : κ × ι →₀ ℕ),
      (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff_inf : ∀ (v : InfinitePlace K) (J : κ × ι →₀ ℕ),
      v ((R v.1).coeff J) ≤
        C ^ (∑ h, e h) * (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m))
    (hR_fin : ∀ v ∈ S₀, (R v.1).IsMultiHomogeneous e)
    (heval_fin : ∀ v ∈ S₀,
      eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
        eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc_fin : ∀ v ∈ S₀, ∀ J : κ × ι →₀ ℕ,
      (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff_fin : ∀ v ∈ S₀, ∀ J : κ × ι →₀ ℕ,
      v ((R v.1).coeff J) ≤
        (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m))
    (hQ : ∀ h, 0 < Q h) (hD0 : 0 ≤ D)
    (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    (hb : ∀ h a, b h a ∈ approxDomain S₀ L c (Q h))
    (hz : ∀ h a, |(z h a : ℝ)| ≤ B_z)
    (hne : eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly ≠ 0) :
    0 ≤ Q_poly.logHeight +
      (∑ h, (e h : ℝ)) *
        (Height.logHeight (refFamily S₀ L) +
          (Module.finrank ℚ K : ℝ) *
            Real.log (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z))) +
      D * (μ * approxWeight S₀ c + Δ * approxAbsWeight S₀ c) +
      (∑ h, E h) * approxAbsWeight S₀ c := by
  have hhref : 0 < Height.mulHeight (refFamily S₀ L) := Height.mulHeight_pos _
  have hhQ : 0 < Q_poly.mulHeight := Q_poly.mulHeight_pos
  have h1 := one_le_mulHeight_mul_exp_of_eval_ne_zero hed hR_inf heval_inf hconc_inf hcoeff_inf
    hR_fin heval_fin hconc_fin hcoeff_fin hQ hD0 hD hb hz hne
  have hX : 0 < (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^
      ((∑ h, e h) * Module.finrank ℚ K) := by
    by_contra! hle
    have hnonpos :
        (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z)) ^
            ((∑ h, e h) * Module.finrank ℚ K) *
          Height.mulHeight (refFamily S₀ L) ^ (∑ h, e h) *
          Q_poly.mulHeight *
          Real.exp (D * (μ * approxWeight S₀ c + Δ * approxAbsWeight S₀ c) +
            (∑ h, E h) * approxAbsWeight S₀ c) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hle (by positivity)) hhQ.le)
        (Real.exp_pos _).le
    linarith
  have hlog := Real.log_nonneg h1
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (by positivity) hhQ.ne',
    Real.log_mul hX.ne' (pow_pos hhref _).ne',
    Real.log_pow, Real.log_pow, Real.log_exp, Nat.cast_mul, Nat.cast_sum,
    ← Q_poly.logHeight_eq_log_mulHeight, ← Height.logHeight_eq_log_mulHeight] at hlog
  linarith

/-- **Contrapositive vanishing criterion.** Under the polynomial, concentration, and approximation
hypotheses of `TauCeti.NumberField.subspace_key_inequality`, if the global logarithmic upper bound
is strictly negative, then `Q_poly` must vanish at `h ↦ ∑ a, z h a • b h a`. -/
theorem eval_eq_zero_of_subspace_key_inequality {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {Q_poly : MvPolynomial (κ × ι) K} {R : AbsoluteValue K ℝ → MvPolynomial (κ × ι) K}
    {e d : κ → ℕ} (hed : ∀ h, e h ≤ d h) {C D μ Δ B_z : ℝ} {Q E : κ → ℝ}
    {b : κ → τ → ι → K} {z : κ → τ → ℤ}
    (hR_inf : ∀ v : InfinitePlace K, (R v.1).IsMultiHomogeneous e)
    (heval_inf : ∀ v : InfinitePlace K,
      eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
        eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc_inf : ∀ (v : InfinitePlace K) (J : κ × ι →₀ ℕ),
      (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff_inf : ∀ (v : InfinitePlace K) (J : κ × ι →₀ ℕ),
      v ((R v.1).coeff J) ≤
        C ^ (∑ h, e h) * (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m))
    (hR_fin : ∀ v ∈ S₀, (R v.1).IsMultiHomogeneous e)
    (heval_fin : ∀ v ∈ S₀,
      eval (fun p ↦ L v.1 p.2 (∑ a, z p.1 a • b p.1 a)) (R v.1) =
        eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly)
    (hconc_fin : ∀ v ∈ S₀, ∀ J : κ × ι →₀ ℕ,
      (∃ i, Δ < |(∑ h, (J (h, i) : ℝ) / d h) - μ|) → (R v.1).coeff J = 0)
    (hcoeff_fin : ∀ v ∈ S₀, ∀ J : κ × ι →₀ ℕ,
      v ((R v.1).coeff J) ≤
        (⨆ r, v (refFamily S₀ L r)) ^ (∑ h, e h) * ⨆ m, v (Q_poly.coeff m))
    (hQ : ∀ h, 0 < Q h) (hD0 : 0 ≤ D)
    (hD : ∀ h, |(d h : ℝ) * Real.log (Q h) - D| ≤ E h)
    (hb : ∀ h a, b h a ∈ approxDomain S₀ L c (Q h))
    (hz : ∀ h a, |(z h a : ℝ)| ≤ B_z)
    (hlt : Q_poly.logHeight +
      (∑ h, (e h : ℝ)) *
        (Height.logHeight (refFamily S₀ L) +
          (Module.finrank ℚ K : ℝ) *
            Real.log (C * (2 : ℝ) ^ Fintype.card ι * max 1 (Fintype.card τ * B_z))) +
      D * (μ * approxWeight S₀ c + Δ * approxAbsWeight S₀ c) +
      (∑ h, E h) * approxAbsWeight S₀ c < 0) :
    eval (fun p ↦ (∑ a, z p.1 a • b p.1 a) p.2) Q_poly = 0 := by
  by_contra hne
  exact not_le_of_gt hlt (subspace_key_inequality hed hR_inf heval_inf hconc_inf hcoeff_inf
    hR_fin heval_fin hconc_fin hcoeff_fin hQ hD0 hD hb hz hne)

end KeyInequality

/-! ### Examples -/

/-- `hne` (`eval ... Q_poly ≠ 0`) cannot be dropped in
`TauCeti.NumberField.subspace_key_inequality`: over `ℚ` in one block of one variable,
`Q_poly = X ((), ())` evaluated at `0` satisfies all multihomogeneity, concentration (`μ = 1`,
`Δ = 0`), and `approxDomain` hypotheses with `D = 2` and `c _ _ = -1`, while the right-hand side of
`subspace_key_inequality` equals `log 2 - 2 < 0`. -/
example :
    let S₀ : Finset (FinitePlace ℚ) := ∅
    let L : AbsoluteValue ℚ ℝ → Unit → Dual ℚ (Unit → ℚ) := fun _ _ ↦ LinearMap.proj ()
    let c : AbsoluteValue ℚ ℝ → Unit → ℝ := fun _ _ ↦ -1
    let Q_poly : MvPolynomial (Unit × Unit) ℚ := X ((), ())
    let e : Unit → ℕ := fun _ ↦ 1
    let Q : Unit → ℝ := fun _ ↦ Real.exp 2
    let b : Unit → Unit → Unit → ℚ := 0
    Q_poly.IsMultiHomogeneous e ∧
    (∀ h a, b h a ∈ approxDomain S₀ L c (Q h)) ∧
    ¬ 0 ≤ Q_poly.logHeight +
      (∑ h, (e h : ℝ)) *
        (Height.logHeight (refFamily S₀ L) +
          (Module.finrank ℚ ℚ : ℝ) *
            Real.log (1 * (2 : ℝ) ^ Fintype.card Unit * max 1 (Fintype.card Unit * 0))) +
      2 * (1 * approxWeight S₀ c + 0 * approxAbsWeight S₀ c) +
      (∑ _h : Unit, (0 : ℝ)) * approxAbsWeight S₀ c := by
  intro S₀ L c Q_poly e Q b
  refine ⟨?_, fun h _ ↦ ?_, ?_⟩
  · convert isMultiHomogeneous_X (R := ℚ) () ()
    ext ⟨⟩
    rfl
  · rw [mem_approxDomain]
    exact ⟨fun v i ↦ by simpa [L, b, Q] using Real.rpow_nonneg (Real.exp_pos 2).le _,
      by simp [S₀], by simp [b]⟩
  · have href_one : ∀ r, refFamily S₀ L r = 1 := by
      rintro (_ | ⟨v | ⟨v, hv⟩, ⟨⟩, ⟨⟩⟩)
      · rfl
      · have hM : LinearMap.toMatrix' (LinearMap.pi (L v.1)) = 1 := by
          ext ⟨⟩ ⟨⟩
          simp [L, LinearMap.toMatrix'_apply]
        simp [hM]
      · exact False.elim (notMem_empty v hv)
    have href_h : Height.logHeight (refFamily S₀ L) = 0 := by
      rw [logHeight_refFamily_eq]
      have hsup_inf (v : InfinitePlace ℚ) : (⨆ r, v (refFamily S₀ L r)) = 1 :=
        le_antisymm (ciSup_le fun r ↦ by rw [href_one]; exact (map_one v).le)
          (one_le_iSup_refFamily S₀ L v.1)
      have hsup_fin (v : FinitePlace ℚ) : (⨆ r, v (refFamily S₀ L r)) = 1 :=
        le_antisymm (ciSup_le fun r ↦ by rw [href_one]; exact (map_one v).le)
          (one_le_iSup_refFamily S₀ L v.1)
      simp_rw [hsup_inf, hsup_fin, Real.log_one]
      simp
    have hw : approxWeight S₀ c = -1 := by
      rw [approxWeight_def]
      dsimp only [S₀, c]
      simp_rw [sum_empty, add_zero, sum_const, card_univ, Fintype.card_unique, one_smul, mul_neg,
        mul_one, sum_neg_distrib, ← Nat.cast_sum, InfinitePlace.sum_mult_eq, Module.finrank_self,
        Nat.cast_one]
    rw [MvPolynomial.logHeight_X, href_h, hw, Module.finrank_self]
    dsimp only [e]
    simp only [univ_unique, sum_singleton, Nat.cast_one, Fintype.card_unique, pow_one, mul_zero,
      max_eq_left zero_le_one, mul_one, one_mul, zero_add]
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

end TauCeti.NumberField
