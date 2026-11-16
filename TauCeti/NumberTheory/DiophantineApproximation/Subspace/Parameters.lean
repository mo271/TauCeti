/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Parameter schedules and multidegree bounds for the Subspace Theorem

Schmidt's proof of the Subspace Theorem (Bombieri–Gubler, Theorem 7.5.13) chooses four coupled
parameters from the ambient dimension `n`, the distinct-form count `f`, the approximation slack
`ε > 0`, and an upper bound `A` on `approxAbsWeight S₀ c`:

1. **Concentration slack** `subspaceSlack n ε A`: small enough that when an exponent family `c` has
   negative weight `approxWeight S₀ c ≤ -(ε / 2)` and absolute weight `approxAbsWeight S₀ c ≤ A`,
   an index-concentrated monomial with center `m / n` and deviation `2 * m * (n - 1) * η` still has
   strictly negative total exponent `≤ -(m : ℝ) * (ε / (4 * n))`
   (`TauCeti.NumberField.mul_approxWeight_add_mul_approxAbsWeight_le`).
2. **Block count** `subspaceBlockCount n f ε A`: large enough that Siegel's lemma has exponentially
   fewer vanishing equations than multihomogeneous monomials,
   `4 * log (2 * f) < n * (n + 1) * (subspaceSlack n ε A) ^ 2 * subspaceBlockCount n f ε A`
   (`TauCeti.NumberField.four_mul_log_lt_subspaceBlockCount`).
3. **Degree-decay ratio** `subspaceRatio m η`: lies in `(0, 1 / 2]` and satisfies Roth's index
   budget `2 * m * σ ^ (1 / 2 ^ (m - 1)) < m * (η / 2)`
   (`TauCeti.NumberField.two_mul_rpow_subspaceRatio_lt`).
4. **Rounded multidegree** `fun h ↦ ⌊D / log (Q h)⌋₊`: along a level chain with
   `2 * σ⁻¹ * log (Q h) ≤ log (Q (h + 1))` and `2 * log (Q h) ≤ D`, the degrees are positive,
   approximate `D / log (Q h)` within `log (Q h)` (`abs_floor_div_log_mul_sub_le`), decay by `σ`
   at each step (`cast_floor_div_log_le_mul`), and sum to at most `2 * D / log (Q 0)`
   (`sum_floor_div_log_le`).

## Main definitions

* `TauCeti.NumberField.subspaceSlack n ε A`: concentration slack `η`.
* `TauCeti.NumberField.subspaceBlockCount n f ε A`: number of blocks `m ≥ 1`.
* `TauCeti.NumberField.subspaceRatio m η`: degree ratio `σ = min (1 / 2) (η / 5) ^ (2 ^ (m - 1))`.

## Main results

* `TauCeti.NumberField.subspaceSlack_pos`, `TauCeti.NumberField.subspaceBlockCount_pos`,
  `TauCeti.NumberField.four_mul_log_lt_subspaceBlockCount`: positivity and auxiliary-polynomial
  threshold.
* `TauCeti.NumberField.subspaceRatio_pos`, `TauCeti.NumberField.subspaceRatio_le_one_half`,
  `TauCeti.NumberField.two_mul_rpow_subspaceRatio_lt`: Roth-lemma degree-ratio conditions.
* `TauCeti.NumberField.mul_approxWeight_add_mul_approxAbsWeight_le`: negative net exponent for
  concentrated monomials.
* `TauCeti.NumberField.floor_div_log_pos`, `TauCeti.NumberField.abs_floor_div_log_mul_sub_le`,
  `TauCeti.NumberField.cast_floor_div_log_le_mul`, `TauCeti.NumberField.sum_floor_div_log_le`:
  multidegree rounding, decay, and total-degree bounds along a rapidly growing chain of levels.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  proof of Theorem 7.5.13.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  Ann. of Math. (2) 156 (2002), §6.
-/

public section

open Finset

namespace TauCeti.NumberField

open _root_.NumberField

/-! ### Concentration slack, block count, and degree ratio -/

/-- **Concentration slack** `η = ε / (8 * n * max 1 ((n - 1) * A))` in the Subspace Theorem. Taking
`max 1 ((n - 1) * A)` in the denominator keeps `subspaceSlack n ε A > 0` even when `n = 1` or
`A ≤ 0`. -/
noncomputable def subspaceSlack (n : ℕ) (ε A : ℝ) : ℝ :=
  ε / (8 * n * max 1 (((n - 1 : ℕ) : ℝ) * A))

theorem subspaceSlack_def (n : ℕ) (ε A : ℝ) :
    subspaceSlack n ε A = ε / (8 * n * max 1 (((n - 1 : ℕ) : ℝ) * A)) :=
  (rfl)

theorem subspaceSlack_pos {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    0 < subspaceSlack n ε A := by
  rw [subspaceSlack_def]
  have : 0 < max (1 : ℝ) (((n - 1 : ℕ) : ℝ) * A) := zero_lt_one.trans_le (le_max_left _ _)
  positivity

/-- **Number of blocks** `m` in the multihomogeneous auxiliary polynomial, chosen strictly above
`4 * max 0 (log (2 * f)) / (n * (n + 1) * (subspaceSlack n ε A) ^ 2)`. -/
noncomputable def subspaceBlockCount (n f : ℕ) (ε A : ℝ) : ℕ :=
  ⌊4 * max 0 (Real.log (2 * f)) / (n * (n + 1) * subspaceSlack n ε A ^ 2)⌋₊ + 1

theorem subspaceBlockCount_def (n f : ℕ) (ε A : ℝ) :
    subspaceBlockCount n f ε A =
      ⌊4 * max 0 (Real.log (2 * f)) / (n * (n + 1) * subspaceSlack n ε A ^ 2)⌋₊ + 1 :=
  (rfl)

theorem subspaceBlockCount_pos (n f : ℕ) (ε A : ℝ) : 0 < subspaceBlockCount n f ε A :=
  Nat.succ_pos _

instance instNeZeroSubspaceBlockCount (n f : ℕ) (ε A : ℝ) :
    NeZero (subspaceBlockCount n f ε A) :=
  ⟨(subspaceBlockCount_pos n f ε A).ne'⟩

/-- `subspaceBlockCount n f ε A` satisfies the block-count threshold required by Siegel's lemma for
`f` distinct linear forms in `n` variables at concentration slack `subspaceSlack n ε A`. -/
theorem four_mul_log_lt_subspaceBlockCount {n : ℕ} (hn : 0 < n) (f : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : ℝ) :
    4 * Real.log (2 * f) <
      n * (n + 1) * subspaceSlack n ε A ^ 2 * subspaceBlockCount n f ε A := by
  have hη : 0 < subspaceSlack n ε A := subspaceSlack_pos hn hε A
  have hden : 0 < (n : ℝ) * (n + 1) * subspaceSlack n ε A ^ 2 := by positivity
  have hlt := Nat.lt_floor_add_one
    (4 * max 0 (Real.log (2 * f)) / ((n : ℝ) * (n + 1) * subspaceSlack n ε A ^ 2))
  have hmul := (div_lt_iff₀ hden).mp hlt
  calc 4 * Real.log (2 * f)
      ≤ 4 * max 0 (Real.log (2 * f)) := by gcongr; exact le_max_right _ _
    _ < (⌊4 * max 0 (Real.log (2 * f)) / ((n : ℝ) * (n + 1) * subspaceSlack n ε A ^ 2)⌋₊ + 1 : ℝ) *
          ((n : ℝ) * (n + 1) * subspaceSlack n ε A ^ 2) := hmul
    _ = n * (n + 1) * subspaceSlack n ε A ^ 2 * subspaceBlockCount n f ε A := by
        rw [subspaceBlockCount_def, Nat.cast_add, Nat.cast_one]
        ring

/-- **Degree-decay ratio** `σ = min (1 / 2) (η / 5) ^ (2 ^ (m - 1))` for Roth's lemma in `m`
blocks. -/
noncomputable def subspaceRatio (m : ℕ) (η : ℝ) : ℝ :=
  min (1 / 2) (η / 5) ^ (2 ^ (m - 1) : ℕ)

theorem subspaceRatio_def (m : ℕ) (η : ℝ) :
    subspaceRatio m η = min (1 / 2) (η / 5) ^ (2 ^ (m - 1) : ℕ) :=
  (rfl)

theorem subspaceRatio_pos (m : ℕ) {η : ℝ} (hη : 0 < η) : 0 < subspaceRatio m η := by
  rw [subspaceRatio_def]
  exact pow_pos (lt_min (by norm_num) (by positivity)) _

theorem subspaceRatio_le_one_half (m : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    subspaceRatio m η ≤ 1 / 2 := by
  rw [subspaceRatio_def]
  have h0 : 0 ≤ min (1 / 2) (η / 5) := le_min (by norm_num) (by positivity)
  have h1 : min (1 / 2) (η / 5) ≤ 1 := (min_le_left _ _).trans (by norm_num)
  exact (pow_le_of_le_one h0 h1 (pow_ne_zero _ two_ne_zero)).trans (min_le_left _ _)

/-- `subspaceRatio m η` keeps Roth's index bound `2 * m * σ ^ (1 / 2 ^ (m - 1))` strictly below
`m * (η / 2)`, leaving the remaining `m * (η / 2)` of the derivative budget `m * η` for the
subspace integer-grid step. -/
theorem two_mul_rpow_subspaceRatio_lt {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    2 * (m : ℝ) * subspaceRatio m η ^ ((1 : ℝ) / 2 ^ (m - 1)) < (m : ℝ) * (η / 2) := by
  have hb0 : 0 ≤ min (1 / 2) (η / 5) := le_min (by norm_num) (by positivity)
  have hrpow : subspaceRatio m η ^ ((1 : ℝ) / 2 ^ (m - 1)) = min (1 / 2) (η / 5) := by
    rw [subspaceRatio_def, ← Real.rpow_natCast, ← Real.rpow_mul hb0, Nat.cast_pow, Nat.cast_ofNat,
      mul_one_div_cancel (by positivity), Real.rpow_one]
  rw [hrpow]
  have hlt : 2 * min (1 / 2) (η / 5) < η / 2 := by
    calc 2 * min (1 / 2) (η / 5) ≤ 2 * (η / 5) := by gcongr; exact min_le_right _ _
      _ < η / 2 := by linarith
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith

/-- **Net exponent bound at concentration slack `subspaceSlack`.** If `0 ≤ ε`,
`approxWeight S₀ c ≤ -(ε / 2)`, and `approxAbsWeight S₀ c ≤ A`, then with center `m / card ι` and
deviation `2 * m * (card ι - 1) * subspaceSlack (card ι) ε A` the concentrated exponent combination
is at most `-(m : ℝ) * (ε / (4 * card ι))`. -/
theorem mul_approxWeight_add_mul_approxAbsWeight_le {K ι : Type*} [Field K] [NumberField K]
    [Fintype ι] {S₀ : Finset (FinitePlace K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε A : ℝ} (hε : 0 ≤ ε) (hc : approxWeight S₀ c ≤ -(ε / 2))
    (habs : approxAbsWeight S₀ c ≤ A) (m : ℕ) :
    ((m : ℝ) / Fintype.card ι) * approxWeight S₀ c +
        (2 * (m : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) *
          subspaceSlack (Fintype.card ι) ε A) * approxAbsWeight S₀ c ≤
      -(m : ℝ) * (ε / (4 * Fintype.card ι)) := by
  set n : ℕ := Fintype.card ι
  rcases eq_or_ne n 0 with hn0 | hn0
  · simp [hn0]
  have _ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  let M : ℝ := max 1 (((n - 1 : ℕ) : ℝ) * A)
  have _ : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have _ : 0 ≤ subspaceSlack n ε A := by
    rw [subspaceSlack_def]
    change 0 ≤ ε / (8 * n * M)
    positivity
  have _ : 0 ≤ approxAbsWeight S₀ c := by
    rw [approxAbsWeight_def]
    positivity
  have hterm1 : ((m : ℝ) / n) * approxWeight S₀ c ≤ -((m : ℝ) * (ε / (2 * n))) := by
    have : ((m : ℝ) / n) * approxWeight S₀ c ≤ ((m : ℝ) / n) * (-(ε / 2)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    linarith [show ((m : ℝ) / n) * (-(ε / 2)) = -((m : ℝ) * (ε / (2 * n))) by ring]
  have hterm2 :
      (2 * (m : ℝ) * ((n - 1 : ℕ) : ℝ) * subspaceSlack n ε A) * approxAbsWeight S₀ c ≤
        (m : ℝ) * (ε / (4 * n)) := by
    calc (2 * (m : ℝ) * ((n - 1 : ℕ) : ℝ) * subspaceSlack n ε A) * approxAbsWeight S₀ c
        ≤ (2 * (m : ℝ) * ((n - 1 : ℕ) : ℝ) * subspaceSlack n ε A) * A :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = 2 * (m : ℝ) * subspaceSlack n ε A * (((n - 1 : ℕ) : ℝ) * A) := by ring
      _ ≤ 2 * (m : ℝ) * subspaceSlack n ε A * M :=
          mul_le_mul_of_nonneg_left (le_max_right 1 _) (by positivity)
      _ = (m : ℝ) * (ε / (4 * n)) := by
          rw [subspaceSlack_def]
          change 2 * (m : ℝ) * (ε / (8 * n * M)) * M = (m : ℝ) * (ε / (4 * n))
          field_simp
          ring
  exact (add_le_add hterm1 hterm2).trans_eq (by ring)

/-! ### Rounded multidegree along a rapidly growing chain of levels -/

/-- When `1 < Q` and `log Q ≤ D`, the rounded degree `⌊D / log Q⌋₊` is positive. -/
theorem floor_div_log_pos {Q D : ℝ} (hQ : 1 < Q) (hD : Real.log Q ≤ D) :
    0 < ⌊D / Real.log Q⌋₊ :=
  Nat.floor_pos.mpr ((one_le_div (Real.log_pos hQ)).mpr hD)

/-- For `1 < Q` and `0 ≤ D`, rounding `D / log Q` down to `⌊D / log Q⌋₊` changes `d * log Q` from
`D` by at most `log Q`. -/
theorem abs_floor_div_log_mul_sub_le {Q D : ℝ} (hQ : 1 < Q) (hD0 : 0 ≤ D) :
    |(⌊D / Real.log Q⌋₊ : ℝ) * Real.log Q - D| ≤ Real.log Q := by
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have hle : (⌊D / Real.log Q⌋₊ : ℝ) * Real.log Q ≤ D :=
    (le_div_iff₀ hlog).mp (Nat.floor_le (div_nonneg hD0 hlog.le))
  have hlt : D < ((⌊D / Real.log Q⌋₊ : ℝ) + 1) * Real.log Q :=
    (div_lt_iff₀ hlog).mp (Nat.lt_floor_add_one _)
  rw [abs_le]
  constructor <;> linarith

/-- **Degree-ratio step.** If `1 < Q`, `2 * log Q ≤ D`, `0 < σ`, and `2 * σ⁻¹ * log Q ≤ log Q'`,
then `⌊D / log Q'⌋₊ ≤ σ * ⌊D / log Q⌋₊`, matching the hypothesis of Roth's lemma. -/
theorem cast_floor_div_log_le_mul {Q Q' D σ : ℝ} (hQ : 1 < Q) (hD : 2 * Real.log Q ≤ D)
    (hσ : 0 < σ) (hgap : 2 * σ⁻¹ * Real.log Q ≤ Real.log Q') :
    (⌊D / Real.log Q'⌋₊ : ℝ) ≤ σ * ⌊D / Real.log Q⌋₊ := by
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have hD0 : 0 ≤ D := (by positivity : 0 ≤ 2 * Real.log Q).trans hD
  have hlog' : 0 < Real.log Q' := (by positivity : 0 < 2 * σ⁻¹ * Real.log Q).trans_le hgap
  have hhalf : D / (2 * Real.log Q) ≤ ⌊D / Real.log Q⌋₊ := by
    have h2 : 2 ≤ D / Real.log Q := (le_div_iff₀ hlog).mpr (by linarith)
    have hlt := Nat.lt_floor_add_one (D / Real.log Q)
    have hident : D / (2 * Real.log Q) = (D / Real.log Q) / 2 := by ring
    linarith
  calc (⌊D / Real.log Q'⌋₊ : ℝ)
      ≤ D / Real.log Q' := Nat.floor_le (div_nonneg hD0 hlog'.le)
    _ ≤ D / (2 * σ⁻¹ * Real.log Q) :=
        div_le_div_of_nonneg_left hD0 (by positivity) hgap
    _ = σ * (D / (2 * Real.log Q)) := by field_simp
    _ ≤ σ * ⌊D / Real.log Q⌋₊ := mul_le_mul_of_nonneg_left hhalf hσ.le

/-- **Geometric bound on the total degree.** If a sequence of levels `Q : Fin m → ℝ` (`0 < m`) has
`1 < Q 0` and `2 * log (Q h) ≤ log (Q j)` at every step `j = h + 1`, then for `0 ≤ D` the sum of
`⌊D / log (Q h)⌋₊` is at most `2 * D / log (Q 0)`. -/
theorem sum_floor_div_log_le {m : ℕ} (hm : 0 < m) {Q : Fin m → ℝ}
    (hQ0 : 1 < Q ⟨0, hm⟩)
    (hstep : ∀ h j : Fin m, (j : ℕ) = h + 1 → 2 * Real.log (Q h) ≤ Real.log (Q j))
    {D : ℝ} (hD0 : 0 ≤ D) :
    ∑ h : Fin m, (⌊D / Real.log (Q h)⌋₊ : ℝ) ≤ 2 * D / Real.log (Q ⟨0, hm⟩) := by
  have hlog0 : 0 < Real.log (Q ⟨0, hm⟩) := Real.log_pos hQ0
  have hpow : ∀ k (hk : k < m), 2 ^ k * Real.log (Q ⟨0, hm⟩) ≤ Real.log (Q ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      calc (2 : ℝ) ^ (k + 1) * Real.log (Q ⟨0, hm⟩)
          = 2 * (2 ^ k * Real.log (Q ⟨0, hm⟩)) := by ring
        _ ≤ 2 * Real.log (Q ⟨k, Nat.lt_of_succ_lt hk⟩) :=
            mul_le_mul_of_nonneg_left (ih (Nat.lt_of_succ_lt hk)) (by norm_num)
        _ ≤ Real.log (Q ⟨k + 1, hk⟩) := hstep ⟨k, Nat.lt_of_succ_lt hk⟩ ⟨k + 1, hk⟩ rfl
  calc ∑ h : Fin m, (⌊D / Real.log (Q h)⌋₊ : ℝ)
      ≤ ∑ h : Fin m, (D / Real.log (Q ⟨0, hm⟩)) * (1 / 2 : ℝ) ^ (h : ℕ) :=
        sum_le_sum fun h _ ↦ by
          have hlogh : 0 < Real.log (Q h) :=
            (by positivity : 0 < (2 : ℝ) ^ (h : ℕ) * Real.log (Q ⟨0, hm⟩)).trans_le (hpow h h.isLt)
          calc (⌊D / Real.log (Q h)⌋₊ : ℝ)
              ≤ D / Real.log (Q h) := Nat.floor_le (div_nonneg hD0 hlogh.le)
            _ ≤ D / ((2 : ℝ) ^ (h : ℕ) * Real.log (Q ⟨0, hm⟩)) :=
                div_le_div_of_nonneg_left hD0 (by positivity) (hpow h h.isLt)
            _ = (D / Real.log (Q ⟨0, hm⟩)) * (1 / 2 : ℝ) ^ (h : ℕ) := by
                rw [one_div, inv_pow]
                ring
    _ = (D / Real.log (Q ⟨0, hm⟩)) * ∑ k ∈ range m, (1 / 2 : ℝ) ^ k := by
        rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun k ↦ (1 / 2 : ℝ) ^ k) m]
    _ ≤ (D / Real.log (Q ⟨0, hm⟩)) * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hD0 hlog0.le)
        rw [geom_sum_eq (by norm_num),
          show ((1 / 2 : ℝ) ^ m - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2 : ℝ) ^ m by ring]
        have : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
        linarith
    _ = 2 * D / Real.log (Q ⟨0, hm⟩) := by ring

/-! ### Examples -/

/-- `1 < Q` cannot be weakened to `1 ≤ Q` in `TauCeti.NumberField.abs_floor_div_log_mul_sub_le`: at
`Q = 1` and `D = 1`, `log 1 = 0`, so the left-hand side is `1` while the right-hand side is `0`. -/
example : ¬ |(⌊(1 : ℝ) / Real.log 1⌋₊ : ℝ) * Real.log 1 - 1| ≤ Real.log 1 := by
  simp

end TauCeti.NumberField
