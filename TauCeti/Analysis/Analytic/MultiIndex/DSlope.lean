/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Data.Finset.Basic

/-!
# Coordinatewise divided differences of analytic functions and formal power series

For a function `f : (ι → 𝕜) → F` on a finite product over a normed field `𝕜`, fixing every
coordinate except the `i`-th turns `f` into the one-variable slice `w ↦ f (Function.update z i w)`.
Its divided difference at a base coordinate `ζ : 𝕜`, evaluated back at `z i`, is
`z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)`: away from the hyperplane `z i = ζ` it is
the difference quotient `(z i - ζ)⁻¹ • (f z - f (Function.update z i ζ))`, and along the hyperplane
it is the partial derivative in the `i`-th coordinate.

At the level of formal power series, `FormalMultilinearSeries.fslopeUpdate p i` shifts the `i`-th
multi-index exponent down by one: its multi-index coefficient at `α` is
`p.mvCoeff (α + Pi.single i 1)` (`FormalMultilinearSeries.mvCoeff_fslopeUpdate`), its radius of
convergence is at least `p.radius` (`FormalMultilinearSeries.radius_le_radius_fslopeUpdate`), and
in a complete target space it represents the coordinate divided difference of `f` on the entire
ball where `f` has power series `p` (`HasFPowerSeriesOnBall.dslope_update`). Iterating `m` times
divides out `(z i - x i) ^ m` whenever `p.mvCoeff α = 0` for all `α` with `α i < m`
(`HasFPowerSeriesOnBall.eq_pow_sub_smul_iterate_dslope_update`,
`HasFPowerSeriesOnBall.exists_eq_pow_smul_of_mvCoeff_eq_zero`), and combining the hyperplane and
off-hyperplane cases shows that `z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)` is
analytic at `x` whenever `f` is analytic at both `x` and `Function.update x i ζ`
(`TauCeti.analyticAt_dslope_update`).

## Main definitions and results

* `FormalMultilinearSeries.fslopeUpdate`: the formal multilinear series obtained by coordinatewise
  divided difference in coordinate `i`, with evaluation formulas
  `FormalMultilinearSeries.fslopeUpdate_apply` and
  `FormalMultilinearSeries.fslopeUpdate_zero_apply`, algebraic simp lemmas `fslopeUpdate_zero`,
  `fslopeUpdate_add`, `fslopeUpdate_smul`, `fslopeUpdate_neg`, `fslopeUpdate_sub`, and one-variable
  compatibility `FormalMultilinearSeries.fslopeUpdate_eq_curryLeft_of_unique`.
* `FormalMultilinearSeries.smul_fslopeUpdate_apply`: the telescoping identity relating
  `z i • (p.fslopeUpdate i) n (fun _ ↦ z)` to
  `p (n + 1) (fun _ ↦ z) - p (n + 1) (fun _ ↦ Function.update z i 0)`.
* `FormalMultilinearSeries.mvCoeff_fslopeUpdate`,
  `FormalMultilinearSeries.mvCoeff_iterate_fslopeUpdate`,
  `FormalMultilinearSeries.apply_eq_zero_of_mvCoeff_eq_zero`: `(p.fslopeUpdate i).mvCoeff α` equals
  `p.mvCoeff (α + Pi.single i 1)`, iterating `m` times shifts `α` by `Pi.single i m`, and vanishing
  of `p.mvCoeff α` for `α i = 0` forces `p k (fun _ ↦ z) = 0` when `z i = 0`.
* `FormalMultilinearSeries.norm_fslopeUpdate_le`,
  `FormalMultilinearSeries.radius_le_radius_fslopeUpdate`,
  `FormalMultilinearSeries.radius_le_radius_iterate_fslopeUpdate`: operator-norm bound
  `‖(p.fslopeUpdate i) n‖ ≤ (n + 1) * ‖p (n + 1)‖` and radius monotonicity
  `p.radius ≤ (p.fslopeUpdate i).radius`.
* `HasFPowerSeriesOnBall.dslope_update`, `HasFPowerSeriesOnBall.iterate_dslope_update`,
  `HasFPowerSeriesAt.dslope_update`, `HasFPowerSeriesAt.iterate_dslope_update`: if `f` has power
  series `p` on `Metric.eball x r` in a complete space, its coordinate divided difference at `x i`
  has power series `p.fslopeUpdate i` on `Metric.eball x r`.
* `HasFPowerSeriesOnBall.eq_zero_of_mvCoeff_eq_zero`,
  `HasFPowerSeriesOnBall.eq_pow_sub_smul_iterate_dslope_update`,
  `HasFPowerSeriesOnBall.exists_eq_pow_smul_of_mvCoeff_eq_zero`: vanishing of `p.mvCoeff α` for
  `α i < m` factors `(z i - x i) ^ m` out of `f` on the whole ball `Metric.eball x r`.
* `TauCeti.analyticAt_dslope_update_of_ne`, `TauCeti.analyticAt_dslope_update_self`,
  `TauCeti.analyticAt_dslope_update`, `TauCeti.analyticAt_iterate_dslope_update_self`,
  `TauCeti.analyticAt_iterate_dslope_update`, `AnalyticOnNhd.dslope_update`,
  `AnalyticOnNhd.iterate_dslope_update`: analyticity of single and iterated coordinatewise divided
  differences.

## References

Coordinatewise power-series division in several variables is also part of Michail Karatarakis's
formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit `1d51891b5b`,
`Mathlib/NumberTheory/Transcendental/Baker/CoordinateDivision.lean`, Apache 2.0).
-/

public section

open Filter Finset Function Topology
open scoped ENNReal

/-! ### Formal coordinatewise divided differences -/

namespace FormalMultilinearSeries

section AnyIndex

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Classical in
/-- Continuous linear projection setting the `i`-th coordinate of `z : ι → 𝕜` to `0`. -/
private noncomputable def updateZeroCLM (𝕜 ι : Type*) [NormedField 𝕜] (i : ι) :
    (ι → 𝕜) →L[𝕜] (ι → 𝕜) where
  toFun z := Function.update z i 0
  map_add' x y := by ext j; by_cases hj : j = i <;> simp [hj]
  map_smul' c x := by ext j; by_cases hj : j = i <;> simp [hj]
  cont := continuous_pi fun j ↦ by
    by_cases hj : j = i
    · simpa [hj] using continuous_const
    · simpa [hj] using continuous_apply j

private theorem updateZeroCLM_apply [DecidableEq ι] (i : ι) (z : ι → 𝕜) :
    updateZeroCLM 𝕜 ι i z = Function.update z i 0 := by
  ext j
  simp [updateZeroCLM, Function.update_apply]

/-- Fix the `m`-th argument of a continuous multilinear map in `n + 1` variables without assuming
`[NontriviallyNormedField 𝕜]`. -/
private def curryMidApply {n : ℕ} (m : Fin (n + 1)) (f : (ι → 𝕜) [×n + 1]→L[𝕜] F) (x : ι → 𝕜) :
    (ι → 𝕜) [×n]→L[𝕜] F where
  toMultilinearMap := f.toMultilinearMap.curryMid m x
  cont := f.cont.comp <| continuous_pi <|
    Fin.succAboveCases m (by simpa using continuous_const) fun j ↦ by simpa using continuous_apply j

@[simp]
private theorem curryMidApply_apply {n : ℕ} (m : Fin (n + 1)) (f : (ι → 𝕜) [×n + 1]→L[𝕜] F)
    (x : ι → 𝕜) (w : Fin n → ι → 𝕜) :
    curryMidApply m f x w = f (m.insertNth x w) :=
  (rfl)

open Classical in
/-- The **formal coordinatewise divided difference** of a formal multilinear series `p` on `ι → 𝕜`
along coordinate `i`. In degree `n`, it sums over `m : Fin (n + 1)` the `(n + 1)`-multilinear map
`p (n + 1)` with `Pi.single i 1` inserted at slot `m`, the `i`-th coordinate zeroed in slots before
`m`, and the remaining slots left unchanged.

On the diagonal, `z i • (p.fslopeUpdate i) n (fun _ ↦ z)` telescopes to
`p (n + 1) (fun _ ↦ z) - p (n + 1) (fun _ ↦ Function.update z i 0)`
(`FormalMultilinearSeries.smul_fslopeUpdate_apply`), and at the multi-index level
`(p.fslopeUpdate i).mvCoeff α = p.mvCoeff (α + Pi.single i 1)`
(`FormalMultilinearSeries.mvCoeff_fslopeUpdate`). -/
noncomputable def fslopeUpdate (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) :
    FormalMultilinearSeries 𝕜 (ι → 𝕜) F := fun n ↦
  ∑ m : Fin (n + 1),
    (curryMidApply m (p (n + 1)) (Pi.single i 1)).compContinuousLinearMap fun j : Fin n ↦
      if j.castSucc < m then updateZeroCLM 𝕜 ι i else ContinuousLinearMap.id 𝕜 (ι → 𝕜)

/-- Pointwise formula for `FormalMultilinearSeries.fslopeUpdate` under `[DecidableEq ι]`. -/
theorem fslopeUpdate_apply [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι)
    (n : ℕ) (v : Fin n → ι → 𝕜) :
    (p.fslopeUpdate i) n v = ∑ m : Fin (n + 1),
      p (n + 1) (m.insertNth (Pi.single i 1) fun j ↦
        if j.castSucc < m then Function.update (v j) i 0 else v j) := by
  unfold fslopeUpdate
  simp only [_root_.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    curryMidApply_apply]
  -- Reconcile classical decidability on `ι` in `fslopeUpdate` with `[DecidableEq ι]`.
  refine Finset.sum_congr rfl fun m _ ↦ congrArg (p (n + 1)) ?_
  funext k
  refine Fin.succAboveCases m ?_ (fun j ↦ ?_) k
  · ext l; simp [Pi.single_apply]
  · simp only [Fin.insertNth_apply_succAbove]
    split_ifs
    · exact updateZeroCLM_apply i (v j)
    · rfl

/-- The constant term of `p.fslopeUpdate i` evaluates `p 1` in direction `Pi.single i 1`. -/
@[simp]
theorem fslopeUpdate_zero_apply [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι)
    (v : Fin 0 → ι → 𝕜) :
    (p.fslopeUpdate i) 0 v = p 1 (fun _ ↦ Pi.single i 1) := by
  rw [fslopeUpdate_apply, Fin.sum_univ_one]
  exact congrArg (p 1) (funext fun k ↦ by simp [Fin.eq_zero k])

/-- `fslopeUpdate` maps the zero series to `0`. -/
@[simp]
theorem fslopeUpdate_zero (i : ι) :
    (0 : FormalMultilinearSeries 𝕜 (ι → 𝕜) F).fslopeUpdate i = 0 := by
  classical
  ext n v
  simp [fslopeUpdate_apply]

/-- `fslopeUpdate` is additive in the formal multilinear series. -/
@[simp]
theorem fslopeUpdate_add (p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) :
    (p + q).fslopeUpdate i = p.fslopeUpdate i + q.fslopeUpdate i := by
  classical
  ext n v
  simp [fslopeUpdate_apply, Finset.sum_add_distrib]

/-- `fslopeUpdate` commutes with scalar multiplication. -/
@[simp]
theorem fslopeUpdate_smul (c : 𝕜) (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) :
    (c • p).fslopeUpdate i = c • p.fslopeUpdate i := by
  classical
  ext n v
  simp [fslopeUpdate_apply, Finset.smul_sum]

/-- `fslopeUpdate` commutes with negation. -/
@[simp]
theorem fslopeUpdate_neg (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) :
    (-p).fslopeUpdate i = -p.fslopeUpdate i := by
  classical
  ext n v
  simp [fslopeUpdate_apply]

/-- `fslopeUpdate` commutes with subtraction. -/
@[simp]
theorem fslopeUpdate_sub (p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) :
    (p - q).fslopeUpdate i = p.fslopeUpdate i - q.fslopeUpdate i := by
  classical
  ext n v
  simp [fslopeUpdate_apply, Finset.sum_sub_distrib]

/-- **Telescoping identity for `fslopeUpdate`**: multiplying the degree-`n` diagonal evaluation of
`p.fslopeUpdate i` by `z i` recovers the difference between `p (n + 1)` at `z` and `p (n + 1)` on
the hyperplane `z i = 0`. -/
theorem smul_fslopeUpdate_apply [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (i : ι) (n : ℕ) (z : ι → 𝕜) :
    z i • (p.fslopeUpdate i) n (fun _ ↦ z) =
      p (n + 1) (fun _ ↦ z) - p (n + 1) (fun _ ↦ Function.update z i 0) := by
  rw [fslopeUpdate_apply, Finset.smul_sum]
  set z₀ := Function.update z i 0
  -- Bind `P := p (n + 1)` at its multilinear map type so `rw` sees `DFunLike.coe`.
  let P : (ι → 𝕜) [×n + 1]→L[𝕜] F := p (n + 1)
  change ∑ m : Fin (n + 1), z i • P (m.insertNth (Pi.single i 1) fun j : Fin n ↦
      if j.castSucc < m then z₀ else z) = P (fun _ ↦ z) - P (fun _ ↦ z₀)
  have hz : z = z₀ + z i • Pi.single i 1 := by
    ext j; by_cases hj : j = i <;> simp [z₀, hj]
  have hstep (m : Fin (n + 1)) :
      z i • P (m.insertNth (Pi.single i 1) fun j : Fin n ↦
          if j.castSucc < m then z₀ else z) =
        P (fun k : Fin (n + 1) ↦ if (k : ℕ) < (m : ℕ) then z₀ else z) -
          P (fun k : Fin (n + 1) ↦ if (k : ℕ) < (m : ℕ) + 1 then z₀ else z) := by
    set w : Fin n → ι → 𝕜 := fun j ↦ if j.castSucc < m then z₀ else z
    have hu₁ : (fun k : Fin (n + 1) ↦ if (k : ℕ) < (m : ℕ) then z₀ else z) =
        m.insertNth (α := fun _ ↦ ι → 𝕜) z w := by
      funext k; refine Fin.succAboveCases m (by simp) (fun j ↦ ?_) k
      simp only [Fin.insertNth_apply_succAbove, w]
      by_cases hjm : j.castSucc < m
      · have hjm' : (j : ℕ) < m := hjm
        simp [hjm, hjm', m.succAbove_of_castSucc_lt j hjm]
      · have hle : (m : ℕ) ≤ j := not_lt.1 hjm
        simp [hjm, m.succAbove_of_le_castSucc j hle, not_lt.2 (hle.trans (Nat.le_succ j))]
    have hu₂ : (fun k : Fin (n + 1) ↦ if (k : ℕ) < (m : ℕ) + 1 then z₀ else z) =
        m.insertNth (α := fun _ ↦ ι → 𝕜) z₀ w := by
      funext k; refine Fin.succAboveCases m (by simp) (fun j ↦ ?_) k
      simp only [Fin.insertNth_apply_succAbove, w]
      by_cases hjm : j.castSucc < m
      · have hjm1 : (j : ℕ) < (m : ℕ) + 1 := Nat.lt_succ_of_lt hjm
        simp [hjm, hjm1, m.succAbove_of_castSucc_lt j hjm]
      · have hle : (m : ℕ) + 1 ≤ (j : ℕ) + 1 := Nat.succ_le_succ (not_lt.1 hjm)
        simp [hjm, m.succAbove_of_le_castSucc j (not_lt.1 hjm), not_lt.2 hle]
    rw [hu₁, hu₂, ← Fin.update_insertNth (α := fun _ ↦ ι → 𝕜) m z₀ z w,
      ← Fin.update_insertNth (α := fun _ ↦ ι → 𝕜) m z₀ (Pi.single i 1) w]
    conv_rhs => enter [1, 2]; rw [hz]
    rw [P.map_update_add, P.map_update_smul, Fin.update_insertNth, Fin.update_insertNth,
      add_sub_cancel_left]
  simp_rw [hstep]
  rw [Fin.sum_univ_eq_sum_range (fun r ↦
      P (fun k : Fin (n + 1) ↦ if (k : ℕ) < r then z₀ else z) -
        P (fun k : Fin (n + 1) ↦ if (k : ℕ) < r + 1 then z₀ else z)) (n + 1),
    Finset.sum_range_sub' (fun r ↦ P fun k : Fin (n + 1) ↦ if (k : ℕ) < r then z₀ else z) (n + 1)]
  simp only [not_lt_zero, Fin.is_lt, ↓reduceIte]

/-- Evaluating `(p.fslopeUpdate i) k` on a tuple of standard basis vectors `Pi.single (a l) 1`
drops every insertion slot `m` strictly after an occurrence of `i` in `a` (where the `i`-th
coordinate is zeroed). -/
private theorem fslopeUpdate_basis_eq_sum_filter [DecidableEq ι]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) {k : ℕ} (a : Fin k → ι) :
    (p.fslopeUpdate i) k (fun l ↦ Pi.single (a l) 1) =
      ∑ m ∈ (univ : Finset (Fin (k + 1))).filter (fun m ↦ ∀ l : Fin k, l.castSucc < m → a l ≠ i),
        p (k + 1) (fun r ↦ Pi.single (m.insertNth (α := fun _ ↦ ι) i a r) 1) := by
  rw [fslopeUpdate_apply]
  refine (Finset.sum_subset (Finset.filter_subset
    (fun m : Fin (k + 1) ↦ ∀ l : Fin k, l.castSucc < m → a l ≠ i) univ) ?_).symm.trans ?_
  · intro m _ hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_ne_iff] at hnot
    obtain ⟨l, hlm, hal⟩ := hnot
    refine (p (k + 1)).map_coord_zero (m.succAbove l) ?_
    simp only [Fin.insertNth_apply_succAbove, hlm, ↓reduceIte, hal]
    ext j
    by_cases hj : j = i <;> simp [hj]
  · refine Finset.sum_congr rfl fun m hm ↦ congrArg (p (k + 1)) ?_
    have hm' := (Finset.mem_filter.1 hm).2
    funext r
    refine Fin.succAboveCases m (by simp) (fun l ↦ ?_) r
    simp only [Fin.insertNth_apply_succAbove]
    split_ifs with hlm
    · ext j; by_cases hj : j = i <;> simp [hj, hm' l hlm]
    · rfl

end AnyIndex

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Multi-index coefficients of `fslopeUpdate`**: taking the formal divided difference in
coordinate `i` shifts the `i`-th multi-index exponent by `1`. -/
@[simp]
theorem mvCoeff_fslopeUpdate [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (i : ι) (α : ι → ℕ) :
    (p.fslopeUpdate i).mvCoeff α = p.mvCoeff (α + Pi.single i 1) := by
  set k := ∑ j, α j
  have hk1 : ∑ j : ι, (α + (Pi.single i 1 : ι → ℕ)) j = k + 1 := by
    simp [k, Finset.sum_add_distrib]
  have hcard_ins (m : Fin (k + 1)) (a : Fin k → ι) (j : ι) :
      Fintype.card {r : Fin (k + 1) // m.insertNth (α := fun _ ↦ ι) i a r = j} =
        Fintype.card {l : Fin k // a l = j} + (Pi.single i 1 : ι → ℕ) j := by
    simp only [Fintype.card_subtype, Finset.card_filter]
    rw [Fin.sum_univ_succAbove _ m, Fin.insertNth_apply_same, add_comm]
    simp [Fin.insertNth_apply_succAbove, Pi.single_apply, eq_comm]
  rw [mvCoeff_eq_sum (p.fslopeUpdate i) (k := k) rfl, mvCoeff_eq_sum p hk1,
    Finset.sum_congr rfl fun a _ ↦ p.fslopeUpdate_basis_eq_sum_filter i a, Finset.sum_sigma']
  refine Finset.sum_bij (fun am _ ↦ am.2.insertNth (α := fun _ ↦ ι) i am.1) ?_ ?_ ?_
    (fun _ _ ↦ rfl)
  · rintro ⟨a, m⟩ ham
    have ha := (Finset.mem_filter.1 (Finset.mem_sigma.1 ham).1).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
    intro j
    rw [hcard_ins, ha j]
  · rintro ⟨a₁, m₁⟩ h₁ ⟨a₂, m₂⟩ h₂ h
    have hnot_lt {b₁ b₂ : Fin k → ι} {n₁ n₂ : Fin (k + 1)}
        (heq : n₁.insertNth (α := fun _ ↦ ι) i b₁ = n₂.insertNth (α := fun _ ↦ ι) i b₂)
        (hn₂ : ∀ l : Fin k, l.castSucc < n₂ → b₂ l ≠ i) (hlt : n₁ < n₂) : False := by
      let l : Fin k := ⟨n₁, by omega⟩
      have hln : l.castSucc < n₂ := hlt
      have hsucc : n₂.succAbove l = n₁ := by ext; simp [n₂.succAbove_of_castSucc_lt l hln, l]
      have hi := congrFun heq n₁
      rw [Fin.insertNth_apply_same, ← hsucc, Fin.insertNth_apply_succAbove] at hi
      exact hn₂ l hln hi.symm
    have hm : m₁ = m₂ := le_antisymm
      (not_lt.1 (hnot_lt h.symm (Finset.mem_filter.1 (Finset.mem_sigma.1 h₁).2).2))
      (not_lt.1 (hnot_lt h (Finset.mem_filter.1 (Finset.mem_sigma.1 h₂).2).2))
    subst hm
    have ha : a₁ = a₂ := by simpa using congrArg (Fin.removeNth m₁) h
    subst ha
    rfl
  · intro b hb
    have hb' := (Finset.mem_filter.1 hb).2
    set sb := (univ : Finset (Fin (k + 1))).filter fun r ↦ b r = i
    have hcard : sb.card = α i + 1 := by simpa [sb, Fintype.card_subtype] using hb' i
    have hne : sb.Nonempty := Finset.card_pos.1 (by omega)
    let m := sb.min' hne
    have hbm : b m = i := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
    have hins : m.insertNth (α := fun _ ↦ ι) i (m.removeNth b) = b := by simp [hbm]
    refine ⟨⟨m.removeNth b, m⟩, Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun j ↦ ?_⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun l hlm hl ↦ ?_⟩⟩, hins⟩
    · have hcj := hcard_ins m (m.removeNth b) j
      rw [hins, hb' j] at hcj
      exact Nat.add_right_cancel hcj.symm
    · have hlt : m.succAbove l < m := (m.succAbove_of_castSucc_lt l hlm).trans_lt hlm
      exact not_lt.2 (Finset.min'_le sb (m.succAbove l) (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        hl⟩)) hlt

/-- Iterating `fslopeUpdate` `m` times in coordinate `i` shifts the `i`-th multi-index exponent
by `m`. -/
@[simp]
theorem mvCoeff_iterate_fslopeUpdate [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (i : ι) (m : ℕ) (α : ι → ℕ) :
    ((fslopeUpdate · i)^[m] p).mvCoeff α = p.mvCoeff (α + Pi.single i m) := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, mvCoeff_fslopeUpdate, add_assoc, ← Pi.single_add]

/-- If every multi-index coefficient of `p` of total degree `k` with `α i = 0` vanishes, then
the degree-`k` homogeneous term `p k (fun _ ↦ z)` vanishes whenever `z i = 0`. -/
theorem apply_eq_zero_of_mvCoeff_eq_zero (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {i : ι}
    {k : ℕ} (h0 : ∀ α : ι → ℕ, ∑ j, α j = k → α i = 0 → p.mvCoeff α = 0) {z : ι → 𝕜}
    (hz : z i = 0) : p k (fun _ ↦ z) = 0 := by
  classical
  rw [p.apply_eq_sum_mvCoeff]
  refine Finset.sum_eq_zero fun α hα ↦ ?_
  by_cases hαi : α i = 0
  · simp [h0 α (Finset.mem_piAntidiag.1 hα).1 hαi]
  · rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_smul]
    simp [hz, zero_pow hαi]

end NormedField

section Unique

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Unique ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- In one variable (`[Unique ι]`), `fslopeUpdate` agrees in every degree with currying `1` on the
left, matching `FormalMultilinearSeries.fslope`. -/
theorem fslopeUpdate_eq_curryLeft_of_unique
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (n : ℕ) :
    (p.fslopeUpdate default) n = (p (n + 1)).curryLeft 1 := by
  classical
  ext v
  rw [fslopeUpdate_apply, Finset.sum_eq_single (0 : Fin (n + 1))]
  · have h1 : (Pi.single default 1 : ι → 𝕜) = 1 := by
      ext j; simp [Unique.eq_default j]
    simp [h1]
  · intro m _ hm0
    rcases m with ⟨_ | m, hm⟩
    · exact False.elim (hm0 rfl)
    · let j₀ : Fin n := ⟨0, Nat.zero_lt_of_lt (Nat.lt_of_succ_lt_succ hm)⟩
      have hj₀ : j₀.castSucc < ⟨m + 1, hm⟩ := Nat.succ_pos m
      have hsucc : (⟨m + 1, hm⟩ : Fin (n + 1)).succAbove j₀ = 0 := by
        ext; simp [Fin.succAbove_of_castSucc_lt _ j₀ hj₀, j₀]
      refine (p (n + 1)).map_coord_zero 0 ?_
      rw [← hsucc, Fin.insertNth_apply_succAbove]
      ext k
      simp [hj₀, Unique.eq_default k]
  · simp

end Unique

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem norm_updateZeroCLM_apply_le (i : ι) (z : ι → 𝕜) :
    ‖updateZeroCLM 𝕜 ι i z‖ ≤ ‖z‖ := by
  classical
  rw [updateZeroCLM_apply]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j ↦ ?_
  by_cases hj : j = i <;> simp [hj, norm_le_pi_norm]

/-- Operator-norm bound for `fslopeUpdate`: each of the `n + 1` summands in degree `n` has norm at
most `‖p (n + 1)‖`. -/
theorem norm_fslopeUpdate_le (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) (n : ℕ) :
    ‖(p.fslopeUpdate i) n‖ ≤ (n + 1) * ‖p (n + 1)‖ := by
  classical
  have hsingle : ‖(Pi.single i 1 : ι → 𝕜)‖ ≤ 1 := by
    simp [Pi.norm_single]
  have hterm (m : Fin (n + 1)) :
      ‖((curryMidApply m (p (n + 1)) (Pi.single i 1)).compContinuousLinearMap fun j : Fin n ↦
        if j.castSucc < m then updateZeroCLM 𝕜 ι i else ContinuousLinearMap.id 𝕜 (ι → 𝕜))‖ ≤
        ‖p (n + 1)‖ := by
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun v ↦ ?_
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, curryMidApply_apply]
    refine ((p (n + 1)).le_opNorm _).trans ?_
    rw [Fin.prod_univ_succAbove _ m, Fin.insertNth_apply_same]
    calc ‖p (n + 1)‖ * (‖(Pi.single i 1 : ι → 𝕜)‖ * _)
        ≤ ‖p (n + 1)‖ * (1 * ∏ j : Fin n, ‖v j‖) := by
          gcongr with j
          simp only [Fin.insertNth_apply_succAbove]
          split_ifs
          · exact norm_updateZeroCLM_apply_le i (v j)
          · simp
      _ = ‖p (n + 1)‖ * ∏ j : Fin n, ‖v j‖ := by ring
  calc ‖(p.fslopeUpdate i) n‖
      ≤ ∑ m : Fin (n + 1), ‖p (n + 1)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ hterm m)
    _ = (n + 1) * ‖p (n + 1)‖ := by simp

/-- **Convergence radius of `fslopeUpdate`**: taking the formal coordinatewise divided difference
does not decrease the radius of convergence. -/
theorem radius_le_radius_fslopeUpdate (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (i : ι) :
    p.radius ≤ (p.fslopeUpdate i).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr0 hr ↦ ?_
  obtain ⟨s, hrs, hsr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
  have hrs' : (r : ℝ) < s := mod_cast hrs
  have hr_pos : 0 < (r : ℝ) := mod_cast hr0
  have hs_pos : 0 < (s : ℝ) := hr_pos.trans hrs'
  obtain ⟨C, _, hC⟩ := p.norm_mul_pow_le_of_lt_radius hsr
  have hq : ‖(r : ℝ) / s‖ < 1 := by
    rw [Real.norm_of_nonneg (div_nonneg hr_pos.le hs_pos.le)]
    exact (div_lt_one hs_pos).2 hrs'
  have hsum : Summable fun n : ℕ ↦
      C * (s : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ) * ((r : ℝ) / s) ^ n) := by
    refine (((summable_pow_mul_geometric_of_norm_lt_one 1 hq).add
      (summable_geometric_of_norm_lt_one hq)).congr fun n ↦ ?_).mul_left (C * (s : ℝ)⁻¹)
    rw [Nat.cast_add, Nat.cast_one, pow_one, add_mul, one_mul]
  refine (p.fslopeUpdate i).le_radius_of_summable (Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hr_pos.le n)) (fun n ↦ ?_) hsum)
  have hle : ‖(p.fslopeUpdate i) n‖ ≤ ((n + 1 : ℕ) : ℝ) * ‖p (n + 1)‖ := by
    simpa only [Nat.cast_add, Nat.cast_one] using p.norm_fslopeUpdate_le i n
  calc ‖(p.fslopeUpdate i) n‖ * (r : ℝ) ^ n
      ≤ ((n + 1 : ℕ) : ℝ) * ‖p (n + 1)‖ * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg hr_pos.le n)
    _ = ((n + 1 : ℕ) : ℝ) * ‖p (n + 1)‖ * ((s : ℝ) ^ n * (((r : ℝ) / s) ^ n)) := by
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero n hs_pos.ne')]
    _ = ((n + 1 : ℕ) : ℝ) * ‖p (n + 1)‖ *
          ((s : ℝ) ^ n * ((s : ℝ) * (s : ℝ)⁻¹) * (((r : ℝ) / s) ^ n)) := by
        rw [mul_inv_cancel₀ hs_pos.ne', mul_one]
    _ = ‖p (n + 1)‖ * (s : ℝ) ^ (n + 1) * (s : ℝ)⁻¹ *
          (((n + 1 : ℕ) : ℝ) * ((r : ℝ) / s) ^ n) := by
        rw [pow_succ]; ring
    _ ≤ C * (s : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ) * ((r : ℝ) / s) ^ n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hC (n + 1)) (inv_nonneg.2 hs_pos.le))
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg hr_pos.le hs_pos.le) _))

/-- Iterating `fslopeUpdate` does not decrease the radius of convergence. -/
theorem radius_le_radius_iterate_fslopeUpdate (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (i : ι) (m : ℕ) : p.radius ≤ ((fslopeUpdate · i)^[m] p).radius := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact (p.radius_le_radius_fslopeUpdate i).trans (ih _)

/-- On the hyperplane `y i = 0`, `fslopeUpdate` agrees term-by-term with Mathlib's formal
derivative series `p.derivSeries` evaluated in direction `Pi.single i 1`. -/
private theorem fslopeUpdate_apply_eq_derivSeries_of_eq_zero [DecidableEq ι]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {i : ι} (n : ℕ) {y : ι → 𝕜} (hyi : y i = 0) :
    (p.fslopeUpdate i) n (fun _ ↦ y) = p.derivSeries n (fun _ ↦ y) (Pi.single i 1) := by
  have hy0 : Function.update y i 0 = y := Function.update_eq_self_iff.2 hyi.symm
  rw [fslopeUpdate_apply]
  simp only [hy0, ite_self]
  simp only [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe, Function.comp_apply,
    FormalMultilinearSeries.changeOriginSeries, _root_.sum_apply,
    continuousMultilinearCurryFin1_apply, Fin.snoc_zero,
    FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  rw [TauCeti.sum_piecewise_eq_sum_update_of_card_eq_succ (by rw [Fintype.card_fin]; omega)]
  have hcast : ∀ (k : ℕ) (hk : n + 1 = k) (m : Fin (n + 1)),
      p (n + 1) (m.insertNth (Pi.single i 1) fun _ ↦ y) =
        p k (Function.update (fun _ ↦ y) (finCongr hk m) (Pi.single i 1)) := by
    rintro _ rfl m
    simp only [finCongr_refl, Equiv.refl_apply]
    refine congrArg (p (n + 1)) ?_
    funext k
    refine Fin.succAboveCases m (by simp) (fun j ↦ ?_) k
    simp [Fin.succAbove_ne]
  exact Fintype.sum_equiv (finCongr (Nat.add_comm n 1)) _ _
    (fun m ↦ hcast (1 + n) (Nat.add_comm n 1) m)

end NontriviallyNormedField

end FormalMultilinearSeries

/-! ### Power series and power division on open polydiscs -/

section PowerSeries

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace HasFPowerSeriesOnBall

/-- **Power series of the coordinatewise divided difference**: if `f` has power series `p` on
`Metric.eball x r` with values in a complete space `F`, then
`z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)` has power series
`p.fslopeUpdate i` on the same ball `Metric.eball x r`. -/
theorem dslope_update [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) (i : ι) :
    HasFPowerSeriesOnBall
      (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i))
      (p.fslopeUpdate i) x r where
  r_le := hf.r_le.trans (p.radius_le_radius_fslopeUpdate i)
  r_pos := hf.r_pos
  hasSum {y} hy := by
    rcases eq_or_ne (y i) 0 with hyi | hyi
    · have hxyi : (x + y) i = x i := by simp [hyi]
      have hmem : x + y ∈ Metric.eball x r := by simpa [eDist_eq_eNorm_sub] using hy
      have hupd (w : 𝕜) : Function.update (x + y) i w = x + y + (w - x i) • Pi.single i 1 := by
        ext j; by_cases hj : j = i <;> simp [hj, hyi]
      have hline : HasDerivAt (fun w ↦ Function.update (x + y) i w) (Pi.single i 1) (x i) := by
        simp_rw [hupd]
        simpa using (((hasDerivAt_id (x i)).sub_const (x i)).smul_const
          (Pi.single i (1 : 𝕜))).const_add (x + y)
      have hder : deriv (fun w ↦ f (Function.update (x + y) i w)) (x i) =
          fderiv 𝕜 f (x + y) (Pi.single i 1) :=
        ((hf.analyticAt_of_mem hmem).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (x i)
          hline (by simp [hxyi])).deriv
      rw [hxyi, dslope_same, hder]
      let eval_i : ((ι → 𝕜) →L[𝕜] F) →L[𝕜] F := ContinuousLinearMap.apply 𝕜 F (Pi.single i 1)
      have heval : HasSum (fun n ↦ eval_i (p.derivSeries n (fun _ ↦ y)))
          (eval_i (fderiv 𝕜 f (x + y))) :=
        eval_i.hasSum (hf.fderiv.hasSum hy)
      exact heval.congr_fun fun n ↦ p.fslopeUpdate_apply_eq_derivSeries_of_eq_zero n hyi
    · have hne : (x + y) i ≠ x i := by simpa using hyi
      have hy0 : Function.update y i 0 ∈ Metric.eball (0 : ι → 𝕜) r :=
        Metric.mem_eball.2 ((edist_pi_le_iff.2 fun j ↦ by
          by_cases hj : j = i
          · simp [hj]
          · simpa only [Function.update_of_ne hj] using edist_le_pi_edist y 0 j).trans_lt
          (Metric.mem_eball.1 hy))
      have hupd : Function.update (x + y) i (x i) = x + Function.update y i 0 := by
        ext j; by_cases hj : j = i <;> simp [hj]
      let g (n : ℕ) : F := p n (fun _ ↦ y) - p n (fun _ ↦ Function.update y i 0)
      have hg0 : g 0 = 0 := by
        simp [g, Subsingleton.elim (fun _ : Fin 0 ↦ y) (fun _ : Fin 0 ↦ Function.update y i 0)]
      have hshift : HasSum (fun n ↦ g (n + 1)) (f (x + y) - f (x + Function.update y i 0)) := by
        rw [hasSum_nat_add_iff 1, Finset.sum_range_one, hg0, add_zero]
        exact (hf.hasSum hy).sub (hf.hasSum hy0)
      have hsmul : HasSum (fun n ↦ (y i)⁻¹ • (y i • (p.fslopeUpdate i) n (fun _ ↦ y)))
          ((y i)⁻¹ • (f (x + y) - f (x + Function.update y i 0))) :=
        (hshift.congr_fun fun n ↦ p.smul_fslopeUpdate_apply i n y).const_smul (y i)⁻¹
      rw [dslope_of_ne _ hne, slope_def_module, Function.update_eq_self, hupd]
      have hxy_sub : ((x + y) i - x i)⁻¹ = (y i)⁻¹ := by simp
      rw [hxy_sub]
      exact hsmul.congr_fun fun n ↦ (inv_smul_smul₀ hyi _).symm

/-- Iterating the coordinatewise divided difference `m` times at `x i` has power series
`(fslopeUpdate · i)^[m] p` on `Metric.eball x r`. -/
theorem iterate_dslope_update [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) (i : ι) (m : ℕ) :
    HasFPowerSeriesOnBall
      (fun z : ι → 𝕜 ↦
        (Function.swap dslope (x i))^[m] (fun w ↦ f (Function.update z i w)) (z i))
      ((FormalMultilinearSeries.fslopeUpdate · i)^[m] p) x r := by
  induction m generalizing f p with
  | zero => simpa using hf
  | succ m ih =>
    simpa [Function.iterate_succ_apply] using ih (hf.dslope_update i)

/-- If every multi-index coefficient of `p` with `α i = 0` vanishes, then `f` vanishes on the
intersection of `Metric.eball x r` with the hyperplane `z i = x i`. -/
theorem eq_zero_of_mvCoeff_eq_zero
    {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) {i : ι}
    (h0 : ∀ α : ι → ℕ, α i = 0 → p.mvCoeff α = 0)
    {z : ι → 𝕜} (hz : z ∈ Metric.eball x r) (hzi : z i = x i) :
    f z = 0 := by
  have hy : z - x ∈ Metric.eball (0 : ι → 𝕜) r := by simpa [eDist_eq_eNorm_sub] using hz
  have hyi : (z - x) i = 0 := sub_eq_zero.2 hzi
  have hsum := hf.hasSum hy
  rw [add_sub_cancel] at hsum
  refine hsum.unique ?_
  convert hasSum_zero with k
  exact p.apply_eq_zero_of_mvCoeff_eq_zero (fun α _ hα ↦ h0 α hα) hyi

/-- **Coordinate power division with explicit quotient**: if `p.mvCoeff α = 0` whenever `α i < m`,
then on `Metric.eball x r`, `f z` factors as `(z i - x i) ^ m` times the `m`-th iterated divided
difference in coordinate `i`. -/
theorem eq_pow_sub_smul_iterate_dslope_update [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) {i : ι} {m : ℕ}
    (h0 : ∀ α : ι → ℕ, α i < m → p.mvCoeff α = 0)
    {z : ι → 𝕜} (hz : z ∈ Metric.eball x r) :
    f z = (z i - x i) ^ m •
      (Function.swap dslope (x i))^[m] (fun w ↦ f (Function.update z i w)) (z i) := by
  have hvan (k : ℕ) (hk : k < m) :
      (Function.swap dslope (x i))^[k] (fun w ↦ f (Function.update z i w)) (x i) = 0 := by
    have hu : Function.update z i (x i) ∈ Metric.eball x r :=
      Metric.mem_eball.2 ((edist_pi_le_iff.2 fun j ↦ by
        by_cases hj : j = i <;> simp [hj, edist_le_pi_edist]).trans_lt (Metric.mem_eball.1 hz))
    have hq := (hf.iterate_dslope_update i k).eq_zero_of_mvCoeff_eq_zero (i := i) ?_ hu
      (Function.update_self i (x i) z)
    · simpa using hq
    · intro β hβ
      rw [FormalMultilinearSeries.mvCoeff_iterate_fslopeUpdate]
      exact h0 _ (by simp [hβ, hk])
  simpa using (pow_sub_smul_iterate_dslope_of_zero m hvan (z i)).symm

/-- **Coordinate power division on a polydisc**: if `f` has power series `p` on `Metric.eball x r`
in a complete space `F` and `p.mvCoeff α = 0` whenever `α i < m`, then there is a function `g`
with power series `(fslopeUpdate · i)^[m] p` on `Metric.eball 0 r` (hence analytic there) such that
`f (x + z) = z i ^ m • g z` for all `z ∈ Metric.eball 0 r`. -/
theorem exists_eq_pow_smul_of_mvCoeff_eq_zero [CompleteSpace F]
    {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) (i : ι) {m : ℕ}
    (h0 : ∀ α : ι → ℕ, α i < m → p.mvCoeff α = 0) :
    ∃ g : (ι → 𝕜) → F,
      HasFPowerSeriesOnBall g ((FormalMultilinearSeries.fslopeUpdate · i)^[m] p) 0 r ∧
      ∀ z ∈ Metric.eball (0 : ι → 𝕜) r, f (x + z) = z i ^ m • g z := by
  classical
  have hG := hf.iterate_dslope_update i m
  refine ⟨fun z ↦ (Function.swap dslope (x i))^[m]
      (fun w ↦ f (Function.update (x + z) i w)) ((x + z) i),
    ⟨hG.r_le, hG.r_pos, fun {z} hz ↦ by simpa using hG.hasSum hz⟩, fun z hz ↦ ?_⟩
  have hxz : x + z ∈ Metric.eball x r := by simpa [eDist_eq_eNorm_sub] using hz
  simpa using hf.eq_pow_sub_smul_iterate_dslope_update h0 hxz

end HasFPowerSeriesOnBall

namespace HasFPowerSeriesAt

/-- Local germ form of `HasFPowerSeriesOnBall.dslope_update`. -/
theorem dslope_update [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜}
    (hf : HasFPowerSeriesAt f p x) (i : ι) :
    HasFPowerSeriesAt
      (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i))
      (p.fslopeUpdate i) x :=
  let ⟨r, hr⟩ := hf
  ⟨r, hr.dslope_update i⟩

/-- Local germ form of `HasFPowerSeriesOnBall.iterate_dslope_update`. -/
theorem iterate_dslope_update [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜}
    (hf : HasFPowerSeriesAt f p x) (i : ι) (m : ℕ) :
    HasFPowerSeriesAt
      (fun z : ι → 𝕜 ↦
        (Function.swap dslope (x i))^[m] (fun w ↦ f (Function.update z i w)) (z i))
      ((FormalMultilinearSeries.fslopeUpdate · i)^[m] p) x :=
  let ⟨r, hr⟩ := hf
  ⟨r, hr.iterate_dslope_update i m⟩

end HasFPowerSeriesAt

end PowerSeries

/-! ### Analyticity of coordinatewise divided differences -/

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- Off the hyperplane `z i = ζ` (`x i ≠ ζ`), the coordinatewise divided difference is the plain
difference quotient `(z i - ζ)⁻¹ • (f z - f (Function.update z i ζ))`, so it is analytic at `x`
without completeness of `F` whenever `f` is analytic at `x` and at `Function.update x i ζ`. -/
theorem analyticAt_dslope_update_of_ne [DecidableEq ι] {f : (ι → 𝕜) → F} (i : ι)
    {ζ : 𝕜} {x : ι → 𝕜} (hx : x i ≠ ζ) (hf : AnalyticAt 𝕜 f x)
    (hres : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  have hquot : AnalyticAt 𝕜
      (fun z : ι → 𝕜 ↦ (z i - ζ)⁻¹ • (f z - f (Function.update z i ζ))) x :=
    ((((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x).sub analyticAt_const).inv
      (sub_ne_zero.2 hx)).smul (hf.sub (hres.comp_of_eq ((analyticAt_id (z := x)).update i
        analyticAt_const) rfl))
  refine hquot.congr ?_
  filter_upwards [((continuous_apply i).tendsto x).eventually (eventually_ne_nhds hx)] with z hz
  simp [dslope_of_ne _ hz, slope_def_module]

/-- On the hyperplane `z i = x i`, analyticity of `f` at `x` alone suffices for the coordinatewise
divided difference at `x i` to be analytic at `x`. -/
theorem analyticAt_dslope_update_self [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F}
    (i : ι) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) x :=
  let ⟨_, hp⟩ := hf
  (hp.dslope_update i).analyticAt

/-- **Analyticity of the coordinatewise divided difference**: if `f` is analytic at `x` and at its
projection `Function.update x i ζ` onto the hyperplane `z i = ζ`, then
`z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)` is analytic at `x`, both across the
hyperplane `z i = ζ` and off it. -/
theorem analyticAt_dslope_update [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F} (i : ι)
    (ζ : 𝕜) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hres : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  rcases eq_or_ne (x i) ζ with rfl | hx
  · exact analyticAt_dslope_update_self i hf
  · exact analyticAt_dslope_update_of_ne i hx hf hres

/-- On the hyperplane `z i = x i`, every iterated coordinatewise divided difference at `x i` is
analytic at `x` as soon as `f` is analytic at `x`. -/
theorem analyticAt_iterate_dslope_update_self [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F}
    (i : ι) (m : ℕ) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦
      (Function.swap dslope (x i))^[m] (fun w ↦ f (Function.update z i w)) (z i)) x :=
  let ⟨_, hp⟩ := hf
  (hp.iterate_dslope_update i m).analyticAt

/-- Iterating the coordinatewise divided difference `m` times at `ζ` preserves analyticity at `x`
whenever `f` is analytic at `x` and at `Function.update x i ζ`. -/
theorem analyticAt_iterate_dslope_update [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F}
    (i : ι) (ζ : 𝕜) (m : ℕ) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hres : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦
      (Function.swap dslope ζ)^[m] (fun w ↦ f (Function.update z i w)) (z i)) x := by
  induction m generalizing f with
  | zero => simpa using hf
  | succ m ih =>
    have hf₁ : AnalyticAt 𝕜
        (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x :=
      analyticAt_dslope_update i ζ hf hres
    have hres₁ : AnalyticAt 𝕜
        (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i))
        (Function.update x i ζ) := by
      simpa using analyticAt_dslope_update_self i hres
    simpa [Function.iterate_succ_apply] using ih hf₁ hres₁

end TauCeti

namespace AnalyticOnNhd

/-- If `f` is analytic on a neighborhood of `s` and projecting the `i`-th coordinate to `ζ` maps
`s` into `s`, then the coordinatewise divided difference at `ζ` is analytic on a neighborhood of
`s`. -/
theorem dslope_update [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F} {s : Set (ι → 𝕜)}
    (hf : AnalyticOnNhd 𝕜 f s) (i : ι) {ζ : 𝕜} (hs : ∀ x ∈ s, Function.update x i ζ ∈ s) :
    AnalyticOnNhd 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s :=
  fun x hx ↦ TauCeti.analyticAt_dslope_update i ζ (hf x hx) (hf _ (hs x hx))

/-- Iterating the coordinatewise divided difference `m` times at `ζ` preserves `AnalyticOnNhd` on
any set `s` stable under `x ↦ Function.update x i ζ`. -/
theorem iterate_dslope_update [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F}
    {s : Set (ι → 𝕜)} (hf : AnalyticOnNhd 𝕜 f s) (i : ι) {ζ : 𝕜} (m : ℕ)
    (hs : ∀ x ∈ s, Function.update x i ζ ∈ s) :
    AnalyticOnNhd 𝕜 (fun z : ι → 𝕜 ↦
      (Function.swap dslope ζ)^[m] (fun w ↦ f (Function.update z i w)) (z i)) s :=
  fun x hx ↦ TauCeti.analyticAt_iterate_dslope_update i ζ m (hf x hx) (hf _ (hs x hx))

end AnalyticOnNhd

end Analytic
