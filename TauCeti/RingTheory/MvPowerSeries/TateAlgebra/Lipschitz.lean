/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Lipschitz continuity of restricted power series evaluation in the argument

Let `R` and `S` be ultrametric normed commutative rings with `S` complete, let `φ : R →+* S` be
norm-nonincreasing, and let `c : Fin k → ℝ` be a positive polyradius. While
`MvPowerSeries.continuous_restrictedEval₂` shows that `f ↦ f(a)` is `1`-Lipschitz in the series `f`
at a fixed bounded point `a`, this file establishes Lipschitz and continuity properties in the
evaluation point `a` (and jointly in `(f, a)`):

* If `0 ≤ δ` and `‖b i - a i‖ ≤ δ * c i` for every `i`, then for every `f ∈ R{X/c}`,
  `‖f(b) - f(a)‖ ≤ ‖f‖ * δ` (`TauCeti.MvPowerSeries.norm_restrictedEval₂_sub_le_of_le`).
* On the closed unit polydisc `c = 1`, evaluation of `f` is `‖f‖`-Lipschitz in the point:
  `‖f(b) - f(a)‖ ≤ ‖f‖ * ‖b - a‖` (`TauCeti.MvPowerSeries.norm_restrictedEval₂_sub_le`).
* For every positive polyradius `c`, `a ↦ f(a)` is Lipschitz on
  `{a : Fin k → S // ∀ i, ‖a i‖ ≤ c i}` and `(f, a) ↦ f(a)` is jointly continuous.

Only positive exponents occur in nonconstant monomials, so no `NormOneClass` hypothesis on `R` or
`S` is needed.

## Main results

* `TauCeti.MvPowerSeries.norm_restrictedEval₂_sub_le_of_le` and
  `TauCeti.MvPowerSeries.norm_restrictedEval₂_sub_le`: relative and unit-polydisc Lipschitz bounds
  for restricted power-series evaluation in the point.
* `TauCeti.MvPowerSeries.lipschitzWith_restrictedEval₂_point` and
  `TauCeti.MvPowerSeries.lipschitzWith_restrictedEval₂_point_of_pos`: `LipschitzWith` bounds on
  `a ↦ f(a)`.
* `TauCeti.MvPowerSeries.continuous_restrictedEval₂_point` and
  `TauCeti.MvPowerSeries.continuous_restrictedEval₂_uncurry`: continuity in the point `a` and joint
  continuity in `(f, a)`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.1.4.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries
open scoped NNReal

section Helpers

/-- Ultrametric telescoping bound for finite products with coordinatewise bounds `M i` and relative
error `δ`. -/
private theorem norm_prod_sub_prod_le_mul {ι S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] {s : Finset ι} {f g : ι → S} {M : ι → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ M i) (hg : ∀ i ∈ s, ‖g i‖ ≤ M i)
    (hfg : ∀ i ∈ s, ‖f i - g i‖ ≤ δ * M i) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ δ * ∏ i ∈ s, M i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hδ]
  | insert j s hj ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hfg j (Finset.mem_insert_self j ∅)
    have hprod : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, M i :=
      (Finset.norm_prod_le' s hs f).trans
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i hi ↦
          hf i (Finset.mem_insert_of_mem hi))
    have htail := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi))
    have hMj : 0 ≤ M j := (norm_nonneg _).trans (hg j (Finset.mem_insert_self j s))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj]
    calc ‖f j * ∏ i ∈ s, f i - g j * ∏ i ∈ s, g i‖ =
          ‖(f j - g j) * ∏ i ∈ s, f i + g j * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖ := by
            congr 1
            ring
      _ ≤ max (‖f j - g j‖ * ‖∏ i ∈ s, f i‖)
            (‖g j‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖) :=
          (IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le_max (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ max (δ * M j * ∏ i ∈ s, M i) (M j * (δ * ∏ i ∈ s, M i)) :=
          max_le_max
            (mul_le_mul (hfg j (Finset.mem_insert_self j s)) hprod (norm_nonneg _)
              (mul_nonneg hδ hMj))
            (mul_le_mul (hg j (Finset.mem_insert_self j s)) htail (norm_nonneg _) hMj)
      _ = δ * (M j * ∏ i ∈ s, M i) := by
          rw [mul_assoc δ, mul_left_comm (M j) δ, max_self]

private theorem norm_pow_sub_pow_le_mul {S : Type*} [SeminormedCommRing S] [IsUltrametricDist S]
    {b a : S} {r δ : ℝ} (hδ : 0 ≤ δ) (hb : ‖b‖ ≤ r) (ha : ‖a‖ ≤ r) (hba : ‖b - a‖ ≤ δ * r)
    {n : ℕ} (hn : 0 < n) :
    ‖b ^ n - a ^ n‖ ≤ δ * r ^ n := by
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  have h1 : b ^ n = ∏ _i ∈ Finset.range n, b := by simp
  have h2 : a ^ n = ∏ _i ∈ Finset.range n, a := by simp
  rw [h1, h2]
  refine (_root_.TauCeti.norm_prod_sub_prod_le (mul_nonneg hδ hr) (fun _ _ ↦ hb) (fun _ _ ↦ ha)
    fun _ _ ↦ hba).trans_eq ?_
  rw [Finset.card_range, mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]

end Helpers

section Lipschitz

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S]
  {c : Fin k → ℝ} [∀ i, Fact (0 < c i)] (φ : R →+* S)

private theorem norm_weightedEvalTerm_sub_le (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) {b a : Fin k → S}
    (hb : ∀ i, ‖b i‖ ≤ c i) (ha : ∀ i, ‖a i‖ ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ)
    (hba : ∀ i, ‖b i - a i‖ ≤ δ * c i) (f : IsRestricted.subring (R := R) c) (t : Fin k →₀ ℕ) :
    ‖Huber.weightedEvalTerm φ b f t - Huber.weightedEvalTerm φ a f t‖ ≤ ‖f‖ * δ := by
  rw [Huber.weightedEvalTerm_def, Huber.weightedEvalTerm_def, ← mul_sub,
    ← Finsupp.prod_fintype t (b · ^ ·) fun _ ↦ pow_zero _,
    ← Finsupp.prod_fintype t (a · ^ ·) fun _ ↦ pow_zero _, Finsupp.prod, Finsupp.prod]
  rcases t.support.eq_empty_or_nonempty with h | _h
  · simp [h, mul_nonneg (norm_nonneg f) hδ]
  have hprod : ‖∏ i ∈ t.support, b i ^ t i - ∏ i ∈ t.support, a i ^ t i‖ ≤
      δ * ∏ i ∈ t.support, c i ^ t i :=
    norm_prod_sub_prod_le_mul hδ
      (fun i hi ↦ (norm_pow_le' _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hb i) _))
      (fun i hi ↦ (norm_pow_le' _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_pow_left₀ (norm_nonneg _) (ha i) _))
      (fun i hi ↦ norm_pow_sub_pow_le_mul hδ (hb i) (ha i) (hba i)
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)))
  calc ‖φ (coeff t (f : MvPowerSeries (Fin k) R)) *
          (∏ i ∈ t.support, b i ^ t i - ∏ i ∈ t.support, a i ^ t i)‖
      ≤ ‖φ (coeff t (f : MvPowerSeries (Fin k) R))‖ *
          ‖∏ i ∈ t.support, b i ^ t i - ∏ i ∈ t.support, a i ^ t i‖ := norm_mul_le _ _
    _ ≤ ‖coeff t (f : MvPowerSeries (Fin k) R)‖ * (δ * ∏ i ∈ t.support, c i ^ t i) :=
        mul_le_mul (hφ _) hprod (norm_nonneg _) (norm_nonneg _)
    _ = ‖coeff t (f : MvPowerSeries (Fin k) R)‖ * t.prod (c · ^ ·) * δ := by
        rw [Finsupp.prod]
        ring
    _ ≤ ‖f‖ * δ := mul_le_mul_of_nonneg_right (norm_coeff_mul_prod_le f t) hδ

variable [CompleteSpace S] (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖)

/-- **Relative Lipschitz bound for restricted series evaluation.** If `0 ≤ δ` and
`‖b i - a i‖ ≤ δ * c i` for every `i`, then `‖f(b) - f(a)‖ ≤ ‖f‖ * δ`. -/
theorem norm_restrictedEval₂_sub_le_of_le {b a : Fin k → S} (hb : ∀ i, ‖b i‖ ≤ c i)
    (ha : ∀ i, ‖a i‖ ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ) (hba : ∀ i, ‖b i - a i‖ ≤ δ * c i)
    (f : IsRestricted.subring (R := R) c) :
    ‖restrictedEval₂ φ b hφ hb f - restrictedEval₂ φ a hφ ha f‖ ≤ ‖f‖ * δ := by
  have hsum := (hasSum_restrictedEval₂ φ b hφ hb f).sub (hasSum_restrictedEval₂ φ a hφ ha f)
  rw [← hsum.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg f) hδ)
    (norm_weightedEvalTerm_sub_le φ hφ hb ha hδ hba f)

/-- **Unit-polydisc Lipschitz bound for restricted series evaluation.** For points `a, b` of the
closed unit polydisc `‖x i‖ ≤ 1`, `‖f(b) - f(a)‖ ≤ ‖f‖ * ‖b - a‖`. -/
theorem norm_restrictedEval₂_sub_le {b a : Fin k → S} (hb : ∀ i, ‖b i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ 1) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    ‖restrictedEval₂ φ b hφ hb f - restrictedEval₂ φ a hφ ha f‖ ≤ ‖f‖ * ‖b - a‖ :=
  norm_restrictedEval₂_sub_le_of_le φ hφ hb ha (norm_nonneg (b - a))
    (fun i ↦ by simpa using norm_le_pi_norm (b - a) i) f

/-- On the closed unit polydisc, `a ↦ f(a)` is `‖f‖₊`-Lipschitz. -/
theorem lipschitzWith_restrictedEval₂_point
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    LipschitzWith ‖f‖₊
      (fun a : {a : Fin k → S // ∀ i, ‖a i‖ ≤ 1} ↦ restrictedEval₂ φ a.1 hφ a.2 f) :=
  LipschitzWith.of_dist_le_mul fun b a ↦ by
    simpa [Subtype.dist_eq, dist_eq_norm] using norm_restrictedEval₂_sub_le φ hφ b.2 a.2 f

/-- On the closed polydisc of positive polyradius `c`, `a ↦ f(a)` is Lipschitz with constant
`‖f‖₊ * sup_i (c i)⁻¹`. -/
theorem lipschitzWith_restrictedEval₂_point_of_pos (f : IsRestricted.subring (R := R) c) :
    LipschitzWith (‖f‖₊ * Finset.univ.sup fun i : Fin k ↦ Real.toNNReal (c i)⁻¹)
      (fun a : {a : Fin k → S // ∀ i, ‖a i‖ ≤ c i} ↦ restrictedEval₂ φ a.1 hφ a.2 f) := by
  set C : ℝ≥0 := Finset.univ.sup fun i : Fin k ↦ Real.toNNReal (c i)⁻¹
  refine LipschitzWith.of_dist_le_mul fun b a ↦ ?_
  simp only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_mul, coe_nnNorm]
  refine (norm_restrictedEval₂_sub_le_of_le φ hφ b.2 a.2
    (mul_nonneg C.coe_nonneg (norm_nonneg (b.1 - a.1))) (fun i ↦ ?_) f).trans_eq
    (mul_assoc _ _ _).symm
  have hci : 0 < c i := Fact.out
  have hle : (c i)⁻¹ ≤ (C : ℝ) := by
    have hmem : Real.toNNReal (c i)⁻¹ ≤ C :=
      Finset.le_sup (f := fun j : Fin k ↦ Real.toNNReal (c j)⁻¹) (Finset.mem_univ i)
    exact (Real.coe_toNNReal (c i)⁻¹ (inv_nonneg.mpr hci.le)).symm.trans_le
      (NNReal.coe_le_coe.mpr hmem)
  have h1 : 1 ≤ (C : ℝ) * c i := by
    simpa [inv_mul_cancel₀ hci.ne'] using mul_le_mul_of_nonneg_right hle hci.le
  calc ‖b.1 i - a.1 i‖ ≤ ‖b.1 - a.1‖ * 1 := by simpa using norm_le_pi_norm (b.1 - a.1) i
    _ ≤ ‖b.1 - a.1‖ * ((C : ℝ) * c i) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (C : ℝ) * ‖b.1 - a.1‖ * c i := by ring

/-- For a fixed restricted power series `f ∈ R{X/c}`, the evaluation map `a ↦ f(a)` is continuous
on the closed polydisc `{a : Fin k → S // ∀ i, ‖a i‖ ≤ c i}`. -/
@[continuity, fun_prop]
theorem continuous_restrictedEval₂_point (f : IsRestricted.subring (R := R) c) :
    Continuous (fun a : {a : Fin k → S // ∀ i, ‖a i‖ ≤ c i} ↦ restrictedEval₂ φ a.1 hφ a.2 f) :=
  (lipschitzWith_restrictedEval₂_point_of_pos φ hφ f).continuous

/-- **Joint continuity of restricted power series evaluation** in `(f, a)` on
`R{X/c} × {a : Fin k → S // ∀ i, ‖a i‖ ≤ c i}`. -/
@[continuity, fun_prop]
theorem continuous_restrictedEval₂_uncurry :
    Continuous (fun p : IsRestricted.subring (R := R) c × {a : Fin k → S // ∀ i, ‖a i‖ ≤ c i} ↦
      restrictedEval₂ φ p.2.1 hφ p.2.2 p.1) := by
  rw [Metric.continuous_iff]
  rintro ⟨f, a⟩ ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuous_iff.mp
    (continuous_restrictedEval₂_point φ hφ f) a ε hε
  refine ⟨min (ε / 2) δ₁, lt_min (half_pos hε) hδ₁, fun ⟨g, b⟩ hgb ↦ ?_⟩
  rw [Prod.dist_eq, max_lt_iff] at hgb
  have hdiff : restrictedEval₂ φ b.1 hφ b.2 g - restrictedEval₂ φ a.1 hφ a.2 f =
      restrictedEval₂ φ b.1 hφ b.2 (g - f) +
        (restrictedEval₂ φ b.1 hφ b.2 f - restrictedEval₂ φ a.1 hφ a.2 f) := by
    rw [map_sub]
    ring
  rw [dist_eq_norm, hdiff]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · refine (norm_restrictedEval₂_le φ b.1 hφ b.2 (g - f)).trans_lt ?_
    exact (lt_of_eq_of_lt (dist_eq_norm g f).symm (lt_min_iff.mp hgb.1).1).trans (half_lt_self hε)
  · simpa [dist_eq_norm] using h₁ b (lt_min_iff.mp hgb.2).2

end Lipschitz

end TauCeti.MvPowerSeries
