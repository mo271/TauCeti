/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Strictly positive elements and σ-unital C⋆-algebras

An element `h` of a (possibly nonunital) complex C⋆-algebra `A` is *strictly positive* if `0 ≤ h`
and every nonzero positive continuous linear functional `φ : A →P[ℂ] ℂ` satisfies `0 < (φ h).re`
(`TauCeti.CStarAlgebra.IsStrictlyPositive`).

Associated to any `h : A` is the canonical sequence of positive strict contractions
`approxUnitOfElement h n = cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹) ((n + 1 : ℝ≥0) • h)` (which in
the unitization `A⁺¹` equals `h * (h + (n + 1)⁻¹)⁻¹`). For `0 ≤ h`, this sequence is monotone
increasing (`monotone_approxUnitOfElement`), satisfies
`‖h - approxUnitOfElement h n * h‖ ≤ 1 / (n + 1)`, and establishes the four-way characterization
of strict positivity (`isStrictlyPositive_tfae`):

1. `IsStrictlyPositive h`;
2. `Dense (Set.range fun a : A => h * a * h)` (the hereditary range `h A h` is dense in `A`);
3. `Dense (Set.range fun a : A => h * a)` (the right ideal `h A` is dense in `A`);
4. `(Filter.map (approxUnitOfElement h) atTop).IsIncreasingApproximateUnit`.

As a consequence, a C⋆-algebra is *σ-unital* — meaning it admits a strictly positive element — if
and only if it admits a (monotone) sequential increasing approximate unit, if and only if it admits
a sequential left or right approximate unit (`exists_isStrictlyPositive_tfae`). Every separable
C⋆-algebra is σ-unital (`exists_isStrictlyPositive_of_separableSpace`,
`exists_monotone_seq_isIncreasingApproximateUnit_of_separableSpace`).

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Section II.4.2.
* Gert K. Pedersen, *C*-Algebras and Their Automorphism Groups*, Section 3.10.
* Gerard J. Murphy, *C*-Algebras and Operator Theory*, Section 3.1.
-/

public section

noncomputable section

open Filter Set Topology Unitization
open scoped CStarAlgebra ComplexOrder NNReal

namespace TauCeti.CStarAlgebra

section Basic

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-! ### Strictly positive elements -/

/-- An element `h` of a (possibly nonunital) C⋆-algebra `A` is *strictly positive* if `0 ≤ h` and
every nonzero positive continuous linear functional takes a strictly positive real value at `h`. -/
def IsStrictlyPositive (h : A) : Prop :=
  0 ≤ h ∧ ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re

/-- Every strictly positive element is nonnegative. -/
theorem IsStrictlyPositive.nonneg {h : A} (hh : IsStrictlyPositive h) : 0 ≤ h :=
  hh.1

/-- Every nonzero positive functional has strictly positive real part on a strictly positive
element. -/
theorem IsStrictlyPositive.re_apply_pos {h : A} (hh : IsStrictlyPositive h) {φ : A →P[ℂ] ℂ}
    (hφ : φ ≠ 0) : 0 < (φ h).re :=
  hh.2 φ hφ

/-- Every nonzero positive functional takes a strictly positive value on a strictly positive
element. -/
theorem IsStrictlyPositive.apply_pos {h : A} (hh : IsStrictlyPositive h) {φ : A →P[ℂ] ℂ}
    (hφ : φ ≠ 0) : 0 < φ h := by
  have h0 : 0 ≤ φ h := φ.map_nonneg hh.1
  rw [Complex.lt_def]
  exact ⟨hh.2 φ hφ, (Complex.le_def.1 h0).2⟩

/-- No nonzero positive functional vanishes on a strictly positive element. -/
theorem IsStrictlyPositive.apply_ne_zero {h : A} (hh : IsStrictlyPositive h) {φ : A →P[ℂ] ℂ}
    (hφ : φ ≠ 0) : φ h ≠ 0 :=
  (hh.apply_pos hφ).ne'

/-- A nonnegative element is strictly positive iff no nonzero positive functional vanishes on it. -/
theorem isStrictlyPositive_iff_apply_ne_zero {h : A} :
    IsStrictlyPositive h ↔ 0 ≤ h ∧ ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → φ h ≠ 0 := by
  refine ⟨fun hh => ⟨hh.1, fun φ hφ => hh.apply_ne_zero hφ⟩, fun ⟨hh, hne⟩ => ⟨hh, fun φ hφ => ?_⟩⟩
  have h0 : 0 ≤ φ h := φ.map_nonneg hh
  obtain ⟨hre, him⟩ := Complex.le_def.1 h0
  refine lt_of_le_of_ne hre fun heq => hne φ hφ ?_
  exact Complex.ext heq.symm him.symm

/-- Any element dominating a strictly positive element is strictly positive. -/
theorem IsStrictlyPositive.mono {h₁ h₂ : A} (hh₁ : IsStrictlyPositive h₁) (hle : h₁ ≤ h₂) :
    IsStrictlyPositive h₂ :=
  ⟨hh₁.1.trans hle, fun φ hφ =>
    (hh₁.2 φ hφ).trans_le (Complex.le_def.1 (φ.mono hle)).1⟩

end Basic

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The unit `1` of a unital C⋆-algebra is strictly positive. -/
theorem isStrictlyPositive_one {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    IsStrictlyPositive (1 : B) := by
  refine ⟨zero_le_one, fun φ hφ => ?_⟩
  have h1 : φ 1 = (‖(φ : B →L[ℂ] ℂ)‖ : ℂ) := (φ.ofReal_opNorm_eq_map_one).symm
  rw [h1, Complex.ofReal_re, norm_pos_iff]
  intro h0
  exact hφ (PositiveContinuousLinearMap.ext fun x => congrArg (fun f : B →L[ℂ] ℂ => f x) h0)

/-- The element `0` is strictly positive if and only if the C⋆-algebra is trivial. -/
theorem isStrictlyPositive_zero_iff : IsStrictlyPositive (0 : A) ↔ Subsingleton A := by
  refine ⟨fun h0 => ?_, fun _ => ⟨le_rfl, fun φ hφ =>
    absurd (PositiveContinuousLinearMap.ext fun a => by
      rw [Subsingleton.elim a 0, map_zero, map_zero]) hφ⟩⟩
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  obtain ⟨ω, hω_norm, -, -⟩ :=
    exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq (a := (0 : A)) le_rfl
  have hω_ne : ω ≠ 0 := fun h => by
    have : ‖(ω : A →L[ℂ] ℂ)‖ = 0 := by simp [h]
    linarith
  have hpos := h0.2 ω hω_ne
  simp at hpos

/-! ### Canonical approximate unit generated by an element -/

/-- The canonical sequence of positive strict contractions generated by `h : A`, given by
`cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹) ((n + 1 : ℝ≥0) • h)`. In `A⁺¹`, this equals
`h * (h + (n + 1)⁻¹)⁻¹`. -/
def approxUnitOfElement (h : A) (n : ℕ) : A :=
  cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹) ((n + 1 : ℝ≥0) • h)

/-- Every term of `approxUnitOfElement h` is nonnegative. -/
theorem approxUnitOfElement_nonneg (h : A) (n : ℕ) : 0 ≤ approxUnitOfElement h n :=
  cfcₙ_nonneg_of_predicate

/-- Every term of `approxUnitOfElement h` is a strict contraction. -/
theorem norm_approxUnitOfElement_lt_one (h : A) (n : ℕ) : ‖approxUnitOfElement h n‖ < 1 :=
  norm_cfcₙ_one_sub_one_add_inv_lt_one _

/-- Every term of `approxUnitOfElement h` has norm at most `1`. -/
theorem norm_approxUnitOfElement_le_one (h : A) (n : ℕ) : ‖approxUnitOfElement h n‖ ≤ 1 :=
  (norm_approxUnitOfElement_lt_one h n).le

/-- For `0 ≤ h`, the sequence `approxUnitOfElement h` is monotone increasing. -/
theorem monotone_approxUnitOfElement {h : A} (hh : 0 ≤ h) : Monotone (approxUnitOfElement h) := by
  intro m n hmn
  have hm : 0 ≤ ((m + 1 : ℝ≥0) • h) := smul_nonneg (by positivity) hh
  have hle : ((m + 1 : ℝ≥0) • h) ≤ ((n + 1 : ℝ≥0) • h) :=
    smul_le_smul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hmn 1) hh
  exact CFC.monotoneOn_one_sub_one_add_inv hm (hm.trans hle) hle

/-- For `0 ≤ h`, each term `approxUnitOfElement h n` is bounded above by `(n + 1 : ℝ≥0) • h`. -/
theorem approxUnitOfElement_le_smul {h : A} (hh : 0 ≤ h) (n : ℕ) :
    approxUnitOfElement h n ≤ ((n + 1 : ℝ≥0) • h) := by
  have hk : 0 ≤ ((n + 1 : ℝ≥0) • h) := smul_nonneg (by positivity) hh
  calc approxUnitOfElement h n
      = cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹) ((n + 1 : ℝ≥0) • h) := rfl
    _ ≤ cfcₙ (id : ℝ≥0 → ℝ≥0) ((n + 1 : ℝ≥0) • h) := by
      refine cfcₙ_mono (fun x _ => ?_)
      rw [id_eq, ← NNReal.coe_le_coe, NNReal.coe_sub (inv_le_one_of_one_le₀ le_self_add),
        NNReal.coe_one, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one, sub_le_iff_le_add]
      have hpos : (0 : ℝ) < 1 + x := by positivity
      rw [← mul_le_mul_iff_right₀ hpos]
      field_simp
      nlinarith [sq_nonneg (x : ℝ)]
    _ = ((n + 1 : ℝ≥0) • h) := cfcₙ_id ℝ≥0 _

/-- In the unitization `A⁺¹`, `1 - approxUnitOfElement h n` is given by the functional calculus
`cfc (fun y : ℝ≥0 => (1 + (n + 1 : ℝ≥0) • y)⁻¹) (h : A⁺¹)`. -/
private theorem one_sub_inr_approxUnitOfElement {h : A} (hh : 0 ≤ h) (n : ℕ) :
    (1 : A⁺¹) - (Unitization.inr (approxUnitOfElement h n) : A⁺¹) =
      cfc (fun y : ℝ≥0 => (1 + (n + 1 : ℝ≥0) • y)⁻¹) (h : A⁺¹) := by
  have hh' : 0 ≤ (h : A⁺¹) := inr_nonneg_iff.2 hh
  have hg : Continuous (fun y : ℝ≥0 => 1 - (1 + y)⁻¹) := by
    rw [← continuousOn_univ]
    fun_prop (disch := intro _ _; positivity)
  have h1 : (Unitization.inr (approxUnitOfElement h n) : A⁺¹) =
      cfc (fun y : ℝ≥0 => 1 - (1 + (n + 1 : ℝ≥0) • y)⁻¹) (h : A⁺¹) := by
    rw [approxUnitOfElement, nnreal_cfcₙ_eq_cfc_inr _ _ (by simp [tsub_self]), inr_smul,
      ← cfc_comp_smul _ _ _ hg.continuousOn hh']
  rw [h1, ← cfc_one (R := ℝ≥0) (h : A⁺¹),
    ← cfc_tsub _ _ (h : A⁺¹) (by simp) hh' (by fun_prop)
      (by fun_prop (disch := intro _ _; positivity))]
  congr! 1 with y _
  simp [tsub_tsub_cancel_of_le]

/-- Quantitative estimate `‖h - approxUnitOfElement h n * h‖ ≤ 1 / (n + 1)` for `0 ≤ h`. -/
theorem norm_sub_approxUnitOfElement_mul_le {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ‖h - approxUnitOfElement h n * h‖ ≤ 1 / (n + 1 : ℝ) := by
  have hh' : 0 ≤ (h : A⁺¹) := inr_nonneg_iff.2 hh
  have hcont : ContinuousOn (fun y : ℝ≥0 => (1 + (n + 1 : ℝ≥0) • y)⁻¹) (spectrum ℝ≥0 (h : A⁺¹)) :=
    ContinuousOn.inv₀ (by fun_prop) fun _ _ => by positivity
  have heq : ((h - approxUnitOfElement h n * h : A) : A⁺¹) =
      cfc (fun y : ℝ≥0 => (1 + (n + 1 : ℝ≥0) • y)⁻¹ * y) (h : A⁺¹) := by
    calc ((h - approxUnitOfElement h n * h : A) : A⁺¹)
        = (1 - (Unitization.inr (approxUnitOfElement h n) : A⁺¹)) * (h : A⁺¹) := by
          rw [inr_sub, inr_mul, sub_mul, one_mul]
      _ = cfc (fun y : ℝ≥0 => (1 + (n + 1 : ℝ≥0) • y)⁻¹) (h : A⁺¹) *
            cfc (fun y : ℝ≥0 => y) (h : A⁺¹) := by
          rw [one_sub_inr_approxUnitOfElement hh n, cfc_id' ℝ≥0 (h : A⁺¹)]
      _ = cfc (fun y : ℝ≥0 => (1 + (n + 1 : ℝ≥0) • y)⁻¹ * y) (h : A⁺¹) := by
          rw [← cfc_mul _ _ (h : A⁺¹) hcont (continuousOn_id' _)]
  rw [← norm_inr (𝕜 := ℂ), heq]
  have hnn : ‖cfc (fun y : ℝ≥0 => (1 + (n + 1 : ℝ≥0) • y)⁻¹ * y) (h : A⁺¹)‖₊ ≤
      ((n + 1 : ℝ≥0))⁻¹ := by
    refine nnNorm_cfc_nnreal_le fun y _ => ?_
    rw [inv_mul_le_iff₀ (by positivity)]
    have hmul : y ≤ ((n + 1 : ℝ≥0))⁻¹ * (1 + (n + 1 : ℝ≥0) * y) := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      exact le_add_of_nonneg_left (by positivity)
    simpa [smul_eq_mul, mul_comm] using hmul
  simpa [one_div] using NNReal.coe_le_coe.2 hnn

/-- For `0 ≤ h`, `approxUnitOfElement h n * h → h` as `n → ∞`. -/
theorem tendsto_approxUnitOfElement_mul_self {h : A} (hh : 0 ≤ h) :
    Tendsto (fun n => approxUnitOfElement h n * h) atTop (𝓝 h) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by rw [norm_sub_rev]; exact norm_sub_approxUnitOfElement_mul_le hh n)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- For `0 ≤ h`, every product `approxUnitOfElement h n * approxUnitOfElement h k` factors on both
sides through `h`. -/
private theorem exists_mul_eq_approxUnitOfElement_mul {h : A} (hh : 0 ≤ h) (n k : ℕ) :
    ∃ q : A, h * q = approxUnitOfElement h n * approxUnitOfElement h k ∧
      q * h = approxUnitOfElement h n * approxUnitOfElement h k := by
  let fn (m : ℕ) : ℝ≥0 → ℝ≥0 := fun y => 1 - (1 + (m + 1 : ℝ≥0) * y)⁻¹
  let g : ℝ≥0 → ℝ≥0 := fun y =>
    (n + 1 : ℝ≥0) * (1 + (n + 1 : ℝ≥0) * y)⁻¹ * (1 - (1 + (k + 1 : ℝ≥0) * y)⁻¹)
  have hg_cont : ContinuousOn g (quasispectrum ℝ≥0 h) := by
    dsimp [g]
    fun_prop (disch := intro _ _; positivity)
  have hg0 : g 0 = 0 := by simp [g, tsub_self]
  have hfn_eq (m : ℕ) : approxUnitOfElement h m = cfcₙ (fn m) h := by
    have hg' : Continuous (fun y : ℝ≥0 => 1 - (1 + y)⁻¹) := by
      rw [← continuousOn_univ]
      fun_prop (disch := intro _ _; positivity)
    rw [approxUnitOfElement, ← cfcₙ_comp_smul _ _ _ hg'.continuousOn (by simp [tsub_self]) hh]
    simp only [fn, smul_eq_mul]
  have hfn_cont (m : ℕ) : ContinuousOn (fn m) (quasispectrum ℝ≥0 h) := by
    dsimp [fn]
    fun_prop (disch := intro _ _; positivity)
  have hfn0 (m : ℕ) : fn m 0 = 0 := by simp [fn, tsub_self]
  have hpt (y : ℝ≥0) : y * g y = fn n y * fn k y := by
    dsimp [g, fn]
    have h1 : (1 - (1 + (n + 1 : ℝ≥0) * y)⁻¹ : ℝ≥0) =
        y * ((n + 1 : ℝ≥0) * (1 + (n + 1 : ℝ≥0) * y)⁻¹) := by
      rw [tsub_eq_iff_eq_add_of_le (inv_le_one_of_one_le₀ le_self_add)]
      field_simp [add_comm]
      ring
    rw [h1]
    ring
  refine ⟨cfcₙ g h, ?_, ?_⟩
  · rw [hfn_eq n, hfn_eq k,
      ← cfcₙ_mul (fn n) (fn k) h (hfn_cont n) (hfn0 n) (hfn_cont k) (hfn0 k)]
    nth_rw 1 [← cfcₙ_id' ℝ≥0 h]
    rw [← cfcₙ_mul (fun y : ℝ≥0 => y) g h (continuousOn_id' _) rfl hg_cont hg0]
    congr! 1 with y _
    exact hpt y
  · rw [hfn_eq n, hfn_eq k,
      ← cfcₙ_mul (fn n) (fn k) h (hfn_cont n) (hfn0 n) (hfn_cont k) (hfn0 k)]
    nth_rw 2 [← cfcₙ_id' ℝ≥0 h]
    rw [← cfcₙ_mul g (fun y : ℝ≥0 => y) h hg_cont hg0 (continuousOn_id' _) rfl]
    congr! 1 with y _
    simpa only [mul_comm y (g y)] using hpt y

/-! ### Four-way characterization of strictly positive elements -/

/-- If `h` is strictly positive, then `approxUnitOfElement h` is an increasing approximate unit
of `A`. -/
private theorem isIncreasingApproximateUnit_approxUnitOfElement_of_isStrictlyPositive
    {h : A} (hh : IsStrictlyPositive h) :
    (Filter.map (approxUnitOfElement h) atTop).IsIncreasingApproximateUnit := by
  have hnonneg : ∀ᶠ e in Filter.map (approxUnitOfElement h) atTop, 0 ≤ e :=
    eventually_map.2 (.of_forall (approxUnitOfElement_nonneg h))
  have hnorm : ∀ᶠ e in Filter.map (approxUnitOfElement h) atTop, ‖e‖ ≤ 1 :=
    eventually_map.2 (.of_forall (norm_approxUnitOfElement_le_one h))
  have hright : ∀ a : A, Tendsto (· * a) (Filter.map (approxUnitOfElement h) atTop) (𝓝 a) := by
    refine _root_.CStarAlgebra.tendsto_mul_right_of_forall_nonneg_tendsto fun a ha ha_norm => ?_
    rw [tendsto_map'_iff]
    change Tendsto (fun n => approxUnitOfElement h n * a) atTop (𝓝 a)
    -- Let `c n = 1 - (e n : A⁺¹)` and `y n = c n * a * c n`. By the C⋆-identity and `a * a ≤ a`,
    -- `‖a - e n * a‖ ^ 2 ≤ ‖y n‖`, so it suffices to prove `‖y n‖ → 0`.
    let c (n : ℕ) : A⁺¹ := 1 - (Unitization.inr (approxUnitOfElement h n) : A⁺¹)
    have hc_icc (n : ℕ) : c n ∈ Set.Icc (0 : A⁺¹) 1 :=
      Set.sub_mem_Icc_zero_iff_right.2 <|
        _root_.CStarAlgebra.inr_mem_Icc_iff_norm_le.2
          ⟨approxUnitOfElement_nonneg h n, norm_approxUnitOfElement_le_one h n⟩
    have hc_nonneg (n : ℕ) : 0 ≤ c n := (hc_icc n).1
    have hc_norm (n : ℕ) : ‖c n‖ ≤ 1 :=
      (_root_.CStarAlgebra.mem_Icc_iff_norm_le_one.1 (hc_icc n)).2
    have hc_star (n : ℕ) : star (c n) = c n := (hc_nonneg n).isSelfAdjoint.star_eq
    let y (n : ℕ) : A⁺¹ := c n * (a : A⁺¹) * c n
    have hy_nonneg (n : ℕ) : 0 ≤ y n := by
      simpa only [y, hc_star n] using star_left_conjugate_nonneg (inr_nonneg_iff.2 ha) (c n)
    have hsq (n : ℕ) : ‖approxUnitOfElement h n * a - a‖ ^ 2 ≤ ‖y n‖ := by
      rw [norm_sub_rev, ← norm_inr (𝕜 := ℂ), inr_sub, inr_mul]
      have hca : (a : A⁺¹) - (Unitization.inr (approxUnitOfElement h n) : A⁺¹) * (a : A⁺¹) =
          c n * (a : A⁺¹) := by
        dsimp only [c]
        rw [sub_mul, one_mul]
      rw [hca, sq, ← CStarRing.norm_self_mul_star]
      have haa : (a : A⁺¹) * (a : A⁺¹) ≤ (a : A⁺¹) :=
        _root_.CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one (inr_nonneg_iff.2 ha)
          (by simpa [norm_inr] using ha_norm.le)
      have hmul : c n * (a : A⁺¹) * star (c n * (a : A⁺¹)) =
          c n * ((a : A⁺¹) * (a : A⁺¹)) * c n := by
        simp only [star_mul, hc_star n, (inr_nonneg_iff.2 ha).isSelfAdjoint.star_eq, mul_assoc]
      rw [hmul]
      have hle : c n * ((a : A⁺¹) * (a : A⁺¹)) * c n ≤ y n := by
        simpa only [y, hc_star n] using star_left_conjugate_le_conjugate haa (c n)
      have hnon : 0 ≤ c n * ((a : A⁺¹) * (a : A⁺¹)) * c n := by
        have ha2 : 0 ≤ (a : A⁺¹) * (a : A⁺¹) := by
          simpa only [(inr_nonneg_iff.2 ha).isSelfAdjoint.star_eq] using
            star_mul_self_nonneg (a : A⁺¹)
        simpa only [hc_star n] using star_left_conjugate_nonneg ha2 (c n)
      exact _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hnon
    have hy_tend : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by
      by_contra hnot
      rw [Metric.tendsto_atTop] at hnot
      push Not at hnot
      obtain ⟨δ, hδ_pos, hfreq⟩ := hnot
      let S : Set ℕ := { n : ℕ | δ ≤ ‖y n‖ }
      let F : Filter ℕ := atTop ⊓ 𝓟 S
      have hF_neBot : F.NeBot := by
        rw [inf_principal_neBot_iff]
        intro U hU
        obtain ⟨N, hN⟩ := eventually_atTop.1 hU
        obtain ⟨n, hnN, hny⟩ := hfreq N
        refine ⟨n, hN n hnN, ?_⟩
        simpa only [S, Set.mem_ofPred_eq, dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
          using hny
      choose ω _ hω_norm hω_val using fun n =>
        exists_positiveContinuousLinearMap_apply_eq_norm (hy_nonneg n)
      let ψCLM (n : ℕ) : A →L[ℂ] ℂ :=
        { toLinearMap :=
            { toFun := fun x => ω n (c n * (x : A⁺¹) * c n)
              map_add' := fun x₁ x₂ => by
                simp only [inr_add, mul_add, add_mul, map_add]
              map_smul' := fun r x => by
                simp only [inr_smul, mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply] }
          cont := (ω n).continuous.comp <|
            (continuous_const.mul Unitization.continuous_inr).mul continuous_const }
      let ψ (n : ℕ) : WeakDual ℂ A := StrongDual.toWeakDual (ψCLM n)
      let K : Set (WeakDual ℂ A) :=
        WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1 ∩
          { φ : WeakDual ℂ A | ∀ x, 0 ≤ x → 0 ≤ φ x }
      have hK_compact : IsCompact K :=
        (WeakDual.isCompact_closedBall 0 1).inter_right WeakDual.isClosed_setOf_map_nonneg
      have hψ_mem (n : ℕ) : ψ n ∈ K := by
        refine ⟨?_, fun x hx => ?_⟩
        · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
          refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
          calc ‖ω n (c n * (x : A⁺¹) * c n)‖
              ≤ ‖(ω n : A⁺¹ →L[ℂ] ℂ)‖ * ‖c n * (x : A⁺¹) * c n‖ := (ω n : A⁺¹ →L[ℂ] ℂ).le_opNorm _
            _ = ‖c n * (x : A⁺¹) * c n‖ := by rw [hω_norm n, one_mul]
            _ ≤ ‖c n‖ * ‖(x : A⁺¹)‖ * ‖c n‖ :=
              (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            _ ≤ 1 * ‖x‖ * 1 := by
              rw [norm_inr]
              exact mul_le_mul (mul_le_mul (hc_norm n) le_rfl (norm_nonneg _) zero_le_one)
                (hc_norm n) (norm_nonneg _) (by positivity)
            _ = 1 * ‖x‖ := mul_one _
        · have hx' : 0 ≤ c n * (x : A⁺¹) * c n := by
            simpa only [hc_star n] using star_left_conjugate_nonneg (inr_nonneg_iff.2 hx) (c n)
          exact (ω n).map_nonneg hx'
      have hmap_neBot : (Filter.map ψ F).NeBot := hF_neBot.map ψ
      obtain ⟨ψ₀, hψ₀K, hclust⟩ := hK_compact.exists_clusterPt
        (f := Filter.map ψ F) (le_principal_iff.2 (eventually_map.2 (.of_forall hψ_mem)))
      -- Show `δ ≤ (ψ₀ a).re` since `δ ≤ (ψ n a).re` along `F`.
      have hψ₀a : δ ≤ (ψ₀ a).re := by
        have hcl : IsClosed { φ : WeakDual ℂ A | δ ≤ (φ a).re } :=
          isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous a))
        have hev : ∀ᶠ n in F, δ ≤ (ψ n a).re := by
          refine Filter.eventually_inf_principal.2 (.of_forall fun n hn => ?_)
          change δ ≤ (ω n (y n)).re
          rw [hω_val n, Complex.ofReal_re]
          exact hn
        have hmem_cl : ψ₀ ∈ closure { φ : WeakDual ℂ A | δ ≤ (φ a).re } :=
          mem_closure_iff_clusterPt.2 <| hclust.mono (le_principal_iff.2 (eventually_map.2 hev))
        rwa [hcl.closure_eq] at hmem_cl
      -- Show `ψ₀ h = 0` since `‖ψ n h‖ ≤ 1 / (n + 1) → 0`.
      have hψh_tend : Tendsto (fun n => ψ n h) F (𝓝 0) := by
        refine Tendsto.mono_left ?_ inf_le_left
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
          tendsto_one_div_add_atTop_nhds_zero_nat
        change ‖ω n (c n * (h : A⁺¹) * c n)‖ ≤ 1 / (n + 1 : ℝ)
        have hch : c n * (h : A⁺¹) = ((h - approxUnitOfElement h n * h : A) : A⁺¹) := by
          dsimp only [c]
          rw [inr_sub, inr_mul, sub_mul, one_mul]
        calc ‖ω n (c n * (h : A⁺¹) * c n)‖
            ≤ ‖(ω n : A⁺¹ →L[ℂ] ℂ)‖ * ‖c n * (h : A⁺¹) * c n‖ := (ω n : A⁺¹ →L[ℂ] ℂ).le_opNorm _
          _ = ‖c n * (h : A⁺¹) * c n‖ := by rw [hω_norm n, one_mul]
          _ ≤ ‖c n * (h : A⁺¹)‖ * ‖c n‖ := norm_mul_le _ _
          _ ≤ ‖h - approxUnitOfElement h n * h‖ * 1 := by
            rw [hch, norm_inr]
            exact mul_le_mul_of_nonneg_left (hc_norm n) (norm_nonneg _)
          _ = ‖h - approxUnitOfElement h n * h‖ := mul_one _
          _ ≤ 1 / (n + 1 : ℝ) := norm_sub_approxUnitOfElement_mul_le hh.1 n
      have hψ₀h : ψ₀ h = 0 := by
        have hcl_h : ClusterPt (ψ₀ h) (Filter.map (fun n => ψ n h) F) := by
          simpa only [Filter.map_map, Function.comp_def] using
            hclust.map (WeakDual.eval_continuous h).continuousAt tendsto_id
        exact eq_of_nhds_neBot (hcl_h.mono hψh_tend)
      let φ : A →P[ℂ] ℂ := .mk₀ (WeakDual.toStrongDual ψ₀) fun _ => hψ₀K.2 _
      have hφ_ne : φ ≠ 0 := fun h0 => by
        have : (φ a).re = 0 := by simp [h0]
        change (ψ₀ a).re = 0 at this
        linarith
      have hpos := hh.2 φ hφ_ne
      change 0 < (ψ₀ h).re at hpos
      rw [hψ₀h, Complex.zero_re] at hpos
      exact lt_irrefl 0 hpos
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsqrt : Tendsto (fun n => Real.sqrt ‖y n‖) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero, Function.comp_def] using
        (Real.continuous_sqrt.tendsto 0).comp hy_tend
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => Real.le_sqrt_of_sq_le (hsq n)) hsqrt
  exact
    { tendsto_mul_left :=
        (_root_.CStarAlgebra.tendsto_mul_left_iff_tendsto_mul_right
          (hnonneg.mono fun _ => IsSelfAdjoint.of_nonneg)).2 hright
      tendsto_mul_right := hright
      neBot := atTop_neBot.map _
      eventually_nonneg := hnonneg
      eventually_norm := hnorm }

/-- **Four-way characterization of strictly positive elements.** For a nonnegative element `h` of
a C⋆-algebra `A`, the following are equivalent:
1. `h` is strictly positive;
2. the hereditary range `{h * a * h | a : A}` is dense in `A`;
3. the right ideal `{h * a | a : A}` is dense in `A`;
4. `approxUnitOfElement h` is an increasing approximate unit of `A`. -/
theorem isStrictlyPositive_tfae {h : A} (hh : 0 ≤ h) :
    List.TFAE [
      IsStrictlyPositive h,
      Dense (Set.range fun a : A => h * a * h),
      Dense (Set.range fun a : A => h * a),
      (Filter.map (approxUnitOfElement h) atTop).IsIncreasingApproximateUnit
    ] := by
  tfae_have 1 → 4 := isIncreasingApproximateUnit_approxUnitOfElement_of_isStrictlyPositive
  tfae_have 4 → 2 := fun hl => by
    intro a
    -- First show `e n * a * e n ∈ closure (range (fun x => h * x * h))` for every `n`.
    have heae (n : ℕ) : approxUnitOfElement h n * a * approxUnitOfElement h n ∈
        closure (Set.range fun x : A => h * x * h) := by
      have hlim : Tendsto (fun k =>
          (approxUnitOfElement h n * approxUnitOfElement h k) * a *
            (approxUnitOfElement h k * approxUnitOfElement h n)) atTop
          (𝓝 (approxUnitOfElement h n * a * approxUnitOfElement h n)) := by
        have h1 : Tendsto (fun k => approxUnitOfElement h n * approxUnitOfElement h k) atTop
            (𝓝 (approxUnitOfElement h n)) :=
          tendsto_map'_iff.1 (hl.tendsto_mul_left (approxUnitOfElement h n))
        have h2 : Tendsto (fun k => approxUnitOfElement h k * approxUnitOfElement h n) atTop
            (𝓝 (approxUnitOfElement h n)) :=
          tendsto_map'_iff.1 (hl.tendsto_mul_right (approxUnitOfElement h n))
        exact (h1.mul tendsto_const_nhds).mul h2
      refine mem_closure_of_tendsto hlim (.of_forall fun k => ?_)
      obtain ⟨q, hql, _⟩ := exists_mul_eq_approxUnitOfElement_mul hh n k
      obtain ⟨q', _, hq'r⟩ := exists_mul_eq_approxUnitOfElement_mul hh k n
      refine ⟨q * a * q', ?_⟩
      simp only [← hql, ← hq'r, mul_assoc]
    have hlim : Tendsto (fun n => approxUnitOfElement h n * a * approxUnitOfElement h n) atTop
        (𝓝 a) := by
      have h1 : Tendsto (fun n => approxUnitOfElement h n * a) atTop (𝓝 a) :=
        tendsto_map'_iff.1 (hl.tendsto_mul_right a)
      have h2 : Tendsto (fun n => (approxUnitOfElement h n * a - a) * approxUnitOfElement h n)
          atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
          (tendsto_iff_norm_sub_tendsto_zero.1 h1)
        calc ‖(approxUnitOfElement h n * a - a) * approxUnitOfElement h n‖
            ≤ ‖approxUnitOfElement h n * a - a‖ * ‖approxUnitOfElement h n‖ := norm_mul_le _ _
          _ ≤ ‖approxUnitOfElement h n * a - a‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_approxUnitOfElement_le_one h n) (norm_nonneg _)
          _ = ‖approxUnitOfElement h n * a - a‖ := mul_one _
      have h3 : Tendsto (fun n => a * approxUnitOfElement h n) atTop (𝓝 a) :=
        tendsto_map'_iff.1 (hl.tendsto_mul_left a)
      simpa only [sub_mul, sub_add_cancel, zero_add] using h2.add h3
    exact isClosed_closure.mem_of_tendsto hlim (.of_forall heae)
  tfae_have 2 → 3 := fun hd =>
    hd.mono (by rintro _ ⟨a, rfl⟩; exact ⟨a * h, (mul_assoc h a h).symm⟩)
  tfae_have 3 → 4 := fun hd => by
    have hnonneg : ∀ᶠ e in Filter.map (approxUnitOfElement h) atTop, 0 ≤ e :=
      eventually_map.2 (.of_forall (approxUnitOfElement_nonneg h))
    have hnorm : ∀ᶠ e in Filter.map (approxUnitOfElement h) atTop, ‖e‖ ≤ 1 :=
      eventually_map.2 (.of_forall (norm_approxUnitOfElement_le_one h))
    have hright : ∀ a : A, Tendsto (· * a) (Filter.map (approxUnitOfElement h) atTop) (𝓝 a) := by
      intro a
      rw [tendsto_map'_iff, Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨_, ⟨b, rfl⟩, hab⟩ := Metric.mem_closure_iff.1 (hd a) (ε / 3) (by positivity)
      have hdist : ‖a - h * b‖ < ε / 3 := by simpa only [dist_eq_norm] using hab
      have hlim_hb : Tendsto (fun n => approxUnitOfElement h n * (h * b)) atTop (𝓝 (h * b)) := by
        simpa only [mul_assoc] using
          (tendsto_approxUnitOfElement_mul_self hh).mul (tendsto_const_nhds (x := b))
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim_hb (ε / 3) (by positivity)
      refine ⟨N, fun n hn => ?_⟩
      have hn' : ‖approxUnitOfElement h n * (h * b) - h * b‖ < ε / 3 := by
        simpa only [dist_eq_norm] using hN n hn
      rw [Function.comp_apply, dist_eq_norm]
      have hsplit : approxUnitOfElement h n * a - a =
          approxUnitOfElement h n * (a - h * b) +
            (approxUnitOfElement h n * (h * b) - h * b) - (a - h * b) := by
        rw [mul_sub]
        abel
      rw [hsplit]
      calc ‖approxUnitOfElement h n * (a - h * b) +
              (approxUnitOfElement h n * (h * b) - h * b) - (a - h * b)‖
          ≤ ‖approxUnitOfElement h n * (a - h * b)‖ +
              ‖approxUnitOfElement h n * (h * b) - h * b‖ + ‖a - h * b‖ :=
            (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
        _ ≤ 1 * ‖a - h * b‖ + ‖approxUnitOfElement h n * (h * b) - h * b‖ + ‖a - h * b‖ := by
          gcongr
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_approxUnitOfElement_le_one h n) (norm_nonneg _))
        _ < ε / 3 + ε / 3 + ε / 3 := by linarith
        _ = ε := by ring
    exact
      { tendsto_mul_left :=
          (_root_.CStarAlgebra.tendsto_mul_left_iff_tendsto_mul_right
            (hnonneg.mono fun _ => IsSelfAdjoint.of_nonneg)).2 hright
        tendsto_mul_right := hright
        neBot := atTop_neBot.map _
        eventually_nonneg := hnonneg
        eventually_norm := hnorm }
  tfae_have 4 → 1 := fun hl => by
    rw [isStrictlyPositive_iff_apply_ne_zero]
    refine ⟨hh, fun φ hφ hφh => hφ ?_⟩
    have hφe (n : ℕ) : φ (approxUnitOfElement h n) = 0 := by
      have h0 : 0 ≤ φ (approxUnitOfElement h n) := φ.map_nonneg (approxUnitOfElement_nonneg h n)
      have hle : φ (approxUnitOfElement h n) ≤ φ (((n + 1 : ℝ≥0) • h)) :=
        φ.mono (approxUnitOfElement_le_smul hh n)
      have hrhs : φ (((n + 1 : ℝ≥0) • h)) = 0 := by
        change φ (((n + 1 : ℝ) : ℂ) • h) = 0
        rw [map_smul, hφh, smul_zero]
      rw [hrhs] at hle
      exact le_antisymm hle h0
    have htend : Tendsto (fun n => φ (approxUnitOfElement h n)) atTop
        (𝓝 (‖(φ : A →L[ℂ] ℂ)‖ : ℂ)) :=
      tendsto_map'_iff.1 (φ.tendsto_nhds_opNorm hl)
    have hnorm0 : (‖(φ : A →L[ℂ] ℂ)‖ : ℂ) = 0 :=
      tendsto_nhds_unique htend (by simpa only [hφe] using tendsto_const_nhds)
    have hclm0 : (φ : A →L[ℂ] ℂ) = 0 := norm_eq_zero.1 (Complex.ofReal_eq_zero.1 hnorm0)
    exact PositiveContinuousLinearMap.ext fun a => congrArg (fun f : A →L[ℂ] ℂ => f a) hclm0
  tfae_finish

/-- A nonnegative element `h` is strictly positive iff `h A h` is dense in `A`. -/
theorem isStrictlyPositive_iff_dense_range_mul_mul {h : A} (hh : 0 ≤ h) :
    IsStrictlyPositive h ↔ Dense (Set.range fun a : A => h * a * h) :=
  (isStrictlyPositive_tfae hh).out 1 2

/-- A nonnegative element `h` is strictly positive iff `h A` is dense in `A`. -/
theorem isStrictlyPositive_iff_dense_range_mul {h : A} (hh : 0 ≤ h) :
    IsStrictlyPositive h ↔ Dense (Set.range fun a : A => h * a) :=
  (isStrictlyPositive_tfae hh).out 1 3

/-- A nonnegative element `h` is strictly positive iff `approxUnitOfElement h` is an increasing
approximate unit of `A`. -/
theorem isStrictlyPositive_iff_isIncreasingApproximateUnit_approxUnitOfElement {h : A}
    (hh : 0 ≤ h) :
    IsStrictlyPositive h ↔
      (Filter.map (approxUnitOfElement h) atTop).IsIncreasingApproximateUnit :=
  (isStrictlyPositive_tfae hh).out 1 4

/-! ### σ-Unitality and separability -/

/-- Given any sequence `u : ℕ → A`, the normalized weighted sum
`∑' n, (2 ^ (n + 1) * (1 + ‖u n‖ ^ 2))⁻¹ • (star (u n) * u n)` is a nonnegative element `h`
such that any positive functional vanishing at `h` vanishes on every `star (u n) * u n`. -/
private theorem exists_nonneg_of_seq (u : ℕ → A) :
    ∃ h : A, 0 ≤ h ∧ ∀ φ : A →P[ℂ] ℂ, φ h = 0 → ∀ n, φ (star (u n) * u n) = 0 := by
  let c (n : ℕ) : ℝ := ((2 : ℝ) ^ (n + 1) * (1 + ‖u n‖ ^ 2))⁻¹
  have hc_pos (n : ℕ) : 0 < c n := by positivity
  let term (n : ℕ) : A := c n • (star (u n) * u n)
  have hterm_nonneg (n : ℕ) : 0 ≤ term n :=
    smul_nonneg (hc_pos n).le (star_mul_self_nonneg (u n))
  have hterm_norm (n : ℕ) : ‖term n‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    rw [norm_smul, Real.norm_of_nonneg (hc_pos n).le, CStarRing.norm_star_mul_self, ← sq]
    dsimp only [c]
    rw [one_div, inv_pow, mul_inv, mul_assoc]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    linarith
  have hsum : Summable term :=
    Summable.of_norm_bounded (g := fun n => (1 / 2 : ℝ) ^ (n + 1))
      ((summable_geometric_two.comp_injective (add_left_injective 1))) hterm_norm
  let h : A := ∑' n, term n
  have hh_nonneg : 0 ≤ h :=
    _root_.CStarAlgebra.isClosed_nonneg.mem_of_tendsto hsum.hasSum <|
      Eventually.of_forall fun s => Finset.sum_nonneg fun n _ => hterm_nonneg n
  have hle (k : ℕ) : term k ≤ h := by
    rw [← sub_nonneg]
    refine _root_.CStarAlgebra.isClosed_nonneg.mem_of_tendsto
      (Tendsto.sub hsum.hasSum tendsto_const_nhds) ?_
    filter_upwards
      [eventually_atTop.2 ⟨{k}, fun s hs => hs (Finset.mem_singleton_self k)⟩] with s hs
    have hsplit : (∑ n ∈ s, term n) - term k = ∑ n ∈ s.erase k, term n := by
      rw [← Finset.add_sum_erase s term hs, add_sub_cancel_left]
    rw [hsplit]
    exact Finset.sum_nonneg fun n _ => hterm_nonneg n
  refine ⟨h, hh_nonneg, fun φ hφh k => ?_⟩
  have h0 : 0 ≤ φ (term k) := φ.map_nonneg (hterm_nonneg k)
  have h1 : φ (term k) ≤ 0 := hφh ▸ φ.mono (hle k)
  have htk : φ (term k) = 0 := le_antisymm h1 h0
  change φ (((c k : ℝ) : ℂ) • (star (u k) * u k)) = 0 at htk
  rw [map_smul, smul_eq_mul] at htk
  exact (mul_eq_zero.1 htk).resolve_left (Complex.ofReal_ne_zero.2 (hc_pos k).ne')

/-- **Characterizations of σ-unitality.** For a (possibly nonunital) C⋆-algebra `A`, the following
are equivalent:
1. `A` has a strictly positive element;
2. `A` has a monotone sequential increasing approximate unit;
3. `A` has a sequential increasing approximate unit;
4. `A` has a sequential right approximate unit;
5. `A` has a sequential left approximate unit. -/
theorem exists_isStrictlyPositive_tfae :
    List.TFAE [
      ∃ h : A, IsStrictlyPositive h,
      ∃ u : ℕ → A, Monotone u ∧ (Filter.map u atTop).IsIncreasingApproximateUnit,
      ∃ u : ℕ → A, (Filter.map u atTop).IsIncreasingApproximateUnit,
      ∃ u : ℕ → A, ∀ a : A, Tendsto (fun n => a * u n) atTop (𝓝 a),
      ∃ u : ℕ → A, ∀ a : A, Tendsto (fun n => u n * a) atTop (𝓝 a)
    ] := by
  tfae_have 1 → 2 := fun ⟨h, hh⟩ =>
    ⟨approxUnitOfElement h, monotone_approxUnitOfElement hh.1,
      (isStrictlyPositive_iff_isIncreasingApproximateUnit_approxUnitOfElement hh.1).1 hh⟩
  tfae_have 2 → 3 := fun ⟨u, _, hu⟩ => ⟨u, hu⟩
  tfae_have 3 → 4 := fun ⟨u, hu⟩ => ⟨u, fun a => tendsto_map'_iff.1 (hu.tendsto_mul_left a)⟩
  tfae_have 4 → 5 := fun ⟨u, hu⟩ => ⟨fun n => star (u n), fun a => by
    have h := (continuous_star.tendsto (star a)).comp (hu (star a))
    simpa only [Function.comp_def, star_mul, star_star] using h⟩
  tfae_have 5 → 4 := fun ⟨u, hu⟩ => ⟨fun n => star (u n), fun a => by
    have h := (continuous_star.tendsto (star a)).comp (hu (star a))
    simpa only [Function.comp_def, star_mul, star_star] using h⟩
  tfae_have 4 → 1 := fun ⟨u, hu⟩ => by
    obtain ⟨h, hh, hvan⟩ := exists_nonneg_of_seq u
    refine ⟨h, isStrictlyPositive_iff_apply_ne_zero.2 ⟨hh, fun φ hφ hφh => hφ ?_⟩⟩
    refine PositiveContinuousLinearMap.ext fun a => ?_
    have hauk (n : ℕ) : φ (a * u n) = 0 := by
      have hcs := PositiveLinearMap.norm_map_star_mul_sq_le φ (star a) (u n)
      rw [star_star, hvan φ hφh n, norm_zero, mul_zero] at hcs
      have h0 : ‖φ (a * u n)‖ = 0 := by nlinarith [norm_nonneg (φ (a * u n))]
      exact norm_eq_zero.1 h0
    have htend : Tendsto (fun n => φ (a * u n)) atTop (𝓝 (φ a)) :=
      (φ.continuous.tendsto a).comp (hu a)
    change φ a = 0
    exact tendsto_nhds_unique htend (by simpa only [hauk] using tendsto_const_nhds)
  tfae_finish

/-- Every separable C⋆-algebra has a strictly positive element. -/
theorem exists_isStrictlyPositive_of_separableSpace [TopologicalSpace.SeparableSpace A] :
    ∃ h : A, IsStrictlyPositive h := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨h, hh, hvan⟩ := exists_nonneg_of_seq d
  refine ⟨h, isStrictlyPositive_iff_apply_ne_zero.2 ⟨hh, fun φ hφ hφh => hφ ?_⟩⟩
  refine PositiveContinuousLinearMap.ext fun a => ?_
  refine hd.induction_on a (isClosed_eq φ.continuous continuous_const) fun n => ?_
  have hle := φ.norm_map_le_sqrt_opNorm_mul (d n)
  rw [hvan φ hφh n, norm_zero, Real.sqrt_zero, mul_zero] at hle
  exact norm_eq_zero.1 (le_antisymm hle (norm_nonneg _))

/-- Every separable C⋆-algebra admits a monotone sequential increasing approximate unit. -/
theorem exists_monotone_seq_isIncreasingApproximateUnit_of_separableSpace
    [TopologicalSpace.SeparableSpace A] :
    ∃ u : ℕ → A, Monotone u ∧ (Filter.map u atTop).IsIncreasingApproximateUnit :=
  (exists_isStrictlyPositive_tfae.out 1 2).1 exists_isStrictlyPositive_of_separableSpace

end TauCeti.CStarAlgebra

end
