/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic

/-!
# Factorization of vectors in Hilbert C⋆-modules

Every vector in a complete Hilbert C⋆-module `E` over a (possibly non-unital) C⋆-algebra `A` admits
three progressively sharper factorizations through the coefficient action:

1. **Cohen–Hewitt factorization** (`CStarModule.exists_smul_eq`, `CStarModule.exists_op_smul_eq`):
   even without completeness, an increasing approximate unit of `A` approximates every `x : E` by
   elements `e • x`, so `A • E` is dense in `E` and its closed linear span is `⊤`. When `E` is
   complete, Cohen–Hewitt factorization for Banach modules produces `a : A` with `‖a‖ ≤ 1` and
   `y ∈ closure (Set.range (· • x))` arbitrarily close to `x` such that `a • y = x`. In particular,
   `A • E = E` (`CStarModule.surjective_smul`) and `A • s = s` for every closed `A`-invariant
   subset `s ⊆ E` (`CStarModule.setOf_exists_smul_eq_of_isClosed`).

2. **Fractional-power factorization** (`CStarModule.existsUnique_nnrpow_inner_self_smul_eq`):
   for `0 < r < 1 / 2`, any `y : E` satisfying `(⟪x, x⟫_A ^ r) • y = x` and
   `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)` is the norm limit as `ε → 0⁺` of the regularized vectors
   `cfcₙ (fun t ↦ t ^ (1 / 2 - r) / (t ^ (1 / 2) + ε)) ⟪x, x⟫_A • x`. Consequently, even without
   completeness, such a `y` is globally unique (`CStarModule.eq_of_nnrpow_inner_self_smul_eq`),
   belongs to `closure (Set.range (· • x))` and to every closed `A`-invariant set containing `x`,
   and satisfies `⟪x, y⟫_A = ⟪y, x⟫_A = ⟪x, x⟫_A ^ (1 - r)` and `‖y‖ = ‖x‖ ^ (1 - 2 * r)`. When `E`
   is complete, the regularized family is Cauchy and the unique factor `y` exists.

3. **Self-inner-product factorization** (`CStarModule.existsUnique_nnrpow_inner_self_smul_self_eq`,
   `CStarModule.existsUnique_inner_self_smul_self_eq`,
   `CStarModule.existsUnique_op_unop_inner_self_smul_self_eq`):
   for any `0 < p : ℝ≥0`, the single equation `(⟪y, y⟫_A ^ p) • y = x` forces
   `⟪y, y⟫_A = ⟪x, x⟫_A ^ (2 * p + 1)⁻¹` and reduces to fractional-power factorization at
   `r = p / (2 * p + 1) < 1 / 2`. Setting `p = 1` yields the canonical factorization
   `⟪y, y⟫_A • y = x` (or `y ⟨y, y⟩_A = x`, written `op (unop (inner Aᵐᵒᵖ y y)) • y = x`, for right
   Hilbert `A`-modules `CStarModule Aᵐᵒᵖ E`), which is globally unique on `E` and satisfies
   `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 / 3)` and `‖y‖ = ‖x‖ ^ (1 / 3)`.

## Main declarations

* `CStarModule.mem_closure_range_smul`, `CStarModule.dense_range_smul`,
  `CStarModule.topologicalClosure_span_range_smul`: essentiality of the action without completeness
  (and right-module forms `*_op_smul`).
* `CStarModule.exists_smul_eq`, `CStarModule.surjective_smul`, `CStarModule.range_smul`,
  `CStarModule.setOf_exists_smul_eq_of_isClosed`: Cohen–Hewitt factorization on complete modules
  (and right-module forms `*_op_smul*`).
* `CStarModule.eq_of_nnrpow_inner_self_smul_eq`,
  `CStarModule.existsUnique_nnrpow_inner_self_smul_eq`: uniqueness and existence for
  `(⟪x, x⟫_A ^ r) • y = x` with `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)` and `0 < r < 1 / 2` (and
  right-module forms).
* `CStarModule.existsUnique_nnrpow_inner_self_smul_self_eq`,
  `CStarModule.existsUnique_inner_self_smul_self_eq`,
  `CStarModule.existsUnique_op_unop_inner_self_smul_self_eq`: unique factorization
  `(⟪y, y⟫_A ^ p) • y = x`, `⟪y, y⟫_A • y = x`, and `y ⟨y, y⟩_A = x`, together with inner-product,
  norm, and closed-set invariance consequences.

## References

* P. J. Cohen, *Factorization in group algebras*, Duke Math. J. 26 (1959), 199–205.
* E. Hewitt, *The ranges of certain convolution operators*, Math. Scand. 15 (1964), 147–155.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Proposition 1.8
  and Lemma 4.4.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 2.31.
-/

public section

open Filter MulOpposite Topology
open scoped NNReal

namespace CStarModule

variable {A E : Type*}

private lemma range_op_smul_eq [SMul Aᵐᵒᵖ E] (x : E) :
    (Set.range fun a : A ↦ op a • x) = Set.range (· • x : Aᵐᵒᵖ → E) :=
  op_surjective.range_comp (· • x : Aᵐᵒᵖ → E)

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Essentiality and Cohen–Hewitt factorization -/

section CohenFactorization

section Essential

variable [NormedAddCommGroup E]

section Left

/-- Every vector `x` in a Hilbert C⋆-module lies in the norm closure of its orbit `A • x`. -/
theorem mem_closure_range_smul [Module ℂ E] [SMul A E] [CStarModule A E] (x : E) :
    x ∈ closure (Set.range (· • x : A → E)) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  exact mem_closure_of_tendsto (tendsto_smul hl.tendsto_mul_right x)
    (Eventually.of_forall fun a ↦ ⟨a, rfl⟩)

/-- Products `a • x` form a dense subset of any Hilbert C⋆-module `E`. -/
theorem dense_range_smul [Module ℂ E] [SMul A E] [CStarModule A E] :
    Dense (Set.range fun p : A × E ↦ p.1 • p.2) := by
  intro x
  refine closure_mono ?_ (mem_closure_range_smul (A := A) x)
  rintro _ ⟨a, rfl⟩
  exact ⟨(a, x), rfl⟩

/-- Any Hilbert C⋆-module is essential: the closed complex linear span of `A • E` is `⊤`. -/
theorem topologicalClosure_span_range_smul [NormedSpace ℂ E] [SMul A E] [CStarModule A E] :
    (Submodule.span ℂ (Set.range fun p : A × E ↦ p.1 • p.2)).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp <|
    (dense_range_smul (A := A) (E := E)).mono Submodule.subset_span

end Left

section Right

/-- Every vector `x` in a right Hilbert C⋆-module lies in the norm closure of `x • A`. -/
theorem mem_closure_range_op_smul [Module ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : E) :
    x ∈ closure (Set.range fun a : A ↦ op a • x) := by
  rw [range_op_smul_eq]
  exact mem_closure_range_smul (A := Aᵐᵒᵖ) x

/-- Right products `x a = op a • x` form a dense subset of any right Hilbert C⋆-module `E`. -/
theorem dense_range_op_smul [Module ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] :
    Dense (Set.range fun p : E × A ↦ op p.2 • p.1) := by
  intro x
  refine closure_mono ?_ (mem_closure_range_op_smul (A := A) x)
  rintro _ ⟨a, rfl⟩
  exact ⟨(x, a), rfl⟩

/-- Any right Hilbert C⋆-module is essential: the closed complex linear span of `E • A` is `⊤`. -/
theorem topologicalClosure_span_range_op_smul [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] :
    (Submodule.span ℂ (Set.range fun p : E × A ↦ op p.2 • p.1)).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp <|
    (dense_range_op_smul (A := A) (E := E)).mono Submodule.subset_span

end Right

end Essential

section Complete

variable [NormedAddCommGroup E] [Module ℂ E] [CompleteSpace E]

section Left

variable [SMul A E] [CStarModule A E]

/-- **Cohen–Hewitt factorization for Hilbert C⋆-modules.** Every `x` in a complete Hilbert
`A`-module `E` factors as `a • y = x` with `‖a‖ ≤ 1`, `y ∈ closure (Set.range (· • x))`, and
`‖y - x‖ < ε`. -/
theorem exists_smul_eq (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ∃ y : E, ‖a‖ ≤ 1 ∧ y ∈ closure (Set.range (· • x : A → E)) ∧ ‖y - x‖ < ε ∧
      a • y = x := by
  let _ : NormedSpace ℂ E := .ofCore (normedSpaceCore A)
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hx : x ∈ (Submodule.span ℂ
      (Set.range fun p : A × E ↦ smulCLM A E p.1 p.2)).topologicalClosure := by
    simp only [smulCLM_apply, topologicalClosure_span_range_smul (A := A) (E := E)]
    exact Submodule.mem_top
  obtain ⟨a, y, ha, hy, hdist, hfac⟩ :=
    ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span (smulCLM A E)
      (smulCLM_mul (A := A) (E := E)) hl.eventually_norm hl.tendsto_mul_right hx hε
  simp only [smulCLM_apply] at hy hfac
  exact ⟨a, y, ha, hy, hdist, hfac⟩

/-- On a complete Hilbert C⋆-module, the action map `(a, y) ↦ a • y` is surjective. -/
theorem surjective_smul : Function.Surjective fun p : A × E ↦ p.1 • p.2 := fun x ↦ by
  obtain ⟨a, y, -, -, -, h⟩ := exists_smul_eq (A := A) x one_pos
  exact ⟨(a, y), h⟩

/-- On a complete Hilbert C⋆-module, products `a • y` span the whole module setwise. -/
@[simp]
theorem range_smul : Set.range (fun p : A × E ↦ p.1 • p.2) = Set.univ :=
  (surjective_smul (A := A) (E := E)).range_eq

/-- For any closed `A`-invariant subset `s` of a complete Hilbert C⋆-module, `A • s = s`. -/
theorem setOf_exists_smul_eq_of_isClosed {s : Set E} (hs : IsClosed s)
    (hsmul : ∀ a : A, ∀ x ∈ s, a • x ∈ s) :
    {x : E | ∃ a : A, ∃ y ∈ s, a • y = x} = s := by
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨a, y, hy, rfl⟩
    exact hsmul a y hy
  · obtain ⟨a, y, -, hy, -, h⟩ := exists_smul_eq (A := A) x one_pos
    refine ⟨a, y, closure_minimal ?_ hs hy, h⟩
    rintro _ ⟨b, rfl⟩
    exact hsmul b x hx

end Left

section Right

variable [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- **Cohen–Hewitt factorization for right Hilbert C⋆-modules.** Every `x` in a complete right
Hilbert `A`-module `E` factors as `op a • y = x` with `‖a‖ ≤ 1`,
`y ∈ closure (Set.range fun b : A ↦ op b • x)`, and `‖y - x‖ < ε`. -/
theorem exists_op_smul_eq (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ∃ y : E, ‖a‖ ≤ 1 ∧ y ∈ closure (Set.range fun b : A ↦ op b • x) ∧ ‖y - x‖ < ε ∧
      op a • y = x := by
  obtain ⟨a, y, ha, hy, hdist, hfac⟩ := exists_smul_eq (A := Aᵐᵒᵖ) x hε
  refine ⟨unop a, y, by rwa [norm_unop], ?_, hdist, by simpa using hfac⟩
  rwa [range_op_smul_eq]

/-- On a complete right Hilbert C⋆-module, the right action `(y, a) ↦ op a • y` is surjective. -/
theorem surjective_op_smul : Function.Surjective fun p : E × A ↦ op p.2 • p.1 := fun x ↦ by
  obtain ⟨a, y, -, -, -, h⟩ := exists_op_smul_eq (A := A) x one_pos
  exact ⟨(y, a), h⟩

/-- On a complete right Hilbert C⋆-module, right products `op a • y` span the whole module
setwise. -/
@[simp]
theorem range_op_smul : Set.range (fun p : E × A ↦ op p.2 • p.1) = Set.univ :=
  (surjective_op_smul (A := A) (E := E)).range_eq

/-- For any closed right-`A`-invariant subset `s` of a complete right Hilbert C⋆-module,
`s • A = s`. -/
theorem setOf_exists_op_smul_eq_of_isClosed {s : Set E} (hs : IsClosed s)
    (hsmul : ∀ a : A, ∀ x ∈ s, op a • x ∈ s) :
    {x : E | ∃ a : A, ∃ y ∈ s, op a • y = x} = s := by
  have h := setOf_exists_smul_eq_of_isClosed (A := Aᵐᵒᵖ) hs fun a x hx ↦ hsmul (unop a) x hx
  ext x
  exact ⟨fun ⟨a, y, hy, hxy⟩ ↦ h.subset ⟨op a, y, hy, hxy⟩,
    fun hx ↦ let ⟨a, y, hy, hxy⟩ := h.symm.subset hx; ⟨unop a, y, hy, by simpa using hxy⟩⟩

end Right

end Complete

end CohenFactorization

/-! ### Fractional-power factorization (`0 < r < 1 / 2`) -/

section FractionalPower

private lemma two_mul_lt_one_of_lt_half {r : ℝ≥0} (hr : r < 1 / 2) : 2 * r < 1 := by
  have hr' : (r : ℝ) < 1 / 2 := by simpa using NNReal.coe_lt_coe.2 hr
  rw [← NNReal.coe_lt_coe]
  push_cast
  linarith

private lemma lt_one_of_lt_half {r : ℝ≥0} (hr : r < 1 / 2) : r < 1 := by
  have hr' : (r : ℝ) < 1 / 2 := by simpa using NNReal.coe_lt_coe.2 hr
  rw [← NNReal.coe_lt_coe]
  push_cast
  linarith

private lemma one_sub_two_mul_add_self {r : ℝ≥0} (hr : r < 1 / 2) :
    1 - 2 * r + r = 1 - r := by
  have h2r := (two_mul_lt_one_of_lt_half hr).le
  have hr1 := (lt_one_of_lt_half hr).le
  ext
  push_cast [h2r, hr1]
  ring

private lemma one_sub_two_mul_mul_half {r : ℝ≥0} (hr : r < 1 / 2) :
    (1 - 2 * r) * (1 / 2) = 1 / 2 - r := by
  have h2r := (two_mul_lt_one_of_lt_half hr).le
  ext
  push_cast [h2r, hr.le]
  ring

private lemma half_sub_add_half_sub {r : ℝ≥0} (hr : r < 1 / 2) :
    (1 / 2 - r) + (1 / 2 - r) = 1 - 2 * r := by
  have h2r := (two_mul_lt_one_of_lt_half hr).le
  ext
  push_cast [h2r, hr.le]
  ring

section AlgebraicNorm

variable [AddCommGroup E] [Module ℂ E] [Norm E]

section Left

variable [SMul A E] [CStarModule A E]

/-- If `(⟪x, x⟫_A ^ r) • y = x` and `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)` with `0 < r < 1 / 2`, then
`⟪x, y⟫_A = ⟪x, x⟫_A ^ (1 - r)`. -/
theorem inner_left_of_nnrpow_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : (inner A x x ^ r) • y = x)
    (hyy : inner A y y = inner A x x ^ (1 - 2 * r)) :
    inner A x y = inner A x x ^ (1 - r) := by
  have h2r : 0 < 1 - 2 * r := tsub_pos_of_lt (two_mul_lt_one_of_lt_half hr₁)
  calc
    inner A x y = inner A ((inner A x x ^ r) • y) y := by rw [hyx]
    _ = inner A y y * star (inner A x x ^ r) := inner_op_smul_left
    _ = inner A x x ^ (1 - 2 * r) * inner A x x ^ r := by
      rw [hyy, CFC.nnrpow_nonneg.isSelfAdjoint.star_eq]
    _ = inner A x x ^ (1 - 2 * r + r) := (CFC.nnrpow_add h2r hr₀).symm
    _ = inner A x x ^ (1 - r) := by rw [one_sub_two_mul_add_self hr₁]

/-- If `(⟪x, x⟫_A ^ r) • y = x` and `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)` with `0 < r < 1 / 2`, then
`⟪y, x⟫_A = ⟪x, x⟫_A ^ (1 - r)`. -/
theorem inner_right_of_nnrpow_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : (inner A x x ^ r) • y = x)
    (hyy : inner A y y = inner A x x ^ (1 - 2 * r)) :
    inner A y x = inner A x x ^ (1 - r) := by
  rw [← star_inner, inner_left_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx hyy,
    CFC.nnrpow_nonneg.isSelfAdjoint.star_eq]

/-- If `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)` with `r < 1 / 2`, then `‖y‖ = ‖x‖ ^ (1 - 2 * r)`. -/
theorem norm_of_nnrpow_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₁ : r < 1 / 2)
    (hyy : inner A y y = inner A x x ^ (1 - 2 * r)) :
    ‖y‖ = ‖x‖ ^ ((1 : ℝ) - 2 * (r : ℝ)) := by
  have h2r := two_mul_lt_one_of_lt_half hr₁
  have hθ : 0 < 1 - 2 * r := tsub_pos_of_lt h2r
  have hcoe : ((1 - 2 * r : ℝ≥0) : ℝ) = 1 - 2 * (r : ℝ) := by push_cast [h2r.le]; rfl
  have hx₀ : 0 ≤ ‖x‖ := CStarModule.norm_nonneg A
  rw [norm_eq_sqrt_norm_inner_self (A := A) y, hyy,
    CFC.norm_nnrpow (inner A x x) hθ inner_self_nonneg, hcoe, ← norm_sq_eq A (x := x),
    Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_mul hx₀, ← Real.rpow_mul hx₀]
  congr 1
  ring

end Left

section Right

variable [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- Right-module form of `inner_left_of_nnrpow_inner_self_smul_eq`. -/
theorem unop_inner_left_of_op_nnrpow_unop_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • y = x)
    (hyy : unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r)) :
    unop (inner Aᵐᵒᵖ x y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - r) := by
  have hyx' : (inner Aᵐᵒᵖ x x ^ r) • y = x := by simpa using hyx
  have hyy' : inner Aᵐᵒᵖ y y = inner Aᵐᵒᵖ x x ^ (1 - 2 * r) :=
    unop_inj.mp (by simpa [CFC.unop_nnrpow] using hyy)
  simpa [CFC.unop_nnrpow] using
    congrArg unop (inner_left_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx' hyy')

/-- Right-module form of `inner_right_of_nnrpow_inner_self_smul_eq`. -/
theorem unop_inner_right_of_op_nnrpow_unop_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • y = x)
    (hyy : unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r)) :
    unop (inner Aᵐᵒᵖ y x) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - r) := by
  have hyx' : (inner Aᵐᵒᵖ x x ^ r) • y = x := by simpa using hyx
  have hyy' : inner Aᵐᵒᵖ y y = inner Aᵐᵒᵖ x x ^ (1 - 2 * r) :=
    unop_inj.mp (by simpa [CFC.unop_nnrpow] using hyy)
  simpa [CFC.unop_nnrpow] using
    congrArg unop (inner_right_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx' hyy')

/-- Right-module form of `norm_of_nnrpow_inner_self_smul_eq`. -/
theorem norm_of_op_nnrpow_unop_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₁ : r < 1 / 2)
    (hyy : unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r)) :
    ‖y‖ = ‖x‖ ^ ((1 : ℝ) - 2 * (r : ℝ)) := by
  have hyy' : inner Aᵐᵒᵖ y y = inner Aᵐᵒᵖ x x ^ (1 - 2 * r) :=
    unop_inj.mp (by simpa [CFC.unop_nnrpow] using hyy)
  exact norm_of_nnrpow_inner_self_smul_eq (A := Aᵐᵒᵖ) hr₁ hyy'

end Right

end AlgebraicNorm

section Topological

variable [NormedAddCommGroup E] [Module ℂ E]

section Left

variable [SMul A E] [CStarModule A E]

/-- Any factor `y` satisfying `(⟪x, x⟫_A ^ r) • y = x` and `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)`
(`0 < r < 1 / 2`) is the norm limit as `ε → 0⁺` of
`cfcₙ (fun t ↦ t ^ (1 / 2 - r) / (t ^ (1 / 2) + ε)) ⟪x, x⟫_A • x`. Completeness of `E` is not
needed. -/
theorem tendsto_cfcₙ_smul_of_nnrpow_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : (inner A x x ^ r) • y = x)
    (hyy : inner A y y = inner A x x ^ (1 - 2 * r)) :
    Tendsto
      (fun ε : ℝ≥0 ↦
        cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t (1 / 2 - r) / (NNReal.nnrpow t (1 / 2) + ε))
          (inner A x x) • x)
      (𝓝[>] 0) (𝓝 y) := by
  set a : A := inner A x x
  set s : ℝ≥0 := 1 / 2 - r
  have hs₀ : 0 < s := tsub_pos_of_lt hr₁
  have hs_le : s ≤ 1 / 2 := tsub_le_self
  have hsqrt_y : CFC.sqrt (inner A y y) = a ^ s := by
    rw [CFC.sqrt_eq_nnrpow, hyy, CFC.nnrpow_nnrpow, one_sub_two_mul_mul_half hr₁]
  have hrs : r + s = 1 / 2 := add_tsub_cancel_of_le hr₁.le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine (tendsto_iff_norm_sub_tendsto_zero.1
    (CFC.tendsto_cfcₙ_nnrpow_div_add_mul_nnrpow a hs₀ hs_le)).congr fun ε ↦ ?_
  set c : A := cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t s / (NNReal.nnrpow t (1 / 2) + ε)) a
  have hcx : c • x = (c * a ^ r) • y := by
    rw [← hyx, (semigroupAction A E).mul_smul]
  rw [hcx, norm_smul_sub_self, hsqrt_y, mul_assoc, ← CFC.nnrpow_add hr₀ hs₀, hrs]

/-- Any factor `y` satisfying `(⟪x, x⟫_A ^ r) • y = x` and `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)`
(`0 < r < 1 / 2`) belongs to the norm closure of `A • x`. -/
theorem mem_closure_range_smul_of_nnrpow_inner_self_smul_eq {x y : E} {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : (inner A x x ^ r) • y = x)
    (hyy : inner A y y = inner A x x ^ (1 - 2 * r)) :
    y ∈ closure (Set.range (· • x : A → E)) :=
  mem_closure_of_tendsto (tendsto_cfcₙ_smul_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx hyy)
    (Eventually.of_forall fun _ ↦ ⟨_, rfl⟩)

/-- Any closed `A`-invariant subset containing `x` also contains any fractional-power factor `y` of
`x` (`0 < r < 1 / 2`). -/
theorem mem_of_isClosed_of_nnrpow_inner_self_smul_eq {s : Set E} (hs : IsClosed s)
    (hsmul : ∀ a : A, ∀ z ∈ s, a • z ∈ s) {x y : E} (hx : x ∈ s) {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : (inner A x x ^ r) • y = x)
    (hyy : inner A y y = inner A x x ^ (1 - 2 * r)) :
    y ∈ s := by
  refine closure_minimal ?_ hs (mem_closure_range_smul_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx hyy)
  rintro _ ⟨a, rfl⟩
  exact hsmul a x hx

/-- Global uniqueness of the fractional-power factor: on any (not necessarily complete) Hilbert
C⋆-module, at most one vector `y : E` satisfies `(⟪x, x⟫_A ^ r) • y = x` and
`⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)` for a given `0 < r < 1 / 2`. -/
theorem eq_of_nnrpow_inner_self_smul_eq {x y z : E} {r : ℝ≥0} (hr₀ : 0 < r) (hr₁ : r < 1 / 2)
    (hyx : (inner A x x ^ r) • y = x) (hyy : inner A y y = inner A x x ^ (1 - 2 * r))
    (hzx : (inner A x x ^ r) • z = x) (hzz : inner A z z = inner A x x ^ (1 - 2 * r)) :
    y = z :=
  tendsto_nhds_unique
    (tendsto_cfcₙ_smul_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx hyy)
    (tendsto_cfcₙ_smul_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hzx hzz)

end Left

section Right

variable [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- Right-module form of `mem_closure_range_smul_of_nnrpow_inner_self_smul_eq`. -/
theorem mem_closure_range_op_smul_of_op_nnrpow_unop_inner_self_smul_eq {x y : E} {r : ℝ≥0}
    (hr₀ : 0 < r) (hr₁ : r < 1 / 2) (hyx : op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • y = x)
    (hyy : unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r)) :
    y ∈ closure (Set.range fun a : A ↦ op a • x) := by
  have hyx' : (inner Aᵐᵒᵖ x x ^ r) • y = x := by simpa using hyx
  have hyy' : inner Aᵐᵒᵖ y y = inner Aᵐᵒᵖ x x ^ (1 - 2 * r) :=
    unop_inj.mp (by simpa [CFC.unop_nnrpow] using hyy)
  rw [range_op_smul_eq]
  exact mem_closure_range_smul_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx' hyy'

/-- Right-module form of `mem_of_isClosed_of_nnrpow_inner_self_smul_eq`. -/
theorem mem_of_isClosed_of_op_nnrpow_unop_inner_self_smul_eq {s : Set E} (hs : IsClosed s)
    (hsmul : ∀ a : A, ∀ z ∈ s, op a • z ∈ s) {x y : E} (hx : x ∈ s) {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) (hyx : op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • y = x)
    (hyy : unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r)) :
    y ∈ s := by
  refine closure_minimal ?_ hs
    (mem_closure_range_op_smul_of_op_nnrpow_unop_inner_self_smul_eq hr₀ hr₁ hyx hyy)
  rintro _ ⟨a, rfl⟩
  exact hsmul a x hx

/-- Right-module form of `eq_of_nnrpow_inner_self_smul_eq`. -/
theorem eq_of_op_nnrpow_unop_inner_self_smul_eq {x y z : E} {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2)
    (hyx : op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • y = x)
    (hyy : unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r))
    (hzx : op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • z = x)
    (hzz : unop (inner Aᵐᵒᵖ z z) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r)) :
    y = z := by
  have hyx' : (inner Aᵐᵒᵖ x x ^ r) • y = x := by simpa using hyx
  have hyy' : inner Aᵐᵒᵖ y y = inner Aᵐᵒᵖ x x ^ (1 - 2 * r) :=
    unop_inj.mp (by simpa [CFC.unop_nnrpow] using hyy)
  have hzx' : (inner Aᵐᵒᵖ x x ^ r) • z = x := by simpa using hzx
  have hzz' : inner Aᵐᵒᵖ z z = inner Aᵐᵒᵖ x x ^ (1 - 2 * r) :=
    unop_inj.mp (by simpa [CFC.unop_nnrpow] using hzz)
  exact eq_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hyx' hyy' hzx' hzz'

end Right

end Topological

section Complete

variable [NormedAddCommGroup E] [Module ℂ E] [CompleteSpace E]

section Left

variable [SMul A E] [CStarModule A E]

/-- **Lance's fractional-power factorization.** In a complete Hilbert C⋆-module `E`, for every
`x : E` and `0 < r < 1 / 2`, there exists a unique `y : E` such that `(⟪x, x⟫_A ^ r) • y = x` and
`⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 - 2 * r)`. -/
theorem existsUnique_nnrpow_inner_self_smul_eq (x : E) {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) :
    ∃! y : E, (inner A x x ^ r) • y = x ∧ inner A y y = inner A x x ^ (1 - 2 * r) := by
  let _ : NormedSpace ℂ E := .ofCore (normedSpaceCore A)
  set a : A := inner A x x with ha_def
  set s : ℝ≥0 := 1 / 2 - r
  have hs₀ : 0 < s := tsub_pos_of_lt hr₁
  have hs_le : s ≤ 1 / 2 := tsub_le_self
  let c : ℝ≥0 → A := fun ε ↦
    cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t s / (NNReal.nnrpow t (1 / 2) + ε)) a
  let u : ℝ≥0 → A := fun ε ↦ c ε * a ^ (1 / 2 : ℝ≥0)
  let g : ℝ≥0 → E := fun ε ↦ c ε • x
  have hu_lim : Tendsto u (𝓝[>] 0) (𝓝 (a ^ s)) :=
    CFC.tendsto_cfcₙ_nnrpow_div_add_mul_nnrpow a hs₀ hs_le
  have hdist_eq : ∀ ε₁ ε₂ : ℝ≥0, dist (g ε₁) (g ε₂) = dist (u ε₁) (u ε₂) := fun ε₁ ε₂ ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← CStarModule.sub_smul, CStarModule.norm_smul,
      CFC.sqrt_eq_nnrpow, sub_mul]
  have hg_cauchy : Cauchy (map g (𝓝[>] 0)) := by
    rw [Metric.cauchy_iff]
    refine ⟨map_neBot, fun δ hδ ↦ ?_⟩
    obtain ⟨t, ht, hdist⟩ := (Metric.cauchy_iff.1 hu_lim.cauchy_map).2 δ hδ
    refine ⟨g '' (u ⁻¹' t), image_mem_map (mem_map.1 ht), ?_⟩
    rintro _ ⟨ε₁, hε₁, rfl⟩ _ ⟨ε₂, hε₂, rfl⟩
    rw [hdist_eq]
    exact hdist (u ε₁) hε₁ (u ε₂) hε₂
  obtain ⟨y, hy_lim⟩ := cauchy_map_iff_exists_tendsto.1 hg_cauchy
  have hyx : (a ^ r) • y = x := by
    have h₁ : Tendsto (fun ε ↦ (a ^ r) • g ε) (𝓝[>] 0) (𝓝 ((a ^ r) • y)) := by
      simpa only [Function.comp_def, smulCLM_apply] using
        ((smulCLM A E (a ^ r)).continuous.tendsto y).comp hy_lim
    have h₂ : Tendsto (fun ε ↦ (a ^ r) • g ε) (𝓝[>] 0) (𝓝 x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hmul : Tendsto (fun ε ↦ u ε * a ^ r) (𝓝[>] 0) (𝓝 (CFC.sqrt a)) := by
        have hsqrt : a ^ s * a ^ r = CFC.sqrt a := by
          rw [← CFC.nnrpow_add hs₀ hr₀, tsub_add_cancel_of_le hr₁.le, CFC.sqrt_eq_nnrpow]
        exact hsqrt ▸ hu_lim.mul_const (a ^ r)
      refine (tendsto_iff_norm_sub_tendsto_zero.1 hmul).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hcomm : a ^ r * c ε = c ε * a ^ r :=
        (CFC.commute_cfcₙ_nnrpow_div_add_nnrpow a hs₀ (1 / 2) hε r).symm.eq
      have hr_sqrt : a ^ r * CFC.sqrt a = a ^ (1 / 2 : ℝ≥0) * a ^ r := by
        rw [CFC.sqrt_eq_nnrpow, ← CFC.nnrpow_add hr₀ (by positivity), add_comm,
          CFC.nnrpow_add (by positivity) hr₀]
      dsimp only [g, u]
      rw [← (semigroupAction A E).mul_smul, hcomm, norm_smul_sub_self, ← ha_def,
        mul_assoc (c ε) (a ^ r), hr_sqrt, ← mul_assoc]
    exact tendsto_nhds_unique h₁ h₂
  have hyy : inner A y y = a ^ (1 - 2 * r) := by
    have hcont : Continuous fun z : E ↦ inner A z z :=
      continuous_inner.comp (continuous_id.prodMk continuous_id)
    have h₁ : Tendsto (fun ε ↦ inner A (g ε) (g ε)) (𝓝[>] 0) (𝓝 (inner A y y)) :=
      (hcont.tendsto y).comp hy_lim
    have h₂ : Tendsto (fun ε ↦ inner A (g ε) (g ε)) (𝓝[>] 0) (𝓝 (a ^ (1 - 2 * r))) := by
      have hlim : Tendsto (fun ε ↦ u ε * star (u ε)) (𝓝[>] 0) (𝓝 (a ^ s * star (a ^ s))) :=
        hu_lim.mul (continuous_star.tendsto _ |>.comp hu_lim)
      have htarget : a ^ s * star (a ^ s) = a ^ (1 - 2 * r) := by
        rw [CFC.nnrpow_nonneg.isSelfAdjoint.star_eq, ← CFC.nnrpow_add hs₀ hs₀,
          half_sub_add_half_sub hr₁]
      refine (htarget ▸ hlim).congr fun ε ↦ ?_
      dsimp only [g, u]
      rw [inner_smul_smul, CFC.sqrt_eq_nnrpow]
    exact tendsto_nhds_unique h₁ h₂
  exact ⟨y, ⟨hyx, hyy⟩, fun z ⟨hzx, hzz⟩ ↦
    eq_of_nnrpow_inner_self_smul_eq hr₀ hr₁ hzx hzz hyx hyy⟩

end Left

section Right

variable [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- **Lance's fractional-power factorization for right Hilbert C⋆-modules.** In a complete right
Hilbert `A`-module `E`, for every `x : E` and `0 < r < 1 / 2`, there exists a unique `y : E` such
that `op (⟨x, x⟩_A ^ r) • y = x` and `⟨y, y⟩_A = ⟨x, x⟩_A ^ (1 - 2 * r)`. -/
theorem existsUnique_op_nnrpow_unop_inner_self_smul_eq (x : E) {r : ℝ≥0} (hr₀ : 0 < r)
    (hr₁ : r < 1 / 2) :
    ∃! y : E, op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • y = x ∧
      unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r) := by
  have hiff : ∀ y : E,
      (op ((unop (inner Aᵐᵒᵖ x x)) ^ r) • y = x ∧
        unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 - 2 * r)) ↔
      ((inner Aᵐᵒᵖ x x ^ r) • y = x ∧ inner Aᵐᵒᵖ y y = inner Aᵐᵒᵖ x x ^ (1 - 2 * r)) := by
    intro y
    simp only [CFC.op_nnrpow, op_unop, ← unop_inj (x := inner Aᵐᵒᵖ y y), CFC.unop_nnrpow]
  simpa only [hiff] using existsUnique_nnrpow_inner_self_smul_eq (A := Aᵐᵒᵖ) x hr₀ hr₁

end Right

end Complete

end FractionalPower

/-! ### Self-inner-product factorization (`(⟪y, y⟫_A ^ p) • y = x` and `⟪y, y⟫_A • y = x`) -/

section SelfInnerFactorization

private lemma div_two_mul_add_one_pos {p : ℝ≥0} (hp : 0 < p) : 0 < p / (2 * p + 1) :=
  div_pos hp (by positivity)

private lemma div_two_mul_add_one_lt_half (p : ℝ≥0) : p / (2 * p + 1) < 1 / 2 := by
  rw [← NNReal.coe_lt_coe]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) two_pos]
  linarith

private lemma one_sub_two_mul_div_two_mul_add_one (p : ℝ≥0) :
    1 - 2 * (p / (2 * p + 1)) = (2 * p + 1)⁻¹ := by
  have hle : 2 * (p / (2 * p + 1)) ≤ 1 :=
    (two_mul_lt_one_of_lt_half (div_two_mul_add_one_lt_half p)).le
  ext
  push_cast [hle]
  field_simp
  ring

private lemma one_sub_div_two_mul_add_one (p : ℝ≥0) :
    1 - p / (2 * p + 1) = (p + 1) / (2 * p + 1) := by
  have hle : p / (2 * p + 1) ≤ 1 :=
    (lt_one_of_lt_half (div_two_mul_add_one_lt_half p)).le
  ext
  push_cast [hle]
  field_simp
  ring

section AlgebraicNorm

variable [AddCommGroup E] [Module ℂ E] [Norm E]

section Left

variable [SMul A E] [CStarModule A E]

/-- If `(⟪y, y⟫_A ^ p) • y = x` with `0 < p`, then `⟪y, y⟫_A = ⟪x, x⟫_A ^ (2 * p + 1)⁻¹`. -/
theorem inner_self_of_nnrpow_inner_self_smul_self_eq {x y : E} {p : ℝ≥0} (hp : 0 < p)
    (hy : (inner A y y ^ p) • y = x) :
    inner A y y = inner A x x ^ (2 * p + 1)⁻¹ := by
  have hxx : inner A x x = inner A y y ^ (2 * p + 1) := by
    calc
      inner A x x = inner A ((inner A y y ^ p) • y) ((inner A y y ^ p) • y) := by rw [hy]
      _ = inner A y y ^ p * inner A y y * star (inner A y y ^ p) := by
        rw [inner_op_smul_left, inner_op_smul_right]
      _ = inner A y y ^ p * inner A y y ^ (1 : ℝ≥0) * inner A y y ^ p := by
        rw [CFC.nnrpow_one (inner A y y) inner_self_nonneg,
          CFC.nnrpow_nonneg.isSelfAdjoint.star_eq]
      _ = inner A y y ^ (p + 1 + p) := by
        rw [← CFC.nnrpow_add hp zero_lt_one, ← CFC.nnrpow_add (by positivity) hp]
      _ = inner A y y ^ (2 * p + 1) := by congr 1; ring
  exact ((CFC.nnrpow_inv_eq (inner A x x) (inner A y y) (by positivity)
    inner_self_nonneg inner_self_nonneg).2 hxx.symm).symm

/-- If `(⟪y, y⟫_A ^ p) • y = x` with `0 < p`, then `(⟪x, x⟫_A ^ (p / (2 * p + 1))) • y = x`. -/
theorem nnrpow_inner_self_smul_eq_of_nnrpow_inner_self_smul_self_eq {x y : E} {p : ℝ≥0}
    (hp : 0 < p) (hy : (inner A y y ^ p) • y = x) :
    (inner A x x ^ (p / (2 * p + 1))) • y = x := by
  have hyy := inner_self_of_nnrpow_inner_self_smul_self_eq hp hy
  have hp_eq : (2 * p + 1)⁻¹ * p = p / (2 * p + 1) := by rw [mul_comm, div_eq_mul_inv]
  rwa [hyy, CFC.nnrpow_nnrpow, hp_eq] at hy

/-- If `(⟪y, y⟫_A ^ p) • y = x` with `0 < p`, then
`⟪x, y⟫_A = ⟪x, x⟫_A ^ ((p + 1) / (2 * p + 1))`. -/
theorem inner_left_of_nnrpow_inner_self_smul_self_eq {x y : E} {p : ℝ≥0} (hp : 0 < p)
    (hy : (inner A y y ^ p) • y = x) :
    inner A x y = inner A x x ^ ((p + 1) / (2 * p + 1)) := by
  have hyx := nnrpow_inner_self_smul_eq_of_nnrpow_inner_self_smul_self_eq hp hy
  have hyy : inner A y y = inner A x x ^ (1 - 2 * (p / (2 * p + 1))) := by
    rw [one_sub_two_mul_div_two_mul_add_one]
    exact inner_self_of_nnrpow_inner_self_smul_self_eq hp hy
  rw [← one_sub_div_two_mul_add_one]
  exact inner_left_of_nnrpow_inner_self_smul_eq (div_two_mul_add_one_pos hp)
    (div_two_mul_add_one_lt_half p) hyx hyy

/-- If `(⟪y, y⟫_A ^ p) • y = x` with `0 < p`, then
`⟪y, x⟫_A = ⟪x, x⟫_A ^ ((p + 1) / (2 * p + 1))`. -/
theorem inner_right_of_nnrpow_inner_self_smul_self_eq {x y : E} {p : ℝ≥0} (hp : 0 < p)
    (hy : (inner A y y ^ p) • y = x) :
    inner A y x = inner A x x ^ ((p + 1) / (2 * p + 1)) := by
  rw [← star_inner, inner_left_of_nnrpow_inner_self_smul_self_eq hp hy,
    CFC.nnrpow_nonneg.isSelfAdjoint.star_eq]

/-- If `(⟪y, y⟫_A ^ p) • y = x` with `0 < p`, then `‖y‖ = ‖x‖ ^ (2 * p + 1)⁻¹`. -/
theorem norm_of_nnrpow_inner_self_smul_self_eq {x y : E} {p : ℝ≥0} (hp : 0 < p)
    (hy : (inner A y y ^ p) • y = x) :
    ‖y‖ = ‖x‖ ^ (2 * (p : ℝ) + 1)⁻¹ := by
  have hyy : inner A y y = inner A x x ^ (1 - 2 * (p / (2 * p + 1))) := by
    rw [one_sub_two_mul_div_two_mul_add_one]
    exact inner_self_of_nnrpow_inner_self_smul_self_eq hp hy
  have hexp : (1 : ℝ) - 2 * ((p / (2 * p + 1) : ℝ≥0) : ℝ) = (2 * (p : ℝ) + 1)⁻¹ := by
    have h := congrArg NNReal.toReal (one_sub_two_mul_div_two_mul_add_one p)
    have hle : 2 * (p / (2 * p + 1)) ≤ 1 :=
      (two_mul_lt_one_of_lt_half (div_two_mul_add_one_lt_half p)).le
    simpa [hle] using h
  rw [← hexp]
  exact norm_of_nnrpow_inner_self_smul_eq (div_two_mul_add_one_lt_half p) hyy

/-- If `⟪y, y⟫_A • y = x`, then `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 / 3)`. -/
theorem inner_self_of_inner_self_smul_self_eq {x y : E} (hy : inner A y y • y = x) :
    inner A y y = inner A x x ^ (1 / 3 : ℝ≥0) := by
  have hy' : (inner A y y ^ (1 : ℝ≥0)) • y = x := by
    rwa [CFC.nnrpow_one (inner A y y) inner_self_nonneg]
  have h := inner_self_of_nnrpow_inner_self_smul_self_eq zero_lt_one hy'
  norm_num at h
  exact h

/-- If `⟪y, y⟫_A • y = x`, then `⟪x, y⟫_A = ⟪x, x⟫_A ^ (2 / 3)`. -/
theorem inner_left_of_inner_self_smul_self_eq {x y : E} (hy : inner A y y • y = x) :
    inner A x y = inner A x x ^ (2 / 3 : ℝ≥0) := by
  have hy' : (inner A y y ^ (1 : ℝ≥0)) • y = x := by
    rwa [CFC.nnrpow_one (inner A y y) inner_self_nonneg]
  have h := inner_left_of_nnrpow_inner_self_smul_self_eq zero_lt_one hy'
  norm_num at h
  exact h

/-- If `⟪y, y⟫_A • y = x`, then `⟪y, x⟫_A = ⟪x, x⟫_A ^ (2 / 3)`. -/
theorem inner_right_of_inner_self_smul_self_eq {x y : E} (hy : inner A y y • y = x) :
    inner A y x = inner A x x ^ (2 / 3 : ℝ≥0) := by
  rw [← star_inner, inner_left_of_inner_self_smul_self_eq hy,
    CFC.nnrpow_nonneg.isSelfAdjoint.star_eq]

/-- If `⟪y, y⟫_A • y = x`, then `‖y‖ = ‖x‖ ^ (1 / 3)`. -/
theorem norm_of_inner_self_smul_self_eq {x y : E} (hy : inner A y y • y = x) :
    ‖y‖ = ‖x‖ ^ (1 / 3 : ℝ) := by
  have hy' : (inner A y y ^ (1 : ℝ≥0)) • y = x := by
    rwa [CFC.nnrpow_one (inner A y y) inner_self_nonneg]
  have h := norm_of_nnrpow_inner_self_smul_self_eq zero_lt_one hy'
  norm_num at h
  exact h

end Left

section Right

variable [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- If `y ⟨y, y⟩_A = x` in a right Hilbert `A`-module, then `⟨y, y⟩_A = ⟨x, x⟩_A ^ (1 / 3)`. -/
theorem unop_inner_self_of_op_unop_inner_self_smul_self_eq {x y : E}
    (hy : op (unop (inner Aᵐᵒᵖ y y)) • y = x) :
    unop (inner Aᵐᵒᵖ y y) = (unop (inner Aᵐᵒᵖ x x)) ^ (1 / 3 : ℝ≥0) := by
  rw [op_unop] at hy
  simpa [CFC.unop_nnrpow] using congrArg unop (inner_self_of_inner_self_smul_self_eq hy)

/-- If `y ⟨y, y⟩_A = x` in a right Hilbert `A`-module, then `⟨x, y⟩_A = ⟨x, x⟩_A ^ (2 / 3)`. -/
theorem unop_inner_left_of_op_unop_inner_self_smul_self_eq {x y : E}
    (hy : op (unop (inner Aᵐᵒᵖ y y)) • y = x) :
    unop (inner Aᵐᵒᵖ x y) = (unop (inner Aᵐᵒᵖ x x)) ^ (2 / 3 : ℝ≥0) := by
  rw [op_unop] at hy
  simpa [CFC.unop_nnrpow] using congrArg unop (inner_left_of_inner_self_smul_self_eq hy)

/-- If `y ⟨y, y⟩_A = x` in a right Hilbert `A`-module, then `⟨y, x⟩_A = ⟨x, x⟩_A ^ (2 / 3)`. -/
theorem unop_inner_right_of_op_unop_inner_self_smul_self_eq {x y : E}
    (hy : op (unop (inner Aᵐᵒᵖ y y)) • y = x) :
    unop (inner Aᵐᵒᵖ y x) = (unop (inner Aᵐᵒᵖ x x)) ^ (2 / 3 : ℝ≥0) := by
  rw [op_unop] at hy
  simpa [CFC.unop_nnrpow] using congrArg unop (inner_right_of_inner_self_smul_self_eq hy)

/-- If `y ⟨y, y⟩_A = x` in a right Hilbert `A`-module, then `‖y‖ = ‖x‖ ^ (1 / 3)`. -/
theorem norm_of_op_unop_inner_self_smul_self_eq {x y : E}
    (hy : op (unop (inner Aᵐᵒᵖ y y)) • y = x) :
    ‖y‖ = ‖x‖ ^ (1 / 3 : ℝ) := by
  rw [op_unop] at hy
  exact norm_of_inner_self_smul_self_eq (A := Aᵐᵒᵖ) hy

end Right

end AlgebraicNorm

section Topological

variable [NormedAddCommGroup E] [Module ℂ E]

section Left

variable [SMul A E] [CStarModule A E]

/-- Any solution `y` of `(⟪y, y⟫_A ^ p) • y = x` (`0 < p`) belongs to the norm closure of
`A • x`. -/
theorem mem_closure_range_smul_of_nnrpow_inner_self_smul_self_eq {x y : E} {p : ℝ≥0} (hp : 0 < p)
    (hy : (inner A y y ^ p) • y = x) :
    y ∈ closure (Set.range (· • x : A → E)) := by
  have hyy : inner A y y = inner A x x ^ (1 - 2 * (p / (2 * p + 1))) := by
    rw [one_sub_two_mul_div_two_mul_add_one]
    exact inner_self_of_nnrpow_inner_self_smul_self_eq hp hy
  exact mem_closure_range_smul_of_nnrpow_inner_self_smul_eq (div_two_mul_add_one_pos hp)
    (div_two_mul_add_one_lt_half p)
    (nnrpow_inner_self_smul_eq_of_nnrpow_inner_self_smul_self_eq hp hy) hyy

/-- Any closed `A`-invariant subset containing `x` also contains any solution `y` of
`(⟪y, y⟫_A ^ p) • y = x` (`0 < p`). -/
theorem mem_of_isClosed_of_nnrpow_inner_self_smul_self_eq {s : Set E} (hs : IsClosed s)
    (hsmul : ∀ a : A, ∀ z ∈ s, a • z ∈ s) {x y : E} (hx : x ∈ s) {p : ℝ≥0} (hp : 0 < p)
    (hy : (inner A y y ^ p) • y = x) :
    y ∈ s := by
  refine closure_minimal ?_ hs (mem_closure_range_smul_of_nnrpow_inner_self_smul_self_eq hp hy)
  rintro _ ⟨a, rfl⟩
  exact hsmul a x hx

/-- Global uniqueness of `(⟪y, y⟫_A ^ p) • y = x` (`0 < p`) on any (not necessarily complete)
Hilbert C⋆-module. -/
theorem eq_of_nnrpow_inner_self_smul_self_eq {x y z : E} {p : ℝ≥0} (hp : 0 < p)
    (hy : (inner A y y ^ p) • y = x) (hz : (inner A z z ^ p) • z = x) :
    y = z := by
  have hyy : inner A y y = inner A x x ^ (1 - 2 * (p / (2 * p + 1))) := by
    rw [one_sub_two_mul_div_two_mul_add_one]
    exact inner_self_of_nnrpow_inner_self_smul_self_eq hp hy
  have hzz : inner A z z = inner A x x ^ (1 - 2 * (p / (2 * p + 1))) := by
    rw [one_sub_two_mul_div_two_mul_add_one]
    exact inner_self_of_nnrpow_inner_self_smul_self_eq hp hz
  exact eq_of_nnrpow_inner_self_smul_eq (div_two_mul_add_one_pos hp)
    (div_two_mul_add_one_lt_half p)
    (nnrpow_inner_self_smul_eq_of_nnrpow_inner_self_smul_self_eq hp hy) hyy
    (nnrpow_inner_self_smul_eq_of_nnrpow_inner_self_smul_self_eq hp hz) hzz

/-- Any solution `y` of `⟪y, y⟫_A • y = x` belongs to the norm closure of `A • x`. -/
theorem mem_closure_range_smul_of_inner_self_smul_self_eq {x y : E} (hy : inner A y y • y = x) :
    y ∈ closure (Set.range (· • x : A → E)) := by
  have hy' : (inner A y y ^ (1 : ℝ≥0)) • y = x := by
    rwa [CFC.nnrpow_one (inner A y y) inner_self_nonneg]
  exact mem_closure_range_smul_of_nnrpow_inner_self_smul_self_eq zero_lt_one hy'

/-- Any closed `A`-invariant subset containing `x` also contains any solution `y` of
`⟪y, y⟫_A • y = x`. -/
theorem mem_of_isClosed_of_inner_self_smul_self_eq {s : Set E} (hs : IsClosed s)
    (hsmul : ∀ a : A, ∀ z ∈ s, a • z ∈ s) {x y : E} (hx : x ∈ s) (hy : inner A y y • y = x) :
    y ∈ s := by
  have hy' : (inner A y y ^ (1 : ℝ≥0)) • y = x := by
    rwa [CFC.nnrpow_one (inner A y y) inner_self_nonneg]
  exact mem_of_isClosed_of_nnrpow_inner_self_smul_self_eq hs hsmul hx zero_lt_one hy'

/-- Global uniqueness of `⟪y, y⟫_A • y = x` on any (not necessarily complete) Hilbert
C⋆-module. -/
theorem eq_of_inner_self_smul_self_eq {x y z : E} (hy : inner A y y • y = x)
    (hz : inner A z z • z = x) : y = z := by
  have hy' : (inner A y y ^ (1 : ℝ≥0)) • y = x := by
    rwa [CFC.nnrpow_one (inner A y y) inner_self_nonneg]
  have hz' : (inner A z z ^ (1 : ℝ≥0)) • z = x := by
    rwa [CFC.nnrpow_one (inner A z z) inner_self_nonneg]
  exact eq_of_nnrpow_inner_self_smul_self_eq zero_lt_one hy' hz'

end Left

section Right

variable [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- If `y ⟨y, y⟩_A = x` in a right Hilbert `A`-module, then `y` belongs to the norm closure of
`x • A`. -/
theorem mem_closure_range_op_smul_of_op_unop_inner_self_smul_self_eq {x y : E}
    (hy : op (unop (inner Aᵐᵒᵖ y y)) • y = x) :
    y ∈ closure (Set.range fun a : A ↦ op a • x) := by
  rw [op_unop] at hy
  rw [range_op_smul_eq]
  exact mem_closure_range_smul_of_inner_self_smul_self_eq hy

/-- Any closed right-`A`-invariant subset containing `x` also contains any solution `y` of
`y ⟨y, y⟩_A = x`. -/
theorem mem_of_isClosed_of_op_unop_inner_self_smul_self_eq {s : Set E} (hs : IsClosed s)
    (hsmul : ∀ a : A, ∀ z ∈ s, op a • z ∈ s) {x y : E} (hx : x ∈ s)
    (hy : op (unop (inner Aᵐᵒᵖ y y)) • y = x) :
    y ∈ s := by
  refine closure_minimal ?_ hs (mem_closure_range_op_smul_of_op_unop_inner_self_smul_self_eq hy)
  rintro _ ⟨a, rfl⟩
  exact hsmul a x hx

/-- Global uniqueness of `y ⟨y, y⟩_A = x` on any (not necessarily complete) right Hilbert
`A`-module. -/
theorem eq_of_op_unop_inner_self_smul_self_eq {x y z : E}
    (hy : op (unop (inner Aᵐᵒᵖ y y)) • y = x)
    (hz : op (unop (inner Aᵐᵒᵖ z z)) • z = x) : y = z := by
  rw [op_unop] at hy hz
  exact eq_of_inner_self_smul_self_eq (A := Aᵐᵒᵖ) hy hz

end Right

end Topological

section Complete

variable [NormedAddCommGroup E] [Module ℂ E] [CompleteSpace E]

section Left

variable [SMul A E] [CStarModule A E]

/-- In a complete Hilbert C⋆-module `E`, for every `x : E` and `0 < p : ℝ≥0`, there exists a unique
`y : E` such that `(⟪y, y⟫_A ^ p) • y = x`. -/
theorem existsUnique_nnrpow_inner_self_smul_self_eq (x : E) {p : ℝ≥0} (hp : 0 < p) :
    ∃! y : E, (inner A y y ^ p) • y = x := by
  obtain ⟨y, ⟨hyx, hyy⟩, -⟩ := existsUnique_nnrpow_inner_self_smul_eq (A := A) x
    (div_two_mul_add_one_pos hp) (div_two_mul_add_one_lt_half p)
  rw [one_sub_two_mul_div_two_mul_add_one] at hyy
  have hyp : inner A y y ^ p = inner A x x ^ (p / (2 * p + 1)) := by
    rw [hyy, CFC.nnrpow_nnrpow, mul_comm, ← div_eq_mul_inv]
  have hy : (inner A y y ^ p) • y = x := by rwa [hyp]
  exact ⟨y, hy, fun z hz ↦ eq_of_nnrpow_inner_self_smul_self_eq hp hz hy⟩

/-- **Canonical self-inner-product factorization.** In a complete Hilbert C⋆-module `E`, every
vector `x : E` factors uniquely as `⟪y, y⟫_A • y = x`. -/
theorem existsUnique_inner_self_smul_self_eq (x : E) :
    ∃! y : E, inner A y y • y = x := by
  have hiff : ∀ y : E, inner A y y • y = x ↔ (inner A y y ^ (1 : ℝ≥0)) • y = x := fun y ↦ by
    rw [CFC.nnrpow_one (inner A y y) inner_self_nonneg]
  simpa only [hiff] using existsUnique_nnrpow_inner_self_smul_self_eq (A := A) x zero_lt_one

end Left

section Right

variable [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- In a complete right Hilbert `A`-module `E`, for every `x : E` and `0 < p : ℝ≥0`, there exists a
unique `y : E` such that `y (⟨y, y⟩_A ^ p) = x`
(written `op ((unop (inner Aᵐᵒᵖ y y)) ^ p) • y = x`). -/
theorem existsUnique_op_nnrpow_unop_inner_self_smul_self_eq (x : E) {p : ℝ≥0} (hp : 0 < p) :
    ∃! y : E, op ((unop (inner Aᵐᵒᵖ y y)) ^ p) • y = x := by
  simpa only [CFC.op_nnrpow, op_unop] using
    existsUnique_nnrpow_inner_self_smul_self_eq (A := Aᵐᵒᵖ) x hp

/-- **Canonical self-inner-product factorization for right Hilbert C⋆-modules.** In a complete
right Hilbert `A`-module `E`, every vector `x : E` factors uniquely as `y ⟨y, y⟩_A = x`
(written `op (unop (inner Aᵐᵒᵖ y y)) • y = x`). -/
theorem existsUnique_op_unop_inner_self_smul_self_eq (x : E) :
    ∃! y : E, op (unop (inner Aᵐᵒᵖ y y)) • y = x := by
  simpa only [op_unop] using existsUnique_inner_self_smul_self_eq (A := Aᵐᵒᵖ) x

end Right

end Complete

end SelfInnerFactorization

end CStarModule
