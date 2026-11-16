/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.Runge.ZeroFree
import TauCeti.Analysis.Normed.Module.Exhaustion

/-!
# Prescribed zeros, divisor realization, and holomorphic quotients on open plane sets

Every meromorphic function on an open subset `Ω ⊆ ℂ` has a locally finitely supported divisor
`MeromorphicOn.divisor F Ω : Function.locallyFinsuppWithin Ω ℤ`. Conversely, Weierstrass's theorem
for arbitrary open plane sets realizes *every* locally finitely supported multiplicity function on
`Ω` by a holomorphic or meromorphic function on `Ω`, without connectedness or simple-connectivity
assumptions on `Ω`.

Unlike the classical entire Weierstrass product on `ℂ`, where zeros can only escape to `∞` and are
tamed by explicit exponential elementary factors, zeros of a locally finite configuration in a
general open set `Ω` accumulate along `frontier Ω` (possibly in infinitely many holes). Exhausting
`Ω` by compact sets `K n ⊆ interior (K (n + 1))` that are filled in `Ω`
(`IsOpen.exists_isFilledIn_compact_exhaustion`), the finite polynomial `P k` collecting the zeros in
`K (k + 1) \ K k` is nonvanishing on `K k`. Zero-free Runge approximation
(`TauCeti.IsFilledIn.exists_differentiableOn_ne_zero_norm_sub_lt`) then approximates `(P k ·)⁻¹` on
`K k` by a function `g k` holomorphic and *nowhere zero on all of `Ω`* so that
`‖P k z * g k z - 1‖ ≤ (1 / 2) ^ (k + 1)` on `K k`, making the infinite product converge locally
uniformly on `Ω` without introducing any extraneous zeros.

## Main results

* `IsOpen.exists_differentiableOn_analyticOrderAt_eq`: for any open `Ω ⊆ ℂ` and
  `m : Function.locallyFinsuppWithin Ω ℕ`, there exists `f` holomorphic on `Ω` with
  `analyticOrderAt f z = m z` for every `z ∈ Ω`.
* `IsOpen.exists_differentiableOn_divisor_eq_of_nonneg`: every nonnegative divisor
  `0 ≤ ν : Function.locallyFinsuppWithin Ω ℤ` is realized by a holomorphic function on `Ω` with
  finite order everywhere on `Ω`.
* `IsOpen.exists_meromorphicOn_divisor_eq`: every divisor `ν : Function.locallyFinsuppWithin Ω ℤ`
  is realized by a meromorphic function `f` on `Ω` satisfying `meromorphicOrderAt f z = ν z` for
  all `z ∈ Ω`.
* `MeromorphicOn.exists_differentiableOn_eq_div`: every function `F` meromorphic on an open set
  `Ω ⊆ ℂ` is representable as a quotient `f / g` of functions holomorphic on `Ω`, where `g`
  realizes the pole divisor `(MeromorphicOn.divisor F Ω)⁻` (hence vanishes nowhere identically on
  any component of `Ω`), `f / g =ᶠ[𝓝[≠] z] F` at every `z ∈ Ω`, and `g z ≠ 0 ∧ F z = f z / g z`
  codiscretely within `Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 15.3 and Corollary 15.4.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorems 15.11 and 15.12.
-/

public section

open Complex Filter Function Metric Set
open scoped Topology

section Helpers

/-- Intersecting a compact subset `K ⊆ Ω` with the support of `m : locallyFinsuppWithin Ω ℕ`
produces a finite set. -/
private theorem finite_inter_support_of_isCompact {Ω : Set ℂ}
    (m : Function.locallyFinsuppWithin Ω ℕ) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (K ∩ m.support).Finite := by
  refine ((m.restrict hKΩ).finiteSupport hK).subset fun z hz ↦ ?_
  rw [Function.mem_support, m.restrict_eqOn hKΩ hz.1]
  exact hz.2

/-- Entire differentiability of a finite product of centered monomials `∏ a ∈ s, (z - a) ^ m a`. -/
private theorem differentiable_finset_prod_sub_pow (s : Finset ℂ) (m : ℂ → ℕ) :
    Differentiable ℂ fun z : ℂ ↦ ∏ a ∈ s, (z - a) ^ m a := by
  classical
  induction s using Finset.induction with
  | empty => simp [differentiable_const]
  | insert a s ha ih =>
    have hmon : Differentiable ℂ fun z : ℂ ↦ (z - a) ^ m a := by fun_prop
    simpa only [Finset.prod_insert ha] using hmon.fun_mul ih

/-- Analytic order at `z₀` of a finite product of centered monomials `∏ a ∈ s, (z - a) ^ m a`. -/
private theorem analyticOrderAt_finset_prod_sub_pow (s : Finset ℂ) (m : ℂ → ℕ) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ ↦ ∏ a ∈ s, (z - a) ^ m a) z₀ =
      if z₀ ∈ s then (m z₀ : ℕ∞) else 0 := by
  classical
  have hprod : (fun z : ℂ ↦ ∏ a ∈ s, (z - a) ^ m a) = ∏ a ∈ s, fun z : ℂ ↦ (z - a) ^ m a :=
    funext fun z ↦ (Finset.prod_apply z s fun a w ↦ (w - a) ^ m a).symm
  have han : ∀ a : ℂ, AnalyticAt ℂ (fun z : ℂ ↦ (z - a) ^ m a) z₀ := fun a ↦
    ((differentiable_id.sub_const a).pow (m a)).analyticAt z₀
  rw [hprod, TauCeti.analyticOrderAt_prod fun a _ ↦ han a]
  have hterm : ∀ a ∈ s, analyticOrderAt (fun z : ℂ ↦ (z - a) ^ m a) z₀ =
      if a = z₀ then (m z₀ : ℕ∞) else 0 := fun a _ ↦ by
    split_ifs with h
    · subst h
      exact analyticOrderAt_centeredMonomial
    · exact (han a).analyticOrderAt_eq_zero.mpr (pow_ne_zero (m a) (sub_ne_zero.mpr (Ne.symm h)))
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']

/-- Pointwise product of finitely many holomorphic functions on `V` is holomorphic on `V`. -/
private theorem differentiableOn_finset_range_prod {V : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) V) :
    ∀ N : ℕ, DifferentiableOn ℂ (fun z ↦ ∏ k ∈ Finset.range N, F k z) V
  | 0 => by simp [differentiableOn_const]
  | N + 1 => by
    simpa only [Finset.prod_range_succ] using
      (differentiableOn_finset_range_prod hF N).fun_mul (hF N)

/-- For a polynomial `P` nonvanishing on a compact set `K ⊆ Ω` filled in `Ω`, zero-free Runge
approximation produces `g` holomorphic and nowhere zero on `Ω` with `‖P z * g z - 1‖ ≤ ε` on `K`. -/
private theorem exists_zeroFree_factor_norm_mul_sub_one_le {K Ω : Set ℂ}
    (hfill : TauCeti.IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) (hPK : ∀ z ∈ K, P z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ Ω, g z ≠ 0) ∧
      ∀ z ∈ K, ‖P z * g z - 1‖ ≤ ε := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hP.continuous.continuousOn
  set C : ℝ := max M 0 + 1
  have hC_pos : 0 < C := by positivity
  set U : Set ℂ := {z | P z ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hP.continuous continuous_const
  have hu_diff : DifferentiableOn ℂ (fun z ↦ (P z)⁻¹) U :=
    hP.differentiableOn.inv fun _ hz ↦ hz
  obtain ⟨g, hg_diff, hg_ne, hg_approx⟩ := hfill.exists_differentiableOn_ne_zero_norm_sub_lt
    hΩ hK hKΩ hU hPK hu_diff (fun z hz ↦ inv_ne_zero (hPK z hz)) (div_pos hε hC_pos)
  refine ⟨g, hg_diff, hg_ne, fun z hz ↦ ?_⟩
  have hPz : P z ≠ 0 := hPK z hz
  have hrew : P z * g z - 1 = P z * (g z - (P z)⁻¹) := by
    rw [mul_sub, mul_inv_cancel₀ hPz]
  have hnormP : ‖P z‖ ≤ C := (hM z hz).trans ((le_max_left M 0).trans (lt_add_one _).le)
  rw [hrew, norm_mul, norm_sub_rev (g z)]
  exact (mul_le_mul hnormP (hg_approx z hz).le (norm_nonneg _) hC_pos.le).trans_eq
    (mul_div_cancel₀ ε hC_pos.ne')

/-- An infinite product `∏' j, (1 + ψ j z)` on an open set `V ⊆ ℂ` whose terms `ψ j` are
holomorphic on `V` and bounded by `(1 / 2) ^ (j + 1)` is holomorphic and nowhere zero on `V`. -/
private theorem differentiableOn_and_ne_zero_tprod_one_add {V : Set ℂ} (hV : IsOpen V)
    {ψ : ℕ → ℂ → ℂ} (hψ_diff : ∀ j, DifferentiableOn ℂ (ψ j) V)
    (hψ_le : ∀ j, ∀ z ∈ V, ‖ψ j z‖ ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    DifferentiableOn ℂ (fun z ↦ ∏' j, (1 + ψ j z)) V ∧
      ∀ z ∈ V, (∏' j, (1 + ψ j z)) ≠ 0 := by
  have hu : Summable (fun j : ℕ ↦ (1 / 2 : ℝ) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr summable_geometric_two
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add hV hu
    (Eventually.of_forall hψ_le) (fun j ↦ (hψ_diff j).continuousOn)
  have hfin_diff := differentiableOn_finset_range_prod (V := V)
    fun j ↦ (differentiableOn_const 1).fun_add (hψ_diff j)
  refine ⟨hprod.tendstoLocallyUniformlyOn_finsetRange.differentiableOn
    (Eventually.of_forall hfin_diff) hV, fun z hz ↦ ?_⟩
  have hsum : Summable (fun j ↦ ψ j z) := hu.of_norm_bounded fun j ↦ hψ_le j z hz
  have hne : ∀ j, 1 + ψ j z ≠ 0 := fun j h0 ↦ by
    have hnorm1 : ‖ψ j z‖ = 1 := by
      rw [eq_neg_of_add_eq_zero_right h0, norm_neg, norm_one]
    have hle : ‖ψ j z‖ ≤ 1 / 2 := (hψ_le j z hz).trans <| by
      simpa using pow_le_pow_of_le_one (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (Nat.succ_pos j)
    linarith
  rw [← Complex.cexp_tsum_eq_tprod hne (Complex.summable_log_one_add_of_summable hsum)]
  exact Complex.exp_ne_zero _

/-- Telescopic identity combining the initial zero polynomial and shell zero polynomials along a
monotone sequence of finite zero sets `T`. -/
private theorem prod_sub_pow_telescopic [DecidableEq ℂ] {T : ℕ → Finset ℂ} (hT : Monotone T)
    (m : ℂ → ℕ) (z : ℂ) :
    ∀ N : ℕ, (∏ a ∈ T 0, (z - a) ^ m a) *
      (∏ k ∈ Finset.range N, ∏ a ∈ T (k + 1) \ T k, (z - a) ^ m a) =
        ∏ a ∈ T N, (z - a) ^ m a
  | 0 => by simp
  | N + 1 => by
    rw [Finset.prod_range_succ, ← mul_assoc, prod_sub_pow_telescopic hT m z N,
      ← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (hT (Nat.le_succ N))]

/-- Splitting an infinite product `P₀ z * ∏' k, (1 + (P k z * g k z - 1))` at index `M` on an
open set `V ⊆ Ω` where `‖P (j + M) z * g (j + M) z - 1‖ ≤ (1 / 2) ^ (j + 1)` separates the finite
polynomial head `P₀ z * ∏ k < M, P k z` from a holomorphic nonvanishing unit on `V`. -/
private theorem exists_local_tprod_unit {Ω V : Set ℂ} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (P₀ : ℂ → ℂ) {P g : ℕ → ℂ → ℂ} (hP : ∀ k, Differentiable ℂ (P k))
    (hg_diff : ∀ k, DifferentiableOn ℂ (g k) Ω) (hg_ne : ∀ k, ∀ z ∈ Ω, g k z ≠ 0)
    (M : ℕ)
    (htail : ∀ j, ∀ z ∈ V, ‖P (j + M) z * g (j + M) z - 1‖ ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    ∃ U : ℂ → ℂ, DifferentiableOn ℂ U V ∧ (∀ z ∈ V, U z ≠ 0) ∧
      ∀ z ∈ V, P₀ z * (∏' k : ℕ, (1 + (P k z * g k z - 1))) =
        (P₀ z * ∏ k ∈ Finset.range M, P k z) * U z := by
  have hψ_diff : ∀ j, DifferentiableOn ℂ (fun z ↦ P (j + M) z * g (j + M) z - 1) V := fun j ↦
    (((hP _).differentiableOn.mono hVΩ).fun_mul
      ((hg_diff _).mono hVΩ)).fun_sub (differentiableOn_const 1)
  obtain ⟨hG_diff, hG_ne⟩ := differentiableOn_and_ne_zero_tprod_one_add hV hψ_diff htail
  have hfin_g := differentiableOn_finset_range_prod (fun k ↦ (hg_diff k).mono hVΩ) M
  refine ⟨fun z ↦ (∏ k ∈ Finset.range M, g k z) * ∏' j, (1 + (P (j + M) z * g (j + M) z - 1)),
    hfin_g.fun_mul hG_diff,
    fun z hz ↦ mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hg_ne k z (hVΩ hz))
      (hG_ne z hz),
    fun z hz ↦ ?_⟩
  have hsum_shift : Summable (fun j ↦ P (j + M) z * g (j + M) z - 1) :=
    ((summable_nat_add_iff 1).mpr summable_geometric_two).of_norm_bounded fun j ↦ htail j z hz
  have hmult_shift : Multipliable (fun j ↦ 1 + (P (j + M) z * g (j + M) z - 1)) :=
    Complex.multipliable_one_add_of_summable hsum_shift
  have hsplit := (hmult_shift.prod_mul_tprod_nat_mul' (f := fun k ↦ 1 + (P k z * g k z - 1))).symm
  have hhead : (∏ k ∈ Finset.range M, (1 + (P k z * g k z - 1))) =
      (∏ k ∈ Finset.range M, P k z) * ∏ k ∈ Finset.range M, g k z := by
    simp only [add_sub_cancel, Finset.prod_mul_distrib]
  refine (congrArg (P₀ z * ·) hsplit).trans ?_
  rw [hhead]
  ring

end Helpers

/-- **Prescribed zero multiplicities on open plane sets** (Weierstrass's theorem, Rainer,
Theorem 15.3). For every open subset `Ω ⊆ ℂ` and every locally finitely supported multiplicity
function `m : Function.locallyFinsuppWithin Ω ℕ`, there exists a holomorphic function `f` on `Ω`
whose analytic order at each `z ∈ Ω` is `(m z : ℕ∞)`. -/
theorem IsOpen.exists_differentiableOn_analyticOrderAt_eq {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (m : Function.locallyFinsuppWithin Ω ℕ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ ∀ z ∈ Ω, analyticOrderAt f z = (m z : ℕ∞) := by
  classical
  obtain ⟨K, hKcpt, hKint, hKunion, hfill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hKΩ : ∀ n, K n ⊆ Ω := fun n z hz ↦ hKunion ▸ mem_iUnion.mpr ⟨n, hz⟩
  have hKmono : Monotone K := monotone_nat_of_le_succ fun n ↦ (hKint n).trans interior_subset
  let T : ℕ → Finset ℂ := fun n ↦ (finite_inter_support_of_isCompact m (hKcpt n) (hKΩ n)).toFinset
  have hT_mem : ∀ {n a}, a ∈ T n ↔ a ∈ K n ∧ m a ≠ 0 := by simp [T]
  have hTmono : Monotone T := fun i j hij a ha ↦
    hT_mem.mpr ⟨hKmono hij (hT_mem.mp ha).1, (hT_mem.mp ha).2⟩
  let P₀ : ℂ → ℂ := fun z ↦ ∏ a ∈ T 0, (z - a) ^ m a
  let P : ℕ → ℂ → ℂ := fun k z ↦ ∏ a ∈ T (k + 1) \ T k, (z - a) ^ m a
  have hP_diff : ∀ k, Differentiable ℂ (P k) := fun k ↦
    differentiable_finset_prod_sub_pow (T (k + 1) \ T k) m
  have hP_ne : ∀ k, ∀ z ∈ K k, P k z ≠ 0 := fun k z hz ↦
    Finset.prod_ne_zero_iff.mpr fun a ha ↦ pow_ne_zero _ <| sub_ne_zero.mpr fun hza ↦ by
      rw [Finset.mem_sdiff, hT_mem, hT_mem] at ha
      exact ha.2 ⟨hza ▸ hz, ha.1.2⟩
  choose g hg_diff hg_ne hg_le using fun k : ℕ ↦
    exists_zeroFree_factor_norm_mul_sub_one_le (hfill k) hΩ (hKcpt k) (hKΩ k) (hP_diff k) (hP_ne k)
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (k + 1))
  let f : ℂ → ℂ := fun z ↦ P₀ z * ∏' k : ℕ, (1 + (P k z * g k z - 1))
  have hlocal : ∀ N : ℕ, ∃ U_N : ℂ → ℂ, DifferentiableOn ℂ U_N (interior (K (N + 1))) ∧
      (∀ z ∈ interior (K (N + 1)), U_N z ≠ 0) ∧
      EqOn f (fun z ↦ (∏ a ∈ T (N + 1), (z - a) ^ m a) * U_N z) (interior (K (N + 1))) := by
    intro N
    obtain ⟨U_N, hU_diff, hU_ne, hU_eq⟩ := exists_local_tprod_unit isOpen_interior
      (interior_subset.trans (hKΩ (N + 1))) P₀ hP_diff hg_diff hg_ne (N + 1) fun j z hz ↦
        (hg_le (j + (N + 1)) z (hKmono (Nat.le_add_left (N + 1) j) (interior_subset hz))).trans <|
          pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
    refine ⟨U_N, hU_diff, hU_ne, fun z hz ↦ (hU_eq z hz).trans ?_⟩
    rw [prod_sub_pow_telescopic hTmono m z (N + 1)]
  have han_ord : ∀ z₀ ∈ Ω, AnalyticAt ℂ f z₀ ∧ analyticOrderAt f z₀ = (m z₀ : ℕ∞) := fun z₀ hz₀ ↦ by
    obtain ⟨N, hN⟩ := mem_iUnion.mp (hKunion.symm ▸ hz₀)
    have hzV : z₀ ∈ interior (K (N + 1)) := hKint N hN
    obtain ⟨U_N, hU_diff, hU_ne, heq⟩ := hlocal N
    have hnhds : interior (K (N + 1)) ∈ 𝓝 z₀ := isOpen_interior.mem_nhds hzV
    have hQ_an : AnalyticAt ℂ (fun z : ℂ ↦ ∏ a ∈ T (N + 1), (z - a) ^ m a) z₀ :=
      (differentiable_finset_prod_sub_pow (T (N + 1)) m).analyticAt z₀
    have hU_an : AnalyticAt ℂ U_N z₀ := hU_diff.analyticAt hnhds
    have hfeq := heq.eventuallyEq_of_mem hnhds
    refine ⟨(hQ_an.mul hU_an).congr hfeq.symm, ?_⟩
    rw [analyticOrderAt_congr hfeq]
    change analyticOrderAt ((fun z : ℂ ↦ ∏ a ∈ T (N + 1), (z - a) ^ m a) * U_N) z₀ = _
    rw [analyticOrderAt_mul hQ_an hU_an, hU_an.analyticOrderAt_eq_zero.mpr (hU_ne z₀ hzV),
      add_zero, analyticOrderAt_finset_prod_sub_pow]
    by_cases hm0 : m z₀ = 0
    · simp [hT_mem, hm0]
    · simp [hT_mem.mpr ⟨interior_subset hzV, hm0⟩]
  exact ⟨f, AnalyticOnNhd.differentiableOn fun z hz ↦ (han_ord z hz).1,
    fun z hz ↦ (han_ord z hz).2⟩

/-- **Holomorphic realization of nonnegative divisors** (Rainer, Theorem 15.3). Every nonnegative
locally finitely supported divisor `0 ≤ ν : Function.locallyFinsuppWithin Ω ℤ` on an open set
`Ω ⊆ ℂ` is the divisor of a function `f` holomorphic on `Ω` with `meromorphicOrderAt f z = ν z` at
every `z ∈ Ω`. -/
theorem IsOpen.exists_differentiableOn_divisor_eq_of_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {ν : Function.locallyFinsuppWithin Ω ℤ} (hν : 0 ≤ ν) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ MeromorphicOn.divisor f Ω = ν ∧
      ∀ z ∈ Ω, meromorphicOrderAt f z = ν z := by
  obtain ⟨f, hf, hord⟩ := hΩ.exists_differentiableOn_analyticOrderAt_eq (ν.mapRange Int.toNat rfl)
  have hm_ord : ∀ z ∈ Ω, meromorphicOrderAt f z = ν z := fun z hz ↦ by
    have han : AnalyticAt ℂ f z := hf.analyticAt (hΩ.mem_nhds hz)
    rw [han.meromorphicOrderAt_eq, hord z hz]
    simp [Int.toNat_of_nonneg (hν z)]
  refine ⟨f, hf, Function.locallyFinsuppWithin.ext fun z ↦ ?_, hm_ord⟩
  by_cases hz : z ∈ Ω
  · rw [(hf.analyticOnNhd hΩ).meromorphicOn.divisor_apply hz, hm_ord z hz, WithTop.untop₀_coe]
  · simp [hz]

/-- **Meromorphic divisor realization on open plane sets** (Rainer, Corollary 15.4). Every locally
finitely supported divisor `ν : Function.locallyFinsuppWithin Ω ℤ` on an open set `Ω ⊆ ℂ` is the
divisor of a meromorphic function `f` on `Ω` satisfying `meromorphicOrderAt f z = ν z` for all
`z ∈ Ω`. -/
theorem IsOpen.exists_meromorphicOn_divisor_eq {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (ν : Function.locallyFinsuppWithin Ω ℤ) :
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧ MeromorphicOn.divisor f Ω = ν ∧
      ∀ z ∈ Ω, meromorphicOrderAt f z = ν z := by
  obtain ⟨f₁, hf₁, hdiv₁, hord₁⟩ :=
    hΩ.exists_differentiableOn_divisor_eq_of_nonneg (posPart_nonneg ν)
  obtain ⟨f₂, hf₂, hdiv₂, hord₂⟩ :=
    hΩ.exists_differentiableOn_divisor_eq_of_nonneg (negPart_nonneg ν)
  have hm₁ : MeromorphicOn f₁ Ω := (hf₁.analyticOnNhd hΩ).meromorphicOn
  have hm₂ : MeromorphicOn f₂ Ω := (hf₂.analyticOnNhd hΩ).meromorphicOn
  refine ⟨f₁ / f₂, hm₁.div hm₂, ?_, fun z hz ↦ ?_⟩
  · rw [div_eq_mul_inv, MeromorphicOn.divisor_mul hm₁ hm₂.inv
      (fun z hz ↦ by rw [hord₁ z hz]; exact WithTop.coe_ne_top)
      (fun z hz ↦ by rw [meromorphicOrderAt_inv, hord₂ z hz]; exact WithTop.coe_ne_top),
      MeromorphicOn.divisor_inv, hdiv₁, hdiv₂, ← sub_eq_add_neg, posPart_sub_negPart]
  · rw [meromorphicOrderAt_div (hm₁ z hz) (hm₂ z hz), hord₁ z hz, hord₂ z hz]
    exact congrArg (fun n : ℤ ↦ (n : WithTop ℤ)) (posPart_sub_negPart (ν z))

/-- **Global quotient representation of meromorphic functions** (Rainer, Corollary 15.4). Every
meromorphic function `F` on an open set `Ω ⊆ ℂ` can be written as a quotient `f / g` of functions
holomorphic on `Ω`, where `g` realizes the pole divisor `(MeromorphicOn.divisor F Ω)⁻` (so `g` has
finite analytic order at every point of `Ω`), `(f / g) =ᶠ[𝓝[≠] z] F` at every `z ∈ Ω`, and
`g z ≠ 0 ∧ F z = f z / g z` codiscretely within `Ω`. -/
theorem MeromorphicOn.exists_differentiableOn_eq_div {Ω : Set ℂ} {F : ℂ → ℂ}
    (hF : MeromorphicOn F Ω) (hΩ : IsOpen Ω) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ DifferentiableOn ℂ g Ω ∧
      MeromorphicOn.divisor g Ω = (MeromorphicOn.divisor F Ω)⁻ ∧
      (∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤) ∧
      (∀ z ∈ Ω, (fun w ↦ f w / g w) =ᶠ[𝓝[≠] z] F) ∧
      ∀ᶠ z in codiscreteWithin Ω, g z ≠ 0 ∧ F z = f z / g z := by
  set D := MeromorphicOn.divisor F Ω
  obtain ⟨g, hg_diff, hg_div, hg_ord⟩ :=
    hΩ.exists_differentiableOn_divisor_eq_of_nonneg (negPart_nonneg D)
  have hg_an : AnalyticOnNhd ℂ g Ω := hg_diff.analyticOnNhd hΩ
  have hg_mero : MeromorphicOn g Ω := hg_an.meromorphicOn
  set f : ℂ → ℂ := toMeromorphicNFOn (F * g) Ω
  have hf_nf : MeromorphicNFOn f Ω := meromorphicNFOn_toMeromorphicNFOn (F * g) Ω
  have hf_an : AnalyticOnNhd ℂ f Ω := fun z hz ↦ by
    refine (hf_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_toMeromorphicNFOn (hF.mul hg_mero) hz,
      meromorphicOrderAt_mul (hF z hz) (hg_mero z hz), hg_ord z hz]
    cases hFz : meromorphicOrderAt F z with
    | top => simp
    | coe n =>
      have hDn : D z = n := by simp [D, hF.divisor_apply hz, hFz]
      rw [← WithTop.coe_add, WithTop.coe_nonneg, Function.locallyFinsuppWithin.negPart_apply, hDn]
      exact neg_le_iff_add_nonneg'.mp (negPart_def (a := n) ▸ le_sup_left)
  have hg_ord_ne_top : ∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤ := fun z hz ↦ by
    have h := hg_ord z hz
    rw [(hg_an z hz).meromorphicOrderAt_eq] at h
    intro htop
    simp [htop] at h
  have hgerm : ∀ z ∈ Ω, (fun w ↦ f w / g w) =ᶠ[𝓝[≠] z] F := fun z hz ↦ by
    have hfg := (hF.mul hg_mero).toMeromorphicNFOn_eq_self_on_nhdsNE hz
    have hg_ev_ne : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hg_mero z hz)).mp
        (by rw [hg_ord z hz]; exact WithTop.coe_ne_top)
    filter_upwards [hfg, hg_ev_ne] with w hw hgw
    have hfw : f w = F w * g w := hw
    rw [hfw, mul_div_cancel_right₀ _ hgw]
  have hcod : ∀ᶠ z in codiscreteWithin Ω, g z ≠ 0 ∧ F z = f z / g z := by
    have hU : Ω ∈ codiscreteWithin Ω := Filter.self_mem_codiscreteWithin Ω
    filter_upwards [hU, D⁻.eq_zero_codiscreteWithin,
      toMeromorphicNFOn_eqOn_codiscrete (hF.mul hg_mero)] with z hz hD0 hfg_eq
    have hgz : g z ≠ 0 := by
      refine (hg_an z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp ?_
      rw [hg_ord z hz, hD0]
      rfl
    have hfz : f z = F z * g z := hfg_eq.symm
    exact ⟨hgz, by rw [hfz, mul_div_cancel_right₀ _ hgz]⟩
  exact ⟨f, g, hf_an.differentiableOn, hg_diff, hg_div, hg_ord_ne_top, hgerm, hcod⟩
