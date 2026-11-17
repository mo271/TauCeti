/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Composition of restricted power series

Let `R` and `A` be normed commutative rings with `A` an ultrametric `R`-algebra with bounded scalar
action. Suppose `f = ∑ aₖ Xᵏ ∈ R⟦X⟧` and `g ∈ A⟦X⟧` has zero constant coefficient. Under formal
substitution, each positive-degree coefficient of `f.subst g` is the finite sum
`∑_{1 ≤ k ≤ n} aₖ • [Xⁿ](gᵏ)`.

If `g` has a Gauss norm at a nonnegative radius `r` bounded by `R₀ ≥ 0`, then for every `k ≥ 1`
submultiplicativity of the Gauss norm gives `‖gᵏ‖_r ≤ ‖g‖_rᵏ ≤ R₀ᵏ`, without needing `‖1‖ = 1`
in `A`. Consequently:

* every positive-degree weighted coefficient of `f.subst g` satisfies
  `‖(f.subst g).coeff n‖ rⁿ ≤ ‖f - f(0)‖_{R₀} ≤ ‖f‖_{R₀}`;
* `‖f.subst g‖_r ≤ max ‖algebraMap R A (constantCoeff f)‖ ‖f - f(0)‖_{R₀}`, and when `R = A`,
  `‖f.subst g‖_r ≤ ‖f‖_{R₀}`;
* if `f` is restricted at `R₀` and `g` is restricted at `r`, then `f.subst g` is restricted at `r`;
* when `A` is complete, point evaluation commutes with substitution on the closed disc `‖x‖ ≤ r`
  for any scalar tower `R → S → A` (`A` need not be commutative):
  `(f.subst g).evalAt x = f.evalAt (g.evalAt x)`.

Allowing `f` to have coefficients in a base ring `R` (such as `ℚ_p`) acting on a Banach
`R`-algebra `A` without assuming `‖1‖ = 1` in `A` preserves sharp Gauss bounds when substituting
into universal series like `exp` and `log`.

## Main results

* `PowerSeries.HasGaussNorm.pow` and `PowerSeries.gaussNorm_pow_le`: powers of a series with a
  Gauss norm satisfy `‖gᵏ‖_c ≤ ‖g‖_cᵏ` for `k ≠ 0`, without requiring `‖1‖ = 1`.
* `PowerSeries.norm_coeff_subst_mul_pow_le_sub_const` and
  `PowerSeries.norm_coeff_subst_mul_pow_le`: positive-degree weighted coefficient bounds for
  `f.subst g`.
* `PowerSeries.hasGaussNorm_subst`, `PowerSeries.gaussNorm_subst_le_max`, and
  `PowerSeries.gaussNorm_subst_le`: Gauss norm estimates for `f.subst g`.
* `PowerSeries.IsRestricted.subst`: composition of restricted power series is restricted.
* `PowerSeries.IsRestricted.continuous_evalAtHom`: evaluation at a point of the closed disc is
  continuous for the positive-radius Gauss norm.
* `PowerSeries.IsRestricted.hasSum_subst`: the substitution series `∑ aₖ • gᵏ` converges to
  `f.subst g` in `PowerSeries.IsRestricted.subring r`.
* `PowerSeries.IsRestricted.evalAt_subst`: `(f.subst g).evalAt x = f.evalAt (g.evalAt x)` on the
  closed disc `‖x‖ ≤ r`.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

namespace PowerSeries

open Filter Finset TauCeti.PowerSeries
open scoped Topology

section Pow

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {c : ℝ} {g : R⟦X⟧}

/-- Every power of a series with a Gauss norm at a nonnegative radius has a Gauss norm there. -/
theorem HasGaussNorm.pow (hg : g.HasGaussNorm norm c) (hc : 0 ≤ c) :
    ∀ k : ℕ, (g ^ k).HasGaussNorm norm c
  | 0 => by
    refine ⟨‖(1 : R)‖, Set.forall_mem_range.mpr fun n ↦ ?_⟩
    rcases n with _ | n <;> simp [coeff_one]
  | k + 1 => by
    rw [pow_succ]
    exact hasGaussNorm_mul hc (hg.pow hc k) hg

/-- **Submultiplicativity of the Gauss norm on positive powers.** Over an ultrametric seminormed
ring, `‖gᵏ‖_c ≤ ‖g‖_cᵏ` for every `k ≠ 0` at a nonnegative radius `c`, without requiring `‖1‖ = 1`.
-/
theorem gaussNorm_pow_le (hc : 0 ≤ c) (hg : g.HasGaussNorm norm c) {k : ℕ} (hk : k ≠ 0) :
    (g ^ k).gaussNorm norm c ≤ g.gaussNorm norm c ^ k := by
  induction k with
  | zero => exact absurd rfl hk
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [pow_succ, pow_succ]
      exact (gaussNorm_mul_le hc (hg.pow hc (k + 1)) hg).trans <|
        mul_le_mul_of_nonneg_right (ih k.succ_ne_zero) (gaussNorm_nonneg norm c g norm_nonneg)

end Pow

section Subst

variable {R A : Type*} [SeminormedCommRing R] [SeminormedCommRing A] [Algebra R A]
  [IsBoundedSMul R A] [IsUltrametricDist A] {f : R⟦X⟧} {g : A⟦X⟧} {r R₀ : ℝ}

/-- Subtracting the constant term of a series preserves existence of the Gauss norm. -/
private theorem hasGaussNorm_sub_C_constantCoeff (hf : f.HasGaussNorm norm R₀) :
    (f - C (constantCoeff f)).HasGaussNorm norm R₀ := by
  refine ⟨f.gaussNorm norm R₀, Set.forall_mem_range.mpr fun k ↦ ?_⟩
  rcases k with _ | k
  · simp [gaussNorm_nonneg norm R₀ f norm_nonneg]
  · simpa [coeff_C] using le_gaussNorm norm R₀ f hf (k + 1)

/-- Subtracting the constant term does not increase the Gauss norm. -/
private theorem gaussNorm_sub_C_constantCoeff_le (hf : f.HasGaussNorm norm R₀) :
    (f - C (constantCoeff f)).gaussNorm norm R₀ ≤ f.gaussNorm norm R₀ := by
  rw [gaussNorm_eq]
  refine Real.iSup_le (fun k ↦ ?_) (gaussNorm_nonneg norm R₀ f norm_nonneg)
  rcases k with _ | k
  · simp [gaussNorm_nonneg norm R₀ f norm_nonneg]
  · simpa [coeff_C] using le_gaussNorm norm R₀ f hf (k + 1)

/-- Each positive-index summand `aₖ • [Xⁿ](gᵏ)` in the substitution formula is bounded by
`‖aₖ‖ R₀ᵏ`. -/
private theorem norm_smul_coeff_pow_mul_pow_le (hr : 0 ≤ r) (hg : g.HasGaussNorm norm r)
    (hgr : g.gaussNorm norm r ≤ R₀) {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    ‖coeff k f • coeff n (g ^ k)‖ * r ^ n ≤ ‖coeff k f‖ * R₀ ^ k := by
  calc ‖coeff k f • coeff n (g ^ k)‖ * r ^ n
      ≤ ‖coeff k f‖ * ‖coeff n (g ^ k)‖ * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_smul_le _ _) (pow_nonneg hr n)
    _ = ‖coeff k f‖ * (‖coeff n (g ^ k)‖ * r ^ n) := mul_assoc _ _ _
    _ ≤ ‖coeff k f‖ * (g ^ k).gaussNorm norm r :=
        mul_le_mul_of_nonneg_left (le_gaussNorm norm r (g ^ k) (hg.pow hr k) n) (norm_nonneg _)
    _ ≤ ‖coeff k f‖ * g.gaussNorm norm r ^ k :=
        mul_le_mul_of_nonneg_left (gaussNorm_pow_le hr hg hk) (norm_nonneg _)
    _ ≤ ‖coeff k f‖ * R₀ ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (gaussNorm_nonneg norm r g norm_nonneg) hgr k) (norm_nonneg _)

/-- **Positive-degree coefficient estimate for substitution.** If `g` has zero constant
coefficient and Gauss norm at most `R₀` at a nonnegative radius `r`, then every positive-degree
weighted coefficient of `f.subst g` is bounded by the Gauss norm of `f - f(0)` at `R₀`. -/
theorem norm_coeff_subst_mul_pow_le_sub_const (hg0 : constantCoeff g = 0) (hr : 0 ≤ r)
    (hf : f.HasGaussNorm norm R₀) (hg : g.HasGaussNorm norm r) (hgr : g.gaussNorm norm r ≤ R₀)
    {n : ℕ} (hn : n ≠ 0) :
    ‖coeff n (f.subst g)‖ * r ^ n ≤ (f - C (constantCoeff f)).gaussNorm norm R₀ := by
  have hM : 0 ≤ (f - C (constantCoeff f)).gaussNorm norm R₀ :=
    gaussNorm_nonneg norm R₀ _ norm_nonneg
  rw [coeff_subst_eq_sum_range f hg0 n]
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [zero_pow hn, hM]
  rw [← le_div_iff₀ (pow_pos hrpos n)]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hM (by positivity))
    fun k _ ↦ ?_
  rw [le_div_iff₀ (pow_pos hrpos n)]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [coeff_one, hn, hM]
  · refine (norm_smul_coeff_pow_mul_pow_le hr hg hgr hk n).trans ?_
    simpa [coeff_C, hk] using
      le_gaussNorm norm R₀ (f - C (constantCoeff f)) (hasGaussNorm_sub_C_constantCoeff hf) k

/-- **Positive-degree coefficient estimate for substitution.** Every positive-degree weighted
coefficient of `f.subst g` is bounded by the Gauss norm of `f` at `R₀`. -/
theorem norm_coeff_subst_mul_pow_le (hg0 : constantCoeff g = 0) (hr : 0 ≤ r)
    (hf : f.HasGaussNorm norm R₀) (hg : g.HasGaussNorm norm r) (hgr : g.gaussNorm norm r ≤ R₀)
    {n : ℕ} (hn : n ≠ 0) :
    ‖coeff n (f.subst g)‖ * r ^ n ≤ f.gaussNorm norm R₀ :=
  (norm_coeff_subst_mul_pow_le_sub_const hg0 hr hf hg hgr hn).trans
    (gaussNorm_sub_C_constantCoeff_le hf)

omit [IsBoundedSMul R A] [IsUltrametricDist A] in
/-- The constant coefficient of `f.subst g` is the image of the constant coefficient of `f` when
`g` has zero constant coefficient. -/
private theorem coeff_zero_subst_of_constantCoeff_zero (hg0 : constantCoeff g = 0) :
    coeff 0 (f.subst g : A⟦X⟧) = algebraMap R A (constantCoeff f) := by
  rw [coeff_zero_eq_constantCoeff_apply]
  exact constantCoeff_subst_of_constantCoeff_zero hg0 f

/-- Substitution preserves the existence of a Gauss norm at a nonnegative radius. -/
theorem hasGaussNorm_subst (hg0 : constantCoeff g = 0) (hr : 0 ≤ r)
    (hf : f.HasGaussNorm norm R₀) (hg : g.HasGaussNorm norm r) (hgr : g.gaussNorm norm r ≤ R₀) :
    HasGaussNorm norm r (f.subst g) := by
  refine ⟨max ‖algebraMap R A (constantCoeff f)‖ ((f - C (constantCoeff f)).gaussNorm norm R₀),
    Set.forall_mem_range.mpr fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_zero_subst_of_constantCoeff_zero hg0]
  · exact le_max_of_le_right (norm_coeff_subst_mul_pow_le_sub_const hg0 hr hf hg hgr hn)

/-- **Gauss norm bound for substitution with change of scalars.** The Gauss norm of `f.subst g`
at `r` is bounded by the maximum of `‖algebraMap R A (constantCoeff f)‖` and
`‖f - f(0)‖_{R₀}`. -/
theorem gaussNorm_subst_le_max (hg0 : constantCoeff g = 0) (hr : 0 ≤ r)
    (hf : f.HasGaussNorm norm R₀) (hg : g.HasGaussNorm norm r) (hgr : g.gaussNorm norm r ≤ R₀) :
    gaussNorm norm r (f.subst g) ≤
      max ‖algebraMap R A (constantCoeff f)‖ ((f - C (constantCoeff f)).gaussNorm norm R₀) := by
  rw [gaussNorm_eq]
  refine Real.iSup_le (fun n ↦ ?_) (le_max_of_le_left (norm_nonneg _))
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_zero_subst_of_constantCoeff_zero hg0]
  · exact le_max_of_le_right (norm_coeff_subst_mul_pow_le_sub_const hg0 hr hf hg hgr hn)

/-- **Gauss norm bound for substitution over the same ring.** Over an ultrametric seminormed
commutative ring `A`, `‖f.subst g‖_r ≤ ‖f‖_{R₀}` whenever `g` has zero constant coefficient and
`‖g‖_r ≤ R₀`, without assuming `‖1‖ = 1`. -/
theorem gaussNorm_subst_le {f g : A⟦X⟧} (hg0 : constantCoeff g = 0) (hr : 0 ≤ r)
    (hf : f.HasGaussNorm norm R₀) (hg : g.HasGaussNorm norm r) (hgr : g.gaussNorm norm r ≤ R₀) :
    gaussNorm norm r (f.subst g) ≤ f.gaussNorm norm R₀ := by
  refine (gaussNorm_subst_le_max hg0 hr hf hg hgr).trans (max_le ?_ ?_)
  · simpa using le_gaussNorm norm R₀ f hf 0
  · exact gaussNorm_sub_C_constantCoeff_le hf

end Subst

section IsRestrictedSubst

variable {R A : Type*} [NormedCommRing R] [NormedCommRing A] [Algebra R A]
  [IsBoundedSMul R A] [IsUltrametricDist A] {f : R⟦X⟧} {g : A⟦X⟧} {r R₀ : ℝ}

/-- **Composition of restricted power series is restricted.** If `f ∈ R⟦X⟧` is restricted at
`R₀`, `g ∈ A⟦X⟧` is restricted at `r ≥ 0` with zero constant coefficient and `‖g‖_r ≤ R₀`, then
`f.subst g` is restricted at `r`. -/
theorem IsRestricted.subst (hf : f.IsRestricted R₀) (hg : g.IsRestricted r)
    (hg0 : constantCoeff g = 0) (hr : 0 ≤ r) (hgr : g.gaussNorm norm r ≤ R₀) :
    IsRestricted r (f.subst g) := by
  rcases hr.eq_or_lt with rfl | hrpos
  · refine (isRestricted_iff' 0 _).mpr (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [zero_pow (by omega), mul_zero]
  have hgg : g.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hg
  rw [isRestricted_iff']
  refine tendsto_order.2 ⟨fun x hx ↦ .of_forall fun n ↦ hx.trans_le (by positivity),
    fun ε hε ↦ ?_⟩
  -- Split the substitution sum at `K ≥ 1` past which `‖coeff k f‖ * R₀ ^ k < ε / 2`.
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (((isRestricted_iff' R₀ f).mp hf).eventually (gt_mem_nhds (half_pos hε)))
  set K := max K₀ 1
  have htail : ∀ k ≥ K, ‖coeff k f‖ * R₀ ^ k < ε / 2 :=
    fun k hk ↦ hK₀ k ((le_max_left _ _).trans hk)
  -- Each of the finitely many terms `k < K` tends to zero in `n` because `g ^ k` is restricted.
  have hlow : ∀ᶠ n in atTop, ∀ k ∈ Finset.range K,
      ‖coeff k f • coeff n (g ^ k)‖ * r ^ n < ε / 2 := by
    refine (Finset.eventually_all _).mpr fun k _ ↦ ?_
    have hgk : (g ^ k).IsRestricted r := pow_mem (S := IsRestricted.subring r) hg k
    have htend : Tendsto (fun n ↦ ‖coeff k f‖ * (‖coeff n (g ^ k)‖ * r ^ n)) atTop (𝓝 0) := by
      simpa using ((isRestricted_iff' r (g ^ k)).mp hgk).const_mul ‖coeff k f‖
    filter_upwards [htend.eventually (gt_mem_nhds (half_pos hε))] with n hn
    calc ‖coeff k f • coeff n (g ^ k)‖ * r ^ n
        ≤ ‖coeff k f‖ * ‖coeff n (g ^ k)‖ * r ^ n :=
          mul_le_mul_of_nonneg_right (norm_smul_le _ _) (pow_nonneg hrpos.le n)
      _ = ‖coeff k f‖ * (‖coeff n (g ^ k)‖ * r ^ n) := mul_assoc _ _ _
      _ < ε / 2 := hn
  filter_upwards [hlow] with n hn
  rw [coeff_subst_eq_sum_range f hg0 n]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [← le_div_iff₀ (pow_pos hrpos n)]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ ↦ ?_
  rw [le_div_iff₀ (pow_pos hrpos n)]
  by_cases hk : k < K
  · exact (hn k (Finset.mem_range.mpr hk)).le
  · have hk1 : k ≠ 0 := by omega
    exact (norm_smul_coeff_pow_mul_pow_le hrpos.le hgg hgr hk1 n).trans (htail k (by omega)).le

end IsRestrictedSubst

section EvalAt

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A]

/-- **Evaluation of restricted series is continuous** for the positive-radius Gauss norm. -/
theorem IsRestricted.continuous_evalAtHom {c : ℝ} [Fact (0 < c)] {b : A} (hb : ‖b‖ ≤ c) :
    Continuous (IsRestricted.evalAtHom (A := A) R hb) := by
  refine (LipschitzWith.of_dist_le_mul (K := ‖(1 : A)‖₊) fun f g ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, IsRestricted.evalAtHom_apply, coe_nnNorm,
    TauCeti.PowerSeries.norm_eq_gaussNorm]
  refine norm_evalAt_le_mul_gaussNorm_of_norm_algebraMap_le
    (hasGaussNorm_of_isRestricted (f - g).2) (fun a ↦ ?_) hb
  rw [Algebra.algebraMap_eq_smul_one, mul_comm]
  exact norm_smul_le a (1 : A)

end EvalAt

section EvalAtSubst

/-- **Convergent substitution series in the restricted-series ring.** For `r > 0`, if `f ∈ R⟦X⟧`
is restricted at `R₀` and `g ∈ S⟦X⟧` is restricted at `r` with zero constant coefficient and
`‖g‖_r ≤ R₀`, then `∑ k, coeff k f • g ^ k` converges to `f.subst g` in
`PowerSeries.IsRestricted.subring r`. -/
theorem IsRestricted.hasSum_subst {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    [Algebra R S] [IsBoundedSMul R S] [IsUltrametricDist S] [CompleteSpace S]
    {f : R⟦X⟧} {g : S⟦X⟧} {r R₀ : ℝ} [Fact (0 < r)]
    (hf : f.IsRestricted R₀) (hg : g.IsRestricted r)
    (hg0 : constantCoeff g = 0) (hgr : g.gaussNorm norm r ≤ R₀) :
    HasSum (fun k ↦ coeff k f • (⟨g, hg⟩ : IsRestricted.subring (R := S) r) ^ k)
      ⟨f.subst g, IsRestricted.subst hf hg hg0 (Fact.out : 0 < r).le hgr⟩ := by
  have hrpos : 0 < r := Fact.out
  let T := IsRestricted.subring (R := S) r
  let gT : T := ⟨g, hg⟩
  let u : ℕ → T := fun k ↦ coeff k f • gT ^ k
  have hgg : g.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hg
  have hcoe (k : ℕ) : (u k : S⟦X⟧) = coeff k f • g ^ k := by
    dsimp only [u, gT]
    rw [coe_smul_isRestrictedSubring, Subring.coe_pow]
  have hu_tend : Tendsto u cofinite (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((isRestricted_iff R₀ f).mp hf)
    filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with k hk
    have hk0 : k ≠ 0 := Set.mem_compl_singleton_iff.mp hk
    refine TauCeti.PowerSeries.norm_le_iff.mpr fun n ↦ ?_
    rw [hcoe k, coeff_smul]
    exact norm_smul_coeff_pow_mul_pow_le hrpos.le hgg hgr hk0 n
  obtain ⟨s, hs⟩ := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hu_tend
  convert hs
  refine Subtype.ext <| PowerSeries.ext fun n ↦ ?_
  have hcoeff := hs.map ((coeff n).toAddMonoidHom.comp T.subtype.toAddMonoidHom)
    (uniformContinuous_coeff (R := S) (c := r) n).continuous
  have hfin : HasSum (fun k ↦ coeff n (u k : S⟦X⟧)) (coeff n (f.subst g)) := by
    rw [coeff_subst_eq_sum_range f hg0 n]
    refine hasSum_sum_of_ne_finset_zero fun k hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [hcoe k, coeff_smul, coeff_of_lt_order _ ((Nat.cast_lt.mpr (by omega : n < k)).trans_le
      (le_order_pow_of_constantCoeff_eq_zero k hg0)), smul_zero]
  exact hfin.unique (by simpa [Function.comp_def] using hcoeff)

/-- **Evaluation commutes with substitution of restricted power series.** In a scalar tower
`R → S → A` of ultrametric normed algebras with `S` and `A` complete (`A` need not be commutative),
if `f ∈ R⟦X⟧` is restricted at `R₀` and `g ∈ S⟦X⟧` is restricted at `r ≥ 0` with zero constant
coefficient and `‖g‖_r ≤ R₀`, then for every `x ∈ A` with `‖x‖ ≤ r`,
`(f.subst g).evalAt x = f.evalAt (g.evalAt x)`. -/
theorem IsRestricted.evalAt_subst {R S A : Type*} [NormedCommRing R] [NormedCommRing S]
    [IsUltrametricDist S] [CompleteSpace S] [NormedRing A] [IsUltrametricDist A] [CompleteSpace A]
    [Algebra R S] [IsBoundedSMul R S] [Algebra S A] [IsBoundedSMul S A] [Algebra R A]
    [IsScalarTower R S A] {f : R⟦X⟧} {g : S⟦X⟧} {r R₀ : ℝ}
    (hf : f.IsRestricted R₀) (hg : g.IsRestricted r)
    (hg0 : constantCoeff g = 0) (hr : 0 ≤ r) (hgr : g.gaussNorm norm r ≤ R₀)
    {x : A} (hx : ‖x‖ ≤ r) :
    evalAt (f.subst g) x = f.evalAt (g.evalAt x) := by
  rcases hr.eq_or_lt with rfl | hrpos
  · obtain rfl : x = 0 := norm_le_zero_iff.mp hx
    rw [evalAt_at_zero, evalAt_at_zero, hg0, map_zero, evalAt_at_zero,
      ← coeff_zero_eq_constantCoeff_apply, coeff_zero_subst_of_constantCoeff_zero hg0,
      ← IsScalarTower.algebraMap_apply R S A]
  have : Fact (0 < r) := ⟨hrpos⟩
  let T := IsRestricted.subring (R := S) r
  let gT : T := ⟨g, hg⟩
  have hsumT := IsRestricted.hasSum_subst hf hg hg0 hgr
  let ev := IsRestricted.evalAtHom (A := A) S hx
  have hev := hsumT.map ev.toAddMonoidHom (IsRestricted.continuous_evalAtHom hx)
  have hev_u (k : ℕ) : ev (coeff k f • gT ^ k) = coeff k f • g.evalAt x ^ k := by
    have hu_eq : coeff k f • gT ^ k = algebraMap R T (coeff k f) * gT ^ k := Algebra.smul_def _ _
    rw [hu_eq, map_mul, map_pow, IsRestricted.evalAtHom_apply, coe_algebraMap_isRestrictedSubring,
      evalAt_C, ← IsScalarTower.algebraMap_apply R S A, Algebra.smul_def,
      IsRestricted.evalAtHom_apply]
  have hev' : HasSum (fun k ↦ coeff k f • g.evalAt x ^ k) (evalAt (f.subst g) x) := by
    convert hev using 1
    · ext k
      exact (hev_u k).symm
    · rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
        IsRestricted.evalAtHom_apply (R := S) hx, evalAt_def]
  rw [evalAt_def f, hev'.tsum_eq]

end EvalAtSubst

end PowerSeries
