/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# Comultiplication on analytic stages

Addition on `ℤ_p` induces a comultiplication on each analytic stage
`LA_h(E) = C₀(ZMod (pʰ) × ℕ, E)`. For points `x = a.val + pʰ u` and `y = b.val + pʰ v` in the discs
of `a, b ∈ ZMod (pʰ)`, Euclidean division of `a.val + b.val` by `pʰ` gives

`x + y = (a + b).val + pʰ (q + u + v)`  with  `q = ⌊(a.val + b.val) / pʰ⌋`.

Re-expanding `∑ₙ (q + u + v)ⁿ • c(a + b, n)` in powers `uⁱ vʲ` produces the two-variable
coefficient family whose `(a, i), (b, j)` entry is

`∑' k, ((i + j + k).choose (i + j) * (i + j).choose i * q ^ k) • c(a + b, i + j + k)`.

When `pʰ ≠ 0`, `ZMod (pʰ)` is finite, so these coefficients vanish jointly as `(i, j) → ∞` in any
complete ultrametric normed group `E`. Currying via `ZeroAtInftyContinuousMap.curryEquiv` gives the
continuous linear map `TauCeti.AnalyticStage.comul S : LA_h(E) →L[S] LA_h(LA_h(E))`.

Because the re-expansion coefficients are natural numbers, `comul` is defined and coassociative
without assuming `p` is prime or that `E` is a `ℤ_p`-module, and it preserves the stage norm
isometrically since evaluating at `(0, 0)` in either variable recovers the original vector. Over a
complete ultrametric `ℤ_p`-module `E` with contractive `ℤ_p`-action, repeated stage evaluation of
`comul S c` at `x` and `y` recovers `(eval S c)(x + y)`. Compatibility with stage re-expansion
`transition` holds first over `ℤ_p` by injectivity of evaluation, and then for every coefficient
module `E`—including torsion ones—by linearity and continuity from single-entry vectors.

## Main definitions

* `TauCeti.AnalyticStage.comul S`: the stage comultiplication `LA_h(E) →L[S] LA_h(LA_h(E))`.

## Main results

* `TauCeti.AnalyticStage.comul_apply_apply`: explicit series formula for `comul S c x y`.
* `TauCeti.AnalyticStage.comul_apply_zero_left`, `TauCeti.AnalyticStage.comul_apply_zero_right`:
  counit identities at `(0, 0)`.
* `TauCeti.AnalyticStage.comul_comm`: symmetry `comul S c x y = comul S c y x`.
* `TauCeti.AnalyticStage.norm_comul`: `comul S` is an isometry.
* `TauCeti.AnalyticStage.comul_assoc`: coassociativity of `comul S`.
* `TauCeti.AnalyticStage.eval_eval_comul`: `eval S (eval S (comul S c) x) y = eval S c (x + y)`.
* `TauCeti.AnalyticStage.comul_transition`, `TauCeti.AnalyticStage.comul_transitionLE`:
  comultiplication commutes with stage re-expansion.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

namespace TauCeti.AnalyticStage

/-! ### Stage comultiplication -/

section Comul

variable {p h : ℕ} {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]

/-- The natural-number scalar in the `k`-th summand of `comul` at `(x, y)`: the coefficient of
`u ^ x.2 * v ^ y.2 * q ^ k` in `(q + u + v) ^ (x.2 + y.2 + k)` evaluated at the carry
`q = ⌊(x.1.val + y.1.val) / pʰ⌋`. -/
private def comulScalar (h : ℕ) (x y : ZMod (p ^ h) × ℕ) (k : ℕ) : ℕ :=
  (x.2 + y.2 + k).choose (x.2 + y.2) * (x.2 + y.2).choose x.2 *
    ((x.1.val + y.1.val) / p ^ h) ^ k

private theorem comulScalar_comm (x y : ZMod (p ^ h) × ℕ) (k : ℕ) :
    comulScalar h x y k = comulScalar h y x k := by
  simp only [comulScalar, add_comm x.2 y.2, add_comm x.1.val y.1.val]
  rw [← Nat.choose_symm_add]

private theorem summable_comulScalar_nsmul [CompleteSpace E] (c : AnalyticStage p h E)
    (x y : ZMod (p ^ h) × ℕ) :
    Summable fun k : ℕ ↦ comulScalar h x y k • c (x.1 + y.1, x.2 + y.2 + k) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun k ↦ IsUltrametricDist.norm_nsmul_le _ _) ?_
  have hinj : Function.Injective fun k : ℕ ↦ (x.1 + y.1, x.2 + y.2 + k) :=
    fun _ _ hk ↦ Nat.add_left_cancel (Prod.ext_iff.mp hk).2
  exact tendsto_zero_iff_norm_tendsto_zero.mp <|
    c.tendsto_cofinite.comp (Nat.cofinite_eq_atTop ▸ hinj.tendsto_cofinite)

/-- The uncurried two-variable coefficient family of `comul` before currying. -/
private noncomputable def comulCoeff (c : AnalyticStage p h E)
    (xy : (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) : E :=
  ∑' k : ℕ, comulScalar h xy.1 xy.2 k • c (xy.1.1 + xy.2.1, xy.1.2 + xy.2.2 + k)

private theorem norm_comulCoeff_le (c : AnalyticStage p h E)
    (xy : (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) :
    ‖comulCoeff c xy‖ ≤ ‖c‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg c) fun _ ↦
    (IsUltrametricDist.norm_nsmul_le _ _).trans (c.norm_coe_le_norm _)

variable [NeZero (p ^ h)]

private theorem tendsto_comulCoeff (c : AnalyticStage p h E) :
    Tendsto (comulCoeff c) cofinite (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ eventually_cofinite.mpr ?_
  have hc : {i : ZMod (p ^ h) × ℕ | ¬ ‖c i‖ < ε / 2}.Finite :=
    eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp c.tendsto_cofinite _ (half_pos hε))
  obtain ⟨N, hN⟩ := (hc.image Prod.snd).bddAbove
  have hsmall (d : ZMod (p ^ h)) (n : ℕ) (hn : N + 1 ≤ n) : ‖c (d, n)‖ ≤ ε / 2 := by
    by_contra! hlt
    have hmem : n ∈ Prod.snd '' {i : ZMod (p ^ h) × ℕ | ¬ ‖c i‖ < ε / 2} :=
      ⟨(d, n), not_lt.mpr hlt.le, rfl⟩
    exact absurd (hN hmem) (by omega)
  have hbox : ((Set.univ ×ˢ Set.Iio (N + 1)) ×ˢ
      (Set.univ ×ˢ Set.Iio (N + 1)) : Set ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ))).Finite :=
    (Set.finite_univ.prod (Set.finite_Iio _)).prod (Set.finite_univ.prod (Set.finite_Iio _))
  refine hbox.subset fun xy hxy ↦ ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hxy
  by_contra hmem
  have hij : N + 1 ≤ xy.1.2 + xy.2.2 := by
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Iio, true_and, not_and_or, not_lt] at hmem
    rcases hmem with h1 | h2 <;> omega
  have hle : ‖comulCoeff c xy‖ ≤ ε / 2 :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le fun _ ↦
      (IsUltrametricDist.norm_nsmul_le _ _).trans (hsmall _ _ (by omega))
  exact absurd (hle.trans_lt (half_lt_self hε)) (not_lt.mpr hxy)

variable [CompleteSpace E]
variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]

/-- **Comultiplication on the analytic stage `LA_h(E)`.** Re-expanding `c(x + y)` in the local
coordinates `(u, v)` on each pair of discs `(a + pʰℤ_p) × (b + pʰℤ_p)` defines a continuous
`S`-linear map `LA_h(E) →L[S] LA_h(LA_h(E))`. -/
noncomputable def comul : AnalyticStage p h E →L[S] AnalyticStage p h (AnalyticStage p h E) :=
  let L : AnalyticStage p h E →ₗ[S] AnalyticStage p h (AnalyticStage p h E) :=
    { toFun c := curryEquiv S E (mkOfDiscrete (comulCoeff c) (tendsto_comulCoeff c))
      map_add' c d := by
        ext x y
        simp only [curryEquiv_apply_apply, coe_mkOfDiscrete, comulCoeff, FunLike.coe_add,
          Pi.add_apply, smul_add]
        exact (summable_comulScalar_nsmul c x y).tsum_add
          (summable_comulScalar_nsmul d x y)
      map_smul' s c := by
        ext x y
        simp only [curryEquiv_apply_apply, coe_mkOfDiscrete, comulCoeff, FunLike.coe_smul,
          Pi.smul_apply, RingHom.id_apply, smul_comm _ s]
        exact (summable_comulScalar_nsmul c x y).tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      refine (norm_le (norm_nonneg c)).mpr fun xy ↦ ?_
      rw [coe_mkOfDiscrete]
      exact norm_comulCoeff_le c xy }

private theorem hasSum_comul_apply_apply (c : AnalyticStage p h E) (x y : ZMod (p ^ h) × ℕ) :
    HasSum (fun k : ℕ ↦ comulScalar h x y k • c (x.1 + y.1, x.2 + y.2 + k))
      (comul S c x y) := by
  simpa only [comul, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    curryEquiv_apply_apply, coe_mkOfDiscrete, comulCoeff] using
    (summable_comulScalar_nsmul c x y).hasSum

/-- Explicit series formula for the `(x, y)` coefficient of `comul S c`. -/
theorem comul_apply_apply (c : AnalyticStage p h E) (x y : ZMod (p ^ h) × ℕ) :
    comul S c x y =
      ∑' k : ℕ, ((x.2 + y.2 + k).choose (x.2 + y.2) * (x.2 + y.2).choose x.2 *
        ((x.1.val + y.1.val) / p ^ h) ^ k) • c (x.1 + y.1, x.2 + y.2 + k) :=
  (hasSum_comul_apply_apply S c x y).tsum_eq.symm

/-- Comultiplication is independent of the scalar semiring `S`. -/
theorem comul_eq_comul (T : Type*) [Semiring T] [Module T E] [ContinuousConstSMul T E]
    (c : AnalyticStage p h E) : comul S c = comul T c := by
  ext x y
  rw [comul_apply_apply, comul_apply_apply]

/-- Stage comultiplication is symmetric in its two stage indices. -/
theorem comul_comm (c : AnalyticStage p h E) (x y : ZMod (p ^ h) × ℕ) :
    comul S c x y = comul S c y x := by
  simp only [comul_apply_apply]
  refine tsum_congr fun k ↦ ?_
  have hsc := comulScalar_comm x y k
  simp only [comulScalar] at hsc
  rw [hsc, add_comm x.1 y.1, add_comm x.2 y.2]

/-- Evaluating the first variable of `comul S c` at `(0, 0)` recovers `c`. -/
@[simp]
theorem comul_apply_zero_left (c : AnalyticStage p h E) : comul S c (0, 0) = c := by
  ext ⟨b, j⟩
  rw [comul_apply_apply, ZMod.val_zero, zero_add, zero_add, zero_add,
    Nat.div_eq_of_lt (ZMod.val_lt b), tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/-- Evaluating the second variable of `comul S c` at `(0, 0)` recovers `c`. -/
@[simp]
theorem comul_apply_zero_right (c : AnalyticStage p h E) (x : ZMod (p ^ h) × ℕ) :
    comul S c x (0, 0) = c x := by
  rw [comul_comm, comul_apply_zero_left]

/-- Stage comultiplication preserves the Gauss norm isometrically. -/
@[simp]
theorem norm_comul (c : AnalyticStage p h E) : ‖comul S c‖ = ‖c‖ := by
  refine le_antisymm ?_ ?_
  · refine (norm_le (norm_nonneg c)).mpr fun x ↦ (norm_le (norm_nonneg c)).mpr fun y ↦ ?_
    simpa only [comul_apply_apply, comulCoeff, comulScalar] using norm_comulCoeff_le c (x, y)
  · simpa only [comul_apply_zero_left] using (comul S c).norm_coe_le_norm (0, 0)

/-- Stage comultiplication is unconditionally injective. -/
theorem comul_injective : Function.Injective (comul (p := p) (h := h) (E := E) S) :=
  fun c d hcd ↦ by simpa only [comul_apply_zero_left] using congrArg (· (0, 0)) hcd

/-- Stage comultiplication has operator norm at most `1`. -/
theorem opNorm_comul_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖comul (p := p) (h := h) (E := E) 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by simp

/-- Stage comultiplication commutes with bounded continuous linear maps on the coefficients. -/
theorem comul_compLeft {F R T : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
    [CompleteSpace F] [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F]
    [ContinuousConstSMul R F] [Semiring T] [Module T F] [ContinuousConstSMul T F]
    (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (c : AnalyticStage p h E) :
    comul T (compLeft u hu c) =
      compLeft (compLeft u hu) (exists_norm_compLeft_apply_le u hu) (comul S c) := by
  ext x y
  simp only [compLeft_apply]
  refine (hasSum_comul_apply_apply T (compLeft u hu c) x y).unique ?_
  simpa only [map_nsmul, compLeft_apply] using (hasSum_comul_apply_apply S c x y).mapL u

/-! ### Coassociativity -/

/-- The natural-number entry of `comul S (single (d, n) e)` at `(x, y)`. When `n < x.2 + y.2` the
factor `n.choose (x.2 + y.2)` vanishes, matching the empty sum. -/
private def comulSingleNat (h : ℕ) (d : ZMod (p ^ h)) (n : ℕ) (x y : ZMod (p ^ h) × ℕ) : ℕ :=
  if x.1 + y.1 = d then
    n.choose (x.2 + y.2) * (x.2 + y.2).choose x.2 *
      ((x.1.val + y.1.val) / p ^ h) ^ (n - (x.2 + y.2))
  else 0

private theorem comul_single_apply_apply (d : ZMod (p ^ h)) (n : ℕ) (e : E)
    (x y : ZMod (p ^ h) × ℕ) :
    comul S (single (d, n) e) x y = comulSingleNat h d n x y • e := by
  rw [comul_apply_apply]
  by_cases hxy : x.1 + y.1 = d
  · by_cases hle : x.2 + y.2 ≤ n
    · rw [tsum_eq_single (n - (x.2 + y.2))]
      · have hadd : x.2 + y.2 + (n - (x.2 + y.2)) = n := Nat.add_sub_of_le hle
        simp [comulSingleNat, hxy, hadd]
      · intro k hk
        have hne : x.2 + y.2 + k ≠ n := by omega
        simp [single_apply, hne]
    · rw [not_le] at hle
      rw [tsum_eq_sum (s := ∅) fun k _ ↦ by
        have hne : x.2 + y.2 + k ≠ n := by omega
        simp [single_apply, hne]]
      simp [comulSingleNat, hxy, Nat.choose_eq_zero_of_lt hle]
  · rw [tsum_eq_sum (s := ∅) fun k _ ↦ by simp [single_apply, hxy]]
    simp [comulSingleNat, hxy]

/-- Associativity of the Euclidean-division carries for three residues modulo `m > 0`. -/
private theorem carry_add_assoc {m : ℕ} [NeZero m] (a₁ a₂ a₃ : ZMod m) :
    (a₂.val + a₃.val) / m + (a₁.val + (a₂ + a₃).val) / m =
      (a₁.val + a₂.val) / m + ((a₁ + a₂).val + a₃.val) / m := by
  have hmod (a b : ZMod m) : a.val + b.val = (a + b).val + m * ((a.val + b.val) / m) := by
    rw [ZMod.val_add, Nat.mod_add_div]
  have h12 := hmod a₁ a₂
  have h12_3 := hmod (a₁ + a₂) a₃
  have h23 := hmod a₂ a₃
  have h1_23 := hmod a₁ (a₂ + a₃)
  rw [← add_assoc a₁ a₂ a₃] at h1_23
  have heq : (a₁ + a₂ + a₃).val + m * ((a₂.val + a₃.val) / m + (a₁.val + (a₂ + a₃).val) / m) =
      (a₁ + a₂ + a₃).val + m * ((a₁.val + a₂.val) / m + ((a₁ + a₂).val + a₃.val) / m) := by
    linarith
  exact Nat.mul_left_cancel (NeZero.pos m) (Nat.add_left_cancel heq)

omit [NeZero (p ^ h)] in
private theorem sum_comulScalar_mul_comulSingleNat_right (d : ZMod (p ^ h)) (n : ℕ)
    (x y z : ZMod (p ^ h) × ℕ) (hd : x.1 + (y.1 + z.1) = d) (hle : x.2 + y.2 + z.2 ≤ n) :
    ∑ k ∈ Finset.range (n - (x.2 + y.2 + z.2) + 1),
      comulScalar h y z k * comulSingleNat h d n x (y.1 + z.1, y.2 + z.2 + k) =
        n.choose (x.2 + y.2 + z.2) * (x.2 + y.2 + z.2).choose x.2 * (y.2 + z.2).choose y.2 *
          ((y.1.val + z.1.val) / p ^ h + (x.1.val + (y.1 + z.1).val) / p ^ h) ^
            (n - (x.2 + y.2 + z.2)) := by
  set M := n - (x.2 + y.2 + z.2)
  set q₂₃ := (y.1.val + z.1.val) / p ^ h
  set q₁_₂₃ := (x.1.val + (y.1 + z.1).val) / p ^ h
  have hpow : (q₂₃ + q₁_₂₃) ^ M =
      ∑ k ∈ Finset.range (M + 1), M.choose k * q₂₃ ^ k * q₁_₂₃ ^ (M - k) := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Nat.cast_id]
    ring
  rw [hpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [comulScalar, comulSingleNat, hd, ite_true]
  have hsub : n - (x.2 + (y.2 + z.2 + k)) = M - k := by omega
  have hc1 : n.choose (x.2 + (y.2 + z.2 + k)) * (x.2 + (y.2 + z.2 + k)).choose x.2 =
      n.choose x.2 * (n - x.2).choose (y.2 + z.2 + k) := by
    rw [Nat.choose_mul (Nat.le_add_right x.2 _), Nat.add_sub_cancel_left]
  have hc2 : (n - x.2).choose (y.2 + z.2 + k) * (y.2 + z.2 + k).choose (y.2 + z.2) =
      (n - x.2).choose (y.2 + z.2) * M.choose k := by
    have hM : n - x.2 - (y.2 + z.2) = M := by omega
    rw [Nat.choose_mul (Nat.le_add_right (y.2 + z.2) k), Nat.add_sub_cancel_left, hM]
  have hc3 : n.choose (x.2 + y.2 + z.2) * (x.2 + y.2 + z.2).choose x.2 =
      n.choose x.2 * (n - x.2).choose (y.2 + z.2) := by
    rw [Nat.add_assoc x.2 y.2 z.2,
      Nat.choose_mul (Nat.le_add_right x.2 (y.2 + z.2)), Nat.add_sub_cancel_left]
  rw [hsub]
  calc ((y.2 + z.2 + k).choose (y.2 + z.2) * (y.2 + z.2).choose y.2 * q₂₃ ^ k) *
        (n.choose (x.2 + (y.2 + z.2 + k)) * (x.2 + (y.2 + z.2 + k)).choose x.2 *
          q₁_₂₃ ^ (M - k))
      = (n.choose (x.2 + (y.2 + z.2 + k)) * (x.2 + (y.2 + z.2 + k)).choose x.2) *
          (y.2 + z.2 + k).choose (y.2 + z.2) * (y.2 + z.2).choose y.2 *
          (q₂₃ ^ k * q₁_₂₃ ^ (M - k)) := by ring
    _ = n.choose x.2 * ((n - x.2).choose (y.2 + z.2 + k) *
          (y.2 + z.2 + k).choose (y.2 + z.2)) * (y.2 + z.2).choose y.2 *
          (q₂₃ ^ k * q₁_₂₃ ^ (M - k)) := by rw [hc1]; ring
    _ = (n.choose x.2 * (n - x.2).choose (y.2 + z.2)) * (y.2 + z.2).choose y.2 *
          (M.choose k * q₂₃ ^ k * q₁_₂₃ ^ (M - k)) := by rw [hc2]; ring
    _ = n.choose (x.2 + y.2 + z.2) * (x.2 + y.2 + z.2).choose x.2 * (y.2 + z.2).choose y.2 *
          (M.choose k * q₂₃ ^ k * q₁_₂₃ ^ (M - k)) := by rw [hc3]

omit [NeZero (p ^ h)] in
private theorem sum_comulScalar_mul_comulSingleNat_left (d : ZMod (p ^ h)) (n : ℕ)
    (x y z : ZMod (p ^ h) × ℕ) (hd : (x.1 + y.1) + z.1 = d) (hle : x.2 + y.2 + z.2 ≤ n) :
    ∑ k ∈ Finset.range (n - (x.2 + y.2 + z.2) + 1),
      comulScalar h x y k * comulSingleNat h d n (x.1 + y.1, x.2 + y.2 + k) z =
        n.choose (x.2 + y.2 + z.2) * (x.2 + y.2 + z.2).choose x.2 * (y.2 + z.2).choose y.2 *
          ((x.1.val + y.1.val) / p ^ h + ((x.1 + y.1).val + z.1.val) / p ^ h) ^
            (n - (x.2 + y.2 + z.2)) := by
  set M := n - (x.2 + y.2 + z.2)
  set q₁₂ := (x.1.val + y.1.val) / p ^ h
  set q₁₂_₃ := ((x.1 + y.1).val + z.1.val) / p ^ h
  have hpow : (q₁₂ + q₁₂_₃) ^ M =
      ∑ k ∈ Finset.range (M + 1), M.choose k * q₁₂ ^ k * q₁₂_₃ ^ (M - k) := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Nat.cast_id]
    ring
  rw [hpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [comulScalar, comulSingleNat, hd, ite_true]
  have hsub : n - (x.2 + y.2 + k + z.2) = M - k := by omega
  have hc1 : n.choose (x.2 + y.2 + k + z.2) * (x.2 + y.2 + k + z.2).choose (x.2 + y.2 + k) =
      n.choose z.2 * (n - z.2).choose (x.2 + y.2 + k) := by
    rw [Nat.choose_symm_add, Nat.choose_mul (Nat.le_add_left z.2 _), Nat.add_sub_cancel_right]
  have hc2 : (n - z.2).choose (x.2 + y.2 + k) * (x.2 + y.2 + k).choose (x.2 + y.2) =
      (n - z.2).choose (x.2 + y.2) * M.choose k := by
    have hM : n - z.2 - (x.2 + y.2) = M := by omega
    rw [Nat.choose_mul (Nat.le_add_right (x.2 + y.2) k), Nat.add_sub_cancel_left, hM]
  have hc3 : n.choose z.2 * (n - z.2).choose (x.2 + y.2) * (x.2 + y.2).choose x.2 =
      n.choose (x.2 + y.2 + z.2) * (x.2 + y.2 + z.2).choose x.2 * (y.2 + z.2).choose y.2 := by
    have ha : n.choose (x.2 + y.2 + z.2) * (x.2 + y.2 + z.2).choose (x.2 + y.2) =
        n.choose z.2 * (n - z.2).choose (x.2 + y.2) := by
      rw [Nat.choose_symm_add, Nat.choose_mul (Nat.le_add_left z.2 _), Nat.add_sub_cancel_right]
    have hb : (x.2 + y.2 + z.2).choose (x.2 + y.2) * (x.2 + y.2).choose x.2 =
        (x.2 + y.2 + z.2).choose x.2 * (y.2 + z.2).choose y.2 := by
      have hsub' : x.2 + y.2 + z.2 - x.2 = y.2 + z.2 := by omega
      rw [Nat.choose_mul (Nat.le_add_right x.2 y.2), hsub', Nat.add_sub_cancel_left]
    rw [← ha, mul_assoc, hb, ← mul_assoc]
  rw [hsub]
  calc ((x.2 + y.2 + k).choose (x.2 + y.2) * (x.2 + y.2).choose x.2 * q₁₂ ^ k) *
        (n.choose (x.2 + y.2 + k + z.2) * (x.2 + y.2 + k + z.2).choose (x.2 + y.2 + k) *
          q₁₂_₃ ^ (M - k))
      = (n.choose (x.2 + y.2 + k + z.2) * (x.2 + y.2 + k + z.2).choose (x.2 + y.2 + k)) *
          (x.2 + y.2 + k).choose (x.2 + y.2) * (x.2 + y.2).choose x.2 *
          (q₁₂ ^ k * q₁₂_₃ ^ (M - k)) := by ring
    _ = n.choose z.2 * ((n - z.2).choose (x.2 + y.2 + k) *
          (x.2 + y.2 + k).choose (x.2 + y.2)) * (x.2 + y.2).choose x.2 *
          (q₁₂ ^ k * q₁₂_₃ ^ (M - k)) := by rw [hc1]; ring
    _ = (n.choose z.2 * (n - z.2).choose (x.2 + y.2) * (x.2 + y.2).choose x.2) *
          (M.choose k * q₁₂ ^ k * q₁₂_₃ ^ (M - k)) := by rw [hc2]; ring
    _ = n.choose (x.2 + y.2 + z.2) * (x.2 + y.2 + z.2).choose x.2 * (y.2 + z.2).choose y.2 *
          (M.choose k * q₁₂ ^ k * q₁₂_₃ ^ (M - k)) := by rw [hc3]

private theorem comul_comul_single_apply (i : ZMod (p ^ h) × ℕ) (e : E)
    (x y z : ZMod (p ^ h) × ℕ) :
    comul S (comul S (single i e) x) y z = comul S (comul S (single i e)) x y z := by
  obtain ⟨d, n⟩ := i
  have hlhs : comul S (comul S (single (d, n) e) x) y z =
      ∑' k : ℕ, (comulScalar h y z k *
        comulSingleNat h d n x (y.1 + z.1, y.2 + z.2 + k)) • e := by
    rw [← (hasSum_comul_apply_apply S _ _ _).tsum_eq]
    refine tsum_congr fun k ↦ ?_
    rw [comul_single_apply_apply, smul_smul]
  have hrhs : comul S (comul S (single (d, n) e)) x y z =
      ∑' k : ℕ, (comulScalar h x y k *
        comulSingleNat h d n (x.1 + y.1, x.2 + y.2 + k) z) • e := by
    have hsum := (hasSum_comul_apply_apply S (comul S (single (d, n) e)) x y).mapL (evalCLM S z)
    have htsum : comul S (comul S (single (d, n) e)) x y z =
        ∑' k : ℕ, evalCLM S z
          (comulScalar h x y k • comul S (single (d, n) e) (x.1 + y.1, x.2 + y.2 + k)) := by
      simpa only [evalCLM_apply] using hsum.tsum_eq.symm
    rw [htsum]
    refine tsum_congr fun k ↦ ?_
    rw [map_nsmul, evalCLM_apply, comul_single_apply_apply, smul_smul]
  rw [hlhs, hrhs]
  by_cases hd : (x.1 + y.1) + z.1 = d
  · have hd' : x.1 + (y.1 + z.1) = d := by rwa [← add_assoc]
    by_cases hle : x.2 + y.2 + z.2 ≤ n
    · rw [tsum_eq_sum (s := Finset.range (n - (x.2 + y.2 + z.2) + 1)) fun k hk ↦ by
          rw [Finset.mem_range, not_lt] at hk
          have hgt : n < x.2 + (y.2 + z.2 + k) := by omega
          simp [comulSingleNat, Nat.choose_eq_zero_of_lt hgt],
        tsum_eq_sum (s := Finset.range (n - (x.2 + y.2 + z.2) + 1)) fun k hk ↦ by
          rw [Finset.mem_range, not_lt] at hk
          have hgt : n < x.2 + y.2 + k + z.2 := by omega
          simp [comulSingleNat, Nat.choose_eq_zero_of_lt hgt],
        ← Finset.sum_smul, ← Finset.sum_smul,
        sum_comulScalar_mul_comulSingleNat_right d n x y z hd' hle,
        sum_comulScalar_mul_comulSingleNat_left d n x y z hd hle,
        carry_add_assoc x.1 y.1 z.1]
    · rw [not_le] at hle
      rw [tsum_eq_sum (s := ∅) fun k _ ↦ by
          have hgt : n < x.2 + (y.2 + z.2 + k) := by omega
          simp [comulSingleNat, Nat.choose_eq_zero_of_lt hgt],
        tsum_eq_sum (s := ∅) fun k _ ↦ by
          have hgt : n < x.2 + y.2 + k + z.2 := by omega
          simp [comulSingleNat, Nat.choose_eq_zero_of_lt hgt]]
      simp
  · have hd' : x.1 + (y.1 + z.1) ≠ d := by rwa [← add_assoc]
    rw [tsum_eq_sum (s := ∅) fun k _ ↦ by simp [comulSingleNat, hd'],
      tsum_eq_sum (s := ∅) fun k _ ↦ by simp [comulSingleNat, hd]]
    simp

/-- **Coassociativity of stage comultiplication.** Comultiplying the inner stage of `comul S c`
agrees with comultiplying its outer stage. -/
@[simp]
theorem comul_assoc {hc : ∃ C, ∀ d : AnalyticStage p h E, ‖comul S d‖ ≤ C * ‖d‖}
    (c : AnalyticStage p h E) :
    compLeft (comul S) hc (comul S c) = comul S (comul S c) := by
  ext x y z
  rw [compLeft_apply]
  have hL := (((((ZeroAtInftyContinuousMap.hasSum_single c).mapL (comul S)).mapL
    (evalCLM S x)).mapL (comul S)).mapL (evalCLM S y)).mapL (evalCLM S z)
  have hR := (((((ZeroAtInftyContinuousMap.hasSum_single c).mapL (comul S)).mapL
    (comul S)).mapL (evalCLM S x)).mapL (evalCLM S y)).mapL (evalCLM S z)
  simpa only [evalCLM_apply] using
    hL.unique (by simpa only [evalCLM_apply, comul_comul_single_apply S] using hR)

end Comul

/-! ### Evaluation and stage transitions -/

section Padic

variable {p h : ℕ} [hp : Fact p.Prime]
  {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

section CompLeft

variable {F R T : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]
  [IsUltrametricDist F] [CompleteSpace F]
  [Semiring T] [Module T F] [ContinuousConstSMul T F] [SMulCommClass ℤ_[p] T F]
  [Semiring R] [Module R E] [ContinuousConstSMul R E] [Module R F] [ContinuousConstSMul R F]
  [LinearMap.CompatibleSMul E F ℤ_[p] R]

/-- Stage evaluation commutes with `ℤ_p`-compatible bounded continuous linear maps on the
coefficients. -/
theorem eval_compLeft_apply (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval T (compLeft u hu c) x = u (eval S c x) := by
  refine (hasSum_eval_apply T (compLeft u hu c) x).unique ?_
  simpa only [compLeft_apply, ContinuousLinearMap.map_smul_of_tower] using
    (hasSum_eval_apply S c x).mapL u

/-- Stage re-expansion commutes with `ℤ_p`-compatible bounded continuous linear maps on the
coefficients. -/
theorem transition_compLeft (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (c : AnalyticStage p h E) :
    transition T (compLeft u hu c) = compLeft u hu (transition S c) := by
  ext ⟨a', j⟩
  rw [compLeft_apply, transition_apply, transition_apply]
  have hsum : Summable fun k : ℕ ↦
      ((k.choose j : ℤ_[p]) * ((a'.val / p ^ h : ℕ) : ℤ_[p]) ^ (k - j) * (p : ℤ_[p]) ^ j) •
        c ((a'.val : ZMod (p ^ h)), k) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Nat.cofinite_eq_atTop]
    refine squeeze_zero_norm (fun k ↦ (norm_smul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))) ?_
    have hinj : Function.Injective fun k : ℕ ↦ ((a'.val : ZMod (p ^ h)), k) :=
      fun _ _ hk ↦ (Prod.ext_iff.mp hk).2
    exact tendsto_zero_iff_norm_tendsto_zero.mp <|
      c.tendsto_cofinite.comp (Nat.cofinite_eq_atTop ▸ hinj.tendsto_cofinite)
  rw [← (hsum.hasSum.mapL u).tsum_eq]
  exact tsum_congr fun k ↦ by simp

/-- Multi-level stage re-expansion commutes with `ℤ_p`-compatible bounded continuous linear maps on
the coefficients. -/
theorem transitionLE_compLeft {k : ℕ} (hhk : h ≤ k) (u : E →L[R] F)
    (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (c : AnalyticStage p h E) :
    transitionLE T hhk (compLeft u hu c) = compLeft u hu (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ T hhk, transitionLE_succ S hhk, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ih, transition_compLeft S u hu]

end CompLeft

private theorem eval_eval_comul_single (i : ZMod (p ^ h) × ℕ) (e : E) (x y : ℤ_[p]) :
    eval S (eval S (comul S (single i e)) x) y = eval S (single i e) (x + y) := by
  obtain ⟨d, n⟩ := i
  obtain ⟨⟨a, u⟩, hx⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨⟨b, v⟩, hy⟩ := (PadicInt.discHomeomorph p h).surjective y
  have hx' : x = (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u :=
    hx ▸ PadicInt.discHomeomorph_apply h (a, u)
  have hy' : y = (b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v :=
    hy ▸ PadicInt.discHomeomorph_apply h (b, v)
  subst hx' hy'
  set q : ℕ := (a.val + b.val) / p ^ h
  have hxy : (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u + ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
      ((a + b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * ((q : ℤ_[p]) + u + v) := by
    have hab : a.val + b.val = (a + b).val + p ^ h * q := by
      rw [ZMod.val_add, Nat.mod_add_div]
    have hab' : ((a.val : ℤ_[p]) + b.val) = ((a + b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * q := by
      exact_mod_cast hab
    linear_combination hab'
  have hinner (j : ℕ) :
      eval S (comul S (single (d, n) e)) ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) (b, j) =
        ∑' i : ℕ, u ^ i • comulSingleNat h d n (a, i) (b, j) • e := by
    have hsum := (hasSum_eval_natCast_val_add_mul S
      (comul S (single (d, n) e)) a u).mapL (evalCLM ℤ_[p] (b, j))
    have htsum :
        eval S (comul S (single (d, n) e)) ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) (b, j) =
          ∑' i : ℕ, evalCLM ℤ_[p] (b, j) (u ^ i • comul S (single (d, n) e) (a, i)) := by
      simpa only [evalCLM_apply] using hsum.tsum_eq.symm
    rw [htsum]
    refine tsum_congr fun i ↦ ?_
    rw [map_smul, evalCLM_apply, comul_single_apply_apply]
  have hlhs :
      eval S (eval S (comul S (single (d, n) e)) ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u))
          ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
        ∑' j : ℕ, v ^ j • ∑' i : ℕ, u ^ i • comulSingleNat h d n (a, i) (b, j) • e := by
    rw [eval_natCast_val_add_mul]
    exact tsum_congr fun j ↦ congrArg (v ^ j • ·) (hinner j)
  rw [hlhs, hxy, eval_natCast_val_add_mul]
  by_cases hab : a + b = d
  · rw [tsum_eq_sum (s := Finset.range (n + 1)) fun j hj ↦ by
        rw [Finset.mem_range, not_lt] at hj
        rw [tsum_eq_sum (s := ∅) fun i _ ↦ by
          have hgt : n < i + j := by omega
          simp [comulSingleNat, Nat.choose_eq_zero_of_lt hgt]]
        simp,
      tsum_eq_single n fun m hm ↦ by simp [single_apply, hm]]
    simp only [hab, single_eq_same]
    have hpoly : ((q : ℤ_[p]) + u + v) ^ n =
        ∑ j ∈ Finset.range (n + 1), v ^ j *
          ∑ i ∈ Finset.range (n - j + 1), u ^ i *
            (n.choose (i + j) * (i + j).choose i * (q : ℤ_[p]) ^ (n - (i + j))) := by
      calc ((q : ℤ_[p]) + u + v) ^ n
          = (v + (u + (q : ℤ_[p]))) ^ n := by ring
        _ = ∑ j ∈ Finset.range (n + 1), v ^ j * (u + (q : ℤ_[p])) ^ (n - j) * n.choose j :=
            add_pow _ _ n
        _ = ∑ j ∈ Finset.range (n + 1), v ^ j *
              ∑ i ∈ Finset.range (n - j + 1), u ^ i *
                (n.choose (i + j) * (i + j).choose i * (q : ℤ_[p]) ^ (n - (i + j))) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [add_pow]
            calc v ^ j * (∑ i ∈ Finset.range (n - j + 1),
                    u ^ i * (q : ℤ_[p]) ^ (n - j - i) * (n - j).choose i) * n.choose j
                = ∑ i ∈ Finset.range (n - j + 1),
                    v ^ j * (u ^ i * ((n.choose j * (n - j).choose i : ℕ) *
                      (q : ℤ_[p]) ^ (n - j - i))) := by
                    rw [Finset.mul_sum, Finset.sum_mul]
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    push_cast
                    ring
              _ = ∑ i ∈ Finset.range (n - j + 1),
                    v ^ j * (u ^ i * (n.choose (i + j) * (i + j).choose i *
                      (q : ℤ_[p]) ^ (n - (i + j)))) := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    have hc : n.choose j * (n - j).choose i =
                        n.choose (i + j) * (i + j).choose i := by
                      rw [Nat.choose_symm_add, Nat.choose_mul (Nat.le_add_left j i),
                        Nat.add_sub_cancel_right]
                    have hsub : n - j - i = n - (i + j) := by omega
                    rw [hc, hsub]
                    push_cast
                    rfl
              _ = v ^ j * ∑ i ∈ Finset.range (n - j + 1),
                    u ^ i * (n.choose (i + j) * (i + j).choose i * (q : ℤ_[p]) ^ (n - (i + j))) :=
                  (Finset.mul_sum _ _ _).symm
    rw [hpoly, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_smul, Finset.sum_smul]
    congr 1
    rw [tsum_eq_sum (s := Finset.range (n - j + 1)) fun i hi ↦ by
      rw [Finset.mem_range, not_lt] at hi
      have hgt : n < i + j := by omega
      simp [comulSingleNat, Nat.choose_eq_zero_of_lt hgt]]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [comulSingleNat, hab, ite_true, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul]
    push_cast
    rfl
  · rw [tsum_eq_sum (s := ∅) fun j _ ↦ by
        rw [tsum_eq_sum (s := ∅) fun i _ ↦ by simp [comulSingleNat, hab]]
        simp,
      tsum_eq_sum (s := ∅) fun m _ ↦ by simp [single_apply, hab]]
    simp

/-- Evaluating a stage vector at `0 ∈ ℤ_p` reads the constant-term coefficient `c (0, 0)` on the
disc `pʰℤ_p`. -/
@[simp]
theorem eval_apply_zero (c : AnalyticStage p h E) : eval S c 0 = c (0, 0) := by
  have h0 : (0 : ℤ_[p]) = ((0 : ZMod (p ^ h)).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * 0 := by simp
  rw [h0, eval_natCast_val_add_mul, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- **Stage evaluation of `comul S c` in both variables recovers `(eval S c)(x + y)`.** -/
@[simp]
theorem eval_eval_comul (c : AnalyticStage p h E) (x y : ℤ_[p]) :
    eval S (eval S (comul S c) x) y = eval S c (x + y) := by
  have hL := (((((ZeroAtInftyContinuousMap.hasSum_single c).mapL (comul S)).mapL (eval S)).mapL
    (ContinuousMap.evalCLM S x)).mapL (eval S)).mapL (ContinuousMap.evalCLM S y)
  have hR := ((ZeroAtInftyContinuousMap.hasSum_single c).mapL (eval S)).mapL
    (ContinuousMap.evalCLM S (x + y))
  simpa only [ContinuousMap.evalCLM_apply] using
    hL.unique (by simpa only [ContinuousMap.evalCLM_apply, eval_eval_comul_single S] using hR)

private theorem isSMulRegular_analyticStage {F : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] {k : ℕ} (hpF : IsSMulRegular F (p : ℤ_[p])) :
    IsSMulRegular (AnalyticStage p k F) (p : ℤ_[p]) := by
  intro f g h
  ext i
  exact hpF (DFunLike.congr_fun h i)

private theorem comul_transition_padicInt (c : AnalyticStage p h ℤ_[p]) :
    comul ℤ_[p] (transition ℤ_[p] c) =
      compLeft (transition ℤ_[p]) ⟨1, fun d ↦ by simpa using norm_transition_le ℤ_[p] d⟩
        (transition ℤ_[p] (comul ℤ_[p] c)) := by
  have hp0 : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
    mul_right_injective₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply eval_injective ℤ_[p] (isSMulRegular_analyticStage hp0)
  ext x : 1
  apply eval_injective ℤ_[p] hp0
  ext y
  rw [eval_eval_comul, eval_transition,
    eval_compLeft_apply (S := ℤ_[p]) (T := ℤ_[p]) (transition ℤ_[p]),
    eval_transition, eval_transition, eval_eval_comul]

private theorem transition_eq_transition (T : Type*) [Semiring T] [Module T E]
    [ContinuousConstSMul T E] [SMulCommClass ℤ_[p] T E] (c : AnalyticStage p h E) :
    transition S c = transition T c := by
  ext ⟨a', j⟩
  rw [transition_apply, transition_apply]

private theorem transitionLE_eq_transitionLE (T : Type*) [Semiring T] [Module T E]
    [ContinuousConstSMul T E] [SMulCommClass ℤ_[p] T E] {k : ℕ} (hhk : h ≤ k)
    (c : AnalyticStage p h E) :
    transitionLE S hhk c = transitionLE T hhk c := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, transitionLE_succ T hhk, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ih, transition_eq_transition S T]

private theorem comul_transition_single_apply (i : ZMod (p ^ h) × ℕ) (e : E)
    (x y : ZMod (p ^ (h + 1)) × ℕ) :
    comul ℤ_[p] (transition ℤ_[p] (single i e)) x y =
      transition ℤ_[p] (transition ℤ_[p] (comul ℤ_[p] (single i e)) x) y := by
  let u : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
  have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ :=
    ⟨‖e‖, fun r ↦ by simpa [u, mul_comm] using norm_smul_le r e⟩
  have hsingle : single i e = compLeft u hu (single i (1 : ℤ_[p])) := by
    simp [u]
  have heq : comul ℤ_[p] (transition ℤ_[p] (single i e)) =
      compLeft (compLeft u hu) (exists_norm_compLeft_apply_le u hu)
        (compLeft (transition ℤ_[p]) ⟨1, fun d ↦ by simpa using norm_transition_le ℤ_[p] d⟩
          (transition ℤ_[p] (comul ℤ_[p] (single i (1 : ℤ_[p]))))) := by
    rw [hsingle, transition_compLeft ℤ_[p] u hu, comul_compLeft ℤ_[p] u hu,
      comul_transition_padicInt]
  rw [heq]
  simp only [compLeft_apply]
  rw [← compLeft_apply u hu, ← transition_compLeft (T := ℤ_[p]) ℤ_[p] u hu,
    ← compLeft_apply (compLeft u hu) (exists_norm_compLeft_apply_le u hu),
    ← transition_compLeft (T := ℤ_[p]) ℤ_[p] (compLeft u hu) (exists_norm_compLeft_apply_le u hu),
    ← comul_compLeft (T := ℤ_[p]) ℤ_[p] u hu, ← hsingle]

/-- **Comultiplication commutes with stage re-expansion.** Re-expanding `c` to level `h + 1` and
comultiplying agrees with comultiplying at level `h` and re-expanding both stages. No
torsion-freeness of `E` is needed. -/
theorem comul_transition (c : AnalyticStage p h E) :
    comul S (transition S c) =
      compLeft (transition S) ⟨1, fun d ↦ by simpa using norm_transition_le S d⟩
        (transition S (comul S c)) := by
  ext x y
  rw [compLeft_apply, comul_eq_comul S ℤ_[p], transition_eq_transition S ℤ_[p],
    transition_eq_transition S ℤ_[p], transition_eq_transition S ℤ_[p], comul_eq_comul S ℤ_[p]]
  have hL := ((((ZeroAtInftyContinuousMap.hasSum_single c).mapL (transition ℤ_[p])).mapL
    (comul ℤ_[p])).mapL (evalCLM ℤ_[p] x)).mapL (evalCLM ℤ_[p] y)
  have hR := (((((ZeroAtInftyContinuousMap.hasSum_single c).mapL (comul ℤ_[p])).mapL
    (transition ℤ_[p])).mapL (evalCLM ℤ_[p] x)).mapL (transition ℤ_[p])).mapL (evalCLM ℤ_[p] y)
  simpa only [evalCLM_apply] using
    hL.unique (by simpa only [evalCLM_apply, comul_transition_single_apply] using hR)

/-- Comultiplication commutes with multi-level stage re-expansion. -/
theorem comul_transitionLE {k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    comul S (transitionLE S hhk c) =
      compLeft (transitionLE S hhk) ⟨1, fun d ↦ by simpa using norm_transitionLE_le S hhk d⟩
        (transitionLE S hhk (comul S c)) := by
  have hZ : ∀ {k : ℕ} (hhk : h ≤ k),
      comul ℤ_[p] (transitionLE ℤ_[p] hhk c) =
        compLeft (transitionLE ℤ_[p] hhk)
          ⟨1, fun d ↦ by simpa using norm_transitionLE_le ℤ_[p] hhk d⟩
          (transitionLE ℤ_[p] hhk (comul ℤ_[p] c)) := by
    intro k hhk
    induction k, hhk using Nat.le_induction with
    | base =>
      ext x y
      simp
    | succ k hhk ih =>
      ext x y
      rw [compLeft_apply, transitionLE_succ ℤ_[p] hhk, ContinuousLinearMap.comp_apply,
        comul_transition ℤ_[p], compLeft_apply, ih,
        transition_compLeft ℤ_[p] (transitionLE ℤ_[p] hhk)
          ⟨1, fun d ↦ by simpa using norm_transitionLE_le ℤ_[p] hhk d⟩]
      simp only [compLeft_apply, transitionLE_succ ℤ_[p] hhk, ContinuousLinearMap.comp_apply]
  ext x y
  simpa only [compLeft_apply, comul_eq_comul S ℤ_[p], transitionLE_eq_transitionLE S ℤ_[p]] using
    congrArg (fun f ↦ f x y) (hZ hhk)

end Padic

end TauCeti.AnalyticStage
