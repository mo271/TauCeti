/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Localization
public import TauCeti.MeasureTheory.Function.Lp.Adjoint
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Truncation
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.Operator.Commutator
import TauCeti.MeasureTheory.Function.LpSeminorm.Clipping
import TauCeti.MeasureTheory.Integral.CalderonZygmund.Commutator
import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
import TauCeti.MeasureTheory.Integral.JohnNirenberg.HigherOscillation

/-!
# The Coifman–Rochberg–Weiss `Lᵖ` commutator theorem and VMO small-radius estimates

Let `T` be a Calderón–Zygmund singular integral operator and `b` a real-valued function of bounded
mean oscillation (`TauCeti.MemBMO`). While neither pointwise multiplication by `b` nor its
postcomposition with `T` preserves `Lᵖ` individually, **the Coifman–Rochberg–Weiss theorem**
asserts that their commutator

`[b, T] f (x) = b(x) T f(x) - T (b f)(x)`

is bounded on `Lᵖ` for every `1 < p < ∞`, with operator norm controlled by `‖b‖_{BMO}`.

The proof combines the pointwise sharp-maximal commutator bound with symmetric clipping,
extension of compact-support kernel representations to arbitrary open sets, orthonormal coordinate
transport, and BMO ball localization:

1. **Bounded multipliers on `ℝⁿ = ι → ℝ` (`1 < p < ∞`)**: when `b ∈ L^∞` and `f ∈ L² ∩ Lᵖ`,
   `[b, T] f` already belongs to `Lᵖ`, so the Fefferman–Stein sharp-maximal inequality
   (`TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction` at `p₀ = p`) applies directly without needing
   to cut off the domain. Combining the pointwise sharp-maximal bound
   (`TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`) at
   `q = (s + p) / 2` with the Hardy–Littlewood maximal bound for `q`-th root maximal functions
   (`TauCeti.eLpNorm_maximalFunction_rpow_le`) gives `‖[b, T] f‖_p ≤ C ‖b‖_{BMO} ‖f‖_p`.
2. **General BMO multipliers**: clipping `b` at height `k` via `bₖ = max (-k) (min k b)` produces
   `L^∞` symbols with `‖bₖ‖_{BMO} ≤ 2 ‖b‖_{BMO}` (`TauCeti.bmoSeminorm_max_min_le`) such that
   `bₖ • f → b • f` in `L²` (`TauCeti.tendsto_eLpNorm_max_min_smul_sub`). Continuity of `T` on `L²`
   yields an a.e. convergent subsequence of `T(bₖ • f)`, and Fatou's lemma passes the `Lᵖ` bound to
   `b`.
3. **Inner product spaces and compact-support kernel representations**: for any kernel satisfying
   the standard size bound `‖k x y‖ ≤ C₀ dist x y ^ (-n)`, kernel representation outside compact
   sets automatically extends to kernel representation on arbitrary open sets where the argument
   vanishes (`TauCeti.ae_eq_integral_of_isOpen_of_isCompact`). Transporting along an orthonormal
   basis then yields the Coifman–Rochberg–Weiss theorem on any finite-dimensional real inner
   product space `V`, both at the `eLpNorm` level and as a unique continuous linear extension
   `Lp E p volume →L[ℝ] Lp F p volume`.
4. **Small-radius VMO commutator estimates**: combining the global `Lᵖ` commutator bound with the
   BMO ball-localization theorem (`TauCeti.exists_eqOn_closedBall_bmoSeminorm_le`) controls `[b, T]`
   on `ball x₀ r` by the VMO modulus `vmoModulus b volume r`, making the local commutator norm on
   `Lᵖ(B_r(x₀))` arbitrarily small uniformly in `x₀` when `b ∈ VMO`.

## Main declarations

* `TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`: the Coifman–Rochberg–Weiss `Lᵖ`
  commutator inequality on `ι → ℝ` for all `1 < p < ∞`.
* `TauCeti.ae_eq_integral_of_isOpen_of_isCompact`: under the standard size bound
  `‖k x y‖ ≤ C₀ dist x y ^ (-finrank ℝ V)`, kernel representation off compact sets implies kernel
  representation on any open set where the `L²` input vanishes a.e.
* `TauCeti.exists_eLpNorm_smul_sub_le_of_isCompact_of_norm_sub_le_mul_rpow` and
  `ContinuousLinearMap.exists_commutator_of_isCompact_of_norm_sub_le_mul_rpow`: Banach-valued
  `Lᵖ` commutator bound and bundled `Lp E p →L[ℝ] Lp F p` commutator on a finite-dimensional real
  inner product space `V`.
* `ContinuousLinearMap.exists_eLpNorm_smul_sub_le_of_calderonZygmund` and
  `ContinuousLinearMap.exists_commutator_of_calderonZygmund`: Hilbert-valued Calderón–Zygmund
  specialization on `V`, deducing the intermediate `Lˢ` and `Lᵖ` bounds for `T` automatically.
* `TauCeti.eLpNorm_restrict_ball_smul_sub_le_mul_vmoModulus`,
  `TauCeti.exists_eLpNorm_restrict_ball_smul_sub_le_mul_vmoModulus`,
  `ContinuousLinearMap.exists_restrict_ball_commutator_of_vmoModulus_le`, and
  `ContinuousLinearMap.exists_restrict_ball_commutator_norm_le_of_memVMO`: small-radius local
  commutator bounds controlled by `vmoModulus b volume r` and vanishing uniformly for `MemVMO b`.

## References

* R. R. Coifman, R. Rochberg, and G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. (2) **103** (1976), 611–635.
* S. Janson, *Mean oscillation and commutators of singular integral operators*, Ark. Mat. **16**
  (1978), 263–270.
* F. Chiarenza, M. Frasca, and P. Longo, *Interior `W^{2,p}` estimates for nondivergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. **40** (1991), 149–168.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Theorem 3.5.6.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set Module ContinuousLinearMap
open scoped ENNReal NNReal Topology

section AeConst

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- When `b` is a.e. equal to a constant `c`, `b • T f - T (b • f)` vanishes almost everywhere by
linearity of `T`. -/
private theorem eLpNorm_smul_sub_eq_zero_of_ae_const (T : Lp E 2 μ →L[ℝ] Lp F 2 μ)
    {b : α → ℝ} {c : ℝ} (hb : b =ᵐ[μ] fun _ => c) (f g : Lp E 2 μ)
    (hg : g =ᵐ[μ] fun x => b x • f x) (p : ℝ≥0∞) :
    eLpNorm (fun x => b x • T f x - T g x) p μ = 0 := by
  have hgc : g = c • f := by
    apply Lp.ext
    filter_upwards [hg, hb, Lp.coeFn_smul c f] with x hxg hxb hxc
    rw [hxg, hxb, hxc, Pi.smul_apply]
  have hae : (fun x => b x • T f x - T g x) =ᵐ[μ] (0 : α → F) := by
    rw [hgc, map_smul]
    filter_upwards [hb, Lp.coeFn_smul c (T f)] with x hxb hxc
    rw [hxb, hxc, Pi.smul_apply, sub_self, Pi.zero_apply]
  rw [eLpNorm_congr_ae hae, eLpNorm_zero]

end AeConst

section Pi

/-! ### Strong-type `Lᵖ` commutator bound on `ℝⁿ = ι → ℝ` -/

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The `Lᵖ` commutator bound on `ι → ℝ` (`Nonempty ι`) when `b ∈ L^∞` and `f ∈ L² ∩ Lᵖ`: in this
case `[b, T] f` already belongs to `Lᵖ`, so the Fefferman–Stein inequality applies at `p₀ = p`. -/
private theorem exists_eLpNorm_smul_sub_le_of_memLp_top [Nonempty ι] {s : ℝ} {p : ℝ≥0∞}
    (hs : 1 ≤ s) (hsp : s < p.toReal) (hp : 1 < p) (hp_top : p ≠ ∞) (A A_p C₀ : ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) p volume ≤ A_p * eLpNorm h p volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, MemLp b ∞ volume → bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))), g =ᵐ[volume] (fun y => b y • f y) →
      MemLp f p volume →
        eLpNorm (fun y => b y • T f y - T g y) p volume ≤ C * M * eLpNorm f p volume := by
  set q := (s + p.toReal) / 2 with hq_def
  have hsq : s < q := by linarith
  have hqp : q < p.toReal := by linarith
  have hq0 : 0 < q := (lt_of_lt_of_le zero_lt_one hs).trans hsq
  obtain ⟨C_sh, hC_sh⟩ :=
    exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow (ι := ι) (E := E) (F := F)
      hs hsq A C₀ hδ
  set C_FS : ℝ≥0∞ :=
    ENNReal.ofReal (2 ^ (p.toReal + 1) * 2 ^ ((p.toReal + 2 * Fintype.card ι + 2) * p.toReal))
      ^ (1 / p.toReal)
  set C_HL : ℝ≥0∞ := maximalFunctionConst (finrank ℝ (ι → ℝ)) (p.toReal / q) ^ (1 / p.toReal)
  have hC_FS_fin : C_FS ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hC_HL_fin : C_HL ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (maximalFunctionConst_ne_top _ _)
  set C_tot : ℝ≥0∞ := C_FS * C_sh * (C_HL * (A_p + 1))
  have hC_tot : C_tot ≠ ∞ := by simp only [C_tot]; finiteness
  refine ⟨C_tot.toNNReal, fun T K hKm hK hrep hTs hTp b M hb_top hb_bmo f g hg hfp => ?_⟩
  have hTfp : MemLp (T f) p volume :=
    (hTp f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hfp)
  have hgp : MemLp g p volume := (hb_top.smul hfp).ae_eq hg.symm
  have hTgp : MemLp (T g) p volume :=
    (hTp g).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hgp)
  set Φ : (ι → ℝ) → F := fun y => b y • T f y - T g y
  have hΦp : MemLp Φ p volume := (hb_top.smul hTfp).sub hTgp
  have hpt := hC_sh T hKm hK hrep hTs (hb_top.locallyIntegrable le_top) hb_bmo f g hg
  set M_Tf : (ι → ℝ) → ℝ≥0∞ := fun x => maximalFunction volume (fun y => ‖T f y‖ₑ ^ q) x ^ q⁻¹
  set M_f : (ι → ℝ) → ℝ≥0∞ := fun x => maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹
  have hsharp_le : eLpNorm (sharpMaximalFunction volume Φ) p volume ≤
      (C_sh * M : ℝ≥0) * (eLpNorm M_Tf p volume + eLpNorm M_f p volume) := by
    calc eLpNorm (sharpMaximalFunction volume Φ) p volume
        ≤ eLpNorm (fun x => ((C_sh * M : ℝ≥0) : ℝ≥0∞) * (M_Tf x + M_f x)) p volume := by
          refine eLpNorm_mono_eNorm_ae
            (measurable_sharpMaximalFunction volume Φ).aestronglyMeasurable
            (Eventually.of_forall fun x => ?_)
          simpa only [eNorm_eq_self, ENNReal.coe_mul] using hpt x
      _ = (C_sh * M : ℝ≥0) * eLpNorm (M_Tf + M_f) p volume :=
          eLpNorm_const_smul_nnreal (f := M_Tf + M_f)
      _ ≤ (C_sh * M : ℝ≥0) * (eLpNorm M_Tf p volume + eLpNorm M_f p volume) := by
          gcongr; exact eLpNorm_add_le hp.le
  have hMTf : eLpNorm M_Tf p volume ≤ C_HL * A_p * eLpNorm f p volume :=
    (eLpNorm_maximalFunction_rpow_le volume (Lp.aestronglyMeasurable (T f)).eNorm
      hq0 hqp hp_top).trans (by rw [mul_assoc]; gcongr; exact hTp f)
  have hMf : eLpNorm M_f p volume ≤ C_HL * eLpNorm f p volume :=
    eLpNorm_maximalFunction_rpow_le volume (Lp.aestronglyMeasurable f).eNorm hq0 hqp hp_top
  rw [ENNReal.coe_toNNReal hC_tot]
  calc eLpNorm Φ p volume
      ≤ C_FS * eLpNorm (sharpMaximalFunction volume Φ) p volume :=
        eLpNorm_le_eLpNorm_sharpMaximalFunction hΦp hp.le le_rfl hp hp_top
    _ ≤ C_FS * ((C_sh * M : ℝ≥0) * (C_HL * A_p * eLpNorm f p volume +
          C_HL * eLpNorm f p volume)) := by
        gcongr; exact hsharp_le.trans (by gcongr)
    _ = C_tot * M * eLpNorm f p volume := by simp only [C_tot, ENNReal.coe_mul]; ring

omit [CompleteSpace F] in
/-- Clipping approximation on `ι → ℝ`: passes the `Lᵖ` commutator bound from bounded BMO symbols
`bₖ = max (-k) (min k b)` to arbitrary locally integrable BMO symbols `b` when `f ∈ L² ∩ Lᵖ`. -/
private theorem eLpNorm_smul_sub_le_of_forall_memLp_top {p : ℝ≥0∞} {C₁ : ℝ≥0}
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    (hbounded : ∀ {b' : (ι → ℝ) → ℝ} {M' : ℝ≥0}, MemLp b' ∞ volume →
      bmoSeminorm b' volume ≤ M' →
      ∀ (f' g' : Lp E 2 (volume : Measure (ι → ℝ))), g' =ᵐ[volume] (fun y => b' y • f' y) →
      MemLp f' p volume →
        eLpNorm (fun y => b' y • T f' y - T g' y) p volume ≤ C₁ * M' * eLpNorm f' p volume)
    {b : (ι → ℝ) → ℝ} {M : ℝ≥0} (hb : LocallyIntegrable b volume)
    (hM : bmoSeminorm b volume ≤ M)
    (f g : Lp E 2 (volume : Measure (ι → ℝ))) (hg : g =ᵐ[volume] fun y => b y • f y)
    (hfp : MemLp f p volume) :
    eLpNorm (fun y => b y • T f y - T g y) p volume ≤ (2 * C₁ : ℝ≥0) * M * eLpNorm f p volume := by
  set b_clip : ℕ → (ι → ℝ) → ℝ := fun k x => max (-(k : ℝ)) (min (k : ℝ) (b x))
  have hb_top (k : ℕ) : MemLp (b_clip k) ∞ volume :=
    hb.aestronglyMeasurable.memLp_top_max_min k
  have hb_bmo (k : ℕ) : bmoSeminorm (b_clip k) volume ≤ (2 * M : ℝ≥0) := by
    push_cast
    exact (bmoSeminorm_max_min_le hb.aestronglyMeasurable k).trans (by gcongr)
  have hg_mem (k : ℕ) : MemLp (fun y => b_clip k y • f y) 2 volume :=
    (hb_top k).smul (Lp.memLp f)
  set g_clip : ℕ → Lp E 2 (volume : Measure (ι → ℝ)) := fun k => (hg_mem k).toLp _
  have hg_tendsto : Tendsto g_clip atTop (𝓝 g) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbf2 : MemLp (fun y => b y • f y) 2 volume := (Lp.memLp g).ae_eq hg
    have heLp := (tendsto_eLpNorm_max_min_smul_sub (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hb.aestronglyMeasurable hbf2).comp tendsto_natCast_atTop_atTop
    have heq (k : ℕ) : ‖g_clip k - g‖ =
        (eLpNorm (fun y => b_clip k y • f y - b y • f y) 2 volume).toReal := by
      have hae : ((g_clip k - g : Lp E 2 volume) : (ι → ℝ) → E) =ᵐ[volume]
          fun y => b_clip k y • f y - b y • f y := by
        filter_upwards [Lp.coeFn_sub (g_clip k) g, (hg_mem k).coeFn_toLp, hg] with y h₁ h₂ h₃
        rw [h₁, Pi.sub_apply, h₂, h₃]
      rw [Lp.norm_def, eLpNorm_congr_ae hae]
    simp_rw [heq]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp heLp
  obtain ⟨ns, hns, hae_Tg⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      ((T.continuous.tendsto g).comp hg_tendsto)).exists_seq_tendsto_ae
  set Ψ : ℕ → (ι → ℝ) → F := fun j y => b_clip (ns j) y • T f y - T (g_clip (ns j)) y
  have hΨm (j : ℕ) : AEStronglyMeasurable (Ψ j) volume :=
    ((hb_top (ns j)).aestronglyMeasurable.smul (Lp.aestronglyMeasurable (T f))).sub
      (Lp.aestronglyMeasurable _)
  have hΦm : AEStronglyMeasurable (fun y => b y • T f y - T g y) volume :=
    (hb.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (T f))).sub (Lp.aestronglyMeasurable _)
  have hae_lim : ∀ᵐ y ∂volume, Tendsto (fun j => Ψ j y) atTop (𝓝 (b y • T f y - T g y)) := by
    filter_upwards [hae_Tg] with y hy
    have hb_lim : Tendsto (fun j => b_clip (ns j) y) atTop (𝓝 (b y)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hns.tendsto_atTop.eventually (eventually_ge_atTop ⌈|b y|⌉₊)] with j hj
      exact (max_neg_min_eq_self_of_abs_le ((Nat.le_ceil |b y|).trans (Nat.cast_le.2 hj))).symm
    exact (hb_lim.smul tendsto_const_nhds).sub hy
  refine Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun j => ?_) hΨm hΦm hae_lim
  calc eLpNorm (Ψ j) p volume
      ≤ C₁ * (2 * M : ℝ≥0) * eLpNorm f p volume :=
        hbounded (hb_top (ns j)) (hb_bmo (ns j)) f (g_clip (ns j)) (hg_mem (ns j)).coeFn_toLp hfp
    _ = (2 * C₁ : ℝ≥0) * M * eLpNorm f p volume := by push_cast; ring

/-- **The Coifman–Rochberg–Weiss `Lᵖ` commutator theorem on `ℝⁿ = ι → ℝ`.** Let `1 ≤ s < p < ∞`
(`1 < p`) and `δ > 0`. For every bounded operator `T : L²(ι → ℝ; E) →L[ℝ] L²(ι → ℝ; F)` satisfying:
- kernel representation `T h x = ∫ K x z (h z)` a.e. on any ball where `h` vanishes a.e., with
  first-variable smoothness `‖K x y - K x' y‖ ≤ C₀ dist x x' ^ δ dist y x' ^ (-(n + δ))` for
  `2 dist x x' < dist y x'`,
- `‖T h‖_s ≤ A ‖h‖_s` and `‖T h‖_p ≤ A_p ‖h‖_p` for all `h ∈ L²`,

and every locally integrable `b : (ι → ℝ) → ℝ` with `bmoSeminorm b volume ≤ M`, every pair
`f, g ∈ L²` with `g =ᵐ b • f` satisfies

`eLpNorm (fun y => b y • T f y - T g y) p volume ≤ C * M * eLpNorm f p volume`,

where `C > 0` depends only on `card ι`, `s`, `p`, `A`, `A_p`, `C₀`, and `δ`. -/
theorem exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow {s : ℝ} {p : ℝ≥0∞}
    (hs : 1 ≤ s) (hsp : s < p.toReal) (hp : 1 < p) (hp_top : p ≠ ∞) (A A_p C₀ : ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) p volume ≤ A_p * eLpNorm h p volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, LocallyIntegrable b volume → bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))), g =ᵐ[volume] (fun y => b y • f y) →
        eLpNorm (fun y => b y • T f y - T g y) p volume ≤ C * M * eLpNorm f p volume := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun T _ _ _ _ _ _ b M _ _ f g hg => ?_⟩
    have hb_const : b =ᵐ[volume] fun _ => b 0 :=
      Eventually.of_forall fun x => congrArg b (Subsingleton.elim x 0)
    rw [eLpNorm_smul_sub_eq_zero_of_ae_const T hb_const f g hg p]
    exact bot_le
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_smul_sub_le_of_memLp_top (ι := ι) (E := E) (F := F)
    hs hsp hp hp_top A A_p C₀ hδ
  set C : ℝ≥0 := 2 * C₁ + 1 with hC_def
  have hCpos : 0 < C := by rw [hC_def]; positivity
  refine ⟨C, hCpos, fun T K hKm hK hrep hTs hTp b M hb hM f g hg => ?_⟩
  rcases eq_or_ne M 0 with rfl | hM0
  · obtain ⟨c, hc⟩ := (bmoSeminorm_eq_zero_iff hb).1
      (le_antisymm (hM.trans_eq ENNReal.coe_zero) bot_le)
    rw [eLpNorm_smul_sub_eq_zero_of_ae_const T hc f g hg p]
    exact bot_le
  by_cases hfp : MemLp f p volume
  · refine (eLpNorm_smul_sub_le_of_forall_memLp_top T
      (fun hb_top hb_bmo f' g' hg' hfp' => hC₁ T hKm hK hrep hTs hTp hb_top hb_bmo f' g' hg' hfp')
      hb hM f g hg hfp).trans ?_
    rw [hC_def]
    gcongr
    exact le_self_add
  · have hftop : eLpNorm f p volume = ∞ := eq_top_iff.2 (not_lt.1 hfp)
    have hCM0 : (C : ℝ≥0∞) * M ≠ 0 :=
      mul_ne_zero (ENNReal.coe_ne_zero.2 hCpos.ne') (ENNReal.coe_ne_zero.2 hM0)
    rw [hftop, ENNReal.mul_top hCM0]
    exact le_top

end Pi

section KernelBridge

/-! ### Extending kernel representation from compact sets to arbitrary open sets -/

variable {V E F : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E]

/-- Truncating an `L²` function on a normed space to `closedBall 0 N` converges to it in `L²`. -/
private theorem tendsto_toLp_indicator_closedBall {μ : Measure V} (h : Lp E 2 μ) :
    Tendsto (fun N : ℕ =>
      ((Lp.memLp h).indicator (s := closedBall (0 : V) N)
        measurableSet_closedBall.nullMeasurableSet).toLp _) atTop (𝓝 h) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heLp : Tendsto (fun N : ℕ =>
      eLpNorm (fun z => (closedBall (0 : V) N).indicator h z - h z) 2 μ) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (Eventually.of_forall fun N => (Lp.aestronglyMeasurable h).indicator measurableSet_closedBall)
      (Lp.memLp h) (Eventually.of_forall fun N => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => tendsto_const_nhds.congr' ?_)
    · by_cases hz : z ∈ closedBall (0 : V) N
      · simp [indicator_of_mem hz]
      · simp [indicator_of_notMem hz]
    · filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with N hN
      have hzB : z ∈ closedBall (0 : V) N :=
        mem_closedBall_zero_iff.2 ((Nat.le_ceil ‖z‖).trans (Nat.cast_le.2 hN))
      exact (indicator_of_mem hzB h).symm
  have hnorm (N : ℕ) :
      ‖((Lp.memLp h).indicator (s := closedBall (0 : V) N)
          measurableSet_closedBall.nullMeasurableSet).toLp _ - h‖ =
        (eLpNorm (fun z => (closedBall (0 : V) N).indicator h z - h z) 2 μ).toReal := by
    have hae : ((((Lp.memLp h).indicator (s := closedBall (0 : V) N)
        measurableSet_closedBall.nullMeasurableSet).toLp _ - h : Lp E 2 μ) : V → E) =ᵐ[μ]
        fun z => (closedBall (0 : V) N).indicator h z - h z := by
      filter_upwards [Lp.coeFn_sub _ h,
        ((Lp.memLp h).indicator (s := closedBall (0 : V) N)
          measurableSet_closedBall.nullMeasurableSet).coeFn_toLp] with z h₁ h₂
      rw [h₁, Pi.sub_apply, h₂]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
  simp_rw [hnorm]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp heLp

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Off `{z | R < dist z x}` (`R > 0`, `finrank ℝ V > 0`), `dist x z ^ (-n)` lies in `L²(μ)`, so its
product with `‖h z‖` (`h ∈ L²(μ)`) is integrable by Cauchy–Schwarz. -/
private theorem integrable_indicator_dist_rpow_neg_mul_norm {μ : Measure V} [μ.IsAddHaarMeasure]
    (hdim : 0 < finrank ℝ V) (h : Lp E 2 μ) (x : V) {R : ℝ} (hR : 0 < R) :
    Integrable (fun z => {z | R < dist z x}.indicator
      (fun z => dist x z ^ (-(finrank ℝ V : ℝ))) z * ‖h z‖) μ := by
  set n := finrank ℝ V
  set S : Set V := {z | R < dist z x}
  have hSm : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_id.dist measurable_const)
  set w : V → ℝ := S.indicator (fun z => dist x z ^ (-(n : ℝ)))
  have hwm : Measurable w :=
    ((measurable_const.dist measurable_id).pow_const (-(n : ℝ))).indicator hSm
  have hw2 : MemLp w 2 μ := by
    refine (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      hwm.aestronglyMeasurable).2 ?_
    have heq : (fun z => ‖w z‖ₑ ^ (2 : ℝ)) =
        S.indicator (fun z => ENNReal.ofReal (dist z x ^ (-(2 * (n : ℝ))))) := by
      ext z
      by_cases hz : z ∈ S
      · have hpos : 0 < dist x z := by rw [dist_comm]; exact hR.trans hz
        rw [indicator_of_mem hz, show w z = dist x z ^ (-(n : ℝ)) from indicator_of_mem hz _,
          Real.eNorm_of_nonneg (Real.rpow_nonneg hpos.le _),
          ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hpos.le _) zero_le_two,
          ← Real.rpow_mul hpos.le, dist_comm x z]
        ring_nf
      · simp [w, indicator_of_notMem hz]
    rw [ENNReal.toReal_ofNat, heq, lintegral_indicator hSm]
    have hns : (n : ℝ) < 2 * (n : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hdim
      linarith
    have htail := setLIntegral_ofReal_dist_rpow_neg_le (μ := μ) (y := x)
      (A := μ (ball (0 : V) 1)) (n := (n : ℝ)) (s := 2 * (n : ℝ)) (R := R)
      (fun r hr => by
        rw [Measure.addHaar_ball_of_pos μ x (hR.trans hr), Measure.addHaar_ball_center,
          mul_comm, Real.rpow_natCast]) hns hR
    exact htail.trans_lt (ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top)
  exact hw2.integrable_mul (Lp.memLp h).norm

variable [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Dominated convergence for `∫ k x z (h_tr (ns j) z)` when `h` vanishes a.e. on an open
neighbourhood of `x`. -/
private theorem tendsto_integral_kernel_indicator_closedBall {μ : Measure V} [μ.IsAddHaarMeasure]
    (hdim : 0 < finrank ℝ V) {k : V → V → E →L[ℝ] F} {x : V}
    (hkmx : AEStronglyMeasurable (k x) μ) {C₀ : ℝ≥0}
    (hsize : ∀ y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ)))
    (h : Lp E 2 μ) {U : Set V} {ρ : ℝ} (hρ : 0 < ρ) (hballU : ball x ρ ⊆ U)
    {ns : ℕ → ℕ} (hns : StrictMono ns) {h_tr : ℕ → Lp E 2 μ}
    (hae_hns : ∀ᵐ z ∂μ, (z ∈ U → h z = 0) ∧
      ∀ j, h_tr (ns j) z = (closedBall (0 : V) (ns j)).indicator h z) :
    Tendsto (fun j => ∫ z, k x z (h_tr (ns j) z) ∂μ) atTop (𝓝 (∫ z, k x z (h z) ∂μ)) := by
  set R := ρ / 2 with hR_def
  have hR : 0 < R := half_pos hρ
  set bound : V → ℝ := fun z => (C₀ : ℝ) *
    ({z | R < dist z x}.indicator (fun z => dist x z ^ (-(finrank ℝ V : ℝ))) z * ‖h z‖)
  refine tendsto_integral_of_dominated_convergence bound
    (fun j => (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).aestronglyMeasurable_comp₂ hkmx
      (Lp.aestronglyMeasurable (h_tr (ns j))))
    ((integrable_indicator_dist_rpow_neg_mul_norm hdim h x hR).const_mul (C₀ : ℝ))
    (fun j => hae_hns.mono fun z ⟨hzU0, hzj⟩ => ?_)
    (hae_hns.mono fun z ⟨_, hzj⟩ => ?_)
  · rw [hzj j]
    by_cases hzU : z ∈ U
    · have hz0 : h z = 0 := hzU0 hzU
      have hind0 : (closedBall (0 : V) (ns j)).indicator h z = 0 := by
        by_cases hzB : z ∈ closedBall (0 : V) (ns j) <;> simp [hzB, hz0]
      simp [bound, hz0, hind0]
    · have hdist : R < dist z x := by
        have : ρ ≤ dist z x := not_lt.1 fun hlt => hzU (hballU (mem_ball.2 hlt))
        linarith
      have hxz : x ≠ z := fun hxz => by simp [hxz] at hdist; linarith
      calc ‖k x z ((closedBall (0 : V) (ns j)).indicator h z)‖
          ≤ ‖k x z‖ * ‖(closedBall (0 : V) (ns j)).indicator h z‖ := le_opNorm _ _
        _ ≤ (C₀ * dist x z ^ (-(finrank ℝ V : ℝ))) * ‖h z‖ :=
            mul_le_mul (hsize z hxz) (norm_indicator_le_norm_self h z)
              (norm_nonneg _) (by positivity)
        _ = bound z := by
            dsimp only [bound]
            rw [indicator_of_mem (show z ∈ {z | R < dist z x} from hdist), mul_assoc]
  · refine ((k x z).continuous.tendsto (h z)).comp (tendsto_const_nhds.congr' ?_)
    filter_upwards [hns.tendsto_atTop.eventually (eventually_ge_atTop ⌈‖z‖⌉₊)] with j hj
    rw [hzj j]
    have hzB : z ∈ closedBall (0 : V) (ns j) :=
      mem_closedBall_zero_iff.2 ((Nat.le_ceil ‖z‖).trans (Nat.cast_le.2 hj))
    exact (indicator_of_mem hzB h).symm

/-- **Kernel representation on open sets from compact-support kernel representation.** Suppose
`T : L²(μ; E) →L[ℝ] L²(μ; F)` on a finite-dimensional real normed space `V` with Haar measure `μ`
is represented outside any compact set `s` by a kernel `k` satisfying the standard size estimate
`‖k x y‖ ≤ C₀ dist x y ^ (-finrank ℝ V)` (`x ≠ y`). Then for every open set `U ⊆ V` and every
`h ∈ L²(μ; E)` vanishing a.e. on `U`,

`T h x = ∫ z, k x z (h z) ∂μ` for `μ`-almost every `x ∈ U`.

In particular, standard Calderón–Zygmund operators whose kernel representation is initially verified
only for compactly supported inputs automatically satisfy the ball-vanishing representation needed
for commutator estimates. -/
theorem ae_eq_integral_of_isOpen_of_isCompact {μ : Measure V} [μ.IsAddHaarMeasure]
    (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) {k : V → V → E →L[ℝ] F}
    (hkm : ∀ x, AEStronglyMeasurable (k x) μ) {C₀ : ℝ≥0}
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hrep : ∀ (f : Lp E 2 μ) (s : Set V), IsCompact s →
      (∀ᵐ x ∂μ, x ∉ s → f x = 0) → ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ z, k x z (f z) ∂μ)
    (h : Lp E 2 μ) {U : Set V} (hU : IsOpen U) (hU0 : ∀ᵐ z ∂μ, z ∈ U → h z = 0) :
    ∀ᵐ x ∂μ, x ∈ U → T h x = ∫ z, k x z (h z) ∂μ := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
  · exact Eventually.of_forall fun _ hx => False.elim hx
  rcases Nat.eq_zero_or_pos (finrank ℝ V) with hdim0 | hdim
  · have : Subsingleton V := Module.finrank_zero_iff.1 hdim0
    have hUuniv : U = univ := eq_univ_of_forall fun x => Subsingleton.elim x u₀ ▸ hu₀
    have hLp0 : h = 0 := by
      apply Lp.ext
      filter_upwards [hU0, Lp.coeFn_zero E 2 μ] with z hz₁ hz₂
      rw [hz₁ (hUuniv ▸ mem_univ z), hz₂, Pi.zero_apply]
    rw [hLp0, map_zero]
    filter_upwards [Lp.coeFn_zero F 2 μ] with x hx _
    have hint0 : ∫ z, k x z ((0 : Lp E 2 μ) z) ∂μ = 0 := by
      refine (integral_congr_ae (g := fun _ => (0 : F)) ?_).trans (integral_zero V F)
      filter_upwards [Lp.coeFn_zero E 2 μ] with z hz
      rw [hz, Pi.zero_apply, map_zero]
    rw [hx, Pi.zero_apply, hint0]
  have hmB (N : ℕ) : NullMeasurableSet (closedBall (0 : V) N) μ :=
    measurableSet_closedBall.nullMeasurableSet
  set h_tr : ℕ → Lp E 2 μ := fun N => ((Lp.memLp h).indicator (hmB N)).toLp _
  have hrep_N (N : ℕ) : ∀ᵐ x ∂μ, x ∈ U → T (h_tr N) x = ∫ z, k x z (h_tr N z) ∂μ := by
    have hsN : IsCompact (closedBall (0 : V) N \ U) := (isCompact_closedBall 0 N).diff hU
    have hsupp : ∀ᵐ z ∂μ, z ∉ closedBall (0 : V) N \ U → h_tr N z = 0 := by
      filter_upwards [((Lp.memLp h).indicator (hmB N)).coeFn_toLp, hU0] with z hz₁ hz₂ hzs
      rw [hz₁]
      by_cases hzB : z ∈ closedBall (0 : V) N
      · rw [indicator_of_mem hzB]
        exact hz₂ (by_contra fun hzU => hzs ⟨hzB, hzU⟩)
      · exact indicator_of_notMem hzB _
    filter_upwards [hrep (h_tr N) _ hsN hsupp] with x hx hxU
    exact hx fun hxs => hxs.2 hxU
  obtain ⟨ns, hns, hae_T⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((T.continuous.tendsto h).comp (tendsto_toLp_indicator_closedBall h))).exists_seq_tendsto_ae
  have hae_hns : ∀ᵐ z ∂μ, (z ∈ U → h z = 0) ∧
      ∀ j, h_tr (ns j) z = (closedBall (0 : V) (ns j)).indicator h z :=
    hU0.and (ae_all_iff.2 fun j => ((Lp.memLp h).indicator (hmB (ns j))).coeFn_toLp)
  filter_upwards [hae_T, ae_all_iff.2 fun j => hrep_N (ns j)] with x hxT hxrep hxU
  obtain ⟨ρ, hρ, hballU⟩ := Metric.isOpen_iff.1 hU x hxU
  have hdom := tendsto_integral_kernel_indicator_closedBall hdim (hkm x) (hsize x) h hρ hballU hns
    hae_hns
  exact tendsto_nhds_unique hxT (hdom.congr fun j => (hxrep j hxU).symm)

end KernelBridge

section InnerProductSpace

/-! ### Orthonormal coordinate transport to finite-dimensional real inner product spaces -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section CoordHelpers

variable {ι : Type*} [Fintype ι] (bas : OrthonormalBasis ι ℝ V)

private noncomputable def ipCoord : (ι → ℝ) ≃ᵐ V :=
  (MeasurableEquiv.toLp 2 (ι → ℝ)).trans bas.measurableEquiv.symm

private theorem ipCoord_apply (x : ι → ℝ) : ipCoord bas x = bas.repr.symm (WithLp.toLp 2 x) :=
  rfl

private theorem continuous_ipCoord : Continuous (ipCoord bas) :=
  bas.repr.symm.continuous.comp (PiLp.continuous_toLp 2 _)

private theorem continuous_ipCoord_symm : Continuous (ipCoord bas).symm :=
  (PiLp.continuous_ofLp 2 _).comp bas.repr.continuous

private theorem dist_le_dist_ipCoord (x x' : ι → ℝ) :
    dist x x' ≤ dist (ipCoord bas x) (ipCoord bas x') := by
  rw [ipCoord_apply, ipCoord_apply, LinearIsometryEquiv.dist_map]
  simpa using (PiLp.lipschitzWith_ofLp 2 (fun _ : ι => ℝ)).dist_le_mul
    (WithLp.toLp 2 x) (WithLp.toLp 2 x')

private theorem dist_ipCoord_le (x x' : ι → ℝ) :
    dist (ipCoord bas x) (ipCoord bas x') ≤ NNReal.sqrt (Fintype.card ι) * dist x x' := by
  rw [ipCoord_apply, ipCoord_apply, LinearIsometryEquiv.dist_map]
  have h := (PiLp.lipschitzWith_toLp 2 (fun _ : ι => ℝ)).dist_le_mul x x'
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
  rwa [NNReal.sqrt_eq_rpow]

/-- First-variable smoothness of `k` in coordinates from size + first-variable smoothness on `V`. -/
private theorem norm_ipCoord_sub_first_le [Nonempty ι] {G : Type*} [SeminormedAddGroup G]
    {k : V → V → G} {C₀ C₁ : ℝ≥0} {δ : ℝ} (hδ : 0 ≤ δ)
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(Fintype.card ι : ℝ)))
    (hk : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖k x y - k x' y‖ ≤ C₁ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ))))
    {x x' y : ι → ℝ} (h : 2 * dist x x' < dist y x') :
    ‖k (ipCoord bas x) (ipCoord bas y) - k (ipCoord bas x') (ipCoord bas y)‖ ≤
      (C₁ * NNReal.sqrt (Fintype.card ι) ^ δ +
          2 * C₀ * (2 * NNReal.sqrt (Fintype.card ι)) ^ (Fintype.card ι + δ) : ℝ≥0) *
        (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ))) := by
  set e := ipCoord bas
  set n : ℝ := (Fintype.card ι : ℝ)
  set L := NNReal.sqrt (Fintype.card ι)
  have hL : 1 ≤ L := NNReal.one_le_sqrt.2 (by exact_mod_cast Fintype.card_pos)
  have hsize' : ∀ u v, 0 < dist u v → ‖k (e v) (e u)‖ ≤ C₀ * dist u v ^ (-n) := fun u v huv => by
    have hle : dist u v ≤ dist (e v) (e u) := by
      rw [dist_comm (e v)]
      exact dist_le_dist_ipCoord bas u v
    refine (hsize _ _ (dist_pos.1 (huv.trans_le hle))).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos huv hle (by simp [n]))
      C₀.coe_nonneg
  have hsmooth : ∀ u v v', (2 * L : ℝ≥0) * dist v v' < dist u v' →
      ‖k (e v) (e u) - k (e v') (e u)‖ ≤
        (C₁ * L ^ δ : ℝ≥0) * (dist v v' ^ δ * dist u v' ^ (-(n + δ))) := by
    intro u v v' huv
    have h₁ : dist (e v) (e v') ≤ L * dist v v' := dist_ipCoord_le bas v v'
    have h₂ : dist u v' ≤ dist (e u) (e v') := dist_le_dist_ipCoord bas u v'
    have huv' : 0 < dist u v' := lt_of_le_of_lt (by positivity) huv
    push_cast at huv ⊢
    refine (hk _ _ _ (by linarith)).trans ?_
    have h₃ : dist (e v) (e v') ^ δ ≤ (L : ℝ) ^ δ * dist v v' ^ δ := by
      rw [← Real.mul_rpow L.coe_nonneg dist_nonneg]
      exact Real.rpow_le_rpow dist_nonneg h₁ hδ
    have h₄ : dist (e u) (e v') ^ (-(n + δ)) ≤ dist u v' ^ (-(n + δ)) :=
      Real.rpow_le_rpow_of_nonpos huv' h₂ (by simp only [n]; linarith)
    calc (C₁ : ℝ) * (dist (e v) (e v') ^ δ * dist (e u) (e v') ^ (-(n + δ)))
        ≤ C₁ * ((L ^ δ * dist v v' ^ δ) * dist u v' ^ (-(n + δ))) := by gcongr
      _ = C₁ * L ^ δ * (dist v v' ^ δ * dist u v' ^ (-(n + δ))) := by ring
  exact norm_sub_le_mul_rpow_of_norm_le_mul_rpow (K := fun u v => k (e v) (e u))
    (by positivity) (by positivity) (le_mul_of_one_le_right zero_le_two hL) hsize' hsmooth h

variable [FiniteDimensional ℝ V]

private theorem measurePreserving_ipCoord : MeasurePreserving (ipCoord bas) :=
  bas.measurePreserving_measurableEquiv.symm.comp (PiLp.volume_preserving_toLp ι)

private noncomputable def lpIpCoord (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 (volume : Measure V) ≃ₗᵢ[ℝ] Lp E 2 (volume : Measure (ι → ℝ)) :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_ipCoord bas)
    (measurePreserving_ipCoord bas).symm (.of_forall fun v => (ipCoord bas).apply_symm_apply v)

private theorem coeFn_lpIpCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume : Measure V)) : lpIpCoord bas E f =ᵐ[volume] f ∘ ipCoord bas :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv ..

private theorem coeFn_lpIpCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    (lpIpCoord bas E).symm f =ᵐ[volume] f ∘ (ipCoord bas).symm :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv_symm ..

private theorem eLpNorm_lpIpCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume : Measure V)) (p : ℝ≥0∞) :
    eLpNorm (lpIpCoord bas E f) p volume = eLpNorm f p volume :=
  (eLpNorm_congr_ae (coeFn_lpIpCoord bas f)).trans
    (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (measurePreserving_ipCoord bas))

private noncomputable def ipCoordConj {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) :
    Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)) :=
  (lpIpCoord bas F : Lp F 2 (volume : Measure V) →L[ℝ] _) ∘L T ∘L
    ((lpIpCoord bas E).symm : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] _)

private theorem ipCoordConj_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    (h : Lp E 2 (volume : Measure (ι → ℝ))) :
    ipCoordConj bas T h = lpIpCoord bas F (T ((lpIpCoord bas E).symm h)) := rfl

private theorem ipCoordConj_lpIpCoord {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    (f : Lp E 2 (volume : Measure V)) :
    ipCoordConj bas T (lpIpCoord bas E f) = lpIpCoord bas F (T f) := by
  rw [ipCoordConj_apply, LinearIsometryEquiv.symm_apply_apply]

private theorem eLpNorm_ipCoordConj_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) {q : ℝ≥0∞} {B : ℝ≥0}
    (hTq : ∀ u : Lp E 2 (volume : Measure V), eLpNorm (T u) q volume ≤ B * eLpNorm u q volume)
    (h : Lp E 2 (volume : Measure (ι → ℝ))) :
    eLpNorm (ipCoordConj bas T h) q volume ≤ B * eLpNorm h q volume := by
  have h₂ : eLpNorm ((lpIpCoord bas E).symm h) q volume = eLpNorm h q volume :=
    (eLpNorm_congr_ae (coeFn_lpIpCoord_symm bas h)).trans
      (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable h)
        (measurePreserving_ipCoord bas).symm)
  rw [ipCoordConj_apply, eLpNorm_lpIpCoord, ← h₂]
  exact hTq _

/-- Ball-vanishing kernel representation in coordinates, deduced from compact-support kernel
representation on `V` via `TauCeti.ae_eq_integral_of_isOpen_of_isCompact`. -/
private theorem ipCoordConj_ae_eq_integral_ball {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    {k : V → V → E →L[ℝ] F} (hkm : ∀ x, AEStronglyMeasurable (k x) volume) {C₀ : ℝ≥0}
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hrep : ∀ (f : Lp E 2 (volume : Measure V)) (s_c : Set V), IsCompact s_c →
      (∀ᵐ x, x ∉ s_c → f x = 0) → ∀ᵐ x, x ∉ s_c → T f x = ∫ z, k x z (f z))
    (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ)
    (hh : ∀ᵐ z, z ∈ ball y ρ → h z = 0) :
    ∀ᵐ x, x ∈ ball y ρ →
      ipCoordConj bas T h x = ∫ z, k (ipCoord bas x) (ipCoord bas z) (h z) := by
  set e := ipCoord bas
  have he := measurePreserving_ipCoord bas
  set U : Set V := e.symm ⁻¹' ball y ρ
  have hU : IsOpen U := isOpen_ball.preimage (continuous_ipCoord_symm bas)
  have hh_symm := coeFn_lpIpCoord_symm bas h
  have hU0 : ∀ᵐ v ∂volume, v ∈ U → (lpIpCoord bas E).symm h v = 0 := by
    filter_upwards [hh_symm, he.symm.quasiMeasurePreserving.ae hh] with v hv₁ hv₂ hvU
    exact hv₁.trans (hv₂ hvU)
  have hopen := ae_eq_integral_of_isOpen_of_isCompact T hkm hsize hrep _ hU hU0
  have hge : ((lpIpCoord bas E).symm h : V → E) ∘ e =ᵐ[volume] h := by
    filter_upwards [he.quasiMeasurePreserving.ae_eq_comp hh_symm] with z hz
    simpa [Function.comp_apply] using hz
  filter_upwards [coeFn_lpIpCoord bas (T ((lpIpCoord bas E).symm h)),
    he.quasiMeasurePreserving.ae hopen] with x hx₁ hx₂ hxB
  have hexU : e x ∈ U := by simpa [U, e.symm_apply_apply] using hxB
  rw [ipCoordConj_apply, hx₁, Function.comp_apply, hx₂ hexU,
    ← he.integral_comp' (fun v => k (e x) v ((lpIpCoord bas E).symm h v))]
  exact integral_congr_ae (hge.mono fun z hz => congrArg (k (e x) (e z)) hz)

private theorem locallyIntegrable_comp_ipCoord {b_sym : V → ℝ}
    (hb : LocallyIntegrable b_sym volume) :
    LocallyIntegrable (b_sym ∘ ipCoord bas) volume :=
  locallyIntegrable_iff.2 fun _ hK =>
    ((measurePreserving_ipCoord bas).integrableOn_image (ipCoord bas).measurableEmbedding).1
      (hb.integrableOn_isCompact (hK.image (continuous_ipCoord bas)))

/-- Comparing the sup-ball BMO seminorm of `b_sym ∘ ipCoord bas` on `ι → ℝ` with the Euclidean BMO
seminorm of `b_sym` on `V`. -/
private theorem bmoSeminorm_comp_ipCoord_le [Nonempty ι] {b_sym : V → ℝ}
    (hb : LocallyIntegrable b_sym volume) :
    bmoSeminorm (b_sym ∘ ipCoord bas) volume ≤
      2 * (ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι) *
        volume (ball (0 : V) 1) / volume (ball (0 : ι → ℝ) 1)) *
        bmoSeminorm b_sym volume := by
  set e := ipCoord bas
  have he := measurePreserving_ipCoord bas
  refine bmoSeminorm_le fun c r => ?_
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hcard_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hsqrt_pos : 0 < √(Fintype.card ι) := Real.sqrt_pos.2 hcard_pos
  have hcoe_sqrt : (NNReal.sqrt (Fintype.card ι) : ℝ) = √(Fintype.card ι) := by
    rw [NNReal.sqrt_eq_rpow, NNReal.coe_rpow, NNReal.coe_natCast, ← Real.sqrt_eq_rpow]
  set B := ball (e c) (√(Fintype.card ι) * r)
  set S : Set V := e.symm ⁻¹' ball c r
  have hSB : S ⊆ B := by
    intro v hv
    rw [mem_preimage, mem_ball] at hv
    rw [mem_ball]
    have hd := dist_ipCoord_le bas (e.symm v) c
    rw [show (ipCoord bas) (e.symm v) = v from e.apply_symm_apply v, hcoe_sqrt] at hd
    exact hd.trans_lt (mul_lt_mul_of_pos_left hv hsqrt_pos)
  have hS : volume S = volume (ball c r) :=
    he.symm.measure_preimage measurableSet_ball.nullMeasurableSet
  have hmap : volume.map e = (1 : ℝ≥0∞) • volume := by rw [one_smul, he.map_eq]
  have hpreS : e ⁻¹' S = ball c r := by ext z; simp [S]
  have hintS : IntegrableOn b_sym S volume :=
    ((hb.integrableOn_isCompact (isCompact_closedBall (e c) (√(Fintype.card ι) * r))).mono_set
      ball_subset_closedBall).mono_set hSB
  have hfinrank : finrank ℝ V = Fintype.card ι := Module.finrank_eq_card_basis bas.toBasis
  have hratio : volume B / volume (ball c r) =
      ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι) *
        volume (ball (0 : V) 1) / volume (ball (0 : ι → ℝ) 1) := by
    rw [Measure.addHaar_ball_of_pos _ _ (mul_pos hsqrt_pos hr),
      Measure.addHaar_ball_of_pos _ _ hr, hfinrank, Module.finrank_fintype_fun_eq_card, mul_pow,
      ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (√_ ^ _)), mul_assoc,
      ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos hr _)).ne' ENNReal.ofReal_ne_top,
      mul_div_assoc]
  have hcomp := setLAverage_enorm_sub_setAverage_comp_preimage_of_map_eq_smul
    hmap one_ne_zero ENNReal.one_ne_top b_sym S
  rw [hpreS] at hcomp
  -- Unfold `Function.comp` in `b_sym ∘ e` so `hcomp` rewrites the oscillation average onto `S`.
  change ⨍⁻ z in ball c r, ‖b_sym (e z) - ⨍ w in ball c r, b_sym (e w)‖ₑ ≤ _
  rw [hcomp]
  refine (setLAverage_enorm_sub_setAverage_le (s := S) hintS (⨍ v in B, b_sym v)).trans ?_
  rw [mul_assoc]
  gcongr 2 * ?_
  refine (setLAverage_le_div_mul_setLAverage_of_subset hSB measure_ball_lt_top.ne).trans ?_
  rw [hS, hratio]
  gcongr
  exact setLAverage_enorm_sub_setAverage_le_bmoSeminorm b_sym volume _ _

/-- Every `MemBMO b_sym volume` on `V` lies in `L²` on every Euclidean ball `ball x₀ r`. -/
private theorem memLp_restrict_ball_of_memBMO {b_sym : V → ℝ} (hb : MemBMO b_sym volume)
    (x₀ : V) (r : ℝ) : MemLp b_sym 2 (volume.restrict (ball x₀ r)) := by
  set bas₀ := stdOrthonormalBasis ℝ V
  set e := ipCoord bas₀
  have he := measurePreserving_ipCoord bas₀
  have hb_comp : MemBMO (b_sym ∘ e) volume := by
    rcases isEmpty_or_nonempty (Fin (finrank ℝ V)) with hι | hι
    · exact (memBMO_const (b_sym (e 0))).congr_ae
        (Eventually.of_forall fun x => congrArg (b_sym ∘ e) (Subsingleton.elim 0 x))
    refine memBMO_iff.2 ⟨locallyIntegrable_comp_ipCoord bas₀ hb.locallyIntegrable,
      (bmoSeminorm_comp_ipCoord_le bas₀ hb.locallyIntegrable).trans_lt ?_⟩
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofNat_lt_top
      (ENNReal.div_lt_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
        (measure_ball_pos _ _ one_pos).ne')) hb.bmoSeminorm_lt_top
  have hsub : e ⁻¹' ball x₀ r ⊆ ball (e.symm x₀) r := by
    intro z hz
    rw [mem_preimage, mem_ball] at hz
    rw [mem_ball]
    have hd := dist_le_dist_ipCoord bas₀ z (e.symm x₀)
    rw [show ipCoord bas₀ (e.symm x₀) = x₀ from e.apply_symm_apply x₀] at hd
    exact hd.trans_lt hz
  have hpre : MemLp (b_sym ∘ e) 2 (volume.restrict (e ⁻¹' ball x₀ r)) :=
    (hb_comp.memLp_restrict_ball_pi ENNReal.ofNat_ne_top (e.symm x₀) r).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hmp_res := he.restrict_preimage_emb e.measurableEmbedding (ball x₀ r)
  exact (eLpNorm_comp_measurePreserving hb.locallyIntegrable.aestronglyMeasurable.restrict
    hmp_res).symm.trans_lt hpre

end CoordHelpers

variable [FiniteDimensional ℝ V]

section StrongTypeV

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Coifman–Rochberg–Weiss `Lᵖ` commutator theorem on an inner product space.** Let `V` be a
finite-dimensional real inner product space of dimension `n`, `1 ≤ s < p < ∞` (`1 < p`), and
`δ > 0`. Suppose `T : L²(V; E) →L[ℝ] L²(V; F)` is represented outside any compact set `s_c` by a
kernel `k` (`T h x = ∫ k x z (h z)` for a.e. `x ∉ s_c` whenever `h` vanishes a.e. off `s_c`)
satisfying the standard size and first-variable smoothness estimates:
- `‖k x y‖ ≤ C₀ dist x y ^ (-n)` for `x ≠ y`,
- `‖k x y - k x' y‖ ≤ C₁ dist x x' ^ δ dist y x' ^ (-(n + δ))` whenever `2 dist x x' < dist y x'`,

and suppose `‖T h‖_s ≤ A ‖h‖_s` and `‖T h‖_p ≤ A_p ‖h‖_p` for all `h ∈ L²(V; E)`. Then there is a
constant `C > 0`, depending only on `dim V`, `s`, `p`, `A`, `A_p`, `C₀`, `C₁`, and `δ`, such that
for every locally integrable `b : V → ℝ` with `bmoSeminorm b volume ≤ M` and every `f, g ∈ L²(V; E)`
with `g =ᵐ b • f`,

`eLpNorm (fun x => b x • T f x - T g x) p volume ≤ C * M * eLpNorm f p volume`. -/
theorem exists_eLpNorm_smul_sub_le_of_isCompact_of_norm_sub_le_mul_rpow {s : ℝ} {p : ℝ≥0∞}
    (hs : 1 ≤ s) (hsp : s < p.toReal) (hp : 1 < p) (hp_top : p ≠ ∞) (A A_p C₀ C₁ : ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 volume)
      {k : V → V → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (k x) volume) →
      (∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ))) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖k x y - k x' y‖ ≤ C₁ * (dist x x' ^ δ * dist y x' ^ (-(finrank ℝ V + δ)))) →
      (∀ (f : Lp E 2 (volume : Measure V)) (s_c : Set V), IsCompact s_c →
        (∀ᵐ x, x ∉ s_c → f x = 0) → ∀ᵐ x, x ∉ s_c → T f x = ∫ z, k x z (f z)) →
      (∀ h : Lp E 2 (volume : Measure V),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure V),
        eLpNorm (T h) p volume ≤ A_p * eLpNorm h p volume) →
      ∀ {b : V → ℝ} {M : ℝ≥0}, LocallyIntegrable b volume → bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure V)), g =ᵐ[volume] (fun x => b x • f x) →
        eLpNorm (fun x => b x • T f x - T g x) p volume ≤ C * M * eLpNorm f p volume := by
  rcases isEmpty_or_nonempty (Fin (finrank ℝ V)) with hι | hι
  · have hdim0 : finrank ℝ V = 0 := by
      by_contra hne; exact hι.false ⟨0, Nat.pos_of_ne_zero hne⟩
    have : Subsingleton V := Module.finrank_zero_iff.1 hdim0
    refine ⟨1, one_pos, fun T _ _ _ _ _ _ _ b M _ _ f g hg => ?_⟩
    have hb_const : b =ᵐ[volume] fun _ => b 0 :=
      Eventually.of_forall fun x => congrArg b (Subsingleton.elim x 0)
    rw [eLpNorm_smul_sub_eq_zero_of_ae_const T hb_const f g hg p]
    exact bot_le
  set bas := stdOrthonormalBasis ℝ V
  set e := ipCoord bas
  have he := measurePreserving_ipCoord bas
  set C₁' : ℝ≥0 := C₁ * NNReal.sqrt (Fintype.card (Fin (finrank ℝ V))) ^ δ +
    2 * C₀ * (2 * NNReal.sqrt (Fintype.card (Fin (finrank ℝ V)))) ^
      (Fintype.card (Fin (finrank ℝ V)) + δ)
  obtain ⟨C_pi, _, hC_pi⟩ :=
    exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow (ι := Fin (finrank ℝ V)) (E := E) (F := F)
      hs hsp hp hp_top A A_p C₁' hδ
  set R_bmo : ℝ≥0∞ := 2 *
    (ENNReal.ofReal (√(Fintype.card (Fin (finrank ℝ V))) ^ Fintype.card (Fin (finrank ℝ V))) *
      volume (ball (0 : V) 1) / volume (ball (0 : Fin (finrank ℝ V) → ℝ) 1))
  have hR_fin : R_bmo ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
      (measure_ball_pos _ _ one_pos).ne')
  set C_out : ℝ≥0 := C_pi * R_bmo.toNNReal + 1 with hC_out_def
  refine ⟨C_out, by rw [hC_out_def]; positivity,
    fun T k hkm hsize hsmooth hrep hTs hTp b M hb hM f g hg => ?_⟩
  have hKm' (x : Fin (finrank ℝ V) → ℝ) : AEStronglyMeasurable (fun z => k (e x) (e z)) volume :=
    (he.aestronglyMeasurable_comp_iff e.measurableEmbedding).2 (hkm (e x))
  have hsize_c : ∀ x y, x ≠ y →
      ‖k x y‖ ≤ C₀ * dist x y ^ (-(Fintype.card (Fin (finrank ℝ V)) : ℝ)) := by
    simpa only [Fintype.card_fin] using hsize
  have hsmooth_c : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖k x y - k x' y‖ ≤
        C₁ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card (Fin (finrank ℝ V)) + δ))) := by
    simpa only [Fintype.card_fin] using hsmooth
  have hb_bmo : bmoSeminorm (b ∘ e) volume ≤ (R_bmo.toNNReal * M : ℝ≥0) := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hR_fin]
    exact (bmoSeminorm_comp_ipCoord_le bas hb).trans (by gcongr)
  have hg' : (lpIpCoord bas E g : (Fin (finrank ℝ V) → ℝ) → E) =ᵐ[volume]
      fun y => (b ∘ e) y • lpIpCoord bas E f y := by
    filter_upwards [coeFn_lpIpCoord bas g, coeFn_lpIpCoord bas f,
      he.quasiMeasurePreserving.ae hg] with y hy₁ hy₂ hy₃
    rw [hy₁, hy₂, Function.comp_apply, Function.comp_apply, Function.comp_apply, hy₃]
  have hpi := hC_pi (ipCoordConj bas T) hKm'
    (fun x x' y h => norm_ipCoord_sub_first_le bas hδ.le hsize_c hsmooth_c h)
    (ipCoordConj_ae_eq_integral_ball bas T hkm hsize hrep)
    (eLpNorm_ipCoordConj_le bas T hTs) (eLpNorm_ipCoordConj_le bas T hTp)
    (locallyIntegrable_comp_ipCoord bas hb) hb_bmo (lpIpCoord bas E f) (lpIpCoord bas E g) hg'
  have hae_comm : (fun y => (b ∘ e) y • ipCoordConj bas T (lpIpCoord bas E f) y -
      ipCoordConj bas T (lpIpCoord bas E g) y) =ᵐ[volume]
      (fun x => b x • T f x - T g x) ∘ e := by
    rw [ipCoordConj_lpIpCoord, ipCoordConj_lpIpCoord]
    filter_upwards [coeFn_lpIpCoord bas (T f), coeFn_lpIpCoord bas (T g)] with y h₁ h₂
    rw [h₁, h₂]; rfl
  have hLHS : eLpNorm (fun x => b x • T f x - T g x) p volume =
      eLpNorm (fun y => (b ∘ e) y • ipCoordConj bas T (lpIpCoord bas E f) y -
        ipCoordConj bas T (lpIpCoord bas E g) y) p volume :=
    (eLpNorm_comp_measurePreserving
      ((hb.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (T f))).sub
        (Lp.aestronglyMeasurable (T g))) he).symm.trans (eLpNorm_congr_ae hae_comm.symm)
  rw [hLHS]
  refine hpi.trans ?_
  rw [eLpNorm_lpIpCoord]
  have hle : (C_pi : ℝ≥0∞) * (R_bmo.toNNReal * M : ℝ≥0) ≤ C_out * M := by
    rw [hC_out_def]; push_cast; rw [← mul_assoc]; gcongr; exact le_self_add
  exact mul_le_mul_left hle _

/-- **Bundled `Lᵖ` commutator operator on an inner product space.** Under the hypotheses of
`TauCeti.exists_eLpNorm_smul_sub_le_of_isCompact_of_norm_sub_le_mul_rpow`, for every
`b : V → ℝ` of bounded mean oscillation (`MemBMO b volume`) there exists a unique continuous linear
map `S : Lp E p volume →L[ℝ] Lp F p volume` agreeing a.e. with `x ↦ b x • T f x - T g x` whenever
`f ∈ L² ∩ Lᵖ` and `g ∈ L²` represents `b • f`, and satisfying `‖S‖ₑ ≤ C * bmoSeminorm b volume`. -/
theorem _root_.ContinuousLinearMap.exists_commutator_of_isCompact_of_norm_sub_le_mul_rpow
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hs : 1 ≤ s) (hsp : s < p.toReal) (hp : 1 < p)
    (hp_top : p ≠ ∞) (A A_p C₀ C₁ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 volume)
      {k : V → V → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (k x) volume) →
      (∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ))) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖k x y - k x' y‖ ≤ C₁ * (dist x x' ^ δ * dist y x' ^ (-(finrank ℝ V + δ)))) →
      (∀ (f : Lp E 2 (volume : Measure V)) (s_c : Set V), IsCompact s_c →
        (∀ᵐ x, x ∉ s_c → f x = 0) → ∀ᵐ x, x ∉ s_c → T f x = ∫ z, k x z (f z)) →
      (∀ h : Lp E 2 (volume : Measure V),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure V),
        eLpNorm (T h) p volume ≤ A_p * eLpNorm h p volume) →
      ∀ {b : V → ℝ}, MemBMO b volume →
        ∃ S : Lp E p (volume : Measure V) →L[ℝ] Lp F p volume,
          ‖S‖ₑ ≤ C * bmoSeminorm b volume ∧
          ∀ (f g : Lp E 2 (volume : Measure V)), g =ᵐ[volume] (fun x => b x • f x) →
            ∀ (hf : MemLp f p volume),
              (S (hf.toLp f) : V → F) =ᵐ[volume] fun x => b x • T f x - T g x := by
  obtain ⟨C, _, hC⟩ :=
    exists_eLpNorm_smul_sub_le_of_isCompact_of_norm_sub_le_mul_rpow (V := V) (E := E) (F := F)
      hs hsp hp hp_top A A_p C₀ C₁ hδ
  refine ⟨C, fun T k hkm hsize hsmooth hrep hTs hTp b hb => ?_⟩
  set M : ℝ≥0 := (bmoSeminorm b volume).toNNReal
  have hM : bmoSeminorm b volume ≤ M := (ENNReal.coe_toNNReal hb.bmoSeminorm_ne_top).ge
  have hM_eq : (M : ℝ≥0∞) = bmoSeminorm b volume := ENNReal.coe_toNNReal hb.bmoSeminorm_ne_top
  have hbound : ∀ (f g : Lp E 2 (volume : Measure V)), g =ᵐ[volume] (fun x => b x • f x) →
      MemLp f p volume →
        eLpNorm (fun x => b x • T f x - T g x) p volume ≤ (C * M : ℝ≥0) * eLpNorm f p volume :=
    fun f g hg _ => by
      push_cast
      exact hC T hkm hsize hsmooth hrep hTs hTp hb.locallyIntegrable hM f g hg
  have hdense := dense_lpTwoSmulSubmodule_of_memLp_restrict_ball (E := E) (p := p)
    (ν := (volume : Measure V)) hp_top (0 : V) fun N => memLp_restrict_ball_of_memBMO hb 0 N
  refine ⟨T.commutatorExtension b (C * M) hbound hdense, ?_,
    fun f g hg hf => T.commutatorExtension_apply_of_memLp b (C * M) hbound hdense f g hg hf⟩
  have hn := T.norm_commutatorExtension_le b (C * M) hbound hdense
  rw [← ofReal_norm, ← hM_eq, ← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hn

end StrongTypeV

section CalderonZygmundV

/-! ### Specialization to Hilbert-valued Calderón–Zygmund operators on `V` -/

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- **The Coifman–Rochberg–Weiss theorem for Calderón–Zygmund operators on an inner product space.**
Let `T : L²(V; H) →L[ℝ] L²(V; K)` be a bounded operator between Hilbert-valued `L²` spaces on a
finite-dimensional real inner product space `V` of dimension `n`. Suppose `T` and `adjoint T` are
represented off compact sets by kernels `k` and `k'`, where:
- `k` satisfies the standard size bound (`C₀`), second-variable smoothness (`C₂`, `δ`), and
  first-variable smoothness (`C₁`, `δ`), and
- `k'` satisfies the standard size bound (`C₀'`) and second-variable smoothness (`C₂'`, `δ'`).

Then for every `1 < p < ∞`, the Calderón–Zygmund strong-type theorem automatically supplies the
intermediate `Lˢ` (`s = (1 + p) / 2`) and `Lᵖ` bounds for `T`, yielding a constant `C > 0` such that
for every locally integrable `b : V → ℝ` with `bmoSeminorm b volume ≤ M` and every `f, g ∈ L²` with
`g =ᵐ b • f`,

`eLpNorm (fun x => b x • T f x - T g x) p volume ≤ C * M * eLpNorm f p volume`. -/
theorem _root_.ContinuousLinearMap.exists_eLpNorm_smul_sub_le_of_calderonZygmund
    (T : Lp H 2 (volume : Measure V) →L[ℝ] Lp K 2 (volume : Measure V))
    {k : V → V → H →L[ℝ] K} (hkm : StronglyMeasurable (Function.uncurry k))
    {k' : V → V → K →L[ℝ] H} (hk'm : StronglyMeasurable (Function.uncurry k'))
    {C₀ C₁ C₂ C₀' C₂' : ℝ≥0} {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ')
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hsize' : ∀ x y, x ≠ y → ‖k' x y‖ ≤ C₀' * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hsmooth₁ : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖k x y - k x' y‖ ≤ C₁ * (dist x x' ^ δ * dist y x' ^ (-(finrank ℝ V + δ))))
    (hsmooth₂ : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ C₂ * (dist y y' ^ δ * dist x y' ^ (-(finrank ℝ V + δ))))
    (hsmooth' : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k' x y - k' x y'‖ ≤ C₂' * (dist y y' ^ δ' * dist x y' ^ (-(finrank ℝ V + δ'))))
    (hrep : ∀ (f : Lp H 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z))
    (hrep' : ∀ (f : Lp K 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → adjoint T f x = ∫ z, k' x z (f z))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {b : V → ℝ} {M : ℝ≥0}, LocallyIntegrable b volume →
      bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp H 2 (volume : Measure V)), g =ᵐ[volume] (fun x => b x • f x) →
        eLpNorm (fun x => b x • T f x - T g x) p volume ≤ C * M * eLpNorm f p volume := by
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  set s := (1 + p.toReal) / 2 with hs_def
  have hs1 : 1 < s := by linarith
  have hsp : s < p.toReal := by linarith
  have hs_enn : 1 < ENNReal.ofReal s := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  obtain ⟨A_s, hTs⟩ := T.exists_eLpNorm_le_of_norm_sub_le_mul_rpow hkm hk'm hδ hδ' hsize hsize'
    hsmooth₂ hsmooth' hrep hrep' hs_enn ENNReal.ofReal_ne_top
  obtain ⟨A_p, hTp⟩ := T.exists_eLpNorm_le_of_norm_sub_le_mul_rpow hkm hk'm hδ hδ' hsize hsize'
    hsmooth₂ hsmooth' hrep hrep' hp hp_top
  obtain ⟨C, hCpos, hC⟩ :=
    exists_eLpNorm_smul_sub_le_of_isCompact_of_norm_sub_le_mul_rpow (V := V) (E := H) (F := K)
      hs1.le hsp hp hp_top A_s A_p C₀ C₁ hδ
  have hkm_x (x : V) : AEStronglyMeasurable (k x) volume :=
    (hkm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact ⟨C, hCpos, fun hb hM f g hg =>
    hC T hkm_x hsize hsmooth₁ hrep hTs hTp hb hM f g hg⟩

/-- **Bundled `Lᵖ` commutator for Calderón–Zygmund operators on an inner product space.** -/
theorem _root_.ContinuousLinearMap.exists_commutator_of_calderonZygmund
    (T : Lp H 2 (volume : Measure V) →L[ℝ] Lp K 2 (volume : Measure V))
    {k : V → V → H →L[ℝ] K} (hkm : StronglyMeasurable (Function.uncurry k))
    {k' : V → V → K →L[ℝ] H} (hk'm : StronglyMeasurable (Function.uncurry k'))
    {C₀ C₁ C₂ C₀' C₂' : ℝ≥0} {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ')
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hsize' : ∀ x y, x ≠ y → ‖k' x y‖ ≤ C₀' * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hsmooth₁ : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖k x y - k x' y‖ ≤ C₁ * (dist x x' ^ δ * dist y x' ^ (-(finrank ℝ V + δ))))
    (hsmooth₂ : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ C₂ * (dist y y' ^ δ * dist x y' ^ (-(finrank ℝ V + δ))))
    (hsmooth' : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k' x y - k' x y'‖ ≤ C₂' * (dist y y' ^ δ' * dist x y' ^ (-(finrank ℝ V + δ'))))
    (hrep : ∀ (f : Lp H 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z))
    (hrep' : ∀ (f : Lp K 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → adjoint T f x = ∫ z, k' x z (f z))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {b : V → ℝ}, MemBMO b volume →
      ∃ S : Lp H p (volume : Measure V) →L[ℝ] Lp K p volume,
        ‖S‖ₑ ≤ C * bmoSeminorm b volume ∧
        ∀ (f g : Lp H 2 (volume : Measure V)), g =ᵐ[volume] (fun x => b x • f x) →
          ∀ (hf : MemLp f p volume),
            (S (hf.toLp f) : V → K) =ᵐ[volume] fun x => b x • T f x - T g x := by
  obtain ⟨C, _, hC⟩ := T.exists_eLpNorm_smul_sub_le_of_calderonZygmund hkm hk'm hδ hδ'
    hsize hsize' hsmooth₁ hsmooth₂ hsmooth' hrep hrep' hp hp_top
  refine ⟨C, fun {b} hb => ?_⟩
  set M : ℝ≥0 := (bmoSeminorm b volume).toNNReal
  have hM : bmoSeminorm b volume ≤ M := (ENNReal.coe_toNNReal hb.bmoSeminorm_ne_top).ge
  have hM_eq : (M : ℝ≥0∞) = bmoSeminorm b volume := ENNReal.coe_toNNReal hb.bmoSeminorm_ne_top
  have hbound : ∀ (f g : Lp H 2 (volume : Measure V)), g =ᵐ[volume] (fun x => b x • f x) →
      MemLp f p volume →
        eLpNorm (fun x => b x • T f x - T g x) p volume ≤ (C * M : ℝ≥0) * eLpNorm f p volume :=
    fun f g hg _ => by
      push_cast
      exact hC hb.locallyIntegrable hM f g hg
  have hdense := dense_lpTwoSmulSubmodule_of_memLp_restrict_ball (E := H) (p := p)
    (ν := (volume : Measure V)) hp_top (0 : V) fun N => memLp_restrict_ball_of_memBMO hb 0 N
  refine ⟨T.commutatorExtension b (C * M) hbound hdense, ?_,
    fun f g hg hf => T.commutatorExtension_apply_of_memLp b (C * M) hbound hdense f g hg hf⟩
  have hn := T.norm_commutatorExtension_le b (C * M) hbound hdense
  rw [← ofReal_norm, ← hM_eq, ← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hn

end CalderonZygmundV

section LocalVMO

/-! ### Small-radius local commutator estimates controlled by the VMO modulus -/

section ExtendRestrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Zero-extension from a measurable subset `s ⊆ V` into the ambient `Lp E p volume` space, built
from `TauCeti.extendByZeroLpₗᵢ` and `TauCeti.castLpₗᵢ`. -/
private def extendRestrictToSpace {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set V} (hs : MeasurableSet s) :
    Lp E p ((volume : Measure V).restrict s) →L[ℝ] Lp E p (volume : Measure V) :=
  ((castLpₗᵢ (𝕜 := ℝ) Measure.restrict_univ).toLinearIsometry.comp
    (extendByZeroLpₗᵢ ℝ (volume : Measure V) hs (subset_univ s))).toContinuousLinearMap

private theorem coeFn_extendRestrictToSpace {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set V}
    (hs : MeasurableSet s) (f : Lp E p ((volume : Measure V).restrict s)) :
    (extendRestrictToSpace (E := E) hs f : V → E) =ᵐ[volume] s.indicator (f : V → E) := by
  have h : (extendByZeroLpₗᵢ ℝ (volume : Measure V) hs (subset_univ s) f : V → E) =ᵐ[volume]
      s.indicator (f : V → E) :=
    (coeFn_extendByZeroLpₗᵢ ℝ hs (subset_univ s) f).filter_mono
      (le_of_eq (congrArg ae Measure.restrict_univ.symm))
  exact h.mono fun x hx =>
    (coeFn_castLpₗᵢ (𝕜 := ℝ) Measure.restrict_univ
      (extendByZeroLpₗᵢ ℝ (volume : Measure V) hs (subset_univ s) f) x).trans hx

/-- Restricting `f ∈ Lp E p volume` supported in `s` to `s` and extending by zero recovers `f`. -/
private theorem extendRestrictToSpace_LpToLpRestrictCLM {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set V}
    (hs : MeasurableSet s) (f : Lp E p (volume : Measure V))
    (hsupp : ∀ᵐ x ∂volume, x ∉ s → f x = 0) :
    extendRestrictToSpace (E := E) hs (LpToLpRestrictCLM V E ℝ volume p s f) = f := by
  apply Lp.ext
  have hind := (ae_eq_restrict_iff_indicator_ae_eq hs).1 (LpToLpRestrictCLM_coeFn ℝ s f)
  filter_upwards [coeFn_extendRestrictToSpace (E := E) (p := p) hs _, hind, hsupp] with x hx₁ hx₂
    hx₃
  rw [hx₁, hx₂]
  by_cases hxs : x ∈ s
  · exact indicator_of_mem hxs _
  · rw [indicator_of_notMem hxs, hx₃ hxs]

end ExtendRestrict

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Small-radius local commutator inequality controlled by the VMO modulus.** Whenever `T`
satisfies the global `Lᵖ` commutator bound with constant `C_glob > 0`, for every ball `ball x₀ r`
(`r > 0`), every locally integrable `b : V → ℝ`, and every `f, g ∈ L²(V; E)` supported in
`ball x₀ r` (`∀ᵐ x, x ∉ ball x₀ r → f x = 0`) with `g =ᵐ b • f`,

`eLpNorm (fun x => b x • T f x - T g x) p (volume.restrict (ball x₀ r))`
`  ≤ (C_glob * bmoLocalizationConst (finrank ℝ V)) * vmoModulus b volume r`
`      * eLpNorm f p (volume.restrict (ball x₀ r))`.

In particular, when `b ∈ VMO`, `vmoModulus b volume r → 0` as `r → 0⁺` uniformly in `x₀`. -/
theorem eLpNorm_restrict_ball_smul_sub_le_mul_vmoModulus {p : ℝ≥0∞}
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 volume) {C_glob : ℝ≥0} (hC_pos : 0 < C_glob)
    (hglob : ∀ {b' : V → ℝ} {M : ℝ≥0}, LocallyIntegrable b' volume →
      bmoSeminorm b' volume ≤ M →
      ∀ (f' g' : Lp E 2 (volume : Measure V)), g' =ᵐ[volume] (fun x => b' x • f' x) →
        eLpNorm (fun x => b' x • T f' x - T g' x) p volume ≤ C_glob * M * eLpNorm f' p volume)
    {b : V → ℝ} (hb : LocallyIntegrable b volume) (x₀ : V) {r : ℝ} (hr : 0 < r)
    (f g : Lp E 2 (volume : Measure V)) (hsupp : ∀ᵐ x ∂volume, x ∉ ball x₀ r → f x = 0)
    (hg : g =ᵐ[volume] fun x => b x • f x) :
    eLpNorm (fun x => b x • T f x - T g x) p (volume.restrict (ball x₀ r)) ≤
      (C_glob * bmoLocalizationConst (finrank ℝ V) : ℝ≥0) * vmoModulus b volume r *
        eLpNorm f p (volume.restrict (ball x₀ r)) := by
  set C_loc : ℝ≥0 := C_glob * bmoLocalizationConst (finrank ℝ V)
  have hC_loc_pos : 0 < C_loc := mul_pos hC_pos (bmoLocalizationConst_pos _)
  have hf_eq : eLpNorm f p volume = eLpNorm f p (volume.restrict (ball x₀ r)) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet]
    refine eLpNorm_congr_ae (hsupp.mono fun x hx => ?_)
    by_cases hxB : x ∈ ball x₀ r
    · exact (indicator_of_mem hxB _).symm
    · rw [hx hxB, indicator_of_notMem hxB]
  rcases eq_or_ne (vmoModulus b volume r) ∞ with htop | hfin
  · rcases eq_or_ne p 0 with rfl | hp0
    · exact (eLpNorm_exponent_zero (f := fun x => b x • T f x - T g x)
        ((hb.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (T f))).sub
          (Lp.aestronglyMeasurable (T g))).restrict).trans_le bot_le
    rcases eq_or_ne (eLpNorm f p (volume.restrict (ball x₀ r))) 0 with hf0 | hf0
    · have hf_ae0 : (f : V → E) =ᵐ[volume] 0 := (eLpNorm_eq_zero_iff hp0).1 (hf_eq.trans hf0)
      have hf_zero : f = 0 := Lp.ext (hf_ae0.trans (Lp.coeFn_zero E 2 volume).symm)
      have hg_zero : g = 0 := by
        apply Lp.ext
        filter_upwards [hg, hf_ae0, Lp.coeFn_zero E 2 volume] with x hxg hxf hxz
        rw [hxg, hxf, hxz, Pi.zero_apply, smul_zero]
      have hcomm0 : (fun x => b x • T f x - T g x) =ᵐ[volume.restrict (ball x₀ r)] (0 : V → F) := by
        rw [hf_zero, hg_zero, map_zero]
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_zero F 2 volume)] with x hx
        rw [hx, Pi.zero_apply, smul_zero, sub_self]
      rw [eLpNorm_congr_ae hcomm0, eLpNorm_zero]
      exact bot_le
    · rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hC_loc_pos.ne'), ENNReal.top_mul hf0]
      exact le_top
  obtain ⟨b_loc, hb_loc_int, hb_eq, hb_bmo⟩ := exists_eqOn_closedBall_bmoSeminorm_le hb x₀ hr
  set η : ℝ≥0 := (vmoModulus b volume r).toNNReal
  have hη_eq : (η : ℝ≥0∞) = vmoModulus b volume r := ENNReal.coe_toNNReal hfin
  have hb_loc_le : bmoSeminorm b_loc volume ≤ (bmoLocalizationConst (finrank ℝ V) * η : ℝ≥0) := by
    rw [ENNReal.coe_mul, hη_eq]; exact hb_bmo
  have hg_loc : g =ᵐ[volume] fun x => b_loc x • f x := by
    filter_upwards [hg, hsupp] with x hxg hxf
    rw [hxg]
    by_cases hxB : x ∈ ball x₀ r
    · rw [hb_eq (ball_subset_closedBall hxB)]
    · rw [hxf hxB, smul_zero, smul_zero]
  have hae_ball : (fun x => b x • T f x - T g x) =ᵐ[volume.restrict (ball x₀ r)]
      fun x => b_loc x • T f x - T g x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hxB
    rw [hb_eq (ball_subset_closedBall hxB)]
  calc eLpNorm (fun x => b x • T f x - T g x) p (volume.restrict (ball x₀ r))
      = eLpNorm (fun x => b_loc x • T f x - T g x) p (volume.restrict (ball x₀ r)) :=
        eLpNorm_congr_ae hae_ball
    _ ≤ eLpNorm (fun x => b_loc x • T f x - T g x) p volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ C_glob * (bmoLocalizationConst (finrank ℝ V) * η : ℝ≥0) * eLpNorm f p volume :=
        hglob hb_loc_int hb_loc_le f g hg_loc
    _ = C_loc * vmoModulus b volume r * eLpNorm f p (volume.restrict (ball x₀ r)) := by
        rw [hf_eq, ← hη_eq]; simp only [C_loc, ENNReal.coe_mul]; ring

/-- **Small-radius local commutator theorem for Calderón–Zygmund operators (`eLpNorm` form).** -/
theorem exists_eLpNorm_restrict_ball_smul_sub_le_mul_vmoModulus
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (T : Lp H 2 (volume : Measure V) →L[ℝ] Lp K 2 (volume : Measure V))
    {k : V → V → H →L[ℝ] K} (hkm : StronglyMeasurable (Function.uncurry k))
    {k' : V → V → K →L[ℝ] H} (hk'm : StronglyMeasurable (Function.uncurry k'))
    {C₀ C₁ C₂ C₀' C₂' : ℝ≥0} {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ')
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hsize' : ∀ x y, x ≠ y → ‖k' x y‖ ≤ C₀' * dist x y ^ (-(finrank ℝ V : ℝ)))
    (hsmooth₁ : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖k x y - k x' y‖ ≤ C₁ * (dist x x' ^ δ * dist y x' ^ (-(finrank ℝ V + δ))))
    (hsmooth₂ : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ C₂ * (dist y y' ^ δ * dist x y' ^ (-(finrank ℝ V + δ))))
    (hsmooth' : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k' x y - k' x y'‖ ≤ C₂' * (dist y y' ^ δ' * dist x y' ^ (-(finrank ℝ V + δ'))))
    (hrep : ∀ (f : Lp H 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z))
    (hrep' : ∀ (f : Lp K 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → adjoint T f x = ∫ z, k' x z (f z))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {b : V → ℝ}, LocallyIntegrable b volume →
      ∀ (x₀ : V) {r : ℝ}, 0 < r →
      ∀ (f g : Lp H 2 (volume : Measure V)), (∀ᵐ x ∂volume, x ∉ ball x₀ r → f x = 0) →
        g =ᵐ[volume] (fun x => b x • f x) →
        eLpNorm (fun x => b x • T f x - T g x) p (volume.restrict (ball x₀ r)) ≤
          C * vmoModulus b volume r * eLpNorm f p (volume.restrict (ball x₀ r)) := by
  obtain ⟨C_glob, hC_pos, hglob⟩ := T.exists_eLpNorm_smul_sub_le_of_calderonZygmund hkm hk'm
    hδ hδ' hsize hsize' hsmooth₁ hsmooth₂ hsmooth' hrep hrep' hp hp_top
  exact ⟨C_glob * bmoLocalizationConst (finrank ℝ V),
    fun hb x₀ _ hr f g hsupp hg =>
      eLpNorm_restrict_ball_smul_sub_le_mul_vmoModulus T hC_pos hglob hb x₀ hr f g hsupp hg⟩

variable [CompleteSpace F]

/-- **Bundled local commutator operator on `Lp E p (volume.restrict (ball x₀ r))`.** Given a global
`Lᵖ` commutator bound (`1 < p < ∞`) with constant `C_glob > 0`, for every `x₀ : V`, `r > 0`, and
locally integrable `b : V → ℝ` with `vmoModulus b volume r ≤ η` (`η : ℝ≥0`), there is a continuous
linear map `S` on `Lp` over `volume.restrict (ball x₀ r)`
of norm at most `(C_glob * bmoLocalizationConst (finrank ℝ V)) * η` that agrees a.e. on
`ball x₀ r` with `x ↦ b x • T f x - T g x` for every `f, g ∈ L²(V; E)` supported in `ball x₀ r`
with `g =ᵐ b • f`. -/
theorem _root_.ContinuousLinearMap.exists_restrict_ball_commutator_of_vmoModulus_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 volume) {C_glob : ℝ≥0} (hC_pos : 0 < C_glob)
    (hglob : ∀ {b' : V → ℝ} {M : ℝ≥0}, LocallyIntegrable b' volume →
      bmoSeminorm b' volume ≤ M →
      ∀ (f' g' : Lp E 2 (volume : Measure V)), g' =ᵐ[volume] (fun x => b' x • f' x) →
        eLpNorm (fun x => b' x • T f' x - T g' x) p volume ≤ C_glob * M * eLpNorm f' p volume)
    {b : V → ℝ} (hb : LocallyIntegrable b volume) (x₀ : V) {r : ℝ} (hr : 0 < r) {η : ℝ≥0}
    (hη : vmoModulus b volume r ≤ η) :
    ∃ S : Lp E p ((volume : Measure V).restrict (ball x₀ r)) →L[ℝ]
        Lp F p ((volume : Measure V).restrict (ball x₀ r)),
      ‖S‖ ≤ (C_glob * bmoLocalizationConst (finrank ℝ V) : ℝ≥0) * η ∧
      ∀ (f g : Lp E 2 (volume : Measure V)),
        (∀ᵐ x ∂volume, x ∉ ball x₀ r → f x = 0) →
        g =ᵐ[volume] (fun x => b x • f x) →
        ∀ (hf : MemLp f p (volume.restrict (ball x₀ r))),
          (S (hf.toLp f) : V → F) =ᵐ[volume.restrict (ball x₀ r)]
            fun x => b x • T f x - T g x := by
  set ν := (volume : Measure V).restrict (ball x₀ r)
  set T_ball : Lp E 2 ν →L[ℝ] Lp F 2 ν :=
    (LpToLpRestrictCLM V F ℝ volume 2 (ball x₀ r)) ∘L T ∘L
      extendRestrictToSpace (E := E) measurableSet_ball
  have hT_ball_apply (u : Lp E 2 ν) :
      T_ball u = LpToLpRestrictCLM V F ℝ volume 2 (ball x₀ r)
        (T (extendRestrictToSpace (E := E) measurableSet_ball u)) := rfl
  set C_loc : ℝ≥0 := C_glob * bmoLocalizationConst (finrank ℝ V)
  obtain ⟨b_loc, hb_loc_int, hb_eq, hb_loc_bmo⟩ := exists_eqOn_closedBall_bmoSeminorm_le hb x₀ hr
  have hb_loc_mem : MemBMO b_loc volume := memBMO_iff.2 ⟨hb_loc_int,
    hb_loc_bmo.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (hη.trans_lt ENNReal.coe_lt_top))⟩
  have hb2 : MemLp b 2 ν := (memLp_restrict_ball_of_memBMO hb_loc_mem x₀ r).ae_eq
    ((ae_restrict_mem measurableSet_ball).mono fun x hx => hb_eq (ball_subset_closedBall hx))
  have hdense : Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := ν) b : Set (Lp E p ν)) :=
    dense_lpTwoSmulSubmodule_of_iUnion_eq_univ (E := E) (p := p) hp_top
      (monotone_const : Monotone fun _ : ℕ => (univ : Set V))
      (fun _ => MeasurableSet.univ) (iUnion_const univ)
      (fun _ => by simpa [Measure.restrict_univ] using hb2)
  have hbound : ∀ (f₀ g₀ : Lp E 2 ν), g₀ =ᵐ[ν] (fun x => b x • f₀ x) → MemLp f₀ p ν →
      eLpNorm (fun x => b x • T_ball f₀ x - T_ball g₀ x) p ν ≤
        (C_loc * η : ℝ≥0) * eLpNorm f₀ p ν := by
    intro f₀ g₀ hg₀ _
    set f := extendRestrictToSpace (E := E) (s := ball x₀ r) measurableSet_ball f₀
    set g := extendRestrictToSpace (E := E) (s := ball x₀ r) measurableSet_ball g₀
    have hf_coe := coeFn_extendRestrictToSpace (E := E) (s := ball x₀ r) measurableSet_ball f₀
    have hg_coe := coeFn_extendRestrictToSpace (E := E) (s := ball x₀ r) measurableSet_ball g₀
    have hsupp : ∀ᵐ x ∂volume, x ∉ ball x₀ r → f x = 0 :=
      hf_coe.mono fun x hx hxB => hx.trans (indicator_of_notMem hxB _)
    have hg_ae : g =ᵐ[volume] fun x => b x • f x := by
      filter_upwards [hg_coe, hf_coe, (ae_eq_restrict_iff_indicator_ae_eq measurableSet_ball).1 hg₀]
        with x hx₁ hx₂ hx₃
      rw [hx₁, hx₃, hx₂]
      by_cases hxB : x ∈ ball x₀ r <;> simp [hxB]
    have hae_comm : (fun x => b x • T_ball f₀ x - T_ball g₀ x) =ᵐ[ν]
        fun x => b x • T f x - T g x := by
      filter_upwards [LpToLpRestrictCLM_coeFn ℝ (ball x₀ r) (T f),
        LpToLpRestrictCLM_coeFn ℝ (ball x₀ r) (T g)] with x h₁ h₂
      rw [hT_ball_apply f₀, hT_ball_apply g₀, h₁, h₂]
    have hf_norm : eLpNorm f p ν = eLpNorm f₀ p ν := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hf_coe, ae_restrict_mem measurableSet_ball] with x hx hxB
      rw [hx, indicator_of_mem hxB]
    rw [eLpNorm_congr_ae hae_comm, ← hf_norm]
    refine (eLpNorm_restrict_ball_smul_sub_le_mul_vmoModulus T hC_pos hglob hb x₀ hr f g hsupp
      hg_ae).trans ?_
    dsimp only [C_loc]; push_cast; gcongr
  refine ⟨T_ball.commutatorExtension b (C_loc * η) hbound hdense,
    T_ball.norm_commutatorExtension_le b (C_loc * η) hbound hdense,
    fun f g hsupp hg hf => ?_⟩
  set f₀ : Lp E 2 ν := LpToLpRestrictCLM V E ℝ volume 2 (ball x₀ r) f
  set g₀ : Lp E 2 ν := LpToLpRestrictCLM V E ℝ volume 2 (ball x₀ r) g
  have hf_res := LpToLpRestrictCLM_coeFn ℝ (ball x₀ r) f
  have hg_res := LpToLpRestrictCLM_coeFn ℝ (ball x₀ r) g
  have hg₀ : g₀ =ᵐ[ν] fun x => b x • f₀ x := by
    filter_upwards [hg_res, hf_res, ae_restrict_of_ae hg] with x hx₁ hx₂ hx₃
    rw [hx₁, hx₃, hx₂]
  have hf₀ : MemLp f₀ p ν := hf.ae_eq hf_res.symm
  have htoLp : hf.toLp f = hf₀.toLp f₀ := MemLp.toLp_congr hf hf₀ hf_res.symm
  have hg_supp : ∀ᵐ x ∂volume, x ∉ ball x₀ r → g x = 0 := by
    filter_upwards [hg, hsupp] with x hxg hxf hxB
    rw [hxg, hxf hxB, smul_zero]
  have hTf : T_ball f₀ =ᵐ[ν] T f := by
    rw [hT_ball_apply f₀, extendRestrictToSpace_LpToLpRestrictCLM measurableSet_ball f hsupp]
    exact LpToLpRestrictCLM_coeFn ℝ (ball x₀ r) (T f)
  have hTg : T_ball g₀ =ᵐ[ν] T g := by
    rw [hT_ball_apply g₀, extendRestrictToSpace_LpToLpRestrictCLM measurableSet_ball g hg_supp]
    exact LpToLpRestrictCLM_coeFn ℝ (ball x₀ r) (T g)
  rw [htoLp]
  have hcomm_f₀ := T_ball.commutatorExtension_apply_of_memLp b (C_loc * η) hbound hdense f₀ g₀ hg₀
    hf₀
  filter_upwards [hcomm_f₀, hTf, hTg] with x hx₁ hx₂ hx₃
  rw [hx₁, hx₂, hx₃]

/-- **Arbitrarily small local `Lᵖ` commutator norm for VMO multipliers.** When `b ∈ VMO` and `T`
satisfies the global `Lᵖ` commutator bound (`1 < p < ∞`), for every `ε > 0` there exists a uniform
radius `r₀ > 0` such that on every ball `ball x₀ r` (`0 < r ≤ r₀`), the local commutator operator
has operator norm at most `ε`. -/
theorem _root_.ContinuousLinearMap.exists_restrict_ball_commutator_norm_le_of_memVMO
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 volume) {C_glob : ℝ≥0} (hC_pos : 0 < C_glob)
    (hglob : ∀ {b' : V → ℝ} {M : ℝ≥0}, LocallyIntegrable b' volume →
      bmoSeminorm b' volume ≤ M →
      ∀ (f' g' : Lp E 2 (volume : Measure V)), g' =ᵐ[volume] (fun x => b' x • f' x) →
        eLpNorm (fun x => b' x • T f' x - T g' x) p volume ≤ C_glob * M * eLpNorm f' p volume)
    {b : V → ℝ} (hb : MemVMO b volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ > 0, ∀ (x₀ : V) {r : ℝ}, 0 < r → r ≤ r₀ →
      ∃ S : Lp E p ((volume : Measure V).restrict (ball x₀ r)) →L[ℝ]
          Lp F p ((volume : Measure V).restrict (ball x₀ r)),
        ‖S‖ ≤ ε ∧
        ∀ (f g : Lp E 2 (volume : Measure V)),
          (∀ᵐ x ∂volume, x ∉ ball x₀ r → f x = 0) →
          g =ᵐ[volume] (fun x => b x • f x) →
          ∀ (hf : MemLp f p (volume.restrict (ball x₀ r))),
            (S (hf.toLp f) : V → F) =ᵐ[volume.restrict (ball x₀ r)]
              fun x => b x • T f x - T g x := by
  set C_loc : ℝ≥0 := C_glob * bmoLocalizationConst (finrank ℝ V)
  have hC_loc_pos : 0 < (C_loc : ℝ) :=
    NNReal.coe_pos.2 (mul_pos hC_pos (bmoLocalizationConst_pos _))
  set η : ℝ≥0 := Real.toNNReal (ε / C_loc)
  have hη_pos : 0 < (η : ℝ≥0∞) := by
    rw [ENNReal.coe_pos, Real.toNNReal_pos]; positivity
  obtain ⟨r₀, hr₀, hmod⟩ := (memVMO_iff.1 hb).2 η hη_pos
  refine ⟨r₀, hr₀, fun x₀ r hr hrr₀ => ?_⟩
  have hη_r : vmoModulus b volume r ≤ η := (monotone_vmoModulus b volume hrr₀).trans hmod
  obtain ⟨S, hS_norm, hS_ae⟩ := T.exists_restrict_ball_commutator_of_vmoModulus_le hp_top
    hC_pos hglob hb.memBMO.locallyIntegrable x₀ hr hη_r
  refine ⟨S, hS_norm.trans_eq ?_, hS_ae⟩
  calc ((C_loc * η : ℝ≥0) : ℝ) = (C_loc : ℝ) * (ε / C_loc) := by
        rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    _ = ε := mul_div_cancel₀ ε hC_loc_pos.ne'

end LocalVMO

end InnerProductSpace

end TauCeti

end
