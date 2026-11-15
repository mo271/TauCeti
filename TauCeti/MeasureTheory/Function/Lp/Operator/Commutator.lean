/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Extending a commutator `[b, T]` from `{f ∈ Lᵖ ∩ L² | b • f ∈ L²}` to `Lᵖ`

Given a bounded operator `T : L²(μ; E) →L[ℝ] L²(μ; F)` and a scalar symbol `b : α → ℝ`, the
pointwise commutator `x ↦ b x • T f x - T (b • f) x` is well-defined whenever both `f` and
`b • f` belong to `L²(μ; E)`. In `Lᵖ(μ; E)` (`1 ≤ p < ∞`), such functions form a submodule
`MeasureTheory.lpTwoSmulSubmodule b`. Whenever the space is exhausted by an increasing sequence of
measurable sets on each of which `b` is square-integrable—for instance, metric balls when `b` has
bounded mean oscillation on `ℝⁿ`—truncating finite-measure indicator functions shows that
`lpTwoSmulSubmodule b` is dense in `Lᵖ(μ; E)`
(`MeasureTheory.dense_lpTwoSmulSubmodule_of_iUnion_eq_univ`,
`MeasureTheory.dense_lpTwoSmulSubmodule_of_memLp_restrict_ball`).

Consequently, a uniform `Lᵖ` commutator bound
`eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ` for `f, g ∈ L²` with `g =ᵐ b • f`
produces a unique continuous linear operator `ContinuousLinearMap.commutatorExtension : Lᵖ →L[ℝ] Lᵖ`
of norm at most `C` agreeing a.e. with `b • T f - T (b • f)` on the dense submodule.

## Main declarations

* `MeasureTheory.lpTwoSmulSubmodule`: the submodule `{f ∈ Lᵖ | f ∈ L² ∧ b • f ∈ L²}` of `Lp E p μ`,
  together with its `L²` projections `toL2` and `smulToL2`.
* `MeasureTheory.dense_lpTwoSmulSubmodule_of_iUnion_eq_univ` and
  `MeasureTheory.dense_lpTwoSmulSubmodule_of_memLp_restrict_ball`: density of
  `lpTwoSmulSubmodule b` in `Lp E p μ` (`1 ≤ p < ∞`) when `b` is locally in `L²`.
* `ContinuousLinearMap.commutatorOnIntersection`: the commutator `[b, T]` as a linear map on
  `lpTwoSmulSubmodule b` with values in `Lp F p μ`.
* `ContinuousLinearMap.commutatorExtension`: the unique continuous linear extension
  `Lp E p μ →L[ℝ] Lp F p μ`, with norm bound `norm_commutatorExtension_le`, evaluation lemma
  `commutatorExtension_apply_of_memLp`, and uniqueness `commutatorExtension_unique_of_ae`.

## References

* R. R. Coifman, R. Rochberg, and G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. (2) **103** (1976), 611–635.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., §3.5.
-/

public section

noncomputable section

namespace MeasureTheory

open Filter Set
open scoped ENNReal NNReal Topology

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞}

/-- The submodule of `Lp E p μ` consisting of functions `f` such that both `f` and `b • f` also
belong to `L²(μ; E)`. -/
def lpTwoSmulSubmodule (b : α → ℝ) : Submodule ℝ (Lp E p μ) where
  carrier := {f | MemLp (f : α → E) 2 μ ∧ MemLp (fun x => b x • (f : α → E) x) 2 μ}
  zero_mem' := by
    refine ⟨(MemLp.zero : MemLp (0 : α → E) 2 μ).ae_eq (Lp.coeFn_zero E p μ).symm, ?_⟩
    refine (MemLp.zero : MemLp (0 : α → E) 2 μ).ae_eq ?_
    filter_upwards [Lp.coeFn_zero E p μ] with x hx
    rw [hx, Pi.zero_apply, smul_zero]
  add_mem' := by
    intro f g hf hg
    refine ⟨(hf.1.add hg.1).ae_eq (Lp.coeFn_add f g).symm, ?_⟩
    refine (hf.2.add hg.2).ae_eq ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, smul_add]
  smul_mem' := by
    intro c f hf
    refine ⟨(hf.1.const_smul c).ae_eq (Lp.coeFn_smul c f).symm, ?_⟩
    refine (hf.2.const_smul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx, Pi.smul_apply, Pi.smul_apply, smul_comm]

theorem mem_lpTwoSmulSubmodule (b : α → ℝ) (f : Lp E p μ) :
    f ∈ lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b ↔
      MemLp (f : α → E) 2 μ ∧ MemLp (fun x => b x • (f : α → E) x) 2 μ :=
  Iff.rfl

/-- The `L²` membership proof for `f` carried by `f ∈ lpTwoSmulSubmodule b`. -/
theorem lpTwoSmulSubmodule.memLp {b : α → ℝ}
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    MemLp (f.1 : α → E) 2 μ :=
  f.2.1

/-- The `L²` membership proof for `b • f` carried by `f ∈ lpTwoSmulSubmodule b`. -/
theorem lpTwoSmulSubmodule.memLp_smul {b : α → ℝ}
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    MemLp (fun x => b x • (f.1 : α → E) x) 2 μ :=
  f.2.2

/-- Inclusion of `lpTwoSmulSubmodule b` into `Lp E 2 μ`. -/
def lpTwoSmulSubmodule.toL2 {b : α → ℝ} :
    lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b →ₗ[ℝ] Lp E 2 μ where
  toFun f := (lpTwoSmulSubmodule.memLp f).toLp (f.1 : α → E)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(lpTwoSmulSubmodule.memLp (f + g)).coeFn_toLp,
      (lpTwoSmulSubmodule.memLp f).coeFn_toLp, (lpTwoSmulSubmodule.memLp g).coeFn_toLp,
      Lp.coeFn_add f.1 g.1,
      Lp.coeFn_add ((lpTwoSmulSubmodule.memLp f).toLp _)
        ((lpTwoSmulSubmodule.memLp g).toLp _)] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Submodule.coe_add, h₄, h₅, Pi.add_apply, Pi.add_apply, h₂, h₃]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(lpTwoSmulSubmodule.memLp (c • f)).coeFn_toLp,
      (lpTwoSmulSubmodule.memLp f).coeFn_toLp, Lp.coeFn_smul c f.1,
      Lp.coeFn_smul c ((lpTwoSmulSubmodule.memLp f).toLp _)] with x h₁ h₂ h₃ h₄
    rw [h₁, Submodule.coe_smul, h₃, RingHom.id_apply, h₄, Pi.smul_apply, Pi.smul_apply, h₂]

theorem lpTwoSmulSubmodule.toL2_ae {b : α → ℝ}
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    (lpTwoSmulSubmodule.toL2 f : α → E) =ᵐ[μ] (f.1 : α → E) :=
  (lpTwoSmulSubmodule.memLp f).coeFn_toLp

/-- The multiplication map `f ↦ b • f` from `lpTwoSmulSubmodule b` into `Lp E 2 μ`. -/
def lpTwoSmulSubmodule.smulToL2 {b : α → ℝ} :
    lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b →ₗ[ℝ] Lp E 2 μ where
  toFun f := (lpTwoSmulSubmodule.memLp_smul f).toLp (fun x => b x • (f.1 : α → E) x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(lpTwoSmulSubmodule.memLp_smul (f + g)).coeFn_toLp,
      (lpTwoSmulSubmodule.memLp_smul f).coeFn_toLp, (lpTwoSmulSubmodule.memLp_smul g).coeFn_toLp,
      Lp.coeFn_add f.1 g.1,
      Lp.coeFn_add ((lpTwoSmulSubmodule.memLp_smul f).toLp _)
        ((lpTwoSmulSubmodule.memLp_smul g).toLp _)] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Submodule.coe_add, h₄, h₅, Pi.add_apply, Pi.add_apply, smul_add, h₂, h₃]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(lpTwoSmulSubmodule.memLp_smul (c • f)).coeFn_toLp,
      (lpTwoSmulSubmodule.memLp_smul f).coeFn_toLp, Lp.coeFn_smul c f.1,
      Lp.coeFn_smul c ((lpTwoSmulSubmodule.memLp_smul f).toLp _)] with x h₁ h₂ h₃ h₄
    rw [h₁, Submodule.coe_smul, h₃, RingHom.id_apply, h₄, Pi.smul_apply, Pi.smul_apply, smul_comm,
      h₂]

theorem lpTwoSmulSubmodule.smulToL2_ae {b : α → ℝ}
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    (lpTwoSmulSubmodule.smulToL2 f : α → E) =ᵐ[μ] fun x => b x • (f.1 : α → E) x :=
  (lpTwoSmulSubmodule.memLp_smul f).coeFn_toLp

section Density

/-- Truncating `indicatorConstLp p hs hμs c` to a set `K` where `b ∈ L²(μ.restrict K)` produces an
element of `lpTwoSmulSubmodule b`. -/
private theorem indicatorConstLp_inter_mem_lpTwoSmulSubmodule {b : α → ℝ} {s K : Set α}
    (hs : MeasurableSet s) (hK : MeasurableSet K) (hμs : μ s ≠ ∞)
    (hbK : MemLp b 2 (μ.restrict K)) (c : E) :
    indicatorConstLp p (hs.inter hK) ((measure_mono inter_subset_left).trans_lt hμs.lt_top).ne c ∈
      lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b := by
  have hμsK : μ (s ∩ K) ≠ ∞ := ((measure_mono inter_subset_left).trans_lt hμs.lt_top).ne
  have hcoe := indicatorConstLp_coeFn (p := p) (hs := hs.inter hK) (hμs := hμsK) (c := c)
  refine ⟨(memLp_indicator_const 2 (hs.inter hK).nullMeasurableSet c (.inr hμsK)).ae_eq hcoe.symm,
    ?_⟩
  have hbsmul : MemLp (fun x => b x • c) 2 (μ.restrict (s ∩ K)) :=
    (((ContinuousLinearMap.id ℝ ℝ).smulRight c).comp_memLp' hbK).mono_measure
      (Measure.restrict_mono inter_subset_right le_rfl)
  have hind : MemLp ((s ∩ K).indicator fun x => b x • c) 2 μ :=
    (memLp_indicator_iff_restrict (hs.inter hK).nullMeasurableSet).2 hbsmul
  refine hind.ae_eq ?_
  filter_upwards [hcoe] with x hx
  rw [hx]
  by_cases hxK : x ∈ s ∩ K <;> simp [hxK]

variable [Fact (1 ≤ p)]

omit [NormedSpace ℝ E] in
/-- Approximating `indicatorConstLp p hs hμs c` in `Lp E p μ` along an exhausting monotone sequence
of measurable sets `K N`. -/
private theorem tendsto_indicatorConstLp_inter_of_iUnion_eq_univ (hp : p ≠ ∞) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {K : ℕ → Set α} (hKmono : Monotone K)
    (hKm : ∀ N, MeasurableSet (K N)) (hKu : ⋃ N, K N = univ) (c : E) :
    Tendsto (fun N => indicatorConstLp p (hs.inter (hKm N))
      ((measure_mono inter_subset_left).trans_lt hμs.lt_top).ne c)
      atTop (𝓝 (indicatorConstLp p hs hμs c)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmeas : Tendsto (fun N => μ (s \ K N)) atTop (𝓝 0) := by
    have hanti : Antitone (fun N => s \ K N) := fun i j hij => sdiff_subset_sdiff_right (hKmono hij)
    have hiInter : (⋂ N, s \ K N) = ∅ := by
      rw [← sdiff_iUnion, hKu, sdiff_univ]
    have h := tendsto_measure_iInter_atTop
      (fun N => (hs.diff (hKm N)).nullMeasurableSet) hanti
      ⟨0, ((measure_mono sdiff_subset).trans_lt hμs.lt_top).ne⟩
    rwa [hiInter, measure_empty] at h
  have hnorm (N : ℕ) :
      ‖indicatorConstLp p (hs.inter (hKm N))
          ((measure_mono inter_subset_left).trans_lt hμs.lt_top).ne c -
        indicatorConstLp p hs hμs c‖ =
        ‖c‖ * (μ (s \ K N)).toReal ^ p.toReal⁻¹ := by
    rw [norm_sub_rev]
    have hμsK : μ (s ∩ K N) ≠ ∞ := ((measure_mono inter_subset_left).trans_lt hμs.lt_top).ne
    have hae : ((indicatorConstLp p hs hμs c -
        indicatorConstLp p (hs.inter (hKm N)) hμsK c : Lp E p μ) : α → E) =ᵐ[μ]
          (s \ K N).indicator (fun _ => c) := by
      filter_upwards [Lp.coeFn_sub (indicatorConstLp p hs hμs c)
        (indicatorConstLp p (hs.inter (hKm N)) hμsK c),
        indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c),
        indicatorConstLp_coeFn (p := p) (hs := hs.inter (hKm N)) (hμs := hμsK) (c := c)]
        with x h₁ h₂ h₃
      rw [h₁, Pi.sub_apply, h₂, h₃]
      by_cases hxs : x ∈ s <;> by_cases hxK : x ∈ K N <;> simp [hxs, hxK]
    rw [Lp.norm_def, eLpNorm_congr_ae hae,
      eLpNorm_indicator_const (hs.diff (hKm N)).nullMeasurableSet hp0 hp,
      ENNReal.toReal_mul, toReal_eNorm, ← ENNReal.toReal_rpow, one_div]
  simp_rw [hnorm]
  have htoReal : Tendsto (fun N => (μ (s \ K N)).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeas
  have hrpow : Tendsto (fun N => (μ (s \ K N)).toReal ^ p.toReal⁻¹) atTop (𝓝 0) := by
    have hc := ((Real.continuous_rpow_const (inv_nonneg.2 hp_pos.le)).tendsto 0).comp htoReal
    rwa [Real.zero_rpow (inv_pos.2 hp_pos).ne'] at hc
  have hmul := hrpow.const_mul ‖c‖
  rwa [mul_zero] at hmul

/-- **Density of `lpTwoSmulSubmodule b` in `Lᵖ`.** If `1 ≤ p < ∞` and the space is exhausted by a
monotone sequence of measurable sets `K N` on each of which `b` belongs to `L²`, then
`{f ∈ Lᵖ ∩ L² | b • f ∈ L²}` is dense in `Lp E p μ`. -/
theorem dense_lpTwoSmulSubmodule_of_iUnion_eq_univ {b : α → ℝ} (hp : p ≠ ∞) {K : ℕ → Set α}
    (hKmono : Monotone K) (hKm : ∀ N, MeasurableSet (K N)) (hKu : ⋃ N, K N = univ)
    (hbK : ∀ N, MemLp b 2 (μ.restrict (K N))) :
    Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b : Set (Lp E p μ)) := by
  set S := (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b : Set (Lp E p μ))
  have hsf : (Lp.simpleFunc E p μ : Set (Lp E p μ)) ⊆ closure S := by
    intro f hf
    have hmem : ((⟨f, hf⟩ : Lp.simpleFunc E p μ) : Lp E p μ) ∈ closure S := by
      refine Lp.simpleFunc.induction (by exact (zero_lt_one.trans_le Fact.out).ne') hp ?_ ?_ ⟨f, hf⟩
      · intro c s hs hμs
        simpa only [Lp.simpleFunc.coe_indicatorConst] using mem_closure_of_tendsto
          (tendsto_indicatorConstLp_inter_of_iUnion_eq_univ hp hs hμs.ne hKmono hKm hKu c)
          (Eventually.of_forall fun N =>
            indicatorConstLp_inter_mem_lpTwoSmulSubmodule hs (hKm N) hμs.ne (hbK N) c)
      · intro g₁ g₂ hg₁ hg₂ _ ih₁ ih₂
        exact (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b).topologicalClosure.add_mem ih₁ ih₂
    exact hmem
  exact fun f => closure_minimal hsf isClosed_closure (Lp.simpleFunc.dense hp f)

/-- On a pseudometric space with Borel-measurable balls, if `b` belongs to `L²` on every open ball
`Metric.ball x₀ N` (`N : ℕ`), then `lpTwoSmulSubmodule b` is dense in `Lp E p μ` for `1 ≤ p < ∞`. -/
theorem dense_lpTwoSmulSubmodule_of_memLp_restrict_ball {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X} {b : X → ℝ} (hp : p ≠ ∞)
    (x₀ : X) (hb : ∀ N : ℕ, MemLp b 2 (ν.restrict (Metric.ball x₀ N))) :
    Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := ν) b : Set (Lp E p ν)) := by
  refine dense_lpTwoSmulSubmodule_of_iUnion_eq_univ hp
    (fun i j hij => Metric.ball_subset_ball (Nat.cast_le.2 hij))
    (fun _ => Metric.isOpen_ball.measurableSet) ?_ hb
  ext x
  simp only [mem_iUnion, Metric.mem_ball, mem_univ, iff_true]
  exact exists_nat_gt (dist x x₀)

end Density

end MeasureTheory

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal NNReal

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞}

/-- An `Lᵖ` commutator estimate on `L²` places `b • T f - T g` in `Lᵖ` whenever `f ∈ L² ∩ Lᵖ` and
`g ∈ L²` represents `b • f`. -/
theorem memLp_commutator_of_eLpNorm_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (f g : Lp E 2 μ) (hfg : (g : α → E) =ᵐ[μ] fun x => b x • f x) (hf : MemLp f p μ) :
    MemLp (fun x => b x • T f x - T g x) p μ :=
  (hT f g hfg hf).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf)

private theorem smulToL2_ae_toL2 {b : α → ℝ}
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    (lpTwoSmulSubmodule.smulToL2 f : α → E) =ᵐ[μ]
      fun x => b x • (lpTwoSmulSubmodule.toL2 f : α → E) x := by
  filter_upwards [lpTwoSmulSubmodule.smulToL2_ae f, lpTwoSmulSubmodule.toL2_ae f] with x h₁ h₂
  rw [h₁, h₂]

private theorem memLp_toL2_of_lpTwoSmulSubmodule {b : α → ℝ}
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    MemLp (lpTwoSmulSubmodule.toL2 f : α → E) p μ :=
  (Lp.memLp f.1).ae_eq (lpTwoSmulSubmodule.toL2_ae f).symm

/-- The commutator `[b, T]` as a linear map on `lpTwoSmulSubmodule b` with values in `Lp F p μ`. -/
def commutatorOnIntersection (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ) :
    lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b →ₗ[ℝ] Lp F p μ where
  toFun f := (memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 f)
    (lpTwoSmulSubmodule.smulToL2 f) (smulToL2_ae_toL2 f)
    (memLp_toL2_of_lpTwoSmulSubmodule f)).toLp _
  map_add' f g := by
    apply Lp.ext
    let hfg := memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 (f + g))
      (lpTwoSmulSubmodule.smulToL2 (f + g)) (smulToL2_ae_toL2 (f + g))
      (memLp_toL2_of_lpTwoSmulSubmodule (f + g))
    let hf := memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 f)
      (lpTwoSmulSubmodule.smulToL2 f) (smulToL2_ae_toL2 f)
      (memLp_toL2_of_lpTwoSmulSubmodule f)
    let hg := memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 g)
      (lpTwoSmulSubmodule.smulToL2 g) (smulToL2_ae_toL2 g)
      (memLp_toL2_of_lpTwoSmulSubmodule g)
    have hTadd1 : (T (lpTwoSmulSubmodule.toL2 (f + g)) : α → F) =ᵐ[μ]
        (T (lpTwoSmulSubmodule.toL2 f) : α → F) + (T (lpTwoSmulSubmodule.toL2 g) : α → F) := by
      rw [map_add, map_add]
      exact Lp.coeFn_add _ _
    have hTadd2 : (T (lpTwoSmulSubmodule.smulToL2 (f + g)) : α → F) =ᵐ[μ]
        (T (lpTwoSmulSubmodule.smulToL2 f) : α → F) +
          (T (lpTwoSmulSubmodule.smulToL2 g) : α → F) := by
      rw [map_add, map_add]
      exact Lp.coeFn_add _ _
    filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp, hTadd1, hTadd2,
      Lp.coeFn_add (hf.toLp _) (hg.toLp _)] with x h₁ h₂ h₃ h₄ h₅ h₆
    rw [h₁, h₄, h₅, h₆, Pi.add_apply, Pi.add_apply, Pi.add_apply, h₂, h₃, smul_add,
      sub_add_sub_comm]
  map_smul' c f := by
    apply Lp.ext
    let hcf := memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 (c • f))
      (lpTwoSmulSubmodule.smulToL2 (c • f)) (smulToL2_ae_toL2 (c • f))
      (memLp_toL2_of_lpTwoSmulSubmodule (c • f))
    let hf := memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 f)
      (lpTwoSmulSubmodule.smulToL2 f) (smulToL2_ae_toL2 f)
      (memLp_toL2_of_lpTwoSmulSubmodule f)
    have hTsmul1 : (T (lpTwoSmulSubmodule.toL2 (c • f)) : α → F) =ᵐ[μ]
        c • (T (lpTwoSmulSubmodule.toL2 f) : α → F) := by
      rw [map_smul, map_smul]
      exact Lp.coeFn_smul _ _
    have hTsmul2 : (T (lpTwoSmulSubmodule.smulToL2 (c • f)) : α → F) =ᵐ[μ]
        c • (T (lpTwoSmulSubmodule.smulToL2 f) : α → F) := by
      rw [map_smul, map_smul]
      exact Lp.coeFn_smul _ _
    filter_upwards [hcf.coeFn_toLp, hf.coeFn_toLp, hTsmul1, hTsmul2,
      Lp.coeFn_smul c (hf.toLp _)] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₃, h₄, RingHom.id_apply, h₅, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, h₂,
      smul_comm (b x) c, smul_sub]

/-- On `lpTwoSmulSubmodule b`, `commutatorOnIntersection` agrees almost everywhere with
`x ↦ b x • T (toL2 f) x - T (smulToL2 f) x`. -/
theorem commutatorOnIntersection_ae (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    (commutatorOnIntersection T b C hT f : α → F) =ᵐ[μ]
      fun x => b x • T (lpTwoSmulSubmodule.toL2 f) x - T (lpTwoSmulSubmodule.smulToL2 f) x :=
  (memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 f)
    (lpTwoSmulSubmodule.smulToL2 f) (smulToL2_ae_toL2 f)
    (memLp_toL2_of_lpTwoSmulSubmodule f)).coeFn_toLp

variable [Fact (1 ≤ p)]

/-- Norm bound `‖[b, T] f‖_p ≤ C ‖f‖_p` on `lpTwoSmulSubmodule b`. -/
theorem norm_commutatorOnIntersection_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    ‖commutatorOnIntersection T b C hT f‖ ≤ C * ‖f‖ := by
  have hfp := memLp_toL2_of_lpTwoSmulSubmodule f
  have hcomm := memLp_commutator_of_eLpNorm_le T b C hT (lpTwoSmulSubmodule.toL2 f)
    (lpTwoSmulSubmodule.smulToL2 f) (smulToL2_ae_toL2 f) hfp
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfp.ne)
    (hT (lpTwoSmulSubmodule.toL2 f) (lpTwoSmulSubmodule.smulToL2 f) (smulToL2_ae_toL2 f) hfp)
  have heq : eLpNorm (lpTwoSmulSubmodule.toL2 f : α → E) p μ = eLpNorm (f.1 : α → E) p μ :=
    eLpNorm_congr_ae (lpTwoSmulSubmodule.toL2_ae f)
  -- Unfold `commutatorOnIntersection` to `MemLp.toLp` so `Lp.norm_toLp` applies.
  change ‖hcomm.toLp _‖ ≤ (C : ℝ) * ‖(f : Lp E p μ)‖
  rw [Lp.norm_toLp, Lp.norm_def]
  simpa [heq, ENNReal.toReal_mul] using h

variable [CompleteSpace F]

/-- The unique continuous linear extension of the commutator `[b, T]` from the dense submodule
`lpTwoSmulSubmodule b` to all of `Lp E p μ`. -/
def commutatorExtension (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (_hb : Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b : Set (Lp E p μ))) :
    Lp E p μ →L[ℝ] Lp F p μ :=
  (commutatorOnIntersection T b C hT).extendOfNorm
    (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b).subtype

theorem commutatorExtension_apply (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (hb : Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b : Set (Lp E p μ)))
    (f : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b) :
    commutatorExtension T b C hT hb f.1 = commutatorOnIntersection T b C hT f :=
  LinearMap.extendOfNorm_eq (denseRange_subtype_val.2 hb)
    ⟨C, norm_commutatorOnIntersection_le T b C hT⟩ f

/-- The operator norm of `commutatorExtension` is at most `C`. -/
theorem norm_commutatorExtension_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (hb : Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b : Set (Lp E p μ))) :
    ‖commutatorExtension T b C hT hb‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_subtype_val.2 hb) C.2
    (norm_commutatorOnIntersection_le T b C hT)

/-- Whenever `f ∈ L² ∩ Lᵖ` and `g ∈ L²` represents `b • f`, `commutatorExtension` applied to
`hf.toLp f` agrees almost everywhere with `x ↦ b x • T f x - T g x`. -/
theorem commutatorExtension_apply_of_memLp (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (hb : Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b : Set (Lp E p μ)))
    (f g : Lp E 2 μ) (hfg : (g : α → E) =ᵐ[μ] fun x => b x • f x) (hf : MemLp f p μ) :
    (commutatorExtension T b C hT hb (hf.toLp f) : α → F) =ᵐ[μ]
      fun x => b x • T f x - T g x := by
  have hf2 : MemLp (hf.toLp f : α → E) 2 μ := (Lp.memLp f).ae_eq hf.coeFn_toLp.symm
  have hg2 : MemLp (fun x => b x • (hf.toLp f : α → E) x) 2 μ := by
    refine (Lp.memLp g).ae_eq ?_
    filter_upwards [hfg, hf.coeFn_toLp] with x hx₁ hx₂
    rw [hx₁, hx₂]
  let u : lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b := ⟨hf.toLp f, hf2, hg2⟩
  have hu_f : lpTwoSmulSubmodule.toL2 u = f := Lp.ext (hf2.coeFn_toLp.trans hf.coeFn_toLp)
  have hu_g : lpTwoSmulSubmodule.smulToL2 u = g := by
    apply Lp.ext
    filter_upwards [lpTwoSmulSubmodule.smulToL2_ae u, hf.coeFn_toLp, hfg] with x hx₁ hx₂ hx₃
    rw [hx₁, hx₂, hx₃]
  rw [commutatorExtension_apply T b C hT hb u]
  simpa only [hu_f, hu_g] using commutatorOnIntersection_ae T b C hT u

/-- Uniqueness of `commutatorExtension`: any continuous linear map `S : Lp E p μ →L[ℝ] Lp F p μ`
agreeing almost everywhere with `b • T f - T g` whenever `f ∈ L² ∩ Lᵖ` and `g ∈ L²` represents
`b • f` equals `commutatorExtension T b C hT hb`. -/
theorem commutatorExtension_unique_of_ae (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (b : α → ℝ) (C : ℝ≥0)
    (hT : ∀ (f g : Lp E 2 μ), (g : α → E) =ᵐ[μ] (fun x => b x • f x) → MemLp f p μ →
      eLpNorm (fun x => b x • T f x - T g x) p μ ≤ C * eLpNorm f p μ)
    (hb : Dense (lpTwoSmulSubmodule (E := E) (p := p) (μ := μ) b : Set (Lp E p μ)))
    (S : Lp E p μ →L[ℝ] Lp F p μ)
    (hS : ∀ (f g : Lp E 2 μ) (_hfg : (g : α → E) =ᵐ[μ] fun x => b x • f x) (hf : MemLp f p μ),
      (S (hf.toLp f) : α → F) =ᵐ[μ] fun x => b x • T f x - T g x) :
    S = commutatorExtension T b C hT hb := by
  symm
  refine LinearMap.extendOfNorm_unique (denseRange_subtype_val.2 hb) C
    (norm_commutatorOnIntersection_le T b C hT) S ?_
  apply LinearMap.ext
  intro u
  have hfp := memLp_toL2_of_lpTwoSmulSubmodule u
  have heq : hfp.toLp (lpTwoSmulSubmodule.toL2 u : α → E) = u.1 :=
    Lp.ext (hfp.coeFn_toLp.trans (lpTwoSmulSubmodule.toL2_ae u))
  have hSu := hS (lpTwoSmulSubmodule.toL2 u) (lpTwoSmulSubmodule.smulToL2 u)
    (smulToL2_ae_toL2 u) hfp
  have hEu := commutatorExtension_apply_of_memLp T b C hT hb (lpTwoSmulSubmodule.toL2 u)
    (lpTwoSmulSubmodule.smulToL2 u) (smulToL2_ae_toL2 u) hfp
  rw [heq] at hSu
  rw [heq, commutatorExtension_apply T b C hT hb u] at hEu
  exact Lp.ext (hSu.trans hEu.symm)

end ContinuousLinearMap

end
