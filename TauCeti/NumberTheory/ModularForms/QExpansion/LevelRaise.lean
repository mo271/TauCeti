/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Linear independence of level-raised modular and cusp forms

For a fixed modular form `f` with a nonzero positive-index Fourier coefficient — in particular, any
nonzero cusp form — its level-raises `(V_d f)(τ) = f(dτ)` across pairwise distinct positive
multipliers `d` are linearly independent over `ℂ`.

On `q`-expansions at width `1`, `V_d` acts as `PowerSeries.expand d`
(`TauCeti.ModularForm.qExpansion_levelRaise`), so any linear relation among the level-raises yields
the same linear relation among the expanded `q`-expansions, which vanishes by
`PowerSeries.linearIndependent_expand_of_coeff_ne_zero`. Because `V_d f` inherits `1`-periodicity
from `f`, no cusp or strict-period hypothesis is needed on the target subgroup `𝒢'`. This is the
single-form linear independence step in the Atkin–Lehner–Miyake–Li decomposition of `S_k(Γ₁(N))`
into level-raised newforms (Diamond–Shurman, Theorem 5.8.3; Miyake, Theorem 4.6.19).

## Main results

* `TauCeti.ModularForm.linearIndependent_levelRaise`: the level-raises `V_{d i} f` of a modular
  form with a nonzero positive-degree `q`-expansion coefficient along an injective family `d` are
  linearly independent.
* `TauCeti.CuspForm.linearIndependent_levelRaise`: the level-raises `V_{d i} f` of a nonzero cusp
  form along an injective family `d` are linearly independent.
* `TauCeti.CuspForm.linearIndependent_levelRaise_iff`: for a nonzero cusp form `f`, the family
  `i ↦ V_{d i} f` is linearly independent if and only if `d` is injective.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.19.
-/

public section

open UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {ι : Type*} {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- A finite sum of functions on `ℍ` whose cusp functions at width `h` are analytic at `0` again
has an analytic cusp function at `0`, and its `q`-expansion is the sum of theirs. -/
private theorem analyticAt_and_qExpansion_sum (h : ℝ) (s : Finset ι) (g : ι → ℍ → ℂ)
    (hg : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (g i)) 0) :
    AnalyticAt ℂ (cuspFunction h (∑ i ∈ s, g i)) 0 ∧
      qExpansion h (∑ i ∈ s, g i) = ∑ i ∈ s, qExpansion h (g i) := by
  induction s using Finset.cons_induction with
  | empty =>
    refine ⟨?_, by simpa using _root_.UpperHalfPlane.qExpansion_zero h⟩
    simpa [show (0 : ℍ → ℂ) = fun _ ↦ 0 from rfl] using analyticAt_const
  | cons a s ha ih =>
    obtain ⟨hana_s, hq_s⟩ := ih fun i hi ↦ hg i (Finset.mem_cons_of_mem hi)
    have hana_a := hg a (Finset.mem_cons_self a s)
    rw [Finset.sum_cons, Finset.sum_cons]
    refine ⟨?_, ?_⟩
    · rw [_root_.UpperHalfPlane.cuspFunction_add hana_a.continuousAt hana_s.continuousAt]
      exact hana_a.add hana_s
    · rw [_root_.UpperHalfPlane.qExpansion_add hana_a hana_s, hq_s]

namespace ModularForm

/-- **Level-raises of a non-constant modular form at distinct multipliers are linearly
independent.** If `1 ∈ 𝒢.strictPeriods`, `f : ModularForm 𝒢 k` has a nonzero `q`-expansion
coefficient at some positive index `m ≠ 0`, and `d : ι → ℕ` is an injective family of nonzero
multipliers, then the level-raised forms `V_{d i} f` in `ModularForm 𝒢' k` are `ℂ`-linearly
independent. -/
theorem linearIndependent_levelRaise [𝒢'.HasDetOne] (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    {d : ι → ℕ} [∀ i, NeZero (d i)] (hinj : Function.Injective d)
    (hle : ∀ i, 𝒢' ≤ ConjAct.toConjAct (scaleGL (d i))⁻¹ • 𝒢)
    {f : ModularForm 𝒢 k} {m : ℕ} (hm : m ≠ 0) (hfm : (qExpansion 1 f).coeff m ≠ 0) :
    LinearIndependent ℂ fun i ↦ ModularForm.levelRaise (d i) (hle i) f := by
  have hli := PowerSeries.linearIndependent_expand_of_coeff_ne_zero (fun i ↦ NeZero.ne (d i))
    hinj hm hfm
  rw [linearIndependent_iff'] at hli ⊢
  intro s c hc
  have hcoe : (∑ i ∈ s, c i • ⇑(ModularForm.levelRaise (d i) (hle i) f) : ℍ → ℂ) = 0 := by
    ext τ
    simpa using congr($hc τ)
  have hana : ∀ i ∈ s, AnalyticAt ℂ
      (cuspFunction 1 (c i • ⇑(ModularForm.levelRaise (d i) (hle i) f))) 0 := by
    intro i _
    have hi := _root_.ModularForm.analyticAt_cuspFunction_levelRaise
      (by simpa using nsmul_mem h𝒢 (d i)) (hle i) f
    rw [_root_.UpperHalfPlane.cuspFunction_smul hi.continuousAt]
    exact analyticAt_const.smul hi
  have hq := (analyticAt_and_qExpansion_sum 1 s _ hana).2
  rw [hcoe, _root_.UpperHalfPlane.qExpansion_zero] at hq
  refine hli s c ((Finset.sum_congr rfl fun i _ ↦ ?_).symm.trans hq.symm)
  have hi := _root_.ModularForm.analyticAt_cuspFunction_levelRaise
    (by simpa using nsmul_mem h𝒢 (d i)) (hle i) f
  rw [_root_.UpperHalfPlane.qExpansion_smul hi, ModularForm.qExpansion_levelRaise h𝒢 (hle i) f]

end ModularForm

namespace CuspForm

/-- **Level-raises of a nonzero cusp form at distinct multipliers are linearly independent**
(Diamond–Shurman, Theorem 5.8.3; Miyake, Theorem 4.6.19). A nonzero cusp form at width `1` has
vanishing constant term and cannot have all positive Fourier coefficients zero. -/
theorem linearIndependent_levelRaise [𝒢'.HasDetOne] (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    {d : ι → ℕ} [∀ i, NeZero (d i)] (hinj : Function.Injective d)
    (hle : ∀ i, 𝒢' ≤ ConjAct.toConjAct (scaleGL (d i))⁻¹ • 𝒢)
    {f : CuspForm 𝒢 k} (hf : f ≠ 0) :
    LinearIndependent ℂ fun i ↦ CuspForm.levelRaise (d i) (hle i) f := by
  -- Since `f ≠ 0` and its `0`-th `q`-expansion coefficient vanishes, some positive coefficient of
  -- `f` is nonzero.
  have hq0 : qExpansion 1 f ≠ 0 := fun h0 ↦ hf <|
    _root_.CuspForm.qExpansion_injective one_pos h𝒢
      (by simpa [_root_.UpperHalfPlane.qExpansion_zero] using h0)
  have hex : ∃ m ≠ 0, (qExpansion 1 f).coeff m ≠ 0 := by
    by_contra! hall
    refine hq0 (PowerSeries.ext fun n ↦ ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using CuspFormClass.qExpansion_coeff_zero (f := f) one_pos h𝒢
    · simpa using hall n hn
  obtain ⟨m, hm, hfm⟩ := hex
  have hmod := ModularForm.linearIndependent_levelRaise h𝒢 hinj hle
    (f := (f : ModularForm 𝒢 k)) hm (by simpa using hfm)
  refine LinearIndependent.of_comp _root_.CuspForm.toModularFormₗ ?_
  convert hmod with i
  ext τ
  simp [_root_.CuspForm.toModularFormₗ_apply]

/-- For a nonzero cusp form `f`, the family `i ↦ V_{d i} f` is linearly independent if and only if
the multiplier map `d` is injective. -/
theorem linearIndependent_levelRaise_iff [𝒢'.HasDetOne] (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    {d : ι → ℕ} [∀ i, NeZero (d i)]
    (hle : ∀ i, 𝒢' ≤ ConjAct.toConjAct (scaleGL (d i))⁻¹ • 𝒢)
    {f : CuspForm 𝒢 k} (hf : f ≠ 0) :
    (LinearIndependent ℂ fun i ↦ CuspForm.levelRaise (d i) (hle i) f) ↔ Function.Injective d := by
  refine ⟨fun hli i j hij ↦ hli.injective ?_,
    fun hinj ↦ linearIndependent_levelRaise h𝒢 hinj hle hf⟩
  ext τ
  simp [hij]

end CuspForm

end TauCeti
