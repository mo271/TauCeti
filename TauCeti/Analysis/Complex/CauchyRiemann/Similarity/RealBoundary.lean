/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundaryReflection
public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak

/-!
# The boundary Sobolev similarity principle and unique continuation

Let `F` be a finite-dimensional complex normed space whose real structure is its `star` operation,
let `2 < p < ∞`, and let `Ω ⊆ ℂ` be a conjugation-invariant open set. Suppose `ξ : ℂ → F` is
continuous on the closed upper part `Ω ∩ {z | 0 ≤ z.im}`, real on `Ω ∩ ℝ` (`star (ξ x) = ξ x`),
and solves `∂ₛξ + i ∂ₜξ + C(z) ξ = 0` weakly on `Ω ∩ {z | 0 ≤ z.im}` with the real boundary
condition (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn`), for a coefficient field
`C ∈ Lᵖ_loc(Ω ∩ {z | 0 ≤ z.im})`.

The theorem
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.isWeakLinearCauchyRiemannOn_starSchwarzReflection`
shows that `TauCeti.starSchwarzReflection ξ` solves the weak linear Cauchy–Riemann equation on all
of `Ω` with the reflected `Lᵖ_loc(Ω)` coefficient `TauCeti.starSchwarzReflectionCoeff C`. Applying
the interior Sobolev similarity principle (`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak`)
to the reflected equation yields the boundary similarity principle and boundary unique continuation:

* Around every point `z₀ ∈ Ω ∩ {z | 0 ≤ z.im}` — including boundary points on `Ω ∩ ℝ` — there is a
  closed disc `closedBall z₀ r ⊆ Ω` (`r > 0`) on whose closed upper half `ξ` factors as `ξ = Φ σ`,
  with `Φ : ℂ → F →L[ℂ] F` continuous, invertible, and in `W^{1,p}_loc` on the full closed disc and
  `σ : ℂ → F` continuous on the closed disc and holomorphic on the open disc
  (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_similarity`).
* When `Ω` is preconnected, `ξ` satisfies unique continuation from an infinite-order interior or
  boundary zero along `{z | 0 ≤ z.im}`
  (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_forall_isBigO`), unique
  continuation from vanishing on a nonempty open interval of `Ω ∩ ℝ`
  (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_eqOn_zero_Ioo`), and discreteness
  of zeros in `Ω ∩ {z | 0 ≤ z.im}`
  (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eventually_ne_zero`,
  `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.setOf_ne_zero_mem_codiscreteWithin`).

The closing checks verify sharpness of the boundary `Lᵖ_loc` condition: neither the flat function
`exp (-1 / ‖z‖²)` (vanishing to infinite order at `0`) nor `z ↦ i · z.im` (vanishing on all of `ℝ`
with singular boundary coefficient `~ y⁻¹`) can solve the weak real-boundary equation with a
coefficient locally in `Lᵖ` (`2 < p < ∞`) up to `ℝ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5, Exercise 2.3.6, and Appendix B.4.
-/

public noncomputable section

open Asymptotics Complex ContinuousLinearMap Filter MeasureTheory Metric Set Topology
  TopologicalSpace
open scoped ComplexConjugate ENNReal

namespace TauCeti

section RealBoundary

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  [ContinuousStar F] [FiniteDimensional ℂ F] {p : ℝ≥0∞} {Ω : Opens ℂ} {C : ℂ → F →L[ℝ] F}
  {ξ : ℂ → F}

/-- **The boundary Sobolev similarity principle.** Let `2 < p < ∞`, `F` finite-dimensional with a
continuous conjugate-linear `star`, and `Ω` conjugation-invariant. Suppose `C` is locally `Lᵖ` on
`Ω ∩ {0 ≤ im}`, and `ξ` is continuous on `Ω ∩ {0 ≤ im}`, fixed by `star` on `Ω ∩ ℝ`, and solves
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly with the real boundary condition. Then around every point
`z₀ ∈ Ω ∩ {0 ≤ im}` (interior or on `ℝ`) there exist `r > 0` with `closedBall z₀ r ⊆ Ω`, a
complex-linear factor `Φ : ℂ → F →L[ℂ] F` continuous, invertible, and in `W^{1,p}_loc` on
`closedBall z₀ r`, and `σ : ℂ → F` continuous on `closedBall z₀ r` and holomorphic on `ball z₀ r`,
such that `starSchwarzReflection ξ = Φ σ` on `closedBall z₀ r` and `ξ = Φ σ` on
`closedBall z₀ r ∩ {0 ≤ im}`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.exists_similarity (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∃ r > 0, closedBall z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → F →L[ℂ] F) (σ : ℂ → F),
      ContinuousOn Φ (closedBall z₀ r) ∧ MemWkpLoc p (closedBall z₀ r) 1 Φ ∧
      (∀ z ∈ closedBall z₀ r, IsUnit (Φ z)) ∧ ContinuousOn σ (closedBall z₀ r) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn (starSchwarzReflection ξ) (fun z ↦ Φ z (σ z)) (closedBall z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (closedBall z₀ r ∩ {z | 0 ≤ z.im}) := by
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hrefl := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hΦu, hσc, hσ, hR⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemann_I_smul_id hp hp_top Ω.isOpen
      (hC.starSchwarzReflectionCoeff hΩ) hrefl hz₀.1
  refine ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hΦu, hσc, hσ, hR, fun z hz ↦ ?_⟩
  simpa only [starSchwarzReflection_of_im_nonneg hz.2] using hR hz.1

/-- **Unique continuation from an infinite-order interior or boundary zero.** On a preconnected
conjugation-invariant open set `Ω`, if `ξ = O((z - z₀)ⁿ)` within `{0 ≤ im}` for every `n` at some
point `z₀ ∈ Ω ∩ {0 ≤ im}`, then `ξ` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_forall_isBigO (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hrefl := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  have hR0 : EqOn (starSchwarzReflection ξ) 0 Ω :=
    eqOn_zero_of_isWeakLinearCauchyRiemann_of_forall_isBigO hp hp_top Ω.isOpen hΩc
      continuousOn_const (memWkpLoc_const _) (fun _ _ ↦ by ext w; simp [smul_smul])
      (hC.starSchwarzReflectionCoeff hΩ) hrefl hz₀.1 fun n ↦
        isBigO_starSchwarzReflection_sub_pow hz₀.2 (h₀ n)
  exact fun z hz ↦ by simpa only [starSchwarzReflection_of_im_nonneg hz.2] using hR0 hz.1

/-- **Boundary unique continuation from a real interval.** On a preconnected conjugation-invariant
open set `Ω`, if `ξ` vanishes on a nonempty open interval `Ioo a b` contained in `Ω ∩ ℝ`, then `ξ`
vanishes on all of `Ω ∩ {0 ≤ im}`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_eqOn_zero_Ioo (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {a b : ℝ} (hab : a < b) (hIΩ : ∀ x ∈ Ioo a b, (x : ℂ) ∈ Ω)
    (hI0 : ∀ x ∈ Ioo a b, ξ x = 0) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have := FiniteDimensional.completeSpace ℂ F
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hrefl := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  set x₀ : ℝ := (a + b) / 2 with hx₀_def
  have hx₀ : x₀ ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hz₀ : (x₀ : ℂ) ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := ⟨hIΩ x₀ hx₀, by simp⟩
  obtain ⟨r, hr, -, Φ, σ, -, -, hΦu, -, hσ, hR, hξΦ⟩ :=
    h.exists_similarity hp hp_top hΩ hC hξc hξr hz₀
  have hσa : AnalyticAt ℂ σ x₀ := hσ.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hσ0 : ∀ᶠ z in 𝓝 (x₀ : ℂ), σ z = 0 := by
    refine hσa.eventually_eq_zero_or_eventually_ne_zero.resolve_right fun hne ↦ ?_
    obtain ⟨δ, hδ, hδne⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hne)
    set ε : ℝ := min (min (r / 2) (δ / 2)) ((b - a) / 4)
    have hε : 0 < ε := lt_min (lt_min (half_pos hr) (half_pos hδ)) (by linarith)
    have hεr : ε ≤ r / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hεδ : ε ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hεb : ε ≤ (b - a) / 4 := min_le_right _ _
    set x₁ : ℝ := x₀ + ε with _
    have hdist : dist (x₁ : ℂ) (x₀ : ℂ) = ε := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        show x₁ - x₀ = ε by ring, Real.norm_of_nonneg hε.le]
    have hx₁c : (x₁ : ℂ) ∈ closedBall (x₀ : ℂ) r :=
      mem_closedBall.2 (hdist.le.trans (hεr.trans (half_lt_self hr).le))
    have hΦσ : Φ x₁ (σ x₁) = 0 := by
      simpa [hI0 x₁ ⟨by linarith, by linarith⟩] using (hξΦ ⟨hx₁c, by simp⟩).symm
    obtain ⟨u, hu⟩ := hΦu x₁ hx₁c
    have h0 : σ x₁ = 0 := (ContinuousLinearEquiv.unitsEquiv ℂ F u).injective
      (by simpa [← hu] using hΦσ)
    exact hδne (hdist.trans_lt (hεδ.trans_lt (half_lt_self hδ)))
      (Complex.ofReal_injective.ne (by linarith)) h0
  have hRnear : ∀ᶠ z in 𝓝 (x₀ : ℂ), starSchwarzReflection ξ z = 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr), hσ0] with z hz hσz
    simp only [hR (ball_subset_closedBall hz), hσz, map_zero]
  have hR0 : EqOn (starSchwarzReflection ξ) 0 Ω :=
    eqOn_zero_of_isWeakLinearCauchyRiemann_of_eventually_eq_zero hp hp_top Ω.isOpen hΩc
      continuousOn_const (memWkpLoc_const _) (fun _ _ ↦ by ext w; simp [smul_smul])
      (hC.starSchwarzReflectionCoeff hΩ) hrefl hz₀.1 hRnear
  exact fun z hz ↦ by simpa only [starSchwarzReflection_of_im_nonneg hz.2] using hR0 hz.1

/-- **Punctured half-plane nonvanishing.** On a preconnected conjugation-invariant open set `Ω`, a
weak real-boundary solution not identically zero on `Ω ∩ {0 ≤ im}` is nonzero on a punctured
closed-upper-half-plane neighbourhood of every point `z₀ ∈ Ω ∩ {0 ≤ im}` (including points on `ℝ`).
-/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.eventually_ne_zero (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∀ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, ξ z ≠ 0 := by
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hrefl := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  obtain ⟨z₁, hz₁, hne₁⟩ := hne
  have hRne : ∀ᶠ z in 𝓝[≠] z₀, starSchwarzReflection ξ z ≠ 0 :=
    eventually_ne_zero_of_isWeakLinearCauchyRiemann hp hp_top Ω.isOpen hΩc
      continuousOn_const (memWkpLoc_const _) (fun _ _ ↦ by ext w; simp [smul_smul])
      (hC.starSchwarzReflectionCoeff hΩ) hrefl
      ⟨z₁, hz₁.1, by rwa [starSchwarzReflection_of_im_nonneg hz₁.2]⟩ hz₀.1
  filter_upwards [hRne.filter_mono
    (nhdsWithin_mono z₀ (s := {z | 0 ≤ z.im} \ {z₀}) fun _ hz ↦ hz.2),
    self_mem_nhdsWithin] with z hz hzH
  rwa [starSchwarzReflection_of_im_nonneg hzH.1] at hz

/-- **Isolated interior and boundary zeros.** On a preconnected conjugation-invariant open set `Ω`,
the zeros in `Ω ∩ {0 ≤ im}` of a weak real-boundary solution not identically zero there form a
discrete subset of `Ω ∩ {0 ≤ im}`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.setOf_ne_zero_mem_codiscreteWithin (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  refine mem_codiscreteWithin.2 fun z₀ hz₀ ↦ disjoint_principal_right.2 ?_
  filter_upwards [nhdsWithin_le_nhds (eventually_nhdsWithin_iff.1
    (h.eventually_ne_zero hp hp_top hΩ hΩc hC hξc hξr hne hz₀)),
    self_mem_nhdsWithin] with z hz hzne hmem
  exact hmem.2 (hz ⟨hmem.1.2, hzne⟩)

end RealBoundary

/-! ### Calibrating checks for the boundary `Lᵖ_loc` hypothesis -/

section Checks

/-- `TauCeti.expNegInvNormSq` is fixed by Schwarz reflection across the real axis. -/
theorem starSchwarzReflection_expNegInvNormSq :
    starSchwarzReflection expNegInvNormSq = expNegInvNormSq := by
  funext z
  by_cases hz : 0 ≤ z.im
  · exact starSchwarzReflection_of_im_nonneg hz
  · simp [starSchwarzReflection_of_im_neg (not_le.1 hz), expNegInvNormSq_def]

/-- **Check (`exp (-1 / ‖z‖²)` at a boundary point).** For `2 < p < ∞` and any conjugation-invariant
open set `Ω` containing `0`, no coefficient `C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})` makes
`TauCeti.expNegInvNormSq` a weak real-boundary solution on `Ω`. -/
theorem not_exists_memLpLoc_hasWeakConjWirtingerDerivRealBoundaryOn_expNegInvNormSq {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Opens ℂ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (h0 : (0 : ℂ) ∈ Ω) :
    ¬ ∃ C : ℂ → ℂ →L[ℝ] ℂ, MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C ∧
      HasWeakConjWirtingerDerivRealBoundaryOn Ω expNegInvNormSq
        (fun z ↦ -(2 : ℂ)⁻¹ • C z (expNegInvNormSq z)) := by
  rintro ⟨C, hC, h⟩
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hrefl := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC
    (contDiff_expNegInvNormSq.continuous.continuousOn) (fun x _ ↦ by simp [expNegInvNormSq_def])
  rw [starSchwarzReflection_expNegInvNormSq] at hrefl
  exact not_exists_memLpLoc_isWeakLinearCauchyRiemannOn_expNegInvNormSq hp hp_top Ω.isOpen h0
    ⟨starSchwarzReflectionCoeff C, hC.starSchwarzReflectionCoeff hΩ, hrefl⟩

/-- **Check (`z ↦ i · z.im` vanishing along the real axis).** Although `ξ(z) = i · z.im` is smooth,
real (zero) on `ℝ`, and satisfies `bar∂ξ = (i / (2 z.im)) ξ` on `{0 < im}`, its singular boundary
coefficient `~ (z.im)⁻¹` cannot be replaced by any `C ∈ Lᵖ_loc` (`2 < p < ∞`) up to the real axis:
boundary unique continuation from `Ioo (-1) 1` would force `ξ` to vanish at `i`. -/
theorem not_exists_memLpLoc_hasWeakConjWirtingerDerivRealBoundaryOn_I_mul_im {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) :
    ¬ ∃ C : ℂ → ℂ →L[ℝ] ℂ, MemLpLoc p ((⊤ : Opens ℂ) ∩ {z | 0 ≤ z.im}) C ∧
      HasWeakConjWirtingerDerivRealBoundaryOn ⊤ (fun z : ℂ ↦ I * (z.im : ℂ))
        (fun z ↦ -(2 : ℂ)⁻¹ • C z (I * (z.im : ℂ))) := by
  rintro ⟨C, hC, h⟩
  have hzero := h.eqOn_zero_of_eqOn_zero_Ioo hp hp_top (mapsTo_univ _ _) isPreconnected_univ hC
    (continuous_const.mul (Complex.continuous_ofReal.comp Complex.continuous_im)).continuousOn
    (fun x _ ↦ by simp) (a := -1) (b := 1) (by norm_num) (fun _ _ ↦ trivial) (fun x _ ↦ by simp)
  have hI : I * ((I : ℂ).im : ℂ) = 0 := hzero ⟨trivial, by simp⟩
  simp [I_ne_zero] at hI

end Checks

end TauCeti
