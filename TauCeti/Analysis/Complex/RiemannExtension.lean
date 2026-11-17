/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.LiminfLimsup
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Topology.ContinuousOn.Dense

/-!
# Riemann's removable singularity theorem across analytic subsets

On an open subset `U` of a finite-dimensional complex normed space `E`, let `A ⊆ E` be locally
contained in the zero set of a non-identically-zero analytic function at every point of `U` (for
instance, the common zero set of an arbitrary family of holomorphic functions on `U` with empty
interior). **Riemann's extension theorem** states that any map `f : E → F` into a complete complex
normed space that is complex differentiable on `U \ A` and locally bounded near every point of
`U ∩ A` extends analytically (hence holomorphically) across `A` to all of `U`.

Locally at a point `p` where `h : E → ℂ` is analytic and does not vanish identically near `p`, a
linear change of coordinates (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`)
puts `h` in general position in the last complex variable. Choosing a small circle `C(w₀, r)` in
that variable on which `h` has no zeros, compactness of the circle keeps `h` nonvanishing on
`ball x₀ δ ×ˢ sphere w₀ r`. The one-variable Cauchy integral
`(x, w) ↦ (2πi)⁻¹ • ∮ ζ in C(w₀, r), (ζ - w)⁻¹ • f (x, ζ)`
is then jointly analytic at `(x₀, w₀)` by `TauCeti.analyticAt_circleIntegral`, and on each slice
`x ∈ ball x₀ δ` it reproduces `f (x, w)` whenever `h (x, w) ≠ 0` by applying the one-dimensional
removable singularity theorem (`Complex.differentiableOn_update_limUnder_of_bddAbove`) at the
isolated zeros of `ζ ↦ h (x, ζ)` inside `ball w₀ R` followed by Cauchy's integral formula.

These local extensions patch canonically via `x ↦ limUnder (𝓝[U \ A] x) f`, yielding analyticity on
`U` without assuming `A` is closed in `U`. Since `U ⊆ closure (U \ A)`, any continuous extension to
`U` is unique by `Set.EqOn.of_subset_closure`. On `ℂ` with `A = {0}`, `z ↦ z⁻¹` shows that local
boundedness is necessary (`TauCeti.not_exists_continuousAt_and_eqOn_inv_compl_zero`).

## Main results

* `TauCeti.exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero`,
  `TauCeti.analyticAt_limUnder_of_analyticAt_ne_zero`,
  `TauCeti.tendsto_limUnder_of_analyticAt_ne_zero`: **local Riemann extension** across the zero
  locus of an analytic function at a point.
* `TauCeti.analyticOnNhd_limUnder_of_locally_analytic_zero`,
  `TauCeti.exists_analyticOnNhd_eqOn_sdiff_of_locally_analytic_zero`: **global Riemann extension**
  on an open set `U` across any set locally contained in nontrivial analytic hypersurfaces.
* `TauCeti.exists_analyticOnNhd_eqOn_sdiff_iInter_zero`,
  `TauCeti.exists_analyticOnNhd_eqOn_sdiff_zero`: extension on an open set across the common zero
  set of an arbitrary family of holomorphic functions (or a single holomorphic function) with empty
  interior.
* `TauCeti.exists_differentiable_eqOn_compl_iInter_zero`,
  `TauCeti.exists_differentiable_eqOn_compl_zero`: global entire extensions on `E`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §4, Theorem 4.2.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I, §C,
  Theorem 3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.3.
-/

public section

open Complex Filter Function Metric Real Set Topology

namespace TauCeti

/-! ### One-dimensional slice formula and product-space local extension -/

section LocalHelpers

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- On a disc `ball w₀ R` where `g : ℂ → ℂ` is analytic and nonvanishing on `sphere w₀ r`
(`0 < r < R`), a function `φ : ℂ → F` that is complex differentiable and bounded by `C` off
`{g = 0}` is recovered on `ball w₀ r \ {g = 0}` by the Cauchy integral over `C(w₀, r)`. -/
private theorem cauchyIntegral_eq_of_analyticOnNhd_ne_zero {g : ℂ → ℂ} {φ : ℂ → F} {w₀ : ℂ}
    {r R C : ℝ} (hr : 0 < r) (hrR : r < R) (hg : AnalyticOnNhd ℂ g (ball w₀ R))
    (hg_sphere : ∀ ζ ∈ sphere w₀ r, g ζ ≠ 0)
    (hφ_diff : ∀ ζ ∈ ball w₀ R, g ζ ≠ 0 → DifferentiableAt ℂ φ ζ)
    (hφ_bdd : ∀ ζ ∈ ball w₀ R, g ζ ≠ 0 → ‖φ ζ‖ ≤ C)
    {w : ℂ} (hw : w ∈ ball w₀ r) (hgw : g w ≠ 0) :
    ((2 * π * I : ℂ)⁻¹ • ∮ ζ in C(w₀, r), (ζ - w)⁻¹ • φ ζ) = φ w := by
  classical
  -- Since `g` does not vanish on `sphere w₀ r ⊆ ball w₀ R`, its zeros in `ball w₀ R` are isolated.
  have hg_ne_zero : ¬EqOn g 0 (ball w₀ R) := fun h0 ↦ by
    have hpt : w₀ + (r : ℂ) ∈ sphere w₀ r := by
      simp [Complex.norm_real, abs_of_pos hr]
    exact hg_sphere _ hpt (h0 (sphere_subset_ball hrR hpt))
  have hcodisc : ∀ᶠ ζ in codiscreteWithin (ball w₀ R), g ζ ≠ 0 :=
    (hg.eqOn_zero_or_eventually_ne_zero_of_preconnected (convex_ball w₀ R).isPreconnected)
      |>.resolve_left hg_ne_zero
  -- Fill the isolated zeros of `g` by punctured limits to obtain a holomorphic map on `ball w₀ R`.
  set Φ : ℂ → F := fun ζ ↦ if g ζ = 0 then limUnder (𝓝[≠] ζ) φ else φ ζ
  have hΦ_diff : DifferentiableOn ℂ Φ (closedBall w₀ r) := by
    refine fun ζ hζ ↦ DifferentiableAt.differentiableWithinAt ?_
    have hζR : ζ ∈ ball w₀ R := closedBall_subset_ball hrR hζ
    by_cases hgζ : g ζ = 0
    · have hne : ∀ᶠ τ in 𝓝[≠] ζ, τ ∈ ball w₀ R → g τ ≠ 0 :=
        eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.1 hcodisc ζ hζR
      set s : Set ℂ := {τ ∈ ball w₀ R | τ = ζ ∨ g τ ≠ 0}
      have hs : s ∈ 𝓝 ζ := by
        filter_upwards [isOpen_ball.mem_nhds hζR, eventually_nhdsWithin_iff.1 hne] with τ hτR hτ
        exact ⟨hτR, by by_cases h : τ = ζ; exacts [Or.inl h, Or.inr (hτ h hτR)]⟩
      have hdiff_s : DifferentiableOn ℂ φ (s \ {ζ}) := fun τ ⟨⟨hτR, hτ⟩, hτζ⟩ ↦
        (hφ_diff τ hτR (hτ.resolve_left hτζ)).differentiableWithinAt
      have hbdd_s : BddAbove (norm ∘ φ '' (s \ {ζ})) :=
        ⟨C, by rintro _ ⟨τ, ⟨⟨hτR, hτ⟩, hτζ⟩, rfl⟩; exact hφ_bdd τ hτR (hτ.resolve_left hτζ)⟩
      have hupd := (Complex.differentiableOn_update_limUnder_of_bddAbove hs hdiff_s hbdd_s)
        |>.differentiableAt hs
      refine hupd.congr_of_eventuallyEq (Filter.eventually_of_mem hs fun τ ⟨_, hτ⟩ ↦ ?_)
      by_cases hτζ : τ = ζ
      · subst hτζ; simp [Φ, hgζ]
      · simp [Φ, hτζ, hτ.resolve_left hτζ]
    · have hopen : {τ | g τ ≠ 0} ∈ 𝓝 ζ :=
        (hg ζ hζR).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hgζ)
      refine (hφ_diff ζ hζR hgζ).congr_of_eventuallyEq ?_
      filter_upwards [hopen] with τ hτ
      simp [Φ, hτ]
  have hcongr : (∮ ζ in C(w₀, r), (ζ - w)⁻¹ • φ ζ) = ∮ ζ in C(w₀, r), (ζ - w)⁻¹ • Φ ζ :=
    circleIntegral.integral_congr hr.le fun ζ hζ ↦ by simp [Φ, hg_sphere ζ hζ]
  rw [hcongr, hΦ_diff.circleIntegral_sub_inv_smul hw, inv_smul_smul₀ two_pi_I_ne_zero]
  simp [Φ, hgw]

/-- Joint analyticity of `(x, w) ↦ (2πi)⁻¹ • ∮ (ζ - w)⁻¹ • f (x, ζ)` at `(x₀, w₀)` when `f` is
complex differentiable on `{p ∈ ball x₀ R ×ˢ ball w₀ R | h p ≠ 0}` and `h (x₀, ζ) ≠ 0` on
`sphere w₀ r`. -/
private theorem analyticAt_cauchyIntegral_of_ne_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {h : V × ℂ → ℂ} {f : V × ℂ → F} {x₀ : V} {w₀ : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hh : AnalyticOnNhd ℂ h (ball x₀ R ×ˢ ball w₀ R))
    (hh_sphere : ∀ ζ ∈ sphere w₀ r, h (x₀, ζ) ≠ 0)
    (hf : ∀ p ∈ ball x₀ R ×ˢ ball w₀ R, h p ≠ 0 → DifferentiableAt ℂ f p) :
    AnalyticAt ℂ (fun p : V × ℂ ↦ (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(w₀, r), (ζ - p.2)⁻¹ • f (p.1, ζ))
      (x₀, w₀) := by
  set U₀ : Set (V × ℂ) := {p ∈ ball x₀ R ×ˢ ball w₀ R | h p ≠ 0}
  have hU₀_open : IsOpen U₀ :=
    hh.continuousOn.isOpen_inter_preimage (isOpen_ball.prod isOpen_ball) isOpen_ne
  have hf_diff : DifferentiableOn ℂ f U₀ := fun p hp ↦ (hf p hp.1 hp.2).differentiableWithinAt
  have hf_an : AnalyticOnNhd ℂ f U₀ := hf_diff.analyticOnNhd_of_finiteDimensional hU₀_open
  refine (analyticAt_circleIntegral
    (f := fun y : (V × ℂ) × ℂ ↦ (y.2 - y.1.2)⁻¹ • f (y.1.1, y.2)) fun ζ hζ ↦ ?_).const_smul
  rw [abs_of_pos hr] at hζ
  have hζw₀ : ζ - w₀ ≠ 0 := sub_ne_zero.2 (sphere_disjoint_ball.ne_of_mem hζ (mem_ball_self hr))
  have hmem : (x₀, ζ) ∈ U₀ :=
    ⟨⟨mem_ball_self (hr.trans hrR), sphere_subset_ball hrR hζ⟩, hh_sphere ζ hζ⟩
  exact ((analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)).inv hζw₀).smul
    ((hf_an (x₀, ζ) hmem).comp_of_eq ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd) rfl)

/-- Product-space form of local Riemann extension: if `h : V × ℂ → ℂ` is analytic at `(x₀, w₀)`
with nontrivial vertical slice `w ↦ h (x₀, w)`, then a function `f : V × ℂ → F` that is complex
differentiable and locally bounded off `{h = 0}` near `(x₀, w₀)` extends analytically at `(x₀, w₀)`.
-/
private theorem exists_analyticAt_prod_of_analyticAt_ne_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {h : V × ℂ → ℂ} {f : V × ℂ → F} {x₀ : V} {w₀ : ℂ}
    (hh : AnalyticAt ℂ h (x₀, w₀)) (hslice : ¬(fun w ↦ h (x₀, w)) =ᶠ[𝓝 w₀] 0)
    (hf : ∀ᶠ p in 𝓝 (x₀, w₀), h p ≠ 0 → DifferentiableAt ℂ f p)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[{p | h p ≠ 0}] (x₀, w₀)) (norm ∘ f)) :
    ∃ g : V × ℂ → F, AnalyticAt ℂ g (x₀, w₀) ∧ ∀ᶠ p in 𝓝 (x₀, w₀), h p ≠ 0 → g p = f p := by
  obtain ⟨C, hC⟩ := hbdd
  have hC' : ∀ᶠ p in 𝓝 (x₀, w₀), h p ≠ 0 → ‖f p‖ ≤ C :=
    eventually_nhdsWithin_iff.1 (eventually_map.1 hC)
  have hball : ∀ᶠ p in 𝓝 (x₀, w₀), AnalyticAt ℂ h p ∧ (h p ≠ 0 → DifferentiableAt ℂ f p) ∧
      (h p ≠ 0 → ‖f p‖ ≤ C) :=
    hh.eventually_analyticAt.and (hf.and hC')
  obtain ⟨R, hR, hR_prop⟩ := Metric.nhds_basis_ball.mem_iff.1 hball
  have hR_prod : ∀ p ∈ ball x₀ R ×ˢ ball w₀ R,
      AnalyticAt ℂ h p ∧ (h p ≠ 0 → DifferentiableAt ℂ f p) ∧ (h p ≠ 0 → ‖f p‖ ≤ C) := fun p hp ↦
    hR_prop (by simpa [ball_prod_same] using hp)
  -- Pick a circle `sphere w₀ r ⊆ ball w₀ R` on which `w ↦ h (x₀, w)` does not vanish.
  have hslice_an : AnalyticAt ℂ (fun w ↦ h (x₀, w)) w₀ :=
    hh.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hne_punct : ∀ᶠ w in 𝓝[≠] w₀, h (x₀, w) ≠ 0 :=
    hslice_an.eventually_eq_zero_or_eventually_ne_zero.resolve_left hslice
  obtain ⟨r₀, hr₀, hr₀_ne⟩ :=
    Metric.nhds_basis_ball.mem_iff.1 (eventually_nhdsWithin_iff.1 hne_punct)
  set r : ℝ := min (R / 2) (r₀ / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hr₀)
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hh_sphere : ∀ ζ ∈ sphere w₀ r, h (x₀, ζ) ≠ 0 := fun ζ hζ ↦
    hr₀_ne (sphere_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hr₀)) hζ)
      (sphere_disjoint_ball.ne_of_mem hζ (mem_ball_self hr))
  -- By compactness of `sphere w₀ r`, `h (x, ζ) ≠ 0` persists for `x` near `x₀` uniformly in `ζ`.
  have hne_tube : ∀ᶠ x in 𝓝 x₀, ∀ ζ ∈ sphere w₀ r, h (x, ζ) ≠ 0 :=
    (isCompact_sphere w₀ r).eventually_forall_of_forall_eventually fun ζ hζ ↦
      (hR_prod (x₀, ζ) ⟨mem_ball_self hR, sphere_subset_ball hrR hζ⟩).1.continuousAt
        |>.preimage_mem_nhds (isOpen_ne.mem_nhds (hh_sphere ζ hζ))
  refine ⟨fun p ↦ (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(w₀, r), (ζ - p.2)⁻¹ • f (p.1, ζ),
    analyticAt_cauchyIntegral_of_ne_zero hr hrR (fun p hp ↦ (hR_prod p hp).1) hh_sphere
      (fun p hp ↦ (hR_prod p hp).2.1), ?_⟩
  have hnhds : (ball x₀ R ∩ {x | ∀ ζ ∈ sphere w₀ r, h (x, ζ) ≠ 0}) ×ˢ ball w₀ r ∈ 𝓝 (x₀, w₀) :=
    prod_mem_nhds (inter_mem (ball_mem_nhds x₀ hR) hne_tube) (ball_mem_nhds w₀ hr)
  refine Filter.eventually_of_mem hnhds fun ⟨x, w⟩ ⟨⟨hxR, hx_sph⟩, hw⟩ hne ↦ ?_
  refine cauchyIntegral_eq_of_analyticOnNhd_ne_zero hr hrR
    (fun ζ hζ ↦ (hR_prod (x, ζ) ⟨hxR, hζ⟩).1.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl)
    hx_sph (fun ζ hζ hζne ↦ ((hR_prod (x, ζ) ⟨hxR, hζ⟩).2.1 hζne).comp ζ
      ((differentiableAt_const x).prodMk differentiableAt_id))
    (fun ζ hζ hζne ↦ (hR_prod (x, ζ) ⟨hxR, hζ⟩).2.2 hζne) hw hne

end LocalHelpers

/-! ### Local Riemann extension theorem -/

section Local

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Local Riemann extension theorem.** Let `E` be a finite-dimensional complex normed space, `F` a
complete complex normed space, and `h : E → ℂ` analytic at `p`. Any map `f : E → F` that is complex
differentiable and locally bounded on `{z | h z ≠ 0}` near `p` agrees on `{z | h z ≠ 0}` near `p`
with a map analytic at `p`. (If `h` vanishes identically near `p`, the conclusion holds trivially
with `g = 0`.) -/
theorem exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero {h : E → ℂ} {f : E → F} {p : E}
    (hh : AnalyticAt ℂ h p)
    (hf : ∀ᶠ z in 𝓝 p, h z ≠ 0 → DifferentiableAt ℂ f z)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[{z | h z ≠ 0}] p) (norm ∘ f)) :
    ∃ g : E → F, AnalyticAt ℂ g p ∧ ∀ᶠ z in 𝓝 p, h z ≠ 0 → g z = f z := by
  by_cases hh0 : h =ᶠ[𝓝 p] 0
  · exact ⟨0, analyticAt_const, hh0.mono fun _ hz hne ↦ (hne hz).elim⟩
  by_cases hp : h p ≠ 0
  · have hne : ∀ᶠ z in 𝓝 p, h z ≠ 0 :=
      hh.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hp)
    have hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z := (hne.and hf).mono fun _ ⟨h1, h2⟩ ↦ h2 h1
    exact ⟨f, DifferentiableOn.analyticAt_of_finiteDimensional (s := {z | DifferentiableAt ℂ f z})
      (fun _ hz ↦ hz.differentiableWithinAt) hdiff, Eventually.of_forall fun _ _ ↦ rfl⟩
  -- When `h p = 0`, `¬h =ᶠ[𝓝 p] 0` forces `E` to be nontrivial, hence `1 ≤ finrank ℂ E`.
  have hp0 : h p = 0 := not_ne_iff.1 hp
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact False.elim (hh0 (Eventually.of_forall fun z ↦ by rw [Subsingleton.elim z p, hp0]; rfl))
  have hpos := Module.finrank_pos (R := ℂ) (M := E)
  set m := Module.finrank ℂ E - 1
  have hfin : Module.finrank ℂ E = Module.finrank ℂ ((Fin m → ℂ) × ℂ) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]; omega
  set e : E ≃L[ℂ] (Fin m → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq hfin
  have hh_e : AnalyticAt ℂ (h ∘ e.symm) (e p) :=
    hh.comp_of_eq (e.symm.analyticAt (e p)) (e.symm_apply_apply p)
  have hh0_e : ¬(h ∘ e.symm) =ᶠ[𝓝 (e p)] 0 := fun h0 ↦ hh0 <|
    ((e.continuous.tendsto p).eventually h0).mono fun _ hz ↦ by simpa using hz
  obtain ⟨L, q, hLq, hord⟩ := hh_e.exists_continuousLinearEquiv_analyticOrderAt_ne_top hh0_e
  set Φ : ((Fin m → ℂ) × ℂ) ≃L[ℂ] E := L.trans e.symm
  have hΦq : Φ q = p := by simp [Φ, hLq]
  have hΦ_tend : Tendsto Φ (𝓝 q) (𝓝 p) := hΦq ▸ Φ.continuous.tendsto q
  have hΦ_within : Tendsto Φ (𝓝[{x | (h ∘ Φ) x ≠ 0}] q) (𝓝[{z | h z ≠ 0}] p) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hΦ_tend.mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin
  obtain ⟨G, hG_an, hG_eq⟩ := exists_analyticAt_prod_of_analyticAt_ne_zero
    (hh.comp_of_eq (Φ.analyticAt q) hΦq) (fun h0 ↦ hord (analyticOrderAt_eq_top.2 h0))
    ((hΦ_tend.eventually hf).mono fun x hx hne ↦ (hx hne).comp x Φ.differentiableAt)
    (hΦ_within.isBoundedUnder_comp hbdd)
  refine ⟨G ∘ Φ.symm, hG_an.comp_of_eq (Φ.symm.analyticAt p) (by simp [← hΦq]), ?_⟩
  have hΦinv : Tendsto Φ.symm (𝓝 p) (𝓝 q) := by simpa [← hΦq] using Φ.symm.continuous.tendsto p
  filter_upwards [hΦinv.eventually hG_eq] with z hz hne
  simpa [Function.comp_apply] using hz (by simpa [Function.comp_apply] using hne)

/-- **Canonical local Riemann extension.** Under the hypotheses of
`exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero`, the map
`z ↦ limUnder (𝓝[{w | h w ≠ 0}] z) f` is analytic at `p`. -/
theorem analyticAt_limUnder_of_analyticAt_ne_zero {h : E → ℂ} {f : E → F} {p : E}
    (hh : AnalyticAt ℂ h p)
    (hf : ∀ᶠ z in 𝓝 p, h z ≠ 0 → DifferentiableAt ℂ f z)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[{z | h z ≠ 0}] p) (norm ∘ f)) :
    AnalyticAt ℂ (fun z ↦ limUnder (𝓝[{w | h w ≠ 0}] z) f) p := by
  by_cases hh0 : h =ᶠ[𝓝 p] 0
  · refine (analyticAt_const (v := limUnder (⊥ : Filter E) f)).congr ?_
    filter_upwards [hh0.eventually_nhds] with z hz
    rw [nhdsWithin, inf_principal_eq_bot.2 (hz.mono fun _ hw ↦ not_not.2 hw)]
  obtain ⟨g, hg, hgf⟩ := exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero hh hf hbdd
  have hfg : f =ᶠ[𝓝[{w | h w ≠ 0}] p] g :=
    eventually_nhdsWithin_iff.2 (hgf.mono fun _ hz hne ↦ (hz hne).symm)
  have hcont : ∀ᶠ z in 𝓝 p, ContinuousWithinAt g {w | h w ≠ 0} z :=
    hg.eventually_analyticAt.mono fun _ hz ↦ hz.continuousAt.continuousWithinAt
  exact hg.congr
    (hfg.eventuallyEq_limUnder_nhdsWithin_of_closure_mem_nhds
      (hh.closure_setOf_ne_zero_mem_nhds hh0) hcont).symm

/-- **Existence of the limit across a removable analytic hypersurface.** Under the hypotheses of
`exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero`, `f` converges along
`𝓝[{z | h z ≠ 0}] p`. -/
theorem tendsto_limUnder_of_analyticAt_ne_zero {h : E → ℂ} {f : E → F} {p : E}
    (hh : AnalyticAt ℂ h p)
    (hf : ∀ᶠ z in 𝓝 p, h z ≠ 0 → DifferentiableAt ℂ f z)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[{z | h z ≠ 0}] p) (norm ∘ f)) :
    Tendsto f (𝓝[{z | h z ≠ 0}] p) (𝓝 (limUnder (𝓝[{z | h z ≠ 0}] p) f)) := by
  by_cases hh0 : h =ᶠ[𝓝 p] 0
  · rw [nhdsWithin, inf_principal_eq_bot.2 (hh0.mono fun _ hw ↦ not_not.2 hw)]
    exact tendsto_bot
  obtain ⟨g, hg, hgf⟩ := exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero hh hf hbdd
  have : (𝓝[{z | h z ≠ 0}] p).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_iff_frequently.2 (not_eventually.1 hh0))
  have hlim : Tendsto f (𝓝[{z | h z ≠ 0}] p) (𝓝 (g p)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_iff.2 hgf)
  rwa [hlim.limUnder_eq]

end Local

/-! ### Global Riemann extension on open sets -/

section Global

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Canonical global Riemann extension on an open set.** Let `U ⊆ E` be open and `A ⊆ E` be
locally contained in the zero set of a non-identically-zero analytic function at every point of
`U`. If `f : E → F` is complex differentiable on `U \ A` and locally bounded near every point of
`U ∩ A`, then `x ↦ limUnder (𝓝[U \ A] x) f` is analytic on `U` (and agrees with `f` on `U \ A`).
-/
theorem analyticOnNhd_limUnder_of_locally_analytic_zero {f : E → F} {U A : Set E} (hU : IsOpen U)
    (hA : ∀ x ∈ U, ∃ h : E → ℂ, AnalyticAt ℂ h x ∧ ¬h =ᶠ[𝓝 x] 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ A → h z = 0)
    (hf : DifferentiableOn ℂ f (U \ A))
    (hbdd : ∀ x ∈ U ∩ A, IsBoundedUnder (· ≤ ·) (𝓝[U \ A] x) (norm ∘ f)) :
    AnalyticOnNhd ℂ (fun x ↦ limUnder (𝓝[U \ A] x) f) U := by
  intro x hx
  obtain ⟨h, hh, hh0, hAh⟩ := hA x hx
  -- Choose an open neighbourhood `V ⊆ U` of `x` on which `h` is continuous and vanishes on `A`.
  obtain ⟨V, hV_prop, hV_open, hxV⟩ := _root_.eventually_nhds_iff.1 <|
    (Filter.eventually_of_mem (hU.mem_nhds hx) fun _ hz ↦ hz).and
      (hh.eventually_analyticAt.and hAh)
  set W : Set E := V ∩ {z | h z ≠ 0}
  have hh_cont : ContinuousOn h V := fun z hz ↦ (hV_prop z hz).2.1.continuousAt.continuousWithinAt
  have hW_open : IsOpen W := hh_cont.isOpen_inter_preimage hV_open isOpen_ne
  have hW_sub : W ⊆ U \ A := fun z ⟨hzV, hne⟩ ↦
    ⟨(hV_prop z hzV).1, fun hzA ↦ hne ((hV_prop z hzV).2.2 hzA)⟩
  have hf_local : ∀ᶠ z in 𝓝 x, h z ≠ 0 → DifferentiableAt ℂ f z := by
    filter_upwards [hV_open.mem_nhds hxV] with z hzV hne
    exact (hf z (hW_sub ⟨hzV, hne⟩)).differentiableAt
      (Filter.mem_of_superset (hW_open.mem_nhds ⟨hzV, hne⟩) hW_sub)
  have hbdd_x : IsBoundedUnder (· ≤ ·) (𝓝[U \ A] x) (norm ∘ f) := by
    by_cases hxA : x ∈ A
    exacts [hbdd x ⟨hx, hxA⟩, (hf.continuousOn x ⟨hx, hxA⟩).norm.isBoundedUnder_le]
  have hle : 𝓝[{z | h z ≠ 0}] x ≤ 𝓝[U \ A] x := nhdsWithin_le_iff.2 <| by
    filter_upwards [nhdsWithin_le_nhds (hV_open.mem_nhds hxV), self_mem_nhdsWithin] with z hzV hne
    exact hW_sub ⟨hzV, hne⟩
  obtain ⟨g, hg, hgf⟩ :=
    exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero hh hf_local (hbdd_x.mono hle)
  -- `W` is locally dense near `x`, so `g` agrees with `f` on `U \ A` near `x`, hence with
  -- `limUnder`.
  have hW_closure : closure W ∈ 𝓝 x := Filter.mem_of_superset
    (inter_mem (hV_open.mem_nhds hxV) (hh.closure_setOf_ne_zero_mem_nhds hh0)) hV_open.inter_closure
  have hfg_W : f =ᶠ[𝓝[W] x] g :=
    eventually_nhdsWithin_iff.2 (hgf.mono fun _ hz hW ↦ (hz hW.2).symm)
  have hfg_UA : f =ᶠ[𝓝[U \ A] x] g :=
    hfg_W.nhdsWithin_of_subset_of_closure_mem_nhdsWithin hW_sub (nhdsWithin_le_nhds hW_closure)
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall fun z hz ↦ hf.continuousOn z hz)
      ((hg.eventually_analyticAt.mono fun _ hz ↦ hz.continuousAt.continuousWithinAt).filter_mono
        nhdsWithin_le_nhds)
  exact hg.congr (hfg_UA.eventuallyEq_limUnder_nhdsWithin_of_closure_mem_nhds
    (Filter.mem_of_superset hW_closure (closure_mono hW_sub))
    (hg.eventually_analyticAt.mono fun _ hz ↦ hz.continuousAt.continuousWithinAt)).symm

/-- **Riemann's extension theorem on an open set.** Let `U ⊆ E` be open and `A ⊆ E` be locally
contained in the zero set of a non-identically-zero analytic function at every point of `U`. Any
map `f : E → F` into a complete complex normed space that is complex differentiable on `U \ A` and
locally bounded near every point of `U ∩ A` extends to an analytic map on `U`. Such an extension is
unique on `U` by `Set.EqOn.of_subset_closure`. -/
theorem exists_analyticOnNhd_eqOn_sdiff_of_locally_analytic_zero {f : E → F} {U A : Set E}
    (hU : IsOpen U)
    (hA : ∀ x ∈ U, ∃ h : E → ℂ, AnalyticAt ℂ h x ∧ ¬h =ᶠ[𝓝 x] 0 ∧
      ∀ᶠ z in 𝓝 x, z ∈ A → h z = 0)
    (hf : DifferentiableOn ℂ f (U \ A))
    (hbdd : ∀ x ∈ U ∩ A, IsBoundedUnder (· ≤ ·) (𝓝[U \ A] x) (norm ∘ f)) :
    ∃ g : E → F, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ A) :=
  ⟨fun x ↦ limUnder (𝓝[U \ A] x) f,
    analyticOnNhd_limUnder_of_locally_analytic_zero hU hA hf hbdd, fun x hx ↦ by
      have := nhdsWithin_neBot_of_mem hx
      exact (hf.continuousOn x hx).limUnder_eq⟩

/-- **Riemann's extension theorem across the common zero set of a family of holomorphic
functions.** Let `U ⊆ E` be open, `g : ι → E → ℂ` an arbitrary family of holomorphic functions on
`U` whose common zero set `A = {z | ∀ i, g i z = 0}` has empty interior in `U`, and `f : E → F` a
map into a complete complex normed space that is complex differentiable on `U \ A` and locally
bounded near every point of `U ∩ A`. Then `f` extends to an analytic (hence complex differentiable)
map on `U`. -/
theorem exists_analyticOnNhd_eqOn_sdiff_iInter_zero {ι : Type*} {g : ι → E → ℂ}
    {f : E → F} {U : Set E} (hU : IsOpen U) (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    (hA : interior {z ∈ U | ∀ i, g i z = 0} = ∅)
    (hf : DifferentiableOn ℂ f (U \ {z | ∀ i, g i z = 0}))
    (hbdd : ∀ x ∈ U ∩ {z | ∀ i, g i z = 0},
      IsBoundedUnder (· ≤ ·) (𝓝[U \ {z | ∀ i, g i z = 0}] x) (norm ∘ f)) :
    ∃ G : E → F, AnalyticOnNhd ℂ G U ∧ EqOn G f (U \ {z | ∀ i, g i z = 0}) := by
  refine exists_analyticOnNhd_eqOn_sdiff_of_locally_analytic_zero hU (fun x hx ↦ ?_) hf hbdd
  have hex : ∃ i, ¬g i =ᶠ[𝓝 x] 0 := by
    by_contra! h0
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hsub : ball x r ⊆ {z ∈ U | ∀ i, g i z = 0} := fun z hz ↦
      ⟨hball hz, fun i ↦
        (((hg i).analyticOnNhd_of_finiteDimensional hU).mono hball)
          |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball x r).isPreconnected
            (mem_ball_self hr) (h0 i) hz⟩
    have hmem : x ∈ interior {z ∈ U | ∀ i, g i z = 0} :=
      mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (ball_mem_nhds x hr) hsub)
    rw [hA] at hmem
    exact hmem
  obtain ⟨i, hi⟩ := hex
  exact ⟨g i, (hg i).analyticAt_of_finiteDimensional (hU.mem_nhds hx), hi,
    Eventually.of_forall fun _ hz ↦ hz i⟩

/-- **Riemann's extension theorem across a holomorphic hypersurface.** Let `U ⊆ E` be open and
`h : E → ℂ` holomorphic on `U` with `interior {z ∈ U | h z = 0} = ∅`. Any map `f : E → F` into a
complete complex normed space that is complex differentiable on `U \ {z | h z = 0}` and locally
bounded near every zero of `h` in `U` extends to an analytic map on `U`. -/
theorem exists_analyticOnNhd_eqOn_sdiff_zero {h : E → ℂ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (hA : interior {z ∈ U | h z = 0} = ∅)
    (hf : DifferentiableOn ℂ f (U \ {z | h z = 0}))
    (hbdd : ∀ x ∈ U ∩ {z | h z = 0},
      IsBoundedUnder (· ≤ ·) (𝓝[U \ {z | h z = 0}] x) (norm ∘ f)) :
    ∃ G : E → F, AnalyticOnNhd ℂ G U ∧ EqOn G f (U \ {z | h z = 0}) := by
  have := exists_analyticOnNhd_eqOn_sdiff_iInter_zero (g := fun _ : Unit ↦ h) hU
    (fun _ ↦ hh) (by simpa using hA) (by simpa using hf) (by simpa using hbdd)
  simpa using this

/-- **Global Riemann extension across the common zero set of an arbitrary family of entire
functions.** -/
theorem exists_differentiable_eqOn_compl_iInter_zero {ι : Type*} {g : ι → E → ℂ}
    {f : E → F} (hg : ∀ i, Differentiable ℂ (g i)) (hA : interior {z | ∀ i, g i z = 0} = ∅)
    (hf : DifferentiableOn ℂ f {z | ∀ i, g i z = 0}ᶜ)
    (hbdd : ∀ x ∈ {z | ∀ i, g i z = 0},
      IsBoundedUnder (· ≤ ·) (𝓝[{z | ∀ i, g i z = 0}ᶜ] x) (norm ∘ f)) :
    ∃ G : E → F, Differentiable ℂ G ∧ EqOn G f {z | ∀ i, g i z = 0}ᶜ := by
  obtain ⟨G, hG, hGf⟩ := exists_analyticOnNhd_eqOn_sdiff_iInter_zero isOpen_univ
    (fun i ↦ (hg i).differentiableOn) (by simpa using hA) (by simpa [compl_eq_univ_sdiff] using hf)
    (by simpa [compl_eq_univ_sdiff] using hbdd)
  exact ⟨G, differentiableOn_univ.1 hG.differentiableOn, by simpa [compl_eq_univ_sdiff] using hGf⟩

/-- **Global Riemann extension across the zero set of a single entire function.** -/
theorem exists_differentiable_eqOn_compl_zero {h : E → ℂ} {f : E → F} (hh : Differentiable ℂ h)
    (hA : interior {z | h z = 0} = ∅) (hf : DifferentiableOn ℂ f {z | h z = 0}ᶜ)
    (hbdd : ∀ x ∈ {z | h z = 0}, IsBoundedUnder (· ≤ ·) (𝓝[{z | h z = 0}ᶜ] x) (norm ∘ f)) :
    ∃ G : E → F, Differentiable ℂ G ∧ EqOn G f {z | h z = 0}ᶜ := by
  have := exists_differentiable_eqOn_compl_iInter_zero (g := fun _ : Unit ↦ h) (fun _ ↦ hh)
    (by simpa using hA) (by simpa using hf) (by simpa using hbdd)
  simpa using this

end Global

end TauCeti
