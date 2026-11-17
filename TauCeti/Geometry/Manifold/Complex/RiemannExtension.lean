/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Order.LiminfLimsup
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.RiemannExtension
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Topology.ContinuousOn.Dense

/-!
# Riemann's removable singularity theorem on complex manifolds

On a boundaryless complex manifold `M` modelled on a finite-dimensional complex normed space `E`,
let `U ⊆ M` be open and `A ⊆ M` be locally contained in the zero set of a non-identically-zero
`C^ω` (equivalently, locally holomorphic) function at every point of `U` (for instance, the common
zero set of an arbitrary family of holomorphic functions on `U` with empty interior). **Riemann's
extension theorem** states that any map `f : M → F` into a complete complex normed space that is
holomorphic on `U \ A` and locally bounded near every point of `U ∩ A` extends to a `C^ω` (hence
holomorphic) map on `U`, with no Hausdorffness or second-countability hypothesis on `M`.

Reading a map in the preferred extended chart `extChartAt I p` reduces the local statement at `p`
to `TauCeti.exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero` on the model space `E`, via
`mdifferentiableWithinAt_extChartAt_symm` and `TauCeti.contMDiffAt_omega_iff_analyticAt`. Patching
local extensions canonically via `x ↦ limUnder (𝓝[U \ A] x) f` using
`Filter.EventuallyEq.eventuallyEq_limUnder_nhdsWithin_of_closure_mem_nhds` then extends holomorphic
maps on `U \ A` across `A` without assuming `A` is closed in `U`. Since `U ⊆ closure (U \ A)`, any
continuous extension to `U` is unique by `Set.EqOn.of_subset_closure`.

## Main results

* `TauCeti.exists_contMDiffAt_omega_and_eventually_eq_of_contMDiffAt_ne_zero`,
  `TauCeti.contMDiffAt_omega_limUnder_of_contMDiffAt_ne_zero`,
  `TauCeti.tendsto_limUnder_of_contMDiffAt_ne_zero`: **local Riemann extension** at a point of a
  complex manifold across the zero locus of a `C^ω` function.
* `TauCeti.contMDiffOn_omega_limUnder_of_locally_contMDiffAt_zero`,
  `TauCeti.exists_mdifferentiableOn_eqOn_sdiff_of_locally_contMDiffAt_zero`: **global Riemann
  extension** on an open set `U` across any set locally contained in nontrivial holomorphic
  hypersurfaces.
* `TauCeti.exists_mdifferentiableOn_eqOn_sdiff_iInter_zero`,
  `TauCeti.exists_mdifferentiableOn_eqOn_sdiff_zero`: extension on an open set across the common
  zero set of an arbitrary family of holomorphic functions (or a single holomorphic function) with
  empty interior.
* `TauCeti.exists_mdifferentiable_eqOn_compl_iInter_zero`,
  `TauCeti.exists_mdifferentiable_eqOn_compl_zero`: global holomorphic extensions on `M`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §4, Theorem 4.2.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I, §C,
  Theorem 3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.3.
-/

public section

open Filter Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-! ### Local Riemann extension on complex manifolds -/

/-- **Local Riemann extension theorem on complex manifolds.** Let `M` be a boundaryless complex
manifold modelled on a finite-dimensional complex normed space `E`, `F` a complete complex normed
space, and `h : M → ℂ` a `C^ω` (equivalently, locally holomorphic) function at `p`. Any map
`f : M → F` that is holomorphic and locally bounded on `{x | h x ≠ 0}` near `p` agrees on
`{x | h x ≠ 0}` near `p` with a map `C^ω` at `p`. (If `h` vanishes identically near `p`, the
conclusion holds trivially with `g = 0`.) -/
theorem exists_contMDiffAt_omega_and_eventually_eq_of_contMDiffAt_ne_zero {h : M → ℂ} {f : M → F}
    {p : M} (hh : ContMDiffAt I 𝓘(ℂ) ω h p)
    (hf : ∀ᶠ x in 𝓝 p, h x ≠ 0 → MDifferentiableAt I 𝓘(ℂ, F) f x)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[{x | h x ≠ 0}] p) (norm ∘ f)) :
    ∃ g : M → F, ContMDiffAt I 𝓘(ℂ, F) ω g p ∧ ∀ᶠ x in 𝓝 p, h x ≠ 0 → g x = f x := by
  set e := extChartAt I p
  have htgt : e.target ∈ 𝓝 (e p) := extChartAt_target_mem_nhds p
  have hsymm_tend : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    have h₁ : Tendsto e.symm (𝓝 (e p)) (𝓝 (e.symm (e p))) :=
      (continuousAt_extChartAt_symm p).tendsto
    rwa [extChartAt_to_inv] at h₁
  have hh_an : AnalyticAt ℂ (h ∘ e.symm) (e p) := contMDiffAt_omega_iff_analyticAt.1 hh
  have hd : ∀ᶠ z in 𝓝 (e p), (h ∘ e.symm) z ≠ 0 → DifferentiableAt ℂ (f ∘ e.symm) z := by
    filter_upwards [htgt, hsymm_tend.eventually hf] with z hzt hmd hne
    exact (((hmd hne).comp_mdifferentiableWithinAt z
      (mdifferentiableWithinAt_extChartAt_symm hzt)).mdifferentiableAt
      (I.range_eq_univ ▸ univ_mem)).differentiableAt
  have hsymm_within : Tendsto e.symm (𝓝[{z | (h ∘ e.symm) z ≠ 0}] (e p)) (𝓝[{x | h x ≠ 0}] p) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsymm_tend.mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin
  obtain ⟨G, hG_an, hG_eq⟩ := exists_analyticAt_and_eventually_eq_of_analyticAt_ne_zero hh_an hd
    (hsymm_within.isBoundedUnder_comp hbdd)
  refine ⟨G ∘ e, contMDiffAt_omega_iff_analyticAt.2 (hG_an.congr ?_), ?_⟩
  · filter_upwards [htgt] with z hzt
    exact (congrArg G (e.right_inv hzt)).symm
  · filter_upwards [extChartAt_source_mem_nhds (I := I) p,
      (continuousAt_extChartAt (I := I) p).tendsto.eventually hG_eq] with x hxs hGx hne
    have hinv : e.symm (extChartAt I p x) = x := e.left_inv hxs
    exact (hGx (by simpa only [Function.comp_apply, hinv] using hne)).trans (congrArg f hinv)

/-- **Canonical local Riemann extension on complex manifolds.** Under the hypotheses of
`exists_contMDiffAt_omega_and_eventually_eq_of_contMDiffAt_ne_zero`, the map
`x ↦ limUnder (𝓝[{y | h y ≠ 0}] x) f` is `C^ω` at `p`. -/
theorem contMDiffAt_omega_limUnder_of_contMDiffAt_ne_zero {h : M → ℂ} {f : M → F} {p : M}
    (hh : ContMDiffAt I 𝓘(ℂ) ω h p)
    (hf : ∀ᶠ x in 𝓝 p, h x ≠ 0 → MDifferentiableAt I 𝓘(ℂ, F) f x)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[{x | h x ≠ 0}] p) (norm ∘ f)) :
    ContMDiffAt I 𝓘(ℂ, F) ω (fun x ↦ limUnder (𝓝[{y | h y ≠ 0}] x) f) p := by
  by_cases hh0 : h =ᶠ[𝓝 p] 0
  · refine (contMDiffAt_const (c := limUnder (⊥ : Filter M) f)).congr_of_eventuallyEq ?_
    filter_upwards [hh0.eventually_nhds] with x hx
    rw [nhdsWithin, inf_principal_eq_bot.2 (hx.mono fun _ hy ↦ not_not.2 hy)]
  obtain ⟨g, hg, hgf⟩ :=
    exists_contMDiffAt_omega_and_eventually_eq_of_contMDiffAt_ne_zero hh hf hbdd
  have hfg : f =ᶠ[𝓝[{y | h y ≠ 0}] p] g :=
    eventually_nhdsWithin_iff.2 (hgf.mono fun _ hx hne ↦ (hx hne).symm)
  have hcont : ∀ᶠ x in 𝓝 p, ContinuousWithinAt g {y | h y ≠ 0} x :=
    ((contMDiffAt_iff_eventually_mdifferentiableAt (by simp)).1 hg).mono fun _ hx ↦
      hx.continuousAt.continuousWithinAt
  exact hg.congr_of_eventuallyEq
    (hfg.eventuallyEq_limUnder_nhdsWithin_of_closure_mem_nhds
      (hh.closure_setOf_ne_zero_mem_nhds hh0) hcont)

/-- **Existence of the limit across a removable holomorphic hypersurface on a complex manifold.**
Under the hypotheses of `exists_contMDiffAt_omega_and_eventually_eq_of_contMDiffAt_ne_zero`, `f`
converges along `𝓝[{x | h x ≠ 0}] p`. -/
theorem tendsto_limUnder_of_contMDiffAt_ne_zero {h : M → ℂ} {f : M → F} {p : M}
    (hh : ContMDiffAt I 𝓘(ℂ) ω h p)
    (hf : ∀ᶠ x in 𝓝 p, h x ≠ 0 → MDifferentiableAt I 𝓘(ℂ, F) f x)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[{x | h x ≠ 0}] p) (norm ∘ f)) :
    Tendsto f (𝓝[{x | h x ≠ 0}] p) (𝓝 (limUnder (𝓝[{x | h x ≠ 0}] p) f)) := by
  by_cases hh0 : h =ᶠ[𝓝 p] 0
  · rw [nhdsWithin, inf_principal_eq_bot.2 (hh0.mono fun _ hy ↦ not_not.2 hy)]
    exact tendsto_bot
  obtain ⟨g, hg, hgf⟩ :=
    exists_contMDiffAt_omega_and_eventually_eq_of_contMDiffAt_ne_zero hh hf hbdd
  have : (𝓝[{x | h x ≠ 0}] p).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_iff_frequently.2 (not_eventually.1 hh0))
  have hlim : Tendsto f (𝓝[{x | h x ≠ 0}] p) (𝓝 (g p)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_iff.2 hgf)
  rwa [hlim.limUnder_eq]

/-! ### Global Riemann extension on open sets and complex manifolds -/

/-- **Canonical global Riemann extension on an open subset of a complex manifold.** Let `U ⊆ M` be
open and `A ⊆ M` be locally contained in the zero set of a non-identically-zero `C^ω` function at
every point of `U`. If `f : M → F` is holomorphic on `U \ A` and locally bounded near every point
of `U ∩ A`, then `x ↦ limUnder (𝓝[U \ A] x) f` is `C^ω` on `U` (and agrees with `f` on `U \ A`).
-/
theorem contMDiffOn_omega_limUnder_of_locally_contMDiffAt_zero {f : M → F} {U A : Set M}
    (hU : IsOpen U)
    (hA : ∀ x ∈ U, ∃ h : M → ℂ, ContMDiffAt I 𝓘(ℂ) ω h x ∧ ¬h =ᶠ[𝓝 x] 0 ∧
      ∀ᶠ y in 𝓝 x, y ∈ A → h y = 0)
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f (U \ A))
    (hbdd : ∀ x ∈ U ∩ A, IsBoundedUnder (· ≤ ·) (𝓝[U \ A] x) (norm ∘ f)) :
    ContMDiffOn I 𝓘(ℂ, F) ω (fun x ↦ limUnder (𝓝[U \ A] x) f) U := by
  intro x hx
  obtain ⟨h, hh, hh0, hAh⟩ := hA x hx
  -- Choose an open neighbourhood `V ⊆ U` of `x` on which `h` is continuous and vanishes on `A`.
  have hh_ev : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℂ) h y :=
    (contMDiffAt_iff_eventually_mdifferentiableAt (by simp)).1 hh
  obtain ⟨V, hV_prop, hV_open, hxV⟩ := eventually_nhds_iff.1 <|
    (Filter.eventually_of_mem (hU.mem_nhds hx) fun _ hy ↦ hy).and (hh_ev.and hAh)
  set W : Set M := V ∩ {y | h y ≠ 0}
  have hh_cont : ContinuousOn h V := fun y hy ↦ (hV_prop y hy).2.1.continuousAt.continuousWithinAt
  have hW_open : IsOpen W := hh_cont.isOpen_inter_preimage hV_open isOpen_ne
  have hW_sub : W ⊆ U \ A := fun y ⟨hyV, hne⟩ ↦
    ⟨(hV_prop y hyV).1, fun hyA ↦ hne ((hV_prop y hyV).2.2 hyA)⟩
  have hf_local : ∀ᶠ y in 𝓝 x, h y ≠ 0 → MDifferentiableAt I 𝓘(ℂ, F) f y := by
    filter_upwards [hV_open.mem_nhds hxV] with y hyV hne
    exact (hf y (hW_sub ⟨hyV, hne⟩)).mdifferentiableAt
      (Filter.mem_of_superset (hW_open.mem_nhds ⟨hyV, hne⟩) hW_sub)
  have hbdd_x : IsBoundedUnder (· ≤ ·) (𝓝[U \ A] x) (norm ∘ f) := by
    by_cases hxA : x ∈ A
    exacts [hbdd x ⟨hx, hxA⟩, (hf.continuousOn x ⟨hx, hxA⟩).norm.isBoundedUnder_le]
  have hle : 𝓝[{y | h y ≠ 0}] x ≤ 𝓝[U \ A] x := nhdsWithin_le_iff.2 <| by
    filter_upwards [nhdsWithin_le_nhds (hV_open.mem_nhds hxV), self_mem_nhdsWithin] with y hyV hne
    exact hW_sub ⟨hyV, hne⟩
  obtain ⟨g, hg, hgf⟩ :=
    exists_contMDiffAt_omega_and_eventually_eq_of_contMDiffAt_ne_zero hh hf_local (hbdd_x.mono hle)
  have hW_closure : closure W ∈ 𝓝 x := Filter.mem_of_superset
    (inter_mem (hV_open.mem_nhds hxV) (hh.closure_setOf_ne_zero_mem_nhds hh0)) hV_open.inter_closure
  have hg_ev : ∀ᶠ y in 𝓝 x, ContinuousWithinAt g W y :=
    ((contMDiffAt_iff_eventually_mdifferentiableAt (by simp)).1 hg).mono fun _ hy ↦
      hy.continuousAt.continuousWithinAt
  have hfg_W : f =ᶠ[𝓝[W] x] g := eventually_nhdsWithin_iff.2 (hgf.mono fun _ hy hW ↦ (hy hW.2).symm)
  have hfg_UA : f =ᶠ[𝓝[U \ A] x] g :=
    hfg_W.nhdsWithin_of_subset_of_closure_mem_nhdsWithin hW_sub (nhdsWithin_le_nhds hW_closure)
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall fun y hy ↦ hf.continuousOn y hy)
      (hg_ev.filter_mono nhdsWithin_le_nhds)
  exact (hg.congr_of_eventuallyEq (hfg_UA.eventuallyEq_limUnder_nhdsWithin_of_closure_mem_nhds
    (Filter.mem_of_superset hW_closure (closure_mono hW_sub))
    (((contMDiffAt_iff_eventually_mdifferentiableAt (by simp)).1 hg).mono fun _ hy ↦
      hy.continuousAt.continuousWithinAt))).contMDiffWithinAt

/-- **Riemann's extension theorem on an open subset of a complex manifold.** Let `U ⊆ M` be open
and `A ⊆ M` be locally contained in the zero set of a non-identically-zero `C^ω` function at every
point of `U`. Any map `f : M → F` into a complete complex normed space that is holomorphic on
`U \ A` and locally bounded near every point of `U ∩ A` extends to a holomorphic (hence `C^ω`, by
`MDifferentiableOn.contMDiffOn`) map on `U`. Such an extension is unique on `U` by
`Set.EqOn.of_subset_closure`. -/
theorem exists_mdifferentiableOn_eqOn_sdiff_of_locally_contMDiffAt_zero {f : M → F} {U A : Set M}
    (hU : IsOpen U)
    (hA : ∀ x ∈ U, ∃ h : M → ℂ, ContMDiffAt I 𝓘(ℂ) ω h x ∧ ¬h =ᶠ[𝓝 x] 0 ∧
      ∀ᶠ y in 𝓝 x, y ∈ A → h y = 0)
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f (U \ A))
    (hbdd : ∀ x ∈ U ∩ A, IsBoundedUnder (· ≤ ·) (𝓝[U \ A] x) (norm ∘ f)) :
    ∃ g : M → F, MDifferentiableOn I 𝓘(ℂ, F) g U ∧ EqOn g f (U \ A) :=
  ⟨fun x ↦ limUnder (𝓝[U \ A] x) f,
    (contMDiffOn_omega_limUnder_of_locally_contMDiffAt_zero hU hA hf hbdd).mdifferentiableOn
      (by simp),
    fun x hx ↦ by
      have := nhdsWithin_neBot_of_mem hx
      exact (hf.continuousOn x hx).limUnder_eq⟩

/-- **Riemann's extension theorem across the common zero set of a family of holomorphic functions
on an open subset of a complex manifold.** Let `U ⊆ M` be open, `g : ι → M → ℂ` an arbitrary family
of holomorphic functions on `U` whose common zero set `A = {x | ∀ i, g i x = 0}` has empty interior
in `U`, and `f : M → F` a map into a complete complex normed space that is holomorphic on `U \ A`
and locally bounded near every point of `U ∩ A`. Then `f` extends to a holomorphic (hence `C^ω`)
map on `U`. -/
theorem exists_mdifferentiableOn_eqOn_sdiff_iInter_zero {ι : Type*} {g : ι → M → ℂ}
    {f : M → F} {U : Set M} (hU : IsOpen U) (hg : ∀ i, MDifferentiableOn I 𝓘(ℂ) (g i) U)
    (hA : interior {x ∈ U | ∀ i, g i x = 0} = ∅)
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f (U \ {x | ∀ i, g i x = 0}))
    (hbdd : ∀ x ∈ U ∩ {x | ∀ i, g i x = 0},
      IsBoundedUnder (· ≤ ·) (𝓝[U \ {x | ∀ i, g i x = 0}] x) (norm ∘ f)) :
    ∃ G : M → F, MDifferentiableOn I 𝓘(ℂ, F) G U ∧ EqOn G f (U \ {x | ∀ i, g i x = 0}) := by
  refine exists_mdifferentiableOn_eqOn_sdiff_of_locally_contMDiffAt_zero hU (fun x hx ↦ ?_) hf hbdd
  have hex : ∃ i, ¬g i =ᶠ[𝓝 x] 0 := by
    by_contra! h0
    set c := extChartAt I x
    have hmem_nhds : c.target ∩ c.symm ⁻¹' U ∈ 𝓝 (c x) :=
      inter_mem (extChartAt_target_mem_nhds x) (extChartAt_preimage_mem_nhds (hU.mem_nhds hx))
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.1 hmem_nhds
    have hsymm_tend : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      have h₁ : Tendsto c.symm (𝓝 (c x)) (𝓝 (c.symm (c x))) :=
        (continuousAt_extChartAt_symm x).tendsto
      rwa [extChartAt_to_inv] at h₁
    have hvanish (i : ι) : EqOn (g i ∘ c.symm) 0 (ball (c x) r) := by
      have hdiff : DifferentiableOn ℂ (g i ∘ c.symm) (ball (c x) r) := fun z hz ↦
        ((((hg i _ (hball hz).2).mdifferentiableAt (hU.mem_nhds (hball hz).2))
          |>.comp_mdifferentiableWithinAt z (mdifferentiableWithinAt_extChartAt_symm (hball hz).1))
          |>.mdifferentiableAt (I.range_eq_univ ▸ univ_mem)).differentiableAt.differentiableWithinAt
      exact (hdiff.analyticOnNhd_of_finiteDimensional isOpen_ball)
        |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (c x) r).isPreconnected
          (mem_ball_self hr) (hsymm_tend.eventually (h0 i))
    have hnhds : c.source ∩ c ⁻¹' ball (c x) r ∈ 𝓝 x :=
      inter_mem (extChartAt_source_mem_nhds (I := I) x)
        ((continuousAt_extChartAt (I := I) x).preimage_mem_nhds (ball_mem_nhds _ hr))
    have hsub : c.source ∩ c ⁻¹' ball (c x) r ⊆ {y ∈ U | ∀ i, g i y = 0} := fun y ⟨hys, hyb⟩ ↦ by
      have hinv : c.symm (c y) = y := c.left_inv hys
      exact ⟨hinv ▸ (hball hyb).2, fun i ↦ by simpa [hinv] using hvanish i hyb⟩
    have hmem : x ∈ interior {y ∈ U | ∀ i, g i y = 0} :=
      mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hnhds hsub)
    rw [hA] at hmem
    exact hmem
  obtain ⟨i, hi⟩ := hex
  exact ⟨g i, ((hg i).contMDiffOn hU).contMDiffAt (hU.mem_nhds hx), hi,
    Eventually.of_forall fun _ hy ↦ hy i⟩

/-- **Riemann's extension theorem across a holomorphic hypersurface on an open subset of a complex
manifold.** Let `U ⊆ M` be open and `h : M → ℂ` holomorphic on `U` with
`interior {x ∈ U | h x = 0} = ∅`. Any map `f : M → F` into a complete complex normed space that is
holomorphic on `U \ {x | h x = 0}` and locally bounded near every zero of `h` in `U` extends to a
holomorphic map on `U`. -/
theorem exists_mdifferentiableOn_eqOn_sdiff_zero {h : M → ℂ} {f : M → F} {U : Set M} (hU : IsOpen U)
    (hh : MDifferentiableOn I 𝓘(ℂ) h U) (hA : interior {x ∈ U | h x = 0} = ∅)
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f (U \ {x | h x = 0}))
    (hbdd : ∀ x ∈ U ∩ {x | h x = 0},
      IsBoundedUnder (· ≤ ·) (𝓝[U \ {x | h x = 0}] x) (norm ∘ f)) :
    ∃ G : M → F, MDifferentiableOn I 𝓘(ℂ, F) G U ∧ EqOn G f (U \ {x | h x = 0}) := by
  have := exists_mdifferentiableOn_eqOn_sdiff_iInter_zero (g := fun _ : Unit ↦ h) hU
    (fun _ ↦ hh) (by simpa using hA) (by simpa using hf) (by simpa using hbdd)
  simpa using this

/-- **Global Riemann extension across the common zero set of an arbitrary family of holomorphic
functions on a complex manifold.** -/
theorem exists_mdifferentiable_eqOn_compl_iInter_zero {ι : Type*} {g : ι → M → ℂ}
    {f : M → F} (hg : ∀ i, MDifferentiable I 𝓘(ℂ) (g i)) (hA : interior {x | ∀ i, g i x = 0} = ∅)
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f {x | ∀ i, g i x = 0}ᶜ)
    (hbdd : ∀ x ∈ {x | ∀ i, g i x = 0},
      IsBoundedUnder (· ≤ ·) (𝓝[{x | ∀ i, g i x = 0}ᶜ] x) (norm ∘ f)) :
    ∃ G : M → F, MDifferentiable I 𝓘(ℂ, F) G ∧ EqOn G f {x | ∀ i, g i x = 0}ᶜ := by
  obtain ⟨G, hG, hGf⟩ := exists_mdifferentiableOn_eqOn_sdiff_iInter_zero isOpen_univ
    (fun i ↦ (hg i).mdifferentiableOn) (by simpa using hA) (by simpa [compl_eq_univ_sdiff] using hf)
    (by simpa [compl_eq_univ_sdiff] using hbdd)
  exact ⟨G, mdifferentiableOn_univ.1 hG, by simpa [compl_eq_univ_sdiff] using hGf⟩

/-- **Global Riemann extension across the zero set of a single holomorphic function on a complex
manifold.** -/
theorem exists_mdifferentiable_eqOn_compl_zero {h : M → ℂ} {f : M → F}
    (hh : MDifferentiable I 𝓘(ℂ) h) (hA : interior {x | h x = 0} = ∅)
    (hf : MDifferentiableOn I 𝓘(ℂ, F) f {x | h x = 0}ᶜ)
    (hbdd : ∀ x ∈ {x | h x = 0}, IsBoundedUnder (· ≤ ·) (𝓝[{x | h x = 0}ᶜ] x) (norm ∘ f)) :
    ∃ G : M → F, MDifferentiable I 𝓘(ℂ, F) G ∧ EqOn G f {x | h x = 0}ᶜ := by
  have := exists_mdifferentiable_eqOn_compl_iInter_zero (g := fun _ : Unit ↦ h) (fun _ ↦ hh)
    (by simpa using hA) (by simpa using hf) (by simpa using hbdd)
  simpa using this

end Manifold

end TauCeti
