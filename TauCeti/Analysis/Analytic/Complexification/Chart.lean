/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Complexification.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Analysis.Analytic.Complexification.Neighborhood

/-!
# Complexification of analytic charts

A real analytic chart and its analytic inverse extend together to a holomorphic chart near each
real point of its source (`OpenPartialHomeomorph.exists_complexification`), or simultaneously over
its entire open source (`OpenPartialHomeomorph.exists_complexification_of_analyticOnNhd`). The
complex chart and its inverse agree with the original maps on the corresponding real points and
commute with conjugation. This allows changes to analytic coordinates before applying holomorphic
polynomial root theorems, and supplies complexified transition maps when gluing real-analytic
atlases into complex manifolds.

The identity theorem on real points transports the two inverse identities to complex
neighborhoods. Restricting those neighborhoods then gives an open partial homeomorphism; no
choice of a derivative or complex linear extension of a derivative is needed.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public section

open Filter Function Metric Set Topology

namespace OpenPartialHomeomorph

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A real chart analytic at a source point, with inverse analytic at its image, extends to a
complex chart analytic on its source with analytic inverse on its target. Both maps agree with
the original chart near the real points and commute with conjugation at every complex point. -/
theorem exists_complexification (e : OpenPartialHomeomorph (ι → ℝ) (κ → ℝ))
    {a : ι → ℝ} (ha : a ∈ e.source) (he : AnalyticAt ℝ e a)
    (he' : AnalyticAt ℝ e.symm (e a)) :
    ∃ E : OpenPartialHomeomorph (ι → ℂ) (κ → ℂ),
      (fun i ↦ (a i : ℂ)) ∈ E.source ∧
      AnalyticOnNhd ℂ E E.source ∧ AnalyticOnNhd ℂ E.symm E.target ∧
      (∀ᶠ x in 𝓝 a, E (fun i ↦ (x i : ℂ)) = fun i ↦ (e x i : ℂ)) ∧
      (∀ᶠ y in 𝓝 (e a), E.symm (fun i ↦ (y i : ℂ)) = fun i ↦ (e.symm y i : ℂ)) ∧
      (∀ z, E (star z) = star (E z)) ∧ (∀ z, E.symm (star z) = star (E.symm z)) := by
  obtain ⟨r, hr, F, hF, hFr, hFs⟩ := he.exists_complexification_pi
  obtain ⟨s, hs, G, hG, hGr, hGs⟩ := he'.exists_complexification_pi
  have hFr' : ∀ᶠ x in 𝓝 a, F (fun i ↦ (x i : ℂ)) = fun i ↦ (e x i : ℂ) := by
    filter_upwards [ball_mem_nhds a hr] with x hx using hFr x hx
  have hGr' : ∀ᶠ y in 𝓝 (e a),
      G (fun i ↦ (y i : ℂ)) = fun i ↦ (e.symm y i : ℂ) := by
    filter_upwards [ball_mem_nhds (e a) hs] with y hy using hGr y hy
  have hFa := hFr'.self_of_nhds
  have hGF := (hF _ (mem_ball_self hr)).eventually_comp_eq_id_of_eventually_real
    (hG _ (mem_ball_self hs)) hFr' hGr'
    (e.eventually_left_inverse ha)
  have hFG : ∀ᶠ z in 𝓝 (fun i ↦ (e a i : ℂ)), F (G z) = z := by
    have h := (hG _ (mem_ball_self hs)).eventually_comp_eq_id_of_eventually_real
      (by simpa only [e.left_inv ha] using hF _ (mem_ball_self hr))
      hGr'
      (by simpa only [e.left_inv ha] using hFr')
      (e.eventually_right_inverse' ha)
    exact h
  obtain ⟨U, hUinv, hUopen, haU⟩ := _root_.eventually_nhds_iff.1 hGF
  obtain ⟨V, hVinv, hVopen, haV⟩ := _root_.eventually_nhds_iff.1 hFG
  let U' := U ∩ ball (fun i ↦ (a i : ℂ)) r
  let V' := V ∩ ball (fun i ↦ (e a i : ℂ)) s
  have hFU : AnalyticOnNhd ℂ F U' := hF.mono inter_subset_right
  have hGV : AnalyticOnNhd ℂ G V' := hG.mono inter_subset_right
  have hgf : LeftInvOn G F (U' ∩ F ⁻¹' V') := fun x hx ↦ hUinv x hx.1.1
  have hfg : RightInvOn G F (V' ∩ G ⁻¹' U') := fun y hy ↦ hVinv y hy.1.1
  let E := hFU.continuousOn.toOpenPartialHomeomorph hGV.continuousOn
    (hUopen.inter isOpen_ball) (hVopen.inter isOpen_ball) hgf hfg
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [E]
    rw [ContinuousOn.toOpenPartialHomeomorph_source, mem_inter_iff, mem_preimage, hFa]
    exact ⟨⟨haU, mem_ball_self hr⟩, ⟨haV, mem_ball_self hs⟩⟩
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph,
      ContinuousOn.toOpenPartialHomeomorph_source] using hFU.mono inter_subset_left
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm,
      ContinuousOn.toOpenPartialHomeomorph_target] using hGV.mono inter_subset_left
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph] using hFr'
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm] using hGr'
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph] using hFs
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm] using hGs

/-- A real open partial homeomorphism between finite coordinate spaces that is analytic on its
source, with inverse analytic on its target, extends to a holomorphic open partial homeomorphism
whose source and target are invariant under conjugation and meet the real locus in `e.source` and
`e.target`, and such that both maps agree with `e` and `e.symm` on the real points and commute with
conjugation everywhere. -/
theorem exists_complexification_of_analyticOnNhd (e : OpenPartialHomeomorph (ι → ℝ) (κ → ℝ))
    (he : AnalyticOnNhd ℝ e e.source) (he' : AnalyticOnNhd ℝ e.symm e.target) :
    ∃ E : OpenPartialHomeomorph (ι → ℂ) (κ → ℂ),
      AnalyticOnNhd ℂ E E.source ∧ AnalyticOnNhd ℂ E.symm E.target ∧
      (∀ x : ι → ℝ, (fun i ↦ (x i : ℂ)) ∈ E.source ↔ x ∈ e.source) ∧
      (∀ y : κ → ℝ, (fun k ↦ (y k : ℂ)) ∈ E.target ↔ y ∈ e.target) ∧
      (∀ z, star z ∈ E.source ↔ z ∈ E.source) ∧
      (∀ w, star w ∈ E.target ↔ w ∈ E.target) ∧
      (∀ x ∈ e.source, E (fun i ↦ (x i : ℂ)) = fun k ↦ (e x k : ℂ)) ∧
      (∀ y ∈ e.target, E.symm (fun k ↦ (y k : ℂ)) = fun i ↦ (e.symm y i : ℂ)) ∧
      (∀ z, E (star z) = star (E z)) ∧ (∀ w, E.symm (star w) = star (E.symm w)) := by
  obtain ⟨W₁, hW₁, hW₁r, _, F, hF, hFe, hFs⟩ := he.exists_complexification_pi e.open_source
  obtain ⟨W₂, hW₂, hW₂r, _, G, hG, hGe, hGs⟩ := he'.exists_complexification_pi e.open_target
  -- Restrict to the complex points mapped into the partner domain, then cut down to where the
  -- composite is the identity by the uniqueness of complexifications.
  let W₁' := W₁ ∩ F ⁻¹' W₂
  have hW₁' : IsOpen W₁' := hF.continuousOn.isOpen_inter_preimage hW₁ hW₂
  have hGF_an : AnalyticOnNhd ℂ (G ∘ F) W₁' :=
    fun z hz ↦ (hG _ hz.2).comp (hF _ hz.1)
  have hGF_mem (x : ι → ℝ) (hx : x ∈ e.source) : (fun i ↦ (x i : ℂ)) ∈ W₁' :=
    ⟨(hW₁r x).2 hx, by rw [mem_preimage, hFe x hx]; exact (hW₂r (e x)).2 (e.map_source hx)⟩
  obtain ⟨U, hUW₁', hUo, hUr, hUs, hGF⟩ :=
    hGF_an.exists_eqOn_of_forall_real (analyticOnNhd_id (s := W₁')) e.open_source hW₁' hGF_mem
      fun x hx ↦ by simp only [comp_apply, hFe x hx, hGe (e x) (e.map_source hx), e.left_inv hx]
  let W₂' := W₂ ∩ G ⁻¹' W₁
  have hW₂' : IsOpen W₂' := hG.continuousOn.isOpen_inter_preimage hW₂ hW₁
  have hFG_an : AnalyticOnNhd ℂ (F ∘ G) W₂' :=
    fun w hw ↦ (hF _ hw.2).comp (hG _ hw.1)
  have hFG_mem (y : κ → ℝ) (hy : y ∈ e.target) : (fun k ↦ (y k : ℂ)) ∈ W₂' :=
    ⟨(hW₂r y).2 hy, by rw [mem_preimage, hGe y hy]; exact (hW₁r (e.symm y)).2 (e.map_target hy)⟩
  obtain ⟨V, hVW₂', hVo, hVr, hVs, hFG⟩ :=
    hFG_an.exists_eqOn_of_forall_real (analyticOnNhd_id (s := W₂')) e.open_target hW₂' hFG_mem
      fun y hy ↦ by simp only [comp_apply, hGe y hy, hFe (e.symm y) (e.map_target hy),
        e.right_inv hy]
  have hFU : AnalyticOnNhd ℂ F U := hF.mono (hUW₁'.trans inter_subset_left)
  have hGV : AnalyticOnNhd ℂ G V := hG.mono (hVW₂'.trans inter_subset_left)
  have hgf : LeftInvOn G F (U ∩ F ⁻¹' V) := fun z hz ↦ hGF hz.1
  have hfg : RightInvOn G F (V ∩ G ⁻¹' U) := fun w hw ↦ hFG hw.1
  let E := hFU.continuousOn.toOpenPartialHomeomorph hGV.continuousOn hUo hVo hgf hfg
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph,
      ContinuousOn.toOpenPartialHomeomorph_source] using hFU.mono inter_subset_left
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm,
      ContinuousOn.toOpenPartialHomeomorph_target] using hGV.mono inter_subset_left
  · intro x
    simp only [E, ContinuousOn.toOpenPartialHomeomorph_source, mem_inter_iff, mem_preimage, hUr]
    exact ⟨And.left, fun hx ↦ ⟨hx, by rw [hFe x hx]; exact (hVr (e x)).2 (e.map_source hx)⟩⟩
  · intro y
    simp only [E, ContinuousOn.toOpenPartialHomeomorph_target, mem_inter_iff, mem_preimage, hVr]
    exact ⟨And.left, fun hy ↦ ⟨hy, by rw [hGe y hy]; exact (hUr (e.symm y)).2 (e.map_target hy)⟩⟩
  · intro z
    simp only [E, ContinuousOn.toOpenPartialHomeomorph_source, mem_inter_iff, mem_preimage,
      hFs, hUs, hVs]
  · intro w
    simp only [E, ContinuousOn.toOpenPartialHomeomorph_target, mem_inter_iff, mem_preimage,
      hGs, hUs, hVs]
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph] using hFe
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm] using hGe
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph] using hFs
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm] using hGs

end OpenPartialHomeomorph
