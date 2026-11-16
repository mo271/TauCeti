/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Analysis.Complex.PrescribedZeros.Divisor
import TauCeti.Analysis.Meromorphic.Identity
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Topology.ConnectedComponents

/-!
# Every open subset of the complex plane is a domain of holomorphy

On a slit disk such as `Ω = ball 0 1 \ [0, 1)`, a boundary point `ξ ∈ (0, 1)` belongs to
`frontier Ω`, yet `ball ξ r ∩ Ω` splits into upper and lower half-disks: a function that jumps
across the slit extends holomorphically across `ball ξ r` from either side separately while failing
to extend on all of `ball ξ r ∩ Ω` at once. Genuine boundary noncontinuation in the plane must
therefore obstruct continuation from *every individual connected component* of `ball ξ r ∩ Ω` whose
closure reaches `ξ`, and even allow *meromorphic* candidates on `ball ξ r`.

This file constructs such a holomorphic function on every open subset `Ω ⊆ ℂ` and deduces the
strongest germ form of the plane domain-of-holomorphy theorem:

1. **Boundary-accumulating locally finite zero set**: exhausting `Ω` by compact sets
   `K n ⊆ interior (K (n + 1))`, each compact shell `L 0 = K 0`,
   `L (n + 1) = K (n + 1) \ interior (K n)` is covered by finitely many balls `ball a (ρ a)` with
   `a ∈ L n` and `ball a (2 * ρ a) ⊆ Ω`. Their centers form a subset `E ⊆ Ω` that is locally finite
   in `Ω` and accumulates at `ξ` inside *every* component
   `C = connectedComponentIn (ball ξ r ∩ Ω) z` with `ξ ∈ closure C` (because `ball a (2 * ρ a) ⊆ Ω`
   forces `ρ a < dist w ξ` and keeps `[w, a]` inside `ball ξ r ∩ Ω`).
2. **Branchwise meromorphic boundary noncontinuation**
   (`IsOpen.exists_differentiableOn_not_meromorphicOn_connectedComponentIn`): realizing the
   indicator of `E` via `IsOpen.exists_differentiableOn_analyticOrderAt_eq` produces `f` holomorphic
   on `Ω` with `analyticOrderAt f z ≠ ⊤` everywhere on `Ω` and simple zeros on `E`. Any `F`
   meromorphic on `ball ξ r` agreeing with `f` on `C` would have finite meromorphic order at `z`,
   hence at `ξ` by preconnectedness of `ball ξ r`, contradicting the zeros of `F` on `C ∩ E`
   accumulating at `ξ`.
3. **Propagation to arbitrary disks and preconnected open sets**
   (`IsOpen.ball_subset_of_not_meromorphicOn_connectedComponentIn`,
   `IsOpen.subset_of_isPreconnected_of_not_meromorphicOn_connectedComponentIn`,
   `IsOpen.exists_differentiableOn_subset_of_isPreconnected_of_meromorphicOn`): if `f` has no
   centered branchwise meromorphic continuation across `frontier Ω`, then *any* preconnected open
   set `V ⊆ ℂ` meeting `Ω` at `z` on which a meromorphic function `F` satisfies `F =ᶠ[𝓝[≠] z] f`
   must satisfy `V ⊆ Ω`.

## Main results

* `IsOpen.ball_subset_of_not_meromorphicOn_connectedComponentIn`: centered branchwise meromorphic
  noncontinuation implies `ball c R ⊆ Ω` for every disk carrying a meromorphic extension of a
  punctured germ of `f`.
* `IsOpen.subset_of_isPreconnected_of_not_meromorphicOn_connectedComponentIn`: the same obstruction
  forces `V ⊆ Ω` for every preconnected open set `V ⊆ ℂ` carrying a meromorphic extension of a
  punctured germ of `f`.
* `IsOpen.exists_differentiableOn_not_meromorphicOn_connectedComponentIn`: every open `Ω ⊆ ℂ`
  admits `f` holomorphic on `Ω` without branchwise meromorphic continuation across any boundary
  point.
* `IsOpen.exists_differentiableOn_ball_subset_of_meromorphicOn`: disk-germ form of the plane
  domain-of-holomorphy theorem.
* `IsOpen.exists_differentiableOn_subset_of_isPreconnected_of_meromorphicOn`: preconnected-open-set
  punctured-germ form of the plane domain-of-holomorphy theorem.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 15.5 and 15.6.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 15.13.
-/

public section

open Filter Function Metric Set
open scoped Topology

section Helpers

/-- Compact exhaustion shells `L 0 = K 0`, `L (n + 1) = K (n + 1) \ interior (K n)` cover `Ω`, are
compact subsets of `Ω`, and avoid `interior (K m)` for indices strictly above `m`. -/
private theorem exists_compact_shell_cover {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∃ K L : ℕ → Set ℂ, (∀ n, K n ⊆ interior (K (n + 1))) ∧ ⋃ n, K n = Ω ∧
      (∀ n, IsCompact (L n)) ∧ (∀ n, L n ⊆ Ω) ∧ ⋃ n, L n = Ω ∧
      ∀ N m, N + 1 ≤ m → Disjoint (interior (K (N + 1))) (L (m + 1)) := by
  obtain ⟨K, hKcpt, hKint, hKunion, -⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hKΩ : ∀ n, K n ⊆ Ω := fun n z hz ↦ hKunion ▸ mem_iUnion.mpr ⟨n, hz⟩
  have hKmono : Monotone K := monotone_nat_of_le_succ fun n ↦ (hKint n).trans interior_subset
  let L : ℕ → Set ℂ := Nat.rec (K 0) fun n _ ↦ K (n + 1) \ interior (K n)
  have hLcpt : ∀ n, IsCompact (L n)
    | 0 => hKcpt 0
    | n + 1 => (hKcpt (n + 1)).diff isOpen_interior
  have hLΩ : ∀ n, L n ⊆ Ω
    | 0 => hKΩ 0
    | n + 1 => Set.sdiff_subset.trans (hKΩ (n + 1))
  have hLunion : ⋃ n, L n = Ω := by
    refine Subset.antisymm (iUnion_subset hLΩ) fun z hz ↦ ?_
    classical
    have hex : ∃ n, z ∈ K n := mem_iUnion.mp (hKunion.symm ▸ hz)
    have hspec : z ∈ K (Nat.find hex) := Nat.find_spec hex
    rcases hm : Nat.find hex with _ | m
    · rw [hm] at hspec
      exact mem_iUnion.mpr ⟨0, hspec⟩
    · rw [hm] at hspec
      have hnot : z ∉ K m := Nat.find_min hex (hm ▸ Nat.lt_succ_self m)
      exact mem_iUnion.mpr ⟨m + 1, hspec, fun hint ↦ hnot (interior_subset hint)⟩
  refine ⟨K, L, hKint, hKunion, hLcpt, hLΩ, hLunion, fun N m hNm ↦ ?_⟩
  exact disjoint_left.mpr fun z hzV hzL ↦ hzL.2 (interior_mono (hKmono hNm) hzV)

open scoped Classical in
/-- A subset `E ⊆ Ω` that is locally finite within `Ω` has a `{0, 1}`-valued indicator in
`Function.locallyFinsuppWithin Ω ℕ` with support `E`. -/
private noncomputable def indicatorLocallyFinsuppWithin {Ω E : Set ℂ} (hEΩ : E ⊆ Ω)
    (hEloc : ∀ z ∈ Ω, ∃ t ∈ 𝓝 z, (t ∩ E).Finite) :
    Function.locallyFinsuppWithin Ω ℕ where
  toFun := E.indicator 1
  supportWithinDomain' := by simpa [Set.support_indicator] using hEΩ
  supportLocallyFiniteWithinDomain' := by simpa [Set.support_indicator] using hEloc

open scoped Classical in
/-- The support of `indicatorLocallyFinsuppWithin hEΩ hEloc` is `E`. -/
private theorem support_indicatorLocallyFinsuppWithin {Ω E : Set ℂ} (hEΩ : E ⊆ Ω)
    (hEloc : ∀ z ∈ Ω, ∃ t ∈ 𝓝 z, (t ∩ E).Finite) :
    (indicatorLocallyFinsuppWithin hEΩ hEloc).support = E := by
  change (E.indicator (1 : ℂ → ℕ)).support = E
  simp [Set.support_indicator]

/-- Every open set `Ω ⊆ ℂ` carries a locally finitely supported `ℕ`-valued multiplicity function
whose support accumulates at `ξ` along every component of `ball ξ r ∩ Ω` adherent to `ξ`. -/
private theorem exists_locallyFinsuppWithin_closure_support {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∃ m : Function.locallyFinsuppWithin Ω ℕ,
      ∀ ξ ∈ frontier Ω, ∀ r > 0, ∀ z ∈ ball ξ r ∩ Ω,
        ξ ∈ closure (connectedComponentIn (ball ξ r ∩ Ω) z) →
        ξ ∈ closure (connectedComponentIn (ball ξ r ∩ Ω) z ∩ m.support) := by
  classical
  obtain ⟨K, L, hKint, hKunion, hLcpt, hLΩ, hLunion, hLdisj⟩ := exists_compact_shell_cover hΩ
  have hball_ex : ∀ x : ℂ, ∃ ρ > 0, x ∈ Ω → ball x (2 * ρ) ⊆ Ω := fun x ↦ by
    by_cases hx : x ∈ Ω
    · obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
      exact ⟨δ / 2, half_pos hδ, fun _ ↦ by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
    · exact ⟨1, one_pos, fun h ↦ (hx h).elim⟩
  choose ρ hρ_pos hρ_sub using hball_ex
  choose F hFL hFfin hLF using fun n : ℕ ↦
    (hLcpt n).elim_finite_subcover_image (fun a _ ↦ isOpen_ball) fun x hx ↦
      mem_biUnion hx (mem_ball_self (hρ_pos x))
  set E : Set ℂ := ⋃ n, F n
  have hEΩ : E ⊆ Ω := iUnion_subset fun n ↦ (hFL n).trans (hLΩ n)
  have hEloc : ∀ z ∈ Ω, ∃ t ∈ 𝓝 z, (t ∩ E).Finite := fun z hz ↦ by
    obtain ⟨N, hN⟩ := mem_iUnion.mp (hKunion.symm ▸ hz)
    refine ⟨interior (K (N + 1)), isOpen_interior.mem_nhds (hKint N hN), ?_⟩
    refine ((Finset.range (N + 2)).finite_toSet.biUnion fun n _ ↦ hFfin n).subset ?_
    rintro a ⟨haV, haE⟩
    obtain ⟨n, han⟩ := mem_iUnion.mp haE
    refine mem_biUnion (Finset.mem_range.mpr ?_) han
    by_contra! hle
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel (by omega)).symm⟩
    exact (hLdisj N m (by omega)).le_bot ⟨haV, hFL (m + 1) han⟩
  refine ⟨indicatorLocallyFinsuppWithin hEΩ hEloc,
    fun ξ hξ r hr z _ hξC ↦ Metric.mem_closure_iff.mpr fun ε hε ↦ ?_⟩
  have hξΩ : ξ ∉ Ω := fun h ↦ hξ.2 (hΩ.interior_eq.symm ▸ h)
  set δ : ℝ := min r ε / 2
  obtain ⟨w, hwC, hwδ⟩ := Metric.mem_closure_iff.mp hξC δ (half_pos (lt_min hr hε))
  have hw_in : w ∈ ball ξ r ∩ Ω := connectedComponentIn_subset _ _ hwC
  obtain ⟨n, hwn⟩ := mem_iUnion.mp (hLunion.symm ▸ hw_in.2)
  obtain ⟨a, haF, hwa⟩ := mem_iUnion₂.mp (hLF n hwn)
  have haE : a ∈ E := mem_iUnion.mpr ⟨n, haF⟩
  have haΩ : a ∈ Ω := hEΩ haE
  have h2ρ : 2 * ρ a ≤ dist ξ a := not_lt.mp fun hlt ↦ hξΩ (hρ_sub a haΩ (by rwa [mem_ball]))
  have hρ_lt : ρ a < dist ξ w := by linarith [dist_triangle ξ w a, mem_ball.mp hwa]
  have ha_dist : dist a ξ < min r ε := by
    have haw : dist a w < ρ a := by rw [dist_comm]; exact mem_ball.mp hwa
    have h2δ : 2 * δ = min r ε := mul_div_cancel₀ _ two_ne_zero
    linarith [dist_triangle a w ξ, dist_comm w ξ]
  have hseg : segment ℝ w a ⊆ ball ξ r ∩ Ω := subset_inter
    ((convex_ball ξ r).segment_subset hw_in.1 (mem_ball.mpr (ha_dist.trans_le (min_le_left r ε))))
    (((convex_ball a (ρ a)).segment_subset hwa (mem_ball_self (hρ_pos a))).trans <|
      (ball_subset_ball (by linarith [hρ_pos a])).trans (hρ_sub a haΩ))
  have haC : a ∈ connectedComponentIn (ball ξ r ∩ Ω) z := by
    rw [connectedComponentIn_eq hwC]
    exact (convex_segment w a).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ w a) hseg (right_mem_segment ℝ w a)
  exact ⟨a, ⟨haC, (support_indicatorLocallyFinsuppWithin hEΩ hEloc).symm ▸ haE⟩,
    by rw [dist_comm]; exact ha_dist.trans_le (min_le_right r ε)⟩

/-- First-exit boundary geometry along the segment `[z, w]` inside a ball `ball c R` when `z ∈ Ω`
and `w ∉ Ω`: produces a frontier point `ξ ∈ ball c R ∩ frontier Ω`, a sub-ball
`ball ξ r ⊆ ball c R`, and an interior point `z₁` in the same component of `ball c R ∩ Ω` as `z`
whose component in `ball ξ r ∩ Ω` adheres to `ξ`. -/
private theorem exists_frontier_ball_connectedComponentIn_of_notMem {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {c z w : ℂ} {R : ℝ} (hz : z ∈ ball c R ∩ Ω) (hw_ball : w ∈ ball c R) (hwΩ : w ∉ Ω) :
    ∃ (ξ : ℂ) (r : ℝ) (z₁ : ℂ), ξ ∈ frontier Ω ∧ 0 < r ∧ ball ξ r ⊆ ball c R ∧
      z₁ ∈ ball ξ r ∩ Ω ∧ z₁ ∈ connectedComponentIn (ball c R ∩ Ω) z ∧
      ξ ∈ closure (connectedComponentIn (ball ξ r ∩ Ω) z₁) := by
  let γ : ℝ → ℂ := AffineMap.lineMap z w
  have hγ_cont : Continuous γ := AffineMap.lineMap_continuous
  have hγ0 : γ 0 = z := AffineMap.lineMap_apply_zero z w
  have hγ_ball : ∀ {t}, t ∈ Icc (0 : ℝ) 1 → γ t ∈ ball c R := fun ht ↦
    (convex_ball c R).segment_subset hz.1 hw_ball
      (segment_eq_image_lineMap ℝ z w ▸ mem_image_of_mem γ ht)
  set S : Set ℝ := Icc 0 1 ∩ γ ⁻¹' Ωᶜ
  have hS_closed : IsClosed S := isClosed_Icc.inter (hΩ.isClosed_compl.preimage hγ_cont)
  have hS_ne : S.Nonempty := ⟨1, right_mem_Icc.mpr zero_le_one,
    by simpa [γ, AffineMap.lineMap_apply_one] using hwΩ⟩
  have hS_bdd : BddBelow S := bddBelow_Icc.mono inter_subset_left
  set t₀ : ℝ := sInf S
  have ht₀_mem : t₀ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht₀_pos : 0 < t₀ := lt_of_le_of_ne ht₀_mem.1.1 fun h0 ↦
    ht₀_mem.2 (by simpa [← h0, hγ0] using hz.2)
  have hIco_Ω : ∀ {t}, t ∈ Ico 0 t₀ → γ t ∈ Ω := fun ht ↦ by
    by_contra hnot
    exact notMem_of_lt_csInf ht.2 hS_bdd ⟨⟨ht.1, ht.2.le.trans ht₀_mem.1.2⟩, hnot⟩
  obtain ⟨r, hr, hr_sub⟩ := Metric.isOpen_iff.mp isOpen_ball (γ t₀) (hγ_ball ht₀_mem.1)
  obtain ⟨δ, hδ, hδ_ball⟩ := Metric.continuousAt_iff.mp hγ_cont.continuousAt r hr
  set t₁ : ℝ := max 0 (t₀ - δ / 2)
  have ht₁_nonneg : 0 ≤ t₁ := le_max_left _ _
  have ht₁_lt : t₁ < t₀ := max_lt ht₀_pos (by linarith)
  have hIco₁_sub : γ '' Ico t₁ t₀ ⊆ ball (γ t₀) r ∩ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨hδ_ball ?_, hIco_Ω ⟨ht₁_nonneg.trans ht.1, ht.2⟩⟩
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr ht.2)]
    linarith [le_max_right 0 (t₀ - δ / 2), ht.1, half_lt_self hδ]
  have hz₁_in : γ t₁ ∈ ball (γ t₀) r ∩ Ω := hIco₁_sub ⟨t₁, left_mem_Ico.mpr ht₁_lt, rfl⟩
  have hC₁ : γ '' Ico t₁ t₀ ⊆ connectedComponentIn (ball (γ t₀) r ∩ Ω) (γ t₁) :=
    (isPreconnected_Ico.image γ hγ_cont.continuousOn).subset_connectedComponentIn
      ⟨t₁, left_mem_Ico.mpr ht₁_lt, rfl⟩ hIco₁_sub
  have hξ_cl : γ t₀ ∈ closure (connectedComponentIn (ball (γ t₀) r ∩ Ω) (γ t₁)) :=
    closure_mono hC₁ (image_closure_subset_closure_image hγ_cont
      ⟨t₀, by rw [closure_Ico ht₁_lt.ne]; exact right_mem_Icc.mpr ht₁_lt.le, rfl⟩)
  have hξ_fr : γ t₀ ∈ frontier Ω :=
    ⟨closure_mono ((connectedComponentIn_subset _ _).trans inter_subset_right) hξ_cl,
      by rw [hΩ.interior_eq]; exact ht₀_mem.2⟩
  have hIco₀_sub : γ '' Ico 0 t₀ ⊆ ball c R ∩ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hγ_ball ⟨ht.1, ht.2.le.trans ht₀_mem.1.2⟩, hIco_Ω ht⟩
  have hz₁_D : γ t₁ ∈ connectedComponentIn (ball c R ∩ Ω) z := by
    rw [← hγ0]
    exact (isPreconnected_Ico.image γ hγ_cont.continuousOn).subset_connectedComponentIn
      ⟨0, left_mem_Ico.mpr ht₀_pos, rfl⟩ hIco₀_sub ⟨t₁, ⟨ht₁_nonneg, ht₁_lt⟩, rfl⟩
  exact ⟨γ t₀, r, γ t₁, hξ_fr, hr, hr_sub, hz₁_in, hz₁_D, hξ_cl⟩

end Helpers

/-- **Disk-germ continuation transfer** (Rainer, proof of Theorem 15.6). Suppose `f` is holomorphic
on an open set `Ω ⊆ ℂ` and admits no meromorphic continuation from any boundary-adherent connected
component of `ball ξ r ∩ Ω` to `ball ξ r`. Then *every* open disk `ball c R` meeting `Ω` at a point
`z` where a meromorphic function `F` on `ball c R` satisfies `F =ᶠ[𝓝[≠] z] f` is contained in
`Ω`. -/
theorem IsOpen.ball_subset_of_not_meromorphicOn_connectedComponentIn {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hobs : ∀ ξ ∈ frontier Ω, ∀ r > 0, ∀ z ∈ ball ξ r ∩ Ω,
      ξ ∈ closure (connectedComponentIn (ball ξ r ∩ Ω) z) →
      ¬ ∃ F : ℂ → ℂ, MeromorphicOn F (ball ξ r) ∧
        EqOn F f (connectedComponentIn (ball ξ r ∩ Ω) z))
    {c z : ℂ} {R : ℝ} (hz : z ∈ ball c R ∩ Ω) {F : ℂ → ℂ}
    (hF : MeromorphicOn F (ball c R)) (hFz : F =ᶠ[𝓝[≠] z] f) :
    ball c R ⊆ Ω := by
  intro w hw_ball
  by_contra hwΩ
  obtain ⟨ξ, r, z₁, hξ_fr, hr, hr_sub, hz₁_in, hz₁_D, hξ_cl⟩ :=
    exists_frontier_ball_connectedComponentIn_of_notMem hΩ hz hw_ball hwΩ
  set D : Set ℂ := connectedComponentIn (ball c R ∩ Ω) z
  have hD_sub : D ⊆ ball c R ∩ Ω := connectedComponentIn_subset _ _
  set G : ℂ → ℂ := toMeromorphicNFOn F (ball c R)
  have hG_nf : MeromorphicNFOn G (ball c R) := meromorphicNFOn_toMeromorphicNFOn F (ball c R)
  have hf_nf : MeromorphicNFOn f D := fun _ hx ↦
    (hf.analyticAt (hΩ.mem_nhds (hD_sub hx).2)).meromorphicNFAt
  have hGz : G =ᶠ[𝓝[≠] z] f := (hF.toMeromorphicNFOn_eq_self_on_nhdsNE hz.1).trans hFz
  have heqD : EqOn G f D :=
    (MeromorphicNFOn.eqOn_of_isPreconnected (fun _ hx ↦ hG_nf (hD_sub hx).1) hf_nf
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hz) hGz)
  have hC₁_sub : connectedComponentIn (ball ξ r ∩ Ω) z₁ ⊆ D := by
    change connectedComponentIn (ball ξ r ∩ Ω) z₁ ⊆ connectedComponentIn (ball c R ∩ Ω) z
    rw [connectedComponentIn_eq hz₁_D]
    exact connectedComponentIn_mono z₁ (inter_subset_inter_left Ω hr_sub)
  exact hobs ξ hξ_fr r hr z₁ hz₁_in hξ_cl
    ⟨G, fun x hx ↦ hG_nf.meromorphicOn x (hr_sub hx), heqD.mono hC₁_sub⟩

/-- **Preconnected-domain germ continuation transfer.** Under the hypotheses of
`IsOpen.ball_subset_of_not_meromorphicOn_connectedComponentIn`, every *preconnected open* set
`V ⊆ ℂ` meeting `Ω` at a point `z` where a meromorphic function `F` on `V` satisfies
`F =ᶠ[𝓝[≠] z] f` is contained in `Ω`. -/
theorem IsOpen.subset_of_isPreconnected_of_not_meromorphicOn_connectedComponentIn {Ω : Set ℂ}
    (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hobs : ∀ ξ ∈ frontier Ω, ∀ r > 0, ∀ z ∈ ball ξ r ∩ Ω,
      ξ ∈ closure (connectedComponentIn (ball ξ r ∩ Ω) z) →
      ¬ ∃ F : ℂ → ℂ, MeromorphicOn F (ball ξ r) ∧
        EqOn F f (connectedComponentIn (ball ξ r ∩ Ω) z))
    {V : Set ℂ} (hV : IsOpen V) (hV_conn : IsPreconnected V) {z : ℂ} (hz : z ∈ V ∩ Ω)
    {F : ℂ → ℂ} (hF : MeromorphicOn F V) (hFz : F =ᶠ[𝓝[≠] z] f) :
    V ⊆ Ω := by
  intro u huV
  by_contra huΩ
  have hV_sdiff_eq : V \ Ωᶜ = V ∩ Ω := Set.sdiff_compl
  have hV_sdiff_open : IsOpen (V \ Ωᶜ) := hV_sdiff_eq ▸ hV.inter hΩ
  have hz_sdiff : z ∈ V \ Ωᶜ := hV_sdiff_eq ▸ hz
  set D : Set ℂ := connectedComponentIn (V \ Ωᶜ) z
  have hD_sub : D ⊆ V ∩ Ω := hV_sdiff_eq ▸ connectedComponentIn_subset (V \ Ωᶜ) z
  have huD : u ∉ D := fun h ↦ huΩ (hD_sub h).2
  obtain ⟨ξ, ⟨hξΩ, hξV⟩, hξ_cl⟩ :=
    hV_conn.exists_mem_inter_closure_connectedComponentIn_sdiff hV_sdiff_open hz_sdiff huV huD
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV ξ hξV
  obtain ⟨w, hwD, hw_ball⟩ := Metric.mem_closure_iff.mp hξ_cl r hr
  set G : ℂ → ℂ := toMeromorphicNFOn F V
  have hG_nf : MeromorphicNFOn G V := meromorphicNFOn_toMeromorphicNFOn F V
  have hf_nf : MeromorphicNFOn f D := fun _ hx ↦
    (hf.analyticAt (hΩ.mem_nhds (hD_sub hx).2)).meromorphicNFAt
  have heqD : EqOn G f D :=
    MeromorphicNFOn.eqOn_of_isPreconnected (fun _ hx ↦ hG_nf (hD_sub hx).1) hf_nf
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hz_sdiff)
      ((hF.toMeromorphicNFOn_eq_self_on_nhdsNE hz.1).trans hFz)
  have hGw : G =ᶠ[𝓝[≠] w] f :=
    (heqD.eventuallyEq_of_mem (hV_sdiff_open.connectedComponentIn.mem_nhds hwD)).filter_mono
      nhdsWithin_le_nhds
  have hw_in : w ∈ ball ξ r ∩ Ω := ⟨by rwa [mem_ball, dist_comm], (hD_sub hwD).2⟩
  exact hξΩ (hΩ.ball_subset_of_not_meromorphicOn_connectedComponentIn hf hobs hw_in
    (fun x hx ↦ hG_nf.meromorphicOn x (hrV hx)) hGw (mem_ball_self hr))

/-- **Branchwise meromorphic boundary noncontinuation** (Rainer, Theorem 15.5). Every open subset
`Ω ⊆ ℂ` admits a holomorphic function `f` with finite analytic order at every point of `Ω` such
that, for every boundary point `ξ ∈ frontier Ω`, every radius `r > 0`, and every `z ∈ ball ξ r ∩ Ω`
whose connected component `C = connectedComponentIn (ball ξ r ∩ Ω) z` has `ξ ∈ closure C`, no
function meromorphic on `ball ξ r` agrees with `f` on `C`. -/
theorem IsOpen.exists_differentiableOn_not_meromorphicOn_connectedComponentIn {Ω : Set ℂ}
    (hΩ : IsOpen Ω) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ z ∈ Ω, analyticOrderAt f z ≠ ⊤) ∧
      ∀ ξ ∈ frontier Ω, ∀ r > 0, ∀ z ∈ ball ξ r ∩ Ω,
        ξ ∈ closure (connectedComponentIn (ball ξ r ∩ Ω) z) →
        ¬ ∃ F : ℂ → ℂ, MeromorphicOn F (ball ξ r) ∧
          EqOn F f (connectedComponentIn (ball ξ r ∩ Ω) z) := by
  obtain ⟨m, hm_cl⟩ := exists_locallyFinsuppWithin_closure_support hΩ
  obtain ⟨f, hf, hord⟩ := hΩ.exists_differentiableOn_analyticOrderAt_eq m
  refine ⟨f, hf, fun z hz ↦ by rw [hord z hz]; exact ENat.natCast_ne_top (m z),
    fun ξ hξ r hr z hz hξC ⟨F, hF, heq⟩ ↦ ?_⟩
  set C : Set ℂ := connectedComponentIn (ball ξ r ∩ Ω) z
  have hC_open : IsOpen C := (isOpen_ball.inter hΩ).connectedComponentIn
  have hFz_eq : F =ᶠ[𝓝[≠] z] f :=
    (heq.eventuallyEq_of_mem (hC_open.mem_nhds (mem_connectedComponentIn hz))).filter_mono
      nhdsWithin_le_nhds
  have hFz_ord : meromorphicOrderAt F z ≠ ⊤ := by
    rw [meromorphicOrderAt_congr hFz_eq, (hf.analyticAt (hΩ.mem_nhds hz.2)).meromorphicOrderAt_eq,
      hord z hz.2]
    exact WithTop.coe_ne_top
  have hFξ_ord : meromorphicOrderAt F ξ ≠ ⊤ :=
    hF.meromorphicOrderAt_ne_top_of_isPreconnected (convex_ball ξ r).isPreconnected hz.1
      (mem_ball_self hr) hFz_ord
  have hF_ev : ∀ᶠ w in 𝓝[≠] ξ, F w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hF ξ (mem_ball_self hr))).mp hFξ_ord
  rw [eventually_nhdsWithin_iff] at hF_ev
  obtain ⟨a, haU, haCS⟩ := mem_closure_iff_nhds.mp (hm_cl ξ hξ r hr z hz hξC) _ hF_ev
  have haΩ : a ∈ Ω := ((connectedComponentIn_subset _ _ haCS.1) : a ∈ ball ξ r ∩ Ω).2
  have ha_ne_ξ : a ≠ ξ := fun h ↦ hξ.2 (hΩ.interior_eq.symm ▸ (h ▸ haΩ))
  have hfa0 : f a = 0 := by
    refine (hf.analyticAt (hΩ.mem_nhds haΩ)).analyticOrderAt_ne_zero.mp ?_
    rw [hord a haΩ]
    exact Nat.cast_ne_zero.mpr haCS.2
  exact haU ha_ne_ξ ((heq haCS.1).trans hfa0)

/-- **Every open subset of `ℂ` is a domain of holomorphy (preconnected-domain germ form).** For any
open set `Ω ⊆ ℂ`, there exists `f` holomorphic on `Ω` with finite analytic order everywhere on `Ω`
such that *every* preconnected open set `V ⊆ ℂ` meeting `Ω` at a point `z` where some `F`
meromorphic on `V` satisfies `F =ᶠ[𝓝[≠] z] f` must satisfy `V ⊆ Ω`. -/
theorem IsOpen.exists_differentiableOn_subset_of_isPreconnected_of_meromorphicOn {Ω : Set ℂ}
    (hΩ : IsOpen Ω) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ z ∈ Ω, analyticOrderAt f z ≠ ⊤) ∧
      ∀ ⦃V : Set ℂ⦄, IsOpen V → IsPreconnected V → ∀ ⦃z : ℂ⦄, z ∈ V ∩ Ω →
        ∀ ⦃F : ℂ → ℂ⦄, MeromorphicOn F V → F =ᶠ[𝓝[≠] z] f → V ⊆ Ω := by
  obtain ⟨f, hf, hord, hobs⟩ := hΩ.exists_differentiableOn_not_meromorphicOn_connectedComponentIn
  exact ⟨f, hf, hord, fun _ hV hVc _ hz _ hF hFz ↦
    hΩ.subset_of_isPreconnected_of_not_meromorphicOn_connectedComponentIn hf hobs hV hVc hz hF hFz⟩

/-- **Every open subset of `ℂ` is a domain of holomorphy (disk-germ form, Rainer, Theorem 15.6).**
For any open set `Ω ⊆ ℂ`, there exists `f` holomorphic on `Ω` with finite analytic order everywhere
on `Ω` such that *every* open disk `ball c R` meeting `Ω` at a point `z` where some `F` meromorphic
on `ball c R` satisfies `F =ᶠ[𝓝[≠] z] f` is contained in `Ω`. -/
theorem IsOpen.exists_differentiableOn_ball_subset_of_meromorphicOn {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ z ∈ Ω, analyticOrderAt f z ≠ ⊤) ∧
      ∀ c : ℂ, ∀ R : ℝ, ∀ z ∈ ball c R ∩ Ω, ∀ F : ℂ → ℂ,
        MeromorphicOn F (ball c R) → F =ᶠ[𝓝[≠] z] f → ball c R ⊆ Ω := by
  obtain ⟨f, hf, hord, hsub⟩ :=
    hΩ.exists_differentiableOn_subset_of_isPreconnected_of_meromorphicOn
  exact ⟨f, hf, hord, fun c R _ hz _ hF hFz ↦
    hsub isOpen_ball (convex_ball c R).isPreconnected hz hF hFz⟩
