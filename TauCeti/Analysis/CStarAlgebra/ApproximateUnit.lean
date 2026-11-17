/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import TauCeti.Topology.ApproximateUnit
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Increasing approximate units: images and uniform convergence

A star-algebra homomorphism between C⋆-algebras is positive and contractive, so it maps the
positive part of the closed unit ball into itself. Hence the image of an increasing approximate
unit under a surjective homomorphism is an increasing approximate unit of the target,
`Filter.IsIncreasingApproximateUnit.map`. This transfers approximate-unit limits, such as the
norm of a positive functional, from a C⋆-algebra to its quotients.

Since an increasing approximate unit eventually lies in the closed unit ball, the convergence
`e * a → a` is uniform for `a` in a compact set,
`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_right`, and so is the convergence
`a * e → a`, `Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_left`. This controls
`e * α_r(b) → α_r(b)` uniformly along a compact set of group elements `r` for a continuous action
`α`, as needed for approximate units of twisted convolution algebras.

`Filter.IsIncreasingApproximateUnit.tendsto_mul_mul` records the two-sided limit `e * a * e → a`.

`TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le` is the estimate for a positive contraction `e`
that drives the approximate-unit argument showing that closed two-sided ideals are self-adjoint:
`‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖`. Its companion
`TauCeti.CStarAlgebra.norm_sub_mul_sq_le`, `‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖`,
drives the proof of the C⋆-identity on the quotient by a closed two-sided ideal, while
`TauCeti.CStarAlgebra.norm_sub_mul_sq_le_of_star_mul_self_le`,
`‖x - x * e‖ ^ 2 ≤ ‖b - b * e‖` whenever `star x * x ≤ b`, controls right multiplication by an
approximate unit (`TauCeti.CStarAlgebra.tendsto_mul_left_of_star_mul_self_le` and
`NonUnitalStarSubalgebra.tendsto_mul_approximateUnit_of_star_mul_self_le`).
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace Filter.IsIncreasingApproximateUnit

section Uniform

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- Along an increasing approximate unit, `e * a → a` uniformly for `a` in a compact set. -/
theorem tendstoUniformlyOn_mul_right {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    {K : Set A} (hK : IsCompact K) : TendstoUniformlyOn (fun e a => e * a) id l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Cover `K` by finitely many balls of radius `ε / 3`, and use the eventual bound `‖e‖ ≤ 1`.
  obtain ⟨t, -, ht, hKt⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  have hconv : ∀ᶠ e in l, ∀ c ∈ t, dist c (e * c) < ε / 3 := (eventually_all_finite ht).2
    fun c _ => (Metric.tendsto_nhds.1 (hl.tendsto_mul_right c) (ε / 3) (by positivity)).mono
      fun _ h => by rwa [dist_comm]
  filter_upwards [hl.eventually_norm, hconv] with e he hc a ha
  obtain ⟨c, hct, hac⟩ := Set.mem_iUnion₂.1 (hKt ha)
  have hmul : dist (e * c) (e * a) ≤ dist c a := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) he)
  calc dist (id a) (e * a) ≤ dist a c + dist c (e * c) + dist (e * c) (e * a) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact Metric.mem_ball.1 hac
        · exact hc c hct
        · exact hmul.trans_lt (by rw [dist_comm]; exact Metric.mem_ball.1 hac)
    _ = ε := by ring

/-- Along an increasing approximate unit, `a * e → a` uniformly for `a` in a compact set. -/
theorem tendstoUniformlyOn_mul_left {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    {K : Set A} (hK : IsCompact K) : TendstoUniformlyOn (fun e a => a * e) id l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Cover `K` by finitely many balls of radius `ε / 3`, and use the eventual bound `‖e‖ ≤ 1`.
  obtain ⟨t, -, ht, hKt⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  have hconv : ∀ᶠ e in l, ∀ c ∈ t, dist c (c * e) < ε / 3 := (eventually_all_finite ht).2
    fun c _ => (Metric.tendsto_nhds.1 (hl.tendsto_mul_left c) (ε / 3) (by positivity)).mono
      fun _ h => by rwa [dist_comm]
  filter_upwards [hl.eventually_norm, hconv] with e he hc a ha
  obtain ⟨c, hct, hac⟩ := Set.mem_iUnion₂.1 (hKt ha)
  have hmul : dist (c * e) (a * e) ≤ dist c a := by
    rw [dist_eq_norm, dist_eq_norm, ← sub_mul]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) he)
  calc dist (id a) (a * e) ≤ dist a c + dist c (c * e) + dist (c * e) (a * e) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact Metric.mem_ball.1 hac
        · exact hc c hct
        · exact hmul.trans_lt (by rw [dist_comm]; exact Metric.mem_ball.1 hac)
    _ = ε := by ring

/-- Along an increasing approximate unit, two-sided multiplication `e * a * e` converges to `a`. -/
theorem tendsto_mul_mul {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e => e * a * e) l (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun e => ‖e * a - a‖ + ‖a * e - a‖) l (𝓝 (0 + 0)) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_right a)).add
      (tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_left a))
  rw [add_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [hl.eventually_norm] with e he
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hsplit : e * a * e - a = (e * a - a) * e + (a * e - a) := by noncomm_ring
  calc
    ‖e * a * e - a‖ ≤ ‖(e * a - a) * e‖ + ‖a * e - a‖ := hsplit ▸ norm_add_le _ _
    _ ≤ ‖e * a - a‖ * ‖e‖ + ‖a * e - a‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖e * a - a‖ * 1 + ‖a * e - a‖ := by gcongr
    _ = ‖e * a - a‖ + ‖a * e - a‖ := by rw [mul_one]

end Uniform

section Map

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- The image of an increasing approximate unit under a surjective star-algebra homomorphism of
C⋆-algebras is an increasing approximate unit. -/
theorem map {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (f : F)
    (hf : Function.Surjective f) : (l.map f).IsIncreasingApproximateUnit where
  toIsApproximateUnit := hl.toIsApproximateUnit.map f (map_continuous f) hf
  eventually_nonneg := eventually_map.mpr <| hl.eventually_nonneg.mono fun _ hx => map_nonneg f hx
  eventually_norm := eventually_map.mpr <| hl.eventually_norm.mono fun a ha =>
    (NonUnitalStarAlgHom.norm_apply_le f a).trans ha

end Map

end Filter.IsIncreasingApproximateUnit

namespace TauCeti.CStarAlgebra

open Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For a positive contraction `e` in a nonunital C⋆-algebra and any `a`, the C⋆-identity in the
unitization gives `‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖`. -/
theorem norm_mul_star_sub_star_sq_le {e : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) (a : A) :
    ‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖ := by
  have he_icc : (e : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
    CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨he₀, he₁⟩
  have h1_icc : 1 - (e : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
    Set.sub_mem_Icc_zero_iff_right.mpr he_icc
  obtain ⟨h1_nonneg, h1_norm⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.mp h1_icc
  have h1_star : star (1 - (e : A⁺¹)) = 1 - (e : A⁺¹) :=
    (IsSelfAdjoint.of_nonneg h1_nonneg).star_eq
  let b : A⁺¹ := (1 - (e : A⁺¹)) * star (a : A⁺¹)
  have hb_norm : ‖e * star a - star a‖ = ‖b‖ := by
    rw [norm_sub_rev, ← Unitization.norm_inr (𝕜 := ℂ), Unitization.inr_sub,
      Unitization.inr_mul, Unitization.inr_star]
    congr 1
    dsimp only [b]
    rw [sub_mul, one_mul]
  have hb_mul : b * star b = ((star a * a - e * (star a * a) : A) : A⁺¹) * (1 - (e : A⁺¹)) := by
    simp only [b, star_mul, star_star, h1_star, Unitization.inr_sub, Unitization.inr_mul,
      Unitization.inr_star]
    noncomm_ring
  calc
    ‖e * star a - star a‖ ^ 2 = ‖b‖ ^ 2 := by rw [hb_norm]
    _ = ‖b * star b‖ := by rw [sq, ← CStarRing.norm_self_mul_star]
    _ = ‖((star a * a - e * (star a * a) : A) : A⁺¹) * (1 - (e : A⁺¹))‖ := by rw [hb_mul]
    _ ≤ ‖((star a * a - e * (star a * a) : A) : A⁺¹)‖ * ‖1 - (e : A⁺¹)‖ := norm_mul_le _ _
    _ ≤ ‖star a * a - e * (star a * a)‖ * 1 := by
      rw [Unitization.norm_inr]
      exact mul_le_mul_of_nonneg_left h1_norm (norm_nonneg _)
    _ = ‖star a * a - e * (star a * a)‖ := mul_one _

/-- For a positive contraction `e` in a nonunital C⋆-algebra and any `a` and `z`, the C⋆-identity in
the unitization applied to `a * (1 - e)` gives `‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖`.
With `z` in a closed two-sided ideal `I` and `e` running through an approximate unit of `I`, the
last term tends to `0`; this bounds `‖mk I a‖ ^ 2` by `‖star a * a + z‖` in the quotient `A ⧸ I`.
-/
theorem norm_sub_mul_sq_le {e : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) (a z : A) :
    ‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖ := by
  have h1_icc : 1 - (e : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
    Set.sub_mem_Icc_zero_iff_right.mpr (CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨he₀, he₁⟩)
  obtain ⟨h1_nonneg, h1_norm⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.mp h1_icc
  have h1_star : star (1 - (e : A⁺¹)) = 1 - (e : A⁺¹) :=
    (IsSelfAdjoint.of_nonneg h1_nonneg).star_eq
  have hb : ((a - a * e : A) : A⁺¹) = (a : A⁺¹) * (1 - (e : A⁺¹)) := by
    rw [Unitization.inr_sub, Unitization.inr_mul, mul_sub, mul_one]
  have hb_mul : star ((a : A⁺¹) * (1 - (e : A⁺¹))) * ((a : A⁺¹) * (1 - (e : A⁺¹))) =
      (1 - (e : A⁺¹)) * ((star a * a + z : A) : A⁺¹) * (1 - (e : A⁺¹)) -
        (1 - (e : A⁺¹)) * ((z - z * e : A) : A⁺¹) := by
    simp only [star_mul, h1_star, Unitization.inr_add, Unitization.inr_sub, Unitization.inr_mul,
      Unitization.inr_star]
    noncomm_ring
  rw [← Unitization.norm_inr (𝕜 := ℂ), hb, sq, ← CStarRing.norm_star_mul_self, hb_mul,
    ← Unitization.norm_inr (𝕜 := ℂ) (star a * a + z), ← Unitization.norm_inr (𝕜 := ℂ) (z - z * e)]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [one_mul, mul_one] using
      norm_mul_le_of_le (norm_mul_le_of_le h1_norm le_rfl) h1_norm
  · simpa only [one_mul] using norm_mul_le_of_le h1_norm le_rfl

/-- For a positive contraction `e` in a nonunital C⋆-algebra and elements `x, b` satisfying
`star x * x ≤ b`, the C⋆-identity in the unitization gives `‖x - x * e‖ ^ 2 ≤ ‖b - b * e‖`. -/
theorem norm_sub_mul_sq_le_of_star_mul_self_le {e : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1)
    {x b : A} (hxb : star x * x ≤ b) :
    ‖x - x * e‖ ^ 2 ≤ ‖b - b * e‖ := by
  have h1_icc : 1 - (e : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
    Set.sub_mem_Icc_zero_iff_right.mpr (CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨he₀, he₁⟩)
  obtain ⟨h1_nonneg, h1_norm⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.mp h1_icc
  have h1_star : star (1 - (e : A⁺¹)) = 1 - (e : A⁺¹) :=
    (IsSelfAdjoint.of_nonneg h1_nonneg).star_eq
  let u : A⁺¹ := 1 - (e : A⁺¹)
  have hxu : ((x - x * e : A) : A⁺¹) = (x : A⁺¹) * u := by
    simp [u, mul_sub]
  have hbu : ((b - b * e : A) : A⁺¹) = (b : A⁺¹) * u := by
    simp [u, mul_sub]
  have hconj_eq : star ((x : A⁺¹) * u) * ((x : A⁺¹) * u) =
      star u * ((star x * x : A) : A⁺¹) * u := by
    simp only [star_mul, Unitization.inr_mul, Unitization.inr_star, mul_assoc]
  have hle : star u * ((star x * x : A) : A⁺¹) * u ≤ star u * (b : A⁺¹) * u :=
    star_left_conjugate_le_conjugate (Unitization.inr_le_inr_iff.mpr hxb) u
  have hnonneg : 0 ≤ star u * ((star x * x : A) : A⁺¹) * u :=
    star_left_conjugate_nonneg (Unitization.inr_nonneg_iff.mpr (star_mul_self_nonneg x)) u
  calc
    ‖x - x * e‖ ^ 2 = ‖((x : A⁺¹) * u)‖ ^ 2 := by rw [← Unitization.norm_inr (𝕜 := ℂ), hxu]
    _ = ‖star ((x : A⁺¹) * u) * ((x : A⁺¹) * u)‖ := by rw [sq, ← CStarRing.norm_star_mul_self]
    _ = ‖star u * ((star x * x : A) : A⁺¹) * u‖ := by rw [hconj_eq]
    _ ≤ ‖star u * (b : A⁺¹) * u‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hnonneg
    _ = ‖u * ((b : A⁺¹) * u)‖ := by rw [h1_star, mul_assoc]
    _ ≤ ‖u‖ * ‖(b : A⁺¹) * u‖ := norm_mul_le _ _
    _ ≤ 1 * ‖(b : A⁺¹) * u‖ := mul_le_mul_of_nonneg_right h1_norm (norm_nonneg _)
    _ = ‖b - b * e‖ := by rw [one_mul, ← hbu, Unitization.norm_inr]

/-- Along any filter of eventually positive contractions `e i`, if `star x * x ≤ b` and
`b * e i → b`, then `x * e i → x`. -/
theorem tendsto_mul_left_of_star_mul_self_le {ι : Type*} {l : Filter ι} {e : ι → A}
    (he₀ : ∀ᶠ i in l, 0 ≤ e i) (he₁ : ∀ᶠ i in l, ‖e i‖ ≤ 1)
    {x b : A} (hxb : star x * x ≤ b) (hb : Tendsto (fun i => b * e i) l (𝓝 b)) :
    Tendsto (fun i => x * e i) l (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb_norm : Tendsto (fun i => ‖b - b * e i‖) l (𝓝 0) := by
    simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp hb
  have hsqrt : Tendsto (fun i => Real.sqrt ‖b - b * e i‖) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp hb_norm
  refine squeeze_zero_norm' ?_ hsqrt
  filter_upwards [he₀, he₁] with i h0 h1
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_sub_rev]
  exact Real.le_sqrt_of_sq_le (norm_sub_mul_sq_le_of_star_mul_self_le h0 h1 hxb)

end TauCeti.CStarAlgebra

namespace NonUnitalStarSubalgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `B` is a closed nonunital `⋆`-subalgebra of a C⋆-algebra `A` and `star x * x ≤ b` for some
`b ∈ B`, then right multiplication by the canonical approximate unit of `B` converges to `x`. -/
theorem tendsto_mul_approximateUnit_of_star_mul_self_le {B : NonUnitalStarSubalgebra ℂ A}
    [IsClosed (B : Set A)] [StarOrderedRing B] {x b : A} (hb : b ∈ B) (hxb : star x * x ≤ b) :
    Tendsto (fun e : B => x * (e : A)) (CStarAlgebra.approximateUnit B) (𝓝 x) := by
  have hl := CStarAlgebra.increasingApproximateUnit B
  have hlim_b : Tendsto (fun e : B => b * (e : A)) (CStarAlgebra.approximateUnit B) (𝓝 b) :=
    (continuous_subtype_val.tendsto ⟨b, hb⟩).comp (hl.tendsto_mul_left ⟨b, hb⟩)
  exact TauCeti.CStarAlgebra.tendsto_mul_left_of_star_mul_self_le (e := fun e : B => (e : A))
    (hl.eventually_nonneg.mono fun _ he => he) hl.eventually_norm hxb hlim_b

end NonUnitalStarSubalgebra

