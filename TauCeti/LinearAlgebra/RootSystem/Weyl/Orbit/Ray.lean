/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.Ray
import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Rays and translates of Weyl orbits of weights

Two facts about the Weyl orbit `W λ` of a weight `λ` of a root pairing over a linearly ordered
field. When the Weyl group is finite, no two distinct weights of `W λ` lie in the same ray, so a
vector in `W λ` is determined by its direction. Adding a weight `χ` fixed by the Weyl group maps
`W λ` into `W (λ + χ)`, since `w λ + χ = w (λ + χ)`.

These are the hypotheses under which a path with velocities in `W λ` has a unique distinguished
presentation, and its central shift by `χ` has velocities in `W (λ + χ)`; see
`TauCeti/RepresentationTheory/LSPath/Distinguished.lean`.

Each Weyl orbit is stable under root reflections. For a root pairing over `ℤ`, an additive map
`f` from the weight lattice to a vector space carries
the reflection `s_i` in the root `αᵢ` to the reflection in `f αᵢ` along a linear form agreeing
with the coroot `αᵢ^∨`, so the image `f (W λ)` is stable under the latter. When `ι` is finite and
linear forms on `V` induce all simple coroots of a base `b`, no two distinct points of the realized
orbit `f (W λ)` lie in the same ray either, even when `f` is not injective on `M`. This is the
hypothesis under which the root operators preserve paths with velocities in `f (W λ)`; see
`TauCeti/RepresentationTheory/LSPath/OrbitStable.lean`.

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
* `RootPairing.mapsTo_preReflection_image_orbit_weylGroup`: the image `f (W λ)` of a Weyl orbit
  in a vector space is stable under the reflection in an image root `f αᵢ`, along a linear form
  agreeing with the coroot `αᵢ^∨`.
* `RootPairing.pairwise_not_sameRay_image_orbit_weylGroup`: when `ι` is finite and linear forms
  agree with the simple coroots of a base, no two distinct points of `f (W λ)` lie in the same ray.
-/

public section

namespace RootPairing

section Field

variable {ι 𝕜 V N : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] [AddCommGroup N] [Module 𝕜 N] (P : RootPairing ι 𝕜 V N)

/-- When the Weyl group is finite, no two distinct weights of a Weyl orbit lie in the same ray.
So a path with velocities in `W λ` has at most one distinguished presentation for `W λ`. -/
theorem pairwise_not_sameRay_orbit_weylGroup [Finite P.weylGroup] (lam : V) :
    (MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v :=
  fun _ hu _ hv huv h ↦ huv (h.eq_of_mem_orbit hu hv (Set.finite_range _))

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Adding a weight `χ` fixed by the Weyl group maps the Weyl orbit `W λ` to `W (λ + χ)`, since
`w λ + χ = w (λ + χ)`. So the central shift by `χ` transports paths with velocities in `W λ` to
paths with velocities in `W (λ + χ)`. -/
theorem mapsTo_add_orbit_weylGroup {χ : V} (hχ : ∀ w : P.weylGroup, w • χ = χ) (lam : V) :
    Set.MapsTo (· + χ) (MulAction.orbit P.weylGroup lam)
      (MulAction.orbit P.weylGroup (lam + χ)) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨w, by simp only [smul_add, hχ]⟩

end Field

section CommRing

variable {ι R V N : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R V N)

/-- A Weyl orbit is stable under reflection in any root along its coroot. -/
theorem mapsTo_preReflection_orbit_weylGroup (i : ι) (lam : V) :
    Set.MapsTo (Module.preReflection (P.root i) (P.coroot' i))
      (MulAction.orbit P.weylGroup lam) (MulAction.orbit P.weylGroup lam) := by
  intro v hv
  simpa [P.reflection_apply, Module.preReflection_apply] using
    MulAction.mapsTo_smul_orbit (weylGroup.ofIdx P i) lam hv

end CommRing

section Realization

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N)
  [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}

/-- An additive map `f` from the weight lattice intertwines the reflection `s_i` in the root `αᵢ`
with the reflection in the image root `f αᵢ` along a linear form `F` agreeing with the coroot
`αᵢ^∨` on the weight lattice. -/
theorem map_reflection_eq_preReflection (i : ι) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (m : M) :
    f (P.reflection i m) = Module.preReflection (f (P.root i)) F (f m) := by
  simp [P.reflection_apply, Module.preReflection_apply, hF, Int.cast_smul_eq_zsmul]

/-- The image `f (W λ)` of a Weyl orbit under an additive map `f` from the weight lattice is
stable under the reflection in the image root `f αᵢ` along a linear form `F` agreeing with the
coroot `αᵢ^∨` on the weight lattice. -/
theorem mapsTo_preReflection_image_orbit_weylGroup (i : ι) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    Set.MapsTo (Module.preReflection (f (P.root i)) F) (f '' MulAction.orbit P.weylGroup lam)
      (f '' MulAction.orbit P.weylGroup lam) := by
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine ⟨_, ⟨weylGroup.ofIdx P i * w, rfl⟩, ?_⟩
  dsimp only
  rw [mul_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul,
    P.map_reflection_eq_preReflection i hF]

/-- When `ι` is finite and linear forms `F i` on `V` agree with all simple coroots of a base `b`,
no two distinct points of the realized Weyl orbit `f (W λ)` lie in the same ray, even when `f` is
not injective on `M`. -/
theorem pairwise_not_sameRay_image_orbit_weylGroup [Finite ι] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (b : P.Base) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (f '' MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  let := Fintype.ofFinite ι
  rintro _ ⟨_, ⟨w₁, rfl⟩, rfl⟩ _ ⟨_, ⟨w₂, rfl⟩, rfl⟩ huv hray
  dsimp only at huv hray
  -- If every simple coroot kills `w₁ • lam` (or `w₂ • lam`), the Weyl group fixes it, so `u = v`.
  by_cases hc₁ : ∀ i ∈ b.support, P.coroot' i (w₁ • lam) = 0
  · refine huv (congrArg f ?_)
    have hfix := TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b hc₁ (w₂ * w₁⁻¹)
    rw [mul_smul, inv_smul_smul] at hfix
    exact hfix.symm
  by_cases hc₂ : ∀ i ∈ b.support, P.coroot' i (w₂ • lam) = 0
  · refine huv (congrArg f ?_)
    have hfix := TauCeti.smul_eq_self_of_forall_coroot'_eq_zero b hc₂ (w₁ * w₂⁻¹)
    rw [mul_smul, inv_smul_smul] at hfix
    exact hfix
  push Not at hc₁ hc₂
  obtain ⟨i₁, hi₁, hne₁⟩ := hc₁
  obtain ⟨i₂, hi₂, hne₂⟩ := hc₂
  have hu₀ : f (w₁ • lam) ≠ 0 := fun h0 ↦ by
    have := hF ⟨i₁, hi₁⟩ (w₁ • lam)
    rw [h0, map_zero] at this
    exact hne₁ (Int.cast_eq_zero.mp this.symm)
  have hv₀ : f (w₂ • lam) ≠ 0 := fun h0 ↦ by
    have := hF ⟨i₂, hi₂⟩ (w₂ • lam)
    rw [h0, map_zero] at this
    exact hne₂ (Int.cast_eq_zero.mp this.symm)
  obtain ⟨r, hr, hrv⟩ := hray.exists_pos_left hu₀ hv₀
  -- Every coroot is a `ℤ`-linear combination of simple coroots, so `w₂ • lam` scales all coroot
  -- pairings of `w₁ • lam` by `r`.
  have hscale : ∀ j : ι, (P.coroot' j (w₂ • lam) : 𝕜) = r * (P.coroot' j (w₁ • lam) : 𝕜) := by
    intro j
    suffices ∀ y ∈ Submodule.span ℤ (P.coroot '' b.support),
        (P.toLinearMap (w₂ • lam) y : 𝕜) = r * (P.toLinearMap (w₁ • lam) y : 𝕜) from
      this _ (b.coroot_mem_span_int j)
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      have := congrArg (F ⟨i, hi⟩) hrv
      simp only [map_smul, smul_eq_mul, hF ⟨i, hi⟩] at this
      exact this.symm
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ =>
      simp only [map_add, Int.cast_add, h₁, h₂, mul_add]
    | smul z y _ hy =>
      simp only [map_zsmul, smul_eq_mul, Int.cast_mul, hy]
      ring
  -- The sum of squares of all coroot pairings is Weyl-invariant and strictly positive on
  -- `w₁ • lam`.
  have hinv : ∀ w : P.weylGroup,
      ∑ j : ι, (P.coroot' j (w • lam) : 𝕜) ^ 2 = ∑ j : ι, (P.coroot' j lam : 𝕜) ^ 2 := by
    intro w
    rw [← (P.weylGroupToPerm w).sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [P.coroot'_weylGroupToPerm_smul]
  have hsum_eq : ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 =
      r ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 := by
    calc
      ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2
        = ∑ j : ι, (P.coroot' j (w₂ • lam) : 𝕜) ^ 2 := (hinv w₁).trans (hinv w₂).symm
      _ = ∑ j : ι, (r * (P.coroot' j (w₁ • lam) : 𝕜)) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ ↦ by rw [hscale j]
      _ = r ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 := by
        simp only [mul_pow, ← Finset.mul_sum]
  have hpos_sum : 0 < ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 := by
    refine lt_of_lt_of_le (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hne₁)) ?_
    exact Finset.single_le_sum (f := fun j ↦ (P.coroot' j (w₁ • lam) : 𝕜) ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i₁)
  have hr2 : r ^ 2 = 1 := by nlinarith
  have hr1 : r = 1 := by nlinarith
  exact huv (by rw [← hrv, hr1, one_smul])

end Realization

end RootPairing
