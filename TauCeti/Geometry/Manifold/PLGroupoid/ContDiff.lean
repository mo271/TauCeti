/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.MonotoneContinuity
public import TauCeti.Geometry.Manifold.Instances.HalfSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smooth coordinate changes are not piecewise linear

While every PL manifold is a topological manifold (`TauCeti.PLGroupoid_le_continuousGroupoid`),
smooth (or even real-analytic) transition maps do not lie in `TauCeti.PLGroupoid` except in
dimension zero. Comparing smooth and PL structures on a manifold therefore requires triangulation
and smoothing theory rather than an inclusion of structure groupoids.

The obstruction already appears in dimension one through the real-analytic homeomorphism
`x ↦ x + x ^ 3` (`TauCeti.cubicHomeomorph`):
* By strict convexity on `(0, ∞)` and strict concavity on `(-∞, 0)`, `x ↦ x + x ^ 3` fails the
  midpoint identity on every nondegenerate interval away from `0`, so `IsPLOn.exists_eqOn_Icc`
  shows that it is not `IsPLWithinAt` at any point of `ℝ` (`TauCeti.not_isPLWithinAt_add_cube`) and
  not `IsPLOn` on any set with nonempty interior (`TauCeti.not_isPLOn_add_cube`).
* Its derivative `1 + 3 * x ^ 2` never vanishes, so `cubicHomeomorph` and its inverse are `C^k` for
  all `k : WithTop ℕ∞`, including `k = ω` (`TauCeti.cubicHomeomorph_mem_contDiffGroupoid`).
* Given any nonzero vector `w` in a real normed space `E` and a continuous linear functional `φ`
  with `φ w = 1` (supplied on any nontrivial space by Hahn–Banach), the shear
  `x ↦ x + (φ x) ^ 3 • w` (`TauCeti.cubicShearHomeomorph`) is a `C^ω` diffeomorphism of `E` that is
  nowhere PL. Combining this with `TauCeti.PLGroupoid_eq_top` yields the exact characterization
  `contDiffGroupoid k 𝓘(ℝ, E) ≤ PLGroupoid 𝓘(ℝ, E) ↔ Subsingleton E`
  (`TauCeti.contDiffGroupoid_le_PLGroupoid_iff`).
* On the product half-space `{q : E × ℝ | 0 ≤ q.2}` the normal coordinate is always nontrivial, so
  `¬ contDiffGroupoid k (modelWithCornersHalfSpace E) ≤ PLGroupoid (modelWithCornersHalfSpace E)`
  holds unconditionally for every real normed space `E` and every `k : WithTop ℕ∞`
  (`TauCeti.not_contDiffGroupoid_le_PLGroupoid_modelWithCornersHalfSpace`).

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. (2) 41 (1940), 809–824.
-/

public section

open Function Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Nowhere-PL property of `x ↦ x + x ^ 3` -/

/-- If `x ↦ x + x ^ 3` agrees with a continuous affine map on `[a, b]`, then `(b - a) ^ 2 * (a + b)`
vanishes: evaluating at the midpoint `(a + b) / 2` isolates the cubic curvature residual. -/
private theorem add_cube_midpoint_eq_zero_of_eqOn_Icc {a b : ℝ} (hab : a ≤ b) {C : ℝ →ᴬ[ℝ] ℝ}
    (hC : EqOn (fun x : ℝ => x + x ^ 3) C (Icc a b)) :
    (3 / 8 : ℝ) * (b - a) ^ 2 * (a + b) = 0 := by
  have hm_mem : (2⁻¹ : ℝ) • a + (2⁻¹ : ℝ) • b ∈ Icc a b := by
    simp only [smul_eq_mul, mem_Icc]
    constructor <;> linarith
  have hmid :
      (fun x : ℝ => x + x ^ 3) ((2⁻¹ : ℝ) • a + (2⁻¹ : ℝ) • b) =
        (2⁻¹ : ℝ) • (fun x : ℝ => x + x ^ 3) a + (2⁻¹ : ℝ) • (fun x : ℝ => x + x ^ 3) b := by
    rw [hC hm_mem, hC (left_mem_Icc.mpr hab), hC (right_mem_Icc.mpr hab)]
    exact Convex.combo_affine_apply (f := (C : ℝ →ᵃ[ℝ] ℝ)) (by norm_num)
  simp only [smul_eq_mul] at hmid
  linarith [show (2⁻¹ * (a + a ^ 3) + 2⁻¹ * (b + b ^ 3)) -
      ((2⁻¹ * a + 2⁻¹ * b) + (2⁻¹ * a + 2⁻¹ * b) ^ 3) =
      (3 / 8 : ℝ) * (b - a) ^ 2 * (a + b) by ring]

/-- The cubic map `x ↦ x + x ^ 3` is not piecewise linear within `univ` at any point `t : ℝ`. -/
theorem not_isPLWithinAt_add_cube (t : ℝ) :
    ¬ IsPLWithinAt (fun x : ℝ => x + x ^ 3) univ t := by
  intro h
  obtain ⟨V, hV, hPA⟩ := isPLWithinAt_univ.mp h
  obtain ⟨ε, hε, A, B, hA, hB⟩ := hPA.isPLOn.exists_eqOn_Icc hV
  rcases le_or_gt 0 t with ht | ht
  · have hzero := add_cube_midpoint_eq_zero_of_eqOn_Icc (by linarith) hB
    have hpos : 0 < (3 / 8 : ℝ) * (t + ε - t) ^ 2 * (t + (t + ε)) := by
      have : t + ε - t = ε := by ring
      rw [this]
      have : 0 < t + (t + ε) := by linarith
      positivity
    linarith
  · have hzero := add_cube_midpoint_eq_zero_of_eqOn_Icc (by linarith) hA
    have hneg : (3 / 8 : ℝ) * (t - (t - ε)) ^ 2 * (t - ε + t) < 0 := by
      have : t - (t - ε) = ε := by ring
      rw [this]
      have h1 : 0 < (3 / 8 : ℝ) * ε ^ 2 := by positivity
      have h2 : t - ε + t < 0 := by linarith
      exact mul_neg_of_pos_of_neg h1 h2
    linarith

/-- The cubic map `x ↦ x + x ^ 3` is not piecewise linear within `s` at any interior point of
`s`. -/
theorem not_isPLWithinAt_add_cube_of_mem_interior {s : Set ℝ} {t : ℝ} (ht : t ∈ interior s) :
    ¬ IsPLWithinAt (fun x : ℝ => x + x ^ 3) s t := by
  intro h
  have hs : s ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  exact not_isPLWithinAt_add_cube t
    ((isPLWithinAt_inter hs).mp (by simpa only [univ_inter] using h))

/-- The cubic map `x ↦ x + x ^ 3` is not piecewise linear on any subset of `ℝ` with nonempty
interior; in particular, it is not PL on any nonempty open set. -/
theorem not_isPLOn_add_cube {s : Set ℝ} (hs : (interior s).Nonempty) :
    ¬ IsPLOn (fun x : ℝ => x + x ^ 3) s := by
  obtain ⟨t, ht⟩ := hs
  exact fun h => not_isPLWithinAt_add_cube_of_mem_interior ht (h.isPLWithinAt (interior_subset ht))

/-! ### The real-analytic homeomorphism `x ↦ x + x ^ 3` on `ℝ` -/

/-- The order isomorphism `x ↦ x + x ^ 3` of `ℝ`. -/
noncomputable def cubicOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun x : ℝ => x + x ^ 3)
    (strictMono_id.add (Odd.strictMono_pow (by decide))) fun y =>
    mem_range_of_exists_le_of_exists_ge (continuous_id.add (continuous_pow 3))
      ⟨min y 0, by
        rcases le_total y 0 with hy | hy
        · rw [min_eq_left hy]
          linarith [Odd.pow_nonpos (n := 3) (by decide) hy]
        · rw [min_eq_right hy]
          linarith⟩
      ⟨max y 0, by
        rcases le_total 0 y with hy | hy
        · rw [max_eq_left hy]
          linarith [pow_nonneg hy 3]
        · rw [max_eq_right hy]
          linarith⟩

/-- The homeomorphism `x ↦ x + x ^ 3` of `ℝ`. -/
noncomputable def cubicHomeomorph : ℝ ≃ₜ ℝ :=
  cubicOrderIso.toHomeomorph

@[simp]
theorem cubicOrderIso_apply (x : ℝ) : cubicOrderIso x = x + x ^ 3 := (rfl)

@[simp]
theorem cubicHomeomorph_apply (x : ℝ) : cubicHomeomorph x = x + x ^ 3 := (rfl)

/-- `TauCeti.cubicHomeomorph` fixes `0`. -/
theorem cubicHomeomorph_zero : cubicHomeomorph 0 = 0 := by simp

@[simp]
theorem cubicHomeomorph_symm_zero : cubicHomeomorph.symm 0 = 0 :=
  cubicHomeomorph.symm_apply_eq.mpr cubicHomeomorph_zero.symm

/-- `TauCeti.cubicHomeomorph` preserves and reflects nonnegativity. -/
theorem cubicHomeomorph_nonneg_iff {x : ℝ} : 0 ≤ cubicHomeomorph x ↔ 0 ≤ x := by
  conv_lhs => rw [← cubicHomeomorph_zero]
  exact cubicOrderIso.le_iff_le

@[simp]
theorem cubicHomeomorph_symm_nonneg_iff {y : ℝ} : 0 ≤ cubicHomeomorph.symm y ↔ 0 ≤ y := by
  conv_lhs => rw [← cubicHomeomorph_symm_zero]
  exact cubicOrderIso.symm.le_iff_le

/-- `TauCeti.cubicHomeomorph` has derivative `1 + 3 * x ^ 2` at every `x : ℝ`. -/
theorem hasDerivAt_cubicHomeomorph (x : ℝ) :
    HasDerivAt cubicHomeomorph (1 + 3 * x ^ 2) x :=
  HasDerivAt.add (hasDerivAt_id x) (by simpa using hasDerivAt_pow 3 x)

/-- `TauCeti.cubicHomeomorph` is `C^k` for every `k : WithTop ℕ∞` (including `∞` and `ω`). -/
theorem contDiff_cubicHomeomorph (k : WithTop ℕ∞) :
    ContDiff ℝ k cubicHomeomorph :=
  contDiff_id.add (contDiff_id.pow 3)

/-- The inverse of `TauCeti.cubicHomeomorph` is `C^k` for every `k : WithTop ℕ∞` (including `∞` and
`ω`), as `1 + 3 * x ^ 2` never vanishes. -/
theorem contDiff_cubicHomeomorph_symm (k : WithTop ℕ∞) :
    ContDiff ℝ k cubicHomeomorph.symm :=
  cubicHomeomorph.contDiff_symm_deriv (fun _ => by positivity)
    hasDerivAt_cubicHomeomorph (contDiff_cubicHomeomorph k)

/-- `TauCeti.cubicHomeomorph` belongs to `contDiffGroupoid k 𝓘(ℝ, ℝ)` for every `k : WithTop ℕ∞`. -/
theorem cubicHomeomorph_mem_contDiffGroupoid (k : WithTop ℕ∞) :
    cubicHomeomorph.toOpenPartialHomeomorph ∈ contDiffGroupoid k 𝓘(ℝ, ℝ) :=
  mem_groupoid_of_pregroupoid.mpr
    ⟨(contDiff_cubicHomeomorph k).contDiffOn, (contDiff_cubicHomeomorph_symm k).contDiffOn⟩

/-- `TauCeti.cubicHomeomorph` does not belong to `TauCeti.PLGroupoid 𝓘(ℝ, ℝ)`. -/
theorem cubicHomeomorph_notMem_PLGroupoid :
    cubicHomeomorph.toOpenPartialHomeomorph ∉ PLGroupoid 𝓘(ℝ, ℝ) := by
  intro h
  have hpl : IsPLOn cubicHomeomorph univ := by
    simpa only [mfld_simps] using ((mem_PLGroupoid_iff 𝓘(ℝ, ℝ)).mp h).1
  exact not_isPLOn_add_cube ⟨0, by simp⟩ hpl

/-! ### Lifting to arbitrary nontrivial real normed spaces -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Given `w : E` and `φ : StrongDual ℝ E` with `φ w = 1`, the map `x ↦ x + (φ x) ^ 3 • w` is a
homeomorphism of `E` whose action on the `φ`-coordinate is `TauCeti.cubicHomeomorph`. -/
noncomputable def cubicShearHomeomorph (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1) : E ≃ₜ E where
  toFun x := x + (φ x) ^ 3 • w
  invFun y := y + (cubicHomeomorph.symm (φ y) - φ y) • w
  left_inv x := by
    dsimp only
    have hφ : φ (x + (φ x) ^ 3 • w) = cubicHomeomorph (φ x) := by
      simp [map_add, map_smul, smul_eq_mul, hφw]
    rw [hφ, cubicHomeomorph.symm_apply_apply, cubicHomeomorph_apply]
    have hscalar : (φ x) ^ 3 + (φ x - (φ x + (φ x) ^ 3)) = 0 := by ring
    rw [add_assoc, ← add_smul, hscalar, zero_smul, add_zero]
  right_inv y := by
    dsimp only
    set t := cubicHomeomorph.symm (φ y)
    have hφ : φ (y + (t - φ y) • w) = t := by
      simp [map_add, map_smul, smul_eq_mul, hφw]
    have ht : t + t ^ 3 = φ y := cubicHomeomorph.apply_symm_apply (φ y)
    rw [hφ]
    have hscalar : (t - φ y) + t ^ 3 = 0 := by linarith
    rw [add_assoc, ← add_smul, hscalar, zero_smul, add_zero]
  continuous_toFun := continuous_id.add ((φ.continuous.pow 3).smul continuous_const)
  continuous_invFun :=
    continuous_id.add
      (((cubicHomeomorph.symm.continuous.comp φ.continuous).sub φ.continuous).smul continuous_const)

@[simp]
theorem cubicShearHomeomorph_apply (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1) (x : E) :
    cubicShearHomeomorph w φ hφw x = x + (φ x) ^ 3 • w := (rfl)

@[simp]
theorem cubicShearHomeomorph_symm_apply (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1) (y : E) :
    (cubicShearHomeomorph w φ hφw).symm y = y + (cubicHomeomorph.symm (φ y) - φ y) • w := (rfl)

/-- `TauCeti.cubicShearHomeomorph` is `C^k` for every `k : WithTop ℕ∞`. -/
theorem contDiff_cubicShearHomeomorph (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1)
    (k : WithTop ℕ∞) :
    ContDiff ℝ k (cubicShearHomeomorph w φ hφw) :=
  contDiff_id.add ((φ.contDiff.pow 3).smul contDiff_const)

/-- The inverse of `TauCeti.cubicShearHomeomorph` is `C^k` for every `k : WithTop ℕ∞`. -/
theorem contDiff_cubicShearHomeomorph_symm (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1)
    (k : WithTop ℕ∞) :
    ContDiff ℝ k (cubicShearHomeomorph w φ hφw).symm :=
  contDiff_id.add
    ((((contDiff_cubicHomeomorph_symm k).comp φ.contDiff).sub φ.contDiff).smul contDiff_const)

/-- `TauCeti.cubicShearHomeomorph` belongs to `contDiffGroupoid k 𝓘(ℝ, E)` for every
`k : WithTop ℕ∞`. -/
theorem cubicShearHomeomorph_mem_contDiffGroupoid (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1)
    (k : WithTop ℕ∞) :
    (cubicShearHomeomorph w φ hφw).toOpenPartialHomeomorph ∈ contDiffGroupoid k 𝓘(ℝ, E) :=
  mem_groupoid_of_pregroupoid.mpr
    ⟨(contDiff_cubicShearHomeomorph w φ hφw k).contDiffOn,
      (contDiff_cubicShearHomeomorph_symm w φ hφw k).contDiffOn⟩

/-- `TauCeti.cubicShearHomeomorph` is nowhere piecewise linear: restricting along the affine line
`t ↦ x₀ + (t - φ x₀) • w` and projecting by `φ` recovers `t ↦ t + t ^ 3`. -/
theorem not_isPLWithinAt_cubicShearHomeomorph (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1)
    (x₀ : E) :
    ¬ IsPLWithinAt (cubicShearHomeomorph w φ hφw) univ x₀ := by
  intro h
  let line : ℝ →ᴬ[ℝ] E :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) w).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ ℝ (x₀ - φ x₀ • w)
  have hline_pt : line (φ x₀) = x₀ := by
    simp [line]
  have hφ_line (t : ℝ) : φ (line t) = t := by
    simp [line, map_add, map_sub, map_smul, smul_eq_mul, hφw]
  rw [← hline_pt] at h
  have hcomp : IsPLWithinAt
      (φ.toContinuousAffineMap ∘ cubicShearHomeomorph w φ hφw ∘ line) univ (φ x₀) :=
    (φ.toContinuousAffineMap.isPLWithinAt univ _).comp
      (h.comp (line.isPLWithinAt univ (φ x₀)) (mapsTo_univ _ _)) (mapsTo_univ _ _)
  refine not_isPLWithinAt_add_cube (φ x₀) (hcomp.congr (fun t _ => ?_) ?_)
  · simp [Function.comp_apply, map_add, map_smul, smul_eq_mul, hφ_line t, hφw]
  · simp [Function.comp_apply, map_add, map_smul, smul_eq_mul, hφ_line (φ x₀), hφw]

/-- `TauCeti.cubicShearHomeomorph` does not belong to `TauCeti.PLGroupoid 𝓘(ℝ, E)`. -/
theorem cubicShearHomeomorph_notMem_PLGroupoid (w : E) (φ : StrongDual ℝ E) (hφw : φ w = 1) :
    (cubicShearHomeomorph w φ hφw).toOpenPartialHomeomorph ∉ PLGroupoid 𝓘(ℝ, E) := by
  intro h
  have hpl : IsPLOn (cubicShearHomeomorph w φ hφw) univ := by
    simpa only [mfld_simps] using ((mem_PLGroupoid_iff 𝓘(ℝ, E)).mp h).1
  exact not_isPLWithinAt_cubicShearHomeomorph w φ hφw 0 (hpl.isPLWithinAt (mem_univ 0))

/-- On any nontrivial real normed space `E`, `contDiffGroupoid k 𝓘(ℝ, E)` is not contained in
`TauCeti.PLGroupoid 𝓘(ℝ, E)`, even for real-analytic maps (`k = ω`). -/
theorem not_contDiffGroupoid_le_PLGroupoid [Nontrivial E] (k : WithTop ℕ∞) :
    ¬ contDiffGroupoid k 𝓘(ℝ, E) ≤ PLGroupoid 𝓘(ℝ, E) := by
  intro hle
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  obtain ⟨φ, -, hφv⟩ := exists_dual_vector ℝ v hnorm
  have hφv' : φ v = ‖v‖ := by simpa using hφv
  have hφw : φ (‖v‖⁻¹ • v) = 1 := by
    rw [map_smul, smul_eq_mul, hφv', inv_mul_cancel₀ hnorm]
  exact cubicShearHomeomorph_notMem_PLGroupoid (‖v‖⁻¹ • v) φ hφw
    (hle (cubicShearHomeomorph_mem_contDiffGroupoid (‖v‖⁻¹ • v) φ hφw k))

/-- **Smooth vs. PL groupoids.** On a real normed space `E` and for any regularity
`k : WithTop ℕ∞`, `contDiffGroupoid k 𝓘(ℝ, E)` is contained in `TauCeti.PLGroupoid 𝓘(ℝ, E)` if and
only if `E` is zero-dimensional (`Subsingleton E`). -/
@[simp]
theorem contDiffGroupoid_le_PLGroupoid_iff (k : WithTop ℕ∞) :
    contDiffGroupoid k 𝓘(ℝ, E) ≤ PLGroupoid 𝓘(ℝ, E) ↔ Subsingleton E := by
  refine ⟨fun hle => ?_, fun _ => by rw [PLGroupoid_eq_top]; exact le_top⟩
  by_contra hsub
  rw [not_subsingleton_iff_nontrivial] at hsub
  exact not_contDiffGroupoid_le_PLGroupoid k hle

end NormedSpace

/-! ### Unconditional non-inclusion on product half-spaces -/

section HalfSpace

/-- Apply `TauCeti.cubicHomeomorph` to the normal coordinate of `{q : E × ℝ | 0 ≤ q.2}`. -/
noncomputable def halfSpaceCubicHomeomorph (E : Type*) [TopologicalSpace E] :
    {q : E × ℝ | 0 ≤ q.2} ≃ₜ {q : E × ℝ | 0 ≤ q.2} where
  toFun q := ⟨(q.1.1, cubicHomeomorph q.1.2), by
    rw [mem_ofPred_eq, cubicHomeomorph_nonneg_iff]
    exact q.2⟩
  invFun q := ⟨(q.1.1, cubicHomeomorph.symm q.1.2), by
    rw [mem_ofPred_eq, cubicHomeomorph_symm_nonneg_iff]
    exact q.2⟩
  left_inv q := Subtype.ext (Prod.ext rfl (cubicHomeomorph.symm_apply_apply q.1.2))
  right_inv q := Subtype.ext (Prod.ext rfl (cubicHomeomorph.apply_symm_apply q.1.2))
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (cubicHomeomorph.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (cubicHomeomorph.symm.continuous.comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _

@[simp]
theorem coe_halfSpaceCubicHomeomorph_apply {E : Type*} [TopologicalSpace E]
    (q : {q : E × ℝ | 0 ≤ q.2}) :
    (halfSpaceCubicHomeomorph E q).1 = (q.1.1, cubicHomeomorph q.1.2) := (rfl)

@[simp]
theorem coe_halfSpaceCubicHomeomorph_symm_apply {E : Type*} [TopologicalSpace E]
    (q : {q : E × ℝ | 0 ≤ q.2}) :
    ((halfSpaceCubicHomeomorph E).symm q).1 = (q.1.1, cubicHomeomorph.symm q.1.2) := (rfl)

/-- `TauCeti.halfSpaceCubicHomeomorph E` belongs to
`contDiffGroupoid k (modelWithCornersHalfSpace E)` for every real normed space `E` and every
`k : WithTop ℕ∞`. -/
theorem halfSpaceCubicHomeomorph_mem_contDiffGroupoid (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : WithTop ℕ∞) :
    (halfSpaceCubicHomeomorph E).toOpenPartialHomeomorph ∈
      contDiffGroupoid k (modelWithCornersHalfSpace E) := by
  refine mem_groupoid_of_pregroupoid.mpr ⟨?_, ?_⟩
  · refine (contDiff_fst.prodMk ((contDiff_cubicHomeomorph k).comp contDiff_snd)).contDiffOn.congr
      fun q hq => ?_
    have hnonneg : 0 ≤ q.2 := by simpa only [range_modelWithCornersHalfSpace, mem_ofPred_eq]
      using hq.2
    simp [coe_modelWithCornersHalfSpace_symm_apply E hnonneg]
  · refine (contDiff_fst.prodMk
      ((contDiff_cubicHomeomorph_symm k).comp contDiff_snd)).contDiffOn.congr fun q hq => ?_
    have hnonneg : 0 ≤ q.2 := by simpa only [range_modelWithCornersHalfSpace, mem_ofPred_eq]
      using hq.2
    simp [coe_modelWithCornersHalfSpace_symm_apply E hnonneg]

/-- `TauCeti.halfSpaceCubicHomeomorph E` does not belong to
`TauCeti.PLGroupoid (modelWithCornersHalfSpace E)` for any real normed space `E`. -/
theorem halfSpaceCubicHomeomorph_notMem_PLGroupoid (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (halfSpaceCubicHomeomorph E).toOpenPartialHomeomorph ∉
      PLGroupoid (modelWithCornersHalfSpace E) := by
  intro h
  let I := modelWithCornersHalfSpace E
  have hpl : IsPLOn (I ∘ halfSpaceCubicHomeomorph E ∘ I.symm) (range I) := by
    simpa only [I, mfld_simps] using ((mem_PLGroupoid_iff I).mp h).1
  let inr : ℝ →ᴬ[ℝ] E × ℝ :=
    ((0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ)).toContinuousAffineMap
  let snd : E × ℝ →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  have hmap : MapsTo inr (Ici (0 : ℝ)) (range I) := fun t ht => by
    simpa only [I, inr, range_modelWithCornersHalfSpace, mem_ofPred_eq, mem_Ici,
      ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.id_apply] using ht
  have hcomp : IsPLOn (snd ∘ (I ∘ halfSpaceCubicHomeomorph E ∘ I.symm) ∘ inr) (Ici (0 : ℝ)) :=
    (isPLOn_continuousAffineMap snd univ).comp
      (hpl.comp (isPLOn_continuousAffineMap inr (Ici (0 : ℝ))) hmap) (mapsTo_univ _ _)
  refine not_isPLOn_add_cube (s := Ici (0 : ℝ)) ⟨1, by rw [interior_Ici]; norm_num⟩
    (hcomp.congr fun t ht => ?_)
  have ht' : 0 ≤ ((0 : E), t).2 := mem_Ici.mp ht
  simp only [I, inr, snd, Function.comp_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
    ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.coe_snd', modelWithCornersHalfSpace_apply,
    coe_modelWithCornersHalfSpace_symm_apply E ht', coe_halfSpaceCubicHomeomorph_apply,
    cubicHomeomorph_apply]

/-- For every real normed space `E` and every `k : WithTop ℕ∞`,
`contDiffGroupoid k (modelWithCornersHalfSpace E)` is not contained in
`TauCeti.PLGroupoid (modelWithCornersHalfSpace E)`. -/
theorem not_contDiffGroupoid_le_PLGroupoid_modelWithCornersHalfSpace (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : WithTop ℕ∞) :
    ¬ contDiffGroupoid k (modelWithCornersHalfSpace E) ≤
      PLGroupoid (modelWithCornersHalfSpace E) := fun hle =>
  halfSpaceCubicHomeomorph_notMem_PLGroupoid E
    (hle (halfSpaceCubicHomeomorph_mem_contDiffGroupoid E k))

end HalfSpace

end TauCeti
