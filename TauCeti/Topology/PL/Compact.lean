/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import TauCeti.Analysis.Convex.Polyhedron.Pi.Neighborhood
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.Compactness.Compact

/-!
# Finite PL decompositions on compact sets

A PL map on a compact subset of a real coordinate product admits a finite
piecewise-affine decomposition. Compactness thus lets one use finitely many
affine pieces to describe a map given by local PL data. The same holds on a
compact subset of a finite-dimensional real normed space, read in linear
coordinates.

In particular, coning a PL map with compact base can use a finite decomposition
at the apex, even though `IsPLOn` is defined using local decompositions.

Compactness cannot be dropped: `TauCeti.intSqInterp`, the continuous piecewise-linear
interpolation of `n ↦ n ^ 2` across unit integer intervals on `ℝ`, satisfies
`IsPLOn intSqInterp univ` (`TauCeti.isPLOn_intSqInterp`) because the intervals `[n, n + 1]`
form a locally finite polyhedral cover, yet `¬ IsPiecewiseAffineOn intSqInterp univ`
(`TauCeti.not_isPiecewiseAffineOn_intSqInterp`) because its slope `2 n + 1` on `[n, n + 1]`
takes infinitely many values.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*,
Springer (1972), Example 1.5(4), p. 5, and Corollary 2.3, p. 12.
-/

public section

open Set Filter Topology Metric

namespace TauCeti

variable {ι : Type*}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {s : Set (ι → ℝ)} {f : (ι → ℝ) → F}

/-- A PL map on a compact subset of a real coordinate product admits a finite
piecewise-affine decomposition on that set. -/
theorem IsPLOn.isPiecewiseAffineOn_of_isCompact (hf : IsPLOn f s) (hs : IsCompact s) :
    IsPiecewiseAffineOn f s := by
  classical
  have hlocal (x : s) : ∃ C ∈ 𝓝 x.1, IsConvexPolyhedron C ∧
      IsPiecewiseAffineOn f (s ∩ C) := by
    obtain ⟨V, hV, hpiece⟩ := isPLOn_iff.mp hf x.1 x.2
    obtain ⟨U, hU, hUV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hV
    obtain ⟨C, hC, hpoly, hCU⟩ := exists_isConvexPolyhedron_mem_nhds_pi hU
    exact ⟨C, hC, hpoly, hpiece.mono (fun y hy => hUV ⟨hCU hy.2, hy.1⟩)⟩
  choose C hC hpoly hpiece using hlocal
  -- Cutting each local decomposition by a polyhedral neighbourhood keeps its affine
  -- formulas valid on the whole selected cell, including overlaps in the finite subcover.
  obtain ⟨t, ht⟩ := hs.elim_nhdsWithin_subcover'
    (fun x hx => C ⟨x, hx⟩) (fun x hx => nhdsWithin_le_nhds (hC ⟨x, hx⟩))
  choose n D A hD hcover heq using
    fun x : t => isPiecewiseAffineOn_iff.mp (hpiece x.1)
  refine isPiecewiseAffineOn_of_finite (ι := Σ x : t, Fin (n x))
    (C := fun p => D p.1 p.2 ∩ C p.1.1)
    (A := fun p => A p.1 p.2)
    (fun p => (hD p.1 p.2).inter (hpoly p.1.1)) ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (ht hy)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨x, hx⟩ ⟨hy, hxy⟩)
    exact mem_iUnion.mpr ⟨⟨⟨x, hx⟩, j⟩, hj, hxy⟩
  · rintro ⟨x, j⟩ y ⟨hy, hyC, hyCneigh⟩
    exact heq x j ⟨⟨hy, hyCneigh⟩, hyC⟩

/-- A PL map on a compact subset of a finite-dimensional real normed space admits a finite
piecewise-affine decomposition on that set. -/
theorem IsPLOn.isPiecewiseAffineOn_of_isCompact_of_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → F} {s : Set E}
    (hf : IsPLOn f s) (hs : IsCompact s) : IsPiecewiseAffineOn f s := by
  -- Read `f` in linear coordinates `e : E ≃L[ℝ] ℝⁿ`, decompose there, and pull the cells back.
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let A : E →ᴬ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (e : E →L[ℝ] _).toContinuousAffineMap
  let B : (Fin (Module.finrank ℝ E) → ℝ) →ᴬ[ℝ] E := (e.symm : _ →L[ℝ] E).toContinuousAffineMap
  have hBA : ∀ x, B (A x) = x := fun x => e.symm_apply_apply x
  have hfB : IsPLOn (f ∘ B) (A '' s) :=
    hf.comp (isPLOn_continuousAffineMap B _) (by rintro _ ⟨x, hx, rfl⟩; simpa [hBA] using hx)
  have hdec := (hfB.isPiecewiseAffineOn_of_isCompact (hs.image A.continuous)).comp
    (isPiecewiseAffineOn_continuousAffineMap A s) (mapsTo_image A s)
  exact hdec.congr fun x _ => by simp [hBA]

/-- The continuous piecewise-linear interpolation of `n ↦ n ^ 2` across unit integer intervals
`[n, n + 1]` on `ℝ`. It is PL on all of `ℝ` (`isPLOn_intSqInterp`) but admits no finite
piecewise-affine decomposition on `ℝ` (`not_isPiecewiseAffineOn_intSqInterp`), showing that
compactness is essential in `IsPLOn.isPiecewiseAffineOn_of_isCompact_of_finiteDimensional`. -/
noncomputable def intSqInterp (x : ℝ) : ℝ :=
  (⌊x⌋ : ℝ) ^ 2 + (x - ⌊x⌋) * (2 * (⌊x⌋ : ℝ) + 1)

@[simp]
theorem intSqInterp_intCast (n : ℤ) : intSqInterp n = (n : ℝ) ^ 2 := by
  simp [intSqInterp]

/-- On each unit integer interval `[n, n + 1]`, `intSqInterp` agrees with the affine function of
slope `2 n + 1` interpolating `(n, n ^ 2)` and `(n + 1, (n + 1) ^ 2)`. -/
theorem intSqInterp_eq_on_Icc (n : ℤ) {x : ℝ} (hx : x ∈ Icc (n : ℝ) (n + 1)) :
    intSqInterp x = (n : ℝ) ^ 2 + (x - n) * (2 * (n : ℝ) + 1) := by
  rw [mem_Icc] at hx
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · have hfl : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨hx.1, hlt⟩
    simp [intSqInterp, hfl]
  · have hcast : (n : ℝ) + 1 = ((n + 1 : ℤ) : ℝ) := by push_cast; rfl
    rw [hcast, intSqInterp_intCast]
    push_cast
    ring

/-- `intSqInterp` is piecewise linear on all of `ℝ`: the unit integer intervals `[n, n + 1]` form
a locally finite family of convex polyhedra on each of which `intSqInterp` is affine. -/
theorem isPLOn_intSqInterp : IsPLOn intSqInterp univ := by
  let C (n : ℤ) : Set ℝ := Icc (n : ℝ) (n + 1)
  let A (n : ℤ) : ℝ →ᴬ[ℝ] ℝ :=
    (2 * (n : ℝ) + 1) • ContinuousAffineMap.id ℝ ℝ -
      ContinuousAffineMap.const ℝ ℝ ((n : ℝ) ^ 2 + n)
  refine isPLOn_of_locallyFinite (C := C) (A := A) ?_ ?_ ?_ ?_
  · intro x _
    refine ⟨Ioo ((⌊x⌋ : ℝ) - 1) ((⌊x⌋ : ℝ) + 2), Ioo_mem_nhds ?_ ?_, ?_⟩
    · linarith [Int.floor_le x]
    · linarith [Int.lt_floor_add_one x]
    · refine (({⌊x⌋ - 1, ⌊x⌋, ⌊x⌋ + 1} : Set ℤ).toFinite).subset fun n ⟨y, hyC, hyU⟩ => ?_
      rw [mem_Icc] at hyC
      rw [mem_Ioo] at hyU
      have h1 : ((⌊x⌋ - 1 : ℤ) : ℝ) < ((n + 1 : ℤ) : ℝ) := by push_cast; linarith
      have h2 : (n : ℝ) < ((⌊x⌋ + 2 : ℤ) : ℝ) := by push_cast; linarith
      have h1' : ⌊x⌋ - 1 < n + 1 := Int.cast_lt.mp h1
      have h2' : n < ⌊x⌋ + 2 := Int.cast_lt.mp h2
      simp only [mem_insert_iff, mem_singleton_iff]
      omega
  · intro n
    have h1 := isConvexPolyhedron_setOf_le
      (ContinuousAffineMap.const ℝ ℝ (n : ℝ) - ContinuousAffineMap.id ℝ ℝ)
    have h2 := isConvexPolyhedron_setOf_le
      (ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ ((n : ℝ) + 1))
    convert h1.inter h2 using 1
    ext x
    simp [C, mem_Icc]
  · intro x _
    exact mem_iUnion.mpr ⟨⌊x⌋, mem_Icc.mpr ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩⟩
  · rintro n x ⟨-, hx⟩
    rw [intSqInterp_eq_on_Icc n hx]
    simp only [A, ContinuousAffineMap.sub_apply, ContinuousAffineMap.smul_apply,
      ContinuousAffineMap.coe_id, id_eq, ContinuousAffineMap.coe_const, Function.const_apply,
      smul_eq_mul]
    ring

/-- `intSqInterp` admits no finite piecewise-affine decomposition on `ℝ`: each interval
`[k, k + 1]` must share at least two distinct sample points with one of the finitely many cells,
forcing that cell's affine piece to have slope `2 k + 1`, which cannot happen for `m + 1` distinct
integers `k` using only `m` cells. -/
theorem not_isPiecewiseAffineOn_intSqInterp : ¬ IsPiecewiseAffineOn intSqInterp univ := by
  intro h
  obtain ⟨m, C, A, -, hcov, heq⟩ := isPiecewiseAffineOn_iff.mp h
  have hslope (k : ℕ) : ∃ i : Fin m, (A i).contLinear 1 = 2 * (k : ℝ) + 1 := by
    let pt (j : Fin (m + 1)) : ℝ := (k : ℝ) + (j : ℝ) / ((m : ℝ) + 1)
    have hpt (j : Fin (m + 1)) : pt j ∈ Icc ((k : ℤ) : ℝ) (((k : ℤ) : ℝ) + 1) := by
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hj : (j : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast j.is_lt.le
      rw [mem_Icc, Int.cast_natCast]
      exact ⟨le_add_of_nonneg_right (by positivity),
        add_le_add_right ((div_le_one hm).mpr hj) _⟩
    choose cell hcell using fun j => mem_iUnion.mp (hcov (mem_univ (pt j)))
    obtain ⟨j₁, j₂, hjne, hceq⟩ := Fintype.exists_ne_map_eq_of_card_lt cell (by simp)
    refine ⟨cell j₁, ?_⟩
    have hv₁ := heq (cell j₁) ⟨mem_univ _, hcell j₁⟩
    have hv₂ := heq (cell j₁) ⟨mem_univ _, hceq ▸ hcell j₂⟩
    have hlin : (pt j₁ - pt j₂) * (A (cell j₁)).contLinear 1 =
        intSqInterp (pt j₁) - intSqInterp (pt j₂) := by
      have := (A (cell j₁)).contLinear_apply_vsub (pt j₁) (pt j₂)
      rw [vsub_eq_sub, vsub_eq_sub, ← hv₁, ← hv₂] at this
      simpa [mul_one] using ((A (cell j₁)).contLinear.map_smul (pt j₁ - pt j₂) (1 : ℝ)).symm.trans
        (by simpa [mul_one] using this)
    rw [intSqInterp_eq_on_Icc (k : ℤ) (hpt j₁), intSqInterp_eq_on_Icc (k : ℤ) (hpt j₂),
      Int.cast_natCast] at hlin
    have hne : pt j₁ - pt j₂ ≠ 0 := by
      simp only [pt, add_sub_add_left_eq_sub, ← sub_div]
      refine div_ne_zero (sub_ne_zero.mpr ?_) (by positivity)
      exact_mod_cast Fin.val_ne_of_ne hjne
    exact mul_left_cancel₀ hne (by linear_combination hlin)
  choose idx hidx using fun k : Fin (m + 1) => hslope k
  obtain ⟨k₁, k₂, hkne, hkeq⟩ := Fintype.exists_ne_map_eq_of_card_lt idx (by simp)
  have hval : (2 : ℝ) * (k₁ : ℝ) + 1 = 2 * (k₂ : ℝ) + 1 := by
    rw [← hidx k₁, hkeq, hidx k₂]
  have hkval : (k₁ : ℝ) = (k₂ : ℝ) := by linarith
  exact hkne (Fin.ext (Nat.cast_injective hkval))

end TauCeti
