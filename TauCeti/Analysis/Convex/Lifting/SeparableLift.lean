/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.FiniteModel
import TauCeti.Analysis.Convex.Lifting.Basic

/-!
# Separable-height lifting for finite mixed-integer models

When each nonlinear residual of a `FiniteModel` decomposes as a weighted sum
`g i x = ∑ j, weight i j * component j x` with nonnegative weights `0 ≤ weight i j`, replacing the
aggregate residuals by component epigraph inequalities `component j (project z) - height z j ≤ 0`
and affine budget rows `∑ j, weight i j * height z j ≤ 0` produces an exact extended formulation
(`FiniteModel.separableLift`). Under nonnegative weights, the exact projection, feasible-minimum,
and attainment results reduce directly to the order-theoretic lifting theorem
`TauCeti.ConvexLifting.image_fst_liftedSet` in `TauCeti.Analysis.Convex.Lifting.Basic`.

## Main definitions

* `TauCeti.ConvexLifting.FiniteModel.separableLift`: separable-height lift with nonnegative
  weights.

## Main statements

* `TauCeti.ConvexLifting.FiniteModel.separableLift_nonlinear_iff` and
  `TauCeti.ConvexLifting.FiniteModel.separableLift_affine_iff`: characterization of the epigraph
  and affine budget rows of `separableLift`.
* `TauCeti.ConvexLifting.FiniteModel.mem_separableLift_feasibleOn_iff` and
  `TauCeti.ConvexLifting.FiniteModel.mem_separableLift_relaxationOn_iff`: membership
  characterization without weight or decomposition hypotheses.
* `TauCeti.ConvexLifting.FiniteModel.image_project_separableLift_feasibleOn` and
  `TauCeti.ConvexLifting.FiniteModel.image_project_separableLift_relaxationOn`: exact projection
  under `project`.
* `TauCeti.ConvexLifting.FiniteModel.mem_separableLift_feasibleOn_and_isMinOn_iff`,
  `TauCeti.ConvexLifting.FiniteModel.mem_separableLift_relaxationOn_and_isMinOn_iff`,
  `TauCeti.ConvexLifting.FiniteModel.exists_mem_separableLift_feasibleOn_isMinOn_iff`, and
  `TauCeti.ConvexLifting.FiniteModel.exists_mem_separableLift_relaxationOn_isMinOn_iff`:
  equivalence of feasible minima and attainment in both the mixed-integer and relaxed models.

## References

* H. Hijazi, P. Bonami and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (4 October 2013),
  pp. 1–14, §3.1 (p. 4).
* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global optimization*,
  Mathematical Programming 103 (2005), 225–249, §2.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.ConvexLifting

namespace FiniteModel

variable {n m l r q : ℕ}

/-- Lift a separable model by introducing `q` continuous component heights with epigraph residuals
`component j (project z) - height z j ≤ 0` and affine aggregate budget rows
`∑ j, weight i j * height z j ≤ 0`. Original affine rows, integer bounds, and objective
coefficients are retained. -/
def separableLift (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    FiniteModel (n + q) m q (r + l) where
  g := fun j z => component j (project z) - height z j
  A := Fin.append (fun k => Fin.append (d.A k) (fun _ => 0))
    (fun i => Fin.append (fun _ => 0) (weight i))
  B := Fin.append d.B (fun _ _ => 0)
  rhs := Fin.append d.rhs (fun _ => 0)
  c1 := Fin.append d.c1 (fun _ => 0)
  c2 := d.c2
  lo := d.lo
  hi := d.hi

/-- The mixed-integer feasible points satisfying the domain, original affine rows, and bounded
integer constraints (before imposing the nonlinear residuals `d.g`). -/
private def baseFeasibleOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
      x.2 = fun j => (y j : ℝ)}

/-- The relaxed points satisfying the domain, original affine rows, and real box bounds (before
imposing the nonlinear residuals `d.g`). -/
private def baseRelaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j}

section SeparableLift

variable (d : FiniteModel n m l r)
  (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)

/-- Evaluating the nonlinear residual field of `separableLift`. -/
@[simp]
theorem separableLift_g (j : Fin q) (z : Point (n + q) m) :
    (d.separableLift component weight).g j z = component j (project z) - height z j := (rfl)

/-- The continuous-block affine matrix of `separableLift`. -/
theorem separableLift_A :
    (d.separableLift component weight).A =
      Fin.append (fun k => Fin.append (d.A k) (fun _ => 0))
        (fun i => Fin.append (fun _ => 0) (weight i)) := (rfl)

/-- The integer-block affine matrix of `separableLift`. -/
theorem separableLift_B :
    (d.separableLift component weight).B = Fin.append d.B (fun _ _ => 0) := (rfl)

/-- The right-hand side vector of `separableLift`. -/
theorem separableLift_rhs :
    (d.separableLift component weight).rhs = Fin.append d.rhs (fun _ => 0) := (rfl)

/-- Continuous-block objective coefficients of `separableLift`. -/
@[simp]
theorem separableLift_c1 :
    (d.separableLift component weight).c1 = Fin.append d.c1 (fun _ => 0) := (rfl)

/-- Integer-block objective coefficients of `separableLift`. -/
@[simp]
theorem separableLift_c2 :
    (d.separableLift component weight).c2 = d.c2 := (rfl)

/-- Integer-block lower bounds of `separableLift`. -/
@[simp]
theorem separableLift_lo :
    (d.separableLift component weight).lo = d.lo := (rfl)

/-- Integer-block upper bounds of `separableLift`. -/
@[simp]
theorem separableLift_hi :
    (d.separableLift component weight).hi = d.hi := (rfl)

/-- The objective of `separableLift` pulls back `d.objective` along `project`. -/
@[simp]
theorem objective_separableLift (z : Point (n + q) m) :
    (d.separableLift component weight).objective z = d.objective (project z) :=
  d.objective_eq_comp_project (d.separableLift component weight) rfl rfl z

/-- The nonlinear constraints of `separableLift` state that each height dominates its component. -/
theorem separableLift_nonlinear_iff (z : Point (n + q) m) :
    (∀ j, (d.separableLift component weight).g j z ≤ 0) ↔
      ∀ j, component j (project z) ≤ height z j := by
  simp

/-- The affine constraints of `separableLift` split into the original affine constraints at
`project z` and the weighted sum budget rows on `height z`. -/
theorem separableLift_affine_iff (z : Point (n + q) m) :
    (∀ k, (∑ i, (d.separableLift component weight).A k i * z.1 i) +
        (∑ j, (d.separableLift component weight).B k j * z.2 j) ≤
          (d.separableLift component weight).rhs k) ↔
      (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        ∀ i, ∑ j, weight i j * height z j ≤ 0 := by
  simp [separableLift_A, separableLift_B, separableLift_rhs, Fin.forall_fin_add]

/-- Characterization of mixed-integer feasibility in `separableLift`: domain membership,
component-height inequalities, original affine rows, weighted budget rows, and bounded integer
coordinates. -/
theorem mem_separableLift_feasibleOn_iff {D : Set (Point n m)} {z : Point (n + q) m} :
    z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ↔
      project z ∈ D ∧
        (∀ j, component j (project z) ≤ height z j) ∧
        (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        (∀ i, ∑ j, weight i j * height z j ≤ 0) ∧
        ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
          (project z).2 = fun j => (y j : ℝ) := by
  rw [mem_feasibleOn_iff, separableLift_nonlinear_iff, separableLift_affine_iff]
  simp only [mem_preimage, separableLift_lo, separableLift_hi, project_snd]
  tauto

/-- Characterization of continuous-relaxation membership in `separableLift`: domain membership,
component-height inequalities, original affine rows, weighted budget rows, and real box bounds. -/
theorem mem_separableLift_relaxationOn_iff {D : Set (Point n m)} {z : Point (n + q) m} :
    z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D) ↔
      project z ∈ D ∧
        (∀ j, component j (project z) ≤ height z j) ∧
        (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        (∀ i, ∑ j, weight i j * height z j ≤ 0) ∧
        ∀ j, d.lo j ≤ (project z).2 j ∧ (project z).2 j ≤ d.hi j := by
  rw [mem_relaxationOn_iff, separableLift_nonlinear_iff, separableLift_affine_iff]
  simp only [mem_preimage, separableLift_lo, separableLift_hi, project_snd]
  tauto

private theorem feasibleOn_eq_originalSet (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    d.feasibleOn D =
      originalSet (d.baseFeasibleOn D) (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
  ext x
  simp only [mem_feasibleOn_iff, mem_originalSet_iff, baseFeasibleOn, mem_ofPred_eq,
    Pi.le_def, Pi.zero_apply]
  refine ⟨fun ⟨hxD, hxg, hxA, hy⟩ => ⟨⟨hxD, hxA, hy⟩, fun i => by simpa [hg i x hxD] using hxg i⟩,
    fun ⟨⟨hxD, hxA, hy⟩, hxg⟩ => ⟨hxD, fun i => by simpa [hg i x hxD] using hxg i, hxA, hy⟩⟩

private theorem relaxationOn_eq_originalSet (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    d.relaxationOn D =
      originalSet (d.baseRelaxationOn D) (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
  ext x
  simp only [mem_relaxationOn_iff, mem_originalSet_iff, baseRelaxationOn, mem_ofPred_eq,
    Pi.le_def, Pi.zero_apply]
  refine ⟨fun ⟨hxD, hxg, hxA, hb⟩ => ⟨⟨hxD, hxA, hb⟩, fun i => by simpa [hg i x hxD] using hxg i⟩,
    fun ⟨⟨hxD, hxA, hb⟩, hxg⟩ => ⟨hxD, fun i => by simpa [hg i x hxD] using hxg i, hxA, hb⟩⟩

private theorem mem_separableLift_feasibleOn_iff_mem_liftedSet (D : Set (Point n m))
    (z : Point (n + q) m) :
    z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ↔
      splitEquiv n m q z ∈
        liftedSet (d.baseFeasibleOn D) Set.univ (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
  rw [mem_separableLift_feasibleOn_iff]
  simp only [mem_liftedSet_iff, splitEquiv_apply, baseFeasibleOn, mem_ofPred_eq, mem_univ,
    true_and, Pi.le_def, Pi.zero_apply]
  tauto

private theorem mem_separableLift_relaxationOn_iff_mem_liftedSet (D : Set (Point n m))
    (z : Point (n + q) m) :
    z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D) ↔
      splitEquiv n m q z ∈
        liftedSet (d.baseRelaxationOn D) Set.univ (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
  rw [mem_separableLift_relaxationOn_iff]
  simp only [mem_liftedSet_iff, splitEquiv_apply, baseRelaxationOn, mem_ofPred_eq, mem_univ,
    true_and, Pi.le_def, Pi.zero_apply]
  tauto

private theorem image_splitEquiv_separableLift_feasibleOn (D : Set (Point n m)) :
    splitEquiv n m q '' (d.separableLift component weight).feasibleOn (project ⁻¹' D) =
      liftedSet (d.baseFeasibleOn D) Set.univ (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
  have hpre : (d.separableLift component weight).feasibleOn (project ⁻¹' D) =
      splitEquiv n m q ⁻¹' liftedSet (d.baseFeasibleOn D) Set.univ (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) :=
    Set.ext (mem_separableLift_feasibleOn_iff_mem_liftedSet d component weight D)
  rw [hpre, (splitEquiv n m q).image_preimage]

private theorem image_splitEquiv_separableLift_relaxationOn (D : Set (Point n m)) :
    splitEquiv n m q '' (d.separableLift component weight).relaxationOn (project ⁻¹' D) =
      liftedSet (d.baseRelaxationOn D) Set.univ (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
  have hpre : (d.separableLift component weight).relaxationOn (project ⁻¹' D) =
      splitEquiv n m q ⁻¹' liftedSet (d.baseRelaxationOn D) Set.univ (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) :=
    Set.ext (mem_separableLift_relaxationOn_iff_mem_liftedSet d component weight D)
  rw [hpre, (splitEquiv n m q).image_preimage]

/-- Graph insertion of actual component values into the mixed-integer feasible set of
`separableLift`. Does not require nonnegative weights. -/
theorem appendHeight_mem_separableLift_feasibleOn {D : Set (Point n m)} {x : Point n m}
    (hg : ∀ i, d.g i x = ∑ j, weight i j * component j x)
    (hx : x ∈ d.feasibleOn D) :
    appendHeight x (fun j => component j x) ∈
      (d.separableLift component weight).feasibleOn (project ⁻¹' D) := by
  rw [mem_separableLift_feasibleOn_iff_mem_liftedSet, splitEquiv_apply, project_appendHeight,
    height_appendHeight]
  obtain ⟨hxD, hxg, hxA, hy⟩ := mem_feasibleOn_iff.1 hx
  have horig : x ∈ originalSet (d.baseFeasibleOn D) (fun x j => component j x)
      (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) :=
    mem_originalSet_iff.2 ⟨⟨hxD, hxA, hy⟩, fun i => by
      simpa only [hg i, Pi.zero_apply] using hxg i⟩
  exact graph_mem_liftedSet (mem_univ _) horig

/-- Graph insertion of actual component values into the continuous relaxation of `separableLift`.
Does not require nonnegative weights. -/
theorem appendHeight_mem_separableLift_relaxationOn {D : Set (Point n m)} {x : Point n m}
    (hg : ∀ i, d.g i x = ∑ j, weight i j * component j x)
    (hx : x ∈ d.relaxationOn D) :
    appendHeight x (fun j => component j x) ∈
      (d.separableLift component weight).relaxationOn (project ⁻¹' D) := by
  rw [mem_separableLift_relaxationOn_iff_mem_liftedSet, splitEquiv_apply, project_appendHeight,
    height_appendHeight]
  obtain ⟨hxD, hxg, hxA, hb⟩ := mem_relaxationOn_iff.1 hx
  have horig : x ∈ originalSet (d.baseRelaxationOn D) (fun x j => component j x)
      (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) :=
    mem_originalSet_iff.2 ⟨⟨hxD, hxA, hb⟩, fun i => by
      simpa only [hg i, Pi.zero_apply] using hxg i⟩
  exact graph_mem_liftedSet (mem_univ _) horig

/-- Under nonnegative weights, every mixed-integer feasible point of `separableLift` projects to
a mixed-integer feasible point of `d`. -/
theorem project_mem_feasibleOn_of_mem_separableLift {D : Set (Point n m)}
    (hw : ∀ i j, 0 ≤ weight i j) {z : Point (n + q) m}
    (hg : ∀ i, d.g i (project z) = ∑ j, weight i j * component j (project z))
    (hz : z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D)) :
    project z ∈ d.feasibleOn D := by
  rw [mem_separableLift_feasibleOn_iff_mem_liftedSet, splitEquiv_apply] at hz
  have hm : MonotoneOn (fun (y : Fin q → ℝ) (i : Fin l) => ∑ j, weight i j * y j) Set.univ :=
    fun _ _ _ _ hy i => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw i j)
  obtain ⟨hbase, hsum⟩ := mem_originalSet_iff.1 (fst_mem_originalSet hm (mem_univ _) hz)
  exact mem_feasibleOn_iff.2 ⟨hbase.1, fun i => by
    simpa only [Pi.zero_apply, ← hg i] using hsum i, hbase.2⟩

/-- Under nonnegative weights, every relaxed point of `separableLift` projects to a relaxed point
of `d`. -/
theorem project_mem_relaxationOn_of_mem_separableLift {D : Set (Point n m)}
    (hw : ∀ i j, 0 ≤ weight i j) {z : Point (n + q) m}
    (hg : ∀ i, d.g i (project z) = ∑ j, weight i j * component j (project z))
    (hz : z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D)) :
    project z ∈ d.relaxationOn D := by
  rw [mem_separableLift_relaxationOn_iff_mem_liftedSet, splitEquiv_apply] at hz
  have hm : MonotoneOn (fun (y : Fin q → ℝ) (i : Fin l) => ∑ j, weight i j * y j) Set.univ :=
    fun _ _ _ _ hy i => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw i j)
  obtain ⟨hbase, hsum⟩ := mem_originalSet_iff.1 (fst_mem_originalSet hm (mem_univ _) hz)
  exact mem_relaxationOn_iff.2 ⟨hbase.1, fun i => by
    simpa only [Pi.zero_apply, ← hg i] using hsum i, hbase.2⟩

/-- **Exact mixed-integer projection under separable-height lifting.** -/
theorem image_project_separableLift_feasibleOn (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    project '' (d.separableLift component weight).feasibleOn (project ⁻¹' D) =
      d.feasibleOn D := by
  have hm : MonotoneOn (fun (y : Fin q → ℝ) (i : Fin l) => ∑ j, weight i j * y j) Set.univ :=
    fun _ _ _ _ hy i => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw i j)
  have hfst : (project : Point (n + q) m → Point n m) = Prod.fst ∘ splitEquiv n m q :=
    funext fun z => by simp [splitEquiv_apply]
  calc project '' (d.separableLift component weight).feasibleOn (project ⁻¹' D)
      = (Prod.fst ∘ splitEquiv n m q) ''
          (d.separableLift component weight).feasibleOn (project ⁻¹' D) := by rw [hfst]
    _ = Prod.fst ''
          (splitEquiv n m q '' (d.separableLift component weight).feasibleOn (project ⁻¹' D)) :=
        Set.image_comp _ _ _
    _ = Prod.fst '' liftedSet (d.baseFeasibleOn D) Set.univ (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
        rw [image_splitEquiv_separableLift_feasibleOn]
    _ = originalSet (d.baseFeasibleOn D) (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) :=
        image_fst_liftedSet (mapsTo_univ _ _) hm
    _ = d.feasibleOn D := (feasibleOn_eq_originalSet d component weight D hg).symm

/-- **Exact continuous-relaxation projection under separable-height lifting.** -/
theorem image_project_separableLift_relaxationOn (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    project '' (d.separableLift component weight).relaxationOn (project ⁻¹' D) =
      d.relaxationOn D := by
  have hm : MonotoneOn (fun (y : Fin q → ℝ) (i : Fin l) => ∑ j, weight i j * y j) Set.univ :=
    fun _ _ _ _ hy i => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw i j)
  have hfst : (project : Point (n + q) m → Point n m) = Prod.fst ∘ splitEquiv n m q :=
    funext fun z => by simp [splitEquiv_apply]
  calc project '' (d.separableLift component weight).relaxationOn (project ⁻¹' D)
      = (Prod.fst ∘ splitEquiv n m q) ''
          (d.separableLift component weight).relaxationOn (project ⁻¹' D) := by rw [hfst]
    _ = Prod.fst ''
          (splitEquiv n m q '' (d.separableLift component weight).relaxationOn (project ⁻¹' D)) :=
        Set.image_comp _ _ _
    _ = Prod.fst '' liftedSet (d.baseRelaxationOn D) Set.univ (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) := by
        rw [image_splitEquiv_separableLift_relaxationOn]
    _ = originalSet (d.baseRelaxationOn D) (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) (0 : Fin l → ℝ) :=
        image_fst_liftedSet (mapsTo_univ _ _) hm
    _ = d.relaxationOn D := (relaxationOn_eq_originalSet d component weight D hg).symm

/-- Equivalence of `IsMinOn` between `separableLift` and the original mixed-integer model. -/
theorem isMinOn_separableLift_feasibleOn_iff (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) (z : Point (n + q) m) :
    IsMinOn (d.separableLift component weight).objective
      ((d.separableLift component weight).feasibleOn (project ⁻¹' D)) z ↔
      IsMinOn d.objective (d.feasibleOn D) (project z) := by
  rw [isMinOn_iff, isMinOn_iff,
    ← image_project_separableLift_feasibleOn d component weight D hw hg, forall_mem_image]
  simp only [objective_separableLift]

/-- Equivalence of `IsMinOn` on the continuous relaxation between `separableLift` and the original
model. -/
theorem isMinOn_separableLift_relaxationOn_iff (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) (z : Point (n + q) m) :
    IsMinOn (d.separableLift component weight).objective
      ((d.separableLift component weight).relaxationOn (project ⁻¹' D)) z ↔
      IsMinOn d.objective (d.relaxationOn D) (project z) := by
  rw [isMinOn_iff, isMinOn_iff,
    ← image_project_separableLift_relaxationOn d component weight D hw hg, forall_mem_image]
  simp only [objective_separableLift]

/-- **Feasible minimum equivalence under separable-height lifting.** -/
theorem mem_separableLift_feasibleOn_and_isMinOn_iff (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) (z : Point (n + q) m) :
    (z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ∧
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).feasibleOn (project ⁻¹' D)) z) ↔
      z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ∧
        project z ∈ d.feasibleOn D ∧ IsMinOn d.objective (d.feasibleOn D) (project z) := by
  constructor
  · rintro ⟨hz, hmin⟩
    have hzD : project z ∈ D :=
      (d.separableLift component weight).feasibleOn_subset (project ⁻¹' D) hz
    exact ⟨hz,
      project_mem_feasibleOn_of_mem_separableLift d component weight hw (fun i => hg i _ hzD) hz,
      (isMinOn_separableLift_feasibleOn_iff d component weight D hw hg z).1 hmin⟩
  · rintro ⟨hz, _, hmin⟩
    exact ⟨hz, (isMinOn_separableLift_feasibleOn_iff d component weight D hw hg z).2 hmin⟩

/-- **Relaxed feasible minimum equivalence under separable-height lifting.** -/
theorem mem_separableLift_relaxationOn_and_isMinOn_iff (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) (z : Point (n + q) m) :
    (z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D) ∧
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).relaxationOn (project ⁻¹' D)) z) ↔
      z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D) ∧
        project z ∈ d.relaxationOn D ∧ IsMinOn d.objective (d.relaxationOn D) (project z) := by
  constructor
  · rintro ⟨hz, hmin⟩
    have hzD : project z ∈ D :=
      (d.separableLift component weight).relaxationOn_subset (project ⁻¹' D) hz
    exact ⟨hz,
      project_mem_relaxationOn_of_mem_separableLift d component weight hw (fun i => hg i _ hzD) hz,
      (isMinOn_separableLift_relaxationOn_iff d component weight D hw hg z).1 hmin⟩
  · rintro ⟨hz, _, hmin⟩
    exact ⟨hz, (isMinOn_separableLift_relaxationOn_iff d component weight D hw hg z).2 hmin⟩

/-- **Attainment equivalence under separable-height lifting.** -/
theorem exists_mem_separableLift_feasibleOn_isMinOn_iff (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    (∃ z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D),
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).feasibleOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.feasibleOn D, IsMinOn d.objective (d.feasibleOn D) x := by
  constructor
  · rintro ⟨z, hz, hmin⟩
    have hzD : project z ∈ D :=
      (d.separableLift component weight).feasibleOn_subset (project ⁻¹' D) hz
    exact ⟨project z,
      project_mem_feasibleOn_of_mem_separableLift d component weight hw (fun i => hg i _ hzD) hz,
      (isMinOn_separableLift_feasibleOn_iff d component weight D hw hg z).1 hmin⟩
  · rintro ⟨x, hx, hmin⟩
    refine ⟨appendHeight x (fun j => component j x),
      appendHeight_mem_separableLift_feasibleOn d component weight
        (fun i => hg i x (d.feasibleOn_subset D hx)) hx, ?_⟩
    rw [isMinOn_separableLift_feasibleOn_iff d component weight D hw hg, project_appendHeight]
    exact hmin

/-- **Relaxed attainment equivalence under separable-height lifting.** -/
theorem exists_mem_separableLift_relaxationOn_isMinOn_iff (D : Set (Point n m))
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i, ∀ x ∈ D, d.g i x = ∑ j, weight i j * component j x) :
    (∃ z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D),
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).relaxationOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.relaxationOn D, IsMinOn d.objective (d.relaxationOn D) x := by
  constructor
  · rintro ⟨z, hz, hmin⟩
    have hzD : project z ∈ D :=
      (d.separableLift component weight).relaxationOn_subset (project ⁻¹' D) hz
    exact ⟨project z,
      project_mem_relaxationOn_of_mem_separableLift d component weight hw (fun i => hg i _ hzD) hz,
      (isMinOn_separableLift_relaxationOn_iff d component weight D hw hg z).1 hmin⟩
  · rintro ⟨x, hx, hmin⟩
    refine ⟨appendHeight x (fun j => component j x),
      appendHeight_mem_separableLift_relaxationOn d component weight
        (fun i => hg i x (d.relaxationOn_subset D hx)) hx, ?_⟩
    rw [isMinOn_separableLift_relaxationOn_iff d component weight D hw hg, project_appendHeight]
    exact hmin

end SeparableLift

end FiniteModel

/-! ### Examples -/

/-- On the mixed-integer model `-1 ≤ x ≤ 1`, `z ∈ {0, 1}`, `(x + z)² ≤ 1`, objective `x + z`,
`separableLift` preserves the feasible minimum at the lifted image of `(-1, 0)` with height `0`. -/
example :
    let d : FiniteModel 1 1 1 2 :=
      { g := fun _ x => (x.1 0 + x.2 0) ^ 2 - 1
        A := ![fun _ => 1, fun _ => -1]
        B := ![fun _ => 0, fun _ => 0]
        rhs := ![1, 1]
        c1 := fun _ => 1
        c2 := fun _ => 1
        lo := fun _ => 0
        hi := fun _ => 1 }
    let comp : Fin 1 → Point 1 1 → ℝ := fun _ x => (x.1 0 + x.2 0) ^ 2 - 1
    let weight : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let dSep := d.separableLift comp weight
    let xOpt : Point 1 1 := (fun _ => -1, fun _ => 0)
    appendHeight xOpt (fun _ => 0) ∈ dSep.feasibleOn (project ⁻¹' Set.univ) ∧
      IsMinOn dSep.objective (dSep.feasibleOn (project ⁻¹' Set.univ))
        (appendHeight xOpt (fun _ => 0)) := by
  intro d comp weight dSep xOpt
  have hOptMem : xOpt ∈ d.feasibleOn Set.univ := by
    rw [FiniteModel.mem_feasibleOn_iff]
    refine ⟨mem_univ _, fun _ => by norm_num [d, xOpt], fun k => ?_, fun _ => 0,
      fun _ => by norm_num [d], funext fun _ => by simp [xOpt]⟩
    fin_cases k <;> simp [d, xOpt]
  have hOptMin : IsMinOn d.objective (d.feasibleOn Set.univ) xOpt := by
    rw [isMinOn_iff]
    intro x hx
    have hA : (∑ i, d.A 1 i * x.1 i) + (∑ j, d.B 1 j * x.2 j) ≤ d.rhs 1 :=
      (FiniteModel.mem_feasibleOn_iff.1 hx).2.2.1 1
    have hlo : d.lo 0 ≤ x.2 0 :=
      (FiniteModel.mem_relaxationOn_iff.1 (d.feasibleOn_subset_relaxationOn Set.univ hx)).2.2.2 0
        |>.1
    simp only [Fin.sum_univ_one, Matrix.cons_val_one, Matrix.cons_val_zero, d] at hA hlo
    simp only [FiniteModel.objective_apply, Fin.sum_univ_one, d, xOpt]
    linarith
  have hgSep : ∀ i, ∀ x ∈ (Set.univ : Set (Point 1 1)),
      d.g i x = ∑ j, weight i j * comp j x := by
    intro _ x _; simp [d, weight, comp]
  rw [d.mem_separableLift_feasibleOn_and_isMinOn_iff comp weight Set.univ
    (fun _ _ => by norm_num [weight]) hgSep]
  have hcomp : (fun _ : Fin 1 => (0 : ℝ)) = fun j => comp j xOpt := by
    ext j; simp [comp, xOpt]
  refine ⟨hcomp ▸ d.appendHeight_mem_separableLift_feasibleOn comp weight
    (fun i => hgSep i xOpt (mem_univ _)) hOptMem,
    by simpa only [project_appendHeight] using hOptMem,
    by simpa only [project_appendHeight] using hOptMin⟩

/-- Negative weights invalidate forward projection in `separableLift`: with component `x`, weight
`-1`, and residual `-x`, the lifted point `(x, y) = (-1, 0)` satisfies `x ≤ y` and `-y ≤ 0`, but
its projection `x = -1` violates `-x ≤ 0`. -/
example :
    let d : FiniteModel 1 0 1 0 :=
      { g := fun _ x => -x.1 0
        A := Fin.elim0
        B := Fin.elim0
        rhs := Fin.elim0
        c1 := fun _ => 0
        c2 := Fin.elim0
        lo := Fin.elim0
        hi := Fin.elim0 }
    let comp : Fin 1 → Point 1 0 → ℝ := fun _ x => x.1 0
    let weight : Fin 1 → Fin 1 → ℝ := fun _ _ => -1
    let x : Point 1 0 := (fun _ => -1, Fin.elim0)
    appendHeight x (fun _ => 0) ∈ (d.separableLift comp weight).feasibleOn (project ⁻¹' Set.univ) ∧
      x ∉ d.feasibleOn Set.univ := by
  intro d comp weight x
  constructor
  · rw [d.mem_separableLift_feasibleOn_iff comp weight]
    simp only [project_appendHeight, height_appendHeight]
    refine ⟨mem_univ _, fun _ => by norm_num [comp, x], fun k => k.elim0,
      fun _ => by norm_num [weight], Fin.elim0, fun j => j.elim0, funext fun j => j.elim0⟩
  · intro hx
    have h0 := (FiniteModel.mem_feasibleOn_iff.1 hx).2.1 0
    norm_num [d, x] at h0

end TauCeti.ConvexLifting
