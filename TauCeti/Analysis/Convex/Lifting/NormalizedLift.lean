/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.FiniteModel

/-!
# Affine-argument normalization for finite mixed-integer models

When each nonlinear residual of a `FiniteModel` decomposes as
`g i x = ∑ j, weight i j * phi j (u j x)` for affine arguments
`u j x = ∑ k, a j k * x₁ k + ∑ k, b j k * x₂ k + offset j`, appending one continuous variable per
argument and two opposite affine inequalities imposing `height z j = u j (project z)` produces an
exact extended formulation (`FiniteModel.normalizedLift`). Because the added coordinates are fixed
by exact substitution rather than one-sided epigraph inequalities, mixed-integer feasibility, the
continuous relaxation, feasible minima, and attainment are preserved without any sign, convexity,
or smoothness assumption.

## Main definitions

* `TauCeti.ConvexLifting.FiniteModel.normalizedLift`: affine-argument normalization lift.

## Main statements

* `TauCeti.ConvexLifting.FiniteModel.normalizedLift_affine_iff`: equivalence between the affine
  rows of `normalizedLift` and the original affine rows together with the argument equalities
  `height z j = affineArgument (a j) (b j) (offset j) (project z)`.
* `TauCeti.ConvexLifting.FiniteModel.mem_normalizedLift_feasibleOn_iff` and
  `TauCeti.ConvexLifting.FiniteModel.mem_normalizedLift_relaxationOn_iff`: membership equivalence
  for the mixed-integer feasible set and its continuous relaxation.
* `TauCeti.ConvexLifting.FiniteModel.image_project_normalizedLift_feasibleOn` and
  `TauCeti.ConvexLifting.FiniteModel.image_project_normalizedLift_relaxationOn`: exact projection
  under `project`.
* `TauCeti.ConvexLifting.FiniteModel.mem_normalizedLift_feasibleOn_and_isMinOn_iff`,
  `TauCeti.ConvexLifting.FiniteModel.mem_normalizedLift_relaxationOn_and_isMinOn_iff`,
  `TauCeti.ConvexLifting.FiniteModel.exists_mem_normalizedLift_feasibleOn_isMinOn_iff`, and
  `TauCeti.ConvexLifting.FiniteModel.exists_mem_normalizedLift_relaxationOn_isMinOn_iff`:
  equivalence of feasible minima and attainment in both the mixed-integer and relaxed models.

## References

* H. Hijazi, P. Bonami and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (4 October 2013),
  pp. 1–14, §3 opening (p. 4).
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.ConvexLifting

namespace FiniteModel

variable {n m l r q : ℕ}

/-- Normalize affine arguments by appending `q` continuous variables and imposing each equality
`height z j = affineArgument (a j) (b j) (offset j) (project z)` via two opposite affine
inequalities. Original affine rows, integer bounds, and objective coefficients are retained. -/
def normalizedLift (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    FiniteModel (n + q) m l (r + (q + q)) where
  g := fun i z => ∑ j, weight i j * phi j (height z j)
  A := Fin.append (fun k => Fin.append (d.A k) (fun _ => 0))
    (Fin.append (fun j => Fin.append (-a j) (Pi.single j 1))
      (fun j => Fin.append (a j) (Pi.single j (-1))))
  B := Fin.append d.B (Fin.append (fun j => -b j) b)
  rhs := Fin.append d.rhs (Fin.append offset (-offset))
  c1 := Fin.append d.c1 (fun _ => 0)
  c2 := d.c2
  lo := d.lo
  hi := d.hi

section NormalizedLift

variable (d : FiniteModel n m l r)
  (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
  (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)

/-- Evaluating the nonlinear residual field of `normalizedLift`. -/
@[simp]
theorem normalizedLift_g (i : Fin l) (z : Point (n + q) m) :
    (d.normalizedLift a b offset phi weight).g i z =
      ∑ j, weight i j * phi j (height z j) := (rfl)

/-- The continuous-block affine matrix of `normalizedLift`. -/
theorem normalizedLift_A :
    (d.normalizedLift a b offset phi weight).A =
      Fin.append (fun k => Fin.append (d.A k) (fun _ => 0))
        (Fin.append (fun j => Fin.append (-a j) (Pi.single j 1))
          (fun j => Fin.append (a j) (Pi.single j (-1)))) := (rfl)

/-- The integer-block affine matrix of `normalizedLift`. -/
theorem normalizedLift_B :
    (d.normalizedLift a b offset phi weight).B =
      Fin.append d.B (Fin.append (fun j => -b j) b) := (rfl)

/-- The right-hand side vector of `normalizedLift`. -/
theorem normalizedLift_rhs :
    (d.normalizedLift a b offset phi weight).rhs =
      Fin.append d.rhs (Fin.append offset (-offset)) := (rfl)

/-- Continuous-block objective coefficients of `normalizedLift`. -/
@[simp]
theorem normalizedLift_c1 :
    (d.normalizedLift a b offset phi weight).c1 = Fin.append d.c1 (fun _ => 0) := (rfl)

/-- Integer-block objective coefficients of `normalizedLift`. -/
@[simp]
theorem normalizedLift_c2 :
    (d.normalizedLift a b offset phi weight).c2 = d.c2 := (rfl)

/-- Integer-block lower bounds of `normalizedLift`. -/
@[simp]
theorem normalizedLift_lo :
    (d.normalizedLift a b offset phi weight).lo = d.lo := (rfl)

/-- Integer-block upper bounds of `normalizedLift`. -/
@[simp]
theorem normalizedLift_hi :
    (d.normalizedLift a b offset phi weight).hi = d.hi := (rfl)

/-- The objective of `normalizedLift` pulls back `d.objective` along `project`. -/
@[simp]
theorem objective_normalizedLift (z : Point (n + q) m) :
    (d.normalizedLift a b offset phi weight).objective z = d.objective (project z) :=
  d.objective_eq_comp_project (d.normalizedLift a b offset phi weight) rfl rfl z

/-- The affine constraints of `normalizedLift` are equivalent to the original affine constraints
at `project z` together with the argument equalities
`height z j = affineArgument (a j) (b j) (offset j) (project z)`. -/
theorem normalizedLift_affine_iff (z : Point (n + q) m) :
    (∀ k, (∑ i, (d.normalizedLift a b offset phi weight).A k i * z.1 i) +
        (∑ j, (d.normalizedLift a b offset phi weight).B k j * z.2 j) ≤
          (d.normalizedLift a b offset phi weight).rhs k) ↔
      (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ j, d.B k j * (project z).2 j) ≤ d.rhs k) ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  simp only [normalizedLift_A, normalizedLift_B, normalizedLift_rhs, Fin.forall_fin_add,
    Fin.append_left, Fin.append_right, sum_append_zero_mul_fst, project_snd]
  refine and_congr_right fun _ => ?_
  have h1 : ∀ j, (∑ i, Fin.append (-a j) (Pi.single j (1 : ℝ)) i * z.1 i) +
      (∑ t, (-b j) t * z.2 t) ≤ offset j ↔
      height z j ≤ affineArgument (a j) (b j) (offset j) (project z) := fun j => by
    rw [sum_append_mul_fst, affineArgument_apply]
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Pi.single_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, project_snd]
    constructor <;> intro h <;> linarith
  have h2 : ∀ j, (∑ i, Fin.append (a j) (Pi.single j (-1 : ℝ)) i * z.1 i) +
      (∑ t, b j t * z.2 t) ≤ (-offset) j ↔
      affineArgument (a j) (b j) (offset j) (project z) ≤ height z j := fun j => by
    rw [sum_append_mul_fst, affineArgument_apply]
    simp only [Pi.neg_apply, Pi.single_apply, ite_mul, neg_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, project_snd]
    constructor <;> intro h <;> linarith
  simp_rw [h1, h2, ← forall_and, ← le_antisymm_iff]

/-- Characterization of mixed-integer feasibility in `normalizedLift` at `z` under the
affine-argument decomposition `hg` at `project z`. -/
theorem mem_normalizedLift_feasibleOn_iff {D : Set (Point n m)} {z : Point (n + q) m}
    (hg : project z ∈ D → ∀ i, d.g i (project z) =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) (project z))) :
    z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ↔
      project z ∈ d.feasibleOn D ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  rw [mem_feasibleOn_iff, normalizedLift_affine_iff, mem_feasibleOn_iff]
  simp only [mem_preimage, normalizedLift_g, normalizedLift_lo, normalizedLift_hi, project_snd]
  constructor
  · rintro ⟨hzD, hzg, ⟨hzA, hzeq⟩, hy⟩
    refine ⟨⟨hzD, fun i => ?_, hzA, hy⟩, hzeq⟩
    simpa only [hg hzD i, ← hzeq] using hzg i
  · rintro ⟨⟨hzD, hzg, hzA, hy⟩, hzeq⟩
    refine ⟨hzD, fun i => ?_, ⟨hzA, hzeq⟩, hy⟩
    simpa only [hg hzD i, ← hzeq] using hzg i

/-- Characterization of continuous-relaxation membership in `normalizedLift` at `z` under `hg`. -/
theorem mem_normalizedLift_relaxationOn_iff {D : Set (Point n m)} {z : Point (n + q) m}
    (hg : project z ∈ D → ∀ i, d.g i (project z) =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) (project z))) :
    z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ↔
      project z ∈ d.relaxationOn D ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  rw [mem_relaxationOn_iff, normalizedLift_affine_iff, mem_relaxationOn_iff]
  simp only [mem_preimage, normalizedLift_g, normalizedLift_lo, normalizedLift_hi, project_snd]
  constructor
  · rintro ⟨hzD, hzg, ⟨hzA, hzeq⟩, hbox⟩
    refine ⟨⟨hzD, fun i => ?_, hzA, hbox⟩, hzeq⟩
    simpa only [hg hzD i, ← hzeq] using hzg i
  · rintro ⟨⟨hzD, hzg, hzA, hbox⟩, hzeq⟩
    refine ⟨hzD, fun i => ?_, ⟨hzA, hzeq⟩, hbox⟩
    simpa only [hg hzD i, ← hzeq] using hzg i

/-- Canonical insertion of affine argument values into the mixed-integer feasible set of
`normalizedLift`. -/
theorem appendHeight_mem_normalizedLift_feasibleOn {D : Set (Point n m)} {x : Point n m}
    (hg : ∀ i, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (hx : x ∈ d.feasibleOn D) :
    appendHeight x (fun j => affineArgument (a j) (b j) (offset j) x) ∈
      (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) := by
  rw [mem_normalizedLift_feasibleOn_iff d a b offset phi weight]
  · simp [hx]
  · intro _ i
    simpa only [project_appendHeight] using hg i

/-- Canonical insertion of affine argument values into the continuous relaxation of
`normalizedLift`. -/
theorem appendHeight_mem_normalizedLift_relaxationOn {D : Set (Point n m)} {x : Point n m}
    (hg : ∀ i, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (hx : x ∈ d.relaxationOn D) :
    appendHeight x (fun j => affineArgument (a j) (b j) (offset j) x) ∈
      (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) := by
  rw [mem_normalizedLift_relaxationOn_iff d a b offset phi weight]
  · simp [hx]
  · intro _ i
    simpa only [project_appendHeight] using hg i

/-- **Exact mixed-integer projection under affine-argument normalization.** No sign, convexity,
or smoothness assumption is required. -/
theorem image_project_normalizedLift_feasibleOn (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    project '' (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) =
      d.feasibleOn D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((mem_normalizedLift_feasibleOn_iff d a b offset phi weight
      (fun hzD i => hg i _ hzD)).1 hz).1
  · intro hx
    exact ⟨appendHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      appendHeight_mem_normalizedLift_feasibleOn d a b offset phi weight
        (fun i => hg i x (d.feasibleOn_subset D hx)) hx,
      project_appendHeight _ _⟩

/-- **Exact continuous-relaxation projection under affine-argument normalization.** -/
theorem image_project_normalizedLift_relaxationOn (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    project '' (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) =
      d.relaxationOn D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((mem_normalizedLift_relaxationOn_iff d a b offset phi weight
      (fun hzD i => hg i _ hzD)).1 hz).1
  · intro hx
    exact ⟨appendHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      appendHeight_mem_normalizedLift_relaxationOn d a b offset phi weight
        (fun i => hg i x (d.relaxationOn_subset D hx)) hx,
      project_appendHeight _ _⟩

/-- Equivalence of `IsMinOn` between `normalizedLift` and the original mixed-integer model. -/
theorem isMinOn_normalizedLift_feasibleOn_iff (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    IsMinOn (d.normalizedLift a b offset phi weight).objective
      ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) z ↔
      IsMinOn d.objective (d.feasibleOn D) (project z) := by
  rw [isMinOn_iff, isMinOn_iff,
    ← image_project_normalizedLift_feasibleOn d a b offset phi weight D hg, forall_mem_image]
  simp only [objective_normalizedLift]

/-- Equivalence of `IsMinOn` on the continuous relaxation between `normalizedLift` and the original
model. -/
theorem isMinOn_normalizedLift_relaxationOn_iff (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    IsMinOn (d.normalizedLift a b offset phi weight).objective
      ((d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D)) z ↔
      IsMinOn d.objective (d.relaxationOn D) (project z) := by
  rw [isMinOn_iff, isMinOn_iff,
    ← image_project_normalizedLift_relaxationOn d a b offset phi weight D hg, forall_mem_image]
  simp only [objective_normalizedLift]

/-- **Feasible minimum equivalence under affine-argument normalization.** -/
theorem mem_normalizedLift_feasibleOn_and_isMinOn_iff (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    (z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ∧
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) z) ↔
      z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ∧
        project z ∈ d.feasibleOn D ∧ IsMinOn d.objective (d.feasibleOn D) (project z) := by
  constructor
  · rintro ⟨hz, hmin⟩
    exact ⟨hz,
      ((mem_normalizedLift_feasibleOn_iff d a b offset phi weight
        (fun hzD i => hg i _ hzD)).1 hz).1,
      (isMinOn_normalizedLift_feasibleOn_iff d a b offset phi weight D hg z).1 hmin⟩
  · rintro ⟨hz, _, hmin⟩
    exact ⟨hz, (isMinOn_normalizedLift_feasibleOn_iff d a b offset phi weight D hg z).2 hmin⟩

/-- **Relaxed feasible minimum equivalence under affine-argument normalization.** -/
theorem mem_normalizedLift_relaxationOn_and_isMinOn_iff (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    (z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ∧
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D)) z) ↔
      z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ∧
        project z ∈ d.relaxationOn D ∧ IsMinOn d.objective (d.relaxationOn D) (project z) := by
  constructor
  · rintro ⟨hz, hmin⟩
    exact ⟨hz,
      ((mem_normalizedLift_relaxationOn_iff d a b offset phi weight
        (fun hzD i => hg i _ hzD)).1 hz).1,
      (isMinOn_normalizedLift_relaxationOn_iff d a b offset phi weight D hg z).1 hmin⟩
  · rintro ⟨hz, _, hmin⟩
    exact ⟨hz, (isMinOn_normalizedLift_relaxationOn_iff d a b offset phi weight D hg z).2 hmin⟩

/-- **Attainment equivalence under affine-argument normalization.** -/
theorem exists_mem_normalizedLift_feasibleOn_isMinOn_iff (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    (∃ z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D),
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.feasibleOn D, IsMinOn d.objective (d.feasibleOn D) x := by
  constructor
  · rintro ⟨z, hz, hmin⟩
    exact ⟨project z,
      ((mem_normalizedLift_feasibleOn_iff d a b offset phi weight
        (fun hzD i => hg i _ hzD)).1 hz).1,
      (isMinOn_normalizedLift_feasibleOn_iff d a b offset phi weight D hg z).1 hmin⟩
  · rintro ⟨x, hx, hmin⟩
    refine ⟨appendHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      appendHeight_mem_normalizedLift_feasibleOn d a b offset phi weight
        (fun i => hg i x (d.feasibleOn_subset D hx)) hx, ?_⟩
    rw [isMinOn_normalizedLift_feasibleOn_iff d a b offset phi weight D hg, project_appendHeight]
    exact hmin

/-- **Relaxed attainment equivalence under affine-argument normalization.** -/
theorem exists_mem_normalizedLift_relaxationOn_isMinOn_iff (D : Set (Point n m))
    (hg : ∀ i, ∀ x ∈ D, d.g i x =
      ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    (∃ z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D),
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.relaxationOn D, IsMinOn d.objective (d.relaxationOn D) x := by
  constructor
  · rintro ⟨z, hz, hmin⟩
    exact ⟨project z,
      ((mem_normalizedLift_relaxationOn_iff d a b offset phi weight
        (fun hzD i => hg i _ hzD)).1 hz).1,
      (isMinOn_normalizedLift_relaxationOn_iff d a b offset phi weight D hg z).1 hmin⟩
  · rintro ⟨x, hx, hmin⟩
    refine ⟨appendHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      appendHeight_mem_normalizedLift_relaxationOn d a b offset phi weight
        (fun i => hg i x (d.relaxationOn_subset D hx)) hx, ?_⟩
    rw [isMinOn_normalizedLift_relaxationOn_iff d a b offset phi weight D hg, project_appendHeight]
    exact hmin

end NormalizedLift

end FiniteModel

/-! ### Example -/

/-- On the mixed-integer model `-1 ≤ x ≤ 1`, `z ∈ {0, 1}`, `(x + z)² ≤ 1`, objective `x + z`,
`normalizedLift` keeps the auxiliary argument coordinate continuous (so `(1/2, 0)` lifts with
fractional `u = 1/2`), and preserves the feasible minimum at the lift of `(-1, 0)`. -/
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
    let a : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let b : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let offset : Fin 1 → ℝ := fun _ => 0
    let phi : Fin 1 → ℝ → ℝ := fun _ u => u ^ 2 - 1
    let weight : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let dNorm := d.normalizedLift a b offset phi weight
    let xHalf : Point 1 1 := (fun _ => 1 / 2, fun _ => 0)
    let xOpt : Point 1 1 := (fun _ => -1, fun _ => 0)
    appendHeight xHalf (fun _ => 1 / 2) ∈ dNorm.feasibleOn (project ⁻¹' Set.univ) ∧
      appendHeight xOpt (fun _ => -1) ∈ dNorm.feasibleOn (project ⁻¹' Set.univ) ∧
      IsMinOn dNorm.objective (dNorm.feasibleOn (project ⁻¹' Set.univ))
        (appendHeight xOpt (fun _ => -1)) := by
  intro d a b offset phi weight dNorm xHalf xOpt
  have hfeas : ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (fun _ => c, fun _ => 0) ∈ d.feasibleOn Set.univ := by
    intro c h1 h2
    rw [FiniteModel.mem_feasibleOn_iff]
    refine ⟨mem_univ _, fun _ => by nlinarith, fun k => ?_, fun _ => 0, fun _ => by norm_num,
      funext fun _ => by simp⟩
    fin_cases k <;> simp [d] <;> linarith
  have hOptMem : xOpt ∈ d.feasibleOn Set.univ := hfeas (-1) (by norm_num) (by norm_num)
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
  have hgNorm : ∀ i, ∀ x ∈ (Set.univ : Set (Point 1 1)),
      d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x) := by
    intro _ x _; simp [d, a, b, offset, phi, weight, affineArgument_apply]
  refine ⟨?_, ?_⟩
  · have harg : (fun _ : Fin 1 => (1 / 2 : ℝ)) =
        fun j => affineArgument (a j) (b j) (offset j) xHalf := by
      ext j; simp [affineArgument_apply, a, b, offset, xHalf]
    rw [harg]
    exact d.appendHeight_mem_normalizedLift_feasibleOn a b offset phi weight
      (fun i => hgNorm i xHalf (mem_univ _)) (hfeas (1 / 2) (by norm_num) (by norm_num))
  · rw [d.mem_normalizedLift_feasibleOn_and_isMinOn_iff a b offset phi weight Set.univ hgNorm]
    have harg : (fun _ : Fin 1 => (-1 : ℝ)) =
        fun j => affineArgument (a j) (b j) (offset j) xOpt := by
      ext j; simp [affineArgument_apply, a, b, offset, xOpt]
    refine ⟨harg ▸ d.appendHeight_mem_normalizedLift_feasibleOn a b offset phi weight
      (fun i => hgNorm i xOpt (mem_univ _)) hOptMem,
      by simpa only [project_appendHeight] using hOptMem,
      by simpa only [project_appendHeight] using hOptMin⟩

end TauCeti.ConvexLifting
