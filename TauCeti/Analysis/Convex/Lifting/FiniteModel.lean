/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Finite mixed-integer models and coordinate lifting interface

This file formalizes finite mixed-integer nonlinear models with `n` continuous coordinates, `m`
ambient real coordinates on which bounded integrality can be imposed, `l` nonlinear residual
constraints `g i x ≤ 0`, `r` affine constraints `A k x₁ + B k x₂ ≤ rhs k`, and a linear objective
`c₁ · x₁ + c₂ · x₂`. Both the mixed-integer feasible set `FiniteModel.feasibleOn` and its
continuous relaxation `FiniteModel.relaxationOn` retain the same domain, nonlinear and affine rows,
and bounds on the second block; integrality is imposed only in `feasibleOn`.

Auxiliary continuous variables are appended to the first block via `appendHeight`, with inverse
coordinates `project` and `height` packaged in `splitEquiv`. We also define `affineArgument` and
establish Fréchet derivative transport through `affineArgument` when each univariate component
derivative is supplied at the evaluated affine argument.

The exact extended formulations `FiniteModel.normalizedLift` and `FiniteModel.separableLift` built
on this interface live in `TauCeti.Analysis.Convex.Lifting.NormalizedLift` and
`TauCeti.Analysis.Convex.Lifting.SeparableLift`.

## Main definitions

* `TauCeti.ConvexLifting.Point`: product `(Fin n → ℝ) × (Fin m → ℝ)` of continuous and ambient
  integer-block coordinates.
* `TauCeti.ConvexLifting.project`, `TauCeti.ConvexLifting.height`,
  `TauCeti.ConvexLifting.appendHeight`, `TauCeti.ConvexLifting.splitEquiv`: coordinate projection,
  height extraction, graph insertion, and the splitting equivalence between `Point (n + q) m` and
  `Point n m × (Fin q → ℝ)`.
* `TauCeti.ConvexLifting.affineArgument` and `TauCeti.ConvexLifting.affineArgumentLinear`: affine
  expressions in `Point n m` and their continuous linear parts.
* `TauCeti.ConvexLifting.FiniteModel`: finite nonlinear/affine mixed-integer model data.
* `TauCeti.ConvexLifting.FiniteModel.objective`, `TauCeti.ConvexLifting.FiniteModel.feasibleOn`,
  `TauCeti.ConvexLifting.FiniteModel.relaxationOn`: linear objective, mixed-integer feasible set,
  and continuous relaxation.

## Main statements

* `TauCeti.ConvexLifting.sum_append_mul_fst`, `TauCeti.ConvexLifting.sum_append_zero_mul_fst`,
  `TauCeti.ConvexLifting.sum_zero_append_mul_fst`: splitting inner products across original and
  appended continuous coordinates.
* `TauCeti.ConvexLifting.hasFDerivAt_affineArgument`,
  `TauCeti.ConvexLifting.hasFDerivAt_comp_affineArgument`,
  `TauCeti.ConvexLifting.hasFDerivAt_sum_mul_comp_affineArgument`: Fréchet derivative transport
  for affine arguments and weighted sums of univariate compositions.
* `TauCeti.ConvexLifting.FiniteModel.objective_eq_comp_project`: pulling back a linear objective
  extended by zero coefficients along `project`.
* `TauCeti.ConvexLifting.FiniteModel.feasibleOn_subset_relaxationOn` and
  `TauCeti.ConvexLifting.FiniteModel.feasibleOn_eq_relaxationOn`: comparison between mixed-integer
  feasibility and the continuous relaxation (with equality when `m = 0`).

## References

* H. Hijazi, P. Bonami and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (4 October 2013),
  pp. 1–14, §§1–2 (pp. 1–2).
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.ConvexLifting

/-! ### Coordinates, graph insertion, and affine arguments -/

/-- Continuous coordinates paired with real coordinates on which integrality can be imposed. -/
abbrev Point (n m : ℕ) : Type := (Fin n → ℝ) × (Fin m → ℝ)

section Coordinates

variable {n m q : ℕ}

/-- Forget the `q` appended continuous coordinates and retain the original integer block. -/
def project (z : Point (n + q) m) : Point n m :=
  (fun i => z.1 (i.castAdd q), z.2)

/-- Extract the `q` appended continuous argument or height coordinates. -/
def height (z : Point (n + q) m) : Fin q → ℝ :=
  fun j => z.1 (j.natAdd n)

/-- Append `q` continuous height coordinates to a base point `x : Point n m`. -/
def appendHeight (x : Point n m) (y : Fin q → ℝ) : Point (n + q) m :=
  (Fin.append x.1 y, x.2)

/-- Evaluating the first block of `project z`. -/
@[simp]
theorem project_fst (z : Point (n + q) m) (i : Fin n) :
    (project z).1 i = z.1 (i.castAdd q) := (rfl)

/-- Evaluating the second block of `project z`. -/
@[simp]
theorem project_snd (z : Point (n + q) m) :
    (project z).2 = z.2 := (rfl)

/-- Evaluating `height z` at a coordinate `j`. -/
@[simp]
theorem height_apply (z : Point (n + q) m) (j : Fin q) :
    height z j = z.1 (j.natAdd n) := (rfl)

/-- Evaluating the first coordinate block of `appendHeight x y`. -/
theorem appendHeight_fst (x : Point n m) (y : Fin q → ℝ) :
    (appendHeight x y).1 = Fin.append x.1 y := (rfl)

/-- Evaluating the original continuous block of `appendHeight x y`. -/
@[simp]
theorem appendHeight_fst_castAdd (x : Point n m) (y : Fin q → ℝ) (i : Fin n) :
    (appendHeight x y).1 (i.castAdd q) = x.1 i := by
  simp [appendHeight]

/-- Evaluating the appended height block of `appendHeight x y`. -/
@[simp]
theorem appendHeight_fst_natAdd (x : Point n m) (y : Fin q → ℝ) (j : Fin q) :
    (appendHeight x y).1 (j.natAdd n) = y j := by
  simp [appendHeight]

/-- Evaluating the integer block of `appendHeight x y`. -/
@[simp]
theorem appendHeight_snd (x : Point n m) (y : Fin q → ℝ) :
    (appendHeight x y).2 = x.2 := (rfl)

/-- Projecting after appending heights recovers the original point. -/
@[simp]
theorem project_appendHeight (x : Point n m) (y : Fin q → ℝ) :
    project (appendHeight x y) = x := by
  ext i <;> simp

/-- Reading heights after appending recovers the appended vector. -/
@[simp]
theorem height_appendHeight (x : Point n m) (y : Fin q → ℝ) :
    height (appendHeight x y) = y := by
  ext j
  simp

/-- Reconstructing an enlarged point from its projection and height vector. -/
@[simp]
theorem appendHeight_project_height (z : Point (n + q) m) :
    appendHeight (project z) (height z) = z := by
  ext i
  · exact Fin.addCases_castAdd_natAdd z.1 i
  · rfl

/-- Projecting with `q = 0` appended coordinates is the identity. -/
@[simp]
theorem project_zero (z : Point (n + 0) m) :
    project (q := 0) z = z := by
  ext i <;> simp

/-- Appending an empty height vector leaves a point unchanged. -/
@[simp]
theorem appendHeight_elim0 (x : Point n m) :
    appendHeight x Fin.elim0 = x := by
  ext i <;> simp [appendHeight]

/-- Two enlarged points coincide if their projections and height vectors coincide. -/
theorem eq_of_project_eq_of_height_eq {z₁ z₂ : Point (n + q) m}
    (hp : project z₁ = project z₂) (hh : height z₁ = height z₂) : z₁ = z₂ := by
  rw [← appendHeight_project_height z₁, ← appendHeight_project_height z₂, hp, hh]

/-- Splitting an enlarged point into its projected base point and appended height vector. -/
def splitEquiv (n m q : ℕ) : Point (n + q) m ≃ Point n m × (Fin q → ℝ) where
  toFun z := (project z, height z)
  invFun p := appendHeight p.1 p.2
  left_inv := appendHeight_project_height
  right_inv p := Prod.ext (project_appendHeight p.1 p.2) (height_appendHeight p.1 p.2)

/-- Evaluation of `splitEquiv`. -/
@[simp]
theorem splitEquiv_apply (z : Point (n + q) m) :
    splitEquiv n m q z = (project z, height z) := (rfl)

/-- Evaluation of the inverse of `splitEquiv`. -/
@[simp]
theorem splitEquiv_symm_apply (p : Point n m × (Fin q → ℝ)) :
    (splitEquiv n m q).symm p = appendHeight p.1 p.2 := (rfl)

/-- Splitting an inner product with an appended coefficient vector over the original and height
blocks. -/
theorem sum_append_mul_fst (u : Fin n → ℝ) (v : Fin q → ℝ) (z : Point (n + q) m) :
    ∑ i, Fin.append u v i * z.1 i =
      (∑ i, u i * (project z).1 i) + ∑ j, v j * height z j := by
  rw [Fin.sum_univ_add]
  simp

/-- Extending coefficients by zeros on the appended block evaluates on `project z`. -/
@[simp]
theorem sum_append_zero_mul_fst (u : Fin n → ℝ) (z : Point (n + q) m) :
    ∑ i, Fin.append u (fun _ => 0) i * z.1 i = ∑ i, u i * (project z).1 i := by
  rw [sum_append_mul_fst]
  simp

/-- Coefficients supported on the appended block evaluate on `height z`. -/
@[simp]
theorem sum_zero_append_mul_fst (v : Fin q → ℝ) (z : Point (n + q) m) :
    ∑ i, Fin.append (fun _ => 0) v i * z.1 i = ∑ j, v j * height z j := by
  rw [sum_append_mul_fst]
  simp

end Coordinates

section AffineArgument

variable {n m : ℕ}

/-- An affine expression in the original continuous and integer coordinates. -/
def affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) : ℝ :=
  (∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset

/-- Expanding `affineArgument` into its coordinate sums and offset. -/
theorem affineArgument_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) :
    affineArgument a b offset x = (∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset := (rfl)

/-- The continuous linear part of `affineArgument a b offset`. -/
noncomputable def affineArgumentLinear (a : Fin n → ℝ) (b : Fin m → ℝ) :
    Point n m →L[ℝ] ℝ :=
  (∑ i, a i • ContinuousLinearMap.proj (R := ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _) +
    (∑ j, b j • ContinuousLinearMap.proj (R := ℝ) j).comp (ContinuousLinearMap.snd ℝ _ _)

/-- Evaluating the continuous linear part of an affine argument. -/
@[simp]
theorem affineArgumentLinear_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (x : Point n m) :
    affineArgumentLinear a b x = (∑ i, a i * x.1 i) + ∑ j, b j * x.2 j := by
  simp [affineArgumentLinear, smul_eq_mul]

/-- Decomposing `affineArgument` into its continuous linear part plus its offset. -/
theorem affineArgument_eq_linear_add (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ)
    (x : Point n m) :
    affineArgument a b offset x = affineArgumentLinear a b x + offset := by
  simp [affineArgument_apply]

/-- The Fréchet derivative of `affineArgument a b offset` is `affineArgumentLinear a b`. -/
theorem hasFDerivAt_affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) :
    HasFDerivAt (affineArgument a b offset) (affineArgumentLinear a b) x := by
  have h : affineArgument a b offset = fun z => affineArgumentLinear a b z + offset :=
    funext (affineArgument_eq_linear_add a b offset)
  rw [h, hasFDerivAt_add_const_iff]
  exact (affineArgumentLinear a b).hasFDerivAt

/-- Chain-rule derivative transport for a univariate function composed with `affineArgument`. -/
theorem hasFDerivAt_comp_affineArgument {phi : ℝ → ℝ} {d : ℝ}
    (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m)
    (hphi : HasDerivAt phi d (affineArgument a b offset x)) :
    HasFDerivAt (fun z => phi (affineArgument a b offset z))
      (d • affineArgumentLinear a b) x :=
  hphi.comp_hasFDerivAt x (hasFDerivAt_affineArgument a b offset x)

/-- Derivative transport for a weighted finite sum of univariate functions of affine arguments,
given each univariate component derivative at its evaluated affine argument. -/
theorem hasFDerivAt_sum_mul_comp_affineArgument {q : ℕ}
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin q → ℝ) (d : Fin q → ℝ) (x : Point n m)
    (hphi : ∀ j, HasDerivAt (phi j) (d j) (affineArgument (a j) (b j) (offset j) x)) :
    HasFDerivAt (fun z => ∑ j, weight j * phi j (affineArgument (a j) (b j) (offset j) z))
      (∑ j, (weight j * d j) • affineArgumentLinear (a j) (b j)) x := by
  have hterm : ∀ j ∈ Finset.univ,
      HasFDerivAt (fun z => weight j * phi j (affineArgument (a j) (b j) (offset j) z))
        ((weight j * d j) • affineArgumentLinear (a j) (b j)) x := fun j _ => by
    simpa only [smul_smul] using
      (hasFDerivAt_comp_affineArgument (a j) (b j) (offset j) x (hphi j)).const_mul (weight j)
  exact HasFDerivAt.fun_sum hterm

end AffineArgument

/-! ### Finite mixed-integer models -/

/-- A finite mixed-integer nonlinear model with `n` continuous variables, `m` bounded integer
variables, `l` nonlinear residual inequalities `g i x ≤ 0`, `r` affine inequalities
`A k x₁ + B k x₂ ≤ rhs k`, and a linear objective `c1 · x₁ + c2 · x₂`. -/
@[ext]
structure FiniteModel (n m l r : ℕ) where
  /-- The `l` nonlinear residual functions, bounded above by zero. -/
  g : Fin l → Point n m → ℝ
  /-- Continuous-block coefficients of the `r` affine constraints. -/
  A : Fin r → Fin n → ℝ
  /-- Integer-block coefficients of the `r` affine constraints. -/
  B : Fin r → Fin m → ℝ
  /-- Right-hand sides of the `r` affine constraints. -/
  rhs : Fin r → ℝ
  /-- Linear objective coefficients on the continuous block. -/
  c1 : Fin n → ℝ
  /-- Linear objective coefficients on the integer block. -/
  c2 : Fin m → ℝ
  /-- Lower bounds on the integer block. -/
  lo : Fin m → ℝ
  /-- Upper bounds on the integer block. -/
  hi : Fin m → ℝ

namespace FiniteModel

variable {n m l r : ℕ}

/-- The linear objective in the continuous and integer coordinate blocks. -/
def objective (d : FiniteModel n m l r) (x : Point n m) : ℝ :=
  (∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j

/-- Expanding `FiniteModel.objective` into its two coordinate sums. -/
theorem objective_apply (d : FiniteModel n m l r) (x : Point n m) :
    d.objective x = (∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j := (rfl)

/-- A model with no continuous or integer coordinates has identically zero objective. -/
@[simp]
theorem objective_zero (d : FiniteModel 0 0 l r) (x : Point 0 0) :
    d.objective x = 0 := by
  simp [objective]

/-- Extending objective coefficients by zeros on appended coordinates pulls back `d.objective`
along `project`. -/
theorem objective_eq_comp_project {q l' r' : ℕ} (d : FiniteModel n m l r)
    (d' : FiniteModel (n + q) m l' r')
    (hc1 : d'.c1 = Fin.append d.c1 (fun _ => 0)) (hc2 : d'.c2 = d.c2)
    (z : Point (n + q) m) :
    d'.objective z = d.objective (project z) := by
  simp [objective, hc1, hc2]

/-- Mixed-integer feasible points in `D`: domain membership, nonlinear residuals `≤ 0`, affine
rows, and bounded integer values on the second coordinate block. -/
def feasibleOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
      x.2 = fun j => (y j : ℝ)}

/-- Continuous relaxation of `feasibleOn`: the same domain, nonlinear residuals, affine rows, and
real box bounds on the second coordinate block without integrality. -/
def relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j}

/-- Membership characterization of `FiniteModel.feasibleOn`. -/
@[simp]
theorem mem_feasibleOn_iff {d : FiniteModel n m l r} {D : Set (Point n m)} {x : Point n m} :
    x ∈ d.feasibleOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
          x.2 = fun j => (y j : ℝ) :=
  Iff.rfl

/-- Membership characterization of `FiniteModel.relaxationOn`. -/
@[simp]
theorem mem_relaxationOn_iff {d : FiniteModel n m l r} {D : Set (Point n m)} {x : Point n m} :
    x ∈ d.relaxationOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j :=
  Iff.rfl

/-- Mixed-integer feasibility is contained in the continuous relaxation. -/
theorem feasibleOn_subset_relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ d.relaxationOn D := by
  rintro x ⟨hxD, hxg, hxA, y, hy, hx2⟩
  refine ⟨hxD, hxg, hxA, fun j => ?_⟩
  simpa [hx2] using hy j

/-- Every mixed-integer feasible point lies in the chosen domain `D`. -/
theorem feasibleOn_subset (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ D :=
  fun _ hx => hx.1

/-- Every point in the continuous relaxation lies in the chosen domain `D`. -/
theorem relaxationOn_subset (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.relaxationOn D ⊆ D :=
  fun _ hx => hx.1

/-- With an empty domain, `feasibleOn` is empty. -/
@[simp]
theorem feasibleOn_empty (d : FiniteModel n m l r) : d.feasibleOn ∅ = ∅ := by
  ext x
  simp

/-- With an empty domain, `relaxationOn` is empty. -/
@[simp]
theorem relaxationOn_empty (d : FiniteModel n m l r) : d.relaxationOn ∅ = ∅ := by
  ext x
  simp

/-- `feasibleOn` is monotone in the domain `D`. -/
@[gcongr]
theorem feasibleOn_mono (d : FiniteModel n m l r) {D₁ D₂ : Set (Point n m)} (hD : D₁ ⊆ D₂) :
    d.feasibleOn D₁ ⊆ d.feasibleOn D₂ :=
  fun _ hx => ⟨hD hx.1, hx.2⟩

/-- `relaxationOn` is monotone in the domain `D`. -/
@[gcongr]
theorem relaxationOn_mono (d : FiniteModel n m l r) {D₁ D₂ : Set (Point n m)} (hD : D₁ ⊆ D₂) :
    d.relaxationOn D₁ ⊆ d.relaxationOn D₂ :=
  fun _ hx => ⟨hD hx.1, hx.2⟩

/-- When there are no integer coordinates (`m = 0`), mixed feasibility coincides with the
continuous relaxation. -/
theorem feasibleOn_eq_relaxationOn (d : FiniteModel n 0 l r) (D : Set (Point n 0)) :
    d.feasibleOn D = d.relaxationOn D := by
  refine subset_antisymm (d.feasibleOn_subset_relaxationOn D) ?_
  rintro x ⟨hxD, hxg, hxA, _⟩
  exact ⟨hxD, hxg, hxA, Fin.elim0, fun j => j.elim0, funext fun j => j.elim0⟩

end FiniteModel

/-! ### Example -/

/-- A concrete mixed-integer model (`-1 ≤ x ≤ 1`, `z ∈ {0, 1}`, `(x + z)² ≤ 1`, objective `x + z`)
showing that `(0, 1/2)` lies in `relaxationOn` but not in `feasibleOn`, while `(-1, 0)` attains
the mixed-integer minimum `-1`. -/
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
    let xRelax : Point 1 1 := (fun _ => 0, fun _ => 1 / 2)
    let xOpt : Point 1 1 := (fun _ => -1, fun _ => 0)
    xRelax ∈ d.relaxationOn Set.univ ∧ xRelax ∉ d.feasibleOn Set.univ ∧
      xOpt ∈ d.feasibleOn Set.univ ∧ IsMinOn d.objective (d.feasibleOn Set.univ) xOpt := by
  intro d xRelax xOpt
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [FiniteModel.mem_relaxationOn_iff, mem_univ, true_and, d, xRelax]
    refine ⟨fun _ => by norm_num, fun k => ?_, fun _ => by norm_num⟩
    fin_cases k <;> norm_num
  · rintro ⟨_, _, _, y, _, hy⟩
    have h0 : (y 0 : ℝ) = 1 / 2 := (congr_fun hy 0).symm
    have hlt : (0 : ℤ) < y 0 := by
      have : (0 : ℝ) < (y 0 : ℝ) := by linarith
      exact_mod_cast this
    have hgt : y 0 < (1 : ℤ) := by
      have : (y 0 : ℝ) < (1 : ℝ) := by linarith
      exact_mod_cast this
    omega
  · simp only [FiniteModel.mem_feasibleOn_iff, mem_univ, true_and, d, xOpt]
    refine ⟨fun _ => by norm_num, fun k => ?_, fun _ => 0, fun _ => by norm_num,
      funext fun _ => by simp⟩
    fin_cases k <;> norm_num
  · rw [isMinOn_iff]
    intro x hx
    have hA : (∑ i, d.A 1 i * x.1 i) + (∑ j, d.B 1 j * x.2 j) ≤ d.rhs 1 := hx.2.2.1 1
    have hlo : d.lo 0 ≤ x.2 0 := (d.feasibleOn_subset_relaxationOn Set.univ hx).2.2.2 0 |>.1
    simp only [Fin.sum_univ_one, Matrix.cons_val_one, Matrix.cons_val_zero, d] at hA hlo
    simp only [FiniteModel.objective_apply, Fin.sum_univ_one, d, xOpt]
    linarith

end TauCeti.ConvexLifting
