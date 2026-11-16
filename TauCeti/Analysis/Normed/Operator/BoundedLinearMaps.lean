/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Bounded bilinear maps and bounded scalar actions over a normed ring

Over a commutative semiring `R`, an `R`-bilinear map `β` between seminormed `R`-modules with
`‖β x y‖ ≤ C * ‖x‖ * ‖y‖` is jointly continuous (`LinearMap.continuous₂_of_bound`). Over a
seminormed commutative ring `R`, a scalar action with `‖r • m‖ ≤ C * ‖r‖ * ‖m‖` is therefore
continuous (`TauCeti.continuousSMul_of_norm_smul_le`), with contractive actions supplying `C = 1`
(`TauCeti.exists_norm_smul_le`), and for an `R`-algebra `S` such a bound makes the structure map
bounded (`TauCeti.exists_norm_algebraMap_le_of_norm_smul_le`).

A fibrewise linear change of coordinates `(x, v) ↦ (x, e x v)`, with `e` continuous at `a`, tends
to `(a, 0)` at `(a, 0)` (`ContinuousAt.tendsto_prodMk_clm_apply`).
-/

public section

open Filter Topology
open scoped NNReal

/-- An `R`-bilinear map bounded by `C * ‖x‖ * ‖y‖` is jointly continuous. -/
theorem LinearMap.continuous₂_of_bound {R X Y Z : Type*} [CommSemiring R]
    [SeminormedAddCommGroup X] [Module R X] [SeminormedAddCommGroup Y] [Module R Y]
    [SeminormedAddCommGroup Z] [Module R Z]
    (β : X →ₗ[R] Y →ₗ[R] Z) (C : ℝ) (hβ : ∀ x y, ‖β x y‖ ≤ C * ‖x‖ * ‖y‖) :
    Continuous fun p : X × Y ↦ β p.1 p.2 :=
  IsBoundedBilinearMap.continuous (𝕜 := R)
    { add_left := fun x₁ x₂ y ↦ by simp
      smul_left := fun c x y ↦ by simp
      add_right := fun x y₁ y₂ ↦ by simp
      smul_right := fun c x y ↦ by simp
      bound := ⟨max C 1, by positivity, fun x y ↦
        (hβ x y).trans (by gcongr; exact le_max_left _ _)⟩ }

/-- A contractive scalar action (`IsBoundedSMul R M`) satisfies the explicit constant bound
`‖r • m‖ ≤ C * ‖r‖ * ‖m‖` with `C = 1`. -/
theorem TauCeti.exists_norm_smul_le {R M : Type*} [SeminormedAddGroup R] [SeminormedAddGroup M]
    [SMulZeroClass R M] [IsBoundedSMul R M] :
    ∃ C : ℝ≥0, ∀ (r : R) (m : M), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖ :=
  ⟨1, fun r m ↦ by simpa using norm_smul_le r m⟩

variable {R : Type*} [SeminormedCommRing R]

/-- A scalar action bounded by `C * ‖r‖ * ‖m‖` is continuous. -/
theorem TauCeti.continuousSMul_of_norm_smul_le {M : Type*} [SeminormedAddCommGroup M]
    [Module R M]
    (h : ∃ C : ℝ≥0, ∀ (r : R) (m : M), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) : ContinuousSMul R M :=
  h.elim fun C hC ↦ ⟨(LinearMap.lsmul R M).continuous₂_of_bound C hC⟩

/-- If the action of `R` on an `R`-algebra `S` is bounded, `‖r • s‖ ≤ C * ‖r‖ * ‖s‖`, then so is
the structure map: `‖algebraMap R S r‖ ≤ C * ‖1‖ * ‖r‖`. -/
theorem TauCeti.exists_norm_algebraMap_le_of_norm_smul_le {S : Type*} [SeminormedRing S]
    [Algebra R S] (h : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) :
    ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖ :=
  h.elim fun C hC ↦ ⟨C * ‖(1 : S)‖₊, fun r ↦ by
    simpa [Algebra.algebraMap_eq_smul_one, mul_right_comm] using hC r 1⟩

/-- A fibrewise linear change of coordinates `(x, v) ↦ (x, e x v)`, with `e` continuous at `a`,
tends to `(a, 0)` at `(a, 0)`. -/
theorem ContinuousAt.tendsto_prodMk_clm_apply {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace X] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {e : X → E →L[𝕜] F} {a : X} (he : ContinuousAt e a) :
    Tendsto (fun z : X × E ↦ (z.1, e z.1 z.2)) (𝓝 (a, 0)) (𝓝 (a, 0)) := by
  have h : ContinuousAt (fun z : X × E ↦ e z.1 z.2) (a, 0) :=
    (he.comp (f := Prod.fst) (x := (a, (0 : E))) continuousAt_fst).clm_apply continuousAt_snd
  simpa using continuousAt_fst.tendsto.prodMk_nhds h.tendsto

end
