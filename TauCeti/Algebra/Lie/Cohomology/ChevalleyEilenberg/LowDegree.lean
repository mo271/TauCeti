/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Submodule
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Low-degree and vanishing results for Chevalley–Eilenberg cohomology

This file identifies the low-degree cohomology groups of the Chevalley–Eilenberg complex
`TauCeti.LieModule.Cohomology.cochainComplex` with the concrete `R`-modules of invariants and
low-degree cocycles modulo coboundaries:

* In degree `0`, `cohomologyZeroEquiv` identifies `cohomology R L M 0` with
  `LieModule.maxTrivSubmodule R L M` (the `L`-invariants of `M`).
* In degree `1`, `cohomologyOneIso` and `cohomologyOneEquiv` identify `cohomology R L M 1` with
  `firstCohomology R L M` (one-cocycles modulo principal cocycles from
  `TauCeti.Algebra.Lie.Cohomology.LowDegree`).
* In positive degree `n + 1`, `cohomologySuccIso` and `cohomologySuccEquiv` expose
  `cohomology R L M (n + 1)` as the explicit quotient of `ker (d R L M (n + 1))` by the image of
  `d R L M n`.
* In degrees strictly above `Module.finrank R L`, `subsingleton_cohomology_of_finrank_lt` proves
  that Chevalley–Eilenberg cohomology vanishes whenever `L` is finite and free over `R`.

## Main definitions

* `TauCeti.LieModule.Cohomology.cohomologyZeroEquiv` / `cohomologyZeroIso`:
  `H⁰(L, M) ≃ M^L`.
* `TauCeti.LieModule.Cohomology.cohomologySuccIso` / `cohomologySuccEquiv`:
  explicit kernel-modulo-range presentation of `H^(n+1)(L, M)`.
* `TauCeti.LieModule.Cohomology.cohomologyOneIso` / `cohomologyOneEquiv`:
  `H¹(L, M) ≃ firstCohomology R L M`.
* `TauCeti.LieModule.Cohomology.cohomologyZeroEquivOfIsTrivial`: `H⁰(L, M) ≃ₗ[R] M` for a trivial
  `L`-module `M`.

## Main results

* `TauCeti.LieModule.Cohomology.subsingleton_cohomology_of_subsingleton`: vanishing when the
  cochain module is subsingleton.
* `TauCeti.LieModule.Cohomology.subsingleton_cohomology_of_finrank_lt`: vanishing above the rank of
  a finite free Lie algebra.
* `TauCeti.LieModule.Cohomology.d_zero_eq_zero_of_isTrivial` / `d_one_apply_of_isTrivial`:
  explicit low-degree differential formulas for trivial coefficients.
-/

public section

open CategoryTheory _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

universe u v w

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-! ### Degree zero: `H⁰(L, M) ≃ M^L` -/

/-- Zero-cochains whose differential vanishes are linearly equivalent to the maximal trivial
submodule `M^L`. -/
def kerDZeroEquivMaxTriv :
    LinearMap.ker (d R L M 0) ≃ₗ[R] LieModule.maxTrivSubmodule R L M where
  toFun ω := ⟨ω.1 ![], fun x ↦ by
    have h := congrArg (fun f : L [⋀^Fin 1]→ₗ[R] M ↦ f ![x]) (LinearMap.mem_ker.mp ω.2)
    rw [d_zero_apply] at h
    exact h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨(AlternatingMap.constLinearEquivOfIsEmpty (R' := R) (M'' := L) (N'' := M)
      (ι := Fin 0)) m.1, by
    rw [LinearMap.mem_ker]
    ext v
    rw [d_zero_apply]
    exact m.2 (v 0)⟩
  left_inv ω := by
    ext v
    simp [Subsingleton.elim v ![]]
  right_inv _ := rfl

@[simp]
theorem kerDZeroEquivMaxTriv_apply_val (ω : LinearMap.ker (d R L M 0)) :
    (kerDZeroEquivMaxTriv R L M ω : M) = ω.1 ![] := (rfl)

@[simp]
theorem kerDZeroEquivMaxTriv_symm_apply_val (m : LieModule.maxTrivSubmodule R L M)
    (v : Fin 0 → L) :
    ((kerDZeroEquivMaxTriv R L M).symm m).1 v = m.1 := (rfl)

/-- In degree `0`, Chevalley–Eilenberg cohomology is the kernel of `d R L M 0`. -/
noncomputable def cohomologyZeroIsoKer :
    cohomology R L M 0 ≅ ModuleCat.of R (LinearMap.ker (d R L M 0)) :=
  (((cochainComplex R L M).homologyIsoSc' 0 0 1 (by simp) (by simp)).trans
    (ShortComplex.asIsoHomologyπ (S := (cochainComplex R L M).sc' 0 0 1)
      ((cochainComplex R L M).shape 0 0 (by simp))).symm).trans
    (((cochainComplex R L M).sc' 0 0 1).moduleCatCyclesIso.trans
      (LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ (by
        change LinearMap.ker ((cochainComplex R L M).d 0 1).hom = LinearMap.ker (d R L M 0)
        rw [cochainComplex_d_succ]
        rfl))))

/-- In degree `0`, Chevalley–Eilenberg cohomology is linearly equivalent to the maximal trivial
submodule `LieModule.maxTrivSubmodule R L M` (for arbitrary universes). -/
noncomputable def cohomologyZeroEquiv :
    cohomology R L M 0 ≃ₗ[R] LieModule.maxTrivSubmodule R L M :=
  (cohomologyZeroIsoKer R L M).toLinearEquiv ≪≫ₗ kerDZeroEquivMaxTriv R L M

/-- In degree `0`, when `L` and `M` live in the same universe, Chevalley–Eilenberg cohomology is
isomorphic in `ModuleCat R` to `LieModule.maxTrivSubmodule R L M`. -/
noncomputable def cohomologyZeroIso (L M : Type v) [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] :
    cohomology R L M 0 ≅ ModuleCat.of R (LieModule.maxTrivSubmodule R L M) :=
  (cohomologyZeroEquiv R L M).toModuleIso

/-! ### Explicit presentation in positive degrees -/

/-- The `n`-th differential with codomain restricted to `(n + 1)`-cocycles. -/
def dToCycles (n : ℕ) :
    (L [⋀^Fin n]→ₗ[R] M) →ₗ[R] LinearMap.ker (d R L M (n + 1)) :=
  (d R L M n).codRestrict (LinearMap.ker (d R L M (n + 1))) fun ω ↦ by
    rw [LinearMap.mem_ker, d_d]

@[simp]
theorem dToCycles_coe (n : ℕ) (ω : L [⋀^Fin n]→ₗ[R] M) :
    (dToCycles R L M n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω := (rfl)

/-- The explicit short complex for degree `n + 1` built directly from `d R L M n` and
`d R L M (n + 1)`. -/
noncomputable def shortComplexSucc (n : ℕ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom (d R L M n)) (ModuleCat.ofHom (d R L M (n + 1))) (by
    rw [← ModuleCat.ofHom_comp, d_comp_d, ModuleCat.ofHom_zero])

/-- In degree `n + 1`, Chevalley–Eilenberg cohomology is isomorphic to the quotient of
`ker (d R L M (n + 1))` by the range of `dToCycles R L M n`. -/
noncomputable def cohomologySuccIso (n : ℕ) :
    cohomology R L M (n + 1) ≅
      ModuleCat.of R (LinearMap.ker (d R L M (n + 1)) ⧸ LinearMap.range (dToCycles R L M n)) :=
  let S := shortComplexSucc R L M n
  let eKer : LinearMap.ker S.g.hom ≃ₗ[R] LinearMap.ker (d R L M (n + 1)) :=
    LinearEquiv.ofEq _ _ rfl
  let hMap :
      (LinearMap.range S.moduleCatToCycles).map eKer.toLinearMap =
        LinearMap.range (dToCycles R L M n) := by
    ext ⟨ω, hω⟩
    constructor
    · rintro ⟨_, ⟨η, rfl⟩, h⟩
      exact ⟨η, Subtype.ext (congrArg Subtype.val h)⟩
    · rintro ⟨η, h⟩
      exact ⟨S.moduleCatToCycles η, ⟨η, rfl⟩, Subtype.ext (congrArg Subtype.val h)⟩
  let eSC : (cochainComplex R L M).sc' n (n + 1) (n + 2) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (cochainComplex_d_succ R L M n).symm
      (cochainComplex_d_succ R L M (n + 1)).symm
  ((cochainComplex R L M).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).trans <|
    (ShortComplex.homologyMapIso eSC).trans <|
      S.moduleCatHomologyIso.trans
        (Submodule.Quotient.equiv _ _ eKer hMap).toModuleIso

/-- In degree `n + 1`, Chevalley–Eilenberg cohomology is linearly equivalent to the quotient of
`ker (d R L M (n + 1))` by the range of `dToCycles R L M n`. -/
noncomputable def cohomologySuccEquiv (n : ℕ) :
    cohomology R L M (n + 1) ≃ₗ[R]
      LinearMap.ker (d R L M (n + 1)) ⧸ LinearMap.range (dToCycles R L M n) :=
  (cohomologySuccIso R L M n).toLinearEquiv

/-! ### Degree one: `H¹(L, M) ≃ firstCohomology R L M` -/

/-- `oneCochainEquiv` restricts to a linear equivalence between `ker (d R L M 1)` and
`oneCocycle R L M`. -/
def kerDOneEquivOneCocycle :
    LinearMap.ker (d R L M 1) ≃ₗ[R] oneCocycle R L M :=
  LinearEquiv.ofLinearMap
    { toFun ω := ⟨oneCochainEquiv R L M ω.1, (mem_oneCocycle_iff R L M).mpr fun x y ↦ by
        have h := congrArg (fun c : twoCochain R L M ↦ c x y) (twoCochainEquiv_d_one ω.1)
        rw [LinearMap.mem_ker.mp ω.2, map_zero] at h
        have h' : ⁅x, oneCochainEquiv R L M ω.1 y⁆ - ⁅y, oneCochainEquiv R L M ω.1 x⁆ -
            oneCochainEquiv R L M ω.1 ⁅x, y⁆ = 0 := by
          change (0 : M) = _ at h
          rw [d₁₂_apply_apply] at h
          exact h.symm
        exact (sub_eq_zero.mp h').symm⟩
      map_add' _ _ := Subtype.ext (map_add _ _ _)
      map_smul' r _ := Subtype.ext (map_smul _ r _) }
    { toFun f := ⟨(oneCochainEquiv R L M).symm f.1, by
        rw [LinearMap.mem_ker]
        apply (twoCochainEquiv R L M).injective
        rw [twoCochainEquiv_d_one, LinearEquiv.apply_symm_apply, map_zero]
        apply Subtype.ext
        ext x y
        change ⁅x, f.1 y⁆ - ⁅y, f.1 x⁆ - f.1 ⁅x, y⁆ = 0
        rw [oneCocycle_apply_lie]
        abel⟩
      map_add' _ _ := Subtype.ext (map_add _ _ _)
      map_smul' r _ := Subtype.ext (map_smul _ r _) }
    (by ext f x; simp)
    (by ext ω v; simp)

@[simp]
theorem kerDOneEquivOneCocycle_apply_val (ω : LinearMap.ker (d R L M 1)) :
    (kerDOneEquivOneCocycle R L M ω : oneCochain R L M) = oneCochainEquiv R L M ω.1 := (rfl)

@[simp]
theorem kerDOneEquivOneCocycle_symm_apply_val (f : oneCocycle R L M) :
    ((kerDOneEquivOneCocycle R L M).symm f : L [⋀^Fin 1]→ₗ[R] M) =
      (oneCochainEquiv R L M).symm f.1 := (rfl)

private theorem map_range_dToCycles_zero :
    (LinearMap.range (dToCycles R L M 0)).map (kerDOneEquivOneCocycle R L M).toLinearMap =
      oneCoboundary R L M := by
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_range, mem_oneCoboundary_iff]
  constructor
  · rintro ⟨_, ⟨ω, rfl⟩, rfl⟩
    refine ⟨ω ![], Subtype.ext ?_⟩
    simpa [d₀₁Cocycle_coe, kerDOneEquivOneCocycle_apply_val] using
      (oneCochainEquiv_d_zero ω).symm
  · rintro ⟨m, rfl⟩
    let ω₀ : L [⋀^Fin 0]→ₗ[R] M :=
      AlternatingMap.constLinearEquivOfIsEmpty (R' := R) (M'' := L) (N'' := M) (ι := Fin 0) m
    refine ⟨dToCycles R L M 0 ω₀, ⟨ω₀, rfl⟩, Subtype.ext ?_⟩
    simpa [ω₀, d₀₁Cocycle_coe, kerDOneEquivOneCocycle_apply_val] using
      oneCochainEquiv_d_zero ω₀

/-- In degree `1`, Chevalley–Eilenberg cohomology is isomorphic to `firstCohomology R L M`
(one-cocycles modulo principal cocycles). -/
noncomputable def cohomologyOneIso :
    cohomology R L M 1 ≅ ModuleCat.of R (firstCohomology R L M) :=
  (cohomologySuccIso R L M 0).trans
    ((Submodule.Quotient.equiv (LinearMap.range (dToCycles R L M 0)) (oneCoboundary R L M)
      (kerDOneEquivOneCocycle R L M) (map_range_dToCycles_zero R L M)).toModuleIso)

/-- In degree `1`, Chevalley–Eilenberg cohomology is linearly equivalent to
`firstCohomology R L M`. -/
noncomputable def cohomologyOneEquiv :
    cohomology R L M 1 ≃ₗ[R] firstCohomology R L M :=
  (cohomologyOneIso R L M).toLinearEquiv

/-! ### Vanishing above the rank -/

variable {R L M}

/-- Chevalley–Eilenberg cohomology vanishes in any degree whose cochain module is subsingleton. -/
theorem subsingleton_cohomology_of_subsingleton {n : ℕ}
    [h : Subsingleton (L [⋀^Fin n]→ₗ[R] M)] :
    Subsingleton (cohomology R L M n) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact ShortComplex.isZero_homology_of_isZero_X₂ (S := (cochainComplex R L M).sc n)
    (ModuleCat.isZero_iff_subsingleton.mpr h)

/-- Chevalley–Eilenberg cohomology vanishes in degrees strictly above the rank of a finite free
Lie algebra. -/
theorem subsingleton_cohomology_of_finrank_lt [Module.Free R L] [Module.Finite R L] {n : ℕ}
    (h : Module.finrank R L < n) :
    Subsingleton (cohomology R L M n) := by
  have : Subsingleton (L [⋀^Fin n]→ₗ[R] M) := by
    refine ⟨fun f g ↦ exteriorPower.alternatingMapLinearEquiv.injective (LinearMap.ext fun x ↦ ?_)⟩
    simp [exteriorPower.eq_zero_of_finrank_lt n h x]
  exact subsingleton_cohomology_of_subsingleton

/-! ### Trivial coefficients -/

section Trivial

variable [LieModule.IsTrivial L M]

/-- For a trivial Lie module `M`, the degree-`0` Chevalley–Eilenberg differential vanishes. -/
theorem d_zero_eq_zero_of_isTrivial : d R L M 0 = 0 := by
  ext ω v
  rw [LinearMap.zero_apply, zero_apply, d_zero_apply]
  exact LieModule.IsTrivial.trivial (v 0) (ω ![])

/-- For a trivial Lie module `M`, `(d 1 ω)(x, y) = -ω(⁅x, y⁆)`. -/
theorem d_one_apply_of_isTrivial (ω : L [⋀^Fin 1]→ₗ[R] M) (x y : L) :
    d R L M 1 ω ![x, y] = -ω ![⁅x, y⁆] := by
  rw [d_succ_apply]
  have h1 : ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
      ⁅![x, y] i, ω (i.removeNth ![x, y])⁆ = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      rw [LieModule.IsTrivial.trivial, smul_zero]
  rw [h1, zero_add]
  have hsum : (∑ i : Fin 1, ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
      ω (Matrix.vecCons ⁅![x, y] i.castSucc, ![x, y] j.succ⁆
        (j.removeNth (i.castSucc.removeNth ![x, y])))) =
      (-1 : ℤ) ^ (1 : ℕ) • ω ![⁅x, y⁆] := by
    rw [Fin.sum_univ_one]
    have hIci : Finset.Ici (0 : Fin 1) = {0} := by decide
    rw [hIci, Finset.sum_singleton]
    have hvec : Matrix.vecCons ⁅![x, y] (0 : Fin 1).castSucc, ![x, y] (0 : Fin 1).succ⁆
        ((0 : Fin 1).removeNth ((0 : Fin 1).castSucc.removeNth ![x, y])) = ![⁅x, y⁆] := by
      ext k
      fin_cases k
      rfl
    rw [hvec]
    rfl
  rw [hsum]
  simp

variable (R L M)

/-- For a trivial Lie module `M`, `H⁰(L, M) ≃ₗ[R] M`. -/
noncomputable def cohomologyZeroEquivOfIsTrivial : cohomology R L M 0 ≃ₗ[R] M :=
  cohomologyZeroEquiv R L M ≪≫ₗ
    LinearEquiv.ofTop (LieModule.maxTrivSubmodule R L M).toSubmodule
      (congrArg LieSubmodule.toSubmodule
        ((LieModule.isTrivial_iff_max_triv_eq_top R L M).mp inferInstance))

end Trivial

end TauCeti.LieModule.Cohomology
