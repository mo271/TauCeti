/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc

import TauCeti.RingTheory.Huber.WeightedEval.Continuous
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PDeriv
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Rename
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Uncompleted Tate series `A⟨T₁, …, T_N⟩`, integral subrings, and Jacobians

Over a commutative nonarchimedean topological ring `A`, the trivial-weight specialization of
`TauCeti.Huber.weightedRestrictedSubring` is the uncompleted restricted power-series algebra
`TauCeti.Huber.tateSeries N A = A⟨T₁, …, T_N⟩`, equipped with Wedhorn's subgroup topology, its
`A`-algebra structure, and its coordinate variables `TauCeti.Huber.tateSeries.X`. Over a complete
Hausdorff base `A`, `tateSeries N A` is already complete and Hausdorff, and
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` identifies it with the completed polydisc
algebra `restrictedMvPowerSeriesCompletion N A`.

Given a subring `A⁺ ⊆ A`, `TauCeti.Huber.tateSeriesPlus N A A⁺` is the subring `A⁺⟨T₁, …, T_N⟩`
of restricted series whose formal coefficients all lie in `A⁺`, cut out inside `tateSeries N A` as
the preimage of the range of `MvPowerSeries.map A⁺.subtype`. It agrees with
`weightedSubring _ isWeightFamily_one_weight A⁺`, with the uncompleted weighted plus ring
`(S.weighted isWeightFamily_one_weight).plus` of any Huber pair `S = (A, A⁺)`, and (when
`tateSeries N A` is complete and Hausdorff) with `S.polydiscPlus N` across the completion
equivalence.

Finally, formal partial derivatives `MvPowerSeries.pderiv j` restrict to `A`-derivations
`TauCeti.Huber.tateSeries.pderiv` on `tateSeries N A` preserving `tateSeriesPlus`, assembling into
the Jacobian matrix `TauCeti.Huber.tateSeriesJacobianMatrix` and Jacobian determinant
`TauCeti.Huber.tateSeriesJacobian` used in standard étale presentations, while
`TauCeti.Huber.tateSeries.evalAlgHom` packages continuous `A`-algebra evaluation at power-bounded
tuples.

## Main definitions

* `TauCeti.Huber.tateSeries`: the uncompleted restricted power-series algebra `A⟨T₁, …, T_N⟩`.
* `TauCeti.Huber.tateSeries.X`: the `i`-th coordinate variable `Tᵢ` in `tateSeries N A`.
* `TauCeti.Huber.tateSeriesPlus`: the coefficientwise integral subring `A⁺⟨T₁, …, T_N⟩`.
* `TauCeti.Huber.tateSeries.renameAlgHom`, `TauCeti.Huber.tateSeries.finZeroAlgEquiv`, and
  `TauCeti.Huber.tateSeries.evalAlgHom`: variable-renaming `A`-algebra maps, the zero-variable
  equivalence `A⟨⟩ ≃ₐ[A] A`, and continuous evaluation at power-bounded tuples.
* `TauCeti.Huber.tateSeries.pderiv`, `TauCeti.Huber.tateSeriesJacobianMatrix`, and
  `TauCeti.Huber.tateSeriesJacobian`: formal partial derivations and Jacobian determinants on
  `tateSeries N A`.

## Main results

* `TauCeti.Huber.mem_tateSeriesPlus_iff` and `TauCeti.Huber.tateSeriesPlus_eq_weightedSubring`:
  characterize `tateSeriesPlus` coefficientwise and identify it with `weightedSubring`.
* `TauCeti.Huber.Pair.map_tateSeriesPlus_completionEquiv_symm`: identifies `tateSeriesPlus` with
  `Pair.polydiscPlus` under `restrictedMvPowerSeriesCompletionEquiv`.
* `TauCeti.Huber.tateSeries.pderiv_mem_tateSeriesPlus` and
  `TauCeti.Huber.tateSeriesJacobian_mem_tateSeriesPlus`: partial derivatives and Jacobian
  determinants preserve `tateSeriesPlus`.

## References

* [R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*][huber1996], §1.6.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48, Proposition 5.49,
  Example 5.54, and Remark and Definition 8.41.
* [P. Scholze, *Étale cohomology of diamonds*][scholze2017], §24.
-/

public section

open Topology

namespace TauCeti.Huber

/-! ### The restricted power-series algebra `tateSeries` and its variables -/

/-- **The uncompleted restricted power-series algebra `A⟨T₁, …, T_N⟩`** over a commutative
nonarchimedean ring `A`, realized as `weightedRestrictedSubring` for the trivial weight family
`i ↦ {1}`. It inherits its `CommRing`, `Algebra A`, `TopologicalSpace`, `UniformSpace`,
`IsTopologicalRing`, `NonarchimedeanRing`, and (over a complete Hausdorff Huber/Tate base)
`CompleteSpace`, `T2Space`, and `IsHuberRing` instances directly from
`weightedRestrictedSubring`. -/
abbrev tateSeries (N : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Type _ :=
  weightedRestrictedSubring (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight

/-- **The `i`-th coordinate variable `Tᵢ` in `tateSeries N A`.** -/
noncomputable def tateSeries.X (N : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (i : Fin N) : tateSeries N A :=
  weightedX (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight i

section Variables

variable {N : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Unfolding lemma identifying `tateSeries.X` with `weightedX` at trivial weights. -/
theorem tateSeries.X_eq_weightedX (i : Fin N) :
    tateSeries.X N A i =
      weightedX (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight i :=
  (rfl)

/-- Coercing `tateSeries.X N A i` to `MvPowerSeries (Fin N) A` gives `MvPowerSeries.X i`. -/
@[simp]
theorem tateSeries.coe_X (i : Fin N) :
    ((tateSeries.X N A i : tateSeries N A) : MvPowerSeries (Fin N) A) = MvPowerSeries.X i := by
  rw [tateSeries.X, coe_weightedX]

/-- Coercing `algebraMap A (tateSeries N A) a` to `MvPowerSeries (Fin N) A` gives the constant
series `MvPowerSeries.C a`. -/
theorem tateSeries.coe_algebraMap (a : A) :
    ((algebraMap A (tateSeries N A) a : tateSeries N A) : MvPowerSeries (Fin N) A) =
      MvPowerSeries.C a := by
  rw [algebraMap_weightedRestrictedSubring, coe_weightedC]

/-- The constant coefficient of any coordinate variable `Tᵢ` vanishes. -/
theorem tateSeries.constantCoeff_X (i : Fin N) :
    MvPowerSeries.constantCoeff ((tateSeries.X N A i : tateSeries N A) : MvPowerSeries (Fin N) A) =
      0 := by
  simp

/-- Over a nontrivial ring `A`, no coordinate variable `Tᵢ` is a unit in `tateSeries N A`. -/
theorem tateSeries.not_isUnit_X [Nontrivial A] (i : Fin N) :
    ¬ IsUnit (tateSeries.X N A i) := by
  intro hu
  have hcoe : IsUnit ((tateSeries.X N A i : tateSeries N A) : MvPowerSeries (Fin N) A) :=
    hu.map (Subring.subtype _)
  have hconst : IsUnit (0 : A) := by
    simpa using hcoe.map (MvPowerSeries.constantCoeff (σ := Fin N) (R := A))
  exact not_isUnit_zero hconst

/-- Under the completion coercion into `restrictedMvPowerSeriesCompletion N A`, `tateSeries.X`
maps to `Pair.polydiscVar`. -/
@[simp]
theorem tateSeries.coe_completion_X (i : Fin N) :
    ((tateSeries.X N A i : tateSeries N A) : restrictedMvPowerSeriesCompletion N A) =
      Pair.polydiscVar N A i :=
  (rfl)

end Variables

/-! ### The coefficientwise subring `tateSeriesPlus` -/

/-- **The subring `A⁺⟨T₁, …, T_N⟩` inside `tateSeries N A`** consisting of restricted power
series whose formal coefficients all lie in `A⁺`, defined as the preimage in `tateSeries N A` of
the range of `MvPowerSeries.map A⁺.subtype`. -/
noncomputable def tateSeriesPlus (N : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (Aplus : Subring A) : Subring (tateSeries N A) :=
  (MvPowerSeries.map Aplus.subtype).range.comap (Subring.subtype _)

section TateSeriesPlus

variable {N : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- A restricted series lies in `tateSeriesPlus N A Aplus` if and only if every formal coefficient
lies in `Aplus`. -/
theorem mem_tateSeriesPlus_iff {Aplus : Subring A} {f : tateSeries N A} :
    f ∈ tateSeriesPlus N A Aplus ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin N) A) ∈ Aplus := by
  rw [tateSeriesPlus, Subring.mem_comap, Subring.coe_subtype, RingHom.mem_range]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨g, hg⟩ ν
    rw [← hg, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff ν g).2
  · let g : MvPowerSeries (Fin N) Aplus :=
      fun ν ↦ ⟨MvPowerSeries.coeff ν (f : MvPowerSeries (Fin N) A), h ν⟩
    refine ⟨g, ?_⟩
    ext ν
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_apply, Subring.coe_subtype]

/-- `tateSeriesPlus` agrees with `weightedSubring` at the trivial weight family `{1}`. -/
theorem tateSeriesPlus_eq_weightedSubring (Aplus : Subring A) :
    tateSeriesPlus N A Aplus =
      weightedSubring (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight Aplus := by
  ext f
  simp [mem_tateSeriesPlus_iff, weightMul_one_weight]

/-- `tateSeriesPlus` is monotone in the coefficient subring. -/
theorem tateSeriesPlus_mono {R S : Subring A} (h : R ≤ S) :
    tateSeriesPlus N A R ≤ tateSeriesPlus N A S := by
  intro f hf
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  exact fun ν ↦ h (hf ν)

/-- At `A⁺ = ⊤`, `tateSeriesPlus N A ⊤` is the whole restricted series ring `⊤`. -/
@[simp]
theorem tateSeriesPlus_top : tateSeriesPlus N A (⊤ : Subring A) = ⊤ := by
  ext f
  simp [mem_tateSeriesPlus_iff]

/-- A constant series `weightedC ... a` lies in `tateSeriesPlus N A Aplus` if and only if
`a ∈ Aplus`. -/
@[simp]
theorem weightedC_mem_tateSeriesPlus_iff {Aplus : Subring A} {a : A} :
    weightedC (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight a ∈
      tateSeriesPlus N A Aplus ↔ a ∈ Aplus := by
  rw [tateSeriesPlus_eq_weightedSubring, weightedC_mem_weightedSubring]

/-- A constant series `algebraMap A (tateSeries N A) a` lies in `tateSeriesPlus N A Aplus` if and
only if `a ∈ Aplus`. -/
theorem algebraMap_mem_tateSeriesPlus_iff {Aplus : Subring A} {a : A} :
    algebraMap A (tateSeries N A) a ∈ tateSeriesPlus N A Aplus ↔ a ∈ Aplus := by
  rw [algebraMap_weightedRestrictedSubring, weightedC_mem_tateSeriesPlus_iff]

/-- Every coordinate variable `Tᵢ` lies in `tateSeriesPlus N A Aplus`. -/
@[simp]
theorem tateSeries.X_mem_tateSeriesPlus (Aplus : Subring A) (i : Fin N) :
    tateSeries.X N A i ∈ tateSeriesPlus N A Aplus := by
  classical
  rw [mem_tateSeriesPlus_iff]
  intro ν
  rw [tateSeries.coe_X, MvPowerSeries.coeff_X]
  split_ifs
  · exact Aplus.one_mem
  · exact Aplus.zero_mem

/-- `tateSeriesPlus N A Aplus` is open in `tateSeries N A` whenever `Aplus` is open in `A`. -/
theorem isOpen_tateSeriesPlus {Aplus : Subring A} (hopen : IsOpen (Aplus : Set A)) :
    IsOpen (tateSeriesPlus N A Aplus : Set (tateSeries N A)) := by
  rw [tateSeriesPlus_eq_weightedSubring]
  exact isOpen_weightedSubring isWeightFamily_one_weight hopen

end TateSeriesPlus

section PairComparison

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- For a Huber pair `S = (A, A⁺)`, the plus ring of the uncompleted trivial-weight pair
`S.weighted isWeightFamily_one_weight` equals `tateSeriesPlus N A S.plus`. -/
theorem Pair.weighted_plus_eq_tateSeriesPlus (S : Pair A) (N : ℕ) :
    (S.weighted (k := N) isWeightFamily_one_weight).plus = tateSeriesPlus N A S.plus := by
  rw [S.weighted_plus_one_weight, tateSeriesPlus_eq_weightedSubring]

/-- When `tateSeries N A` is complete and Hausdorff, `restrictedMvPowerSeriesCompletionEquiv`
carries `S.polydiscPlus N` onto `tateSeriesPlus N A S.plus`. -/
theorem Pair.map_polydiscPlus_eq_tateSeriesPlus (S : Pair A) (N : ℕ)
    [CompleteSpace (tateSeries N A)] [T0Space (tateSeries N A)] :
    (S.polydiscPlus N).map (restrictedMvPowerSeriesCompletionEquiv N A).toRingHom =
      tateSeriesPlus N A S.plus := by
  rw [tateSeriesPlus_eq_weightedSubring]
  exact S.map_polydiscPlus_equiv N

/-- **Comparison of `tateSeriesPlus` and `Pair.polydiscPlus`.** When `tateSeries N A` is complete
and Hausdorff, `(restrictedMvPowerSeriesCompletionEquiv N A).symm` maps `tateSeriesPlus N A S.plus`
onto `S.polydiscPlus N`. -/
theorem Pair.map_tateSeriesPlus_completionEquiv_symm (S : Pair A) (N : ℕ)
    [CompleteSpace (tateSeries N A)] [T0Space (tateSeries N A)] :
    (tateSeriesPlus N A S.plus).map
        (restrictedMvPowerSeriesCompletionEquiv N A).symm.toRingHom =
      S.polydiscPlus N := by
  rw [← S.map_polydiscPlus_eq_tateSeriesPlus N, Subring.map_map]
  ext x
  simp

end PairComparison

/-! ### Variable renaming and the zero-variable equivalence -/

section RenameAndZero

variable {N M : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **Renaming variables along `e : Fin N ↪ Fin M` as an `A`-algebra homomorphism on
`tateSeries`.** -/
noncomputable def tateSeries.renameAlgHom (e : Fin N ↪ Fin M) :
    tateSeries N A →ₐ[A] tateSeries M A :=
  weightedRenameAlgHom e isWeightFamily_one_weight isWeightFamily_one_weight fun _ ↦ subset_rfl

/-- `tateSeries.renameAlgHom` coerces to `MvPowerSeries.rename e` on formal power series. -/
@[simp]
theorem tateSeries.coe_renameAlgHom (e : Fin N ↪ Fin M) (f : tateSeries N A) :
    ((tateSeries.renameAlgHom e f : tateSeries M A) : MvPowerSeries (Fin M) A) =
      MvPowerSeries.rename e (f : MvPowerSeries (Fin N) A) := by
  simp [tateSeries.renameAlgHom]

/-- `tateSeries.renameAlgHom e` sends `X i` to `X (e i)`. -/
@[simp]
theorem tateSeries.renameAlgHom_X (e : Fin N ↪ Fin M) (i : Fin N) :
    tateSeries.renameAlgHom e (tateSeries.X N A i) = tateSeries.X M A (e i) := by
  simp [tateSeries.renameAlgHom, tateSeries.X]

/-- `tateSeries.renameAlgHom e` is continuous. -/
theorem tateSeries.continuous_renameAlgHom (e : Fin N ↪ Fin M) :
    Continuous (tateSeries.renameAlgHom (A := A) e) :=
  (continuous_weightedRename (A := A) e isWeightFamily_one_weight isWeightFamily_one_weight
    fun _ ↦ subset_rfl).congr fun f ↦ (weightedRenameAlgHom_apply _ _ _ _ f).symm

/-- `tateSeries.renameAlgHom e` is injective. -/
theorem tateSeries.renameAlgHom_injective (e : Fin N ↪ Fin M) :
    Function.Injective (tateSeries.renameAlgHom (A := A) e) := fun _ _ hfg ↦
  weightedRename_injective e (fun _ ↦ subset_rfl)
    (by simpa only [tateSeries.renameAlgHom, weightedRenameAlgHom_apply] using hfg)

/-- Renaming along an embedding preserves and reflects membership in `tateSeriesPlus`. -/
@[simp]
theorem tateSeries.renameAlgHom_mem_tateSeriesPlus_iff (e : Fin N ↪ Fin M)
    {Aplus : Subring A} {f : tateSeries N A} :
    tateSeries.renameAlgHom e f ∈ tateSeriesPlus M A Aplus ↔ f ∈ tateSeriesPlus N A Aplus := by
  rw [mem_tateSeriesPlus_iff, mem_tateSeriesPlus_iff]
  refine ⟨fun h s ↦ ?_, fun h ν ↦ ?_⟩
  · simpa only [tateSeries.coe_renameAlgHom, MvPowerSeries.coeff_embDomain_rename] using
      h (Finsupp.embDomain e s)
  · rw [tateSeries.coe_renameAlgHom]
    by_cases hν : ν ∈ Set.range (Finsupp.embDomain e)
    · obtain ⟨s, rfl⟩ := hν
      simpa only [MvPowerSeries.coeff_embDomain_rename] using h s
    · rw [MvPowerSeries.coeff_rename_eq_zero e _
        (by rwa [← funext (Finsupp.embDomain_eq_mapDomain e)])]
      exact Aplus.zero_mem

/-- **The zero-variable `A`-algebra equivalence `A⟨⟩ ≃ₐ[A] A`.** -/
noncomputable def tateSeries.finZeroAlgEquiv (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : tateSeries 0 A ≃ₐ[A] A :=
  AlgEquiv.ofRingEquiv
    (f := weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))
    fun a ↦ by simp [algebraMap_weightedRestrictedSubring]

@[simp]
theorem tateSeries.finZeroAlgEquiv_apply (f : tateSeries 0 A) :
    tateSeries.finZeroAlgEquiv A f =
      MvPowerSeries.constantCoeff (f : MvPowerSeries (Fin 0) A) := by
  simp [tateSeries.finZeroAlgEquiv]

@[simp]
theorem tateSeries.coe_finZeroAlgEquiv_symm_apply (a : A) :
    (((tateSeries.finZeroAlgEquiv A).symm a : tateSeries 0 A) : MvPowerSeries (Fin 0) A) =
      MvPowerSeries.C a := by
  simp [tateSeries.finZeroAlgEquiv]

theorem tateSeries.continuous_finZeroAlgEquiv :
    Continuous (tateSeries.finZeroAlgEquiv A) :=
  continuous_weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A))

theorem tateSeries.continuous_finZeroAlgEquiv_symm :
    Continuous (tateSeries.finZeroAlgEquiv A).symm :=
  continuous_weightedRestrictedSubringFinZeroEquiv_symm (fun _ : Fin 0 ↦ ({1} : Set A))

/-- `tateSeries.finZeroAlgEquiv A` is a topological quotient map, being a homeomorphism. -/
theorem tateSeries.isQuotientMap_finZeroAlgEquiv :
    IsQuotientMap (tateSeries.finZeroAlgEquiv A) :=
  (Homeomorph.mk (tateSeries.finZeroAlgEquiv A).toEquiv
    tateSeries.continuous_finZeroAlgEquiv
    tateSeries.continuous_finZeroAlgEquiv_symm).isQuotientMap

/-- In zero variables, `tateSeries.finZeroAlgEquiv A` maps `tateSeriesPlus 0 A Aplus` onto
`Aplus`. -/
@[simp]
theorem tateSeries.map_tateSeriesPlus_finZeroAlgEquiv (Aplus : Subring A) :
    (tateSeriesPlus 0 A Aplus).map (tateSeries.finZeroAlgEquiv A : tateSeries 0 A →+* A) =
      Aplus := by
  ext a
  simp only [Subring.mem_map]
  refine ⟨?_, fun ha ↦ ⟨algebraMap A (tateSeries 0 A) a,
    algebraMap_mem_tateSeriesPlus_iff.mpr ha, (tateSeries.finZeroAlgEquiv A).commutes a⟩⟩
  rintro ⟨f, hf, rfl⟩
  simpa [tateSeries.finZeroAlgEquiv_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff] using
    mem_tateSeriesPlus_iff.mp hf 0

end RenameAndZero

/-! ### Formal partial derivatives and Jacobians on `tateSeries` -/

section Jacobian

variable {N M : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The `j`-th formal partial derivative `∂/∂Tⱼ` on `tateSeries N A`**, bundled as an
`A`-derivation by restricting `MvPowerSeries.pderiv j`. -/
noncomputable def tateSeries.pderiv (j : Fin N) :
    Derivation A (tateSeries N A) (tateSeries N A) where
  toFun f := ⟨MvPowerSeries.pderiv j (f : MvPowerSeries (Fin N) A),
    mem_weightedRestrictedSubring.mpr ((mem_weightedRestrictedSubring.mp f.2).pderiv_one_weight j)⟩
  map_add' f g := Subtype.ext (by simp)
  map_smul' a f := Subtype.ext (by simp [Algebra.smul_def])
  map_one_eq_zero' := Subtype.ext (by simp)
  leibniz' f g := Subtype.ext <| by
    simpa only [Subring.coe_add, Subring.coe_mul, smul_eq_mul, LinearMap.coe_mk,
      AddHom.coe_mk] using
      (MvPowerSeries.pderiv j).leibniz
        (f : MvPowerSeries (Fin N) A) (g : MvPowerSeries (Fin N) A)

/-- Coercing `tateSeries.pderiv j f` to `MvPowerSeries (Fin N) A` gives
`MvPowerSeries.pderiv j f`. -/
@[simp]
theorem tateSeries.coe_pderiv (j : Fin N) (f : tateSeries N A) :
    ((tateSeries.pderiv j f : tateSeries N A) : MvPowerSeries (Fin N) A) =
      MvPowerSeries.pderiv j (f : MvPowerSeries (Fin N) A) :=
  (rfl)

/-- Coefficient formula for `tateSeries.pderiv`. -/
theorem tateSeries.coeff_pderiv (j : Fin N) (f : tateSeries N A) (ν : Fin N →₀ ℕ) :
    MvPowerSeries.coeff ν (tateSeries.pderiv j f : MvPowerSeries (Fin N) A) =
      MvPowerSeries.coeff (ν + Finsupp.single j 1) (f : MvPowerSeries (Fin N) A) * (ν j + 1) :=
  MvPowerSeries.coeff_pderiv _ _

@[simp]
theorem tateSeries.pderiv_X_self (i : Fin N) :
    tateSeries.pderiv i (tateSeries.X N A i) = 1 :=
  Subtype.ext (by simp)

@[simp]
theorem tateSeries.pderiv_X_of_ne {i j : Fin N} (h : i ≠ j) :
    tateSeries.pderiv j (tateSeries.X N A i) = 0 :=
  Subtype.ext (by simp [MvPowerSeries.pderiv_X_of_ne h])

theorem tateSeries.pderiv_X (j i : Fin N) :
    tateSeries.pderiv j (tateSeries.X N A i) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · exact tateSeries.pderiv_X_of_ne h

/-- Formal partial differentiation vanishes on constant restricted series `weightedC`. -/
@[simp]
theorem tateSeries.pderiv_weightedC (j : Fin N) (a : A) :
    tateSeries.pderiv j
      (weightedC (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight a) = 0 :=
  (tateSeries.pderiv j).map_algebraMap a

/-- Formal partial differentiation vanishes on `algebraMap A (tateSeries N A) a`. -/
theorem tateSeries.pderiv_algebraMap (j : Fin N) (a : A) :
    tateSeries.pderiv j (algebraMap A (tateSeries N A) a) = 0 :=
  (tateSeries.pderiv j).map_algebraMap a

/-- Product rule for `tateSeries.pderiv` written with ring multiplication. -/
theorem tateSeries.pderiv_mul (j : Fin N) (f g : tateSeries N A) :
    tateSeries.pderiv j (f * g) = f * tateSeries.pderiv j g + g * tateSeries.pderiv j f := by
  simpa only [smul_eq_mul] using (tateSeries.pderiv j).leibniz f g

/-- Power rule for `tateSeries.pderiv` written with ring multiplication. -/
theorem tateSeries.pderiv_pow (j : Fin N) (f : tateSeries N A) (n : ℕ) :
    tateSeries.pderiv j (f ^ n) = (n : tateSeries N A) * f ^ (n - 1) * tateSeries.pderiv j f := by
  simpa only [nsmul_eq_mul, smul_eq_mul, mul_assoc] using (tateSeries.pderiv j).leibniz_pow f n

/-- Formal partial differentiation preserves `tateSeriesPlus`. -/
theorem tateSeries.pderiv_mem_tateSeriesPlus {Aplus : Subring A} (j : Fin N) {f : tateSeries N A}
    (hf : f ∈ tateSeriesPlus N A Aplus) :
    tateSeries.pderiv j f ∈ tateSeriesPlus N A Aplus := by
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  exact MvPowerSeries.coeff_pderiv_mem hf j

/-- Differentiating a renamed series with respect to a renamed variable commutes with renaming. -/
@[simp]
theorem tateSeries.pderiv_renameAlgHom_apply (e : Fin N ↪ Fin M) (j : Fin N) (f : tateSeries N A) :
    tateSeries.pderiv (e j) (tateSeries.renameAlgHom e f) =
      tateSeries.renameAlgHom e (tateSeries.pderiv j f) := by
  apply Subtype.ext
  rw [tateSeries.coe_pderiv, tateSeries.coe_renameAlgHom, tateSeries.coe_renameAlgHom,
    tateSeries.coe_pderiv, MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.pderiv_subst (MvPowerSeries.HasSubst.X_comp e)]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Function.comp_apply, MvPowerSeries.pderiv_X_of_ne (e.injective.ne hij), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Differentiating a renamed series with respect to a variable outside the image of `e` gives
zero. -/
theorem tateSeries.pderiv_renameAlgHom_of_notMem_range (e : Fin N ↪ Fin M) {j : Fin M}
    (hj : j ∉ Set.range e) (f : tateSeries N A) :
    tateSeries.pderiv j (tateSeries.renameAlgHom e f) = 0 := by
  apply Subtype.ext
  rw [tateSeries.coe_pderiv, tateSeries.coe_renameAlgHom, Subring.coe_zero,
    MvPowerSeries.rename_eq_subst,
    MvPowerSeries.pderiv_subst (MvPowerSeries.HasSubst.X_comp e)]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hij : e i ≠ j := fun h ↦ hj ⟨i, h⟩
  rw [Function.comp_apply, MvPowerSeries.pderiv_X_of_ne hij, mul_zero]

/-- **The `N × N` Jacobian matrix `(∂Fᵢ/∂Tⱼ)` of a tuple `F : Fin N → tateSeries N A`.** -/
noncomputable def tateSeriesJacobianMatrix (F : Fin N → tateSeries N A) :
    Matrix (Fin N) (Fin N) (tateSeries N A) :=
  Matrix.of fun i j ↦ tateSeries.pderiv j (F i)

@[simp]
theorem tateSeriesJacobianMatrix_apply (F : Fin N → tateSeries N A) (i j : Fin N) :
    tateSeriesJacobianMatrix F i j = tateSeries.pderiv j (F i) :=
  (rfl)

/-- **The Jacobian determinant `det (∂Fᵢ/∂Tⱼ)` of `F : Fin N → tateSeries N A`**, as an element of
`tateSeries N A`. -/
noncomputable def tateSeriesJacobian (F : Fin N → tateSeries N A) : tateSeries N A :=
  (tateSeriesJacobianMatrix F).det

/-- Defining equation of `tateSeriesJacobian`, whose body is not exposed across modules. -/
theorem tateSeriesJacobian_def (F : Fin N → tateSeries N A) :
    tateSeriesJacobian F = (tateSeriesJacobianMatrix F).det :=
  (rfl)

/-- Coercing `tateSeriesJacobian F` to `MvPowerSeries (Fin N) A` gives the determinant of the
formal partial-derivative matrix `(MvPowerSeries.pderiv j (F i))`. -/
@[simp]
theorem coe_tateSeriesJacobian (F : Fin N → tateSeries N A) :
    (tateSeriesJacobian F : MvPowerSeries (Fin N) A) =
      (Matrix.of fun i j ↦ MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A)).det := by
  have h := RingHom.map_det (Subring.subtype _) (tateSeriesJacobianMatrix F)
  refine h.trans (congrArg Matrix.det ?_)
  ext i j
  simp

/-- If every component of `F` lies in `tateSeriesPlus N A Aplus`, then so does
`tateSeriesJacobian F`. -/
theorem tateSeriesJacobian_mem_tateSeriesPlus {Aplus : Subring A} {F : Fin N → tateSeries N A}
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus) :
    tateSeriesJacobian F ∈ tateSeriesPlus N A Aplus := by
  let M : Matrix (Fin N) (Fin N) (tateSeriesPlus N A Aplus) :=
    Matrix.of fun i j ↦ ⟨tateSeries.pderiv j (F i), tateSeries.pderiv_mem_tateSeriesPlus j (hF i)⟩
  have hdet :
      ((tateSeriesPlus N A Aplus).subtype M.det : tateSeries N A) = tateSeriesJacobian F := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det (Matrix.ext fun _ _ ↦ rfl)
  exact hdet ▸ M.det.2

/-- In zero variables, the Jacobian determinant of the empty system is `1`. -/
@[simp]
theorem tateSeriesJacobian_fin_zero (F : Fin 0 → tateSeries 0 A) :
    tateSeriesJacobian F = 1 := by
  simp [tateSeriesJacobian]

/-- In one variable, the Jacobian determinant of `F : Fin 1 → tateSeries 1 A` is `∂(F 0)/∂T₀`. -/
@[simp]
theorem tateSeriesJacobian_fin_one (F : Fin 1 → tateSeries 1 A) :
    tateSeriesJacobian F = tateSeries.pderiv 0 (F 0) := by
  simp [tateSeriesJacobian, tateSeriesJacobianMatrix]

/-- In two variables, the Jacobian determinant is `(∂F₀/∂T₀)(∂F₁/∂T₁) - (∂F₀/∂T₁)(∂F₁/∂T₀)`. -/
theorem tateSeriesJacobian_fin_two (F : Fin 2 → tateSeries 2 A) :
    tateSeriesJacobian F =
      tateSeries.pderiv 0 (F 0) * tateSeries.pderiv 1 (F 1) -
        tateSeries.pderiv 1 (F 0) * tateSeries.pderiv 0 (F 1) := by
  simp [tateSeriesJacobian, tateSeriesJacobianMatrix, Matrix.det_fin_two]

end Jacobian

/-! ### Continuous evaluation and uniqueness of `A`-algebra maps on `tateSeries` -/

section Eval

variable {N M : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Two continuous `A`-algebra homomorphisms out of `tateSeries N A` into a Hausdorff `A`-algebra
agree as soon as they agree on every coordinate variable `tateSeries.X N A i`. -/
theorem tateSeries.algHom_ext_of_continuous {B : Type*} [Semiring B] [TopologicalSpace B]
    [T2Space B] [Algebra A B] {φ ψ : tateSeries N A →ₐ[A] B} (hφ : Continuous φ)
    (hψ : Continuous ψ) (hX : ∀ i, φ (tateSeries.X N A i) = ψ (tateSeries.X N A i)) :
    φ = ψ := by
  apply AlgHom.toRingHom_injective
  refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight hφ hψ
    (fun a ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_coe, ← algebraMap_weightedRestrictedSubring, AlgHom.commutes]
  · simpa only [RingHom.coe_coe, tateSeries.X_eq_weightedX] using hX i

section EvalAlgHom

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T3Space B] [Algebra A B]

/-- **Continuous `A`-algebra evaluation of `tateSeries N A` at power-bounded elements** of a
complete `T3Space` nonarchimedean `A`-algebra `B` whose structure map `algebraMap A B` is
continuous at zero. -/
noncomputable def tateSeries.evalAlgHom (hcont : ContinuousAt (algebraMap A B) 0)
    {x : Fin N → B} (hx : ∀ i, IsPowerBounded (x i)) : tateSeries N A →ₐ[A] B where
  toRingHom := weightedEvalHom isWeightFamily_one_weight hcont
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded (algebraMap A B) x).mpr hx)
  commutes' a := weightedEvalHom_weightedC isWeightFamily_one_weight hcont
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded (algebraMap A B) x).mpr hx) a

/-- `tateSeries.evalAlgHom` is continuous with respect to Wedhorn's subgroup topology. -/
theorem tateSeries.continuous_evalAlgHom (hcont : ContinuousAt (algebraMap A B) 0)
    {x : Fin N → B} (hx : ∀ i, IsPowerBounded (x i)) :
    Continuous (tateSeries.evalAlgHom hcont hx) :=
  continuous_weightedEvalHom isWeightFamily_one_weight hcont
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded (algebraMap A B) x).mpr hx)

@[simp]
theorem tateSeries.evalAlgHom_X (hcont : ContinuousAt (algebraMap A B) 0)
    {x : Fin N → B} (hx : ∀ i, IsPowerBounded (x i)) (i : Fin N) :
    tateSeries.evalAlgHom hcont hx (tateSeries.X N A i) = x i := by
  rw [tateSeries.X_eq_weightedX]
  exact weightedEvalHom_weightedX isWeightFamily_one_weight hcont
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded (algebraMap A B) x).mpr hx) i

@[simp]
theorem tateSeries.evalAlgHom_comp_renameAlgHom (e : Fin N ↪ Fin M)
    (hcont : ContinuousAt (algebraMap A B) 0) {x : Fin M → B}
    (hx : ∀ i, IsPowerBounded (x i)) :
    (tateSeries.evalAlgHom hcont hx).comp (tateSeries.renameAlgHom e) =
      tateSeries.evalAlgHom hcont (fun i ↦ hx (e i)) := by
  refine tateSeries.algHom_ext_of_continuous
    ((tateSeries.continuous_evalAlgHom hcont hx).comp (tateSeries.continuous_renameAlgHom e))
    (tateSeries.continuous_evalAlgHom hcont _) fun i ↦ ?_
  simp

end EvalAlgHom

end Eval

end TauCeti.Huber

end
