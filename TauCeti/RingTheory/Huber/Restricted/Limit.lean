/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Limit
public import TauCeti.RingTheory.AdicCompletion.UniformCompletion
public import TauCeti.RingTheory.Huber.Restricted.Reduction

/-!
# Projective-limit presentation of adic restricted power series

Let `A` be a nonarchimedean commutative ring whose topology is the `I`-adic topology of a finitely
generated ideal `I`. Building on the adic completeness results in
`TauCeti.RingTheory.Huber.Restricted.Adic`, this module establishes the algebraic adic-completion
comparison and projective-limit presentation of both the completed restricted power-series algebra
`A⟨X₁, …, Xₖ⟩` (`TauCeti.Huber.restrictedMvPowerSeriesCompletion k A`) and the uncompleted
restricted-series subring (`TauCeti.Huber.weightedRestrictedSubring` at weight `{1}`):

* Without assuming `A` complete or Hausdorff, `A⟨X₁, …, Xₖ⟩` is canonically isomorphic as a
  topological `A`-algebra to the algebraic adic completion `AdicCompletion (I · S) S` of the
  uncompleted subring `S`, and is the projective limit in `CommRingCat` of the polynomial algebras
  `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` along `MvPolynomial.map (Ideal.Quotient.factorPow I _)`.
* When `A` is `I`-adically complete, transporting along `restrictedMvPowerSeriesCompletionEquiv`
  exhibits the uncompleted subring `S` itself as the projective limit of
  `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`.

## Main definitions

* `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquivAdicCompletion`: the `A`-algebra isomorphism
  `A⟨X₁, …, Xₖ⟩ ≃ₐ[A] AdicCompletion (I · S) S`.
* `TauCeti.Huber.restrictedReductionCompletionLift` and `TauCeti.Huber.restrictedReductionLift`:
  universe-polymorphic lifts of compatible families `R →+* (A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` from an
  arbitrary `NonAssocSemiring R`.
* `Ideal.mvPolynomialQuotientPowSuccDiagram`: the diagram `n ↦ (A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` in
  `CommRingCat`.
* `TauCeti.Huber.isLimitRestrictedReductionCompletionPowSuccCone` and
  `TauCeti.Huber.isLimitRestrictedReductionPowSuccCone`: limit witnesses for the cones of
  polynomial reductions.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.1–7.5.4.
* N. Bourbaki, *Commutative Algebra*, Ch. III, §2, no. 11–12.
-/

open CategoryTheory Limits Opposite Topology UniformSpace

public section

namespace TauCeti.Huber

section AdicCompletionEquiv

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

/-- For a finitely generated ideal of definition `I` of `A`, the separated uniform completion
`restrictedMvPowerSeriesCompletion k A` is isomorphic as an `A`-algebra to the algebraic adic
completion of the uncompleted restricted-series subring along `I`. -/
noncomputable def restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    restrictedMvPowerSeriesCompletion k A ≃ₐ[A]
      AdicCompletion
        (I.map (algebraMap A (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
          isWeightFamily_one_weight)))
        (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) := by
  let S := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  have hadic : IsAdic (I.map (algebraMap A S)) :=
    isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg
  refine AlgEquiv.ofRingEquiv (f := hadic.completionEquivAdicCompletion (hfg.map _)) fun a ↦ ?_
  rw [Completion.algebraMap_def, IsAdic.completionEquivAdicCompletion_coe]
  exact (IsScalarTower.algebraMap_apply A S _ a).symm

/-- `restrictedMvPowerSeriesCompletionEquivAdicCompletion` extends the canonical `algebraMap` from
the uncompleted restricted-series subring into its adic completion. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_coe
    (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg
        (f : restrictedMvPowerSeriesCompletion k A) =
      algebraMap _ _ f :=
  IsAdic.completionEquivAdicCompletion_coe
    (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg) (hfg.map _) f

/-- The inverse of `restrictedMvPowerSeriesCompletionEquivAdicCompletion` sends the canonical image
of a restricted series in the adic completion to its image in the uniform completion. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_symm_algebraMap
    (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg).symm (algebraMap _ _ f) =
      (f : restrictedMvPowerSeriesCompletion k A) :=
  IsAdic.completionEquivAdicCompletion_symm_algebraMap
    (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg) (hfg.map _) f

/-- `restrictedMvPowerSeriesCompletionEquivAdicCompletion` is a homeomorphism when the adic
completion carries the adic topology of the extended ideal. -/
theorem isHomeomorph_restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    let S := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
    let J := I.map (algebraMap A S)
    @IsHomeomorph _ _ _ (J.map (algebraMap S (AdicCompletion J S))).adicTopology
      (restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg) :=
  IsAdic.isHomeomorph_completionEquivAdicCompletion
    (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg) (hfg.map _)

end AdicCompletionEquiv

section UniversalLift

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {R : Type*} [NonAssocSemiring R] {k : ℕ} {I : Ideal A}

open Ideal (restrictedReduction restrictedReductionCompletion)

private theorem factorPow_comp_completionFamily
    (hI : IsAdic I) (hfg : I.FG)
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) {m : ℕ} :
    (Ideal.Quotient.factorPow
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
      (Nat.succ_le_succ m.le_succ)).comp
      ((quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
        (m + 1 + 1)).symm.toRingEquiv.toRingHom.comp (g (m + 1))) =
      (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
        (m + 1)).symm.toRingEquiv.toRingHom.comp (g m) := by
  ext r
  apply (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)).injective
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv]
  rw [← map_factorPow_quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg
    (Nat.succ_le_succ m.le_succ), AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact RingHom.congr_fun hg r

/-- A compatible family of ring homomorphisms `R →+* (A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` lifts to a
ring homomorphism `R →+* restrictedMvPowerSeriesCompletion k A`, with no completeness assumption
on `A` and no universe restriction on `R`. -/
noncomputable def restrictedReductionCompletionLift
    (hI : IsAdic I) (hfg : I.FG)
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) :
    R →+* restrictedMvPowerSeriesCompletion k A :=
  have := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion (k := k) hI hfg
  IsAdicComplete.StrictMono.liftRingHom (a := (· + 1))
    (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
    (strictMono_id.add_const 1)
    (fun n ↦ (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
      (n + 1)).symm.toRingEquiv.toRingHom.comp (g n))
    (factorPow_comp_completionFamily hI hfg g hg)

/-- Applying `restrictedReductionCompletion` modulo `I ^ (n + 1)` to
`restrictedReductionCompletionLift` at `r` recovers `g n r`. -/
@[simp]
theorem restrictedReductionCompletion_restrictedReductionCompletionLift
    (hI : IsAdic I) (hfg : I.FG)
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) (n : ℕ) (r : R) :
    restrictedReductionCompletion (I ^ (n + 1)) (hI.isOpen_pow (n + 1))
      (restrictedReductionCompletionLift hI hfg g hg r) = g n r := by
  have := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion (k := k) hI hfg
  rw [← quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk hI hfg]
  have hmk := IsAdicComplete.StrictMono.mk_liftRingHom (a := (· + 1))
    (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
    (strictMono_id.add_const 1)
    (fun n ↦ (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
      (n + 1)).symm.toRingEquiv.toRingHom.comp (g n))
    (factorPow_comp_completionFamily hI hfg g hg) (n := n) r
  dsimp only [restrictedReductionCompletionLift]
  rw [hmk]
  simp

/-- Composing `restrictedReductionCompletion` modulo `I ^ (n + 1)` with
`restrictedReductionCompletionLift` recovers `g n`. -/
@[simp]
theorem restrictedReductionCompletion_comp_restrictedReductionCompletionLift
    (hI : IsAdic I) (hfg : I.FG)
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) (n : ℕ) :
    (restrictedReductionCompletion (I ^ (n + 1)) (hI.isOpen_pow (n + 1))).comp
      (restrictedReductionCompletionLift hI hfg g hg) = g n :=
  RingHom.ext (restrictedReductionCompletion_restrictedReductionCompletionLift hI hfg g hg n)

/-- A ring homomorphism into `restrictedMvPowerSeriesCompletion k A` is uniquely determined by its
polynomial reductions modulo `I ^ (n + 1)`. -/
theorem eq_restrictedReductionCompletionLift
    (hI : IsAdic I) (hfg : I.FG)
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m)
    {F : R →+* restrictedMvPowerSeriesCompletion k A}
    (hF : ∀ n, (restrictedReductionCompletion (I ^ (n + 1)) (hI.isOpen_pow (n + 1))).comp F =
      g n) :
    F = restrictedReductionCompletionLift hI hfg g hg := by
  have := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion (k := k) hI hfg
  refine IsAdicComplete.StrictMono.eq_liftRingHom (a := (· + 1)) _
    (strictMono_id.add_const 1) _
    (factorPow_comp_completionFamily hI hfg g hg) fun n ↦ ?_
  ext r
  apply (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (n + 1)).injective
  simpa only [RingHom.comp_apply, quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.apply_symm_apply] using RingHom.congr_fun (hF n) r

/-- **Universal property of `A⟨X₁, …, Xₖ⟩` as an inverse limit of polynomial algebras.** -/
theorem existsUnique_ringHom_restrictedReductionCompletion
    (hI : IsAdic I) (hfg : I.FG)
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) :
    ∃! F : R →+* restrictedMvPowerSeriesCompletion k A,
      ∀ n, (restrictedReductionCompletion (I ^ (n + 1)) (hI.isOpen_pow (n + 1))).comp F = g n :=
  ⟨restrictedReductionCompletionLift hI hfg g hg,
    restrictedReductionCompletion_comp_restrictedReductionCompletionLift hI hfg g hg,
    fun _ hF ↦ eq_restrictedReductionCompletionLift hI hfg g hg hF⟩

/-- When `A` is `I`-adically complete, a compatible family of ring homomorphisms
`R →+* (A ⧸ I ^ (n + 1))[X₁, …, Xₖ]` lifts to the uncompleted restricted power-series subring. -/
noncomputable def restrictedReductionLift
    (hI : IsAdic I) (hfg : I.FG) [IsAdicComplete I A]
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) :
    R →+* weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  have := completeSpace_weightedRestrictedSubring_one_weight_of_isPrecomplete (k := k) hI
  have := t2Space_weightedRestrictedSubring_one_weight_of_isHausdorff (k := k) hI
  (restrictedMvPowerSeriesCompletionEquiv k A).toRingHom.comp
    (restrictedReductionCompletionLift hI hfg g hg)

/-- Applying `restrictedReduction` modulo `I ^ (n + 1)` to `restrictedReductionLift` at `r`
recovers `g n r`. -/
@[simp]
theorem restrictedReduction_restrictedReductionLift
    (hI : IsAdic I) (hfg : I.FG) [IsAdicComplete I A]
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) (n : ℕ) (r : R) :
    restrictedReduction (I ^ (n + 1)) (hI.isOpen_pow (n + 1))
      (restrictedReductionLift hI hfg g hg r) = g n r := by
  have := completeSpace_weightedRestrictedSubring_one_weight_of_isPrecomplete (k := k) hI
  have := t2Space_weightedRestrictedSubring_one_weight_of_isHausdorff (k := k) hI
  simp [restrictedReductionLift]

/-- Composing `restrictedReduction` modulo `I ^ (n + 1)` with `restrictedReductionLift` recovers
`g n`. -/
@[simp]
theorem restrictedReduction_comp_restrictedReductionLift
    (hI : IsAdic I) (hfg : I.FG) [IsAdicComplete I A]
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) (n : ℕ) :
    (restrictedReduction (I ^ (n + 1)) (hI.isOpen_pow (n + 1))).comp
      (restrictedReductionLift hI hfg g hg) = g n :=
  RingHom.ext (restrictedReduction_restrictedReductionLift hI hfg g hg n)

/-- Over an `I`-adically complete base, a ring homomorphism into the uncompleted restricted
power-series subring is uniquely determined by its polynomial reductions modulo `I ^ (n + 1)`. -/
theorem eq_restrictedReductionLift
    (hI : IsAdic I) (hfg : I.FG) [IsAdicComplete I A]
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m)
    {F : R →+* weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight}
    (hF : ∀ n, (restrictedReduction (I ^ (n + 1)) (hI.isOpen_pow (n + 1))).comp F = g n) :
    F = restrictedReductionLift hI hfg g hg := by
  have := completeSpace_weightedRestrictedSubring_one_weight_of_isPrecomplete (k := k) hI
  have := t2Space_weightedRestrictedSubring_one_weight_of_isHausdorff (k := k) hI
  have hFc : (restrictedMvPowerSeriesCompletionEquiv k A).symm.toRingHom.comp F =
      restrictedReductionCompletionLift hI hfg g hg :=
    eq_restrictedReductionCompletionLift hI hfg g hg fun n ↦ RingHom.ext fun r ↦ by
      simpa using RingHom.congr_fun (hF n) r
  refine RingHom.ext fun r ↦ ?_
  simpa [restrictedReductionLift] using
    congrArg (restrictedMvPowerSeriesCompletionEquiv k A) (RingHom.congr_fun hFc r)

/-- **Universal property of uncompleted restricted power series over an adically complete ring as
an inverse limit of polynomial algebras.** -/
theorem existsUnique_ringHom_restrictedReduction
    (hI : IsAdic I) (hfg : I.FG) [IsAdicComplete I A]
    (g : ∀ n, R →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hg : ∀ {m}, (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPowSucc I (m + 1))).comp (g (m + 1)) = g m) :
    ∃! F : R →+* weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight,
      ∀ n, (restrictedReduction (I ^ (n + 1)) (hI.isOpen_pow (n + 1))).comp F = g n :=
  ⟨restrictedReductionLift hI hfg g hg,
    restrictedReduction_comp_restrictedReductionLift hI hfg g hg,
    fun _ hF ↦ eq_restrictedReductionLift hI hfg g hg hF⟩

end UniversalLift

end TauCeti.Huber

end

@[expose] public section

universe u

namespace Ideal

/-- The inverse system `(A ⧸ I)[X₁, …, Xₖ] ← (A ⧸ I ^ 2)[X₁, …, Xₖ] ← ⋯` of polynomial algebras
over the infinitesimal thickenings of `A ⧸ I` in `CommRingCat`. -/
@[simps]
noncomputable def mvPolynomialQuotientPowSuccDiagram {A : Type u} [CommRing A] (k : ℕ)
    (I : Ideal A) : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (MvPolynomial (Fin k) (A ⧸ I ^ (n.unop + 1)))
  map f := CommRingCat.ofHom
    (MvPolynomial.map (σ := Fin k)
      (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f.unop))))
  map_id _ := by
    apply CommRingCat.hom_ext
    ext x <;> simp [Ideal.Quotient.factorPow]
  map_comp _ _ := by
    apply CommRingCat.hom_ext
    ext x <;> simp [Ideal.Quotient.factorPow]

end Ideal

namespace TauCeti.Huber

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

/-- The cone over `Ideal.mvPolynomialQuotientPowSuccDiagram k I` with apex
`restrictedMvPowerSeriesCompletion k A` and projections `Ideal.restrictedReductionCompletion`. -/
@[simps]
noncomputable def restrictedReductionCompletionPowSuccCone (hI : IsAdic I) :
    Cone (Ideal.mvPolynomialQuotientPowSuccDiagram k I) where
  pt := CommRingCat.of (restrictedMvPowerSeriesCompletion k A)
  π.app n := CommRingCat.ofHom
    (Ideal.restrictedReductionCompletion (I ^ (n.unop + 1)) (hI.isOpen_pow (n.unop + 1)))
  π.naturality _ _ f := by
    ext x
    exact (map_restrictedReductionCompletion (hI.isOpen_pow _) (hI.isOpen_pow _)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm

/-- The cone over `Ideal.mvPolynomialQuotientPowSuccDiagram k I` with apex the uncompleted
restricted power-series subring and projections `Ideal.restrictedReduction`. -/
@[simps]
noncomputable def restrictedReductionPowSuccCone (hI : IsAdic I) :
    Cone (Ideal.mvPolynomialQuotientPowSuccDiagram k I) where
  pt := CommRingCat.of
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
  π.app n := CommRingCat.ofHom
    (Ideal.restrictedReduction (I ^ (n.unop + 1)) (hI.isOpen_pow (n.unop + 1)))
  π.naturality _ _ f := by
    ext x
    exact (map_restrictedReduction (hI.isOpen_pow _) (hI.isOpen_pow _)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm

end TauCeti.Huber

end

public section

namespace TauCeti.Huber

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

private noncomputable def mvPolynomialQuotientPowSuccDiagramIso
    (hI : IsAdic I) (hfg : I.FG) :
    Ideal.quotientPowSuccDiagram
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ≅
      Ideal.mvPolynomialQuotientPowSuccDiagram k I :=
  NatIso.ofComponents
    (fun n ↦ (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
      (n.unop + 1)).toRingEquiv.toCommRingCatIso)
    fun f ↦ by
      ext z
      exact (map_factorPow_quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg
        (Nat.succ_le_succ (leOfHom f.unop)) z).symm

/-- For a finitely generated ideal of definition `I` of `A` (without assuming `A` complete or
Hausdorff), `restrictedMvPowerSeriesCompletion k A` is the limit in `CommRingCat` of the polynomial
algebras `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitRestrictedReductionCompletionPowSuccCone
    (hI : IsAdic I) (hfg : I.FG) :
    IsLimit (restrictedReductionCompletionPowSuccCone (k := k) hI) :=
  have := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion (k := k) hI hfg
  IsLimit.ofIsoLimit
    ((IsLimit.postcomposeHomEquiv (mvPolynomialQuotientPowSuccDiagramIso (k := k) hI hfg) _).symm
      (IsAdicComplete.isLimitQuotientPowSuccCone _))
    (Cone.ext (Iso.refl _) fun _ ↦ CommRingCat.hom_ext <| RingHom.ext fun x ↦
      quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk hI hfg x)

/-- When `A` is `I`-adically complete for a finitely generated ideal of definition `I`, the
uncompleted restricted power-series subring is the limit in `CommRingCat` of the polynomial
algebras `(A ⧸ I ^ (n + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitRestrictedReductionPowSuccCone
    (hI : IsAdic I) (hfg : I.FG) [IsAdicComplete I A] :
    IsLimit (restrictedReductionPowSuccCone (k := k) hI) :=
  have := completeSpace_weightedRestrictedSubring_one_weight_of_isPrecomplete (k := k) hI
  have := t2Space_weightedRestrictedSubring_one_weight_of_isHausdorff (k := k) hI
  IsLimit.ofIsoLimit (isLimitRestrictedReductionCompletionPowSuccCone (k := k) hI hfg)
    (Cone.ext (restrictedMvPowerSeriesCompletionEquiv k A).toCommRingCatIso fun _ ↦
      CommRingCat.hom_ext <| RingHom.ext fun x ↦
        (Ideal.restrictedReduction_restrictedMvPowerSeriesCompletionEquiv _ _ x).symm)

end TauCeti.Huber

end
