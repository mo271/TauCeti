/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Comparison
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Quotient

/-!
# Coefficientwise kernels and bounded lifts on compared Huber series carriers

Through the unit-radius and unit-weight Gauss comparisons of
`TauCeti.RingTheory.Huber.Restricted.GaussNorm` and
`TauCeti.RingTheory.Huber.Restricted.Comparison`, the quantitative lift bounds, sharp lifts,
coefficientwise kernel formulas, and extended-ideal characterizations of
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Quotient` transport directly to Huber's topological
restricted-series rings and their completions.

Specifically:
* For weights given by norm-multiplicative units `uᵢ ∈ Rˣ` and `vᵢ ∈ Sˣ` encoding the same positive
  radii `cᵢ`, `weightedMap` commutes with `weightedRestrictedGaussAlgEquiv`, so bounded, sharp, and
  exact coefficient lifts produce lifts in `weightedRestrictedSubring` satisfying the corresponding
  Gauss-norm bounds, and ideals `I` with uniformly bounded finite generators satisfy
  `f ∈ I · R⟨X⟩_u ↔ ∀ ν, coeff ν f ∈ I`.
* At the trivial weight `{1}`, the same quantitative lift bounds and extended-ideal membership hold
  both on `weightedRestrictedSubring` and, over complete coefficient rings, on the completed Huber
  carrier `restrictedMvPowerSeriesCompletion k R`, where coefficients and norms are read through
  `restrictedMvPowerSeriesCompletionGaussEquiv`.
* Under uniformly bounded coefficient lifts, the quotient of `restrictedMvPowerSeriesCompletion k R`
  by the kernel of `weightedMapCompletion` is topologically isomorphic to
  `restrictedMvPowerSeriesCompletion k S` (`weightedMapCompletionQuotientEquiv`), compatibly with
  `restrictedMapQuotientEquiv`.

## Main definitions

* `TauCeti.Huber.weightedMapCompletionQuotientEquiv`: the ring isomorphism
  `restrictedMvPowerSeriesCompletion k R ⧸ ker (weightedMapCompletion ...) ≃+*
    restrictedMvPowerSeriesCompletion k S` for a bounded coefficient map with uniformly bounded
  lifts, continuous in both directions.
* `Ideal.restrictedMvPowerSeriesCompletionQuotientEquiv`: the topological ring isomorphism
  `restrictedMvPowerSeriesCompletion k R ⧸ (I · R⟨X⟩) ≃+*
    restrictedMvPowerSeriesCompletion k (R ⧸ I)` for a closed ideal `I` with uniformly bounded
  finite generators.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.1.1, 5.2.7.
* T. Wedhorn, *Adic Spaces*, §5.6.
-/

public section

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

section UnitWeight

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {φ : R →+* S} {C : ℝ}
  (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
  (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
  (v : Fin k → Sˣ) (hv : ∀ i, IsNormMulUnit (v i : S))
  {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1) (hc' : ∀ i, ‖(v i : S)‖ * c i = 1)
  (hTS : ∀ i, φ '' {(u i : R)} ⊆ {(v i : S)})

/-- **Naturality of the unit-weight Gauss comparison.** For unit weights `u` on `R` and `v` on `S`
encoding the same radii `c`, `weightedMap` corresponds to `restrictedMap` under
`weightedRestrictedGaussAlgEquiv`. -/
theorem weightedRestrictedGaussAlgEquiv_weightedMap
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedRestrictedGaussAlgEquiv v hv hc'
        (weightedMap hφc (isWeightFamily_units u) (isWeightFamily_units v) hTS f) =
      restrictedMap φ hφ (weightedRestrictedGaussAlgEquiv u hu hc f) := by
  apply Subtype.ext
  simp only [coe_weightedRestrictedGaussAlgEquiv, coe_weightedMap, coe_restrictedMap]

variable [∀ i, Fact (0 < c i)]

include hφ in
/-- Uniformly bounded coefficient lifts give Gauss-bounded lifts on unit-weight Huber series. -/
theorem exists_weightedMap_units_eq_and_norm_le {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (g : weightedRestrictedSubring (fun i ↦ ({(v i : S)} : Set S)) (isWeightFamily_units v)) :
    ∃ f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u),
      weightedMap hφc (isWeightFamily_units u) (isWeightFamily_units v) hTS f = g ∧
        ‖weightedRestrictedGaussAlgEquiv u hu hc f‖ ≤
          L * ‖weightedRestrictedGaussAlgEquiv v hv hc' g‖ := by
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_le φ hφ hlift
    (weightedRestrictedGaussAlgEquiv v hv hc' g)
  refine ⟨(weightedRestrictedGaussAlgEquiv u hu hc).symm f₀, ?_, by simpa using hfn⟩
  apply (weightedRestrictedGaussAlgEquiv v hv hc').injective
  rw [weightedRestrictedGaussAlgEquiv_weightedMap hφc hφ u hu v hv hc hc' hTS,
    AlgEquiv.apply_symm_apply, hf₀]

include hφ in
/-- Sharp coefficient lifts give sharp Gauss-norm lifts on unit-weight Huber series. -/
theorem exists_weightedMap_units_eq_and_norm_lt
    (hsharp : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ < ‖b‖ + ε)
    (g : weightedRestrictedSubring (fun i ↦ ({(v i : S)} : Set S)) (isWeightFamily_units v))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u),
      weightedMap hφc (isWeightFamily_units u) (isWeightFamily_units v) hTS f = g ∧
        ‖weightedRestrictedGaussAlgEquiv u hu hc f‖ <
          ‖weightedRestrictedGaussAlgEquiv v hv hc' g‖ + ε := by
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_lt φ hφ hsharp
    (weightedRestrictedGaussAlgEquiv v hv hc' g) hε
  refine ⟨(weightedRestrictedGaussAlgEquiv u hu hc).symm f₀, ?_, by simpa using hfn⟩
  apply (weightedRestrictedGaussAlgEquiv v hv hc').injective
  rw [weightedRestrictedGaussAlgEquiv_weightedMap hφc hφ u hu v hv hc hc' hTS,
    AlgEquiv.apply_symm_apply, hf₀]

/-- Exact coefficient lifts (`‖a‖ ≤ ‖b‖`) under contractive `φ` give exact Gauss-norm lifts on
unit-weight Huber series. -/
theorem exists_weightedMap_units_eq_and_norm_eq (hφ₁ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (hlift₁ : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖)
    (g : weightedRestrictedSubring (fun i ↦ ({(v i : S)} : Set S)) (isWeightFamily_units v)) :
    ∃ f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u),
      weightedMap hφc (isWeightFamily_units u) (isWeightFamily_units v) hTS f = g ∧
        ‖weightedRestrictedGaussAlgEquiv u hu hc f‖ =
          ‖weightedRestrictedGaussAlgEquiv v hv hc' g‖ := by
  have hφ' : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖ := fun r ↦ by rw [one_mul]; exact hφ₁ r
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_eq φ hφ' hφ₁ hlift₁
    (weightedRestrictedGaussAlgEquiv v hv hc' g)
  refine ⟨(weightedRestrictedGaussAlgEquiv u hu hc).symm f₀, ?_, by simpa using hfn⟩
  apply (weightedRestrictedGaussAlgEquiv v hv hc').injective
  rw [weightedRestrictedGaussAlgEquiv_weightedMap hφc hφ' u hu v hv hc hc' hTS,
    AlgEquiv.apply_symm_apply, hf₀]

end UnitWeight

section OneWeight

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {φ : R →+* S} {C : ℝ}
  (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

include hφ in
/-- Uniformly bounded coefficient lifts give Gauss-bounded lifts on trivial-weight Huber series. -/
theorem exists_weightedMap_one_weight_eq_and_norm_le {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight) :
    ∃ f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight,
      weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f = g ∧
        ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ L * ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_le φ hφ hlift
    (restrictedMvPowerSeriesGaussEquiv g)
  refine ⟨restrictedMvPowerSeriesGaussEquiv.symm f₀, ?_, by simpa using hfn⟩
  apply restrictedMvPowerSeriesGaussEquiv.injective
  rw [restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ,
    RingEquiv.apply_symm_apply, hf₀]

include hφ in
/-- Sharp coefficient lifts give sharp Gauss-norm lifts on trivial-weight Huber series. -/
theorem exists_weightedMap_one_weight_eq_and_norm_lt
    (hsharp : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ < ‖b‖ + ε)
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight,
      weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f = g ∧
        ‖restrictedMvPowerSeriesGaussEquiv f‖ < ‖restrictedMvPowerSeriesGaussEquiv g‖ + ε := by
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_lt φ hφ hsharp
    (restrictedMvPowerSeriesGaussEquiv g) hε
  refine ⟨restrictedMvPowerSeriesGaussEquiv.symm f₀, ?_, by simpa using hfn⟩
  apply restrictedMvPowerSeriesGaussEquiv.injective
  rw [restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ,
    RingEquiv.apply_symm_apply, hf₀]

/-- Exact coefficient lifts (`‖a‖ ≤ ‖b‖`) under contractive `φ` give exact Gauss-norm lifts on
trivial-weight Huber series. -/
theorem exists_weightedMap_one_weight_eq_and_norm_eq (hφ₁ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (hlift₁ : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖)
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight) :
    ∃ f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight,
      weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f = g ∧
        ‖restrictedMvPowerSeriesGaussEquiv f‖ = ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
  have hφ' : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖ := fun r ↦ by rw [one_mul]; exact hφ₁ r
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_eq φ hφ' hφ₁ hlift₁
    (restrictedMvPowerSeriesGaussEquiv g)
  refine ⟨restrictedMvPowerSeriesGaussEquiv.symm f₀, ?_, by simpa using hfn⟩
  apply restrictedMvPowerSeriesGaussEquiv.injective
  rw [restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ',
    RingEquiv.apply_symm_apply, hf₀]

end OneWeight

section Completion

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] {φ : R →+* S} {C : ℝ}
  (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

include hφ in
/-- **Coefficientwise kernel on the completed Huber carrier.** An element `f` of
`restrictedMvPowerSeriesCompletion k R` lies in `ker (weightedMapCompletion ...)` if and only if
every coefficient of `restrictedMvPowerSeriesCompletionGaussEquiv f` lies in `ker φ`. -/
theorem mem_ker_weightedMapCompletion_iff (f : restrictedMvPowerSeriesCompletion k R) :
    f ∈ RingHom.ker (weightedMapCompletion hφc isWeightFamily_one_weight
        isWeightFamily_one_weight (by simp)) ↔
      ∀ ν, coeff ν (restrictedMvPowerSeriesCompletionGaussEquiv f :
        MvPowerSeries (Fin k) R) ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker, ← map_eq_zero_iff restrictedMvPowerSeriesCompletionGaussEquiv
      restrictedMvPowerSeriesCompletionGaussEquiv.injective,
    restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ,
    ← RingHom.mem_ker, mem_ker_restrictedMap]

include hφ in
/-- An injective bounded coefficient homomorphism induces an injection on completed Huber
restricted-series rings. -/
theorem weightedMapCompletion_injective (hφinj : Function.Injective φ) :
    Function.Injective (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
      isWeightFamily_one_weight (by simp)) := by
  intro f g hfg
  apply restrictedMvPowerSeriesCompletionGaussEquiv.injective
  apply restrictedMap_injective φ hφ hφinj
  simpa only [← restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ] using
    congrArg restrictedMvPowerSeriesCompletionGaussEquiv hfg

include hφ in
/-- **Bounded lifts on the completed Huber carrier.** Uniformly bounded coefficient lifts produce
lifts along `weightedMapCompletion` obeying the same bound in the compared Gauss norms. -/
theorem exists_weightedMapCompletion_eq_and_norm_le {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (g : restrictedMvPowerSeriesCompletion k S) :
    ∃ f : restrictedMvPowerSeriesCompletion k R,
      weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f = g ∧
        ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ ≤
          L * ‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ := by
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_le φ hφ hlift
    (restrictedMvPowerSeriesCompletionGaussEquiv g)
  refine ⟨restrictedMvPowerSeriesCompletionGaussEquiv.symm f₀, ?_, by simpa using hfn⟩
  apply restrictedMvPowerSeriesCompletionGaussEquiv.injective
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ,
    RingEquiv.apply_symm_apply, hf₀]

include hφ in
/-- **Sharp lifts on the completed Huber carrier.** Sharp coefficient lifts produce lifts along
`weightedMapCompletion` with Gauss norm within `ε` of the target Gauss norm. -/
theorem exists_weightedMapCompletion_eq_and_norm_lt
    (hsharp : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ < ‖b‖ + ε)
    (g : restrictedMvPowerSeriesCompletion k S) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : restrictedMvPowerSeriesCompletion k R,
      weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f = g ∧
        ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ <
          ‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ + ε := by
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_lt φ hφ hsharp
    (restrictedMvPowerSeriesCompletionGaussEquiv g) hε
  refine ⟨restrictedMvPowerSeriesCompletionGaussEquiv.symm f₀, ?_, by simpa using hfn⟩
  apply restrictedMvPowerSeriesCompletionGaussEquiv.injective
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ,
    RingEquiv.apply_symm_apply, hf₀]

/-- **Exact Gauss-norm lifts on the completed Huber carrier.** When `φ` is contractive and every
`b : S` lifts with `‖a‖ ≤ ‖b‖`, every element of `restrictedMvPowerSeriesCompletion k S` lifts
along `weightedMapCompletion` with exact equality of compared Gauss norms. -/
theorem exists_weightedMapCompletion_eq_and_norm_eq (hφ₁ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (hlift₁ : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖)
    (g : restrictedMvPowerSeriesCompletion k S) :
    ∃ f : restrictedMvPowerSeriesCompletion k R,
      weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f = g ∧
        ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ =
          ‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ := by
  have hφ' : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖ := fun r ↦ by rw [one_mul]; exact hφ₁ r
  obtain ⟨f₀, hf₀, hfn⟩ := exists_restrictedMap_eq_and_norm_eq φ hφ' hφ₁ hlift₁
    (restrictedMvPowerSeriesCompletionGaussEquiv g)
  refine ⟨restrictedMvPowerSeriesCompletionGaussEquiv.symm f₀, ?_, by simpa using hfn⟩
  apply restrictedMvPowerSeriesCompletionGaussEquiv.injective
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ',
    RingEquiv.apply_symm_apply, hf₀]

include hφ in
/-- Uniformly bounded coefficient lifts make `weightedMapCompletion` surjective on completed Huber
restricted-series rings. -/
theorem weightedMapCompletion_surjective_of_exists_norm_le {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    Function.Surjective (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
      isWeightFamily_one_weight (by simp)) := by
  intro g
  obtain ⟨f, hf, -⟩ := exists_weightedMapCompletion_eq_and_norm_le hφc hφ hlift g
  exact ⟨f, hf⟩

/-- **Quotient ring isomorphism on completed Huber carriers** induced by a bounded coefficient map
with uniformly bounded lifts. -/
noncomputable def weightedMapCompletionQuotientEquiv {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    (restrictedMvPowerSeriesCompletion k R ⧸
        RingHom.ker (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
          isWeightFamily_one_weight (by simp))) ≃+*
      restrictedMvPowerSeriesCompletion k S :=
  (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
    isWeightFamily_one_weight (by simp)).quotientKerEquivOfSurjective
    (weightedMapCompletion_surjective_of_exists_norm_le hφc hφ hlift)

/-- `weightedMapCompletionQuotientEquiv` acts as `weightedMapCompletion` on residue classes. -/
@[simp]
theorem weightedMapCompletionQuotientEquiv_mk {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) (f : restrictedMvPowerSeriesCompletion k R) :
    weightedMapCompletionQuotientEquiv hφc hφ hlift (Ideal.Quotient.mk _ f) =
      weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
        (by simp) f :=
  (rfl)

/-- The inverse of `weightedMapCompletionQuotientEquiv` sends `weightedMapCompletion ... f` to the
residue class of `f`. -/
@[simp]
theorem weightedMapCompletionQuotientEquiv_symm_weightedMapCompletion {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) (f : restrictedMvPowerSeriesCompletion k R) :
    (weightedMapCompletionQuotientEquiv hφc hφ hlift).symm
        (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f) =
      Ideal.Quotient.mk _ f :=
  RingHom.quotientKerEquivOfSurjective_symm_apply
    (weightedMapCompletion_surjective_of_exists_norm_le hφc hφ hlift) f

/-- `restrictedMvPowerSeriesCompletionGaussEquiv` maps `ker (weightedMapCompletion ...)` onto
`ker (restrictedMap φ hφ)`. -/
theorem map_ker_weightedMapCompletion :
    RingHom.ker (restrictedMap (c := fun _ : Fin k ↦ (1 : ℝ)) φ hφ) =
      (RingHom.ker (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
        isWeightFamily_one_weight (by simp))).map
        ((restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)) :
          restrictedMvPowerSeriesCompletion k R →+* _) := by
  rw [Ideal.map_comap_of_equiv]
  ext g
  simp only [Ideal.mem_comap, mem_ker_restrictedMap,
    mem_ker_weightedMapCompletion_iff hφc hφ, RingEquiv.apply_symm_apply]

/-- `weightedMapCompletionQuotientEquiv` commutes with `restrictedMapQuotientEquiv` under the
completed Gauss comparison. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletionQuotientEquiv {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (x : restrictedMvPowerSeriesCompletion k R ⧸
      RingHom.ker (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
        isWeightFamily_one_weight (by simp))) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (weightedMapCompletionQuotientEquiv hφc hφ hlift x) =
      restrictedMapQuotientEquiv φ hφ hlift
        (Ideal.quotientEquiv _ _ restrictedMvPowerSeriesCompletionGaussEquiv
          (map_ker_weightedMapCompletion hφc hφ) x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [weightedMapCompletionQuotientEquiv_mk,
    restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ,
    Ideal.quotientEquiv_mk, restrictedMapQuotientEquiv_mk]

/-- `weightedMapCompletionQuotientEquiv` is continuous for the quotient and completion
topologies. -/
theorem continuous_weightedMapCompletionQuotientEquiv {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    Continuous (weightedMapCompletionQuotientEquiv (k := k) hφc hφ hlift) := by
  refine (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr ?_
  exact continuous_weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight _

/-- The inverse of `weightedMapCompletionQuotientEquiv` is continuous for the completion and
quotient topologies. -/
theorem continuous_weightedMapCompletionQuotientEquiv_symm {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖) :
    Continuous (weightedMapCompletionQuotientEquiv (k := k) hφc hφ hlift).symm := by
  -- Factor `(weightedMapCompletionQuotientEquiv ...).symm` through the Gauss-normed carriers:
  -- `S⟨X⟩ → S{X} → R{X} ⧸ ker → R⟨X⟩ ⧸ ker`.
  let qEquiv := Ideal.quotientEquiv _ _ restrictedMvPowerSeriesCompletionGaussEquiv
    (map_ker_weightedMapCompletion (k := k) hφc hφ)
  have hq_cont : Continuous qEquiv.symm := by
    refine (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr ?_
    have hcomp : ⇑qEquiv.symm ∘ ⇑(Ideal.Quotient.mk _) =
        ⇑(Ideal.Quotient.mk _) ∘ ⇑restrictedMvPowerSeriesCompletionGaussEquiv.symm := by
      ext g
      exact Ideal.quotientEquiv_symm_mk _ _ _ _ g
    rw [hcomp]
    exact (QuotientRing.isOpenQuotientMap_mk _).continuous.comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm
  have hfac : ⇑(weightedMapCompletionQuotientEquiv (k := k) hφc hφ hlift).symm =
      ⇑qEquiv.symm ∘ ⇑(restrictedMapQuotientEquiv φ hφ hlift).symm ∘
        ⇑(restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := S)) := by
    ext s
    obtain ⟨f, rfl⟩ := weightedMapCompletion_surjective_of_exists_norm_le hφc hφ hlift s
    rw [Function.comp_apply, Function.comp_apply,
      weightedMapCompletionQuotientEquiv_symm_weightedMapCompletion,
      restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ,
      restrictedMapQuotientEquiv_symm_restrictedMap, Ideal.quotientEquiv_symm_mk,
      RingEquiv.symm_apply_apply]
  rw [hfac]
  exact hq_cont.comp ((continuous_restrictedMapQuotientEquiv_symm φ hφ hlift).comp
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv)

end Completion

end TauCeti.Huber

namespace Ideal

open _root_.MvPowerSeries TauCeti TauCeti.MvPowerSeries TauCeti.Huber

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- **Extended ideals in unit-weight Huber series.** For `I : Ideal R` admitting uniformly bounded
finite generators and norm-multiplicative units `uᵢ` with `‖uᵢ‖ * cᵢ = 1`, a series in `R⟨X⟩_u`
lies in `I · R⟨X⟩_u` if and only if every coefficient lies in `I`. -/
theorem mem_map_weightedC_units_iff (I : Ideal R)
    (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
    {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1)
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖)
    {f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)} :
    f ∈ I.map (weightedC (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) ↔
      ∀ ν, coeff ν (f : MvPowerSeries (Fin k) R) ∈ I := by
  let e := weightedRestrictedGaussAlgEquiv u hu hc
  have hmap : (I.map (algebraMap R _)).map e.toRingEquiv = I.map (algebraMap R _) :=
    (I.map_map (algebraMap R _) e.toRingEquiv.toRingHom).trans
      (congrArg I.map (RingHom.ext e.commutes))
  rw [← algebraMap_weightedRestrictedSubring,
    ← Ideal.apply_mem_of_equiv_iff (f := e.toRingEquiv), hmap,
    mem_map_algebraMap_isRestricted_subring_iff_of_exists_finset_sum_mul I hFI hgen]
  simp only [AlgEquiv.coe_toRingEquiv, e, coe_weightedRestrictedGaussAlgEquiv]

/-- **Extended ideals in trivial-weight Huber series.** For `I : Ideal R` admitting uniformly
bounded finite generators, a series in `R⟨X⟩` lies in `I · R⟨X⟩` if and only if every coefficient
lies in `I`. -/
theorem mem_map_weightedC_one_weight_iff (I : Ideal R)
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight} :
    f ∈ I.map (weightedC (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) ↔
      ∀ ν, coeff ν (f : MvPowerSeries (Fin k) R) ∈ I := by
  let e := restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)
  have hmap : (I.map (algebraMap R _)).map e.toRingEquiv = I.map (algebraMap R _) :=
    (I.map_map (algebraMap R _) e.toRingEquiv.toRingHom).trans
      (congrArg I.map (RingHom.ext e.commutes))
  rw [← algebraMap_weightedRestrictedSubring,
    ← Ideal.apply_mem_of_equiv_iff (f := e.toRingEquiv), hmap,
    mem_map_algebraMap_isRestricted_subring_iff_of_exists_finset_sum_mul I hFI hgen]
  simp only [AlgEquiv.coe_toRingEquiv, e, coe_restrictedMvPowerSeriesGaussAlgEquiv,
    coe_restrictedMvPowerSeriesGaussEquiv]

section Complete

variable [CompleteSpace R]

/-- **Extended ideals in completed Huber series.** Over a complete base `R`, for `I : Ideal R`
with uniformly bounded finite generators, an element `f` of `restrictedMvPowerSeriesCompletion k R`
lies in `I · R⟨X⟩` if and only if every coefficient of
`restrictedMvPowerSeriesCompletionGaussEquiv f` lies in `I`. -/
theorem mem_map_algebraMap_restrictedMvPowerSeriesCompletion_iff (I : Ideal R)
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖)
    {f : restrictedMvPowerSeriesCompletion k R} :
    f ∈ I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R)) ↔
      ∀ ν, coeff ν (restrictedMvPowerSeriesCompletionGaussEquiv f :
        MvPowerSeries (Fin k) R) ∈ I := by
  let e := restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)
  have hmap : (I.map (algebraMap R _)).map e.toRingEquiv = I.map (algebraMap R _) :=
    (I.map_map (algebraMap R _) e.toRingEquiv.toRingHom).trans
      (congrArg I.map (RingHom.ext e.commutes))
  rw [← Ideal.apply_mem_of_equiv_iff (f := e.toRingEquiv), hmap,
    mem_map_algebraMap_isRestricted_subring_iff_of_exists_finset_sum_mul I hFI hgen]
  simp only [AlgEquiv.coe_toRingEquiv, e, coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv]

/-- For a closed ideal `I` of a complete ultrametric commutative ring `R` with uniformly bounded
finite generators, the kernel of `weightedMapCompletion` along `Ideal.Quotient.mk I : R →+* R ⧸ I`
is the extended ideal `I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R))`. -/
theorem ker_weightedMapCompletion_quotientMk_of_exists_finset_sum_mul
    (I : Ideal R) [IsClosed (I : Set R)]
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖) :
    RingHom.ker (weightedMapCompletion (k := k) (φ := Ideal.Quotient.mk I)
        (QuotientRing.isOpenQuotientMap_mk I).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (by simp)) =
      I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R)) := by
  ext f
  rw [mem_ker_weightedMapCompletion_iff (QuotientRing.isOpenQuotientMap_mk I).continuous
      (C := 1) (fun a ↦ by simpa only [one_mul] using Ideal.Quotient.norm_mk_le_norm I a),
    Ideal.mk_ker, mem_map_algebraMap_restrictedMvPowerSeriesCompletion_iff I hFI hgen]

/-- **Topological ring isomorphism
`restrictedMvPowerSeriesCompletion k R ⧸ (I · R⟨X⟩) ≃+*
  restrictedMvPowerSeriesCompletion k (R ⧸ I)`** for a closed ideal `I` with uniformly bounded
finite generators. -/
noncomputable def restrictedMvPowerSeriesCompletionQuotientEquiv
    (I : Ideal R) [IsClosed (I : Set R)]
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖) :
    (restrictedMvPowerSeriesCompletion k R ⧸
        I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R))) ≃+*
      restrictedMvPowerSeriesCompletion k (R ⧸ I) :=
  (Ideal.quotEquivOfEq
    (ker_weightedMapCompletion_quotientMk_of_exists_finset_sum_mul I hFI hgen).symm).trans
    (weightedMapCompletionQuotientEquiv
      (QuotientRing.isOpenQuotientMap_mk I).continuous
      (C := 1) (fun a ↦ by simpa only [one_mul] using Ideal.Quotient.norm_mk_le_norm I a)
      (exists_norm_le_of_forall_pos_lt_add (Ideal.Quotient.mk I)
        (fun x _ hε ↦ Ideal.Quotient.exists_norm_mk_lt x hε) one_lt_two))

/-- `Ideal.restrictedMvPowerSeriesCompletionQuotientEquiv` acts as `weightedMapCompletion` on
residue classes. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionQuotientEquiv_mk
    (I : Ideal R) [IsClosed (I : Set R)]
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖)
    (f : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesCompletionQuotientEquiv I hFI hgen (Ideal.Quotient.mk _ f) =
      weightedMapCompletion (φ := Ideal.Quotient.mk I)
        (QuotientRing.isOpenQuotientMap_mk I).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f :=
  (rfl)

/-- `Ideal.restrictedMvPowerSeriesCompletionQuotientEquiv` is continuous. -/
theorem continuous_restrictedMvPowerSeriesCompletionQuotientEquiv
    (I : Ideal R) [IsClosed (I : Set R)]
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖) :
    Continuous (restrictedMvPowerSeriesCompletionQuotientEquiv (k := k) I hFI hgen) := by
  refine (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr ?_
  have hcomp : ⇑(restrictedMvPowerSeriesCompletionQuotientEquiv (k := k) I hFI hgen) ∘
      ⇑(Ideal.Quotient.mk _) =
      ⇑(weightedMapCompletion (k := k) (φ := Ideal.Quotient.mk I)
        (QuotientRing.isOpenQuotientMap_mk I).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (by simp)) := by
    ext f
    exact restrictedMvPowerSeriesCompletionQuotientEquiv_mk I hFI hgen f
  rw [hcomp]
  exact continuous_weightedMapCompletion (QuotientRing.isOpenQuotientMap_mk I).continuous
    isWeightFamily_one_weight isWeightFamily_one_weight _

/-- The inverse of `Ideal.restrictedMvPowerSeriesCompletionQuotientEquiv` is continuous. -/
theorem continuous_restrictedMvPowerSeriesCompletionQuotientEquiv_symm
    (I : Ideal R) [IsClosed (I : Set R)]
    {F : Finset R} (hFI : ∀ x ∈ F, x ∈ I) {L : ℝ}
    (hgen : ∀ y ∈ I, ∃ a : R → R, y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖) :
    Continuous (restrictedMvPowerSeriesCompletionQuotientEquiv (k := k) I hFI hgen).symm := by
  let hEq := ker_weightedMapCompletion_quotientMk_of_exists_finset_sum_mul (k := k) I hFI hgen
  have hcont_eq : Continuous (Ideal.quotEquivOfEq hEq) := by
    refine (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr ?_
    have hcomp : ⇑(Ideal.quotEquivOfEq hEq) ∘ ⇑(Ideal.Quotient.mk _) =
        ⇑(Ideal.Quotient.mk _) := by
      ext f
      exact Ideal.quotEquivOfEq_mk hEq f
    rw [hcomp]
    exact (QuotientRing.isOpenQuotientMap_mk _).continuous
  exact hcont_eq.comp (continuous_weightedMapCompletionQuotientEquiv_symm
    (QuotientRing.isOpenQuotientMap_mk I).continuous
    (C := 1) (fun a ↦ by simpa only [one_mul] using Ideal.Quotient.norm_mk_le_norm I a)
    (exists_norm_le_of_forall_pos_lt_add (Ideal.Quotient.mk I)
      (fun x _ hε ↦ Ideal.Quotient.exists_norm_mk_lt x hε) one_lt_two))

end Complete

end Ideal
