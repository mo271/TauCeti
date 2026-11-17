/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProductMeasure
public import TauCeti.InformationTheory.Hellinger.Basic

import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Probability.Independence.InfinitePi

/-!
# Hellinger affinity and squared Hellinger distance of product measures

The Hellinger affinity factorizes over binary products (`hellingerAffinity_prod`), finite
dependent products (`hellingerAffinity_pi`), and infinite products of probability measures that
agree outside a finite set of coordinates (`hellingerAffinity_infinitePi`). In particular, for an
i.i.d. product indexed by a finite type `ι`, the squared Hellinger distance satisfies
`sqHellinger (Measure.pi fun _ : ι ↦ P) (Measure.pi fun _ : ι ↦ Q) =`
`2 * (1 - (1 - sqHellinger P Q / 2) ^ Fintype.card ι)`.

## Main results

* `TauCeti.hellingerAffinity_prod`: factorization over binary products of σ-finite measures.
* `TauCeti.hellingerAffinity_pi`: factorization over finite products of σ-finite measures.
* `TauCeti.hellingerAffinity_pi_const`: affinity of a finite product power `P^ι` and `Q^ι`.
* `TauCeti.sqHellinger_pi_const`: squared Hellinger distance of a finite power of a measure.
* `TauCeti.hellingerAffinity_infinitePi`: factorization over infinite products of probability
  measures agreeing outside a finite index set.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Definition 2.3,
  property (iv), p. 83.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

/-- **Tensorization of the Hellinger affinity.** The Hellinger affinity of two binary product
measures of σ-finite measures is the product of the Hellinger affinities of their factors. -/
theorem hellingerAffinity_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P Q : Measure X) (P' Q' : Measure Y)
    [SigmaFinite P] [SigmaFinite Q] [SigmaFinite P'] [SigmaFinite Q'] :
    hellingerAffinity (P.prod P') (Q.prod Q') =
      hellingerAffinity P Q * hellingerAffinity P' Q' := by
  set ν := P + Q
  set ν' := P' + Q'
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hP'ν' : P' ≪ ν' := Measure.AbsolutelyContinuous.rfl.add_right Q'
  have hQ'ν' : Q' ≪ ν' := Measure.AbsolutelyContinuous.rfl.add_right' P'
  have hprod : ∀ (A : Measure X) (B : Measure Y) [SigmaFinite A] [SigmaFinite B],
      A ≪ ν → B ≪ ν' →
      A.prod B = (ν.prod ν').withDensity fun z ↦ A.rnDeriv ν z.1 * B.rnDeriv ν' z.2 := by
    intro A B _ _ hA hB
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq A ν hA,
      ← Measure.withDensity_rnDeriv_eq B ν' hB]
    exact prod_withDensity (μ := ν) (ν := ν')
      (Measure.measurable_rnDeriv A ν) (Measure.measurable_rnDeriv B ν')
  have hmeas : ∀ (A : Measure X) (B : Measure Y),
      AEMeasurable (fun z : X × Y ↦ A.rnDeriv ν z.1 * B.rnDeriv ν' z.2) (ν.prod ν') :=
    fun A B ↦ (((Measure.measurable_rnDeriv A ν).comp measurable_fst).mul
      ((Measure.measurable_rnDeriv B ν').comp measurable_snd)).aemeasurable
  have : SigmaFinite ((ν.prod ν').withDensity
      fun z ↦ P.rnDeriv ν z.1 * P'.rnDeriv ν' z.2) := by
    rw [← hprod P P' hPν hP'ν']; infer_instance
  have : SigmaFinite ((ν.prod ν').withDensity
      fun z ↦ Q.rnDeriv ν z.1 * Q'.rnDeriv ν' z.2) := by
    rw [← hprod Q Q' hQν hQ'ν']; infer_instance
  rw [hprod P P' hPν hP'ν', hprod Q Q' hQν hQ'ν',
    hellingerAffinity_withDensity (ν.prod ν') (hmeas P P') (hmeas Q Q')]
  have hpt : ∀ z : X × Y,
      √((P.rnDeriv ν z.1 * P'.rnDeriv ν' z.2).toReal *
          (Q.rnDeriv ν z.1 * Q'.rnDeriv ν' z.2).toReal) =
        √((P.rnDeriv ν z.1).toReal * (Q.rnDeriv ν z.1).toReal) *
          √((P'.rnDeriv ν' z.2).toReal * (Q'.rnDeriv ν' z.2).toReal) := fun z ↦ by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ← Real.sqrt_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
    congr 1; ring
  simp_rw [hpt]
  rw [integral_prod_mul (f := fun x ↦ √((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal))
      (g := fun y ↦ √((P'.rnDeriv ν' y).toReal * (Q'.rnDeriv ν' y).toReal)),
    hellingerAffinity_def, hellingerAffinity_def]

/-- **Factorization of the Hellinger affinity on finite products.** For any finite index type `ι`,
the Hellinger affinity of two finite product measures of σ-finite measures is the product of the
coordinate affinities. -/
theorem hellingerAffinity_pi.{u, v} {ι : Type u} [Fintype ι] {X : ι → Type v}
    [∀ i, MeasurableSpace (X i)] (P Q : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (P i)] [∀ i, SigmaFinite (Q i)] :
    hellingerAffinity (Measure.pi P) (Measure.pi Q) = ∏ i, hellingerAffinity (P i) (Q i) := by
  refine Fintype.induction_empty_option
    (P := fun ι _ ↦ ∀ {X : ι → Type v} [∀ i, MeasurableSpace (X i)] (P Q : ∀ i, Measure (X i))
      [∀ i, SigmaFinite (P i)] [∀ i, SigmaFinite (Q i)],
      hellingerAffinity (Measure.pi P) (Measure.pi Q) = ∏ i, hellingerAffinity (P i) (Q i))
    ?_ ?_ ?_ ι P Q
  · intro α β _ e ih X _ P Q _ _
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    let e_meas := MeasurableEquiv.piCongrLeft X e
    rw [← Measure.pi_map_piCongrLeft e P, ← Measure.pi_map_piCongrLeft e Q,
      e_meas.hellingerAffinity_map, ih (fun i ↦ P (e i)) (fun i ↦ Q (e i)),
      e.prod_comp (fun i ↦ hellingerAffinity (P i) (Q i))]
  · intro X _ P Q _ _
    rw [Measure.pi_of_empty P, Measure.pi_of_empty Q, hellingerAffinity_self,
      Measure.real_def, measure_univ, ENNReal.toReal_one, Fintype.prod_empty]
  · intro α _ ih X _ P Q _ _
    let e_meas := (MeasurableEquiv.piOptionEquivProd X).symm
    rw [← Measure.pi_map_piOptionEquivProd P, ← Measure.pi_map_piOptionEquivProd Q,
      e_meas.hellingerAffinity_map, hellingerAffinity_prod,
      ih (fun i ↦ P (some i)) (fun i ↦ Q (some i)), Fintype.prod_option, mul_comm]

/-- The Hellinger affinity of two finite product powers `P^ι` and `Q^ι` of σ-finite measures equals
`hellingerAffinity P Q ^ Fintype.card ι`. -/
theorem hellingerAffinity_pi_const {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] :
    hellingerAffinity (Measure.pi fun _ : ι ↦ P) (Measure.pi fun _ : ι ↦ Q) =
      hellingerAffinity P Q ^ Fintype.card ι := by
  simp [hellingerAffinity_pi]

/-- **Tensorization of the squared Hellinger distance.** For any finite index type `ι` and σ-finite
measures `P`, `Q`, the squared Hellinger distance between the product powers `P^ι` and `Q^ι` is
`2 * (1 - (1 - sqHellinger P Q / 2) ^ Fintype.card ι)`. -/
theorem sqHellinger_pi_const {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] :
    sqHellinger (Measure.pi fun _ : ι ↦ P) (Measure.pi fun _ : ι ↦ Q) =
      2 * (1 - (1 - sqHellinger P Q / 2) ^ Fintype.card ι) := by
  rw [sqHellinger_def, hellingerAffinity_pi_const, sqHellinger_def]
  have h : 1 - 2 * (1 - hellingerAffinity P Q) / 2 = hellingerAffinity P Q := by ring
  rw [h]

/-- **Factorization of the Hellinger affinity on infinite products.** If two families of
probability measures agree outside a finite set `s` of coordinates, then the Hellinger affinity of
their infinite product measures equals the finite product of the affinities over `s`. -/
theorem hellingerAffinity_infinitePi {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (P Q : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    {s : Finset ι} (hPQ : ∀ i ∉ s, P i = Q i) :
    hellingerAffinity (Measure.infinitePi P) (Measure.infinitePi Q) =
      ∏ i ∈ s, hellingerAffinity (P i) (Q i) := by
  classical
  let S : Set ι := s
  let T : Set ι := Sᶜ
  let e : (∀ i, X i) ≃ᵐ (∀ i : S, X i) × (∀ i : T, X i) :=
    MeasurableEquiv.piEquivPiSubtypeProd X (· ∈ S)
  have hmapP : (Measure.infinitePi P).map e =
      (Measure.infinitePi fun i : S ↦ P i).prod (Measure.infinitePi fun i : T ↦ P i) :=
    TauCeti.Probability.infinitePi_map_pair_domRestrict P disjoint_compl_right
  have hmapQ : (Measure.infinitePi Q).map e =
      (Measure.infinitePi fun i : S ↦ Q i).prod (Measure.infinitePi fun i : T ↦ Q i) :=
    TauCeti.Probability.infinitePi_map_pair_domRestrict Q disjoint_compl_right
  have htail : (fun i : T ↦ P i) = (fun i : T ↦ Q i) := funext fun i ↦ hPQ i.1 i.2
  rw [← e.hellingerAffinity_map, hmapP, hmapQ, hellingerAffinity_prod, htail,
    hellingerAffinity_self, Measure.real_def, measure_univ, ENNReal.toReal_one, mul_one,
    Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi, hellingerAffinity_pi]
  exact Finset.prod_coe_sort s (fun i ↦ hellingerAffinity (P i) (Q i))

end TauCeti
