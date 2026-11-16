/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.TemperleyLieb.Trace
public import TauCeti.Algebra.TypeAHeckeAlgebra.UnitaryStar
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.RingTheory.TraceFunctional.Positive
import Mathlib.Algebra.Star.LinearMap

/-!
# Unit-circle star transport and Jones positivity on the Temperley–Lieb quotient

In the unit-circle involution of `TauCeti.Algebra.TypeAHeckeAlgebra.UnitaryStar`, where
`Fact ((q : R) ∈ unitary R)`, each Hecke generator `T i` is unitary with adjoint
`T i⁻¹ = T i - (q - q⁻¹)`. Consequently `δ = q + q⁻¹ = q + star q` is self-adjoint, the generator
images `e i - q⁻¹` in `TemperleyLieb R δ n` are unitary, and `toTemperleyLieb` preserves `star` by
the universal property `TauCeti.TypeAHeckeAlgebra.UnitCircle.map_star_iff`. Even though `T i` is
not self-adjoint in general, the shifted element `T i + q⁻¹` is self-adjoint, so for `(s : R) =
q + q⁻¹` the normalized eigenprojections `eigenprojection q s i = s⁻¹ • (T i + q⁻¹)` are again star
projections mapping onto `s⁻¹ • e i`.

On the infinite Hecke algebra, `ocneanuTrace R q z` conjugates under the unit-circle involution to
`ocneanuTrace R q (star z + (q - q⁻¹))`. For any self-adjoint `s : Rˣ`, the Temperley–Lieb Markov
parameter `temperleyLiebOcneanuParam q s = s⁻¹ - q⁻¹` satisfies
`star (s⁻¹ - q⁻¹) + (q - q⁻¹) = (s⁻¹ - q) + (q - q⁻¹) = s⁻¹ - q⁻¹`, so `ocneanuTrace` at
`s⁻¹ - q⁻¹` is still star-preserving, `temperleyLiebFiniteRadical` is star-stable, and the finite
trace-radical quotient isomorphism upgrades to a star algebra equivalence
`finiteQuotientTemperleyLiebStarEquiv`.

Over `ℂ`, unitarity of `q` forces `δ = q + q⁻¹ = 2 Re q ∈ [-2, 2]`, so the admissible positive loop
parameters reduce to `{2 cos (π / m) : m ≥ 3} ∪ {2}`. Because `toTemperleyLieb` is surjective and
intertwines `star`, Jones's positivity theorem transports in both directions to the unit-circle
Hecke tower: for `0 < δ` with `(s : ℂ) = δ = q + q⁻¹`, `ocneanuTrace ℂ q (s⁻¹ - q⁻¹)` is positive
semidefinite on all finite stages `TypeAHeckeAlgebra ℂ q n` if and only if
`δ ∈ TemperleyLieb.jonesLoopParameters`, failing from level `⌊π / arccos (δ / 2)⌋₊` onward
otherwise. At the root-of-unity specialization `q = exp (i π / m)` (`m ≥ 3`), where
`δ = 2 cos (π / m)`, `ocneanuTrace` defines a bundled `StarPositiveFunctional` whose GNS null space
is `temperleyLiebFiniteRadical`, and every `(m - 1)`-strand lift of the Jones–Wenzl projection lies
in that null ideal.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.UnitCircle.toTemperleyLiebStarAlgHom`: `toTemperleyLieb` bundled as a
  star algebra homomorphism in the unit-circle fiber.
* `TauCeti.TypeAHeckeAlgebra.UnitCircle.finiteQuotientStrandInclStarAlgHom`: the star algebra tower
  map on finite Hecke trace-radical quotients in the unit-circle fiber.
* `TauCeti.TypeAHeckeAlgebra.UnitCircle.finiteQuotientTemperleyLiebStarEquiv`: the star algebra
  isomorphism between finite Hecke and Temperley–Lieb trace-radical quotients.
* `TauCeti.TypeAHeckeAlgebra.UnitCircle.temperleyLiebPositiveTrace`: the bundled
  `StarPositiveFunctional` on `TypeAHeckeAlgebra ℂ q n` at an admissible unit-circle parameter.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle.ocneanuTrace_star`: `ocneanuTrace R q z (star x) =
  star (ocneanuTrace R q (star z + (q - q⁻¹)) x)` in the unit-circle fiber.
* `TauCeti.TypeAHeckeAlgebra.UnitCircle.isStarProjection_eigenprojection`: `eigenprojection q s i`
  is a star projection in the unit-circle fiber when `(s : R) = q + q⁻¹`.
* `TauCeti.TypeAHeckeAlgebra.UnitCircle.forall_ocneanuTrace_temperleyLieb_nonneg_iff`: **Jones's
  positivity theorem** for `ocneanuTrace` on the unit-circle Hecke tower.
* `TauCeti.TypeAHeckeAlgebra.UnitCircle.exists_ocneanuTrace_temperleyLieb_star_mul_self_neg`:
  failure of positivity from level `⌊π / arccos (δ / 2)⌋₊` onward when `δ ∉ jonesLoopParameters`.
* `TauCeti.TypeAHeckeAlgebra.UnitCircle.mem_finiteRadical_of_toTemperleyLieb_eq_jonesWenzl`: at
  `δ = 2 cos (π / m)` (`m ≥ 3`), every `(m - 1)`-strand Hecke lift of the Jones–Wenzl projection
  lies in `temperleyLiebFiniteRadical`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4, 5, and 11.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383,
  Section 3.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [hq : Fact ((q : R) ∈ unitary R)]

/-- In the unit-circle involution, `ocneanuTrace R q z` conjugates under `star` to
`ocneanuTrace R q (star z + (q - q⁻¹))`. -/
@[simp]
theorem ocneanuTrace_star (z : R) (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q z (star x) = star (ocneanuTrace R q (star z + ((q : R) - ↑q⁻¹)) x) := by
  let w : R := star z + ((q : R) - ↑q⁻¹)
  let τ' : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R :=
    (star (WithConv.toConv (ocneanuTrace R q w))).ofConv
  have happly (y : InfiniteTypeAHeckeAlgebra R q) :
      τ' y = star (ocneanuTrace R q w (star y)) := by
    simp [τ']
  have hτ : IsMarkovTrace w (ocneanuTrace R q w) := isMarkovTrace_ocneanuTrace w
  have hw : w - ((q : R) - ↑q⁻¹) = star z := add_sub_cancel_right (star z) _
  have hτ' : IsMarkovTrace z τ' :=
    { map_one := by simp [happly]
      map_mul_comm a b := by simp only [happly, star_mul, hτ.map_mul_comm (star b)]
      map_mul_T {n a} ha := by
        have hsa : star a ∈ stage R q (n + 1) := star_mem_stage_iff.mpr ha
        rw [happly, star_mul, star_T, hτ.map_mul_comm (↑(unitT q n)⁻¹),
          hτ.map_mul_val_inv_unitT hsa, hw, star_mul, star_star, ← happly, mul_comm] }
  have heq := LinearMap.congr_fun hτ'.eq_ocneanuTrace (star x)
  simpa only [happly, star_star] using heq.symm

/-- When `star z + (q - q⁻¹) = z`, `ocneanuTrace R q z` commutes with the unit-circle involution.
-/
theorem ocneanuTrace_star_of_star_add_sub_eq {z : R} (hz : star z + ((q : R) - ↑q⁻¹) = z)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q z (star x) = star (ocneanuTrace R q z x) := by
  rw [ocneanuTrace_star, hz]

end TauCeti.InfiniteTypeAHeckeAlgebra.UnitCircle

namespace TauCeti.TypeAHeckeAlgebra.UnitCircle

open InfiniteTypeAHeckeAlgebra

section StarRing

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} {n : ℕ}
variable [hq : Fact ((q : R) ∈ unitary R)]

/-- For unitary `q`, the loop parameter `δ = q + q⁻¹ = q + star q` is self-adjoint. -/
theorem isSelfAdjoint_add_inv {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) : IsSelfAdjoint δ := by
  rw [IsSelfAdjoint, hδ, star_add, Units.mem_unitary_iff_star_eq_inv.1 hq.out,
    Units.star_inv_eq_of_mem_unitary hq.out, add_comm]

/-- For `δ = q + q⁻¹` with `q` unitary, the Temperley–Lieb image `e i - q⁻¹` of each Hecke
generator `T i` is unitary. -/
theorem toTemperleyLieb_T_mem_unitary {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) [Fact (IsSelfAdjoint δ)]
    (i : Fin (n - 1)) :
    toTemperleyLieb n hδ (T q i) ∈ unitary (TemperleyLieb R δ n) := by
  have hstar : star (toTemperleyLieb n hδ (T q i)) =
      TemperleyLieb.e δ i - algebraMap R _ (q : R) := by
    rw [toTemperleyLieb_T, star_sub, TemperleyLieb.star_e, ← algebraMap_star_comm,
      Units.star_inv_eq_of_mem_unitary hq.out]
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [hstar, toTemperleyLieb_T, sub_mul, mul_sub, mul_sub, TemperleyLieb.e_mul_self,
      ← Algebra.commutes (↑q⁻¹ : R) (TemperleyLieb.e δ i), ← Algebra.smul_def, ← Algebra.smul_def,
      ← map_mul, q.mul_inv, map_one, hδ, add_smul]
    abel
  · rw [hstar, toTemperleyLieb_T, sub_mul, mul_sub, mul_sub, TemperleyLieb.e_mul_self,
      ← Algebra.commutes (q : R) (TemperleyLieb.e δ i), ← Algebra.smul_def, ← Algebra.smul_def,
      ← map_mul, q.inv_mul, map_one, hδ, add_smul]
    abel

/-- In the unit-circle convention, `toTemperleyLieb` commutes with `star`. -/
@[simp]
theorem toTemperleyLieb_star {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) [Fact (IsSelfAdjoint δ)]
    (x : TypeAHeckeAlgebra R q n) :
    toTemperleyLieb n hδ (star x) = star (toTemperleyLieb n hδ x) :=
  map_star_iff.mpr (toTemperleyLieb_T_mem_unitary hδ) x

variable (n) in
/-- `toTemperleyLieb` bundled as a star algebra homomorphism in the unit-circle fiber. -/
noncomputable def toTemperleyLiebStarAlgHom {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint δ)] :
    TypeAHeckeAlgebra R q n →⋆ₐ[R] TemperleyLieb R δ n :=
  { toTemperleyLieb n hδ with map_star' := toTemperleyLieb_star hδ }

/-- Forgetting star compatibility recovers `toTemperleyLieb`. -/
@[simp]
theorem toAlgHom_toTemperleyLiebStarAlgHom {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint δ)] :
    (toTemperleyLiebStarAlgHom n hδ).toAlgHom = toTemperleyLieb n hδ := (rfl)

/-- Evaluating `toTemperleyLiebStarAlgHom` agrees with `toTemperleyLieb`. -/
@[simp]
theorem toTemperleyLiebStarAlgHom_apply {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint δ)] (x : TypeAHeckeAlgebra R q n) :
    toTemperleyLiebStarAlgHom n hδ x = toTemperleyLieb n hδ x := (rfl)

/-- `toTemperleyLiebStarAlgHom` is surjective. -/
theorem toTemperleyLiebStarAlgHom_surjective {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint δ)] :
    Function.Surjective (toTemperleyLiebStarAlgHom n hδ) :=
  toTemperleyLieb_surjective hδ

/-- Even though `T i` is unitary rather than self-adjoint in the unit-circle fiber, the shifted
generator `T i + q⁻¹` is self-adjoint because `star (T i) = T i - (q - q⁻¹)` and `star (q⁻¹) = q`.
-/
theorem isSelfAdjoint_T_add_algebraMap_inv (i : Fin (n - 1)) :
    IsSelfAdjoint (T q i + algebraMap R (TypeAHeckeAlgebra R q n) (↑q⁻¹ : R)) := by
  rw [IsSelfAdjoint, star_add, star_T, val_inv_unitT, ← algebraMap_star_comm,
    Units.star_inv_eq_of_mem_unitary hq.out, map_sub]
  abel

/-- For self-adjoint `s : Rˣ`, `eigenprojection q s i` is self-adjoint in the unit-circle fiber. -/
theorem isSelfAdjoint_eigenprojection {s : Rˣ} (hs_sa : IsSelfAdjoint (s : R))
    (i : Fin (n - 1)) : IsSelfAdjoint (eigenprojection q s i) := by
  have hsinv : IsSelfAdjoint (↑s⁻¹ : R) := by
    simpa only [Ring.inverse_unit] using hs_sa.ringInverse
  rw [IsSelfAdjoint, eigenprojection_def, star_smul, hsinv.star_eq,
    (isSelfAdjoint_T_add_algebraMap_inv (q := q) i).star_eq]

/-- In the unit-circle fiber, `eigenprojection q s i` is a star projection when
`(s : R) = q + q⁻¹`. -/
theorem isStarProjection_eigenprojection {s : Rˣ} (hs : (s : R) = (q : R) + ↑q⁻¹)
    (i : Fin (n - 1)) : IsStarProjection (eigenprojection q s i) :=
  ⟨isIdempotentElem_eigenprojection hs i,
    isSelfAdjoint_eigenprojection (isSelfAdjoint_add_inv hs) i⟩

/-- For self-adjoint `s : Rˣ`, the Temperley–Lieb Markov parameter `s⁻¹ - q⁻¹` satisfies the
unit-circle self-adjointness condition `star z + (q - q⁻¹) = z`. -/
theorem star_temperleyLiebOcneanuParam_add_sub {s : Rˣ} (hs_sa : IsSelfAdjoint (s : R)) :
    star (temperleyLiebOcneanuParam q s) + ((q : R) - ↑q⁻¹) = temperleyLiebOcneanuParam q s := by
  have hsinv : IsSelfAdjoint (↑s⁻¹ : R) := by
    simpa only [Ring.inverse_unit] using hs_sa.ringInverse
  rw [temperleyLiebOcneanuParam_def, star_sub, hsinv.star_eq,
    Units.star_inv_eq_of_mem_unitary hq.out]
  abel

/-- At any self-adjoint `s : Rˣ`, `ocneanuTrace R q (temperleyLiebOcneanuParam q s)` commutes with
the unit-circle involution. -/
theorem ocneanuTrace_temperleyLiebOcneanuParam_star {s : Rˣ} (hs_sa : IsSelfAdjoint (s : R))
    (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q (temperleyLiebOcneanuParam q s) (star x) =
      star (ocneanuTrace R q (temperleyLiebOcneanuParam q s) x) :=
  InfiniteTypeAHeckeAlgebra.UnitCircle.ocneanuTrace_star_of_star_add_sub_eq
    (star_temperleyLiebOcneanuParam_add_sub hs_sa) x

/-- At self-adjoint `s : Rˣ`, `temperleyLiebFiniteRadical` is invariant under the unit-circle
involution. -/
instance instIsStarTemperleyLiebFiniteRadical (s : Rˣ) [hs_sa : Fact (IsSelfAdjoint (s : R))]
    (n : ℕ) : (temperleyLiebFiniteRadical (q := q) s n).IsStar := by
  rw [temperleyLiebFiniteRadical, finiteRadical_def]
  refine LinearMap.isStar_traceRadical _ _ fun x ↦ ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, toInfinite_star]
  exact ocneanuTrace_temperleyLiebOcneanuParam_star hs_sa.out (toInfinite R q n x)

/-- Forward tower map between finite Hecke trace-radical quotients bundled as a star algebra
homomorphism in the unit-circle fiber. -/
noncomputable def finiteQuotientStrandInclStarAlgHom (s : Rˣ) (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))] (n : ℕ) :
    TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n →⋆ₐ[R]
      TypeAHeckeAlgebra R q (n + 1) ⧸ temperleyLiebFiniteRadical (q := q) s (n + 1) :=
  Ideal.quotientStarAlgHom (temperleyLiebFiniteRadical (q := q) s (n + 1))
    { strandIncl R q n with map_star' := strandIncl_star }
    (comap_finiteRadical_temperleyLieb_strandIncl hs n).ge

/-- Evaluating `finiteQuotientStrandInclStarAlgHom` agrees with `finiteQuotientStrandIncl`. -/
@[simp]
theorem finiteQuotientStrandInclStarAlgHom_apply (s : Rˣ) (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))] (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) :
    finiteQuotientStrandInclStarAlgHom s hs n x = finiteQuotientStrandIncl s hs n x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientStrandInclStarAlgHom, Ideal.quotientStarAlgHom_mk, finiteQuotientStrandIncl_mk]
  rfl

/-- **Star algebra isomorphism between the finite Hecke trace-radical quotient and the
Temperley–Lieb trace-radical quotient in the unit-circle fiber.** -/
noncomputable def finiteQuotientTemperleyLiebStarEquiv {s : Rˣ} (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))]
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) ≃⋆ₐ[R]
      TemperleyLieb R (s : R) n ⧸ (tr n).traceRadical (htr.map_mul_comm n) :=
  Ideal.quotientStarAlgEquivOfSurjective ((tr n).traceRadical (htr.map_mul_comm n))
    (toTemperleyLiebStarAlgHom n hs)
    (by
      rw [toAlgHom_toTemperleyLiebStarAlgHom]
      exact finiteRadical_temperleyLieb_eq_comap hs htr n)
    (toTemperleyLiebStarAlgHom_surjective hs)

/-- `finiteQuotientTemperleyLiebStarEquiv` acts on quotient representatives by `toTemperleyLieb`.
-/
@[simp]
theorem finiteQuotientTemperleyLiebStarEquiv_mk {s : Rˣ} (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))]
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] (x : TypeAHeckeAlgebra R q n) :
    finiteQuotientTemperleyLiebStarEquiv hs htr
        (Ideal.Quotient.mk (temperleyLiebFiniteRadical (q := q) s n) x) =
      Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) (toTemperleyLieb n hs x) :=
  Ideal.quotientStarAlgEquivOfSurjective_mk ((tr n).traceRadical (htr.map_mul_comm n))
    (toTemperleyLiebStarAlgHom n hs) _ (toTemperleyLiebStarAlgHom_surjective hs) x

/-- `finiteQuotientTemperleyLiebStarEquiv` intertwines the quotient traces up to `s ^ n`. -/
@[simp]
theorem quotientTrace_finiteQuotientTemperleyLiebStarEquiv {s : Rˣ}
    (hs : (s : R) = (q : R) + ↑q⁻¹) [Fact (IsSelfAdjoint (s : R))]
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) :
    (tr n).quotientTrace (htr.map_mul_comm n) (finiteQuotientTemperleyLiebStarEquiv hs htr x) =
      (s : R) ^ n * temperleyLiebFiniteQuotientTrace s n x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientTemperleyLiebStarEquiv_mk, LinearMap.quotientTrace_mk,
    temperleyLiebFiniteQuotientTrace, finiteQuotientTrace_mk,
    temperleyLieb_trace_eq_mul_ocneanuTrace hs htr n x]

end StarRing

section JonesPositivity

open scoped ComplexOrder

/-- For a complex unitary unit `q`, the loop parameter `q + q⁻¹` equals `2 Re q`. -/
theorem add_inv_eq_two_mul_re (q : ℂˣ) [hq : Fact ((q : ℂ) ∈ unitary ℂ)] :
    (q : ℂ) + ↑q⁻¹ = ((2 * (q : ℂ).re : ℝ) : ℂ) := by
  rw [← Units.mem_unitary_iff_star_eq_inv.1 hq.out, Complex.star_def, Complex.add_conj,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- Any real loop value `δ = q + q⁻¹` coming from a complex unitary parameter `q` satisfies
`|δ| ≤ 2`. -/
theorem abs_le_two_of_eq_add_inv {q : ℂˣ} [hq : Fact ((q : ℂ) ∈ unitary ℂ)] {δ : ℝ}
    (hδ : (δ : ℂ) = (q : ℂ) + ↑q⁻¹) : |δ| ≤ 2 := by
  have h1 : ‖star (q : ℂ) * (q : ℂ)‖ = 1 := by
    rw [Unitary.star_mul_self_of_mem hq.out, norm_one]
  rw [norm_mul, norm_star] at h1
  have hnorm : ‖(q : ℂ)‖ = 1 := by nlinarith [norm_nonneg (q : ℂ)]
  have hre : |(q : ℂ).re| ≤ 1 := hnorm ▸ Complex.abs_re_le_norm (q : ℂ)
  have hδ_eq : δ = 2 * (q : ℂ).re :=
    Complex.ofReal_injective (hδ.trans (add_inv_eq_two_mul_re q))
  rw [hδ_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  linarith

/-- On the unit-circle fiber `(δ : ℂ) = q + q⁻¹`, an admissible loop parameter is either a discrete
Jones value `2 cos (π / m)` (`m ≥ 3`) or the endpoint `δ = 2`. -/
theorem mem_jonesLoopParameters_iff_of_eq_add_inv {q : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)] {δ : ℝ}
    (hδ : (δ : ℂ) = (q : ℂ) + ↑q⁻¹) :
    δ ∈ TemperleyLieb.jonesLoopParameters ↔
      (∃ m : ℕ, 3 ≤ m ∧ δ = 2 * Real.cos (Real.pi / m)) ∨ δ = 2 := by
  have hle2 : δ ≤ 2 := (abs_le.mp (abs_le_two_of_eq_add_inv hδ)).2
  rw [TemperleyLieb.mem_jonesLoopParameters]
  refine or_congr_right ⟨fun h2 ↦ le_antisymm hle2 h2, fun h2 ↦ h2.symm.le⟩

/-- **Jones's positivity theorem on the unit-circle Temperley–Lieb pullback.** For `0 < δ` with
`(δ : ℂ) = q + q⁻¹`, pulling back a Temperley–Lieb Markov trace along `toTemperleyLieb` gives
positive semidefinite forms on all `TypeAHeckeAlgebra ℂ q n` if and only if
`δ ∈ TemperleyLieb.jonesLoopParameters`. -/
theorem forall_temperleyLieb_pullback_nonneg_iff {q : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ : (δ : ℂ) = (q : ℂ) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (δ : ℂ))]
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : TemperleyLieb.IsMarkovTrace ℂ (δ : ℂ) tr) :
    (∀ (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n),
        0 ≤ tr n (toTemperleyLieb n hδ (star x * x))) ↔
      δ ∈ TemperleyLieb.jonesLoopParameters := by
  rw [← htr.forall_map_star_mul_self_nonneg_iff hδ_pos]
  refine ⟨fun h n y ↦ ?_, fun h n x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := toTemperleyLieb_surjective hδ y
    simpa only [map_mul, toTemperleyLieb_star] using h n x
  · simpa only [map_mul, toTemperleyLieb_star] using h n (toTemperleyLieb n hδ x)

/-- Multiplying a complex number by a positive real scalar preserves nonnegativity in
`ComplexOrder`. -/
private theorem ofReal_mul_nonneg_iff_of_pos {c : ℝ} (hc : 0 < c) {z : ℂ} :
    0 ≤ (c : ℂ) * z ↔ 0 ≤ z := by
  rw [Complex.nonneg_iff, Complex.nonneg_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    mul_nonneg_iff_of_pos_left hc, eq_comm, mul_eq_zero_iff_left hc.ne', eq_comm]

/-- Multiplying a complex number by a positive real scalar preserves strict negativity in
`ComplexOrder`. -/
private theorem ofReal_mul_neg_iff_of_pos {c : ℝ} (hc : 0 < c) {z : ℂ} :
    (c : ℂ) * z < 0 ↔ z < 0 := by
  rw [Complex.neg_iff, Complex.neg_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    mul_eq_zero_iff_left hc.ne']
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨by nlinarith [h1], h2⟩,
    fun ⟨h1, h2⟩ ↦ ⟨mul_neg_of_pos_of_neg hc h1, h2⟩⟩

/-- Relation between `(s⁻¹ : ℂ)` and `(δ⁻¹ : ℝ)` when `(s : ℂ) = δ` for `0 < δ`. -/
private theorem val_inv_eq_ofReal_inv {s : ℂˣ} {δ : ℝ} (hδ_pos : 0 < δ) (hsδ : (s : ℂ) = δ) :
    (↑s⁻¹ : ℂ) = ((δ⁻¹ : ℝ) : ℂ) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [hsδ, ← Complex.ofReal_mul, mul_inv_cancel₀ hδ_pos.ne', Complex.ofReal_one]

/-- **Jones's positivity theorem for the Ocneanu trace in the unit-circle fiber.** For `0 < δ` with
`(s : ℂ) = δ` and `(s : ℂ) = q + q⁻¹`, `ocneanuTrace ℂ q (s⁻¹ - q⁻¹)` is positive semidefinite on
every finite Hecke algebra `TypeAHeckeAlgebra ℂ q n` if and only if
`δ ∈ TemperleyLieb.jonesLoopParameters`. -/
theorem forall_ocneanuTrace_temperleyLieb_nonneg_iff {q s : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hsδ : (s : ℂ) = δ) (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) :
    (∀ (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n),
        0 ≤ ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) (toInfinite ℂ q n (star x * x))) ↔
      δ ∈ TemperleyLieb.jonesLoopParameters := by
  let s₀ : ℂˣ := Units.mk0 (δ : ℂ) (Complex.ofReal_ne_zero.mpr hδ_pos.ne')
  have hs_eq : s = s₀ := Units.ext hsδ
  subst hs_eq
  have : Fact (IsSelfAdjoint (δ : ℂ)) := ⟨Complex.conj_ofReal δ⟩
  let htr := TemperleyLieb.isMarkovTrace_markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
  rw [← forall_temperleyLieb_pullback_nonneg_iff hδ_pos hs htr]
  refine forall_congr' fun n ↦ forall_congr' fun x ↦ ?_
  rw [← mul_temperleyLieb_trace_eq_ocneanuTrace hs htr n (star x * x),
    val_inv_eq_ofReal_inv hδ_pos rfl, ← Complex.ofReal_pow]
  exact ofReal_mul_nonneg_iff_of_pos (by positivity)

/-- At an admissible unit-circle loop parameter `δ ∈ TemperleyLieb.jonesLoopParameters` with
`0 < δ`, `ocneanuTrace ℂ q (s⁻¹ - q⁻¹)` is nonnegative on every `star x * x`. -/
theorem ocneanuTrace_temperleyLieb_star_mul_self_nonneg {q s : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδJ : δ ∈ TemperleyLieb.jonesLoopParameters) (hsδ : (s : ℂ) = δ)
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    0 ≤ ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) (toInfinite ℂ q n (star x * x)) :=
  (forall_ocneanuTrace_temperleyLieb_nonneg_iff hδ_pos hsδ hs).mpr hδJ n x

/-- **Failure of positivity from level `⌊π / arccos (δ / 2)⌋₊` onward.** At an inadmissible
unit-circle parameter `0 < δ` with `δ ∉ TemperleyLieb.jonesLoopParameters`, for every
`n ≥ ⌊π / arccos (δ / 2)⌋₊` some element of `TypeAHeckeAlgebra ℂ q n` has strictly negative
Ocneanu norm. -/
theorem exists_ocneanuTrace_temperleyLieb_star_mul_self_neg {q s : ℂˣ}
    [Fact ((q : ℂ) ∈ unitary ℂ)] {δ : ℝ} (hδ_pos : 0 < δ)
    (hδJ : δ ∉ TemperleyLieb.jonesLoopParameters) (hsδ : (s : ℂ) = δ)
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) {n : ℕ} (hn : ⌊Real.pi / Real.arccos (δ / 2)⌋₊ ≤ n) :
    ∃ x : TypeAHeckeAlgebra ℂ q n,
      ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) (toInfinite ℂ q n (star x * x)) < 0 := by
  let s₀ : ℂˣ := Units.mk0 (δ : ℂ) (Complex.ofReal_ne_zero.mpr hδ_pos.ne')
  have hs_eq : s = s₀ := Units.ext hsδ
  subst hs_eq
  have : Fact (IsSelfAdjoint (δ : ℂ)) := ⟨Complex.conj_ofReal δ⟩
  have : Fact (IsSelfAdjoint (s₀ : ℂ)) := ⟨isSelfAdjoint_add_inv hs⟩
  let htr := TemperleyLieb.isMarkovTrace_markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
  obtain ⟨y, hy⟩ := htr.exists_map_star_mul_self_neg hδ_pos hδJ hn
  obtain ⟨x, rfl⟩ := toTemperleyLieb_surjective hs y
  refine ⟨x, ?_⟩
  rw [← mul_temperleyLieb_trace_eq_ocneanuTrace hs htr n (star x * x),
    val_inv_eq_ofReal_inv hδ_pos rfl, ← Complex.ofReal_pow,
    ofReal_mul_neg_iff_of_pos (by positivity), map_mul, toTemperleyLieb_star]
  exact hy

/-- Bundled `StarPositiveFunctional` on `TypeAHeckeAlgebra ℂ q n` induced by `ocneanuTrace` at an
admissible unit-circle parameter `δ ∈ TemperleyLieb.jonesLoopParameters` (`0 < δ`). -/
noncomputable def temperleyLiebPositiveTrace {q s : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδJ : δ ∈ TemperleyLieb.jonesLoopParameters)
    (hsδ : (s : ℂ) = δ) (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) ∘ₗ (toInfinite ℂ q n).toLinearMap
  square_nonneg x := ocneanuTrace_temperleyLieb_star_mul_self_nonneg hδ_pos hδJ hsδ hs n x

/-- Underlying linear map of `temperleyLiebPositiveTrace`. -/
@[simp]
theorem toLinearMap_temperleyLiebPositiveTrace {q s : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδJ : δ ∈ TemperleyLieb.jonesLoopParameters)
    (hsδ : (s : ℂ) = δ) (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    (temperleyLiebPositiveTrace hδ_pos hδJ hsδ hs n).toLinearMap =
      ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) ∘ₗ (toInfinite ℂ q n).toLinearMap := (rfl)

/-- Evaluating `temperleyLiebPositiveTrace` recovers `ocneanuTrace` along `toInfinite`. -/
@[simp]
theorem temperleyLiebPositiveTrace_apply {q s : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδJ : δ ∈ TemperleyLieb.jonesLoopParameters)
    (hsδ : (s : ℂ) = δ) (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ)
    (x : TypeAHeckeAlgebra ℂ q n) :
    temperleyLiebPositiveTrace hδ_pos hδJ hsδ hs n x =
      ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) (toInfinite ℂ q n x) := (rfl)

/-- `temperleyLiebPositiveTrace` is normalized at `1`. -/
theorem temperleyLiebPositiveTrace_one {q s : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδJ : δ ∈ TemperleyLieb.jonesLoopParameters)
    (hsδ : (s : ℂ) = δ) (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    temperleyLiebPositiveTrace hδ_pos hδJ hsδ hs n 1 = 1 := by
  simp

/-- The GNS null space of `temperleyLiebPositiveTrace` in the unit-circle fiber is the underlying
complex submodule of `temperleyLiebFiniteRadical`. -/
theorem nullSubmodule_temperleyLiebPositiveTrace {q s : ℂˣ} [Fact ((q : ℂ) ∈ unitary ℂ)]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδJ : δ ∈ TemperleyLieb.jonesLoopParameters)
    (hsδ : (s : ℂ) = δ) (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    (temperleyLiebPositiveTrace hδ_pos hδJ hsδ hs n).nullSubmodule =
      (temperleyLiebFiniteRadical (q := q) s n).restrictScalars ℂ := by
  have hcomm := (ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s)).comp_algHom_mul_comm
    (isMarkovTrace_ocneanuTrace (q := q) (temperleyLiebOcneanuParam q s)).map_mul_comm
    (toInfinite ℂ q n)
  rw [(temperleyLiebPositiveTrace hδ_pos hδJ hsδ hs n).nullSubmodule_eq_traceRadical hcomm,
    temperleyLiebFiniteRadical, finiteRadical_def]
  ext x
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_traceRadical,
    toLinearMap_temperleyLiebPositiveTrace]

/-- Every element of `Circle` defines a unitary unit `Circle.toUnits z` in `ℂ`. -/
theorem circleToUnits_mem_unitary (z : Circle) : (Circle.toUnits z : ℂ) ∈ unitary ℂ := by
  rw [Units.mem_unitary_iff_star_eq_inv, ← map_inv, Circle.toUnits_apply, Circle.toUnits_apply,
    Units.val_mk0, Units.val_mk0, Circle.coe_inv_eq_conj, Complex.star_def]

/-- For `q = Circle.toUnits (Circle.exp θ)`, the loop parameter `q + q⁻¹` is `2 cos θ`. -/
theorem circleToUnits_exp_add_inv (θ : ℝ) :
    (Circle.toUnits (Circle.exp θ) : ℂ) + ↑(Circle.toUnits (Circle.exp θ))⁻¹ =
      ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [← map_inv, Circle.toUnits_apply, Circle.toUnits_apply, Units.val_mk0, Units.val_mk0,
    Circle.coe_inv, Circle.coe_add_inv_coe, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- For `m ≥ 3`, the discrete loop value `2 cos (π / m)` is strictly positive. -/
theorem two_mul_cos_pi_div_pos {m : ℕ} (hm : 3 ≤ m) : 0 < 2 * Real.cos (Real.pi / m) := by
  have hm_pos : (0 : ℝ) < m := by positivity
  have hlt : Real.pi / m < Real.pi / 2 := by
    rw [div_lt_div_iff₀ hm_pos two_pos]
    have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos (Real.pi / m) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [div_pos Real.pi_pos hm_pos], hlt⟩
  linarith

/-- For `m ≥ 3`, `2 cos (π / m)` belongs to `TemperleyLieb.jonesLoopParameters`. -/
theorem two_mul_cos_pi_div_mem_jonesLoopParameters {m : ℕ} (hm : 3 ≤ m) :
    2 * Real.cos (Real.pi / m) ∈ TemperleyLieb.jonesLoopParameters :=
  TemperleyLieb.mem_jonesLoopParameters.mpr (Or.inl ⟨m, hm, rfl⟩)

/-- **Negligibility of `(m - 1)`-strand Jones–Wenzl lifts at `δ = 2 cos (π / m)`.** When `3 ≤ m`
and `(s : ℂ) = 2 cos (π / m) = q + q⁻¹`, the quantum integers `[1], …, [m - 1]` are positive units
while `[m] = 0`, so every `(m - 1)`-strand Hecke lift of `TemperleyLieb.jonesWenzl` lies in
`temperleyLiebFiniteRadical s (m - 1)`. -/
theorem mem_finiteRadical_of_toTemperleyLieb_eq_jonesWenzl {q s : ℂˣ} {m : ℕ} (hm : 3 ≤ m)
    (hsm : (s : ℂ) = ((2 * Real.cos (Real.pi / m) : ℝ) : ℂ))
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) {x : TypeAHeckeAlgebra ℂ q (m - 1)}
    (hx : toTemperleyLieb (m - 1) hs x = TemperleyLieb.jonesWenzl (s : ℂ) (m - 1)) :
    x ∈ temperleyLiebFiniteRadical (q := q) s (m - 1) := by
  have hq (j : ℕ) : qInt ℂ (s : ℂ) j = (qInt ℝ (2 * Real.cos (Real.pi / m)) j : ℂ) := by
    rw [hsm]
    exact (Complex.ofRealHom.map_qInt _ j).symm
  have hunit : ∀ k ∈ Finset.Icc 1 (m - 1), IsUnit (qInt ℂ (s : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
    rw [hq]
    exact (Complex.ofReal_ne_zero.mpr
      (qInt_two_mul_cos_pi_div_pos (by omega) (by omega)).ne').isUnit
  rw [mem_finiteRadical_iff_qInt_eq_zero hs hunit hx,
    -- For `m ≥ 3`, `(m - 1) + 1 = m`, where the `m`-th quantum integer vanishes.
    show m - 1 + 1 = m by omega, hq, qInt_two_mul_cos_pi_div_eq_zero (by omega),
    Complex.ofReal_zero]

end JonesPositivity

end TauCeti.TypeAHeckeAlgebra.UnitCircle
