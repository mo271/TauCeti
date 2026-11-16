/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Fixed points of inversion on the multiplicative group

On the multiplicative group `𝔾ₘ = Spec R[T;T⁻¹]` over a commutative ring `R`, group-scheme
inversion corresponds contravariantly to the antipode `HopfAlgebra.antipodeBialgHom` sending `T` to
`T⁻¹`. Its fixed-point Hopf ideal `HopfIdeal.multiplicativeGroupInversion R` cuts out the
`2`-torsion closed subgroup scheme `μ₂ ⊆ 𝔾ₘ`:
* On `A`-points, the subgroup cut out by `multiplicativeGroupInversion R` consists of those units
  `u = MultiplicativeGroup.pointsMulEquiv g` satisfying `u ^ 2 = 1`
  (`CommHopfAlgCat.mem_quotientPointsSubgroup_multiplicativeGroupInversion_iff`).
* Over a nontrivial base ring `R` in which `2` is invertible, `(1 / 2) • (1 + T)` defines a
  nontrivial idempotent in `R[T;T⁻¹] ⧸ (multiplicativeGroupInversion R).toIdeal`, so the prime
  spectrum of the fixed-point quotient is disconnected
  (`HopfIdeal.not_connectedSpace_primeSpectrum_quotient_multiplicativeGroupInversion`). Smooth
  fixed-point subgroup schemes of connected smooth groups under tame finite actions need not remain
  connected.

## Main declarations

* `TauCeti.HopfIdeal.multiplicativeGroupInversion`: the equalizer Hopf ideal of the antipode and
  the identity on `R[T;T⁻¹]`.
* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_multiplicativeGroupInversion_iff`: on
  `A`-points, `multiplicativeGroupInversion R` cuts out `{u ∈ Aˣ | u ^ 2 = 1}`.
* `TauCeti.HopfIdeal.not_connectedSpace_primeSpectrum_quotient_multiplicativeGroupInversion`:
  disconnectedness of `PrimeSpectrum (R[T;T⁻¹] ⧸ (multiplicativeGroupInversion R).toIdeal)` when
  `2 ∈ Rˣ` in a nontrivial commutative ring `R`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §3, pp. 293–295.
* J. S. Milne, *Algebraic Groups* (2017), §1.h and §2.b.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory WithConv
open scoped LaurentPolynomial

namespace TauCeti

universe u x

namespace HopfIdeal

/-- The fixed-point Hopf ideal of inversion (`HopfAlgebra.antipodeBialgHom`) on `R[T;T⁻¹]`,
cutting out the `2`-torsion closed subgroup `μ₂ ⊆ 𝔾ₘ`. -/
noncomputable def multiplicativeGroupInversion (R : Type u) [CommRing R] : HopfIdeal R R[T;T⁻¹] :=
  equalizer (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])) (BialgHom.id R R[T;T⁻¹])

theorem multiplicativeGroupInversion_def (R : Type u) [CommRing R] :
    multiplicativeGroupInversion R =
      equalizer (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹]))
        (BialgHom.id R R[T;T⁻¹]) :=
  (rfl)

/-- Every `2`-torsion unit `u : Rˣ` (`u⁻¹ = u`) defines an `R`-algebra evaluation on `R[T;T⁻¹]`
that vanishes on `multiplicativeGroupInversion R`. -/
private theorem eval_eq_zero_of_mem_multiplicativeGroupInversion {R : Type u} [CommRing R]
    {u : Rˣ} (hu : u⁻¹ = u) {p : R[T;T⁻¹]}
    (hp : p ∈ (multiplicativeGroupInversion R).toIdeal) :
    laurentEval (R := R) u p = 0 := by
  have hle : (multiplicativeGroupInversion R).toIdeal ≤
      RingHom.ker (laurentEval (R := R) u).toRingHom := by
    rw [multiplicativeGroupInversion_def, equalizer_le_ker_iff]
    have heq : (laurentEval (R := R) u).comp (_root_.HopfAlgebra.antipodeAlgHom R R[T;T⁻¹]) =
        laurentEval (R := R) u := by
      apply laurentEval_unique
      simp [zpow_neg, hu]
    intro q
    simpa only [HopfAlgebra.antipodeBialgHom_apply, BialgHom.id_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.comp_apply, _root_.HopfAlgebra.antipodeAlgHom_apply] using
      congr($heq q)
  simpa using RingHom.mem_ker.mp (hle hp)

/-- Modulo `multiplicativeGroupInversion R`, the coordinate `T 1` squares to `1`. -/
private theorem mk_T_mul_self_multiplicativeGroupInversion (R : Type u) [CommRing R] :
    let I := (multiplicativeGroupInversion R).toIdeal
    Ideal.Quotient.mk I (LaurentPolynomial.T 1) *
      Ideal.Quotient.mk I (LaurentPolynomial.T 1) = 1 := by
  intro I
  have ht_inv : Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) =
      Ideal.Quotient.mk I (LaurentPolynomial.T 1) := by
    apply Ideal.Quotient.eq.mpr
    have hmem : (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])) (LaurentPolynomial.T 1) -
        (BialgHom.id R R[T;T⁻¹]) (LaurentPolynomial.T 1) ∈ I :=
      mem_toIdeal.mpr (sub_mem_equalizer (LaurentPolynomial.T 1))
    simpa only [HopfAlgebra.antipodeBialgHom_apply, LaurentPolynomial.antipode_T,
      BialgHom.id_apply] using hmem
  calc
    Ideal.Quotient.mk I (LaurentPolynomial.T 1) * Ideal.Quotient.mk I (LaurentPolynomial.T 1)
        = Ideal.Quotient.mk I (LaurentPolynomial.T 1) *
            Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) := by rw [ht_inv]
    _ = Ideal.Quotient.mk I (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) :=
          (map_mul _ _ _).symm
    _ = 1 := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, map_one]

/-- Every `2`-torsion unit `u : Rˣ` (`u⁻¹ = u`) induces an `R`-algebra map on the inversion
fixed-point quotient sending the class of `c • (1 + T)` to `c * (1 + u)`. -/
private theorem exists_algHom_eval_idempotent {R : Type u} [CommRing R] {u : Rˣ} (hu : u⁻¹ = u)
    (c : R) :
    ∃ φ : (R[T;T⁻¹] ⧸ (multiplicativeGroupInversion R).toIdeal) →ₐ[R] R,
      φ (Ideal.Quotient.mkₐ R (multiplicativeGroupInversion R).toIdeal
        (c • (1 + LaurentPolynomial.T 1))) = c * (1 + u) := by
  refine ⟨Ideal.Quotient.liftₐ (multiplicativeGroupInversion R).toIdeal
    (laurentEval (R := R) u)
    (fun _ hx ↦ eval_eq_zero_of_mem_multiplicativeGroupInversion hu hx), ?_⟩
  have hmk := DFunLike.congr_fun
    (Ideal.Quotient.liftₐ_comp (multiplicativeGroupInversion R).toIdeal
      (laurentEval (R := R) u)
      (fun _ hx ↦ eval_eq_zero_of_mem_multiplicativeGroupInversion hu hx))
    (c • (1 + LaurentPolynomial.T 1))
  simpa only [AlgHom.comp_apply, map_smul, map_add, map_one, laurentEval_T, zpow_one,
    smul_eq_mul] using hmk

/-- Over a nontrivial base ring `R` in which `2` is invertible, the fixed-point quotient of
`R[T;T⁻¹]` under inversion has a nontrivial idempotent `(1/2) • (1 + T)` and hence a disconnected
prime spectrum. Smooth fixed-point subgroup schemes of connected smooth groups need not be
connected. -/
theorem not_connectedSpace_primeSpectrum_quotient_multiplicativeGroupInversion
    {R : Type u} [CommRing R] [Nontrivial R] (h2 : IsUnit (2 : R)) :
    ¬ ConnectedSpace
      (PrimeSpectrum (R[T;T⁻¹] ⧸ (multiplicativeGroupInversion R).toIdeal)) := by
  intro hconn
  let I : Ideal R[T;T⁻¹] := (multiplicativeGroupInversion R).toIdeal
  let c : R := ↑h2.unit⁻¹
  have hc2 : c * 2 = 1 := Units.inv_mul_eq_one.mpr rfl
  have hc2' : algebraMap R (R[T;T⁻¹] ⧸ I) c * 2 = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (algebraMap R (R[T;T⁻¹] ⧸ I)) hc2
  let t : R[T;T⁻¹] ⧸ I := Ideal.Quotient.mk I (LaurentPolynomial.T 1)
  have ht : t * t = 1 := mk_T_mul_self_multiplicativeGroupInversion R
  set e : R[T;T⁻¹] ⧸ I := Ideal.Quotient.mkₐ R I (c • (1 + LaurentPolynomial.T 1)) with he_def
  have he : IsIdempotentElem e := by
    have he_eq : e = algebraMap R (R[T;T⁻¹] ⧸ I) c * (1 + t) := by
      rw [he_def, map_smul, Algebra.smul_def, map_add, map_one, Ideal.Quotient.mkₐ_eq_mk]
    rw [isIdempotentElem_iff, he_eq, ← sub_eq_zero]
    calc
      algebraMap R _ c * (1 + t) * (algebraMap R _ c * (1 + t)) - algebraMap R _ c * (1 + t)
          = algebraMap R _ c * ((algebraMap R _ c * 2 - 1) * (1 + t) +
              algebraMap R _ c * (t * t - 1)) := by ring
      _ = 0 := by rw [hc2', ht, sub_self, zero_mul, mul_zero, add_zero, mul_zero]
  rcases he.eq_zero_or_eq_one_of_preconnectedSpace with he0 | he1
  · obtain ⟨φ, hφ⟩ := exists_algHom_eval_idempotent (R := R) inv_one c
    rw [← he_def, he0, map_zero, Units.val_one, one_add_one_eq_two, hc2] at hφ
    exact zero_ne_one hφ
  · obtain ⟨φ, hφ⟩ := exists_algHom_eval_idempotent (R := R) (u := -1) (Units.ext (by simp)) c
    rw [← he_def, he1, map_one, Units.val_neg, Units.val_one, add_neg_cancel, mul_zero] at hφ
    exact one_ne_zero hφ

end HopfIdeal

namespace CommHopfAlgCat

/-- On `A`-points of `𝔾ₘ = Spec R[T;T⁻¹]`, the closed subgroup cut out by
`HopfIdeal.multiplicativeGroupInversion R` consists of those units
`u = MultiplicativeGroup.pointsMulEquiv g` satisfying `u ^ 2 = 1`. -/
theorem mem_quotientPointsSubgroup_multiplicativeGroupInversion_iff
    {R : Type u} [CommRing R] (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.of R R[T;T⁻¹]) A) :
    g ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (HopfIdeal.multiplicativeGroupInversion R) A ↔
      MultiplicativeGroup.pointsMulEquiv g ^ 2 = 1 := by
  have heq : HopfIdeal.multiplicativeGroupInversion R =
      equalizerHopfIdeal
        (_root_.CommHopfAlgCat.ofHom (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])))
        (𝟙 (_root_.CommHopfAlgCat.of R R[T;T⁻¹])) := by
    rw [HopfIdeal.multiplicativeGroupInversion_def, equalizerHopfIdeal_def,
      ← _root_.CommHopfAlgCat.ofHom_id]
    simp only [_root_.CommHopfAlgCat.hom_ofHom]
  rw [heq, mem_quotientPointsSubgroup_equalizerHopfIdeal_iff]
  have hinv : BialgHom.mapDomain (A := A)
      ((_root_.CommHopfAlgCat.ofHom
        (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹]))).hom) g = g⁻¹ := by
    rw [BialgHom.mapDomain_apply, _root_.CommHopfAlgCat.hom_ofHom, WithConv.algHom_inv_def]
    congr 1
    ext p
    simp [AlgHom.antipodeComp_apply]
  have hid : BialgHom.mapDomain (A := A)
      (hom (𝟙 (_root_.CommHopfAlgCat.of R R[T;T⁻¹]))) g = g := by
    rw [← _root_.CommHopfAlgCat.ofHom_id, _root_.CommHopfAlgCat.hom_ofHom, BialgHom.mapDomain_id,
      MonoidHom.id_apply]
  rw [hinv, hid, ← (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).injective.eq_iff,
    map_inv, inv_eq_iff_mul_eq_one, ← sq]

end CommHopfAlgCat

end TauCeti
