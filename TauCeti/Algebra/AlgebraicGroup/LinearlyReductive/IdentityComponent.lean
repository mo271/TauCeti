/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Colinear
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Translation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Components
import TauCeti.Algebra.AlgebraicGroup.Representation.Coinvariants
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.Algebra.AlgebraicGroup.Representation.Translation
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed

/-!
# Linear reductivity via the identity component

Let `H` be a finite-type commutative Hopf algebra over a field `k`, representing an affine group
`G` of finite type without any connectedness or reducedness assumption. After extension to an
algebraic closure `K = AlgebraicClosure k`, the group sits in an exact sequence with normal
connected subgroup `(G_K)°` and finite constant component quotient `π₀(G_K)`. This file
characterizes linear reductivity of `G` in terms of `(G_K)°` and the order of `π₀(G_K)`:

* Over an algebraically closed field `k`, `G` is linearly reductive if and only if `G°` is linearly
  reductive and `(Nat.card π₀(G) : k) ≠ 0`.
* Over an arbitrary field `k`, `G` is linearly reductive if and only if `(G_K)°` is linearly
  reductive over `K` and `(Nat.card π₀(G_K) : k) ≠ 0`.
* Over a field `k` of characteristic zero, the component-order condition is automatic, so `G` is
  linearly reductive if and only if `(G_K)°` is linearly reductive over `K`. Combined with the
  connected characteristic-zero equivalence in
  `TauCeti.Algebra.AlgebraicGroup.Reductive.CompleteReducibility`, this yields Milne's
  Corollary 22.43 (`linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent`).

This reduces linear reductivity of disconnected affine groups to the connected case, both in
characteristic zero and in positive characteristic.

## Main declarations

* `TauCeti.linearlyReductiveCommHopfAlgProperty.natCast_card_connectedComponents_ne_zero`: over an
  algebraically closed field, the number of connected components of a linearly reductive
  finite-type affine group is nonzero in `k`.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.identityComponent`: linear reductivity passes from
  a finite-type affine group over an algebraically closed field to its identity component.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_identityComponent_of_card_ne_zero`: linear
  reductivity of the identity component together with invertible component-group order implies
  linear reductivity.
* `linearlyReductiveCommHopfAlgProperty_iff_identityComponent_and_card_ne_zero_of_isAlgClosed` and
  `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_identityComponent_and_card_ne_zero`: the full
  characterization over an algebraically closed field and over an arbitrary field.
* `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_charZero`: in
  characteristic zero, linear reductivity is equivalent to linear reductivity of the geometric
  identity component.

## References

* M. Nagata, *Complete reducibility of rational representations of a matric group*,
  J. Math. Kyoto Univ. **1** (1961), 87–99.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.l and Corollary 22.43.
-/

public section

open scoped TensorProduct
open CategoryTheory WithConv

namespace TauCeti

universe u

section IsAlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, the number of connected components of a linearly reductive
finite-type affine group is nonzero in the base field. -/
theorem linearlyReductiveCommHopfAlgProperty.natCast_card_connectedComponents_ne_zero
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : linearlyReductiveCommHopfAlgProperty k H.obj) :
    (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0 := by
  have hcomp := linearlyReductiveCommHopfAlgProperty.of_injective
    (FiniteTypeCommHopfAlgCat.componentCoordinateHom H)
    (FiniteTypeCommHopfAlgCat.componentCoordinateHom_injective H) hH
  exact (ConstantGroup.linearlyReductiveCommHopfAlgProperty_coordinateRing_iff k
    (ConnectedComponents (PrimeSpectrum H))).mp hcomp

/-- **Linear reductivity passes to the identity component.** Over an algebraically closed field,
if a finite-type affine group is linearly reductive, then its identity component is linearly
reductive, with no reducedness hypothesis. -/
theorem linearlyReductiveCommHopfAlgProperty.identityComponent
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : linearlyReductiveCommHopfAlgProperty k H.obj) :
    linearlyReductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.identityComponent H).obj := by
  obtain ⟨σ, hσ1, hσ⟩ := FiniteTypeCommHopfAlgCat.exists_unital_colinear H
  exact linearlyReductiveCommHopfAlgProperty.of_unital_colinear
    (FiniteTypeCommHopfAlgCat.identityComponentCoordinateMap H).hom σ hσ1 hσ hH

section Converse

/-- Averaging a vector fixed by the identity component over coset representatives of `π₀` produces
a vector fixed by the whole affine group. -/
private theorem average_mem_fixedSubcomodule_of_identityComponent_fixed
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
    (g : ConnectedComponents (PrimeSpectrum H) → WithConv (H →ₐ[k] k))
    (hg : ∀ C, FiniteTypeCommHopfAlgCat.rationalComponentMap H (g C) = C)
    [Fintype (ConnectedComponents (PrimeSpectrum H))]
    {m₀ : M}
    (hm₀ : TensorProduct.map LinearMap.id
      (Ideal.Quotient.mkₐ k
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal).toLinearMap
      (Comodule.coact (R := k) (C := H) m₀) =
        m₀ ⊗ₜ[k] (1 : H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal)) :
    ((Nat.card (ConnectedComponents (PrimeSpectrum H)) : k)⁻¹ •
        ∑ C : ConnectedComponents (PrimeSpectrum H),
          Comodule.basePointsRepresentation (H := H) M (g C) m₀) ∈
      Comodule.fixedSubcomodule k H M := by
  let _ : Module.Free k M := Module.Free.of_divisionRing k M
  let π₀ := ConnectedComponents (PrimeSpectrum H)
  let m : M :=
    (Nat.card π₀ : k)⁻¹ • ∑ C : π₀, Comodule.basePointsRepresentation (H := H) M (g C) m₀
  rw [Comodule.mem_fixedSubcomodule, Comodule.coact_eq_tmul_iff_forall_matrixCoefficient]
  intro ψ
  have hcoinv : Comodule.matrixCoefficient (R := k) (C := H) ψ m₀ ∈
      (FiniteTypeCommHopfAlgCat.componentCoordinateMap H).range := by
    rw [← FiniteTypeCommHopfAlgCat.coinvariants_identityComponentHopfIdeal_eq_range H]
    exact (HopfAlgebra.identityComponentHopfIdeal (k := k)
      (H := H)).matrixCoefficient_mem_coinvariants_of_quotient_coact_eq_tmul_one M ψ m₀ hm₀
  obtain ⟨a, ha⟩ := hcoinv
  let ι := FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom H
  have ha' : ι a = Comodule.matrixCoefficient (R := k) (C := H) ψ m₀ :=
    (FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom_apply H a).trans ha
  have hmap (C : π₀) : BialgHom.mapDomain ι (g C) = ConstantGroup.toPoints k π₀ C := by
    apply WithConv.ofConv_injective
    ext x
    have hev := AlgHom.congr_fun (FiniteTypeCommHopfAlgCat.eval_componentCoordinateMap H (g C)) x
    rw [AlgHom.comp_apply, hg C] at hev
    simpa [BialgHom.mapDomain_apply, ι] using hev
  have hsum_range : Comodule.matrixCoefficient (R := k) (C := H) ψ m ∈
      Set.range (algebraMap k H) := by
    have hcoeff : Comodule.matrixCoefficient (R := k) (C := H) ψ m =
        (Nat.card π₀ : k)⁻¹ •
          ι (∑ C : π₀, HopfAlgebra.rightTranslationAlgHom (ConstantGroup.toPoints k π₀ C) a) := by
      rw [← Comodule.matrixCoefficientLinear_apply, map_smul, map_sum, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun C _ ↦ ?_
      rw [Comodule.matrixCoefficientLinear_apply,
        ← Comodule.rightTranslationAlgHom_matrixCoefficient, ← ha']
      have htr := AlgHom.congr_fun (BialgHom.comp_rightTranslationAlgHom ι (g C)) a
      simpa only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, hmap C] using htr.symm
    let r : k := ∑ C : π₀, ConstantGroup.functionAlgEquiv k π₀ a C
    have hr : ∑ C : π₀, HopfAlgebra.rightTranslationAlgHom (ConstantGroup.toPoints k π₀ C) a =
        algebraMap k (ConstantGroup.coordinateRing k π₀) r :=
      ConstantGroup.sum_rightTranslationAlgHom_toPoints a
    refine ⟨(Nat.card π₀ : k)⁻¹ * r, ?_⟩
    rw [hcoeff, hr, AlgHomClass.commutes ι r, map_mul, Algebra.smul_def]
  obtain ⟨s, hs⟩ := hsum_range
  have hs_eq : s = ψ m := by
    have hε := congrArg (Bialgebra.counitAlgHom k H) hs
    simpa only [AlgHom.commutes, Algebra.algebraMap_self_apply,
      Bialgebra.counitAlgHom_apply, Comodule.counit_matrixCoefficient] using hε
  rw [← hs, hs_eq, Algebra.smul_def, mul_one]

/-- When the identity component is linearly reductive, any `H`-invariant element in the image of a
comodule morphism lifts to a preimage fixed by the restricted coaction of `identityComponent H`. -/
private theorem exists_identityComponent_fixed_preimage
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH₀ : linearlyReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.identityComponent H).obj)
    {M N : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
    [AddCommGroup N] [Module k N] [Comodule k H N]
    (φ : Comodule.Hom k H M N) {n : N} (hn : n ∈ Comodule.fixedSubcomodule k H N)
    (hrange : n ∈ LinearMap.range φ.toLinearMap) :
    ∃ m₀ : M, φ m₀ = n ∧
      TensorProduct.map LinearMap.id
        (Ideal.Quotient.mkₐ k
          (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal).toLinearMap
        (Comodule.coact (R := k) (C := H) m₀) =
          m₀ ⊗ₜ[k]
            (1 : H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal) := by
  let H₀ := FiniteTypeCommHopfAlgCat.identityComponent H
  let q := FiniteTypeCommHopfAlgCat.toBialgHom
    (FiniteTypeCommHopfAlgCat.identityComponentCoordinateMap H)
  let _ : Comodule k H₀ M := Comodule.Corestrict q.toCoalgHom
  let _ : Comodule k H₀ N := Comodule.Corestrict q.toCoalgHom
  have hn₀ : n ∈ Comodule.fixedSubcomodule k H₀ N :=
    Comodule.mem_fixedSubcomodule_corestrict q.toCoalgHom (map_one q) hn
  obtain ⟨m₀, hm₀, hφm₀⟩ :=
    (Comodule.corestrictHom q.toCoalgHom φ).exists_fixed_preimage_of_isLinearlyReductive
      ((linearlyReductiveCommHopfAlgProperty_iff k H₀.obj).mp hH₀) hn₀
      (by rwa [Comodule.corestrictHom_toLinearMap])
  rw [Comodule.corestrictHom_apply] at hφm₀
  refine ⟨m₀, hφm₀, ?_⟩
  have h := Comodule.mem_fixedSubcomodule.mp hm₀
  rw [Comodule.corestrict_coact_apply] at h
  have hq_lin : q.toCoalgHom.toLinearMap =
      (Ideal.Quotient.mkₐ k
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal).toLinearMap := by
    ext x
    dsimp only [q]
    rw [CoalgHom.toLinearMap_eq_ofClass, LinearMap.coe_ofClass, BialgHom.toCoalgHom_apply,
      FiniteTypeCommHopfAlgCat.identityComponentCoordinateMap_def,
      FiniteTypeCommHopfAlgCat.mkQuotient_apply, AlgHom.toLinearMap_apply]
  rwa [hq_lin] at h

/-- **Linear reductivity from the identity component and component order.** Over an algebraically
closed field, if the identity component of a finite-type affine group is linearly reductive and the
number of connected components is nonzero in `k`, then the group is linearly reductive. -/
theorem linearlyReductiveCommHopfAlgProperty.of_identityComponent_of_card_ne_zero
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH₀ : linearlyReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.identityComponent H).obj)
    (hcard : (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  rw [linearlyReductiveCommHopfAlgProperty_iff,
    Coalgebra.isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective]
  intro M N f hf n
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  let φ : Comodule.Hom k H M N := ConcreteCategory.hom f.hom
  obtain ⟨y₀, hy₀⟩ := hf n.1
  obtain ⟨m₀, hφm₀, hm₀_quot⟩ := exists_identityComponent_fixed_preimage hH₀ φ n.2 ⟨y₀, hy₀⟩
  let m : M := (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k)⁻¹ •
    ∑ C : ConnectedComponents (PrimeSpectrum H),
      Comodule.basePointsRepresentation (H := H) M
        (FiniteTypeCommHopfAlgCat.componentRepresentative H C) m₀
  have hm : m ∈ Comodule.fixedSubcomodule k H M :=
    average_mem_fixedSubcomodule_of_identityComponent_fixed H
      (FiniteTypeCommHopfAlgCat.componentRepresentative H)
      (FiniteTypeCommHopfAlgCat.rationalComponentMap_componentRepresentative H) hm₀_quot
  have hφm : φ m = n.1 :=
    φ.map_inv_natCard_smul_sum_basePointsRepresentation_of_mem_fixedSubcomodule
      hcard (FiniteTypeCommHopfAlgCat.componentRepresentative H) hφm₀ n.2
  exact ⟨⟨m, hm⟩, Subtype.ext ((φ.fixedMap_apply ⟨m, hm⟩).trans hφm)⟩

end Converse

/-- Over an algebraically closed field `k`, a finite-type affine group is linearly reductive if and
only if its identity component is linearly reductive and the order of its component group is
nonzero in `k`. No reducedness hypothesis is needed. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_identityComponent_and_card_ne_zero_of_isAlgClosed
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      linearlyReductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.identityComponent H).obj ∧
        (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0 :=
  ⟨fun hH ↦ ⟨hH.identityComponent, hH.natCast_card_connectedComponents_ne_zero⟩,
    fun ⟨hH₀, hcard⟩ ↦
      linearlyReductiveCommHopfAlgProperty.of_identityComponent_of_card_ne_zero hH₀ hcard⟩

end IsAlgClosed

section ArbitraryField

variable {k : Type u} [Field k]

/-- Over an arbitrary field `k`, a finite-type affine group is linearly reductive if and only if
its geometric identity component over `AlgebraicClosure k` is linearly reductive and the number of
geometric connected components is nonzero in `k`. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_identityComponent_and_card_ne_zero
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.identityComponent
          ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H)).obj ∧
      (Nat.card (ConnectedComponents (PrimeSpectrum
        ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H))) : k) ≠
          0 := by
  let Hbar := (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H
  have hcast :
      (Nat.card (ConnectedComponents (PrimeSpectrum Hbar)) : AlgebraicClosure k) ≠ 0 ↔
        (Nat.card (ConnectedComponents (PrimeSpectrum Hbar)) : k) ≠ 0 := by
    rw [← map_natCast (algebraMap k (AlgebraicClosure k))]
    exact map_ne_zero_iff (algebraMap k (AlgebraicClosure k))
      (algebraMap k (AlgebraicClosure k)).injective
  exact (linearlyReductiveCommHopfAlgProperty_baseChange_iff (AlgebraicClosure k) H.obj).symm.trans
    ((linearlyReductiveCommHopfAlgProperty_iff_identityComponent_and_card_ne_zero_of_isAlgClosed
      Hbar).trans (and_congr_right' hcast))

/-- In characteristic zero, a finite-type affine group over a field `k` is linearly reductive if
and only if its geometric identity component over `AlgebraicClosure k` is linearly reductive. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_charZero
    [CharZero k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.identityComponent
          ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H)).obj := by
  let Hbar := (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H
  let _ : Finite (ConnectedComponents (PrimeSpectrum Hbar)) :=
    FiniteTypeCommHopfAlgCat.instFiniteConnectedComponents Hbar
  have : Nonempty (ConnectedComponents (PrimeSpectrum Hbar)) :=
    ⟨ConnectedComponents.mk (Bialgebra.augmentationPoint (AlgebraicClosure k) Hbar)⟩
  have hcard : (Nat.card (ConnectedComponents (PrimeSpectrum Hbar)) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact (linearlyReductiveCommHopfAlgProperty_iff_identityComponent_and_card_ne_zero H).trans
    (and_iff_left hcard)

end ArbitraryField

end TauCeti
