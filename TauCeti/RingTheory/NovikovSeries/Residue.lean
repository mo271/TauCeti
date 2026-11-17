/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import TauCeti.RingTheory.NovikovSeries.Grading
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing

/-!
# The zero-period residue ring of nonnegative Novikov series

Let `H` be an additive group with a period homomorphism `N : H →+ ℝ`, and `R` a ring. A series in
the nonnegative subring `nonnegSubring R N` vanishes on all negative-period exponents and has only
finitely many nonzero coefficients on `N.ker`. Restricting coefficients to `N.ker` therefore defines
a surjective unital ring homomorphism `residueHom R N : nonnegSubring R N →+* R[N.ker]` whose
kernel is the positive ideal `posIdeal R N`. The first isomorphism theorem identifies the quotient
`nonnegSubring R N ⧸ posIdeal R N` with the group ring `R[N.ker]` (`residueQuotientEquiv`), and
likewise as `S`-algebras when `R` is an `S`-algebra (`residueQuotientAlgEquiv`). Both the
embedding `ofKernel` of `R[N.ker]` into `nonnegSubring R N` and the reduction `residueHom` preserve
supports and any grading `gradeBy` on exponents.

Since every element `1 - p` with `p ∈ posIdeal R N` is a unit of `nonnegSubring R N` via its
convergent geometric series (`isUnit_one_sub_of_mem_posIdeal`), a series in `nonnegSubring R N` is
invertible if and only if its zero-period residue is invertible in `R[N.ker]`
(`isUnit_nonnegSubring_iff`). Over a nontrivial ring and any additive monoid `H`, no element of the
positive ideal — and hence no monomial of positive period — is a unit in `nonnegSubring R N`. When
`N` is injective, `N.ker` is trivial and `nonnegSubring R N ⧸ posIdeal R N ≃+* R`
(`residueQuotientEquivOfInjective`, and `residueQuotientAlgEquivOfInjective` as `S`-algebras for a
commutative semiring `S`). In this case, `nonnegSubring R N` is a local ring if and only if `R` is
a local ring (`isLocalRing_nonnegSubring_iff_of_injective`); over a commutative local ring the
maximal ideal consists of series whose constant coefficient lies in `IsLocalRing.maximalIdeal R`,
and over a field `posIdeal R N` is its unique maximal ideal. Over a division ring with injective
`N`, the non-units of `nonnegSubring R N` are precisely `posIdeal R N`.

## Main definitions

* `TauCeti.NovikovSeries.ofKernel`: the inclusion of the kernel group ring `R[N.ker]` into
  `nonnegSubring R N`.
* `TauCeti.NovikovSeries.residueHom`: the zero-period residue ring homomorphism
  `nonnegSubring R N →+* R[N.ker]`.
* `TauCeti.NovikovSeries.residueQuotientEquiv`: the ring isomorphism
  `nonnegSubring R N ⧸ posIdeal R N ≃+* R[N.ker]`.
* `TauCeti.NovikovSeries.residueQuotientEquivOfInjective`: when `N` is injective, the ring
  isomorphism `nonnegSubring R N ⧸ posIdeal R N ≃+* R`.
* `TauCeti.NovikovSeries.ofKernelAlgHom`, `TauCeti.NovikovSeries.residueAlgHom`,
  `TauCeti.NovikovSeries.residueQuotientAlgEquiv`, and
  `TauCeti.NovikovSeries.residueQuotientAlgEquivOfInjective`: the corresponding `S`-algebra maps
  and equivalences for an `S`-algebra `R` over a commutative semiring `S`.

## Main results

* `TauCeti.NovikovSeries.posIdeal_ne_top`, `TauCeti.NovikovSeries.not_isUnit_of_mem_posIdeal`, and
  `TauCeti.NovikovSeries.not_isUnit_single_nonnegSubring`: over a nontrivial ring and any additive
  monoid `H`, `posIdeal R N` is proper and contains no units of `nonnegSubring R N` (in particular,
  no positive-period monomial is a unit).
* `TauCeti.NovikovSeries.residueHom_ofKernel` and `TauCeti.NovikovSeries.residueHom_surjective`:
  `ofKernel` is a right inverse to `residueHom`, so `residueHom` is surjective.
* `TauCeti.NovikovSeries.ker_residueHom`: the kernel of `residueHom` is `posIdeal R N`.
* `TauCeti.NovikovSeries.support_residueHom_subset`,
  `TauCeti.NovikovSeries.ofKernel_mem_supported_iff`,
  `TauCeti.NovikovSeries.residueHom_mem_gradeBy`, and
  `TauCeti.NovikovSeries.ofKernel_mem_gradeBy_iff`:
  zero-period reduction and kernel inclusion are compatible with supports and exponent gradings.
* `TauCeti.NovikovSeries.isUnit_nonnegSubring_iff` and
  `TauCeti.NovikovSeries.isUnit_nonnegSubring_iff_of_injective`: an element of `nonnegSubring R N`
  is a unit if and only if its zero-period residue is a unit of `R[N.ker]` (or its constant
  coefficient is a unit of `R` when `N` is injective).
* `TauCeti.NovikovSeries.isLocalRing_nonnegSubring_iff_of_injective`,
  `TauCeti.NovikovSeries.mem_maximalIdeal_nonnegSubring_iff_of_injective`, and
  `TauCeti.NovikovSeries.maximalIdeal_nonnegSubring_of_injective`: when `N` is injective,
  `nonnegSubring R N` is local iff `R` is local, with maximal ideal pulled back from `R` (equal to
  `posIdeal R N` over a field).

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*}

section PosIdealNonUnits

variable [AddMonoid H] {N : H →+ ℝ} [Ring R]

/-- Over a nontrivial ring, the positive ideal is a proper ideal of `nonnegSubring R N`. -/
theorem posIdeal_ne_top [Nontrivial R] : posIdeal R N ≠ ⊤ := by
  intro htop
  have h1 : (1 : nonnegSubring R N) ∈ posIdeal R N := htop ▸ Submodule.mem_top
  have h0 : ((1 : nonnegSubring R N) : NovikovSeries R H N).coeff 0 = 0 :=
    mem_posIdeal.1 h1 0 (map_zero N).le
  rw [OneMemClass.coe_one, ← single_zero_one, coeff_single_same] at h0
  exact one_ne_zero h0

/-- Over a nontrivial ring, no element of the positive ideal is a unit in `nonnegSubring R N`. -/
theorem not_isUnit_of_mem_posIdeal [Nontrivial R] {a : nonnegSubring R N}
    (ha : a ∈ posIdeal R N) : ¬ IsUnit a := fun hu =>
  posIdeal_ne_top (Ideal.eq_top_of_isUnit_mem (posIdeal R N) ha hu)

/-- Over a nontrivial ring, a monomial of strictly positive period is not a unit in
`nonnegSubring R N`. -/
theorem not_isUnit_single_nonnegSubring [Nontrivial R] {g : H} (hg : 0 < N g) (r : R) :
    ¬ IsUnit (⟨single g r, single_mem_nonnegSubring hg.le r⟩ : nonnegSubring R N) :=
  not_isUnit_of_mem_posIdeal (single_mem_posIdeal hg r)

end PosIdealNonUnits

section Ring

variable [AddGroup H] {N : H →+ ℝ} [Ring R]

variable (R N) in
/-- The inclusion of the kernel group ring `R[N.ker]` into `nonnegSubring R N`: a finitely
supported combination of zero-period exponents is a nonnegative Novikov series. -/
def ofKernel : AddMonoidAlgebra R N.ker →+* nonnegSubring R N :=
  ((ofAddMonoidAlgebra (R := R) (N := N)).comp
      (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype)).codRestrict
    (nonnegSubring R N) fun p => by
      refine mem_nonnegSubring.2 fun h hh => ?_
      rw [RingHom.comp_apply, coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.coeff_mapDomain]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨g, rfl⟩
      exact hh.ne (AddMonoidHom.mem_ker.1 g.2)

/-- Explicit formula for the underlying `NovikovSeries` of `ofKernel R N p`. -/
theorem coe_ofKernel (p : AddMonoidAlgebra R N.ker) :
    (ofKernel R N p : NovikovSeries R H N) =
      ofAddMonoidAlgebra (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype p) :=
  (rfl)

@[simp]
theorem coeff_ofKernel_coe (p : AddMonoidAlgebra R N.ker) (g : N.ker) :
    ((ofKernel R N p : nonnegSubring R N) : NovikovSeries R H N).coeff g = p.coeff g := by
  rw [coe_ofKernel, coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective p.coeff g

theorem coeff_ofKernel_of_notMem (p : AddMonoidAlgebra R N.ker) {h : H} (hh : h ∉ N.ker) :
    ((ofKernel R N p : nonnegSubring R N) : NovikovSeries R H N).coeff h = 0 := by
  rw [coe_ofKernel, coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨g, rfl⟩
  exact hh g.2

@[simp]
theorem ofKernel_single (g : N.ker) (r : R) :
    (ofKernel R N (AddMonoidAlgebra.single g r) : NovikovSeries R H N) = single (g : H) r := by
  simp [coe_ofKernel, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]

/-- Including `R[N.ker]` into `nonnegSubring R N` is injective. -/
theorem ofKernel_injective : Injective (ofKernel R N) := fun p q hpq => by
  ext g
  have h := congrArg (fun a : nonnegSubring R N => (a : NovikovSeries R H N).coeff g) hpq
  simpa only [coeff_ofKernel_coe] using h

/-- The underlying zero-period coefficient map `nonnegSubring R N → R[N.ker]`. -/
private def residueFun (a : nonnegSubring R N) : AddMonoidAlgebra R N.ker :=
  AddMonoidAlgebra.ofCoeff <|
    Finsupp.ofSupportFinite (fun g : N.ker => (a : NovikovSeries R H N).coeff g) <|
      ((a : NovikovSeries R H N).finite_le 0).preimage Subtype.val_injective.injOn |>.subset
        fun g hg => ⟨hg, (AddMonoidHom.mem_ker.1 g.2).le⟩

private theorem coeff_residueFun (a : nonnegSubring R N) (g : N.ker) :
    (residueFun a).coeff g = (a : NovikovSeries R H N).coeff g :=
  congrFun Finsupp.ofSupportFinite_coe g

/-- Subtracting the kernel-ring part of a nonnegative series leaves an element of `posIdeal`. -/
private theorem sub_ofKernel_residueFun_mem_posIdeal (a : nonnegSubring R N) :
    a - ofKernel R N (residueFun a) ∈ posIdeal R N := by
  refine mem_posIdeal.2 fun h hh => ?_
  rw [AddSubgroupClass.coe_sub, coeff_sub]
  rcases hh.lt_or_eq with hlt | heq
  · rw [mem_nonnegSubring.1 a.2 h hlt, mem_nonnegSubring.1 (ofKernel R N _).2 h hlt, sub_self]
  · let g : N.ker := ⟨h, AddMonoidHom.mem_ker.2 heq⟩
    have hg : (g : H) = h := rfl
    rw [← hg, coeff_ofKernel_coe, coeff_residueFun, sub_self]

variable (R N) in
/-- The zero-period residue ring homomorphism `nonnegSubring R N →+* R[N.ker]`, restricting a
nonnegative Novikov series to its coefficients on `N.ker`. -/
def residueHom : nonnegSubring R N →+* AddMonoidAlgebra R N.ker where
  toFun := residueFun
  map_one' := by
    classical
    ext g
    rw [coeff_residueFun, OneMemClass.coe_one, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, coeff_one]
    by_cases hg : g = 0
    · simp [hg]
    · have hg' : (g : H) ≠ 0 := fun h => hg (Subtype.ext h)
      simp [hg, hg']
  map_mul' a b := by
    -- Express `a * b - ofKernel (residueFun a * residueFun b)` in the two-sided ideal `posIdeal`.
    have ha := sub_ofKernel_residueFun_mem_posIdeal a
    have hb := sub_ofKernel_residueFun_mem_posIdeal b
    have hmul : a * b - ofKernel R N (residueFun a * residueFun b) ∈ posIdeal R N := by
      have hdecomp : a * b - ofKernel R N (residueFun a * residueFun b) =
          (a - ofKernel R N (residueFun a)) * b +
            ofKernel R N (residueFun a) * (b - ofKernel R N (residueFun b)) := by
        rw [map_mul, sub_mul, mul_sub]
        abel
      rw [hdecomp]
      exact (posIdeal R N).add_mem (Ideal.mul_mem_right b _ ha) (Ideal.mul_mem_left _ _ hb)
    ext g
    have hzero := mem_posIdeal.1 hmul g (AddMonoidHom.mem_ker.1 g.2).le
    rw [AddSubgroupClass.coe_sub, coeff_sub, sub_eq_zero] at hzero
    rw [coeff_residueFun, hzero, coeff_ofKernel_coe]
  map_zero' := by
    ext g
    simp [coeff_residueFun]
  map_add' a b := by
    ext g
    simp [coeff_residueFun, coeff_add]

@[simp]
theorem coeff_residueHom (a : nonnegSubring R N) (g : N.ker) :
    (residueHom R N a).coeff g = (a : NovikovSeries R H N).coeff g :=
  coeff_residueFun a g

/-- The residue of a zero-period monomial is the corresponding monomial of `R[N.ker]`. -/
@[simp]
theorem residueHom_single_of_mem_ker {g : H} (hg : g ∈ N.ker) (r : R) :
    residueHom R N ⟨single g r, single_mem_nonnegSubring (AddMonoidHom.mem_ker.1 hg).ge r⟩ =
      AddMonoidAlgebra.single ⟨g, hg⟩ r := by
  classical
  ext k
  rw [coeff_residueHom, AddMonoidAlgebra.coeff_single, coeff_single]
  by_cases h : (⟨g, hg⟩ : N.ker) = k
  · subst h
    simp
  · have h' : g ≠ (k : H) := fun hgk => h (Subtype.ext hgk)
    simp [h, h']

/-- The residue of a positive-period monomial is zero. -/
@[simp]
theorem residueHom_single_of_pos {g : H} (hg : 0 < N g) (r : R) :
    residueHom R N ⟨single g r, single_mem_nonnegSubring hg.le r⟩ = 0 := by
  ext k
  rw [coeff_residueHom, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
    coeff_single_of_ne]
  intro hgk
  have hk : N k = 0 := AddMonoidHom.mem_ker.1 k.2
  rw [hgk] at hk
  exact hg.ne' hk

/-- Subtracting the kernel-ring part of a nonnegative series leaves an element of `posIdeal`. -/
theorem sub_ofKernel_residueHom_mem_posIdeal (a : nonnegSubring R N) :
    a - ofKernel R N (residueHom R N a) ∈ posIdeal R N :=
  sub_ofKernel_residueFun_mem_posIdeal a

/-- `ofKernel` is a right inverse to `residueHom`. -/
@[simp]
theorem residueHom_ofKernel (p : AddMonoidAlgebra R N.ker) :
    residueHom R N (ofKernel R N p) = p := by
  ext g
  rw [coeff_residueHom, coeff_ofKernel_coe]

/-- The zero-period residue homomorphism is surjective. -/
theorem residueHom_surjective : Surjective (residueHom R N) :=
  Function.RightInverse.surjective residueHom_ofKernel

variable (R N) in
/-- The kernel of `residueHom` is precisely the positive ideal `posIdeal R N`. -/
theorem ker_residueHom : RingHom.ker (residueHom R N) = posIdeal R N := by
  ext a
  rw [RingHom.mem_ker, mem_posIdeal]
  constructor
  · intro ha h hh
    rcases hh.lt_or_eq with hlt | heq
    · exact mem_nonnegSubring.1 a.2 h hlt
    · have hmem : h ∈ N.ker := AddMonoidHom.mem_ker.2 heq
      have hcoeff := congrArg (fun p : AddMonoidAlgebra R N.ker => p.coeff ⟨h, hmem⟩) ha
      simpa only [coeff_residueHom, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
        Pi.zero_apply] using hcoeff
  · intro ha
    ext g
    rw [coeff_residueHom, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact ha g (AddMonoidHom.mem_ker.1 g.2).le

variable (R N) in
/-- The quotient of `nonnegSubring R N` by `posIdeal R N` is isomorphic as a ring to the kernel
group ring `R[N.ker]`. -/
def residueQuotientEquiv : nonnegSubring R N ⧸ posIdeal R N ≃+* AddMonoidAlgebra R N.ker :=
  (Ideal.quotEquivOfEq (ker_residueHom R N).symm).trans
    (RingHom.quotientKerEquivOfRightInverse (residueHom_ofKernel (R := R) (N := N)))

@[simp]
theorem residueQuotientEquiv_mk (a : nonnegSubring R N) :
    residueQuotientEquiv R N (Ideal.Quotient.mk (posIdeal R N) a) = residueHom R N a :=
  (rfl)

@[simp]
theorem residueQuotientEquiv_symm_apply (p : AddMonoidAlgebra R N.ker) :
    (residueQuotientEquiv R N).symm p = Ideal.Quotient.mk (posIdeal R N) (ofKernel R N p) :=
  (rfl)

section Support

/-- The support of the zero-period residue is the preimage of the support of the series in `N.ker`.
-/
theorem support_residueHom_subset (a : nonnegSubring R N) :
    ((residueHom R N a).coeff.support : Set N.ker) ⊆
      Subtype.val ⁻¹' (a : NovikovSeries R H N).support := by
  intro g hg
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_residueHom] at hg
  exact mem_support.2 hg

/-- A series from `R[N.ker]` is supported in `s` as a Novikov series if and only if its support in
`N.ker` lies in the preimage of `s`. -/
theorem ofKernel_mem_supported_iff {s : Set H} {p : AddMonoidAlgebra R N.ker} :
    (ofKernel R N p : NovikovSeries R H N) ∈ supported R N s ↔
      (p.coeff.support : Set N.ker) ⊆ Subtype.val ⁻¹' s := by
  constructor
  · intro hp g hg
    have hg' : (g : H) ∈ (ofKernel R N p : NovikovSeries R H N).support := by
      rw [mem_support, coeff_ofKernel_coe]
      exact Finsupp.mem_support_iff.1 hg
    exact mem_supported.1 hp hg'
  · intro hp
    refine mem_supported.2 fun h hh => ?_
    by_cases hker : h ∈ N.ker
    · have hg : (⟨h, hker⟩ : N.ker) ∈ p.coeff.support := by
        rw [Finsupp.mem_support_iff, ← coeff_ofKernel_coe (N := N) p ⟨h, hker⟩]
        exact mem_support.1 hh
      exact hp hg
    · exact absurd (coeff_ofKernel_of_notMem p hker) (mem_support.1 hh)

end Support

section Units

/-- A nonnegative Novikov series is a unit of `nonnegSubring R N` if and only if its zero-period
residue is a unit of `R[N.ker]`. -/
theorem isUnit_nonnegSubring_iff {a : nonnegSubring R N} :
    IsUnit a ↔ IsUnit (residueHom R N a) := by
  refine ⟨fun ha => ha.map (residueHom R N), fun hres => ?_⟩
  obtain ⟨u, hu⟩ := hres
  let b : nonnegSubring R N := ofKernel R N (↑u⁻¹ : AddMonoidAlgebra R N.ker)
  have hba : 1 - b * a ∈ posIdeal R N := by
    rw [← ker_residueHom, RingHom.mem_ker, map_sub, map_one, map_mul,
      residueHom_ofKernel, ← hu, Units.inv_mul, sub_self]
  have hab : 1 - a * b ∈ posIdeal R N := by
    rw [← ker_residueHom, RingHom.mem_ker, map_sub, map_one, map_mul,
      residueHom_ofKernel, ← hu, Units.mul_inv, sub_self]
  obtain ⟨ul, hul⟩ : IsUnit (b * a) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_mem_posIdeal hba
  obtain ⟨ur, hur⟩ : IsUnit (a * b) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_mem_posIdeal hab
  refine isUnit_iff_exists_and_exists.2 ⟨⟨b * ↑ur⁻¹, ?_⟩, ⟨↑ul⁻¹ * b, ?_⟩⟩
  · rw [← mul_assoc, ← hur, Units.mul_inv]
  · rw [mul_assoc, ← hul, Units.inv_mul]

end Units

section InjectivePeriod

variable (R N) in
/-- When the period homomorphism is injective, the quotient of `nonnegSubring R N` by
`posIdeal R N` is isomorphic to the coefficient ring `R`. -/
def residueQuotientEquivOfInjective (hN : Injective N) :
    nonnegSubring R N ⧸ posIdeal R N ≃+* R :=
  haveI : Subsingleton N.ker := (N.ker_eq_bot hN).symm ▸ inferInstance
  (residueQuotientEquiv R N).trans (AddMonoidAlgebra.uniqueRingEquiv N.ker)

@[simp]
theorem residueQuotientEquivOfInjective_mk (hN : Injective N) (a : nonnegSubring R N) :
    residueQuotientEquivOfInjective R N hN (Ideal.Quotient.mk (posIdeal R N) a) =
      (a : NovikovSeries R H N).coeff 0 := by
  have : Subsingleton N.ker := (N.ker_eq_bot hN).symm ▸ inferInstance
  rw [residueQuotientEquivOfInjective, RingEquiv.trans_apply, residueQuotientEquiv_mk,
    AddMonoidAlgebra.uniqueRingEquiv_apply, coeff_residueHom, ZeroMemClass.coe_zero]

@[simp]
theorem residueQuotientEquivOfInjective_symm_apply (hN : Injective N) (r : R) :
    (residueQuotientEquivOfInjective R N hN).symm r =
      Ideal.Quotient.mk (posIdeal R N)
        ⟨single 0 r, single_mem_nonnegSubring (map_zero N).ge r⟩ := by
  have : Subsingleton N.ker := (N.ker_eq_bot hN).symm ▸ inferInstance
  rw [residueQuotientEquivOfInjective, RingEquiv.symm_trans_apply,
    AddMonoidAlgebra.uniqueRingEquiv_symm_apply, residueQuotientEquiv_symm_apply]
  congr 1
  exact Subtype.ext (by simp)

/-- When the period homomorphism is injective, the kernel group ring is isomorphic to `R`, so a
nonnegative series is a unit of `nonnegSubring R N` if and only if its constant coefficient is a
unit of `R`. -/
theorem isUnit_nonnegSubring_iff_of_injective (hN : Injective N) {a : nonnegSubring R N} :
    IsUnit a ↔ IsUnit ((a : NovikovSeries R H N).coeff 0) := by
  have : Subsingleton N.ker := (N.ker_eq_bot hN).symm ▸ inferInstance
  rw [isUnit_nonnegSubring_iff,
    ← MulEquiv.isUnit_map (f := (AddMonoidAlgebra.uniqueRingEquiv (R := R) N.ker).toMulEquiv)]
  simp [AddMonoidAlgebra.uniqueRingEquiv_apply]

end InjectivePeriod

end Ring

section Grading

variable [AddGroup H] {N : H →+ ℝ} [CommRing R] {ι : Type*}

/-- Zero-period reduction preserves homogeneous degrees of exponents. -/
theorem residueHom_mem_gradeBy {f : H → ι} {i : ι} {a : nonnegSubring R N}
    (ha : (a : NovikovSeries R H N) ∈ gradeBy R N f i) :
    residueHom R N a ∈ AddMonoidAlgebra.gradeBy R (fun g : N.ker => f g) i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  exact fun g hg => mem_gradeBy_iff.1 ha (support_residueHom_subset a hg)

/-- The kernel-ring inclusion preserves and reflects homogeneous degrees of exponents. -/
theorem ofKernel_mem_gradeBy_iff {f : H → ι} {i : ι} {p : AddMonoidAlgebra R N.ker} :
    (ofKernel R N p : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      p ∈ AddMonoidAlgebra.gradeBy R (fun g : N.ker => f g) i := by
  rw [mem_gradeBy_iff, ← mem_supported, ofKernel_mem_supported_iff,
    AddMonoidAlgebra.mem_gradeBy_iff]
  rfl

end Grading

section LocalRing

variable [AddGroup H] {N : H →+ ℝ} [Ring R]

/-- When the period homomorphism is injective, `nonnegSubring R N` is a local ring if and only if
`R` is a local ring. -/
theorem isLocalRing_nonnegSubring_iff_of_injective (hN : Injective N) :
    IsLocalRing (nonnegSubring R N) ↔ IsLocalRing R := by
  constructor
  · intro hloc
    have hnt : Nontrivial R := (subsingleton_or_nontrivial R).resolve_left fun _ =>
      have : Subsingleton (nonnegSubring R N) :=
        ⟨fun _ _ => Subtype.ext (NovikovSeries.ext fun _ => Subsingleton.elim _ _)⟩
      false_of_nontrivial_of_subsingleton (nonnegSubring R N)
    refine IsLocalRing.of_nonunits_add fun r s hr hs => ?_
    let a : nonnegSubring R N := ⟨single 0 r, single_mem_nonnegSubring (map_zero N).ge r⟩
    let b : nonnegSubring R N := ⟨single 0 s, single_mem_nonnegSubring (map_zero N).ge s⟩
    have ha : a ∈ nonunits (nonnegSubring R N) := by
      simpa [a, mem_nonunits_iff, isUnit_nonnegSubring_iff_of_injective hN] using hr
    have hb : b ∈ nonunits (nonnegSubring R N) := by
      simpa [b, mem_nonunits_iff, isUnit_nonnegSubring_iff_of_injective hN] using hs
    have hab := IsLocalRing.nonunits_add ha hb
    simpa [a, b, mem_nonunits_iff, isUnit_nonnegSubring_iff_of_injective hN,
      AddMemClass.coe_add, coeff_add] using hab
  · intro hloc
    have : Nontrivial (nonnegSubring R N) := inferInstance
    refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
    rw [mem_nonunits_iff, isUnit_nonnegSubring_iff_of_injective hN] at ha hb ⊢
    rw [AddMemClass.coe_add, coeff_add]
    exact IsLocalRing.nonunits_add ha hb

/-- Over a local ring with injective period homomorphism, the nonnegative subring is a local ring.
-/
theorem isLocalRing_nonnegSubring_of_injective [IsLocalRing R] (hN : Injective N) :
    IsLocalRing (nonnegSubring R N) :=
  (isLocalRing_nonnegSubring_iff_of_injective hN).2 ‹_›

/-- Over a local ring `R`, the nonnegative real Novikov subring is a local ring. -/
instance isLocalRing_nonnegSubring_real [IsLocalRing R] :
    IsLocalRing (nonnegSubring R (AddMonoidHom.id ℝ)) :=
  isLocalRing_nonnegSubring_of_injective injective_id

end LocalRing

section CommLocalRing

variable [AddCommGroup H] {N : H →+ ℝ} [CommRing R]

/-- Over a commutative local ring with injective period homomorphism, an element of
`nonnegSubring R N` belongs to its maximal ideal if and only if its constant coefficient lies in
`IsLocalRing.maximalIdeal R`. -/
theorem mem_maximalIdeal_nonnegSubring_iff_of_injective [IsLocalRing R] (hN : Injective N)
    [IsLocalRing (nonnegSubring R N)] {a : nonnegSubring R N} :
    a ∈ IsLocalRing.maximalIdeal (nonnegSubring R N) ↔
      (a : NovikovSeries R H N).coeff 0 ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_nonnegSubring_iff_of_injective hN]

end CommLocalRing

section DivisionRing

variable [AddGroup H] {N : H →+ ℝ} [DivisionRing R]

/-- Over a division ring with injective period homomorphism, a nonnegative series is a non-unit if
and only if it lies in the positive ideal. -/
theorem mem_posIdeal_iff_not_isUnit_of_injective (hN : Injective N) {a : nonnegSubring R N} :
    a ∈ posIdeal R N ↔ ¬ IsUnit a := by
  rw [isUnit_nonnegSubring_iff_of_injective hN, isUnit_iff_ne_zero, not_not, mem_posIdeal]
  refine ⟨fun ha => ha 0 (map_zero N).le, fun ha h hh => ?_⟩
  rcases hh.lt_or_eq with hlt | heq
  · exact mem_nonnegSubring.1 a.2 h hlt
  · have h0 : h = 0 := hN (heq.trans (map_zero N).symm)
    rwa [h0]

end DivisionRing

section Field

variable [AddCommGroup H] {N : H →+ ℝ} [Field R]

/-- Over a field and an abelian group with injective period homomorphism, the unique maximal ideal
of `nonnegSubring R N` is `posIdeal R N`. -/
theorem maximalIdeal_nonnegSubring_of_injective (hN : Injective N)
    [IsLocalRing (nonnegSubring R N)] :
    IsLocalRing.maximalIdeal (nonnegSubring R N) = posIdeal R N := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_posIdeal_iff_not_isUnit_of_injective hN]

end Field

end NovikovSeries

section Algebra

namespace NovikovSeries

variable (S : Type*) [CommSemiring S] (R : Type*) [Ring R] [Algebra S R]
  {H : Type*} [AddGroup H] (N : H →+ ℝ)

/-- The kernel-ring inclusion as an `S`-algebra homomorphism. -/
def ofKernelAlgHom : AddMonoidAlgebra R N.ker →ₐ[S] nonnegSubring R N where
  __ := ofKernel R N
  commutes' s := Subtype.ext <| by
    rw [RingHom.toFun_eq_coe, coe_ofKernel, AddMonoidAlgebra.coe_algebraMap,
      Function.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.mapDomain_single, ofAddMonoidAlgebra_single, map_zero,
      coe_algebraMap_nonnegSubring, algebraMap_apply]

@[simp]
theorem ofKernelAlgHom_toRingHom :
    (ofKernelAlgHom S R N : AddMonoidAlgebra R N.ker →+* nonnegSubring R N) = ofKernel R N :=
  (rfl)

@[simp]
theorem ofKernelAlgHom_apply (p : AddMonoidAlgebra R N.ker) :
    ofKernelAlgHom S R N p = ofKernel R N p :=
  (rfl)

/-- The zero-period residue homomorphism as an `S`-algebra homomorphism. -/
def residueAlgHom : nonnegSubring R N →ₐ[S] AddMonoidAlgebra R N.ker where
  __ := residueHom R N
  commutes' s := by
    rw [RingHom.toFun_eq_coe, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply]
    have h0 : (0 : H) ∈ N.ker := N.ker.zero_mem
    have hs : algebraMap S (nonnegSubring R N) s =
        ⟨single 0 (algebraMap S R s), single_mem_nonnegSubring (map_zero N).ge _⟩ :=
      Subtype.ext (by rw [coe_algebraMap_nonnegSubring, algebraMap_apply])
    rw [hs]
    exact residueHom_single_of_mem_ker h0 (algebraMap S R s)

@[simp]
theorem residueAlgHom_toRingHom :
    (residueAlgHom S R N : nonnegSubring R N →+* AddMonoidAlgebra R N.ker) = residueHom R N :=
  (rfl)

@[simp]
theorem residueAlgHom_apply (a : nonnegSubring R N) :
    residueAlgHom S R N a = residueHom R N a :=
  (rfl)

/-- The quotient of `nonnegSubring R N` by `posIdeal R N` is isomorphic as an `S`-algebra to the
kernel group ring `R[N.ker]`. -/
def residueQuotientAlgEquiv :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[S] AddMonoidAlgebra R N.ker :=
  (Ideal.quotientEquivAlgOfEq S (ker_residueHom R N).symm).trans
    (Ideal.quotientKerAlgEquivOfRightInverse (f := residueAlgHom S R N)
      (residueHom_ofKernel (R := R) (N := N)))

@[simp]
theorem residueQuotientAlgEquiv_mk (a : nonnegSubring R N) :
    residueQuotientAlgEquiv S R N (Ideal.Quotient.mk (posIdeal R N) a) = residueHom R N a :=
  (rfl)

@[simp]
theorem residueQuotientAlgEquiv_symm_apply (p : AddMonoidAlgebra R N.ker) :
    (residueQuotientAlgEquiv S R N).symm p = Ideal.Quotient.mk (posIdeal R N) (ofKernel R N p) :=
  (rfl)

/-- When the period homomorphism is injective, the quotient of `nonnegSubring R N` by
`posIdeal R N` is isomorphic as an `S`-algebra to `R`. -/
def residueQuotientAlgEquivOfInjective (hN : Injective N) :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[S] R :=
  haveI : Subsingleton N.ker := (N.ker_eq_bot hN).symm ▸ inferInstance
  (residueQuotientAlgEquiv S R N).trans (AddMonoidAlgebra.uniqueAlgEquiv S N.ker)

@[simp]
theorem residueQuotientAlgEquivOfInjective_mk (hN : Injective N) (a : nonnegSubring R N) :
    residueQuotientAlgEquivOfInjective S R N hN (Ideal.Quotient.mk (posIdeal R N) a) =
      (a : NovikovSeries R H N).coeff 0 :=
  residueQuotientEquivOfInjective_mk hN a

@[simp]
theorem residueQuotientAlgEquivOfInjective_symm_apply (hN : Injective N) (r : R) :
    (residueQuotientAlgEquivOfInjective S R N hN).symm r =
      Ideal.Quotient.mk (posIdeal R N)
        ⟨single 0 r, single_mem_nonnegSubring (map_zero N).ge r⟩ :=
  residueQuotientEquivOfInjective_symm_apply hN r

end NovikovSeries

end Algebra

end TauCeti
