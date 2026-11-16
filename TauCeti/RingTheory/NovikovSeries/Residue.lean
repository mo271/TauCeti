/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.Grading

/-!
# Period-zero residue ring of nonnegative Novikov series

Every series `a` in the nonnegative subring `Nov≥0(R, H, N)` is supported in periods `N h ≥ 0`, and
by the Novikov finiteness condition below cutoff `1` it has only finitely many nonzero coefficients
at exponents of period `0`. Retaining the coefficients on the kernel `ker N` therefore defines a
finitely supported element of the group ring `R[ker N]`.

Because two nonnegative real numbers adding up to `0` are both `0`, no pair of exponents of strictly
positive period can contribute to a convolution sum at an exponent of period `0`. Retaining the
period-zero coefficients is therefore a ring homomorphism
`residueRingHom : Nov≥0(R, H, N) →+* R[ker N]`, split by the canonical inclusion
`ofKerAddMonoidAlgebra : R[ker N] →+* Nov≥0(R, H, N)` of finitely supported period-zero series. The
kernel of `residueRingHom` is the ideal `posIdeal R N` of series supported in strictly positive
periods, yielding the canonical ring (and algebra) isomorphism
`Nov≥0(R, H, N) ⧸ posIdeal R N ≃+* R[ker N]`. When `ker N` is trivial — for instance when `N` is
injective — composing with `AddMonoidAlgebra.uniqueRingEquiv` identifies the residue ring with `R`.

## Main definitions

* `TauCeti.NovikovSeries.residueRingHom`: the period-zero projection
  `Nov≥0(R, H, N) →+* R[ker N]`, and `TauCeti.NovikovSeries.residueAlgHom`: its `A`-algebra
  enhancement.
* `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra`: the right-inverse inclusion
  `R[ker N] →+* Nov≥0(R, H, N)` of finitely supported period-zero series, and
  `TauCeti.NovikovSeries.ofKerAddMonoidAlgebraAlgHom`: its `A`-algebra enhancement.
* `TauCeti.NovikovSeries.quotientPosIdealEquiv`: the canonical ring isomorphism
  `Nov≥0(R, H, N) ⧸ posIdeal R N ≃+* R[ker N]`, and
  `TauCeti.NovikovSeries.quotientPosIdealAlgEquiv`: its `A`-algebra enhancement.
* `TauCeti.NovikovSeries.quotientPosIdealEquivSelf`: the residue ring isomorphism
  `Nov≥0(R, H, N) ⧸ posIdeal R N ≃+* R` when `ker N` is trivial.

## Main results

* `TauCeti.NovikovSeries.periodIdeal_le_posIdeal` and `TauCeti.NovikovSeries.isClosed_posIdeal`:
  every positive cutoff ideal lies in `posIdeal R N`, and `posIdeal R N` is closed in the period
  topology.
* `TauCeti.NovikovSeries.residueRingHom_ofKerAddMonoidAlgebra` and
  `TauCeti.NovikovSeries.ker_residueRingHom`: `ofKerAddMonoidAlgebra` is a section of
  `residueRingHom`, and the kernel of `residueRingHom` is `posIdeal R N`.
* `TauCeti.NovikovSeries.sub_ofKerAddMonoidAlgebra_residueRingHom_mem_posIdeal`: every nonnegative
  Novikov series differs from its period-zero part by an element of `posIdeal R N`.
* `TauCeti.NovikovSeries.residueRingHom_mem_gradeBy` and
  `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra_mem_nonnegGradeBy_iff`: compatibility of the
  period-zero projection and section with homogeneous gradings.
* `TauCeti.NovikovSeries.residueRingHom_mapNonnegSubring`: functoriality of the period-zero
  projection under period-rescaling pushforwards.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46, 2009, Chapter 2.
* H. Hofer, D. Salamon, *Floer homology and Novikov rings*, The Floer Memorial Volume,
  Birkhäuser 1995, Section 4.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Function Set

namespace TauCeti.NovikovSeries

variable {A R S H H' ι : Type*}

section PosIdeal

variable [Ring R] [AddMonoid H] {N : H →+ ℝ}

/-- Every cutoff ideal at a strictly positive period threshold is contained in the positive
ideal. -/
theorem periodIdeal_le_posIdeal {C : ℝ} (hC : 0 < C) :
    periodIdeal R N C ≤ posIdeal R N := fun _ ha =>
  mem_posIdeal.2 fun h hh => mem_periodFiltration.1 (mem_periodIdeal.1 ha) h (hh.trans_lt hC)

/-- The positive ideal is closed in the nonnegative subring for the period topology. -/
theorem isClosed_posIdeal : IsClosed (posIdeal R N : Set (nonnegSubring R N)) := by
  have hset : (posIdeal R N : Set (nonnegSubring R N)) =
      ⋂ h ∈ ({h : H | N h ≤ 0} : Set H),
        Subtype.val ⁻¹' {b : NovikovSeries R H N | b.coeff h = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_posIdeal, mem_iInter]
    rfl
  rw [hset]
  exact isClosed_biInter fun h _ =>
    ((isLocallyConstant_coeff h).isClosed_fiber 0).preimage continuous_subtype_val

end PosIdeal

section Ring

variable [Ring R] [AddGroup H] {N : H →+ ℝ}

/-- Every Novikov series has only finitely many nonzero coefficients on `ker N`, since every
exponent in `ker N` has period `0 < 1`. -/
theorem finite_support_ker (a : NovikovSeries R H N) :
    {k : N.ker | a.coeff k ≠ 0}.Finite :=
  ((a.finite_lt 1).preimage N.ker.subtype_injective.injOn).subset fun k hk =>
    ⟨hk, by simp [AddMonoidHom.mem_ker.1 k.2]⟩

/-- The finitely supported coefficient function of a Novikov series restricted to `ker N`. -/
private def residueFinsupp (a : NovikovSeries R H N) : N.ker →₀ R :=
  Finsupp.ofSupportFinite (fun k : N.ker => a.coeff k) (finite_support_ker a)

@[simp]
private theorem residueFinsupp_apply (a : NovikovSeries R H N) (k : N.ker) :
    residueFinsupp a k = a.coeff k :=
  congrFun Finsupp.ofSupportFinite_coe k

variable (R N) in
/-- **Period-zero projection.** Retaining the coefficients on `ker N` is a ring homomorphism from
the nonnegative Novikov subring onto the group ring `R[ker N]`: no pair of strictly positive periods
can sum to `0`. -/
def residueRingHom : nonnegSubring R N →+* AddMonoidAlgebra R N.ker where
  toFun a := AddMonoidAlgebra.ofCoeff (residueFinsupp (a : NovikovSeries R H N))
  map_zero' := AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => by simp
  map_add' a b := AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => by simp [coeff_add]
  map_one' := AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => by
    rw [AddMonoidAlgebra.coeff_ofCoeff, residueFinsupp_apply, Subring.coe_one, one_def,
      AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    by_cases hk : k = 0
    · subst hk
      rw [AddSubgroup.coe_zero, coeff_single_same, Finsupp.single_eq_same]
    · have hkH : (k : H) ≠ 0 := mt (fun h => Subtype.ext h) hk
      rw [coeff_single_of_ne hkH, Finsupp.single_eq_of_ne hk]
  map_mul' a b := by
    classical
    refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun k => ?_)
    rw [AddMonoidAlgebra.coeff_ofCoeff, residueFinsupp_apply, Subring.coe_mul]
    set F := ((residueFinsupp (a : NovikovSeries R H N)).support ×ˢ
        (residueFinsupp (b : NovikovSeries R H N)).support).filter fun p => p.1 + p.2 = k
    rw [coeff_mul_eq_sum_of_injOn (F := F) (f := fun p : N.ker × N.ker => ((p.1 : H), (p.2 : H)))
      (fun p hp => by
        have hpk := (Finset.mem_filter.1 hp).2
        exact congrArg Subtype.val hpk)
      (fun u v huv hua hvb => ?_)
      (fun p _ q _ hpq => by
        simp only [Prod.mk.injEq] at hpq
        exact Prod.ext (Subtype.ext hpq.1) (Subtype.ext hpq.2))]
    · rw [Finset.sum_filter, Finset.sum_product, AddMonoidAlgebra.coeff_mul]
      simp [Finsupp.sum]
    · have hu0 : 0 ≤ N u := by_contra fun hlt => hua (mem_nonnegSubring.1 a.2 u (lt_of_not_ge hlt))
      have hv0 : 0 ≤ N v := by_contra fun hlt => hvb (mem_nonnegSubring.1 b.2 v (lt_of_not_ge hlt))
      have hsum : N u + N v = 0 := by
        rw [← map_add, huv]
        exact AddMonoidHom.mem_ker.1 k.2
      have huk : u ∈ N.ker := AddMonoidHom.mem_ker.2 (le_antisymm (by linarith) hu0)
      have hvk : v ∈ N.ker := AddMonoidHom.mem_ker.2 (le_antisymm (by linarith) hv0)
      refine ⟨(⟨u, huk⟩, ⟨v, hvk⟩), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩,
        Subtype.ext huv⟩, rfl⟩
      · exact Finsupp.mem_support_iff.2 hua
      · exact Finsupp.mem_support_iff.2 hvb

@[simp]
theorem coeff_residueRingHom (a : nonnegSubring R N) (k : N.ker) :
    (residueRingHom R N a).coeff k = (a : NovikovSeries R H N).coeff k :=
  (rfl)

@[simp]
theorem residueRingHom_single_of_mem_ker {g : H} (hg : g ∈ N.ker) (r : R) :
    residueRingHom R N ⟨single g r, single_mem_nonnegSubring (AddMonoidHom.mem_ker.1 hg).ge r⟩ =
      AddMonoidAlgebra.single ⟨g, hg⟩ r := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun k => ?_)
  rw [coeff_residueRingHom, AddMonoidAlgebra.coeff_single]
  by_cases hk : k = ⟨g, hg⟩
  · subst hk
    simp
  · have hkg : (k : H) ≠ g := fun e => hk (Subtype.ext e)
    rw [coeff_single_of_ne hkg, Finsupp.single_eq_of_ne hk]

@[simp]
theorem residueRingHom_single_of_pos {g : H} (hg : 0 < N g) (r : R) :
    residueRingHom R N ⟨single g r, single_mem_nonnegSubring hg.le r⟩ = 0 := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun k => ?_)
  rw [coeff_residueRingHom, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  refine coeff_single_of_ne (fun hkg => ?_) r
  have hk0 : N k = 0 := AddMonoidHom.mem_ker.1 k.2
  rw [hkg] at hk0
  exact hg.ne' hk0

variable (R N) in
/-- **Period-zero section.** The group ring `R[ker N]` embeds into the nonnegative Novikov subring
as the finitely supported series supported in period `0`. -/
def ofKerAddMonoidAlgebra : AddMonoidAlgebra R N.ker →+* nonnegSubring R N :=
  ((ofAddMonoidAlgebra (R := R) (N := N)).comp
    (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype)).codRestrict (nonnegSubring R N) fun x =>
    mem_nonnegSubring.2 fun h hh => by
      simp only [RingHom.comp_apply, coeff_ofAddMonoidAlgebra,
        AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
      refine Finsupp.mapDomain_of_notMem_range _ _ fun ⟨k, hk⟩ => ?_
      have hk0 : N k = 0 := AddMonoidHom.mem_ker.1 k.2
      rw [← AddSubgroup.subtype_apply, hk] at hk0
      exact hh.ne hk0

@[simp]
theorem coe_ofKerAddMonoidAlgebra (x : AddMonoidAlgebra R N.ker) :
    (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N) =
      ofAddMonoidAlgebra (AddMonoidAlgebra.mapDomain N.ker.subtype x) :=
  (rfl)

theorem coeff_ofKerAddMonoidAlgebra_of_notMem (x : AddMonoidAlgebra R N.ker) {h : H}
    (hh : h ∉ N.ker) : (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N).coeff h = 0 := by
  rw [coe_ofKerAddMonoidAlgebra, coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range _ _ fun ⟨k, hk⟩ => hh (hk ▸ k.2)

@[simp]
theorem ofKerAddMonoidAlgebra_single (k : N.ker) (r : R) :
    ofKerAddMonoidAlgebra R N (AddMonoidAlgebra.single k r) =
      ⟨single (k : H) r, single_mem_nonnegSubring (AddMonoidHom.mem_ker.1 k.2).ge r⟩ := by
  ext h
  simp [coe_ofKerAddMonoidAlgebra]

/-- The inclusion `ofKerAddMonoidAlgebra` is a right inverse to `residueRingHom`. -/
theorem residueRingHom_ofKerAddMonoidAlgebra :
    RightInverse (ofKerAddMonoidAlgebra R N) (residueRingHom R N) := fun x =>
  AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => by simp

@[simp]
theorem residueRingHom_comp_ofKerAddMonoidAlgebra :
    (residueRingHom R N).comp (ofKerAddMonoidAlgebra R N) = RingHom.id _ :=
  RingHom.ext residueRingHom_ofKerAddMonoidAlgebra

theorem residueRingHom_surjective : Surjective (residueRingHom R N) :=
  residueRingHom_ofKerAddMonoidAlgebra.surjective

theorem ofKerAddMonoidAlgebra_injective : Injective (ofKerAddMonoidAlgebra R N) :=
  residueRingHom_ofKerAddMonoidAlgebra.injective

/-- The kernel of the period-zero projection is the positive ideal `posIdeal R N`. -/
@[simp]
theorem ker_residueRingHom : RingHom.ker (residueRingHom R N) = posIdeal R N := by
  ext a
  rw [RingHom.mem_ker, mem_posIdeal]
  constructor
  · intro ha h hh
    rcases hh.lt_or_eq with hlt | heq
    · exact mem_nonnegSubring.1 a.2 h hlt
    · have hk : h ∈ N.ker := AddMonoidHom.mem_ker.2 heq
      rw [← coeff_residueRingHom a ⟨h, hk⟩, ha, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro ha
    refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun k => ?_)
    rw [coeff_residueRingHom, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact ha k (AddMonoidHom.mem_ker.1 k.2).le

/-- **Zero-energy reduction.** Every nonnegative Novikov series differs from its period-zero part by
an element of `posIdeal R N`. -/
theorem sub_ofKerAddMonoidAlgebra_residueRingHom_mem_posIdeal (a : nonnegSubring R N) :
    a - ofKerAddMonoidAlgebra R N (residueRingHom R N a) ∈ posIdeal R N := by
  rw [← ker_residueRingHom, RingHom.mem_ker, map_sub,
    residueRingHom_ofKerAddMonoidAlgebra (residueRingHom R N a), sub_self]

variable (R N) in
/-- **Residue ring of nonnegative Novikov series.** Quotienting the nonnegative subring by the ideal
of strictly positive periods yields the group ring of period-zero exponents `R[ker N]`. -/
def quotientPosIdealEquiv : (nonnegSubring R N ⧸ posIdeal R N) ≃+* AddMonoidAlgebra R N.ker :=
  (Ideal.quotEquivOfEq (ker_residueRingHom (R := R) (N := N)).symm).trans <|
    RingHom.quotientKerEquivOfRightInverse residueRingHom_ofKerAddMonoidAlgebra

@[simp]
theorem quotientPosIdealEquiv_mk (a : nonnegSubring R N) :
    quotientPosIdealEquiv R N (Ideal.Quotient.mk (posIdeal R N) a) = residueRingHom R N a :=
  (rfl)

@[simp]
theorem quotientPosIdealEquiv_symm (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealEquiv R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) :=
  (rfl)

variable (R N) in
/-- When `ker N` is trivial (for instance when `N` is injective), the residue ring
`Nov≥0(R, H, N) ⧸ posIdeal R N` is canonically isomorphic to the coefficient ring `R`. -/
def quotientPosIdealEquivSelf [Subsingleton N.ker] :
    (nonnegSubring R N ⧸ posIdeal R N) ≃+* R :=
  (quotientPosIdealEquiv R N).trans (AddMonoidAlgebra.uniqueRingEquiv N.ker)

@[simp]
theorem quotientPosIdealEquivSelf_mk [Subsingleton N.ker] (a : nonnegSubring R N) :
    quotientPosIdealEquivSelf R N (Ideal.Quotient.mk (posIdeal R N) a) =
      (a : NovikovSeries R H N).coeff 0 := by
  simp [quotientPosIdealEquivSelf]

@[simp]
theorem quotientPosIdealEquivSelf_symm [Subsingleton N.ker] (r : R) :
    (quotientPosIdealEquivSelf R N).symm r =
      Ideal.Quotient.mk (posIdeal R N)
        ⟨single 0 r, single_mem_nonnegSubring (map_zero N).ge r⟩ := by
  simp [quotientPosIdealEquivSelf]

end Ring

section Algebra

variable (A R) [CommSemiring A] [Ring R] [Algebra A R] [AddGroup H]

/-- The period-zero projection `Nov≥0(R, H, N) →ₐ[A] R[ker N]` as an `A`-algebra homomorphism. -/
def residueAlgHom (N : H →+ ℝ) : nonnegSubring R N →ₐ[A] AddMonoidAlgebra R N.ker where
  __ := residueRingHom R N
  commutes' s := by
    have hs : algebraMap A (nonnegSubring R N) s =
        ⟨single 0 (algebraMap A R s), single_mem_nonnegSubring (map_zero N).ge _⟩ :=
      Subtype.ext (by simp [algebraMap_apply])
    rw [RingHom.toFun_eq_coe, hs, residueRingHom_single_of_mem_ker N.ker.zero_mem]
    rfl

@[simp]
theorem coe_residueAlgHom (N : H →+ ℝ) : ⇑(residueAlgHom A R N) = residueRingHom R N :=
  (rfl)

/-- The period-zero section `R[ker N] →ₐ[A] Nov≥0(R, H, N)` as an `A`-algebra homomorphism. -/
def ofKerAddMonoidAlgebraAlgHom (N : H →+ ℝ) :
    AddMonoidAlgebra R N.ker →ₐ[A] nonnegSubring R N where
  __ := ofKerAddMonoidAlgebra R N
  commutes' s := by
    ext h
    simp [algebraMap_apply]

@[simp]
theorem coe_ofKerAddMonoidAlgebraAlgHom (N : H →+ ℝ) :
    ⇑(ofKerAddMonoidAlgebraAlgHom A R N) = ofKerAddMonoidAlgebra R N :=
  (rfl)

/-- The canonical `A`-algebra isomorphism `Nov≥0(R, H, N) ⧸ posIdeal R N ≃ₐ[A] R[ker N]`. -/
def quotientPosIdealAlgEquiv (N : H →+ ℝ) :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[A] AddMonoidAlgebra R N.ker :=
  (Ideal.quotientEquivAlgOfEq A (ker_residueRingHom (R := R) (N := N)).symm).trans <|
    Ideal.quotientKerAlgEquivOfRightInverse (f := residueAlgHom A R N)
      (g := ofKerAddMonoidAlgebraAlgHom A R N) residueRingHom_ofKerAddMonoidAlgebra

@[simp]
theorem quotientPosIdealAlgEquiv_mk {N : H →+ ℝ} (a : nonnegSubring R N) :
    quotientPosIdealAlgEquiv A R N (Ideal.Quotient.mk (posIdeal R N) a) = residueRingHom R N a :=
  (rfl)

@[simp]
theorem quotientPosIdealAlgEquiv_symm {N : H →+ ℝ} (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealAlgEquiv A R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) :=
  (rfl)

end Algebra

section Grading

variable [CommRing R] [AddGroup H] {N : H →+ ℝ}

/-- The period-zero projection preserves homogeneous degrees. -/
theorem residueRingHom_mem_gradeBy {f : H → ι} {i : ι} {a : nonnegSubring R N}
    (ha : a ∈ nonnegGradeBy R N f i) :
    residueRingHom R N a ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro k hk
  exact mem_gradeBy_iff.1 (mem_nonnegGradeBy_iff.1 ha)
    (mem_support.2 (Finsupp.mem_support_iff.1 hk))

/-- The period-zero section preserves and reflects homogeneous degrees. -/
theorem ofKerAddMonoidAlgebra_mem_nonnegGradeBy_iff {f : H → ι} {i : ι}
    {x : AddMonoidAlgebra R N.ker} :
    ofKerAddMonoidAlgebra R N x ∈ nonnegGradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  classical
  rw [mem_nonnegGradeBy_iff, coe_ofKerAddMonoidAlgebra, ofAddMonoidAlgebra_mem_gradeBy_iff,
    AddMonoidAlgebra.mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff]
  constructor
  · intro hx k hk
    have hm : (k : H) ∈ (AddMonoidAlgebra.mapDomain N.ker.subtype x).coeff.support := by
      rw [AddMonoidAlgebra.coeff_mapDomain, Finsupp.mem_support_iff]
      exact (Finsupp.mapDomain_apply_of_injective N.ker.subtype_injective x.coeff k).symm ▸
        Finsupp.mem_support_iff.1 hk
    exact hx hm
  · intro hx h hh
    rw [AddMonoidAlgebra.coeff_mapDomain] at hh
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hh)
    exact hx hk

end Grading

section Functoriality

variable [Ring R] [Ring S] [AddGroup H] [AddGroup H'] {N : H →+ ℝ} {N' : H' →+ ℝ}

/-- An exponent homomorphism `φ` rescaling periods by a positive constant restricts to a
homomorphism `ker N →+ ker N'`. -/
def restrictKer (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) : N.ker →+ N'.ker :=
  (φ.comp N.ker.subtype).codRestrict N'.ker fun k => by
    obtain ⟨c, _, hcφ⟩ := hφ
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, hcφ,
      AddMonoidHom.mem_ker.1 k.2, mul_zero]

@[simp]
theorem coe_restrictKer_apply (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (k : N.ker) :
    (restrictKer φ hφ k : H') = φ k :=
  (rfl)

/-- **Functoriality of the period-zero projection.** Pushing forward a nonnegative Novikov series
along `(ρ, φ)` and taking its period-zero residue agrees with pushing forward its period-zero
residue along `ρ` and `restrictKer φ`. -/
theorem residueRingHom_mapNonnegSubring (ρ : R →+* S) (φ : H →+ H')
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (a : nonnegSubring R N) :
    residueRingHom S N' (mapNonnegSubring ρ φ hφ a) =
      AddMonoidAlgebra.mapDomain (restrictKer φ hφ)
        (AddMonoidAlgebra.mapRingHom N.ker ρ (residueRingHom R N a)) := by
  classical
  obtain ⟨c, hc, hcφ⟩ := hφ
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun k' => ?_)
  rw [coeff_residueRingHom, coe_mapNonnegSubring, AddMonoidAlgebra.coeff_mapDomain,
    Finsupp.mapDomain_apply, Finsupp.sum]
  set F := (residueFinsupp (a : NovikovSeries R H N)).support.filter
    fun k => restrictKer φ ⟨c, hc, hcφ⟩ k = k'
  have hsupp : ∀ h, (a : NovikovSeries R H N).coeff h ≠ 0 → φ h = k' → h ∈ N.ker :=
    fun h _ hφh => by
      have hN' : N' (φ h) = 0 := by
        rw [hφh]
        exact AddMonoidHom.mem_ker.1 k'.2
      rw [hcφ] at hN'
      exact AddMonoidHom.mem_ker.2 ((mul_eq_zero.1 hN').resolve_left hc.ne')
  rw [coeff_map_eq_sum (ρ : R →+ S) φ ⟨c, hc, hcφ⟩ (a : NovikovSeries R H N)
    (F.image N.ker.subtype)
    (fun h ⟨hh, hφh⟩ => Finset.mem_image.2
      ⟨⟨h, hsupp h (mem_support.1 hh) hφh⟩, Finset.mem_filter.2
        ⟨Finsupp.mem_support_iff.2 (mem_support.1 hh), Subtype.ext hφh⟩, rfl⟩)
    (fun h hh => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hh
      exact congrArg Subtype.val (Finset.mem_filter.1 hk).2),
    Finset.sum_image (fun k₁ _ k₂ _ h12 => N.ker.subtype_injective h12)]
  simp only [AddMonoidAlgebra.coeff_mapRingHom, coeff_residueRingHom, AddSubgroup.subtype_apply,
    Finsupp.single_apply]
  rw [← Finset.sum_filter (p := fun k => restrictKer φ ⟨c, hc, hcφ⟩ k = k')]
  refine (Finset.sum_subset (fun k hk => ?_) (fun k hF hnot => ?_)).symm
  · obtain ⟨hmem, hk'⟩ := Finset.mem_filter.1 hk
    refine Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 fun h0 => ?_, hk'⟩
    rw [residueFinsupp_apply] at h0
    have hρ0 := Finsupp.mem_support_iff.1 hmem
    rw [AddMonoidAlgebra.coeff_mapRingHom, coeff_residueRingHom, h0, map_zero] at hρ0
    exact hρ0 rfl
  · obtain ⟨_, hk'⟩ := Finset.mem_filter.1 hF
    by_contra hρ0
    exact hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2
      (by simpa [AddMonoidAlgebra.coeff_mapRingHom, coeff_residueRingHom] using hρ0), hk'⟩)

end Functoriality

end TauCeti.NovikovSeries
