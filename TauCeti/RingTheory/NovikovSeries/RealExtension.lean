/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Localization
public import TauCeti.RingTheory.NovikovSeries.Residue

/-!
# Real-period extension and action-field specialization of Novikov rings

Given an additive monoid `H` with a period homomorphism `N : H →+ ℝ`, adjoining an independent real
action parameter produces the extended exponent monoid `H × ℝ` with period homomorphism
`realExtPeriod N : H × ℝ →+ ℝ`, `(h, r) ↦ N h + r`. Any grading `f : H → ι` extends by
`realExtDegree f (h, r) = f h`, so that the real action monomials `T^r := single (0, r) 1`
(`realMonomial R N r`) are central (`commute_realMonomial`), invertible with inverse `T^(-r)`
(`realMonomialUnit`), shift the period filtration by `r`
(`realMonomial_mul_mem_periodFiltration_iff`), and leave every homogeneous degree invariant
(`realMonomial_mul_mem_gradeBy_iff`). Distinct exponent classes with equal total period remain
distinct in the extended ring: `(g₁, r₁)` and `(g₂, r₂)` yield distinct monomials whenever
`g₁ ≠ g₂`, even if `N g₁ + r₁ = N g₂ + r₂`.

The canonical inclusion `realExtIncl` along `h ↦ (h, 0)` embeds `NovikovSeries R H N` continuously
and injectively into `NovikovSeries R (H × ℝ) (realExtPeriod N)`, preserving and reflecting the
period filtration, exponent gradings, and the nonnegative subring and positive ideal.

When `H` is an additive group, unlike the unextended ring — whose zero-period residue is
`R[N.ker]` — the kernel of `realExtPeriod N` is isomorphic to the entire group `H` via
`h ↦ (h, -N h)` (`realExtPeriodKerEquiv`). Composing with the general residue isomorphism of
`TauCeti.RingTheory.NovikovSeries.Residue` identifies the zero-period quotient
`nonnegSubring R (realExtPeriod N) ⧸ posIdeal R (realExtPeriod N)` with the full group ring `R[H]`
(`realExtResidueQuotientEquiv`, and `realExtResidueQuotientAlgEquiv` for `S`-algebras over any
commutative semiring `S`), preserving gradings and detecting units
(`isUnit_nonnegSubring_realExtPeriod_iff`). In particular, over a nontrivial ring each positive
action monomial `T^r` (`0 < r`) is a unit of the full extended ring with inverse `T^(-r)` yet a
non-unit of `nonnegSubring R (realExtPeriod N)` (`not_isUnit_nonnegRealMonomial`).

Over a commutative ring `R` and commutative additive monoid `H`, inverting the multiplicative
submonoid `realMonomialSubmonoid R N` of nonnegative action monomials `{T^r : r ≥ 0}` recovers the
entire extended ring `NovikovSeries R (H × ℝ) (realExtPeriod N)`
(`isLocalization_realMonomialSubmonoid`). Thus any ring homomorphism out of
`nonnegSubring R (realExtPeriod N)` that sends strictly positive action monomials to units factors
uniquely through `NovikovSeries R (H × ℝ) (realExtPeriod N)`.

Finally, for any ring homomorphism `ρ : R →+* S` and any period homomorphism `N : H →+ ℝ`, pushing
forward along `N : H →+ ℝ` defines the continuous unital ring homomorphism
`periodPushforward ρ N : NovikovSeries R H N →+* NovikovSeries S ℝ (AddMonoidHom.id ℝ)` (and its
restriction `periodPushforwardNonneg ρ N` on nonnegative subrings), preserving filtration pieces
`U_C` and `posIdeal`. Applied to `realExtPeriod N`, it yields the action-field specialization
sending `T^r` to `e^r`, extending `periodPushforward ρ N` along `realExtIncl`
(`periodPushforward_comp_realExtIncl`), and factoring uniquely through the localization at
`realMonomialSubmonoid`. Whenever `H` and `S` are nontrivial, this specialization is strictly
non-injective: for `h ≠ 0`, both `e^(h, -N h)` and `1` map to `1`.

## Main definitions

* `TauCeti.NovikovSeries.realExtPeriod`: the extended period homomorphism `(h, r) ↦ N h + r`.
* `TauCeti.NovikovSeries.realExtDegree` and `TauCeti.NovikovSeries.realExtDegreeHom`: the extended
  degree map `(h, r) ↦ f h`.
* `TauCeti.NovikovSeries.realMonomial` and `TauCeti.NovikovSeries.nonnegRealMonomial`: the degree-0
  action monomials `T^r = single (0, r) 1` (in the full ring and in `nonnegSubring`).
* `TauCeti.NovikovSeries.realExtIncl` and `TauCeti.NovikovSeries.realExtNonnegIncl`: the canonical
  inclusions `Nov(R, H, N) →+* Nov(R, H × ℝ, realExtPeriod N)` and on nonnegative subrings.
* `TauCeti.NovikovSeries.realExtPeriodKerEquiv`: the additive isomorphism
  `H ≃+ (realExtPeriod N).ker`, `h ↦ (h, -N h)`.
* `TauCeti.NovikovSeries.realExtOfBase`, `TauCeti.NovikovSeries.realExtResidueHom`,
  `TauCeti.NovikovSeries.realExtResidueQuotientEquiv`, and
  `TauCeti.NovikovSeries.realExtResidueQuotientAlgEquiv`: the residue maps and isomorphisms
  identifying `nonnegSubring R (realExtPeriod N) ⧸ posIdeal R (realExtPeriod N)` with `R[H]`.
* `TauCeti.NovikovSeries.realMonomialSubmonoid`: the multiplicative submonoid `{T^r : r ≥ 0}` of
  `nonnegSubring R (realExtPeriod N)`.
* `TauCeti.NovikovSeries.periodPushforward` and `TauCeti.NovikovSeries.periodPushforwardNonneg`:
  the continuous unital pushforward along any period homomorphism `N : H →+ ℝ` to real Novikov
  series.

## Main results

* `TauCeti.NovikovSeries.commute_realMonomial`: action monomials `T^r` are central.
* `TauCeti.NovikovSeries.isUnit_realMonomial` and
  `TauCeti.NovikovSeries.not_isUnit_nonnegRealMonomial`: for `0 < r` over a nontrivial ring, `T^r`
  is a unit of the extended ring (with inverse `T^(-r)`) and a non-unit of its nonnegative subring.
* `TauCeti.NovikovSeries.realMonomial_mul_mem_periodFiltration_iff` and
  `TauCeti.NovikovSeries.realMonomial_mul_mem_gradeBy_iff`: multiplying by `T^r` shifts the period
  filtration by `r` and preserves every homogeneous piece.
* `TauCeti.NovikovSeries.isUnit_nonnegSubring_realExtPeriod_iff`: unit criterion via the residue
  in `R[H]`.
* `TauCeti.NovikovSeries.isLocalization_realMonomialSubmonoid`: the full extended Novikov ring is
  the localization of its nonnegative subring at `{T^r : r ≥ 0}`.
* `TauCeti.NovikovSeries.periodPushforward_comp_realExtIncl`: the action-field specialization
  extends `periodPushforward ρ N` along `realExtIncl`.
* `TauCeti.NovikovSeries.periodPushforward_realExtPeriod_eq_lift`: the action-field specialization
  factors uniquely through this localization.
* `TauCeti.NovikovSeries.not_injective_periodPushforward_realExtPeriod`: for nontrivial `H` and
  `S`, the action-field specialization is never injective.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, and K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46 (2009), Chapter 3.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovSeries

variable {R S H ι : Type*}

section Degree

/-- Extension of a degree function `f : H → ι` to `H × ℝ` by projecting onto `H`. -/
def realExtDegree (f : H → ι) : H × ℝ → ι :=
  f ∘ Prod.fst

@[simp]
theorem realExtDegree_apply (f : H → ι) (p : H × ℝ) : realExtDegree f p = f p.1 :=
  (rfl)

end Degree

section PeriodAndDegree

variable [AddMonoid H]

/-- The extended period homomorphism `H × ℝ →+ ℝ`, sending `(h, r) ↦ N h + r`. -/
def realExtPeriod (N : H →+ ℝ) : H × ℝ →+ ℝ :=
  N.coprod (AddMonoidHom.id ℝ)

@[simp]
theorem realExtPeriod_apply (N : H →+ ℝ) (p : H × ℝ) : realExtPeriod N p = N p.1 + p.2 :=
  (rfl)

/-- Extension of an additive degree homomorphism `f : H →+ ι` to `H × ℝ →+ ι`. -/
def realExtDegreeHom [AddZeroClass ι] (f : H →+ ι) : H × ℝ →+ ι :=
  f.comp (AddMonoidHom.fst H ℝ)

@[simp]
theorem realExtDegreeHom_apply [AddZeroClass ι] (f : H →+ ι) (p : H × ℝ) :
    realExtDegreeHom f p = f p.1 :=
  (rfl)

/-- The canonical inclusion `h ↦ (h, 0)` rescales periods by `1`. -/
theorem exists_period_rescale_inl (N : H →+ ℝ) :
    ∃ c > 0, ∀ h : H, realExtPeriod N (AddMonoidHom.inl H ℝ h) = c * N h :=
  ⟨1, one_pos, fun h => by simp⟩

end PeriodAndDegree

section ActionMonomials

variable [AddMonoid H] {N : H →+ ℝ}

/-- Distinct `H`-classes remain distinct as monomials after real extension, even when their total
periods coincide. -/
theorem single_ne_single_of_fst_ne [Zero R] {g₁ g₂ : H} {r₁ r₂ : ℝ} {c₁ c₂ : R}
    (h : g₁ ≠ g₂) (hc : c₁ ≠ 0) :
    (single (g₁, r₁) c₁ : NovikovSeries R (H × ℝ) (realExtPeriod N)) ≠ single (g₂, r₂) c₂ := by
  intro heq
  have hne : (g₁, r₁) ≠ (g₂, r₂) := fun hp => h (congrArg Prod.fst hp)
  have hcoeff := congrArg (fun a : NovikovSeries R (H × ℝ) (realExtPeriod N) =>
    a.coeff (g₁, r₁)) heq
  rw [coeff_single_same, coeff_single_of_ne hne] at hcoeff
  exact hc hcoeff

section Semiring

variable [Semiring R]

variable (R N) in
/-- The real action monomial `T^r := single (0, r) 1` in the real-period extension
`NovikovSeries R (H × ℝ) (realExtPeriod N)`. -/
def realMonomial (r : ℝ) : NovikovSeries R (H × ℝ) (realExtPeriod N) :=
  single (0, r) 1

@[simp]
theorem realMonomial_zero : realMonomial R N 0 = 1 :=
  single_zero_one

@[simp]
theorem realMonomial_mul_realMonomial (r s : ℝ) :
    realMonomial R N r * realMonomial R N s = realMonomial R N (r + s) := by
  rw [realMonomial, realMonomial, realMonomial, single_mul_single, mul_one]
  simp

@[simp]
theorem realMonomial_pow (r : ℝ) (n : ℕ) :
    realMonomial R N r ^ n = realMonomial R N (n • r) := by
  rw [realMonomial, single_pow, one_pow]
  simp [realMonomial]

/-- Every action monomial `T^r` is homogeneous of degree `f 0`. -/
theorem realMonomial_mem_gradeBy (f : H → ι) (r : ℝ) :
    realMonomial R N r ∈ gradeBy R (realExtPeriod N) (realExtDegree f) (f 0) :=
  single_mem_gradeBy (realExtDegree f) (0, r) 1

/-- Every action monomial `T^r` has degree `0` for any additive degree homomorphism `f : H →+ ι`.
-/
theorem realMonomial_mem_gradeBy_zero [AddZeroClass ι] (f : H →+ ι) (r : ℝ) :
    realMonomial R N r ∈ gradeBy R (realExtPeriod N) (realExtDegree f) 0 := by
  simpa only [map_zero] using realMonomial_mem_gradeBy (R := R) (N := N) f r

@[simp]
theorem coeff_realMonomial_mul (r : ℝ) (a : NovikovSeries R (H × ℝ) (realExtPeriod N))
    (h : H) (s : ℝ) :
    (realMonomial R N r * a).coeff (h, s) = a.coeff (h, s - r) := by
  rw [realMonomial, coeff_mul_eq_sum (s := {((0, r), (h, s - r))})
    (fun p hp => by
      rw [Finset.mem_singleton.1 hp]
      exact Prod.ext (zero_add h) (add_sub_cancel r s))
    fun u v huv hu _ => by
      have hu0 : u = (0, r) := by
        by_contra hne
        exact hu (coeff_single_of_ne hne 1)
      subst hu0
      have hv1 : v.1 = h := by simpa using congrArg Prod.fst huv
      have hv2 : v.2 = s - r := by
        have h2 : r + v.2 = s := congrArg Prod.snd huv
        linarith
      exact Finset.mem_singleton.2 (Prod.ext rfl (Prod.ext hv1 hv2)),
    Finset.sum_singleton, coeff_single_same, one_mul]

@[simp]
theorem coeff_mul_realMonomial (a : NovikovSeries R (H × ℝ) (realExtPeriod N)) (r : ℝ)
    (h : H) (s : ℝ) :
    (a * realMonomial R N r).coeff (h, s) = a.coeff (h, s - r) := by
  rw [realMonomial, coeff_mul_eq_sum (s := {((h, s - r), (0, r))})
    (fun p hp => by
      rw [Finset.mem_singleton.1 hp]
      exact Prod.ext (add_zero h) (sub_add_cancel s r))
    fun u v huv _ hv => by
      have hv0 : v = (0, r) := by
        by_contra hne
        exact hv (coeff_single_of_ne hne 1)
      subst hv0
      have hu1 : u.1 = h := by simpa using congrArg Prod.fst huv
      have hu2 : u.2 = s - r := by
        have h2 : u.2 + r = s := congrArg Prod.snd huv
        linarith
      exact Finset.mem_singleton.2 (Prod.ext (Prod.ext hu1 hu2) rfl),
    Finset.sum_singleton, coeff_single_same, mul_one]

/-- Every action monomial `T^r` is central in `NovikovSeries R (H × ℝ) (realExtPeriod N)`, even
when `R` and `H` are noncommutative. -/
theorem commute_realMonomial (r : ℝ) (a : NovikovSeries R (H × ℝ) (realExtPeriod N)) :
    Commute (realMonomial R N r) a := by
  ext ⟨h, s⟩
  rw [coeff_realMonomial_mul, coeff_mul_realMonomial]

variable (R N) in
/-- Every action monomial `T^r` is invertible in the full extended ring, with inverse `T^(-r)`. -/
def realMonomialUnit (r : ℝ) : (NovikovSeries R (H × ℝ) (realExtPeriod N))ˣ where
  val := realMonomial R N r
  inv := realMonomial R N (-r)
  val_inv := by rw [realMonomial_mul_realMonomial, add_neg_cancel, realMonomial_zero]
  inv_val := by rw [realMonomial_mul_realMonomial, neg_add_cancel, realMonomial_zero]

@[simp]
theorem val_realMonomialUnit (r : ℝ) :
    (realMonomialUnit R N r : NovikovSeries R (H × ℝ) (realExtPeriod N)) = realMonomial R N r :=
  (rfl)

@[simp]
theorem val_inv_realMonomialUnit (r : ℝ) :
    (↑(realMonomialUnit R N r)⁻¹ : NovikovSeries R (H × ℝ) (realExtPeriod N)) =
      realMonomial R N (-r) :=
  (rfl)

/-- Every action monomial `T^r` is a unit of the extended Novikov ring. -/
theorem isUnit_realMonomial (r : ℝ) : IsUnit (realMonomial R N r) :=
  (realMonomialUnit R N r).isUnit

/-- Multiplying by `T^r` preserves and reflects every homogeneous piece `gradeBy`. -/
theorem realMonomial_mul_mem_gradeBy_iff (f : H → ι) {i : ι} (r : ℝ)
    {a : NovikovSeries R (H × ℝ) (realExtPeriod N)} :
    realMonomial R N r * a ∈ gradeBy R (realExtPeriod N) (realExtDegree f) i ↔
      a ∈ gradeBy R (realExtPeriod N) (realExtDegree f) i := by
  rw [mem_gradeBy_iff, mem_gradeBy_iff]
  constructor
  · intro ha ⟨h, s⟩ hs
    have hcoeff : (realMonomial R N r * a).coeff (h, s + r) ≠ 0 := by
      rw [coeff_realMonomial_mul, add_sub_cancel_right]
      exact mem_support.1 hs
    have hdeg : (h, s + r) ∈ realExtDegree f ⁻¹' {i} := ha (mem_support.2 hcoeff)
    exact hdeg
  · intro ha ⟨h, s⟩ hs
    have hcoeff : a.coeff (h, s - r) ≠ 0 := by
      rw [← coeff_realMonomial_mul (N := N) r a h s]
      exact mem_support.1 hs
    have hdeg : (h, s - r) ∈ realExtDegree f ⁻¹' {i} := ha (mem_support.2 hcoeff)
    exact hdeg

end Semiring

section Ring

variable [Ring R]

/-- Action monomials `T^r` lie in `periodFiltration R (realExtPeriod N) r`. -/
theorem realMonomial_mem_periodFiltration (r : ℝ) :
    realMonomial R N r ∈ periodFiltration R (realExtPeriod N) r := by
  have h := single_mem_periodFiltration (R := R) (N := realExtPeriod N) (0, r) 1
  simpa [realMonomial] using h

variable (R N) in
/-- A nonnegative real action monomial `T^r` (`0 ≤ r`) viewed inside
`nonnegSubring R (realExtPeriod N)`. -/
def nonnegRealMonomial {r : ℝ} (hr : 0 ≤ r) : nonnegSubring R (realExtPeriod N) :=
  ⟨realMonomial R N r, single_mem_nonnegSubring (by simpa using hr) 1⟩

@[simp]
theorem coe_nonnegRealMonomial {r : ℝ} (hr : 0 ≤ r) :
    (nonnegRealMonomial R N hr : NovikovSeries R (H × ℝ) (realExtPeriod N)) =
      realMonomial R N r :=
  (rfl)

@[simp]
theorem nonnegRealMonomial_zero : nonnegRealMonomial R N le_rfl = 1 :=
  Subtype.ext realMonomial_zero

@[simp]
theorem nonnegRealMonomial_mul {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    nonnegRealMonomial R N hr * nonnegRealMonomial R N hs =
      nonnegRealMonomial R N (add_nonneg hr hs) :=
  Subtype.ext (realMonomial_mul_realMonomial r s)

@[simp]
theorem nonnegRealMonomial_pow {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    nonnegRealMonomial R N hr ^ n = nonnegRealMonomial R N (nsmul_nonneg hr n) :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow, coe_nonnegRealMonomial, realMonomial_pow,
    coe_nonnegRealMonomial])

/-- Multiplying by `T^r` shifts the period filtration of the extended ring by `r`. -/
theorem realMonomial_mul_mem_periodFiltration_iff (r C : ℝ)
    {a : NovikovSeries R (H × ℝ) (realExtPeriod N)} :
    realMonomial R N r * a ∈ periodFiltration R (realExtPeriod N) (r + C) ↔
      a ∈ periodFiltration R (realExtPeriod N) C := by
  rw [mem_periodFiltration, mem_periodFiltration]
  constructor
  · intro ha ⟨h, s⟩ hs
    have h := ha (h, s + r) (by simp only [realExtPeriod_apply] at hs ⊢; linarith)
    simpa [coeff_realMonomial_mul] using h
  · intro ha ⟨h, s⟩ hs
    rw [coeff_realMonomial_mul]
    exact ha (h, s - r) (by simp only [realExtPeriod_apply] at hs ⊢; linarith)

/-- For `0 < r`, the action monomial `T^r` belongs to the positive ideal `posIdeal`. -/
theorem nonnegRealMonomial_mem_posIdeal {r : ℝ} (hr : 0 < r) :
    nonnegRealMonomial R N hr.le ∈ posIdeal R (realExtPeriod N) :=
  single_mem_posIdeal (by simpa using hr) 1

/-- Over a nontrivial ring, a strictly positive action monomial `T^r` (`0 < r`) is not a unit in
`nonnegSubring R (realExtPeriod N)` (even though it is a unit in the full extended ring). -/
theorem not_isUnit_nonnegRealMonomial [Nontrivial R] {r : ℝ} (hr : 0 < r) :
    ¬ IsUnit (nonnegRealMonomial R N hr.le) :=
  not_isUnit_of_mem_posIdeal (nonnegRealMonomial_mem_posIdeal hr)

end Ring

end ActionMonomials

section Inclusion

variable [AddMonoid H] {N : H →+ ℝ}

section SemiringIncl

variable [Semiring R]

variable (R N) in
/-- The canonical inclusion `NovikovSeries R H N →+* NovikovSeries R (H × ℝ) (realExtPeriod N)`
along `h ↦ (h, 0)`. -/
def realExtIncl : NovikovSeries R H N →+* NovikovSeries R (H × ℝ) (realExtPeriod N) :=
  mapRingHom (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

@[simp]
theorem realExtIncl_single (h : H) (r : R) :
    realExtIncl R N (single h r) = single (h, 0) r := by
  rw [realExtIncl, mapRingHom_apply, map_single]
  rfl

@[simp]
theorem coeff_realExtIncl_zero (a : NovikovSeries R H N) (h : H) :
    (realExtIncl R N a).coeff (h, 0) = a.coeff h := by
  have hinj : Injective (AddMonoidHom.inl H ℝ) := fun _ _ hab => congrArg Prod.fst hab
  rw [realExtIncl, mapRingHom_apply]
  exact coeff_map_of_injective (RingHom.id R : R →+ R) (AddMonoidHom.inl H ℝ)
    (exists_period_rescale_inl N) hinj a h

/-- Coefficients of `realExtIncl R N a` vanish whenever the real parameter is nonzero. -/
theorem coeff_realExtIncl_of_ne_zero (a : NovikovSeries R H N) (h : H) {r : ℝ} (hr : r ≠ 0) :
    (realExtIncl R N a).coeff (h, r) = 0 := by
  rw [realExtIncl, mapRingHom_apply]
  refine coeff_map_eq_zero_of_notMem_range (RingHom.id R : R →+ R) (AddMonoidHom.inl H ℝ)
    (exists_period_rescale_inl N) a ?_
  rintro ⟨g, hg⟩
  exact hr (congrArg Prod.snd hg).symm

/-- The canonical inclusion `Nov(R, H, N) →+* Nov(R, H × ℝ, realExtPeriod N)` is injective. -/
theorem realExtIncl_injective : Injective (realExtIncl R N) := fun _ _ hab =>
  map_injective (RingHom.id R : R →+ R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)
    injective_id (fun _ _ h => congrArg Prod.fst h)
    (by simpa only [realExtIncl, mapRingHom_apply] using hab)

/-- The canonical inclusion preserves and reflects homogeneous degrees. -/
theorem realExtIncl_mem_gradeBy_iff (f : H → ι) {i : ι} {a : NovikovSeries R H N} :
    realExtIncl R N a ∈ gradeBy R (realExtPeriod N) (realExtDegree f) i ↔
      a ∈ gradeBy R N f i := by
  rw [mem_gradeBy_iff, mem_gradeBy_iff]
  constructor
  · intro ha h hh
    have hmem : (h, (0 : ℝ)) ∈ (realExtIncl R N a).support := by
      rw [mem_support, coeff_realExtIncl_zero]
      exact mem_support.1 hh
    exact ha hmem
  · intro ha ⟨h, r⟩ hr
    by_cases hr0 : r = 0
    · subst hr0
      rw [mem_support, coeff_realExtIncl_zero] at hr
      exact ha (mem_support.2 hr)
    · exact absurd (coeff_realExtIncl_of_ne_zero a h hr0) (mem_support.1 hr)

end SemiringIncl

section RingIncl

variable [Ring R]

/-- The canonical inclusion is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_realExtIncl : Continuous (realExtIncl R N) :=
  continuous_mapRingHom (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

/-- The canonical inclusion preserves and reflects the period filtration `U_C`. -/
theorem realExtIncl_mem_periodFiltration_iff {C : ℝ} {a : NovikovSeries R H N} :
    realExtIncl R N a ∈ periodFiltration R (realExtPeriod N) C ↔
      a ∈ periodFiltration R N C := by
  constructor
  · intro ha
    refine mem_periodFiltration.2 fun h hh => ?_
    rw [← coeff_realExtIncl_zero a h]
    exact mem_periodFiltration.1 ha (h, 0) (by simpa using hh)
  · intro ha
    rw [realExtIncl, mapRingHom_apply]
    simpa only [one_mul] using map_mem_periodFiltration (RingHom.id R : R →+ R)
      (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N) zero_le_one (fun h => by simp) ha

variable (R N) in
/-- The restriction of `realExtIncl` to nonnegative subrings. -/
def realExtNonnegIncl : nonnegSubring R N →+* nonnegSubring R (realExtPeriod N) :=
  mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

@[simp]
theorem coe_realExtNonnegIncl (a : nonnegSubring R N) :
    (realExtNonnegIncl R N a : NovikovSeries R (H × ℝ) (realExtPeriod N)) =
      realExtIncl R N a := by
  rw [realExtNonnegIncl, coe_mapNonnegSubring, realExtIncl, mapRingHom_apply]

/-- The canonical inclusion on nonnegative subrings is injective. -/
theorem realExtNonnegIncl_injective : Injective (realExtNonnegIncl R N) :=
  mapNonnegSubring_injective (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)
    injective_id fun _ _ hab => congrArg Prod.fst hab

/-- The canonical inclusion on nonnegative subrings is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_realExtNonnegIncl : Continuous (realExtNonnegIncl R N) :=
  continuous_mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

/-- The canonical inclusion preserves and reflects the positive ideal. -/
theorem realExtNonnegIncl_mem_posIdeal_iff {a : nonnegSubring R N} :
    realExtNonnegIncl R N a ∈ posIdeal R (realExtPeriod N) ↔ a ∈ posIdeal R N := by
  constructor
  · intro ha
    refine mem_posIdeal.2 fun h hh => ?_
    rw [← coeff_realExtIncl_zero (a : NovikovSeries R H N) h, ← coe_realExtNonnegIncl]
    exact mem_posIdeal.1 ha (h, 0) (by simpa using hh)
  · exact mapNonnegSubring_mem_posIdeal (RingHom.id R) (AddMonoidHom.inl H ℝ)
      (exists_period_rescale_inl N)

end RingIncl

end Inclusion

section Residue

variable [AddGroup H] (N : H →+ ℝ)

/-- The zero-period kernel of `realExtPeriod N` is isomorphic as an additive group to the entire
group `H`, via `h ↦ (h, -N h)`. -/
def realExtPeriodKerEquiv : H ≃+ (realExtPeriod N).ker where
  toFun h := ⟨(h, -N h), by simp [realExtPeriod]⟩
  invFun x := x.1.1
  left_inv _ := rfl
  right_inv x := Subtype.ext <| Prod.ext rfl <| by
    have hx : N x.1.1 + x.1.2 = 0 := AddMonoidHom.mem_ker.1 x.2
    linarith
  map_add' h₁ h₂ := Subtype.ext <| Prod.ext rfl <| by simp [add_comm]

@[simp]
theorem coe_realExtPeriodKerEquiv_apply (h : H) :
    ((realExtPeriodKerEquiv N h : (realExtPeriod N).ker) : H × ℝ) = (h, -N h) :=
  (rfl)

@[simp]
theorem realExtPeriodKerEquiv_symm_apply (x : (realExtPeriod N).ker) :
    (realExtPeriodKerEquiv N).symm x = x.1.1 :=
  (rfl)

section RingResidue

variable {N} [Ring R]

variable (R N) in
/-- The inclusion of the full group ring `R[H]` into `nonnegSubring R (realExtPeriod N)` sending
`e^h` to `e^(h, -N h)`. -/
def realExtOfBase : AddMonoidAlgebra R H →+* nonnegSubring R (realExtPeriod N) :=
  (ofKernel R (realExtPeriod N)).comp
    (AddMonoidAlgebra.mapDomainRingEquiv R (realExtPeriodKerEquiv N)).toRingHom

@[simp]
theorem realExtOfBase_single (h : H) (r : R) :
    (realExtOfBase R N (AddMonoidAlgebra.single h r) :
        NovikovSeries R (H × ℝ) (realExtPeriod N)) = single (h, -N h) r := by
  rw [realExtOfBase, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AddMonoidAlgebra.mapDomainRingEquiv_single, ofKernel_single, coe_realExtPeriodKerEquiv_apply]

/-- The inclusion `realExtOfBase : R[H] →+* nonnegSubring R (realExtPeriod N)` is injective. -/
theorem realExtOfBase_injective : Injective (realExtOfBase R N) :=
  ofKernel_injective.comp
    (AddMonoidAlgebra.mapDomainRingEquiv R (realExtPeriodKerEquiv N)).injective

variable (R N) in
/-- The energy-zero residue ring homomorphism after real extension,
`nonnegSubring R (realExtPeriod N) →+* R[H]`, extracting the coefficient at `(h, -N h)`. -/
def realExtResidueHom : nonnegSubring R (realExtPeriod N) →+* AddMonoidAlgebra R H :=
  (AddMonoidAlgebra.mapDomainRingEquiv R (realExtPeriodKerEquiv N).symm).toRingHom.comp
    (residueHom R (realExtPeriod N))

@[simp]
theorem coeff_realExtResidueHom (a : nonnegSubring R (realExtPeriod N)) (h : H) :
    (realExtResidueHom R N a).coeff h =
      (a : NovikovSeries R (H × ℝ) (realExtPeriod N)).coeff (h, -N h) := by
  rw [realExtResidueHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply,
    AddEquiv.coe_toEquiv_symm, AddEquiv.symm_symm, coeff_residueHom,
    coe_realExtPeriodKerEquiv_apply]

/-- `realExtOfBase` is a right inverse to `realExtResidueHom`. -/
@[simp]
theorem realExtResidueHom_ofBase (p : AddMonoidAlgebra R H) :
    realExtResidueHom R N (realExtOfBase R N p) = p := by
  dsimp only [realExtResidueHom, realExtOfBase, RingHom.comp_apply]
  rw [residueHom_ofKernel]
  exact (AddMonoidAlgebra.mapDomainRingEquiv R (realExtPeriodKerEquiv N)).symm_apply_apply p

/-- The energy-zero residue homomorphism after real extension is surjective onto `R[H]`. -/
theorem realExtResidueHom_surjective : Surjective (realExtResidueHom R N) :=
  Function.RightInverse.surjective realExtResidueHom_ofBase

variable (R N) in
/-- The kernel of `realExtResidueHom` is precisely `posIdeal R (realExtPeriod N)`. -/
theorem ker_realExtResidueHom :
    RingHom.ker (realExtResidueHom R N) = posIdeal R (realExtPeriod N) := by
  ext a
  rw [RingHom.mem_ker, ← ker_residueHom, RingHom.mem_ker]
  exact (AddMonoidAlgebra.mapDomainRingEquiv R (realExtPeriodKerEquiv N).symm).map_eq_zero_iff

/-- Every strictly positive action monomial `T^r` (`0 < r`) has zero residue in `R[H]`. -/
@[simp]
theorem realExtResidueHom_nonnegRealMonomial_of_pos {r : ℝ} (hr : 0 < r) :
    realExtResidueHom R N (nonnegRealMonomial R N hr.le) = 0 := by
  rw [← RingHom.mem_ker, ker_realExtResidueHom]
  exact nonnegRealMonomial_mem_posIdeal hr

variable (R N) in
/-- After the real-period extension, the energy-zero quotient
`nonnegSubring R (realExtPeriod N) ⧸ posIdeal R (realExtPeriod N)` is isomorphic as a ring to the
full group ring `R[H]`. -/
def realExtResidueQuotientEquiv :
    nonnegSubring R (realExtPeriod N) ⧸ posIdeal R (realExtPeriod N) ≃+* AddMonoidAlgebra R H :=
  (residueQuotientEquiv R (realExtPeriod N)).trans
    (AddMonoidAlgebra.mapDomainRingEquiv R (realExtPeriodKerEquiv N).symm)

@[simp]
theorem realExtResidueQuotientEquiv_mk (a : nonnegSubring R (realExtPeriod N)) :
    realExtResidueQuotientEquiv R N (Ideal.Quotient.mk (posIdeal R (realExtPeriod N)) a) =
      realExtResidueHom R N a := by
  rw [realExtResidueQuotientEquiv, RingEquiv.trans_apply, residueQuotientEquiv_mk]
  rfl

@[simp]
theorem realExtResidueQuotientEquiv_symm_apply (p : AddMonoidAlgebra R H) :
    (realExtResidueQuotientEquiv R N).symm p =
      Ideal.Quotient.mk (posIdeal R (realExtPeriod N)) (realExtOfBase R N p) := by
  rw [realExtResidueQuotientEquiv, RingEquiv.symm_trans_apply, residueQuotientEquiv_symm_apply]
  rfl

/-- A nonnegative series in the real-period extension is a unit of
`nonnegSubring R (realExtPeriod N)` if and only if its energy-zero residue in `R[H]` is a unit. -/
theorem isUnit_nonnegSubring_realExtPeriod_iff {a : nonnegSubring R (realExtPeriod N)} :
    IsUnit a ↔ IsUnit (realExtResidueHom R N a) := by
  rw [isUnit_nonnegSubring_iff]
  exact (MulEquiv.isUnit_map (f := (AddMonoidAlgebra.mapDomainRingEquiv R
    (realExtPeriodKerEquiv N).symm).toMulEquiv)).symm

end RingResidue

section GradingResidue

variable {N} [CommRing R]

/-- The energy-zero residue after real extension preserves homogeneous degrees. -/
theorem realExtResidueHom_mem_gradeBy {f : H → ι} {i : ι}
    {a : nonnegSubring R (realExtPeriod N)}
    (ha : (a : NovikovSeries R (H × ℝ) (realExtPeriod N)) ∈
      gradeBy R (realExtPeriod N) (realExtDegree f) i) :
    realExtResidueHom R N a ∈ AddMonoidAlgebra.gradeBy R f i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro h hh
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_realExtResidueHom] at hh
  exact mem_gradeBy_iff.1 ha (mem_support.2 hh)

/-- The inclusion `realExtOfBase : R[H] →+* nonnegSubring R (realExtPeriod N)` preserves and
reflects homogeneous degrees. -/
theorem realExtOfBase_mem_gradeBy_iff {f : H → ι} {i : ι} {p : AddMonoidAlgebra R H} :
    (realExtOfBase R N p : NovikovSeries R (H × ℝ) (realExtPeriod N)) ∈
      gradeBy R (realExtPeriod N) (realExtDegree f) i ↔
      p ∈ AddMonoidAlgebra.gradeBy R f i := by
  constructor
  · intro hp
    simpa only [realExtResidueHom_ofBase] using realExtResidueHom_mem_gradeBy hp
  · intro hp
    have hker : AddMonoidAlgebra.mapDomainRingEquiv R (realExtPeriodKerEquiv N) p ∈
        AddMonoidAlgebra.gradeBy R (fun g : (realExtPeriod N).ker => realExtDegree f g) i := by
      rw [AddMonoidAlgebra.mem_gradeBy_iff]
      intro g hg
      rw [Finset.mem_coe, Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_mapDomainRingEquiv,
        Finsupp.equivMapDomain_apply] at hg
      exact (AddMonoidAlgebra.mem_gradeBy_iff R f i p).1 hp (Finsupp.mem_support_iff.2 hg)
    exact ofKernel_mem_gradeBy_iff.2 hker

end GradingResidue

end Residue

end NovikovSeries

section AlgebraResidue

namespace NovikovSeries

variable (S : Type*) [CommSemiring S] (R : Type*) [Ring R] [Algebra S R]
  {H : Type*} [AddGroup H] (N : H →+ ℝ)

/-- After the real-period extension, the energy-zero quotient
`nonnegSubring R (realExtPeriod N) ⧸ posIdeal R (realExtPeriod N)` is isomorphic as an `S`-algebra
to `R[H]`. -/
def realExtResidueQuotientAlgEquiv :
    (nonnegSubring R (realExtPeriod N) ⧸ posIdeal R (realExtPeriod N)) ≃ₐ[S]
      AddMonoidAlgebra R H :=
  (residueQuotientAlgEquiv S R (realExtPeriod N)).trans
    (AddMonoidAlgebra.domCongr S R (realExtPeriodKerEquiv N).symm)

@[simp]
theorem realExtResidueQuotientAlgEquiv_mk (a : nonnegSubring R (realExtPeriod N)) :
    realExtResidueQuotientAlgEquiv S R N (Ideal.Quotient.mk (posIdeal R (realExtPeriod N)) a) =
      realExtResidueHom R N a := by
  rw [realExtResidueQuotientAlgEquiv, AlgEquiv.trans_apply, residueQuotientAlgEquiv_mk]
  rfl

@[simp]
theorem realExtResidueQuotientAlgEquiv_symm_apply (p : AddMonoidAlgebra R H) :
    (realExtResidueQuotientAlgEquiv S R N).symm p =
      Ideal.Quotient.mk (posIdeal R (realExtPeriod N)) (realExtOfBase R N p) := by
  rw [realExtResidueQuotientAlgEquiv, AlgEquiv.symm_trans_apply,
    residueQuotientAlgEquiv_symm_apply]
  rfl

end NovikovSeries

end AlgebraResidue

namespace NovikovSeries

variable {R S H ι : Type*}

section RealLocalization

variable [AddMonoid H] {N : H →+ ℝ}

variable (R N) in
/-- The multiplicative submonoid `{T^r : r ≥ 0}` of nonnegative degree-zero action monomials in
`nonnegSubring R (realExtPeriod N)`. -/
def realMonomialSubmonoid [Ring R] : Submonoid (nonnegSubring R (realExtPeriod N)) :=
  monomialSubmonoid R (realExtPeriod N)
    ((nonnegPeriodSubmonoid (AddMonoidHom.id ℝ)).map (AddMonoidHom.inr H ℝ))

@[simp]
theorem mem_realMonomialSubmonoid [Ring R] {a : nonnegSubring R (realExtPeriod N)} :
    a ∈ realMonomialSubmonoid R N ↔
      ∃ r : ℝ, 0 ≤ r ∧ (a : NovikovSeries R (H × ℝ) (realExtPeriod N)) = realMonomial R N r := by
  simp only [realMonomialSubmonoid, mem_monomialSubmonoid, AddSubmonoid.mem_map,
    mem_nonnegPeriodSubmonoid, AddMonoidHom.id_apply, AddMonoidHom.inr_apply]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, ha⟩
    exact ⟨r, hr, ha⟩
  · rintro ⟨r, hr, ha⟩
    exact ⟨(0, r), ⟨r, hr, rfl⟩, ha⟩

/-- Every nonnegative action monomial `T^r` (`0 ≤ r`) belongs to `realMonomialSubmonoid R N`. -/
theorem nonnegRealMonomial_mem_realMonomialSubmonoid [Ring R] {r : ℝ} (hr : 0 ≤ r) :
    nonnegRealMonomial R N hr ∈ realMonomialSubmonoid R N :=
  mem_realMonomialSubmonoid.2 ⟨r, hr, coe_nonnegRealMonomial hr⟩

/-- A monoid/ring homomorphism out of `nonnegSubring R (realExtPeriod N)` sends every element of
`realMonomialSubmonoid R N` to a unit if and only if it sends every strictly positive action
monomial `T^r` (`0 < r`) to a unit. -/
theorem forall_isUnit_realMonomialSubmonoid_iff {A : Type*} [Ring R] [Monoid A]
    {F : Type*} [FunLike F (nonnegSubring R (realExtPeriod N)) A]
    [MonoidHomClass F (nonnegSubring R (realExtPeriod N)) A] (f : F) :
    (∀ y : realMonomialSubmonoid R N, IsUnit (f y)) ↔
      ∀ r : ℝ, (hr : 0 < r) → IsUnit (f (nonnegRealMonomial R N hr.le)) := by
  constructor
  · intro hf r hr
    exact hf ⟨nonnegRealMonomial R N hr.le, nonnegRealMonomial_mem_realMonomialSubmonoid hr.le⟩
  · rintro hf ⟨a, ha⟩
    obtain ⟨r, hr, haeq⟩ := mem_realMonomialSubmonoid.1 ha
    have ha' : a = nonnegRealMonomial R N hr := Subtype.ext haeq
    dsimp only
    rcases hr.eq_or_lt with rfl | hpos
    · rw [ha', nonnegRealMonomial_zero, _root_.map_one]
      exact isUnit_one
    · rw [ha']
      exact hf r hpos

end RealLocalization

section RealLocalizationInstance

/-- The full real-period extended ring `NovikovSeries R (H × ℝ) (realExtPeriod N)` is the
localization of `nonnegSubring R (realExtPeriod N)` at the submonoid `realMonomialSubmonoid R N`
of nonnegative action monomials `{T^r : r ≥ 0}`. -/
instance isLocalization_realMonomialSubmonoid [CommRing R] [AddCommMonoid H] {N : H →+ ℝ} :
    IsLocalization (realMonomialSubmonoid R N)
      (NovikovSeries R (H × ℝ) (realExtPeriod N)) := by
  refine isLocalization_of_isUnit_of_forall_exists_mem_periodFiltration _ ?_ ?_
  · intro s hs
    obtain ⟨r, -, ha⟩ := mem_realMonomialSubmonoid.1 hs
    rw [ha]
    exact isUnit_realMonomial r
  · intro C
    refine ⟨nonnegRealMonomial R N (le_max_right C 0),
      nonnegRealMonomial_mem_realMonomialSubmonoid (le_max_right C 0), ?_⟩
    rw [coe_nonnegRealMonomial]
    exact antitone_periodFiltration (le_max_left C 0)
      (realMonomial_mem_periodFiltration (max C 0))

end RealLocalizationInstance

section PeriodPushforward

variable [AddMonoid H]

/-- The identity period homomorphism on `ℝ` equals `1 * N` along `N : H →+ ℝ`. -/
theorem exists_period_rescale_self (N : H →+ ℝ) :
    ∃ c > 0, ∀ h : H, AddMonoidHom.id ℝ (N h) = c * N h :=
  ⟨1, one_pos, fun h => by simp⟩

section SemiringPushforward

variable [Semiring R] [Semiring S] (ρ : R →+* S) (N : H →+ ℝ)

/-- The unital pushforward ring homomorphism along a period homomorphism `N : H →+ ℝ` into real
Novikov series, summing coefficients along fibres of `N`. -/
def periodPushforward : NovikovSeries R H N →+* NovikovSeries S ℝ (AddMonoidHom.id ℝ) :=
  mapRingHom ρ N (exists_period_rescale_self N)

@[simp]
theorem periodPushforward_single (h : H) (r : R) :
    periodPushforward ρ N (single h r) = single (N h) (ρ r) := by
  rw [periodPushforward, mapRingHom_apply, map_single]
  rfl

@[simp]
theorem periodPushforward_realMonomial (r : ℝ) :
    periodPushforward ρ (realExtPeriod N) (realMonomial R N r) = single r 1 := by
  rw [realMonomial, periodPushforward_single, realExtPeriod_apply, map_zero, zero_add,
    _root_.map_one]

/-- Pushing forward the real-period extension along `realExtPeriod N` restricts on the canonical
subring `NovikovSeries R H N` to `periodPushforward ρ N`. -/
@[simp]
theorem periodPushforward_comp_realExtIncl :
    (periodPushforward ρ (realExtPeriod N)).comp (realExtIncl R N) =
      periodPushforward ρ N := by
  have hφ : (realExtPeriod N).comp (AddMonoidHom.inl H ℝ) = N :=
    AddMonoidHom.ext fun h => by simp
  rw [periodPushforward, realExtIncl, mapRingHom_comp, periodPushforward]
  simp only [RingHom.comp_id, hφ]

@[simp]
theorem periodPushforward_realExtIncl (a : NovikovSeries R H N) :
    periodPushforward ρ (realExtPeriod N) (realExtIncl R N a) = periodPushforward ρ N a :=
  RingHom.congr_fun (periodPushforward_comp_realExtIncl ρ N) a

end SemiringPushforward

section RingPushforward

variable [Ring R] [Ring S] (ρ : R →+* S) (N : H →+ ℝ)

/-- Pushing forward along `N` sends the period filtration `U_C` into `U'_C`. -/
theorem periodPushforward_mem_periodFiltration {C : ℝ} {a : NovikovSeries R H N}
    (ha : a ∈ periodFiltration R N C) :
    periodPushforward ρ N a ∈ periodFiltration S (AddMonoidHom.id ℝ) C := by
  rw [periodPushforward, mapRingHom_apply]
  simpa only [one_mul] using map_mem_periodFiltration (ρ : R →+ S) N
    (exists_period_rescale_self N) zero_le_one (fun h => by simp) ha

/-- The period pushforward is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_periodPushforward : Continuous (periodPushforward ρ N) :=
  continuous_mapRingHom ρ N (exists_period_rescale_self N)

/-- The restriction of `periodPushforward ρ N` to nonnegative subrings. -/
def periodPushforwardNonneg :
    nonnegSubring R N →+* nonnegSubring S (AddMonoidHom.id ℝ) :=
  mapNonnegSubring ρ N (exists_period_rescale_self N)

@[simp]
theorem coe_periodPushforwardNonneg (a : nonnegSubring R N) :
    (periodPushforwardNonneg ρ N a : NovikovSeries S ℝ (AddMonoidHom.id ℝ)) =
      periodPushforward ρ N a := by
  rw [periodPushforwardNonneg, coe_mapNonnegSubring, periodPushforward, mapRingHom_apply]

/-- The nonnegative period pushforward is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_periodPushforwardNonneg : Continuous (periodPushforwardNonneg ρ N) :=
  continuous_mapNonnegSubring ρ N (exists_period_rescale_self N)

/-- The nonnegative period pushforward sends the positive ideal into the positive ideal. -/
theorem periodPushforwardNonneg_mem_posIdeal {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) :
    periodPushforwardNonneg ρ N a ∈ posIdeal S (AddMonoidHom.id ℝ) :=
  mapNonnegSubring_mem_posIdeal ρ N (exists_period_rescale_self N) ha

end RingPushforward

section NonInjectivity

variable [Ring R] [Ring S]

/-- For nontrivial `H` and `S`, the nonnegative action-field specialization
`periodPushforwardNonneg ρ (realExtPeriod N)` is never injective: for any `h ≠ 0`, both
`e^(h, -N h)` and `1` map to `1`. -/
theorem not_injective_periodPushforwardNonneg_realExtPeriod [Nontrivial H] [Nontrivial S]
    (ρ : R →+* S) (N : H →+ ℝ) :
    ¬ Injective (periodPushforwardNonneg ρ (realExtPeriod N)) := by
  intro hinj
  have : Nontrivial R := ρ.domain_nontrivial
  obtain ⟨h, hh⟩ := exists_ne (0 : H)
  let x : nonnegSubring R (realExtPeriod N) :=
    ⟨single (h, -N h) 1, single_mem_nonnegSubring (by simp [realExtPeriod]) 1⟩
  have hmap : periodPushforwardNonneg ρ (realExtPeriod N) x =
      periodPushforwardNonneg ρ (realExtPeriod N) 1 := by
    apply Subtype.ext
    rw [coe_periodPushforwardNonneg, coe_periodPushforwardNonneg, OneMemClass.coe_one,
      _root_.map_one]
    dsimp only [x]
    rw [periodPushforward_single, realExtPeriod_apply, add_neg_cancel, _root_.map_one,
      single_zero_one]
  have hx1 : x = 1 := hinj hmap
  have hval : (single (h, -N h) 1 : NovikovSeries R (H × ℝ) (realExtPeriod N)) =
      single (0, 0) 1 :=
    (congrArg Subtype.val hx1).trans <| by
      rw [OneMemClass.coe_one, ← single_zero_one]
      rfl
  exact single_ne_single_of_fst_ne hh one_ne_zero hval

/-- For nontrivial `H` and `S`, the action-field specialization
`periodPushforward ρ (realExtPeriod N)` is never injective. -/
theorem not_injective_periodPushforward_realExtPeriod [Nontrivial H] [Nontrivial S]
    (ρ : R →+* S) (N : H →+ ℝ) :
    ¬ Injective (periodPushforward ρ (realExtPeriod N)) := fun hinj =>
  not_injective_periodPushforwardNonneg_realExtPeriod ρ N fun a b hab => by
    apply Subtype.ext
    have hval : periodPushforward ρ (realExtPeriod N) (a : NovikovSeries R (H × ℝ)
        (realExtPeriod N)) = periodPushforward ρ (realExtPeriod N) b := by
      simpa only [coe_periodPushforwardNonneg] using congrArg Subtype.val hab
    exact hinj hval

end NonInjectivity

end PeriodPushforward

section Factorization

variable [AddCommMonoid H] [CommRing R] [CommRing S]

/-- The action-field specialization on `NovikovSeries R (H × ℝ) (realExtPeriod N)` is the unique
factorization through the localization `realMonomialSubmonoid R N` of its restriction to
`nonnegSubring R (realExtPeriod N)`. -/
theorem periodPushforward_realExtPeriod_eq_lift (ρ : R →+* S) (N : H →+ ℝ) :
    periodPushforward ρ (realExtPeriod N) =
      IsLocalization.lift (M := realMonomialSubmonoid R N)
        (g := (nonnegSubring S (AddMonoidHom.id ℝ)).subtype.comp
          (periodPushforwardNonneg ρ (realExtPeriod N)))
        ((forall_isUnit_realMonomialSubmonoid_iff _).2 fun r _ => by
          rw [RingHom.comp_apply, Subring.coe_subtype, coe_periodPushforwardNonneg,
            coe_nonnegRealMonomial, periodPushforward_realMonomial]
          exact isUnit_single r isUnit_one) := by
  symm
  refine IsLocalization.lift_unique _ fun a => ?_
  rw [RingHom.comp_apply, Subring.coe_subtype, coe_periodPushforwardNonneg]
  rfl

end Factorization

end NovikovSeries

end TauCeti
