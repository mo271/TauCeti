/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import TauCeti.RingTheory.NovikovSeries.Localization
public import TauCeti.RingTheory.NovikovSeries.Residue

/-!
# Period-evaluation pushforwards and real period extensions of Novikov rings

Every period homomorphism `N : H →+ ℝ` is tautologically compatible with the identity period map on
`ℝ` with rescaling factor `1`. Pushing forward along `(ρ, N)` therefore defines a continuous ring
homomorphism `mapPeriodRingHom ρ N : Nov(R, H, N) →+* Nov(S, ℝ, id)` and its nonnegative restriction
`mapPeriodNonnegSubring ρ N : Nov≥0(R, H, N) →+* Nov≥0(S, ℝ, id)`, sending `U_C` into `U'_C` without
rescaling the cutoff and sending `e^g` to `T^(N g)`.

When `ker N` is a proper subgroup of `H`, the residue ring `Nov≥0(R, H, N) ⧸ posIdeal R N ≃+*
R[ker N]` records only period-zero classes, and `N` itself may fail to supply degree-zero elements
of arbitrary positive period. Adjoining an independent real action coordinate via
`N.coprod (AddMonoidHom.id ℝ) : H × ℝ →+ ℝ`, `(h, r) ↦ N h + r`, resolves both issues
simultaneously while keeping `Nov(R, H, N)` and `Nov(R, ℝ, id)` as canonically embedded subrings:

* **Full group-ring residue:** every class `h : H` has a unique lift `(h, -N h)` of total period
  `0`, giving an additive equivalence `coprodIdKerEquiv N : H ≃+ (N.coprod (.id ℝ)).ker` and hence
  the canonical residue ring isomorphism
  `Nov≥0(R, H × ℝ, N.coprod (.id ℝ)) ⧸ posIdeal ≃+* R[H]`
  (`TauCeti.NovikovSeries.quotientPosIdealCoprodEquiv`).
* **Degree-zero real monomials and localization:** for any grading `f : H →+ ι` pulled back along
  `Prod.fst`, the real monomial `T^r = single (0, r) 1` (`r ≥ 0`) has degree `0`, is a unit in
  `Nov(R, H × ℝ, N.coprod (.id ℝ))` with inverse `T^(-r)`, is never a unit in `Nov≥0` for `r > 0`
  over a nontrivial ring, and inverting `{T^r : r ≥ 0}` (or `{T^r : r > 0}`, or any single `T^r`
  with `r > 0`) localizes `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` onto
  `Nov(R, H × ℝ, N.coprod (.id ℝ))` compatibly with `mapPeriodRingHom`.
* **Algebraic vs. completed grading:** over a nontrivial commutative ring, the algebraic direct sum
  of homogeneous pieces of `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` along `f ∘ Prod.fst` exhausts the
  nonnegative subring if and only if `range f` is finite
  (`TauCeti.NovikovSeries.iSup_nonnegGradeBy_coprod_eq_top_iff`), whereas its period-topology
  closure is always the whole nonnegative subring.

## Main definitions

* `TauCeti.NovikovSeries.mapPeriodRingHom` and `TauCeti.NovikovSeries.mapPeriodNonnegSubring`:
  period-evaluation pushforwards `Nov(R, H, N) →+* Nov(S, ℝ, id)` and
  `Nov≥0(R, H, N) →+* Nov≥0(S, ℝ, id)`.
* `TauCeti.NovikovSeries.inlRingHom`, `TauCeti.NovikovSeries.inlNonnegSubring`,
  `TauCeti.NovikovSeries.inrRingHom`, and `TauCeti.NovikovSeries.inrNonnegSubring`: canonical
  embeddings of `Nov(R, H, N)` and `Nov(R, ℝ, id)` into `Nov(R, H × ℝ, N.coprod (.id ℝ))` and their
  nonnegative restrictions.
* `TauCeti.NovikovSeries.coprodRealMonomial`: the degree-zero real monomial `T^r = single (0, r) 1`
  in `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` for `r ≥ 0`.
* `TauCeti.NovikovSeries.coprodIdKerEquiv` and
  `TauCeti.NovikovSeries.quotientPosIdealCoprodEquiv`: the kernel identification
  `H ≃+ (N.coprod (.id ℝ)).ker` and residue isomorphism
  `Nov≥0(R, H × ℝ, N.coprod (.id ℝ)) ⧸ posIdeal ≃+* R[H]`.
* `TauCeti.NovikovSeries.coprodMonomialSubmonoid`,
  `TauCeti.NovikovSeries.localizationCoprodMonomialAlgEquiv`, and
  `TauCeti.NovikovSeries.liftCoprodOfPosMonomialIsUnit`: localization of
  `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` at degree-zero real monomials.

## Main results

* `TauCeti.NovikovSeries.mapPeriodRingHom_mem_periodFiltration`: period evaluation preserves every
  filtration level `U_C` with constant `1`.
* `TauCeti.NovikovSeries.mapPeriodRingHom_comp_inlRingHom` and
  `TauCeti.NovikovSeries.mapPeriodRingHom_comp_inrRingHom`: period evaluation on `H × ℝ` extends
  period evaluation on `H` and retracts `Nov(R, ℝ, id)`.
* `TauCeti.NovikovSeries.not_isUnit_coprodRealMonomial_of_pos` and
  `TauCeti.NovikovSeries.isUnit_coe_coprodRealMonomial`: `T^r` (`r > 0`) is non-invertible in
  `Nov≥0` (over a nontrivial ring) and invertible in `Nov`.
* `TauCeti.NovikovSeries.iSup_nonnegGradeBy_coprod_eq_top_iff`: the homogeneous pieces along
  `f ∘ Prod.fst` span `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` algebraically if and only if `range f` is
  finite.
* `TauCeti.NovikovSeries.isLocalization_coprodMonomialSubmonoid` and
  `TauCeti.NovikovSeries.mapPeriodRingHom_coprod_eq_liftCoprodOfPosMonomialIsUnit`: localization at
  degree-zero real monomials and compatibility of its universal property with period evaluation.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46, 2009, Chapter 2.
* P. Seidel, *Fukaya Categories and Picard–Lefschetz Theory*, EMS 2008, Section (8b).
-/

public section

noncomputable section

open Filter Function Set

namespace TauCeti.NovikovSeries

variable {A R S H ι : Type*}

section PeriodEvaluation

/-- Every period homomorphism `N : H →+ ℝ` is period-compatible with `id : ℝ →+ ℝ` with rescaling
constant `1`. -/
theorem exists_period_rescale_self [AddZeroClass H] (N : H →+ ℝ) :
    ∃ c > 0, ∀ h, (AddMonoidHom.id ℝ) (N h) = c * N h :=
  ⟨1, one_pos, fun h => by simp⟩

section Semiring

variable [AddMonoid H] [Semiring R] [Semiring S] (ρ : R →+* S) (N : H →+ ℝ)

/-- **Period-evaluation pushforward.** Collapsing exponents in `H` to their real periods `N h` along
a coefficient homomorphism `ρ : R →+* S` yields a ring homomorphism
`Nov(R, H, N) →+* Nov(S, ℝ, id)`. -/
def mapPeriodRingHom : NovikovSeries R H N →+* NovikovSeries S ℝ (AddMonoidHom.id ℝ) :=
  mapRingHom ρ N (exists_period_rescale_self N)

@[simp]
theorem mapPeriodRingHom_single (h : H) (r : R) :
    mapPeriodRingHom ρ N (single h r) = single (N h) (ρ r) := by
  simp [mapPeriodRingHom, map_single]

end Semiring

section Ring

variable [AddMonoid H] [Ring R] [Ring S] (ρ : R →+* S) (N : H →+ ℝ)

/-- Period evaluation preserves every filtration subgroup `U_C` without rescaling the cutoff. -/
theorem mapPeriodRingHom_mem_periodFiltration {C : ℝ} {a : NovikovSeries R H N}
    (ha : a ∈ periodFiltration R N C) :
    mapPeriodRingHom ρ N a ∈ periodFiltration S (AddMonoidHom.id ℝ) C := by
  rw [mapPeriodRingHom, mapRingHom_apply]
  simpa only [one_mul] using map_mem_periodFiltration (ρ : R →+ S) N
    (exists_period_rescale_self N) zero_le_one (fun h => by simp) ha

@[fun_prop]
theorem continuous_mapPeriodRingHom : Continuous (mapPeriodRingHom ρ N) :=
  continuous_mapRingHom ρ N (exists_period_rescale_self N)

/-- The restriction of the period-evaluation pushforward to the nonnegative Novikov subrings. -/
def mapPeriodNonnegSubring : nonnegSubring R N →+* nonnegSubring S (AddMonoidHom.id ℝ) :=
  mapNonnegSubring ρ N (exists_period_rescale_self N)

@[simp]
theorem coe_mapPeriodNonnegSubring (a : nonnegSubring R N) :
    (mapPeriodNonnegSubring ρ N a : NovikovSeries S ℝ (AddMonoidHom.id ℝ)) =
      mapPeriodRingHom ρ N a := by
  rw [mapPeriodNonnegSubring, coe_mapNonnegSubring, mapPeriodRingHom, mapRingHom_apply]

@[simp]
theorem mapPeriodNonnegSubring_nonnegMonomial {g : H} (hg : 0 ≤ N g) :
    mapPeriodNonnegSubring ρ N (nonnegMonomial R hg) =
      nonnegMonomial S (N := AddMonoidHom.id ℝ) hg :=
  Subtype.ext <| by simp

theorem mapPeriodNonnegSubring_mem_periodIdeal {C : ℝ} {a : nonnegSubring R N}
    (ha : a ∈ periodIdeal R N C) :
    mapPeriodNonnegSubring ρ N a ∈ periodIdeal S (AddMonoidHom.id ℝ) C := by
  rw [mem_periodIdeal, coe_mapPeriodNonnegSubring]
  exact mapPeriodRingHom_mem_periodFiltration ρ N (mem_periodIdeal.1 ha)

theorem mapPeriodNonnegSubring_mem_posIdeal {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) :
    mapPeriodNonnegSubring ρ N a ∈ posIdeal S (AddMonoidHom.id ℝ) :=
  mapNonnegSubring_mem_posIdeal ρ N (exists_period_rescale_self N) ha

@[fun_prop]
theorem continuous_mapPeriodNonnegSubring : Continuous (mapPeriodNonnegSubring ρ N) :=
  continuous_mapNonnegSubring ρ N (exists_period_rescale_self N)

end Ring

end PeriodEvaluation

section RealExtension

/-- Left inclusion `H →+ H × ℝ` preserves periods with constant `1` for `N.coprod (.id ℝ)`. -/
theorem exists_period_rescale_inl [AddMonoid H] (N : H →+ ℝ) :
    ∃ c > 0, ∀ h, (N.coprod (AddMonoidHom.id ℝ)) (AddMonoidHom.inl H ℝ h) = c * N h :=
  ⟨1, one_pos, fun h => by simp⟩

/-- Right inclusion `ℝ →+ H × ℝ` preserves periods with constant `1` for `N.coprod (.id ℝ)`. -/
theorem exists_period_rescale_inr [AddMonoid H] (N : H →+ ℝ) :
    ∃ c > 0,
      ∀ r, (N.coprod (AddMonoidHom.id ℝ)) (AddMonoidHom.inr H ℝ r) =
        c * (AddMonoidHom.id ℝ) r :=
  ⟨1, one_pos, fun r => by simp⟩

section Embeddings

variable [AddMonoid H]

/-- The canonical embedding `Nov(R, H, N) →+* Nov(R, H × ℝ, N.coprod (.id ℝ))` along
`h ↦ (h, 0)`. -/
def inlRingHom (R : Type*) [Semiring R] (N : H →+ ℝ) :
    NovikovSeries R H N →+* NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ)) :=
  mapRingHom (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

@[simp]
theorem inlRingHom_single [Semiring R] (N : H →+ ℝ) (h : H) (r : R) :
    inlRingHom R N (single h r) = single (h, (0 : ℝ)) r := by
  simp [inlRingHom, map_single]

theorem inlRingHom_injective [Semiring R] (N : H →+ ℝ) : Injective (inlRingHom R N) :=
  fun _ _ hab =>
    map_injective (RingHom.id R : R →+ R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)
      injective_id (fun _ _ h => (Prod.mk.inj h).1)
      (by simpa only [inlRingHom, mapRingHom_apply] using hab)

@[fun_prop]
theorem continuous_inlRingHom [Ring R] (N : H →+ ℝ) : Continuous (inlRingHom R N) :=
  continuous_mapRingHom (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

/-- The canonical embedding `Nov≥0(R, H, N) →+* Nov≥0(R, H × ℝ, N.coprod (.id ℝ))`. -/
def inlNonnegSubring (R : Type*) [Ring R] (N : H →+ ℝ) :
    nonnegSubring R N →+* nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) :=
  mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

@[simp]
theorem coe_inlNonnegSubring [Ring R] (N : H →+ ℝ) (a : nonnegSubring R N) :
    (inlNonnegSubring R N a : NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))) =
      inlRingHom R N a := by
  rw [inlNonnegSubring, coe_mapNonnegSubring, inlRingHom, mapRingHom_apply]

theorem inlNonnegSubring_injective [Ring R] (N : H →+ ℝ) : Injective (inlNonnegSubring R N) :=
  mapNonnegSubring_injective (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)
    injective_id (fun _ _ h => (Prod.mk.inj h).1)

@[fun_prop]
theorem continuous_inlNonnegSubring [Ring R] (N : H →+ ℝ) : Continuous (inlNonnegSubring R N) :=
  continuous_mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl H ℝ) (exists_period_rescale_inl N)

/-- Period evaluation on `H × ℝ` extends period evaluation on `H` along `inlRingHom`. -/
@[simp]
theorem mapPeriodRingHom_comp_inlRingHom [Semiring R] [Semiring S] (ρ : R →+* S) (N : H →+ ℝ) :
    (mapPeriodRingHom ρ (N.coprod (AddMonoidHom.id ℝ))).comp (inlRingHom R N) =
      mapPeriodRingHom ρ N := by
  rw [mapPeriodRingHom, inlRingHom, mapRingHom_comp]
  congr 1
  ext h
  simp

/-- The canonical embedding `Nov(R, ℝ, id) →+* Nov(R, H × ℝ, N.coprod (.id ℝ))` along
`r ↦ (0, r)`. -/
def inrRingHom (R : Type*) [Semiring R] (N : H →+ ℝ) :
    NovikovSeries R ℝ (AddMonoidHom.id ℝ) →+*
      NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ)) :=
  mapRingHom (RingHom.id R) (AddMonoidHom.inr H ℝ) (exists_period_rescale_inr N)

@[simp]
theorem inrRingHom_single [Semiring R] (N : H →+ ℝ) (r : ℝ) (c : R) :
    inrRingHom R N (single r c) = single ((0 : H), r) c := by
  simp [inrRingHom, map_single]

theorem inrRingHom_injective [Semiring R] (N : H →+ ℝ) : Injective (inrRingHom R N) :=
  fun _ _ hab =>
    map_injective (RingHom.id R : R →+ R) (AddMonoidHom.inr H ℝ) (exists_period_rescale_inr N)
      injective_id (fun _ _ h => (Prod.mk.inj h).2)
      (by simpa only [inrRingHom, mapRingHom_apply] using hab)

@[fun_prop]
theorem continuous_inrRingHom [Ring R] (N : H →+ ℝ) : Continuous (inrRingHom R N) :=
  continuous_mapRingHom (RingHom.id R) (AddMonoidHom.inr H ℝ) (exists_period_rescale_inr N)

/-- Period evaluation `Nov(R, H × ℝ, N.coprod (.id ℝ)) →+* Nov(R, ℝ, id)` is a ring retraction of
`inrRingHom`. -/
@[simp]
theorem mapPeriodRingHom_comp_inrRingHom [Semiring R] (N : H →+ ℝ) :
    (mapPeriodRingHom (RingHom.id R) (N.coprod (AddMonoidHom.id ℝ))).comp (inrRingHom R N) =
      RingHom.id _ := by
  rw [mapPeriodRingHom, inrRingHom, mapRingHom_comp]
  convert mapRingHom_id (R := R) (N := AddMonoidHom.id ℝ)
  ext r
  simp

/-- The canonical embedding `Nov≥0(R, ℝ, id) →+* Nov≥0(R, H × ℝ, N.coprod (.id ℝ))`. -/
def inrNonnegSubring (R : Type*) [Ring R] (N : H →+ ℝ) :
    nonnegSubring R (AddMonoidHom.id ℝ) →+*
      nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) :=
  mapNonnegSubring (RingHom.id R) (AddMonoidHom.inr H ℝ) (exists_period_rescale_inr N)

@[simp]
theorem coe_inrNonnegSubring [Ring R] (N : H →+ ℝ) (a : nonnegSubring R (AddMonoidHom.id ℝ)) :
    (inrNonnegSubring R N a : NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))) =
      inrRingHom R N a := by
  rw [inrNonnegSubring, coe_mapNonnegSubring, inrRingHom, mapRingHom_apply]

theorem inrNonnegSubring_injective [Ring R] (N : H →+ ℝ) : Injective (inrNonnegSubring R N) :=
  mapNonnegSubring_injective (RingHom.id R) (AddMonoidHom.inr H ℝ) (exists_period_rescale_inr N)
    injective_id (fun _ _ h => (Prod.mk.inj h).2)

@[fun_prop]
theorem continuous_inrNonnegSubring [Ring R] (N : H →+ ℝ) : Continuous (inrNonnegSubring R N) :=
  continuous_mapNonnegSubring (RingHom.id R) (AddMonoidHom.inr H ℝ) (exists_period_rescale_inr N)

end Embeddings

section CoprodRealMonomial

/-- The degree-zero real monomial `T^r = single (0, r) 1` inside
`Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` for `r ≥ 0`. -/
def coprodRealMonomial (R : Type*) [Ring R] [AddMonoid H] (N : H →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) :=
  nonnegMonomial R (N := N.coprod (AddMonoidHom.id ℝ)) (g := (0, r)) (by simpa using hr)

@[simp, norm_cast]
theorem coe_coprodRealMonomial [Ring R] [AddMonoid H] (N : H →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (coprodRealMonomial R N hr : NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))) =
      single ((0 : H), r) 1 :=
  coe_nonnegMonomial _

@[simp]
theorem coprodRealMonomial_zero [Ring R] [AddMonoid H] (N : H →+ ℝ) :
    coprodRealMonomial R N le_rfl = 1 :=
  Subtype.ext <| by simp [Prod.mk_zero_zero]

@[simp]
theorem coprodRealMonomial_add [Ring R] [AddMonoid H] (N : H →+ ℝ) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    coprodRealMonomial R N hr * coprodRealMonomial R N hs =
      coprodRealMonomial R N (add_nonneg hr hs) :=
  Subtype.ext <| by simp [single_mul_single]

@[simp]
theorem mapPeriodNonnegSubring_coprodRealMonomial [Ring R] [Ring S] [AddMonoid H]
    (ρ : R →+* S) (N : H →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    mapPeriodNonnegSubring ρ (N.coprod (AddMonoidHom.id ℝ)) (coprodRealMonomial R N hr) =
      nonnegMonomial S (N := AddMonoidHom.id ℝ) hr :=
  Subtype.ext <| by simp

/-- Every real monomial `T^r` (`r ≥ 0`) is homogeneous of degree `0` for any additive grading pulled
back from `H`. -/
theorem coprodRealMonomial_mem_nonnegGradeBy_zero [CommRing R] [AddMonoid H] [AddMonoid ι]
    (N : H →+ ℝ) (f : H →+ ι) {r : ℝ} (hr : 0 ≤ r) :
    coprodRealMonomial R N hr ∈
      nonnegGradeBy R (N.coprod (AddMonoidHom.id ℝ)) (f.comp (AddMonoidHom.fst H ℝ)) 0 := by
  rw [coprodRealMonomial]
  convert nonnegMonomial_mem_nonnegGradeBy (R := R)
    (N := N.coprod (AddMonoidHom.id ℝ)) (g := (0, r)) (by simpa using hr)
    (f.comp (AddMonoidHom.fst H ℝ))
  simp

/-- Every real monomial `T^r` (`r ≥ 0`) is a unit in `Nov(R, H × ℝ, N.coprod (.id ℝ))` with inverse
`T^(-r) = single (0, -r) 1`. -/
theorem isUnit_coe_coprodRealMonomial [Ring R] [AddGroup H] (N : H →+ ℝ) {r : ℝ} (hr : 0 ≤ r) :
    IsUnit (coprodRealMonomial R N hr :
      NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))) :=
  isUnit_coe_nonnegMonomial _

/-- Over a nontrivial coefficient ring, `T^r` (`r ≥ 0`) is a unit in
`Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` if and only if `r = 0`. -/
@[simp]
theorem isUnit_coprodRealMonomial_iff [Ring R] [Nontrivial R] [AddGroup H] (N : H →+ ℝ)
    {r : ℝ} (hr : 0 ≤ r) : IsUnit (coprodRealMonomial R N hr) ↔ r = 0 := by
  simp [coprodRealMonomial]

/-- Over a nontrivial coefficient ring, `T^r` is never a unit in
`Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` for `r > 0`. -/
theorem not_isUnit_coprodRealMonomial_of_pos [Ring R] [Nontrivial R] [AddGroup H] (N : H →+ ℝ)
    {r : ℝ} (hr : 0 < r) : ¬IsUnit (coprodRealMonomial R N hr.le) := by
  rw [isUnit_coprodRealMonomial_iff]
  exact hr.ne'

end CoprodRealMonomial

section FullGroupRingResidue

variable [AddGroup H]

/-- Sending `h : H` to `(h, -N h)` identifies `H` additively with the period-zero kernel of
`N.coprod (.id ℝ) : H × ℝ →+ ℝ`. -/
def coprodIdKerEquiv (N : H →+ ℝ) : H ≃+ (N.coprod (AddMonoidHom.id ℝ)).ker where
  toFun h := ⟨(h, -N h), AddMonoidHom.mem_ker.2 (by simp)⟩
  invFun k := k.1.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨h, r⟩, hk⟩
    refine Subtype.ext (Prod.ext rfl ?_)
    have h0 : N h + r = 0 := by simpa using AddMonoidHom.mem_ker.1 hk
    linarith
  map_add' h₁ h₂ := Subtype.ext <| Prod.ext rfl <| by simp [map_add, add_comm]

@[simp]
theorem coe_coprodIdKerEquiv_apply (N : H →+ ℝ) (h : H) :
    ((coprodIdKerEquiv N h : (N.coprod (AddMonoidHom.id ℝ)).ker) : H × ℝ) = (h, -N h) :=
  (rfl)

@[simp]
theorem coprodIdKerEquiv_symm_apply (N : H →+ ℝ) (k : (N.coprod (AddMonoidHom.id ℝ)).ker) :
    (coprodIdKerEquiv N).symm k = k.1.1 :=
  (rfl)

/-- **Full group-ring residue projection.** Projecting `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` to period
`0` and reindexing along `coprodIdKerEquiv` recovers the full group ring `R[H]`, reading off the
coefficient of each `h : H` at `(h, -N h)`. -/
def coprodResidueRingHom (R : Type*) [Ring R] (N : H →+ ℝ) :
    nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) →+* AddMonoidAlgebra R H :=
  (AddMonoidAlgebra.mapDomainRingEquiv R (coprodIdKerEquiv N).symm).toRingHom.comp
    (residueRingHom R (N.coprod (AddMonoidHom.id ℝ)))

@[simp]
theorem coeff_coprodResidueRingHom [Ring R] (N : H →+ ℝ)
    (a : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ))) (h : H) :
    (coprodResidueRingHom R N a).coeff h =
      (a : NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))).coeff (h, -N h) := by
  simp [coprodResidueRingHom]

@[simp]
theorem ker_coprodResidueRingHom [Ring R] (N : H →+ ℝ) :
    RingHom.ker (coprodResidueRingHom R N) = posIdeal R (N.coprod (AddMonoidHom.id ℝ)) := by
  ext a
  rw [RingHom.mem_ker, coprodResidueRingHom, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_eq_zero_iff _ (RingEquiv.injective _),
    ← RingHom.mem_ker, ker_residueRingHom]

/-- **Period-compensated group-ring section.** Sending `single h c` to `single (h, -N h) c` embeds
the full group ring `R[H]` into `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` as a right inverse to
`coprodResidueRingHom`. -/
def ofAddMonoidAlgebraCoprod (R : Type*) [Ring R] (N : H →+ ℝ) :
    AddMonoidAlgebra R H →+* nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) :=
  (ofKerAddMonoidAlgebra R (N.coprod (AddMonoidHom.id ℝ))).comp
    (AddMonoidAlgebra.mapDomainRingEquiv R (coprodIdKerEquiv N)).toRingHom

@[simp]
theorem ofAddMonoidAlgebraCoprod_single [Ring R] (N : H →+ ℝ) (h : H) (c : R) :
    ofAddMonoidAlgebraCoprod R N (AddMonoidAlgebra.single h c) =
      ⟨single (h, -N h) c,
        single_mem_nonnegSubring (N := N.coprod (AddMonoidHom.id ℝ)) (by simp) c⟩ := by
  ext p
  simp [ofAddMonoidAlgebraCoprod]

theorem coprodResidueRingHom_ofAddMonoidAlgebraCoprod [Ring R] (N : H →+ ℝ) :
    RightInverse (ofAddMonoidAlgebraCoprod R N) (coprodResidueRingHom R N) := fun x => by
  rw [coprodResidueRingHom, ofAddMonoidAlgebraCoprod, RingHom.comp_apply, RingHom.comp_apply,
    residueRingHom_ofKerAddMonoidAlgebra]
  exact (AddMonoidAlgebra.mapDomainRingEquiv R (coprodIdKerEquiv N)).symm_apply_apply x

/-- **Full group-ring residue isomorphism.** After adjoining a real period coordinate via
`N.coprod (.id ℝ)`, the quotient of the nonnegative Novikov subring by `posIdeal` is canonically
isomorphic to the full group ring `R[H]`. -/
def quotientPosIdealCoprodEquiv (R : Type*) [Ring R] (N : H →+ ℝ) :
    (nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) ⧸
      posIdeal R (N.coprod (AddMonoidHom.id ℝ))) ≃+* AddMonoidAlgebra R H :=
  (quotientPosIdealEquiv R (N.coprod (AddMonoidHom.id ℝ))).trans
    (AddMonoidAlgebra.mapDomainRingEquiv R (coprodIdKerEquiv N).symm)

@[simp]
theorem quotientPosIdealCoprodEquiv_mk [Ring R] (N : H →+ ℝ)
    (a : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ))) :
    quotientPosIdealCoprodEquiv R N
        (Ideal.Quotient.mk (posIdeal R (N.coprod (AddMonoidHom.id ℝ))) a) =
      coprodResidueRingHom R N a := by
  simp [quotientPosIdealCoprodEquiv, coprodResidueRingHom]

@[simp]
theorem quotientPosIdealCoprodEquiv_symm [Ring R] (N : H →+ ℝ) (x : AddMonoidAlgebra R H) :
    (quotientPosIdealCoprodEquiv R N).symm x =
      Ideal.Quotient.mk (posIdeal R (N.coprod (AddMonoidHom.id ℝ)))
        (ofAddMonoidAlgebraCoprod R N x) := by
  simp [quotientPosIdealCoprodEquiv, ofAddMonoidAlgebraCoprod]

/-- The `A`-algebra version of `quotientPosIdealCoprodEquiv`. -/
def quotientPosIdealCoprodAlgEquiv (A R : Type*) [CommSemiring A] [Ring R] [Algebra A R]
    (N : H →+ ℝ) :
    (nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) ⧸
      posIdeal R (N.coprod (AddMonoidHom.id ℝ))) ≃ₐ[A] AddMonoidAlgebra R H :=
  (quotientPosIdealAlgEquiv A R (N.coprod (AddMonoidHom.id ℝ))).trans
    (AddMonoidAlgebra.domCongr A R (coprodIdKerEquiv N).symm)

@[simp]
theorem quotientPosIdealCoprodAlgEquiv_mk (A R : Type*) [CommSemiring A] [Ring R] [Algebra A R]
    (N : H →+ ℝ) (a : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ))) :
    quotientPosIdealCoprodAlgEquiv A R N
        (Ideal.Quotient.mk (posIdeal R (N.coprod (AddMonoidHom.id ℝ))) a) =
      coprodResidueRingHom R N a := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun h => ?_)
  simp [quotientPosIdealCoprodAlgEquiv]

@[simp]
theorem quotientPosIdealCoprodAlgEquiv_symm (A R : Type*) [CommSemiring A] [Ring R] [Algebra A R]
    (N : H →+ ℝ) (x : AddMonoidAlgebra R H) :
    (quotientPosIdealCoprodAlgEquiv A R N).symm x =
      Ideal.Quotient.mk (posIdeal R (N.coprod (AddMonoidHom.id ℝ)))
        (ofAddMonoidAlgebraCoprod R N x) := by
  have heq : AddMonoidAlgebra.domCongr A R (coprodIdKerEquiv N) x =
      AddMonoidAlgebra.mapDomainRingEquiv R (coprodIdKerEquiv N) x :=
    AddMonoidAlgebra.coeff_injective (Finsupp.ext fun k => by simp)
  simp [quotientPosIdealCoprodAlgEquiv, ofAddMonoidAlgebraCoprod, heq]

/-- The period-compensated embedding `R[H] →+* Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` preserves and
reflects homogeneous degrees for any degree function pulled back from `H`. -/
theorem ofAddMonoidAlgebraCoprod_mem_nonnegGradeBy_iff [CommRing R] (N : H →+ ℝ)
    {f : H → ι} {i : ι} {x : AddMonoidAlgebra R H} :
    ofAddMonoidAlgebraCoprod R N x ∈
        nonnegGradeBy R (N.coprod (AddMonoidHom.id ℝ)) (f ∘ Prod.fst) i ↔
      x ∈ AddMonoidAlgebra.gradeBy R f i := by
  classical
  rw [ofAddMonoidAlgebraCoprod, RingHom.comp_apply, ofKerAddMonoidAlgebra_mem_nonnegGradeBy_iff,
    AddMonoidAlgebra.mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff]
  constructor
  · intro hx h hh
    have hm : coprodIdKerEquiv N h ∈
        ((AddMonoidAlgebra.mapDomainRingEquiv R (coprodIdKerEquiv N)) x).coeff.support := by
      rw [Finset.mem_coe] at hh
      rw [Finsupp.mem_support_iff] at hh ⊢
      simpa using hh
    exact hx hm
  · intro hx k hk
    have hm : (coprodIdKerEquiv N).symm k ∈ x.coeff.support := by
      rw [Finset.mem_coe] at hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      simpa using hk
    simpa using hx hm

end FullGroupRingResidue

section GradingCharacterization

/-- **Exact algebraic spanning criterion on the real-extended nonnegative Novikov ring.** Over a
nontrivial commutative ring, the homogeneous pieces of `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` along
`f ∘ Prod.fst` span the whole nonnegative subring algebraically if and only if `range f` is finite
(whereas their topological closure is always `⊤` by `topologicalClosure_iSup_nonnegGradeBy`). -/
theorem iSup_nonnegGradeBy_coprod_eq_top_iff [CommRing R] [Nontrivial R] [AddMonoid H]
    (N : H →+ ℝ) (f : H → ι) :
    ⨆ i, nonnegGradeBy R (N.coprod (AddMonoidHom.id ℝ)) (f ∘ Prod.fst) i = ⊤ ↔
      (range f).Finite := by
  constructor
  · intro htop
    by_contra hinf
    have hinf' : (range f).Infinite := hinf
    let e := hinf'.natEmbedding
    let h : ℕ → H := fun n => (e n).2.choose
    have hfh (n : ℕ) : f (h n) = (e n).1 := (e n).2.choose_spec
    let g : ℕ → H × ℝ := fun n => (h n, max 0 (-N (h n)) + n)
    have hge (n : ℕ) : (n : ℝ) ≤ (N.coprod (AddMonoidHom.id ℝ)) (g n) := by
      have hle : -N (h n) ≤ max 0 (-N (h n)) := le_max_right 0 (-N (h n))
      simp only [AddMonoidHom.coprod_apply, AddMonoidHom.id_apply, g]
      linarith
    have hnonneg (n : ℕ) : 0 ≤ (N.coprod (AddMonoidHom.id ℝ)) (g n) :=
      (Nat.cast_nonneg n).trans (hge n)
    have htend : Tendsto (fun n => (N.coprod (AddMonoidHom.id ℝ)) (g n)) atTop atTop :=
      tendsto_atTop_mono hge tendsto_natCast_atTop_atTop
    have hinj : Injective ((f ∘ Prod.fst) ∘ g) := fun m n hmn => by
      apply e.injective
      apply Subtype.ext
      simpa only [Function.comp_apply, g, hfh] using hmn
    exact iSup_nonnegGradeBy_ne_top_of_tendsto (R := R) hnonneg htend hinj htop
  · intro hfin
    exact iSup_nonnegGradeBy_eq_top_of_finite_range
      (hfin.subset (range_comp_subset_range Prod.fst f))

end GradingCharacterization

section CoprodLocalization

variable [CommRing R] [AddCommGroup H]

/-- The additive submonoid `{(0, r) : r ≥ 0} ≤ H × ℝ` of nonnegative real periods in degree `0`. -/
def coprodNonnegRealAddSubmonoid (H : Type*) [AddZeroClass H] : AddSubmonoid (H × ℝ) where
  carrier := {p | p.1 = 0 ∧ 0 ≤ p.2}
  zero_mem' := ⟨rfl, le_rfl⟩
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], add_nonneg ha.2 hb.2⟩

@[simp]
theorem mem_coprodNonnegRealAddSubmonoid_iff {p : H × ℝ} :
    p ∈ coprodNonnegRealAddSubmonoid H ↔ p.1 = 0 ∧ 0 ≤ p.2 :=
  Iff.rfl

theorem coprod_nonneg_of_mem_coprodNonnegRealAddSubmonoid (N : H →+ ℝ) :
    ∀ p ∈ coprodNonnegRealAddSubmonoid H, 0 ≤ (N.coprod (AddMonoidHom.id ℝ)) p := by
  intro p hp
  rw [AddMonoidHom.coprod_apply, hp.1, map_zero, zero_add, AddMonoidHom.id_apply]
  exact hp.2

theorem eq_zero_of_mem_coprodNonnegRealAddSubmonoid_of_coprod_eq_zero (N : H →+ ℝ) :
    ∀ p ∈ coprodNonnegRealAddSubmonoid H, (N.coprod (AddMonoidHom.id ℝ)) p = 0 → p = 0 := by
  rintro ⟨h, r⟩ hp h0
  have hh : h = 0 := hp.1
  subst hh
  exact Prod.ext rfl (by simpa using h0)

/-- The multiplicative submonoid `{T^r : r ≥ 0}` of degree-zero real monomials in
`Nov≥0(R, H × ℝ, N.coprod (.id ℝ))`. -/
def coprodMonomialSubmonoid (R : Type*) [CommRing R] (N : H →+ ℝ) :
    Submonoid (nonnegSubring R (N.coprod (AddMonoidHom.id ℝ))) :=
  monomialSubmonoid R (P := coprodNonnegRealAddSubmonoid H)
    (coprod_nonneg_of_mem_coprodNonnegRealAddSubmonoid N)

@[simp]
theorem mem_coprodMonomialSubmonoid_iff {N : H →+ ℝ}
    {x : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ))} :
    x ∈ coprodMonomialSubmonoid R N ↔
      ∃ (r : ℝ) (hr : 0 ≤ r), coprodRealMonomial R N hr = x := by
  rw [coprodMonomialSubmonoid, mem_monomialSubmonoid_iff]
  constructor
  · rintro ⟨⟨h, r⟩, hp, rfl⟩
    have hh : h = 0 := hp.1
    exact ⟨r, hp.2, Subtype.ext (by simp [hh])⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(0, r), ⟨rfl, hr⟩, Subtype.ext (by simp)⟩

/-- The multiplicative submonoid generated by strictly positive degree-zero real monomials
`{T^r : r > 0}` coincides with `coprodMonomialSubmonoid R N`. -/
theorem closure_posCoprodRealMonomial_eq_coprodMonomialSubmonoid (R : Type*) [CommRing R]
    (N : H →+ ℝ) :
    Submonoid.closure
      {x : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) |
        ∃ (r : ℝ) (hr : 0 < r), coprodRealMonomial R N hr.le = x} =
      coprodMonomialSubmonoid R N := by
  rw [coprodMonomialSubmonoid, ← closure_posMonomial_eq_monomialSubmonoid (R := R)
    (N := N.coprod (AddMonoidHom.id ℝ)) (P := coprodNonnegRealAddSubmonoid H)
    (coprod_nonneg_of_mem_coprodNonnegRealAddSubmonoid N)
    (eq_zero_of_mem_coprodNonnegRealAddSubmonoid_of_coprod_eq_zero N)]
  congr 1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(0, r), ⟨rfl, hr.le⟩, by simpa using hr, Subtype.ext (by simp)⟩
  · rintro ⟨⟨h, r⟩, hp, hpos, rfl⟩
    have hh : h = 0 := hp.1
    subst hh
    exact ⟨r, by simpa using hpos, Subtype.ext (by simp)⟩

/-- **Localization of the real-extended nonnegative Novikov ring.** Inverting the degree-zero real
monomials `{T^r : r ≥ 0}` (or `{T^r : r > 0}`) localizes `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` onto
`Nov(R, H × ℝ, N.coprod (.id ℝ))`. -/
instance isLocalization_coprodMonomialSubmonoid (R : Type*) [CommRing R] (N : H →+ ℝ) :
    IsLocalization (coprodMonomialSubmonoid R N)
      (NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))) :=
  isLocalization_monomialSubmonoid_of_exists_pos (P := coprodNonnegRealAddSubmonoid H)
    (coprod_nonneg_of_mem_coprodNonnegRealAddSubmonoid N)
    ⟨((0 : H), (1 : ℝ)), ⟨rfl, zero_le_one⟩, by simp⟩

/-- Inverting any single positive real monomial `T^r` (`r > 0`) already localizes
`Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` onto `Nov(R, H × ℝ, N.coprod (.id ℝ))`. -/
theorem isLocalization_away_coprodRealMonomial (N : H →+ ℝ) {r : ℝ} (hr : 0 < r) :
    IsLocalization.Away (coprodRealMonomial R N hr.le)
      (NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))) :=
  isLocalization_away_nonnegMonomial (g := (0, r)) (by simpa using hr)

/-- The canonical `Nov≥0(R, H × ℝ, N.coprod (.id ℝ))`-algebra isomorphism from
`Localization (coprodMonomialSubmonoid R N)` onto `Nov(R, H × ℝ, N.coprod (.id ℝ))`. -/
def localizationCoprodMonomialAlgEquiv (R : Type*) [CommRing R] (N : H →+ ℝ) :
    Localization (coprodMonomialSubmonoid R N) ≃ₐ[nonnegSubring R (N.coprod (AddMonoidHom.id ℝ))]
      NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ)) :=
  Localization.algEquiv (coprodMonomialSubmonoid R N)
    (NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ)))

/-- **Universal property of `Nov(R, H × ℝ, N.coprod (.id ℝ))`.** Any ring homomorphism out of
`Nov≥0(R, H × ℝ, N.coprod (.id ℝ))` into a commutative ring `A` sending `T^r` to a unit for every
`r > 0` extends uniquely to `Nov(R, H × ℝ, N.coprod (.id ℝ))`. -/
def liftCoprodOfPosMonomialIsUnit [CommRing A] {N : H →+ ℝ}
    (φ : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) →+* A)
    (hunit : ∀ (r : ℝ) (hr : 0 < r), IsUnit (φ (coprodRealMonomial R N hr.le))) :
    NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ)) →+* A :=
  liftOfPosMonomialIsUnit (P := coprodNonnegRealAddSubmonoid H)
    (coprod_nonneg_of_mem_coprodNonnegRealAddSubmonoid N)
    (eq_zero_of_mem_coprodNonnegRealAddSubmonoid_of_coprod_eq_zero N)
    ⟨((0 : H), (1 : ℝ)), ⟨rfl, zero_le_one⟩, by simp⟩ φ fun ⟨h, r⟩ hp hpos => by
      have hh : h = 0 := hp.1
      subst hh
      have hr : 0 < r := by simpa using hpos
      have heq : nonnegMonomial R (N := N.coprod (AddMonoidHom.id ℝ)) hpos.le =
          coprodRealMonomial R N hr.le := Subtype.ext (by simp)
      rw [heq]
      exact hunit r hr

@[simp]
theorem liftCoprodOfPosMonomialIsUnit_coe [CommRing A] {N : H →+ ℝ}
    (φ : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) →+* A)
    (hunit : ∀ (r : ℝ) (hr : 0 < r), IsUnit (φ (coprodRealMonomial R N hr.le)))
    (a : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ))) :
    liftCoprodOfPosMonomialIsUnit φ hunit
        (a : NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ))) = φ a :=
  liftOfPosMonomialIsUnit_coe (P := coprodNonnegRealAddSubmonoid H) _ _ _ φ _ a

theorem liftCoprodOfPosMonomialIsUnit_unique [CommRing A] {N : H →+ ℝ}
    (φ : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)) →+* A)
    (hunit : ∀ (r : ℝ) (hr : 0 < r), IsUnit (φ (coprodRealMonomial R N hr.le)))
    {ψ : NovikovSeries R (H × ℝ) (N.coprod (AddMonoidHom.id ℝ)) →+* A}
    (hψ : ∀ a : nonnegSubring R (N.coprod (AddMonoidHom.id ℝ)), ψ a = φ a) :
    ψ = liftCoprodOfPosMonomialIsUnit φ hunit :=
  liftOfPosMonomialIsUnit_unique (P := coprodNonnegRealAddSubmonoid H) _ _ _ φ _ hψ

/-- **Compatibility of localization with period evaluation.** Extending the nonnegative
period-evaluation homomorphism `Nov≥0(R, H × ℝ, N.coprod (.id ℝ)) →+* Nov(S, ℝ, id)` via the
universal property of localization recovers the ambient period-evaluation homomorphism
`mapPeriodRingHom ρ (N.coprod (.id ℝ))`. -/
theorem mapPeriodRingHom_coprod_eq_liftCoprodOfPosMonomialIsUnit [CommRing S]
    (ρ : R →+* S) (N : H →+ ℝ) :
    mapPeriodRingHom ρ (N.coprod (AddMonoidHom.id ℝ)) =
      liftCoprodOfPosMonomialIsUnit
        ((nonnegSubring S (AddMonoidHom.id ℝ)).subtype.comp
          (mapPeriodNonnegSubring ρ (N.coprod (AddMonoidHom.id ℝ))))
        (fun r hr => by
          rw [RingHom.comp_apply, mapPeriodNonnegSubring_coprodRealMonomial]
          exact isUnit_coe_nonnegMonomial hr.le) :=
  liftCoprodOfPosMonomialIsUnit_unique _ _ fun a =>
    (coe_mapPeriodNonnegSubring ρ (N.coprod (AddMonoidHom.id ℝ)) a).symm

end CoprodLocalization

end RealExtension

end TauCeti.NovikovSeries
