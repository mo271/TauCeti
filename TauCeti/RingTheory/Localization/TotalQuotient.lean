/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.IsField
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.Regular.Submonoid
public import TauCeti.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Total quotients of commutative semirings

The total quotient `TauCeti.TotalQuotient R` of a commutative semiring `R` is its localization at
the submonoid `TauCeti.regulars R` of regular elements. The canonical map from `R` is injective,
and Mathlib's `IsLocalization` API supplies the universal property: a semiring map out of `R`
extends to the total quotient, necessarily uniquely, exactly when it sends regular elements to
units (`IsLocalization.lift`, `IsLocalization.ringHom_ext` and `IsLocalization.isUnit_comp`).

For a commutative ring the regular elements are the non-zero-divisors
(`TauCeti.regulars_eq_nonZeroDivisors`), so the total quotient is Mathlib's `FractionRing`. For
semirings the two submonoids can differ, and this localization is the one that keeps `R` inside.
When multiplication cancels nonzero elements, the two submonoids again agree, so the total quotient
identifies with any fraction semiring (`TauCeti.TotalQuotient.algEquivOfIsFractionRing`), in
particular `TotalQuotient ℕ ≃ₐ[ℕ] ℚ≥0`.

Any localization of a commutative semiring in which sums vanish only when every summand does
inherits this property (`IsLocalization.subsingleton_addUnits`). The total quotient of a
semiring domain is a semifield, in which a fraction is the quotient of its numerator by its
denominator. Semiring and algebra isomorphisms induce isomorphisms of total quotients
(`TauCeti.TotalQuotient.ringEquivOfRingEquiv`, `TauCeti.TotalQuotient.algEquivOfAlgEquiv`).

Localizing a commutative semiring `R` at a submonoid `M ≤ regulars R` does not change its total
quotient: every element of `R` maps to a regular element of `S` iff it is already regular
(`TauCeti.TotalQuotient.comap_regulars_eq`), giving a canonical `R`-algebra isomorphism
`TauCeti.TotalQuotient.localizationEquiv : TotalQuotient S ≃ₐ[R] TotalQuotient R` commuting with
the base maps and with `IsLocalization.lift`. Specializing to a single regular element `e` yields
`TauCeti.TotalQuotient.awayEquiv : TotalQuotient (Localization.Away e) ≃ₐ[R] TotalQuotient R`.
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace TauCeti

/-- The total quotient of a commutative semiring: its localization at all regular elements. -/
abbrev TotalQuotient (R : Type*) [CommSemiring R] := Localization (regulars R)

namespace TotalQuotient

variable {R : Type*} [CommSemiring R]

/-- A commutative semiring embeds in its total quotient. -/
instance : FaithfulSMul R (TotalQuotient R) :=
  (faithfulSMul_iff_algebraMap_injective R _).mpr <|
    IsLocalization.injectiveₛ _ fun _ ↦ mem_regulars.mp

/-- The total quotient inherits zero-sum-freeness. -/
instance [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (TotalQuotient R)) :=
  IsLocalization.subsingleton_addUnits (regulars R) _

/-- The total quotient of a semiring domain satisfies `IsField`: every nonzero element has a
multiplicative inverse, so it carries a semifield structure (a field only when `R` is a ring). -/
theorem isField [IsDomain R] : IsField (TotalQuotient R) where
  exists_pair_ne := ⟨0, 1, fun h ↦ zero_ne_one <|
    FaithfulSMul.algebraMap_injective R (TotalQuotient R) (by simpa using h)⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regulars R) a
    have hr : r ∈ regulars R :=
      mem_regulars_iff_ne_zero.mpr (IsLocalization.ne_zero_of_mk'_ne_zero ha)
    exact ⟨IsLocalization.mk' _ (s : R) ⟨r, hr⟩, IsLocalization.mk'_mul_mk'_eq_one' r s hr⟩

/-- The total quotient of a semiring domain is a semifield. -/
instance [IsDomain R] : Semifield (TotalQuotient R) :=
  isField.toSemifield

/-- In the total quotient of a semiring domain, a fraction is the quotient of the images of its
numerator and denominator. -/
theorem mk'_eq_div [IsDomain R] (r : R) (s : regulars R) :
    IsLocalization.mk' (TotalQuotient R) r s =
      algebraMap R (TotalQuotient R) r / algebraMap R (TotalQuotient R) s := by
  rw [eq_div_iff (IsLocalization.map_units _ s).ne_zero, IsLocalization.mk'_spec]

/-! ### Functoriality under equivalences -/

section RingEquiv

variable {S T : Type*} [CommSemiring S] [CommSemiring T]

/-- A semiring equivalence induces a semiring equivalence of total quotients. -/
def ringEquivOfRingEquiv (e : R ≃+* S) : TotalQuotient R ≃+* TotalQuotient S :=
  IsLocalization.ringEquivOfRingEquiv (TotalQuotient R) (TotalQuotient S) e
    (map_regulars e.toMulEquiv)

@[simp]
theorem ringEquivOfRingEquiv_algebraMap (e : R ≃+* S) (r : R) :
    ringEquivOfRingEquiv e (algebraMap R (TotalQuotient R) r) =
      algebraMap S (TotalQuotient S) (e r) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ r

@[simp]
theorem ringEquivOfRingEquiv_mk' (e : R ≃+* S) (r : R) (s : regulars R) :
    ringEquivOfRingEquiv e (IsLocalization.mk' (TotalQuotient R) r s) =
      IsLocalization.mk' (TotalQuotient S) (e r)
        ⟨e s, mem_regulars.mpr (e.toMulEquiv.isRegular_iff.mpr (mem_regulars.mp s.2))⟩ :=
  IsLocalization.ringEquivOfRingEquiv_mk' _ r s

@[simp]
theorem ringEquivOfRingEquiv_refl :
    ringEquivOfRingEquiv (RingEquiv.refl R) = RingEquiv.refl (TotalQuotient R) := by
  ext x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regulars R) x
  simp

@[simp]
theorem ringEquivOfRingEquiv_symm (e : R ≃+* S) :
    (ringEquivOfRingEquiv e).symm = ringEquivOfRingEquiv e.symm :=
  IsLocalization.ringEquivOfRingEquiv_symm (map_regulars e.toMulEquiv)

@[simp]
theorem ringEquivOfRingEquiv_trans (e : R ≃+* S) (f : S ≃+* T) :
    (ringEquivOfRingEquiv e).trans (ringEquivOfRingEquiv f) = ringEquivOfRingEquiv (e.trans f) := by
  ext x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regulars R) x
  simp

/-- An algebra equivalence induces an algebra equivalence of total quotients. -/
def algEquivOfAlgEquiv {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S] (e : R ≃ₐ[A] S) :
    TotalQuotient R ≃ₐ[A] TotalQuotient S :=
  IsLocalization.algEquivOfAlgEquiv (TotalQuotient R) (TotalQuotient S) e
    (map_regulars e.toMulEquiv)

@[simp]
theorem algEquivOfAlgEquiv_algebraMap {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S]
    (e : R ≃ₐ[A] S) (r : R) :
    algEquivOfAlgEquiv e (algebraMap R (TotalQuotient R) r) =
      algebraMap S (TotalQuotient S) (e r) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ r

@[simp]
theorem algEquivOfAlgEquiv_mk' {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S]
    (e : R ≃ₐ[A] S) (r : R) (s : regulars R) :
    algEquivOfAlgEquiv e (IsLocalization.mk' (TotalQuotient R) r s) =
      IsLocalization.mk' (TotalQuotient S) (e r)
        ⟨e s, mem_regulars.mpr (e.toMulEquiv.isRegular_iff.mpr (mem_regulars.mp s.2))⟩ :=
  IsLocalization.algEquivOfAlgEquiv_mk' _ r s

@[simp]
theorem algEquivOfAlgEquiv_refl {A : Type*} [CommSemiring A] [Algebra A R] :
    algEquivOfAlgEquiv (AlgEquiv.refl : R ≃ₐ[A] R) = AlgEquiv.refl := by
  ext x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regulars R) x
  simp

@[simp]
theorem algEquivOfAlgEquiv_symm {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S]
    (e : R ≃ₐ[A] S) :
    (algEquivOfAlgEquiv e).symm = algEquivOfAlgEquiv e.symm :=
  IsLocalization.algEquivOfAlgEquiv_symm (map_regulars e.toMulEquiv)

@[simp]
theorem algEquivOfAlgEquiv_trans {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S]
    [Algebra A T] (e : R ≃ₐ[A] S) (f : S ≃ₐ[A] T) :
    (algEquivOfAlgEquiv e).trans (algEquivOfAlgEquiv f) = algEquivOfAlgEquiv (e.trans f) := by
  ext x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regulars R) x
  simp

end RingEquiv

/-! ### Comparison with fraction semirings -/

section FractionRing

/-- For a commutative semiring whose multiplication cancels nonzero elements, any fraction
semiring is a localization at the regular elements. -/
theorem isLocalization_of_isFractionRing [IsCancelMulZero R] (K : Type*) [CommSemiring K]
    [Algebra R K] [IsFractionRing R K] : IsLocalization (regulars R) K := by
  rwa [regulars_eq_nonZeroDivisors_of_isCancelMulZero R]

/-- For a commutative semiring whose multiplication cancels nonzero elements, the total quotient
is canonically isomorphic to any fraction semiring (for instance, `TotalQuotient ℕ ≃ₐ[ℕ] ℚ≥0` and
`TotalQuotient R ≃ₐ[R] FractionRing R` for a domain `R`). -/
def algEquivOfIsFractionRing [IsCancelMulZero R] (K : Type*) [CommSemiring K] [Algebra R K]
    [IsFractionRing R K] : TotalQuotient R ≃ₐ[R] K :=
  haveI := isLocalization_of_isFractionRing (R := R) K
  IsLocalization.algEquiv (regulars R) (TotalQuotient R) K

theorem algEquivOfIsFractionRing_algebraMap [IsCancelMulZero R] (K : Type*) [CommSemiring K]
    [Algebra R K] [IsFractionRing R K] (r : R) :
    algEquivOfIsFractionRing K (algebraMap R (TotalQuotient R) r) = algebraMap R K r :=
  (algEquivOfIsFractionRing K).commutes r

@[simp]
theorem algEquivOfIsFractionRing_mk' [IsCancelMulZero R] (K : Type*) [CommSemiring K]
    [Algebra R K] [IsFractionRing R K] (r : R) (s : regulars R) :
    algEquivOfIsFractionRing K (IsLocalization.mk' (TotalQuotient R) r s) =
      IsLocalization.mk' K r ⟨s, (regulars_eq_nonZeroDivisors_of_isCancelMulZero R).le s.2⟩ := by
  have := isLocalization_of_isFractionRing (R := R) K
  apply (IsLocalization.map_units K ⟨(s : R),
    (regulars_eq_nonZeroDivisors_of_isCancelMulZero R).le s.2⟩).mul_right_inj.mp
  rw [IsLocalization.mk'_spec', ← algEquivOfIsFractionRing_algebraMap K (s : R), ← map_mul,
    IsLocalization.mk'_spec', algEquivOfIsFractionRing_algebraMap]

end FractionRing

/-! ### Invariance under localization at regular elements -/

section Localization

variable (M : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization M S]

/-- In a localization at regular elements, an element of the base semiring maps to a regular
element if and only if it is already regular. -/
theorem comap_regulars_eq (hM : M ≤ regulars R) :
    (regulars S).comap (algebraMap R S) = regulars R := by
  ext r
  have hr : algebraMap R S r = IsLocalization.mk' S r (1 : M) :=
    (IsLocalization.mk'_one (M := M) S r).symm
  simpa [hr, mem_regulars] using IsLocalization.isRegular_mk' (S := S) (M := M)
    (fun m hm ↦ mem_regulars.mp (hM hm)) (r := r) (m := 1)

/-- A total quotient of a localization at regular elements is a total quotient of the base
semiring. -/
theorem isLocalization_of_isLocalization (T : Type*) [CommSemiring T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization (regulars S) T] (hM : M ≤ regulars R) :
    IsLocalization (regulars R) T := by
  rw [← comap_regulars_eq M S hM]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units M (regulars S) T
    fun _ hx ↦ mem_regulars.mpr hx.isRegular

/-- A total quotient of a commutative semiring is also a total quotient of any intermediate
localization at regular elements. -/
theorem isLocalization_regulars_of_isLocalization (T : Type*) [CommSemiring T] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [IsLocalization (regulars R) T] (hM : M ≤ regulars R) :
    IsLocalization (regulars S) T := by
  have := IsLocalization.isLocalization_of_submonoid_le S T M (regulars R) hM
  refine IsLocalization.isLocalization_of_is_exists_mul_mem (S := T)
    ((regulars R).map (algebraMap R S)) (regulars S) ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact Submonoid.mem_comap.mp ((comap_regulars_eq M S hM).ge hr)
  · rintro ⟨x, hx⟩
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    have hr : r ∈ regulars R := mem_regulars.mpr <|
      (IsLocalization.isRegular_mk' (S := S) (fun _ hm ↦ mem_regulars.mp (hM hm))).mp
        (mem_regulars.mp hx)
    exact ⟨algebraMap R S m, by
      dsimp only
      rw [IsLocalization.mk'_spec']
      exact Submonoid.mem_map_of_mem _ hr⟩

/-- The total quotient of a localization at regular elements is canonically isomorphic, as an
algebra over the base semiring, to the total quotient of the base semiring. -/
def localizationEquiv (hM : M ≤ regulars R) : TotalQuotient S ≃ₐ[R] TotalQuotient R :=
  haveI := isLocalization_of_isLocalization M S (TotalQuotient S) hM
  IsLocalization.algEquiv (regulars R) (TotalQuotient S) (TotalQuotient R)

@[simp]
theorem localizationEquiv_algebraMap (hM : M ≤ regulars R) (r : R) :
    localizationEquiv M S hM (algebraMap S (TotalQuotient S) (algebraMap R S r)) =
      algebraMap R (TotalQuotient R) r := by
  rw [← IsScalarTower.algebraMap_apply R S (TotalQuotient S)]
  exact (localizationEquiv M S hM).commutes r

theorem localizationEquiv_symm_algebraMap (hM : M ≤ regulars R) (r : R) :
    (localizationEquiv M S hM).symm (algebraMap R (TotalQuotient R) r) =
      algebraMap S (TotalQuotient S) (algebraMap R S r) := by
  rw [AlgEquiv.symm_apply_eq, localizationEquiv_algebraMap]

@[simp]
theorem localizationEquiv_algebraMap_mk' (hM : M ≤ regulars R) (r : R) (m : M) :
    localizationEquiv M S hM (algebraMap S (TotalQuotient S) (IsLocalization.mk' S r m)) =
      IsLocalization.mk' (TotalQuotient R) r ⟨m, hM m.2⟩ := by
  apply (IsLocalization.map_units (TotalQuotient R) ⟨(m : R), hM m.2⟩).mul_right_inj.mp
  rw [IsLocalization.mk'_spec', ← localizationEquiv_algebraMap M S hM (m : R), ← map_mul,
    ← map_mul, IsLocalization.mk'_spec', localizationEquiv_algebraMap]

@[simp]
theorem localizationEquiv_symm_mk' (hM : M ≤ regulars R) (r : R) (m : M) :
    (localizationEquiv M S hM).symm (IsLocalization.mk' (TotalQuotient R) r ⟨m, hM m.2⟩) =
      algebraMap S (TotalQuotient S) (IsLocalization.mk' S r m) := by
  rw [AlgEquiv.symm_apply_eq, localizationEquiv_algebraMap_mk']

/-- If a semiring map out of `R` sends every regular element of `R` to a unit, then its extension
to a localization `S` at `M ≤ regulars R` sends every regular element of `S` to a unit. -/
theorem isUnit_lift_of_mem_regulars {P : Type*} [CommSemiring P] (hM : M ≤ regulars R)
    {g : R →+* P} (hg : ∀ r : regulars R, IsUnit (g r)) (s : regulars S) :
    IsUnit (IsLocalization.lift (M := M) (S := S) (fun m ↦ hg ⟨m, hM m.2⟩) s) := by
  obtain ⟨⟨r, m⟩, h⟩ := IsLocalization.mk'_surjective M (s : S)
  have hr : r ∈ regulars R := mem_regulars.mpr <|
    (IsLocalization.isRegular_mk' (S := S) (fun _ hm ↦ mem_regulars.mp (hM hm))).mp
      (mem_regulars.mp (h ▸ s.2))
  have hmul : IsLocalization.lift (M := M) (S := S) (fun m ↦ hg ⟨m, hM m.2⟩) s * g m = g r := by
    rw [← h, ← IsLocalization.lift_eq (M := M) (S := S) (fun m ↦ hg ⟨m, hM m.2⟩) (m : R),
      ← map_mul, IsLocalization.mk'_spec, IsLocalization.lift_eq]
  exact (IsUnit.mul_iff.mp (hmul.symm ▸ hg ⟨r, hr⟩)).1

/-- The isomorphism `localizationEquiv` intertwines universal lifts out of `TotalQuotient R` and
`TotalQuotient S`. -/
theorem lift_localizationEquiv {P : Type*} [CommSemiring P] (hM : M ≤ regulars R)
    {f : S →+* P} (hf : ∀ s : regulars S, IsUnit (f s)) (x : TotalQuotient S) :
    IsLocalization.lift (M := regulars R) (S := TotalQuotient R) (g := f.comp (algebraMap R S))
      (fun r ↦ hf ⟨algebraMap R S r, Submonoid.mem_comap.mp ((comap_regulars_eq M S hM).ge r.2)⟩)
      (localizationEquiv M S hM x) =
      IsLocalization.lift (M := regulars S) (S := TotalQuotient S) hf x := by
  have := isLocalization_of_isLocalization M S (TotalQuotient S) hM
  have h : (IsLocalization.lift (M := regulars R) (S := TotalQuotient R)
        (g := f.comp (algebraMap R S))
        (fun r ↦ hf ⟨algebraMap R S r,
          Submonoid.mem_comap.mp ((comap_regulars_eq M S hM).ge r.2)⟩)).comp
      (localizationEquiv M S hM).toRingHom =
      IsLocalization.lift (M := regulars S) (S := TotalQuotient S) hf := by
    refine IsLocalization.ringHom_ext (regulars R) ?_
    ext r
    simp [IsScalarTower.algebraMap_apply R S (TotalQuotient S)]
  exact DFunLike.congr_fun h x

/-- Starting from a map `g : R →+* P` inverting `regulars R`, extending to `TotalQuotient R`
agrees along `localizationEquiv` with extending first to `S` and then to `TotalQuotient S`. -/
theorem lift_localizationEquiv_of_base {P : Type*} [CommSemiring P] (hM : M ≤ regulars R)
    {g : R →+* P} (hg : ∀ r : regulars R, IsUnit (g r)) (x : TotalQuotient S) :
    IsLocalization.lift (M := regulars R) (S := TotalQuotient R) hg (localizationEquiv M S hM x) =
      IsLocalization.lift (M := regulars S) (S := TotalQuotient S)
        (isUnit_lift_of_mem_regulars M S hM hg) x := by
  have hcomp : (IsLocalization.lift (M := M) (S := S) (fun m ↦ hg ⟨m, hM m.2⟩)).comp
      (algebraMap R S) = g := by
    ext r
    simp
  rw [← lift_localizationEquiv M S hM (isUnit_lift_of_mem_regulars M S hM hg) x]
  congr 1
  exact IsLocalization.ringHom_ext (regulars R) <| by ext r; simp [hcomp]

end Localization

section Away

/-- Inverting a single regular element does not change the total quotient. -/
def awayEquiv {e : R} (he : IsRegular e) :
    TotalQuotient (Localization.Away e) ≃ₐ[R] TotalQuotient R :=
  localizationEquiv (.powers e) (Localization.Away e)
    (Submonoid.powers_le.mpr (mem_regulars.mpr he))

@[simp]
theorem awayEquiv_algebraMap {e : R} (he : IsRegular e) (r : R) :
    awayEquiv he (algebraMap (Localization.Away e) _ (algebraMap R (Localization.Away e) r)) =
      algebraMap R (TotalQuotient R) r :=
  localizationEquiv_algebraMap (.powers e) (Localization.Away e)
    (Submonoid.powers_le.mpr (mem_regulars.mpr he)) r

theorem awayEquiv_symm_algebraMap {e : R} (he : IsRegular e) (r : R) :
    (awayEquiv he).symm (algebraMap R (TotalQuotient R) r) =
      algebraMap (Localization.Away e) _ (algebraMap R (Localization.Away e) r) :=
  localizationEquiv_symm_algebraMap (.powers e) (Localization.Away e)
    (Submonoid.powers_le.mpr (mem_regulars.mpr he)) r

/-- The isomorphism `awayEquiv` commutes with universal evaluation out of the total quotient. -/
theorem lift_awayEquiv {P : Type*} [CommSemiring P] {e : R} (he : IsRegular e)
    {g : R →+* P} (hg : ∀ r : regulars R, IsUnit (g r))
    (x : TotalQuotient (Localization.Away e)) :
    IsLocalization.lift (M := regulars R) (S := TotalQuotient R) hg (awayEquiv he x) =
      IsLocalization.lift (M := regulars (Localization.Away e))
        (S := TotalQuotient (Localization.Away e))
        (isUnit_lift_of_mem_regulars (.powers e) (Localization.Away e)
          (Submonoid.powers_le.mpr (mem_regulars.mpr he)) hg) x :=
  lift_localizationEquiv_of_base (.powers e) (Localization.Away e)
    (Submonoid.powers_le.mpr (mem_regulars.mpr he)) hg x

end Away

end TotalQuotient

end TauCeti
