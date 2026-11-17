/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Basic

import Mathlib.Algebra.CharP.Subring
import Mathlib.RingTheory.WittVector.Complete
import TauCeti.RingTheory.Huber.Pair.Complete
import TauCeti.RingTheory.WittVector.Primitive.Quotient

/-!
# Sharp map, functoriality, and quotients of the untilt

This file develops the basic maps associated with the untilt `TauCeti.Perfectoid.untilt p P J` of
a Huber pair `P = (R, R⁺)` along an ideal `J` of `𝕎 R⁺`:

* **The multiplicative sharp map** `TauCeti.Perfectoid.untilt.sharp p P J : R →*₀ untilt p P J`
  for a Tate ring `R` and an arbitrary ideal `J`, sending `a ∈ R⁺` to the image of `[a]` and
  extended to `R = R⁺[1/ϖ]` by inverting a pseudouniformiser. It is independent of `ϖ`, carries
  `R⁺` into `untiltPlus p P J`, and carries pseudouniformisers of `R` to pseudouniformisers of
  the untilt.
* **Functoriality** `TauCeti.Perfectoid.untilt.map`: every morphism `f : P → Q` of Huber pairs
  with `W(f)(J) ⊆ J'` induces a ring homomorphism `untilt p P J →+* untilt p Q J'`, which is
  functorial in `f`, intertwines the sharp maps, and is continuous whenever `R` and `S` are Tate
  rings (with no primitivity or characteristic-`p` assumption).
* **Reduction modulo `[ϖ]`** `TauCeti.Perfectoid.untilt.quotEquiv`: when `R` is a perfect Tate
  ring of characteristic `p`, `ξ ∈ 𝕎 R⁺` is primitive, and `ϖ ∈ R⁺` divides `ξ.coeff 0`, we have
  `untiltPlus p P (span {ξ}) ⧸ (sharp ϖ) ≃+* R⁺ ⧸ (ϖ)`.
* **Recovery in characteristic `p`** `TauCeti.Perfectoid.untilt.equivOfSpanP`: when `R` is a
  perfect Tate ring of characteristic `p`, `untilt p P (span {p}) ≃+* R`, identifying `untiltPlus`
  with `R⁺` and `sharp` with the inverse; it is a homeomorphism whenever `R` is uniform.

## Main definitions

* `TauCeti.Perfectoid.untilt.sharp`: the multiplicative map `R →*₀ untilt p P J`.
* `TauCeti.Perfectoid.untilt.map`: functoriality of the untilt in Huber pair morphisms.
* `TauCeti.Perfectoid.untilt.quotientEquivUntiltPlus`: `𝕎 R⁺ ⧸ (ξ) ≃+* untiltPlus p P (span {ξ})`
  for primitive `ξ`.
* `TauCeti.Perfectoid.untilt.quotEquiv`: `untiltPlus ⧸ (sharp ϖ) ≃+* R⁺ ⧸ (ϖ)` when `ϖ ∣ ξ.coeff 0`.
* `TauCeti.Perfectoid.untilt.equivOfSpanP`: `untilt p P (span {p}) ≃+* R`.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Theorem 3.17.
* P. Scholze and J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Theorem 6.2.11.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Theorem 2.3.9.
-/

public section

open Filter Topology TauCeti.Huber WittVector
open scoped Pointwise

namespace TauCeti.Perfectoid.untilt

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

local notation "𝕎" => WittVector p

section Algebra

variable [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]
  {P : Pair R} {J : Ideal (WittVector p P.plus)}

/-- The untilt over a zero base is the zero ring. -/
theorem subsingleton_of_subsingleton [Subsingleton R] : Subsingleton (untilt p P J) := by
  refine (IsLocalization.toLocalizationMap ((untiltDenominators p P).map (Ideal.Quotient.mk J))
    (untilt p P J)).subsingleton ?_
  refine ⟨teichmuller p (0 : P.plus), mem_untiltDenominators.mpr ⟨0, isUnit_of_subsingleton _, rfl⟩,
    ?_⟩
  rw [teichmuller_zero, map_zero]

end Algebra

section Sharp

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R]

/-- The image `A⁺` of `𝕎 R⁺ ⧸ J` lies in the power-bounded subring of the untilt. -/
theorem untiltPlus_le_powerBoundedSubring {P : Pair R} {J : Ideal (WittVector p P.plus)} :
    untiltPlus p P J ≤ powerBoundedSubring (untilt p P J) := fun _ hx ↦
  mem_powerBoundedSubring.mpr (isBounded_untiltPlus.isPowerBounded_of_mem hx)

variable (p) (P : Pair R) (J : Ideal (WittVector p P.plus)) in
/-- **The multiplicative sharp map `♯_J : R →*₀ untilt p P J`**, sending `a ∈ R⁺` to the image of
`[a]` and extended to `R = R⁺[1/ϖ]` by inverting a pseudouniformiser. It is independent of the
choice of `ϖ` (`sharp_unique`). -/
noncomputable def sharp : R →*₀ untilt p P J :=
  let ϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose
  let hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  letI := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  letI := isLocalizationAway (J := J) hϖ
  let g : P.plus →*₀ untilt p P J :=
    { toFun a := algebraMap (𝕎 P.plus ⧸ J) (untilt p P J) (Ideal.Quotient.mk J (teichmuller p a))
      map_zero' := by simp
      map_one' := by simp
      map_mul' a b := by simp [map_mul] }
  (IsLocalization.toLocalizationMap (Submonoid.powers ϖ) R).lift₀ g fun ⟨y, n, hn⟩ ↦ by
    subst hn
    dsimp only
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := untilt p P J) (Ideal.Quotient.mk J (teichmuller p ϖ))).pow n

variable {P : Pair R} {J : Ideal (WittVector p P.plus)}

/-- On `R⁺`, `sharp` sends `a` to the image of its Teichmüller representative `[a]`. -/
@[simp]
theorem sharp_coe (a : P.plus) :
    sharp p P J (a : R) =
      algebraMap (𝕎 P.plus ⧸ J) (untilt p P J) (Ideal.Quotient.mk J (teichmuller p a)) := by
  unfold sharp
  dsimp only
  rw [Submonoid.LocalizationMap.lift₀_def]
  exact Submonoid.LocalizationMap.lift_eq _ _ a

/-- **Uniqueness of `sharp`**: any monoid homomorphism `R →* untilt p P J` agreeing with
`a ↦ [a]` on `R⁺` equals `sharp`. In particular, `sharp` does not depend on the choice of a
pseudouniformiser. -/
theorem sharp_unique (φ : R →* untilt p P J)
    (hφ : ∀ a : P.plus,
      φ (a : R) = algebraMap (𝕎 P.plus ⧸ J) (untilt p P J) (Ideal.Quotient.mk J (teichmuller p a)))
    (x : R) : φ x = sharp p P J x := by
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  have := isLocalizationAway (J := J) hϖ
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ϖ x
  have hu : IsUnit (sharp p P J (ϖ : R) ^ n) := by
    rw [sharp_coe]
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := untilt p P J) (Ideal.Quotient.mk J (teichmuller p ϖ))).pow n
  apply hu.mul_right_cancel
  calc φ x * sharp p P J (ϖ : R) ^ n
    _ = φ x * φ ((ϖ : R) ^ n) := by rw [map_pow, hφ, sharp_coe]
    _ = φ (x * (ϖ : R) ^ n) := (map_mul φ _ _).symm
    _ = φ (a : R) := by rw [show x * (ϖ : R) ^ n = (a : R) from ha]
    _ = sharp p P J (a : R) := by rw [hφ, sharp_coe]
    _ = sharp p P J (x * (ϖ : R) ^ n) := by rw [show (a : R) = x * (ϖ : R) ^ n from ha.symm]
    _ = sharp p P J x * sharp p P J (ϖ : R) ^ n := by rw [map_mul, map_pow]

/-- `sharp` sends elements of `R⁺` into `untiltPlus`. -/
theorem sharp_mem_untiltPlus {a : R} (ha : a ∈ P.plus) :
    sharp p P J a ∈ untiltPlus p P J := by
  rw [show a = ((⟨a, ha⟩ : P.plus) : R) from rfl, sharp_coe]
  exact mem_untiltPlus.mpr ⟨_, rfl⟩

/-- `sharp` carries pseudouniformisers of `R` to pseudouniformisers of the untilt. -/
theorem isPseudoUniformizer_sharp {ϖ : R} (hϖ : IsPseudoUniformizer ϖ) :
    IsPseudoUniformizer (sharp p P J ϖ) := by
  have hmem : ϖ ∈ P.plus :=
    P.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent
  rw [show ϖ = ((⟨ϖ, hmem⟩ : P.plus) : R) from rfl, sharp_coe]
  exact isPseudoUniformizer_algebraMap (ϖ := ⟨ϖ, hmem⟩) hϖ

/-- `sharp` is continuous at zero for any Tate ring `R` and any ideal `J ≤ 𝕎 R⁺`. -/
theorem tendsto_sharp_zero : Tendsto (sharp p P J) (𝓝 (0 : R)) (𝓝 (0 : untilt p P J)) := by
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  refine (hasBasis_nhds_zero (J := J) hϖ).tendsto_right_iff.mpr fun n _ ↦ ?_
  -- `{y | ϖ⁻ⁿ * y ∈ R⁺}` is an open neighbourhood of `0` in `R` mapped into `[ϖ] ^ n A⁺`.
  obtain ⟨u, hu⟩ := hϖ.isUnit.pow n
  have hopen : IsOpen (((↑u⁻¹ : R) * ·) ⁻¹' (P.plus : Set R)) :=
    P.isRingOfIntegralElements.isOpen.preimage (continuous_const_mul (↑u⁻¹ : R))
  have hmem0 : (0 : R) ∈ ((↑u⁻¹ : R) * ·) ⁻¹' (P.plus : Set R) := by
    simp [P.plus.zero_mem]
  filter_upwards [hopen.mem_nhds hmem0] with y hy
  refine mem_awayNhd.mpr ⟨Ideal.Quotient.mk _ (teichmuller p ⟨(↑u⁻¹ : R) * y, hy⟩), ?_⟩
  have hy_eq : y = (ϖ : R) ^ n * ((⟨(↑u⁻¹ : R) * y, hy⟩ : P.plus) : R) := by
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  symm
  calc sharp p P J y
    _ = sharp p P J ((ϖ : R) ^ n * ((⟨(↑u⁻¹ : R) * y, hy⟩ : P.plus) : R)) := congrArg _ hy_eq
    _ = algebraMap _ _ (Ideal.Quotient.mk _ (teichmuller p ϖ) ^ n *
          Ideal.Quotient.mk _ (teichmuller p ⟨(↑u⁻¹ : R) * y, hy⟩)) := by
        rw [map_mul, map_pow, sharp_coe, sharp_coe, map_mul, map_pow]

end Sharp

section Map

variable [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]
  {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsHuberRing S]
  {P : Pair R} {Q : Pair S}
  {J : Ideal (WittVector p P.plus)} {J' : Ideal (WittVector p Q.plus)}

/-- **Functoriality of the untilt**: a Huber pair morphism `f : P → Q` with `W(f)(J) ⊆ J'`
induces a ring homomorphism `untilt p P J →+* untilt p Q J'`, for arbitrary ideals `J` and `J'`. -/
noncomputable def map (f : Pair.Hom P Q)
    (hJ : J.map (WittVector.map (f.toRingHom.restrict P.plus Q.plus f.map_mem_plus)) ≤ J') :
    untilt p P J →+* untilt p Q J' :=
  let f_plus : P.plus →+* Q.plus := f.toRingHom.restrict P.plus Q.plus f.map_mem_plus
  let q : 𝕎 P.plus ⧸ J →+* 𝕎 Q.plus ⧸ J' :=
    Ideal.quotientMap J' (WittVector.map f_plus) (Ideal.map_le_iff_le_comap.mp hJ)
  IsLocalization.lift (M := (untiltDenominators p P).map (Ideal.Quotient.mk J))
    (g := (algebraMap (𝕎 Q.plus ⧸ J') (untilt p Q J')).comp q) fun ⟨y, x, hx, hy⟩ ↦ by
      subst hy
      obtain ⟨a, ha, rfl⟩ := mem_untiltDenominators.mp hx
      have hmem : Ideal.Quotient.mk J' (teichmuller p (f_plus a)) ∈
          (untiltDenominators p Q).map (Ideal.Quotient.mk J') :=
        Submonoid.mem_map_of_mem _
          (mem_untiltDenominators.mpr ⟨f_plus a, by simpa [f_plus] using ha.map f.toRingHom, rfl⟩)
      simpa only [q, RingHom.comp_apply, Ideal.quotientMap_mk, WittVector.map_teichmuller] using
        IsLocalization.map_units (untilt p Q J') ⟨_, hmem⟩

/-- `untilt.map` acts on `𝕎 R⁺ ⧸ J` via `WittVector.map`. -/
@[simp]
theorem map_algebraMap (f : Pair.Hom P Q)
    (hJ : J.map (WittVector.map (f.toRingHom.restrict P.plus Q.plus f.map_mem_plus)) ≤ J')
    (x : 𝕎 P.plus) :
    map f hJ (algebraMap (𝕎 P.plus ⧸ J) (untilt p P J) (Ideal.Quotient.mk J x)) =
      algebraMap (𝕎 Q.plus ⧸ J') (untilt p Q J')
        (Ideal.Quotient.mk J'
          (WittVector.map (f.toRingHom.restrict P.plus Q.plus f.map_mem_plus) x)) := by
  simp [map]

/-- `untilt.map` sends `untiltPlus p P J` into `untiltPlus p Q J'`. -/
theorem map_mem_untiltPlus (f : Pair.Hom P Q)
    (hJ : J.map (WittVector.map (f.toRingHom.restrict P.plus Q.plus f.map_mem_plus)) ≤ J')
    {x : untilt p P J} (hx : x ∈ untiltPlus p P J) :
    map f hJ x ∈ untiltPlus p Q J' := by
  obtain ⟨y, rfl⟩ := mem_untiltPlus.mp hx
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [map_algebraMap]
  exact mem_untiltPlus.mpr ⟨_, rfl⟩

/-- `untilt.map` preserves the identity morphism. -/
@[simp]
theorem map_id
    (hJ : J.map (WittVector.map ((Pair.Hom.id P).toRingHom.restrict P.plus P.plus
      (Pair.Hom.id P).map_mem_plus)) ≤ J) :
    map (Pair.Hom.id P) hJ = RingHom.id (untilt p P J) := by
  apply IsLocalization.ringHom_ext ((untiltDenominators p P).map (Ideal.Quotient.mk J))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, map_algebraMap]
  congr 2
  ext n
  simp [WittVector.map_coeff]

/-- `untilt.map` preserves composition of Huber pair morphisms. -/
theorem map_comp {T : Type*} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [IsHuberRing T] {U : Pair T} {J'' : Ideal (WittVector p U.plus)}
    (g : Pair.Hom Q U) (f : Pair.Hom P Q)
    (hJ : J.map (WittVector.map (f.toRingHom.restrict P.plus Q.plus f.map_mem_plus)) ≤ J')
    (hJ' : J'.map (WittVector.map (g.toRingHom.restrict Q.plus U.plus g.map_mem_plus)) ≤ J'')
    (hJ'' : J.map (WittVector.map ((g.comp f).toRingHom.restrict P.plus U.plus
      (g.comp f).map_mem_plus)) ≤ J'') :
    map (g.comp f) hJ'' = (map g hJ').comp (map f hJ) := by
  apply IsLocalization.ringHom_ext ((untiltDenominators p P).map (Ideal.Quotient.mk J))
  ext w
  simp only [RingHom.comp_apply, map_algebraMap]
  congr 2
  ext n
  simp [WittVector.map_coeff]

end Map

section MapTate

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R]
  {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsTateRing S]
  {P : Pair R} {Q : Pair S}
  {J : Ideal (WittVector p P.plus)} {J' : Ideal (WittVector p Q.plus)}

/-- `untilt.map` intertwines the sharp maps. -/
@[simp]
theorem map_sharp (f : Pair.Hom P Q)
    (hJ : J.map (WittVector.map (f.toRingHom.restrict P.plus Q.plus f.map_mem_plus)) ≤ J')
    (x : R) :
    map f hJ (sharp p P J x) = sharp p Q J' (f.toRingHom x) := by
  have hplus (a : P.plus) :
      map f hJ (sharp p P J (a : R)) = sharp p Q J' (f.toRingHom (a : R)) := by
    let f_plus : P.plus →+* Q.plus := f.toRingHom.restrict P.plus Q.plus f.map_mem_plus
    rw [sharp_coe, map_algebraMap, WittVector.map_teichmuller,
      show f.toRingHom (a : R) = ((f_plus a : Q.plus) : S) from rfl, sharp_coe]
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ϖ x
  have hu : IsUnit (sharp p Q J' (f.toRingHom (ϖ : R)) ^ n) :=
    (isPseudoUniformizer_sharp (hϖ.map f.continuous_toRingHom)).isUnit.pow n
  apply hu.mul_right_cancel
  calc map f hJ (sharp p P J x) * sharp p Q J' (f.toRingHom (ϖ : R)) ^ n
    _ = map f hJ (sharp p P J x) * map f hJ (sharp p P J (ϖ : R) ^ n) := by
        rw [map_pow, hplus ϖ]
    _ = map f hJ (sharp p P J (x * (ϖ : R) ^ n)) := by rw [← map_mul, ← map_pow, ← map_mul]
    _ = map f hJ (sharp p P J (a : R)) := by rw [show x * (ϖ : R) ^ n = (a : R) from ha]
    _ = sharp p Q J' (f.toRingHom (a : R)) := hplus a
    _ = sharp p Q J' (f.toRingHom (x * (ϖ : R) ^ n)) := by
        rw [show (a : R) = x * (ϖ : R) ^ n from ha.symm]
    _ = sharp p Q J' (f.toRingHom x) * sharp p Q J' (f.toRingHom (ϖ : R)) ^ n := by
        rw [map_mul, map_pow, map_mul, map_pow]

/-- **Continuity of `untilt.map`**: for Tate rings `R` and `S` and arbitrary ideals `J, J'` with
`W(f)(J) ⊆ J'`, the induced map `untilt p P J →+* untilt p Q J'` is continuous. -/
@[fun_prop, continuity]
theorem continuous_map (f : Pair.Hom P Q)
    (hJ : J.map (WittVector.map (f.toRingHom.restrict P.plus Q.plus f.map_mem_plus)) ≤ J') :
    Continuous (map f hJ) := by
  refine continuous_of_continuousAt_zero (map f hJ).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  let f_plus : P.plus →+* Q.plus := f.toRingHom.restrict P.plus Q.plus f.map_mem_plus
  have hϖ' : IsPseudoUniformizer (f_plus ϖ : S) := hϖ.map f.continuous_toRingHom
  refine (hasBasis_nhds_zero (J := J) hϖ).tendsto_iff
    (hasBasis_nhds_zero (J := J') hϖ') |>.mpr fun n _ ↦ ⟨n, trivial, fun x hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := mem_awayNhd.mp hx
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine mem_awayNhd.mpr ⟨Ideal.Quotient.mk J' (WittVector.map f_plus w), ?_⟩
  have hval : (map f hJ).toAddMonoidHom (algebraMap _ _
      (Ideal.Quotient.mk J (teichmuller p ϖ) ^ n * Ideal.Quotient.mk J w)) =
      map f hJ (algebraMap _ _
        (Ideal.Quotient.mk J (teichmuller p ϖ) ^ n * Ideal.Quotient.mk J w)) := rfl
  symm
  rw [hval, ← map_pow, ← map_mul, map_algebraMap, map_mul, map_pow, WittVector.map_teichmuller,
    map_mul, map_pow]

end MapTate

section PrimitiveQuotient

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R] [CharP R p] [PerfectRing R p]
  {P : Pair R} {ξ : WittVector p P.plus}

/-- For a primitive element `ξ`, `𝕎 R⁺ ⧸ (ξ)` is canonically isomorphic to the subring
`untiltPlus p P (span {ξ})` of the untilt. -/
noncomputable def quotientEquivUntiltPlus (hξ : ξ.IsPrimitive) :
    𝕎 P.plus ⧸ Ideal.span {ξ} ≃+* untiltPlus p P (Ideal.span {ξ}) :=
  RingEquiv.ofBijective
    ((algebraMap (𝕎 P.plus ⧸ Ideal.span {ξ}) (untilt p P (Ideal.span {ξ}))).codRestrict
      (untiltPlus p P (Ideal.span {ξ})) fun x ↦ mem_untiltPlus.mpr ⟨x, rfl⟩)
    ⟨fun _ _ h ↦ algebraMap_injective hξ (congrArg Subtype.val h), fun ⟨_, hx⟩ ↦ by
      obtain ⟨a, rfl⟩ := mem_untiltPlus.mp hx
      exact ⟨a, rfl⟩⟩

/-- `quotientEquivUntiltPlus` acts as `algebraMap`. -/
@[simp]
theorem coe_quotientEquivUntiltPlus (hξ : ξ.IsPrimitive) (x : 𝕎 P.plus ⧸ Ideal.span {ξ}) :
    (quotientEquivUntiltPlus hξ x : untilt p P (Ideal.span {ξ})) =
      algebraMap (𝕎 P.plus ⧸ Ideal.span {ξ}) (untilt p P (Ideal.span {ξ})) x := by
  rfl

/-- The inverse of `quotientEquivUntiltPlus` recovers the preimage in `𝕎 R⁺ ⧸ (ξ)`. -/
@[simp]
theorem quotientEquivUntiltPlus_symm_algebraMap (hξ : ξ.IsPrimitive)
    (x : 𝕎 P.plus ⧸ Ideal.span {ξ}) :
    (quotientEquivUntiltPlus hξ).symm
      ⟨algebraMap (𝕎 P.plus ⧸ Ideal.span {ξ}) (untilt p P (Ideal.span {ξ})) x,
        mem_untiltPlus.mpr ⟨x, rfl⟩⟩ = x :=
  (quotientEquivUntiltPlus hξ).symm_apply_apply x

/-- **Reduction of `untiltPlus` modulo `sharp ϖ`**: when `ξ` is primitive and `ϖ ∈ R⁺` divides
`ξ.coeff 0`, we have `untiltPlus p P (span {ξ}) ⧸ (sharp ϖ) ≃+* R⁺ ⧸ (ϖ)`. -/
noncomputable def quotEquiv (hξ : ξ.IsPrimitive) {ϖ : P.plus} (hξ₀ : ϖ ∣ ξ.coeff 0) :
    untiltPlus p P (Ideal.span {ξ}) ⧸
        Ideal.span {(⟨sharp p P (Ideal.span {ξ}) (ϖ : R), sharp_mem_untiltPlus ϖ.2⟩ :
          untiltPlus p P (Ideal.span {ξ}))} ≃+*
      P.plus ⧸ Ideal.span {ϖ} :=
  (Ideal.quotientEquiv _ _ (quotientEquivUntiltPlus hξ).symm (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    apply (quotientEquivUntiltPlus hξ).injective
    apply Subtype.ext
    simp [sharp_coe])).trans (hξ.isDistinguished.quotientTeichmullerEquiv hξ₀)

/-- `quotEquiv` sends the class of the image of `w : 𝕎 R⁺` to the class of `w.coeff 0`. -/
@[simp]
theorem quotEquiv_mk_algebraMap (hξ : ξ.IsPrimitive) {ϖ : P.plus} (hξ₀ : ϖ ∣ ξ.coeff 0)
    (w : 𝕎 P.plus) :
    quotEquiv hξ hξ₀ (Ideal.Quotient.mk _
      ⟨algebraMap (𝕎 P.plus ⧸ Ideal.span {ξ}) (untilt p P (Ideal.span {ξ}))
        (Ideal.Quotient.mk _ w), mem_untiltPlus.mpr ⟨_, rfl⟩⟩) =
      Ideal.Quotient.mk (Ideal.span {ϖ}) (w.coeff 0) := by
  simp [quotEquiv]

/-- `quotEquiv` sends the class of `sharp a` (`a ∈ R⁺`) to the class of `a`. -/
theorem quotEquiv_mk_sharp (hξ : ξ.IsPrimitive) {ϖ : P.plus} (hξ₀ : ϖ ∣ ξ.coeff 0) (a : P.plus) :
    quotEquiv hξ hξ₀ (Ideal.Quotient.mk _
      ⟨sharp p P (Ideal.span {ξ}) (a : R), sharp_mem_untiltPlus a.2⟩) =
      Ideal.Quotient.mk (Ideal.span {ϖ}) a := by
  simp only [sharp_coe, quotEquiv_mk_algebraMap, teichmuller_coeff_zero]

/-- The inverse of `quotEquiv` sends the class of `a ∈ R⁺` to the class of `sharp a`. -/
@[simp]
theorem quotEquiv_symm_mk (hξ : ξ.IsPrimitive) {ϖ : P.plus} (hξ₀ : ϖ ∣ ξ.coeff 0) (a : P.plus) :
    (quotEquiv hξ hξ₀).symm (Ideal.Quotient.mk (Ideal.span {ϖ}) a) =
      Ideal.Quotient.mk _ ⟨sharp p P (Ideal.span {ξ}) (a : R), sharp_mem_untiltPlus a.2⟩ := by
  rw [RingEquiv.symm_apply_eq, quotEquiv_mk_sharp]

end PrimitiveQuotient

section SpanP

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R] [CharP R p] [PerfectRing R p]
  {P : Pair R}

variable (p P) in
/-- **Recovery in characteristic `p`**: for a perfect Tate ring `R` of characteristic `p`, the
untilt along `(p)` is canonically ring-isomorphic to `R`. -/
noncomputable def equivOfSpanP :
    untilt p P (Ideal.span {(p : 𝕎 P.plus)}) ≃+* R :=
  let ϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose
  let hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  letI := isLocalizationAway (J := Ideal.span {(p : 𝕎 P.plus)}) hϖ
  letI := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (Ideal.Quotient.mk (Ideal.span {(p : 𝕎 P.plus)}) (teichmuller p ϖ)))
    (T := Submonoid.powers ϖ)
    (untilt p P (Ideal.span {(p : 𝕎 P.plus)})) R
    (WittVector.quotientPEquiv (p := p) (k := P.plus)) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers
        ((WittVector.quotientPEquiv_mk (teichmuller p ϖ)).trans (teichmuller_coeff_zero p ϖ)))

/-- `equivOfSpanP` acts on `𝕎 R⁺ ⧸ (p)` by taking the zeroth Witt coordinate. -/
@[simp]
theorem equivOfSpanP_algebraMap (w : 𝕎 P.plus) :
    equivOfSpanP p P (algebraMap (𝕎 P.plus ⧸ Ideal.span {(p : 𝕎 P.plus)})
      (untilt p P (Ideal.span {(p : 𝕎 P.plus)})) (Ideal.Quotient.mk _ w)) =
      (w.coeff 0 : R) := by
  let ϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose
  have hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  have := isLocalizationAway (J := Ideal.span {(p : 𝕎 P.plus)}) hϖ
  have := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  unfold equivOfSpanP
  dsimp only
  rw [IsLocalization.ringEquivOfRingEquiv_eq]
  exact congrArg Subtype.val (WittVector.quotientPEquiv_mk w)

/-- `equivOfSpanP` is left inverse to `sharp` for `J = (p)`. -/
@[simp]
theorem equivOfSpanP_sharp (x : R) :
    equivOfSpanP p P (sharp p P (Ideal.span {(p : 𝕎 P.plus)}) x) = x := by
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ϖ x
  have hplus (b : P.plus) :
      equivOfSpanP p P (sharp p P (Ideal.span {(p : 𝕎 P.plus)}) (b : R)) = (b : R) := by
    rw [sharp_coe, equivOfSpanP_algebraMap, teichmuller_coeff_zero]
  apply (hϖ.isUnit.pow n).mul_right_cancel
  calc equivOfSpanP p P (sharp p P (Ideal.span {(p : 𝕎 P.plus)}) x) * (ϖ : R) ^ n
    _ = equivOfSpanP p P (sharp p P (Ideal.span {(p : 𝕎 P.plus)}) x) *
          equivOfSpanP p P (sharp p P (Ideal.span {(p : 𝕎 P.plus)}) (ϖ : R) ^ n) := by
        rw [map_pow, hplus ϖ]
    _ = equivOfSpanP p P (sharp p P (Ideal.span {(p : 𝕎 P.plus)}) (x * (ϖ : R) ^ n)) := by
        rw [← map_mul, ← map_pow, ← map_mul]
    _ = equivOfSpanP p P (sharp p P (Ideal.span {(p : 𝕎 P.plus)}) (a : R)) := by
        rw [show x * (ϖ : R) ^ n = (a : R) from ha]
    _ = (a : R) := hplus a
    _ = x * (ϖ : R) ^ n := ha.symm

/-- The inverse of `equivOfSpanP` is `sharp` for `J = (p)`. -/
@[simp]
theorem equivOfSpanP_symm_apply (x : R) :
    (equivOfSpanP p P).symm x = sharp p P (Ideal.span {(p : 𝕎 P.plus)}) x :=
  (equivOfSpanP p P).injective (by rw [RingEquiv.apply_symm_apply, equivOfSpanP_sharp])

/-- Under `equivOfSpanP`, `untiltPlus p P (span {p})` maps onto `R⁺`. -/
theorem map_untiltPlus_equivOfSpanP :
    (untiltPlus p P (Ideal.span {(p : 𝕎 P.plus)})).map (equivOfSpanP p P).toRingHom = P.plus := by
  ext x
  simp only [Subring.mem_map, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨y, rfl⟩ := mem_untiltPlus.mp hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [equivOfSpanP_algebraMap]
    exact (w.coeff 0).2
  · intro hx
    refine ⟨sharp p P (Ideal.span {(p : 𝕎 P.plus)}) x, sharp_mem_untiltPlus hx,
      equivOfSpanP_sharp x⟩

/-- The inverse `(equivOfSpanP p P).symm : R → untilt p P (span {p})` is always continuous. -/
@[fun_prop, continuity]
theorem continuous_equivOfSpanP_symm : Continuous (equivOfSpanP p P).symm := by
  refine continuous_of_continuousAt_zero (equivOfSpanP p P).symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  have hfun : ⇑(equivOfSpanP p P).symm.toAddMonoidHom =
      ⇑(sharp p P (Ideal.span {(p : 𝕎 P.plus)})) :=
    funext equivOfSpanP_symm_apply
  rw [hfun]
  exact tendsto_sharp_zero

/-- `equivOfSpanP p P` is continuous whenever `R⁺` is bounded. -/
theorem continuous_equivOfSpanP_of_isBounded (hP : IsBounded (P.plus : Set R)) :
    Continuous (equivOfSpanP p P) := by
  refine continuous_of_continuousAt_zero (equivOfSpanP p P).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  refine (hasBasis_nhds_zero (J := Ideal.span {(p : 𝕎 P.plus)}) hϖ).tendsto_left_iff.mpr
    fun U hU ↦ ?_
  obtain ⟨n, hn⟩ := hP.exists_pow_mul_subset hϖ.isTopologicallyNilpotent hU
  refine ⟨n, trivial, fun x hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := mem_awayNhd.mp hx
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine hn ?_
  have hmem : (ϖ : R) ^ n * (w.coeff 0 : R) ∈ {(ϖ : R) ^ n} * (P.plus : Set R) :=
    Set.mul_mem_mul (Set.mem_singleton _) (w.coeff 0).2
  have heq : (equivOfSpanP p P).toAddMonoidHom (algebraMap _ _
      (Ideal.Quotient.mk (Ideal.span {(p : 𝕎 P.plus)}) (teichmuller p ϖ) ^ n *
        Ideal.Quotient.mk _ w)) = (ϖ : R) ^ n * (w.coeff 0 : R) := by
    have hval : (equivOfSpanP p P).toAddMonoidHom (algebraMap _ _
        (Ideal.Quotient.mk (Ideal.span {(p : 𝕎 P.plus)}) (teichmuller p ϖ) ^ n *
          Ideal.Quotient.mk _ w)) =
        equivOfSpanP p P (algebraMap _ _
          (Ideal.Quotient.mk (Ideal.span {(p : 𝕎 P.plus)}) (teichmuller p ϖ) ^ n *
            Ideal.Quotient.mk _ w)) := rfl
    rw [hval, ← map_pow, ← map_mul, equivOfSpanP_algebraMap, ← constantCoeff_apply, map_mul,
      map_pow, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero, Subring.coe_mul,
      Subring.coe_pow]
  rwa [heq]

/-- `equivOfSpanP p P` is continuous when `R` is uniform. -/
@[fun_prop, continuity]
theorem continuous_equivOfSpanP [IsUniform R] : Continuous (equivOfSpanP p P) :=
  continuous_equivOfSpanP_of_isBounded P.isRingOfIntegralElements.isBounded

/-- **Topological recovery in characteristic `p`**: for a uniform perfect Tate ring `R` of
characteristic `p`, `equivOfSpanP p P : untilt p P (span {p}) ≃+* R` is a homeomorphism. -/
theorem isHomeomorph_equivOfSpanP [IsUniform R] : IsHomeomorph (equivOfSpanP p P) :=
  (Homeomorph.mk (equivOfSpanP p P).toEquiv continuous_equivOfSpanP
    continuous_equivOfSpanP_symm).isHomeomorph

end SpanP

end TauCeti.Perfectoid.untilt
