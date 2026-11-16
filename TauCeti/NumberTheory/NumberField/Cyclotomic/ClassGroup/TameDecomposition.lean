/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.NumberField.Cyclotomic.ClassGroup.Action
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent
public import TauCeti.RingTheory.Henselian.Teichmuller
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.UnitsDecomposition.Basic

/-!
# Tame `(p - 1)`-st root-of-unity characters and cyclotomic class-module eigenspaces

For a prime `p` and an integer `r ≥ 1`, reduction modulo `p` (`ZMod.unitsMap`) restricts to a
multiplicative equivalence

`tameRootsEquivUnitsZMod p r hr : rootsOfUnity (p - 1) (ZMod (p ^ r)) ≃* (ZMod p)ˣ`,

identifying the unique subgroup of `(ZMod (p ^ r))ˣ` of order `p - 1` with `(ZMod p)ˣ`. Meanwhile,
`padicTeichmuller p : (ZMod p)ˣ →* ℤ_[p]ˣ` is the unique multiplicative section of
`PadicInt.toZMod` (`eq_padicTeichmuller`).

Given any character `ω : (ZMod p)ˣ →* ℤ_[p]ˣ` and exponent `i : ℤ`,
`TauCeti.cyclotomicClassEigenspace` cuts out the submodule of
`ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))` on which
`rootsOfUnity (p - 1) (ZMod (p ^ r))` acts via `a ↦ ω(a mod p) ^ i`; no condition is imposed on the
wild `(1 + p)`-subgroup, which preserves every tame eigenspace. Because `p - 1` is a unit in
`ℤ_[p]`, each tame eigenspace is the image of the explicit character projector
`TauCeti.cyclotomicClassProjector`. When `ω` is a section of reduction modulo `p`, the powers
`ω ^ i` (`i : ZMod (p - 1)`) exhaust all `ℤ_[p]ˣ`-valued characters of
`rootsOfUnity (p - 1) (ZMod (p ^ r))`, yielding an internal direct-sum decomposition
`isInternal_cyclotomicClassEigenspace`.

## Main definitions

* `TauCeti.padicTeichmuller p`: the Teichmüller character `(ZMod p)ˣ →* ℤ_[p]ˣ`.
* `TauCeti.tameRootsEquivUnitsZMod p r hr`: the reduction isomorphism
  `rootsOfUnity (p - 1) (ZMod (p ^ r)) ≃* (ZMod p)ˣ`.
* `TauCeti.cyclotomicClassEigenspace p r hr ω i`: the tame `ω ^ i`-submodule of the `p`-primary
  class module at conductor `p ^ r`.
* `TauCeti.cyclotomicTameChar p r hr ω i`, `TauCeti.cyclotomicClassProjector p r hr ω i`: the
  tame character `a ↦ ω(a mod p) ^ i` and its idempotent projector.
* `TauCeti.cyclotomicClassTameEquiv p r hr ω hω`: the `ℤ_[p]`-linear direct-sum decomposition
  `⨁ i : ZMod (p - 1), cyclotomicClassEigenspace p r hr ω i.val ≃ₗ[ℤ_[p]] ...`.

## Main results

* `TauCeti.eq_padicTeichmuller`: `padicTeichmuller p` is the unique multiplicative section of
  `PadicInt.toZMod`.
* `TauCeti.range_cyclotomicClassProjector`: the image of `cyclotomicClassProjector` is
  `cyclotomicClassEigenspace`.
* `TauCeti.cyclotomicClassEigenspace_add_mul_sub_one`: `(p - 1)`-periodicity in `i : ℤ`.
* `TauCeti.isInternal_cyclotomicClassEigenspace`: internal direct-sum decomposition of the
  `p`-primary class module over `ZMod (p - 1)` when `ω` lifts reduction modulo `p`.
* `TauCeti.cyclotomicClassAction_neg_one_of_mem_eigenspace`: for `p ≠ 2`, `-1` acts as `(-1) ^ i`
  on `cyclotomicClassEigenspace p r hr ω i`.
* `TauCeti.classGroupExtendedLinearMap_mem_cyclotomicClassEigenspace`,
  `TauCeti.classGroupRelNormLinearMap_mem_cyclotomicClassEigenspace`,
  `TauCeti.classGroupExtendedLinearMap_cyclotomicClassProjector`,
  `TauCeti.classGroupRelNormLinearMap_cyclotomicClassProjector`: tower extension and relative
  norm commute with `cyclotomicClassProjector` and preserve each tame `ω ^ i`-eigenspace across
  levels `1 ≤ r ≤ s`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §§4.3, 6.3, 10.1.
* R. Sharifi, *Iwasawa Theory*, §§1.3, 2.1, 2.8.
* The prime-level (`r = 1`) character-idempotent decomposition of `p`-primary cyclotomic class
  groups was previously formalized in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), project
  `FltRegularBernoulli` (`BernoulliRegular.Idempotents`, `BernoulliRegular.ClassGroup`); here it is
  developed for prime-power conductors `p ^ r` (`r ≥ 1`) with wild-group stability and tower
  compatibility via `TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent`.
-/

public section

open NumberField TensorProduct MonoidAlgebra
open scoped DirectSum Pointwise

namespace TauCeti

attribute [local instance] instIsCyclotomicExtensionSingletonCyclotomicField

/-- For every prime `p`, `p - 1` is nonzero. -/
local instance instNeZeroPredPrime (p : ℕ) [Fact p.Prime] : NeZero (p - 1) :=
  ⟨Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt⟩

/-- Constructive decidability of membership in `rootsOfUnity` when equality of units is
decidable. -/
local instance instDecidablePredMemRootsOfUnity (n : ℕ) (M : Type*) [CommMonoid M]
    [DecidableEq Mˣ] : DecidablePred (· ∈ rootsOfUnity n M) :=
  fun u ↦ decidable_of_iff (u ^ n = 1) (mem_rootsOfUnity n u).symm

/-! ### Tame `(p - 1)`-st roots of unity in `ZMod (p ^ r)` and the Teichmüller character -/

section TameUnitsAndTeichmuller

variable (p : ℕ) [Fact p.Prime]

/-- For every prime `p`, `p` and `p - 1` are coprime. -/
theorem coprime_prime_sub_one : p.Coprime (p - 1) :=
  (Fact.out : p.Prime).coprime_iff_not_dvd.mpr <|
    Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.sub_lt (Fact.out : p.Prime).pos zero_lt_one)

/-- For every prime `p`, `p - 1` is a unit in `ℤ_[p]`. -/
theorem isUnit_prime_sub_one_padicInt : IsUnit ((p - 1 : ℕ) : ℤ_[p]) :=
  PadicInt.isUnit_natCast_of_coprime (coprime_prime_sub_one p)

/-- Every homomorphism `(ZMod p)ˣ →* G` takes values of order dividing `p - 1`. -/
theorem hom_units_zmod_pow_sub_one {G : Type*} [Group G] (ω : (ZMod p)ˣ →* G) (a : (ZMod p)ˣ) :
    ω a ^ (p - 1) = 1 := by
  rw [← map_pow, ← Nat.totient_prime (Fact.out : p.Prime), ZMod.pow_totient, map_one]

/-- The **Teichmüller character** `(ZMod p)ˣ →* ℤ_[p]ˣ`, transporting `TauCeti.teichmuller ℤ_[p]`
along `PadicInt.residueField : ResidueField ℤ_[p] ≃+* ZMod p`. -/
noncomputable def padicTeichmuller : (ZMod p)ˣ →* ℤ_[p]ˣ :=
  (teichmuller ℤ_[p]).comp (Units.mapEquiv PadicInt.residueField.symm.toMulEquiv).toMonoidHom

/-- `padicTeichmuller p` is a section of reduction modulo `p`. -/
@[simp]
theorem toZMod_padicTeichmuller (a : (ZMod p)ˣ) :
    PadicInt.toZMod ((padicTeichmuller p a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p) := by
  change PadicInt.residueField (IsLocalRing.residue ℤ_[p]
    (teichmuller ℤ_[p] ((Units.mapEquiv PadicInt.residueField.symm.toMulEquiv) a) : ℤ_[p])) = _
  rw [residue_teichmuller]
  simp

theorem padicTeichmuller_pow_sub_one (a : (ZMod p)ˣ) : padicTeichmuller p a ^ (p - 1) = 1 :=
  hom_units_zmod_pow_sub_one p (padicTeichmuller p) a

/-- **Uniqueness of the `p`-adic Teichmüller character**: any multiplicative homomorphism
`ω : (ZMod p)ˣ →* ℤ_[p]ˣ` reducing to the identity modulo `p` equals `padicTeichmuller p`. -/
theorem eq_padicTeichmuller {ω : (ZMod p)ˣ →* ℤ_[p]ˣ}
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    ω = padicTeichmuller p := by
  have hsec : ω.comp (Units.mapEquiv PadicInt.residueField.toMulEquiv).toMonoidHom =
      teichmuller ℤ_[p] := by
    refine eq_teichmuller ℤ_[p] _ fun x ↦ PadicInt.residueField.injective ?_
    change PadicInt.toZMod ((ω ((Units.mapEquiv PadicInt.residueField.toMulEquiv) x) :
      ℤ_[p]ˣ) : ℤ_[p]) = PadicInt.residueField (x : IsLocalRing.ResidueField ℤ_[p])
    rw [hω]
    rfl
  refine MonoidHom.ext fun a ↦ ?_
  have h : ω ((Units.mapEquiv PadicInt.residueField.toMulEquiv)
      ((Units.mapEquiv PadicInt.residueField.symm.toMulEquiv) a)) = padicTeichmuller p a :=
    DFunLike.congr_fun hsec ((Units.mapEquiv PadicInt.residueField.symm.toMulEquiv) a)
  have hinv : (Units.mapEquiv PadicInt.residueField.toMulEquiv)
      ((Units.mapEquiv PadicInt.residueField.symm.toMulEquiv) a) = a :=
    Units.ext (PadicInt.residueField.apply_symm_apply a.val)
  rwa [hinv] at h

/-- For an odd prime `p`, any multiplicative section `ω : (ZMod p)ˣ →* ℤ_[p]ˣ` of reduction modulo
`p` sends `-1` to `-1`. -/
theorem apply_neg_one_of_toZMod_eq {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} (hp : p ≠ 2)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    ω (-1) = -1 := by
  have hneg : (Units.mapEquiv PadicInt.residueField.symm.toMulEquiv) (-1 : (ZMod p)ˣ) = -1 := by
    ext
    simp
  rw [eq_padicTeichmuller p hω, padicTeichmuller, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    hneg]
  refine teichmuller_neg_one ℤ_[p] ?_
  rw [PadicInt.card_residueField]
  exact (Fact.out : p.Prime).odd_of_ne_two hp

/-- Reduction modulo `p` identifies the `(p - 1)`-st roots of unity in `ZMod (p ^ r)` (`r ≥ 1`)
with `(ZMod p)ˣ`. -/
noncomputable def tameRootsEquivUnitsZMod (r : ℕ) (hr : 1 ≤ r) :
    rootsOfUnity (p - 1) (ZMod (p ^ r)) ≃* (ZMod p)ˣ := by
  have hr0 : r ≠ 0 := by omega
  have hdiv : p ∣ p ^ r := dvd_pow_self p hr0
  let f : rootsOfUnity (p - 1) (ZMod (p ^ r)) →* (ZMod p)ˣ :=
    (ZMod.unitsMap hdiv).comp (rootsOfUnity (p - 1) (ZMod (p ^ r))).subtype
  refine MulEquiv.ofBijective f ⟨(injective_iff_map_eq_one f).mpr fun ζ hζ ↦ ?_, fun a ↦ ?_⟩
  · set u : ZMod (p ^ r) := (ζ.1 : ZMod (p ^ r))
    have hu_mod : ZMod.castHom hdiv (ZMod p) u = 1 := by
      simpa [f, ZMod.unitsMap_def] using congrArg Units.val hζ
    have hu_pow : u ^ (p - 1) = 1 := (mem_rootsOfUnity' (p - 1) _).mp ζ.2
    let s : ZMod (p ^ r) := ∑ k ∈ Finset.range (p - 1), u ^ k
    have hgeom : s * (u - 1) = 0 := by simpa [s, hu_pow] using geom_sum_mul u (p - 1)
    have hs_mod : ZMod.castHom hdiv (ZMod p) s = (p - 1 : ℕ) := by
      simp [s, map_sum, map_pow, hu_mod]
    have hs_ne : ZMod.castHom hdiv (ZMod p) s ≠ 0 := by
      rw [hs_mod, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp (coprime_prime_sub_one p)
    have hp_ndvd : ¬ p ∣ s.val := by
      intro hd
      apply hs_ne
      conv_lhs => rw [← ZMod.natCast_zmod_val s, map_natCast]
      exact (ZMod.natCast_eq_zero_iff s.val p).mpr hd
    have hs_unit : IsUnit s := by
      rw [← ZMod.natCast_zmod_val s, ZMod.isUnit_iff_coprime]
      exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_ndvd).pow_left r).symm
    exact Subtype.ext (Units.ext (sub_eq_zero.mp (hs_unit.mul_right_eq_zero.mp hgeom)))
  · let u : (ZMod (p ^ r))ˣ := PadicInt.unitsToZModPow r (padicTeichmuller p a)
    have hu : u ∈ rootsOfUnity (p - 1) (ZMod (p ^ r)) := by
      rw [mem_rootsOfUnity, ← map_pow, padicTeichmuller_pow_sub_one, map_one]
    refine ⟨⟨u, hu⟩, Units.ext ?_⟩
    simp only [f, u, MonoidHom.comp_apply, Subgroup.coe_subtype, ZMod.unitsMap_val,
      PadicInt.coe_unitsToZModPow_apply, PadicInt.cast_toZModPow_eq_toZMod hr0,
      toZMod_padicTeichmuller]

@[simp]
theorem tameRootsEquivUnitsZMod_apply (r : ℕ) (hr : 1 ≤ r)
    (a : rootsOfUnity (p - 1) (ZMod (p ^ r))) :
    tameRootsEquivUnitsZMod p r hr a =
      ZMod.unitsMap (dvd_pow_self p (by omega : r ≠ 0)) a.val :=
  (rfl)

theorem card_tameRoots (r : ℕ) (hr : 1 ≤ r) :
    Nat.card (rootsOfUnity (p - 1) (ZMod (p ^ r))) = p - 1 := by
  rw [Nat.card_congr (tameRootsEquivUnitsZMod p r hr).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]

theorem isUnit_card_tameRoots (r : ℕ) (hr : 1 ≤ r) :
    IsUnit (Nat.card (rootsOfUnity (p - 1) (ZMod (p ^ r))) : ℤ_[p]) := by
  rw [card_tameRoots p r hr]
  exact isUnit_prime_sub_one_padicInt p

end TameUnitsAndTeichmuller

/-! ### Tame `ω ^ i`-eigenspaces, projectors, and direct-sum decomposition -/

section TameEigenspaces

/-- The tame `ω ^ i` submodule at conductor `p ^ r`. Only the `(p - 1)`-st roots of unity in the
residue-unit group act in this condition; the wild action is retained. -/
noncomputable def cyclotomicClassEigenspace (p r : ℕ) [Fact p.Prime]
    (hr : 1 ≤ r) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) :
    Submodule ℤ_[p]
      (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))) :=
  ⨅ a : rootsOfUnity (p - 1) (ZMod (p ^ r)),
    LinearMap.ker (cyclotomicClassAction ℤ_[p] (p ^ r) a.val -
      (((ω (ZMod.unitsMap (dvd_pow_self p (by omega : r ≠ 0)) a.val)) ^ i : ℤ_[p]ˣ) :
        ℤ_[p]) • LinearMap.id)

/-- The `ℤ_[p]ˣ`-valued character `a ↦ ω(a mod p) ^ i` of `rootsOfUnity (p - 1) (ZMod (p ^ r))`. -/
noncomputable def cyclotomicTameChar (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) :
    rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ where
  toFun a := (ω (ZMod.unitsMap (dvd_pow_self p (by omega : r ≠ 0)) a.val)) ^ i
  map_one' := by simp
  map_mul' a b := by simp [mul_zpow]

@[simp]
theorem cyclotomicTameChar_apply (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) (a : rootsOfUnity (p - 1) (ZMod (p ^ r))) :
    cyclotomicTameChar p r hr ω i a =
      (ω (ZMod.unitsMap (dvd_pow_self p (by omega : r ≠ 0)) a.val)) ^ i :=
  (rfl)

/-- Restriction of `cyclotomicClassRep ℤ_[p] (p ^ r)` to the tame `(p - 1)`-st roots-of-unity
subgroup of `(ZMod (p ^ r))ˣ`. -/
noncomputable def cyclotomicTameRep (p r : ℕ) [Fact p.Prime] :
    Representation ℤ_[p] (rootsOfUnity (p - 1) (ZMod (p ^ r)))
      (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))) :=
  (cyclotomicClassRep ℤ_[p] (p ^ r)).comp (rootsOfUnity (p - 1) (ZMod (p ^ r))).subtype

@[simp]
theorem cyclotomicTameRep_apply (p r : ℕ) [Fact p.Prime]
    (a : rootsOfUnity (p - 1) (ZMod (p ^ r))) :
    cyclotomicTameRep p r a = cyclotomicClassAction ℤ_[p] (p ^ r) a.val := by
  simp [cyclotomicTameRep]

/-- Membership criterion for `cyclotomicClassEigenspace`: every tame `(p - 1)`-st root of unity
`a` acts by the scalar `ω(a mod p) ^ i`. -/
theorem mem_cyclotomicClassEigenspace_iff {p r : ℕ} [Fact p.Prime] (hr : 1 ≤ r)
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {i : ℤ}
    {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))} :
    x ∈ cyclotomicClassEigenspace p r hr ω i ↔
      ∀ a : rootsOfUnity (p - 1) (ZMod (p ^ r)),
        cyclotomicClassAction ℤ_[p] (p ^ r) a.val x =
          ((cyclotomicTameChar p r hr ω i a : ℤ_[p]ˣ) : ℤ_[p]) • x := by
  simp [cyclotomicClassEigenspace, Submodule.mem_iInf, sub_eq_zero]

/-- `cyclotomicClassEigenspace` is the joint eigenspace of `cyclotomicTameRep` for
`cyclotomicTameChar`. -/
theorem cyclotomicClassEigenspace_eq_iInf_eigenspace (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) :
    cyclotomicClassEigenspace p r hr ω i =
      ⨅ a : rootsOfUnity (p - 1) (ZMod (p ^ r)),
        Module.End.eigenspace (cyclotomicTameRep p r a)
          ((cyclotomicTameChar p r hr ω i a : ℤ_[p]ˣ) : ℤ_[p]) := by
  ext x
  simp [mem_cyclotomicClassEigenspace_iff, Submodule.mem_iInf]

/-- **Wild action stability**: the full `(ZMod (p ^ r))ˣ` action (in particular the wild
`(1 + p)`-subgroup) preserves every tame eigenspace `cyclotomicClassEigenspace p r hr ω i`. -/
theorem cyclotomicClassAction_mem_cyclotomicClassEigenspace {p r : ℕ} [Fact p.Prime]
    (hr : 1 ≤ r) {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {i : ℤ} (b : (ZMod (p ^ r))ˣ)
    {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))}
    (hx : x ∈ cyclotomicClassEigenspace p r hr ω i) :
    cyclotomicClassAction ℤ_[p] (p ^ r) b x ∈ cyclotomicClassEigenspace p r hr ω i := by
  rw [mem_cyclotomicClassEigenspace_iff] at hx ⊢
  intro a
  rw [← cyclotomicClassAction_apply_mul, mul_comm, cyclotomicClassAction_apply_mul, hx a, map_smul]

/-- The **tame character projector** `e_{ω ^ i}` on the `p`-primary cyclotomic class module at
conductor `p ^ r`. -/
noncomputable def cyclotomicClassProjector (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) :
    Module.End ℤ_[p]
      (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))) :=
  (cyclotomicTameRep p r).asAlgebraHom (charIdempotent (cyclotomicTameChar p r hr ω i))

/-- Explicit averaging sum formula for `cyclotomicClassProjector`. -/
theorem cyclotomicClassProjector_eq_sum (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) :
    cyclotomicClassProjector p r hr ω i =
      Ring.inverse ((p - 1 : ℕ) : ℤ_[p]) •
        ∑ a : rootsOfUnity (p - 1) (ZMod (p ^ r)),
          (((cyclotomicTameChar p r hr ω i a)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) •
            cyclotomicClassAction ℤ_[p] (p ^ r) a.val := by
  rw [cyclotomicClassProjector, Representation.asAlgebraHom_charIdempotent, card_tameRoots p r hr]
  simp

theorem isIdempotentElem_cyclotomicClassProjector (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) :
    IsIdempotentElem (cyclotomicClassProjector p r hr ω i) := by
  rw [cyclotomicClassProjector]
  exact (isIdempotentElem_charIdempotent _).map _

/-- **The image of `cyclotomicClassProjector` is `cyclotomicClassEigenspace`.** -/
@[simp]
theorem range_cyclotomicClassProjector (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) :
    LinearMap.range (cyclotomicClassProjector p r hr ω i) =
      cyclotomicClassEigenspace p r hr ω i := by
  rw [cyclotomicClassProjector,
    Representation.range_asAlgebraHom_charIdempotent _ (isUnit_card_tameRoots p r hr),
    cyclotomicClassEigenspace_eq_iInf_eigenspace]

theorem cyclotomicClassProjector_apply_mem (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ)
    (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))) :
    cyclotomicClassProjector p r hr ω i x ∈ cyclotomicClassEigenspace p r hr ω i := by
  rw [← range_cyclotomicClassProjector]
  exact LinearMap.mem_range_self _ x

theorem cyclotomicClassProjector_apply_of_mem {p r : ℕ} [Fact p.Prime] (hr : 1 ≤ r)
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {i : ℤ}
    {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))}
    (hx : x ∈ cyclotomicClassEigenspace p r hr ω i) :
    cyclotomicClassProjector p r hr ω i x = x := by
  rw [← range_cyclotomicClassProjector] at hx
  obtain ⟨y, rfl⟩ := hx
  exact DFunLike.congr_fun (isIdempotentElem_cyclotomicClassProjector p r hr ω i).eq y

/-- Periodicity of `cyclotomicTameChar` modulo `p - 1`. -/
theorem cyclotomicTameChar_add_mul_sub_one (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i k : ℤ) :
    cyclotomicTameChar p r hr ω (i + k * (p - 1 : ℕ)) = cyclotomicTameChar p r hr ω i := by
  ext a
  rw [cyclotomicTameChar_apply, cyclotomicTameChar_apply, zpow_add, mul_comm k, zpow_mul,
    zpow_natCast, hom_units_zmod_pow_sub_one, one_zpow, mul_one]

/-- `cyclotomicTameChar` depends on `i : ℤ` only through its residue in `ZMod (p - 1)`. -/
theorem cyclotomicTameChar_eq_of_zmod_eq {p r : ℕ} [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {i j : ℤ} (hij : (i : ZMod (p - 1)) = (j : ZMod (p - 1))) :
    cyclotomicTameChar p r hr ω i = cyclotomicTameChar p r hr ω j := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub j i (p - 1)).mp hij.symm
  have hi : i = j + k * (p - 1 : ℕ) := by linear_combination hk
  rw [hi]
  exact cyclotomicTameChar_add_mul_sub_one p r hr ω j k

/-- **Periodicity of `cyclotomicClassEigenspace` modulo `p - 1`.** -/
theorem cyclotomicClassEigenspace_add_mul_sub_one (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i k : ℤ) :
    cyclotomicClassEigenspace p r hr ω (i + k * (p - 1 : ℕ)) =
      cyclotomicClassEigenspace p r hr ω i := by
  rw [cyclotomicClassEigenspace_eq_iInf_eigenspace, cyclotomicClassEigenspace_eq_iInf_eigenspace,
    cyclotomicTameChar_add_mul_sub_one]

theorem cyclotomicClassEigenspace_eq_of_zmod_eq {p r : ℕ} [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {i j : ℤ} (hij : (i : ZMod (p - 1)) = (j : ZMod (p - 1))) :
    cyclotomicClassEigenspace p r hr ω i = cyclotomicClassEigenspace p r hr ω j := by
  rw [cyclotomicClassEigenspace_eq_iInf_eigenspace, cyclotomicClassEigenspace_eq_iInf_eigenspace,
    cyclotomicTameChar_eq_of_zmod_eq hr ω hij]

theorem cyclotomicClassProjector_add_mul_sub_one (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i k : ℤ) :
    cyclotomicClassProjector p r hr ω (i + k * (p - 1 : ℕ)) =
      cyclotomicClassProjector p r hr ω i := by
  rw [cyclotomicClassProjector, cyclotomicClassProjector, cyclotomicTameChar_add_mul_sub_one]

theorem hasEnoughRootsOfUnity_padicInt_tameRoots (p r : ℕ) [Fact p.Prime] :
    HasEnoughRootsOfUnity ℤ_[p]
      (Monoid.exponent (rootsOfUnity (p - 1) (ZMod (p ^ r)))) := by
  have h1 : HasEnoughRootsOfUnity ℤ_[p] (p - 1) :=
    HasEnoughRootsOfUnity.of_card_le (card_rootsOfUnity_padicInt p).ge
  exact HasEnoughRootsOfUnity.of_dvd ℤ_[p]
    (Monoid.exponent_dvd_of_forall_pow_eq_one fun a ↦
      Subtype.ext ((mem_rootsOfUnity _ _).mp a.2))

/-- When `ω` is a section of reduction modulo `p`, `k : ZMod (p - 1) ↦ cyclotomicTameChar ... k.val`
is a bijection onto all `ℤ_[p]ˣ`-valued characters of `rootsOfUnity (p - 1) (ZMod (p ^ r))`. -/
noncomputable def tameCharEquiv (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    ZMod (p - 1) ≃ (rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ) := by
  have := hasEnoughRootsOfUnity_padicInt_tameRoots p r
  have : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  let φ : ZMod (p - 1) → (rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ) :=
    fun k ↦ cyclotomicTameChar p r hr ω k.val
  have hinj : Function.Injective φ := fun k₁ k₂ hk ↦ by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime (Fact.out : p.Prime)]
    let a := (tameRootsEquivUnitsZMod p r hr).symm g
    have ha : ZMod.unitsMap (dvd_pow_self p (by omega : r ≠ 0)) a.val = g :=
      (tameRootsEquivUnitsZMod p r hr).apply_symm_apply g
    have hpow' : (ω g) ^ (k₁.val : ℤ) = (ω g) ^ (k₂.val : ℤ) := by
      have h := DFunLike.congr_fun hk a
      simpa only [φ, cyclotomicTameChar_apply, ha] using h
    have hpow : (ω g) ^ k₁.val = (ω g) ^ k₂.val := by
      simpa only [zpow_natCast] using hpow'
    have hmod : g ^ k₁.val = g ^ k₂.val := by
      apply Units.ext
      have hval := congrArg (fun u : ℤ_[p]ˣ ↦ PadicInt.toZMod (u : ℤ_[p])) hpow
      simpa [Units.val_pow_eq_pow_val, map_pow, hω g] using hval
    have hmeq : k₁.val ≡ k₂.val [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hmod
    rw [hord] at hmeq
    exact ZMod.val_injective _ (hmeq.eq_of_lt_of_lt k₁.val_lt k₂.val_lt)
  have hcard : Fintype.card (ZMod (p - 1)) =
      Fintype.card (rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, card_tameRoots p r hr]
  exact Equiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)

@[simp]
theorem tameCharEquiv_apply (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p))
    (k : ZMod (p - 1)) :
    tameCharEquiv p r hr ω hω k = cyclotomicTameChar p r hr ω k.val :=
  (rfl)

/-- When `ω` lifts reduction modulo `p`, distinct residues `k₁ ≠ k₂` in `ZMod (p - 1)` give
orthogonal projectors. -/
theorem cyclotomicClassProjector_mul_eq_zero_of_ne {p r : ℕ} [Fact p.Prime] (hr : 1 ≤ r)
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ}
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p))
    {k₁ k₂ : ZMod (p - 1)} (hne : k₁ ≠ k₂) :
    cyclotomicClassProjector p r hr ω k₁.val * cyclotomicClassProjector p r hr ω k₂.val = 0 := by
  have hχ : cyclotomicTameChar p r hr ω k₁.val ≠ cyclotomicTameChar p r hr ω k₂.val := fun h ↦
    hne ((tameCharEquiv p r hr ω hω).injective h)
  rw [cyclotomicClassProjector, cyclotomicClassProjector, ← map_mul,
    charIdempotent_mul_charIdempotent_of_ne hχ, map_zero]

/-- **Completeness of the tame character projectors**: summing `cyclotomicClassProjector` over
`k : ZMod (p - 1)` yields the identity operator on the `p`-primary class module. -/
theorem sum_cyclotomicClassProjector (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    ∑ k : ZMod (p - 1), cyclotomicClassProjector p r hr ω k.val = 1 := by
  have := hasEnoughRootsOfUnity_padicInt_tameRoots p r
  calc ∑ k : ZMod (p - 1), cyclotomicClassProjector p r hr ω k.val
      = ∑ k : ZMod (p - 1),
          (cyclotomicTameRep p r).asAlgebraHom
            (charIdempotent (tameCharEquiv p r hr ω hω k)) := rfl
    _ = ∑ χ : rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ,
          (cyclotomicTameRep p r).asAlgebraHom (charIdempotent χ) :=
        (tameCharEquiv p r hr ω hω).sum_comp
          (fun χ ↦ (cyclotomicTameRep p r).asAlgebraHom (charIdempotent χ))
    _ = (cyclotomicTameRep p r).asAlgebraHom
          (∑ χ : rootsOfUnity (p - 1) (ZMod (p ^ r)) →* ℤ_[p]ˣ, charIdempotent χ) :=
        (map_sum _ _ _).symm
    _ = 1 := by rw [sum_charIdempotent (isUnit_card_tameRoots p r hr), map_one]

/-- The tame character projectors indexed by `ZMod (p - 1)` form a `CompleteOrthogonalIdempotents`
family in `Module.End ℤ_[p]`. -/
theorem completeOrthogonalIdempotents_cyclotomicClassProjector (p r : ℕ) [Fact p.Prime]
    (hr : 1 ≤ r) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    CompleteOrthogonalIdempotents
      (fun k : ZMod (p - 1) ↦ cyclotomicClassProjector p r hr ω k.val) :=
  ⟨⟨fun k ↦ isIdempotentElem_cyclotomicClassProjector p r hr ω k.val,
    fun _ _ hne ↦ cyclotomicClassProjector_mul_eq_zero_of_ne hr hω hne⟩,
    sum_cyclotomicClassProjector p r hr ω hω⟩

/-- **Tame eigenspace direct-sum decomposition**: when `ω` lifts reduction modulo `p`, the
`p`-primary cyclotomic class module at conductor `p ^ r` is the internal direct sum of its tame
eigenspaces `cyclotomicClassEigenspace p r hr ω k.val` over `k : ZMod (p - 1)`. -/
theorem isInternal_cyclotomicClassEigenspace (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    DirectSum.IsInternal (fun k : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r hr ω k.val) := by
  have hfun : (fun k : ZMod (p - 1) ↦
      cyclotomicClassProjector p r hr ω k.val •
        (⊤ : Submodule ℤ_[p]
          (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))))) =
      (fun k : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r hr ω k.val) := by
    funext k
    have hlin : DistribSMul.toLinearMap ℤ_[p]
        (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ))))
        (cyclotomicClassProjector p r hr ω k.val) =
        cyclotomicClassProjector p r hr ω k.val := rfl
    rw [Submodule.pointwise_smul_def, Submodule.map_top, hlin, range_cyclotomicClassProjector]
  rw [← hfun]
  exact isInternal_smul_top (S := ℤ_[p])
    (completeOrthogonalIdempotents_cyclotomicClassProjector p r hr ω hω)

/-- The bundled `ℤ_[p]`-linear equivalence between the direct sum of tame eigenspaces and the
`p`-primary cyclotomic class module at conductor `p ^ r`. -/
noncomputable def cyclotomicClassTameEquiv (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    (⨁ k : ZMod (p - 1), cyclotomicClassEigenspace p r hr ω k.val) ≃ₗ[ℤ_[p]]
      (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))) :=
  LinearEquiv.ofBijective
    (DirectSum.coeLinearMap fun k : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r hr ω k.val)
    (isInternal_cyclotomicClassEigenspace p r hr ω hω)

/-! ### Complex conjugation action and prime-power tower compatibility -/

/-- For an odd prime `p`, `-1 ∈ (ZMod (p ^ r))ˣ` is a `(p - 1)`-st root of unity. -/
theorem neg_one_mem_tameRoots (p r : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (-1 : (ZMod (p ^ r))ˣ) ∈ rootsOfUnity (p - 1) (ZMod (p ^ r)) := by
  rw [mem_rootsOfUnity]
  exact (Nat.Odd.sub_odd ((Fact.out : p.Prime).odd_of_ne_two hp) odd_one).neg_one_pow

/-- **Complex conjugation on tame eigenspaces**: for `p ≠ 2` and a section `ω` of reduction modulo
`p`, the Galois element `-1 : (ZMod (p ^ r))ˣ` acts on `cyclotomicClassEigenspace p r hr ω i` by
`(-1) ^ i`. -/
theorem cyclotomicClassAction_neg_one_of_mem_eigenspace {p r : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hr : 1 ≤ r) {ω : (ZMod p)ˣ →* ℤ_[p]ˣ}
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p))
    {i : ℤ} {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))}
    (hx : x ∈ cyclotomicClassEigenspace p r hr ω i) :
    cyclotomicClassAction ℤ_[p] (p ^ r) (-1) x = (((-1 : ℤ_[p]ˣ) ^ i : ℤ_[p]ˣ) : ℤ_[p]) • x := by
  have hact := (mem_cyclotomicClassEigenspace_iff hr).mp hx ⟨-1, neg_one_mem_tameRoots p r hp⟩
  have hmap : ZMod.unitsMap (dvd_pow_self p (by omega : r ≠ 0)) (-1 : (ZMod (p ^ r))ˣ) = -1 := by
    ext
    simp [ZMod.unitsMap_def]
  simpa [cyclotomicTameChar_apply, hmap, apply_neg_one_of_toZMod_eq p hp hω] using hact

/-- Natural-exponent specialization of `cyclotomicClassAction_neg_one_of_mem_eigenspace`. -/
theorem cyclotomicClassAction_neg_one_of_mem_eigenspace_natCast {p r : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hr : 1 ≤ r) {ω : (ZMod p)ˣ →* ℤ_[p]ˣ}
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p))
    {k : ℕ} {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))}
    (hx : x ∈ cyclotomicClassEigenspace p r hr ω k) :
    cyclotomicClassAction ℤ_[p] (p ^ r) (-1) x = ((-1 : ℤ_[p]) ^ k) • x := by
  simpa using cyclotomicClassAction_neg_one_of_mem_eigenspace hp hr hω hx

/-- For `1 ≤ r ≤ s`, reduction `ZMod.unitsMap` restricts to a multiplicative equivalence between
the `(p - 1)`-st roots of unity modulo `p ^ s` and modulo `p ^ r`. -/
noncomputable def tameRootsTowerEquiv (p r s : ℕ) [Fact p.Prime] (hr : 1 ≤ r) (hrs : r ≤ s) :
    rootsOfUnity (p - 1) (ZMod (p ^ s)) ≃* rootsOfUnity (p - 1) (ZMod (p ^ r)) :=
  (tameRootsEquivUnitsZMod p s (hr.trans hrs)).trans (tameRootsEquivUnitsZMod p r hr).symm

@[simp]
theorem coe_tameRootsTowerEquiv_apply (p r s : ℕ) [Fact p.Prime] (hr : 1 ≤ r) (hrs : r ≤ s)
    (a : rootsOfUnity (p - 1) (ZMod (p ^ s))) :
    (tameRootsTowerEquiv p r s hr hrs a : (ZMod (p ^ r))ˣ) =
      ZMod.unitsMap (Nat.pow_dvd_pow p hrs) a.val := by
  have hmem : ZMod.unitsMap (Nat.pow_dvd_pow p hrs) a.val ∈
      rootsOfUnity (p - 1) (ZMod (p ^ r)) := by
    rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity _ _).mp a.2, map_one]
  have h1 : tameRootsEquivUnitsZMod p r hr (tameRootsTowerEquiv p r s hr hrs a) =
      tameRootsEquivUnitsZMod p r hr ⟨_, hmem⟩ := by
    rw [tameRootsTowerEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      tameRootsEquivUnitsZMod_apply, tameRootsEquivUnitsZMod_apply,
      ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  exact congrArg Subtype.val ((tameRootsEquivUnitsZMod p r hr).injective h1)

/-- **Tower compatibility of class-group extension on tame eigenspaces**: for `1 ≤ r ≤ s`,
extending classes from `CyclotomicField (p ^ r) ℚ` to `CyclotomicField (p ^ s) ℚ` preserves the
`i`-th tame eigenspace. -/
theorem classGroupExtendedLinearMap_mem_cyclotomicClassEigenspace {p r s : ℕ} [Fact p.Prime]
    (hr : 1 ≤ r) (hrs : r ≤ s)
    [Algebra (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ)]
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {i : ℤ}
    {x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))}
    (hx : x ∈ cyclotomicClassEigenspace p r hr ω i) :
    classGroupExtendedLinearMap ℤ_[p] (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ) x ∈
      cyclotomicClassEigenspace p s (hr.trans hrs) ω i := by
  have hr0 : r ≠ 0 := by omega
  rw [mem_cyclotomicClassEigenspace_iff] at hx ⊢
  intro a
  let b := tameRootsTowerEquiv p r s hr hrs a
  have hb : b.val = ZMod.unitsMap (Nat.pow_dvd_pow p hrs) a.val :=
    coe_tameRootsTowerEquiv_apply p r s hr hrs a
  have hchar : cyclotomicTameChar p r hr ω i b =
      cyclotomicTameChar p s (hr.trans hrs) ω i a := by
    simp only [cyclotomicTameChar_apply, hb]
    congr 2
    exact DFunLike.congr_fun
      (ZMod.unitsMap_comp (dvd_pow_self p hr0) (Nat.pow_dvd_pow p hrs)) a.val
  rw [cyclotomicClassAction_eq_cyclotomicFieldClassAction,
    cyclotomicFieldClassAction_extendedLinearMap ℤ_[p] (Nat.pow_dvd_pow p hrs), ← hb,
    ← cyclotomicClassAction_eq_cyclotomicFieldClassAction, hx b, map_smul, hchar]

/-- **Tower compatibility of class-group relative norm on tame eigenspaces**: for `1 ≤ r ≤ s`,
the relative norm from `CyclotomicField (p ^ s) ℚ` to `CyclotomicField (p ^ r) ℚ` preserves the
`i`-th tame eigenspace. -/
theorem classGroupRelNormLinearMap_mem_cyclotomicClassEigenspace {p r s : ℕ} [Fact p.Prime]
    (hr : 1 ≤ r) (hrs : r ≤ s)
    [Algebra (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ)]
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {i : ℤ}
    {y : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ s) ℚ)))}
    (hy : y ∈ cyclotomicClassEigenspace p s (hr.trans hrs) ω i) :
    classGroupRelNormLinearMap ℤ_[p] (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ) y ∈
      cyclotomicClassEigenspace p r hr ω i := by
  have hr0 : r ≠ 0 := by omega
  rw [mem_cyclotomicClassEigenspace_iff] at hy ⊢
  intro b
  let a := (tameRootsTowerEquiv p r s hr hrs).symm b
  have ha : ZMod.unitsMap (Nat.pow_dvd_pow p hrs) a.val = b.val := by
    rw [← coe_tameRootsTowerEquiv_apply p r s hr hrs a, MulEquiv.apply_symm_apply]
  have hchar : cyclotomicTameChar p s (hr.trans hrs) ω i a =
      cyclotomicTameChar p r hr ω i b := by
    simp only [cyclotomicTameChar_apply, ← ha]
    congr 2
    exact (DFunLike.congr_fun
      (ZMod.unitsMap_comp (dvd_pow_self p hr0) (Nat.pow_dvd_pow p hrs)) a.val).symm
  rw [cyclotomicClassAction_eq_cyclotomicFieldClassAction, ← ha,
    cyclotomicFieldClassAction_relNormLinearMap ℤ_[p] (Nat.pow_dvd_pow p hrs),
    ← cyclotomicClassAction_eq_cyclotomicFieldClassAction, hy a, map_smul, hchar]

/-- **Class-group extension commutes with tame projectors** across prime-power levels
`1 ≤ r ≤ s`. -/
theorem classGroupExtendedLinearMap_cyclotomicClassProjector {p r s : ℕ} [Fact p.Prime]
    (hr : 1 ≤ r) (hrs : r ≤ s)
    [Algebra (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ)]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ)
    (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))) :
    classGroupExtendedLinearMap ℤ_[p] (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ)
        (cyclotomicClassProjector p r hr ω i x) =
      cyclotomicClassProjector p s (hr.trans hrs) ω i
        (classGroupExtendedLinearMap ℤ_[p]
          (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ) x) := by
  have hr0 : r ≠ 0 := by omega
  let e := tameRootsTowerEquiv p r s hr hrs
  simp only [cyclotomicClassProjector_eq_sum, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, map_smul, map_sum]
  congr 1
  rw [← e.toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [show e.toEquiv a = e a from rfl]
  have hb : (e a).val = ZMod.unitsMap (Nat.pow_dvd_pow p hrs) a.val :=
    coe_tameRootsTowerEquiv_apply p r s hr hrs a
  have hchar : cyclotomicTameChar p r hr ω i (e a) =
      cyclotomicTameChar p s (hr.trans hrs) ω i a := by
    rw [cyclotomicTameChar_apply, cyclotomicTameChar_apply, coe_tameRootsTowerEquiv_apply]
    congr 2
    exact DFunLike.congr_fun
      (ZMod.unitsMap_comp (dvd_pow_self p hr0) (Nat.pow_dvd_pow p hrs)) a.val
  rw [hchar, cyclotomicClassAction_eq_cyclotomicFieldClassAction, hb,
    ← cyclotomicFieldClassAction_extendedLinearMap ℤ_[p] (Nat.pow_dvd_pow p hrs),
    ← cyclotomicClassAction_eq_cyclotomicFieldClassAction]

/-- **Class-group relative norm commutes with tame projectors** across prime-power levels
`1 ≤ r ≤ s`. -/
theorem classGroupRelNormLinearMap_cyclotomicClassProjector {p r s : ℕ} [Fact p.Prime]
    (hr : 1 ≤ r) (hrs : r ≤ s)
    [Algebra (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ)]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ)
    (y : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ s) ℚ)))) :
    classGroupRelNormLinearMap ℤ_[p] (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ)
        (cyclotomicClassProjector p s (hr.trans hrs) ω i y) =
      cyclotomicClassProjector p r hr ω i
        (classGroupRelNormLinearMap ℤ_[p]
          (CyclotomicField (p ^ r) ℚ) (CyclotomicField (p ^ s) ℚ) y) := by
  have hr0 : r ≠ 0 := by omega
  let e := tameRootsTowerEquiv p r s hr hrs
  simp only [cyclotomicClassProjector_eq_sum, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, map_smul, map_sum]
  congr 1
  symm
  rw [← e.toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [show e.toEquiv a = e a from rfl]
  have hb : (e a).val = ZMod.unitsMap (Nat.pow_dvd_pow p hrs) a.val :=
    coe_tameRootsTowerEquiv_apply p r s hr hrs a
  have hchar : cyclotomicTameChar p r hr ω i (e a) =
      cyclotomicTameChar p s (hr.trans hrs) ω i a := by
    rw [cyclotomicTameChar_apply, cyclotomicTameChar_apply, coe_tameRootsTowerEquiv_apply]
    congr 2
    exact DFunLike.congr_fun
      (ZMod.unitsMap_comp (dvd_pow_self p hr0) (Nat.pow_dvd_pow p hrs)) a.val
  rw [hchar, cyclotomicClassAction_eq_cyclotomicFieldClassAction, hb,
    cyclotomicFieldClassAction_relNormLinearMap ℤ_[p] (Nat.pow_dvd_pow p hrs),
    ← cyclotomicClassAction_eq_cyclotomicFieldClassAction]

end TameEigenspaces

end TauCeti
