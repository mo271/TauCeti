/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.MultiquadraticConductor
public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.CharacterConductors
public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.ConductorDiscriminant
public import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield
public import TauCeti.NumberTheory.NumberField.Discriminant.Relative

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.GroupTheory.FiniteAbelian.Duality
import TauCeti.NumberTheory.NumberField.Global.RayClass.Rat
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Worked checks of the conductor–discriminant formula on cyclotomic extensions of `ℚ`

For a finite abelian extension `L/K` and a commutative monoid `M` with enough roots of unity, the
conductor–discriminant theorem (`relDiscr_eq_finprod_finitePart_abelianConductor`) and the
character-conductor maximum theorem (`exponent_abelianConductor_eq_iSup_fixedField_ker`) express
the relative discriminant and the extension conductor in terms of the conductors
`abelianConductor K (fixedField χ.ker)` of the characters `χ : Gal(L/K) →* Mˣ`:

* `multiplicity v (𝔡_{L/K}) = ∑_χ (abelianConductor K L^{ker χ}).exponent v`,
* `(abelianConductor K L).exponent v = ⨆_χ (abelianConductor K L^{ker χ}).exponent v`.

This file evaluates every term of both identities on three classical cyclotomic families over `ℚ`:

1. **The Gaussian field `ℚ(i) = ℚ(ζ₄)`.** The two characters of `Gal(ℚ(i)/ℚ)` have conductors
   `(1)` and `(4)·∞`, with `2`-exponents `{0, 2}` summing to `2 = v₂(|d_{ℚ(i)}|)` (`|d_{ℚ(i)}| = 4`)
   and having maximum `2`.
2. **The eighth cyclotomic field `ℚ(ζ₈) = ℚ(i, √2)`.** Its Galois group `(ℤ/8ℤ)ˣ ≅ C₂ × C₂` cuts
   out `ℚ` and the three quadratic subfields `ℚ(i)`, `ℚ(√2)`, `ℚ(√-2)`, whose conductors are `(1)`,
   `(4)·∞`, `(8)`, `(8)·∞`. At the prime `2`, the character conductor exponents form the multiset
   `{0, 2, 3, 3}`: their sum is `8 = v₂(256)` (`|d_{ℚ(ζ₈)}| = 256`), whereas their maximum is `3`
   (`(abelianConductor ℚ ℚ(ζ₈)).finitePart` has norm `8 ≠ 256`), illustrating the difference
   between the discriminant product and the conductor least common multiple in a non-cyclic
   extension.
3. **Prime cyclotomic fields `ℚ(ζ_p)`.** Every nontrivial subextension `ℚ(ζ_p)^H` (`H ≠ ⊤`) has
   finite conductor norm `p`, hence `p`-exponent `1`. A nontrivial character `χ` has full conductor
   `(p)` when `χ` is even (`χ(τ) = 1` on complex conjugation `τ`) and `(p)·∞` when `χ` is odd. For
   an odd prime `p`, the `p - 2` nontrivial characters and `1` trivial character sum to
   `p - 2 = v_p(|d_{ℚ(ζ_p)}|)` (`|d_{ℚ(ζ_p)}| = p^{p - 2}`) with maximum `1`.

## Main results

* `TauCeti.ClassFieldTheory.isTotallyReal_fixedField_ker_iff`: in `ℚ(ζ_n)/ℚ`, `fixedField χ.ker`
  is totally real iff `χ` is trivial on complex conjugation `(galEquivZMod n F).symm (-1)`.
* `TauCeti.ClassFieldTheory.multiset_abelianConductor_cyclotomic_four`,
  `TauCeti.ClassFieldTheory.multiset_exponent_abelianConductor_cyclotomic_four`, and
  `TauCeti.ClassFieldTheory.finsum_exponent_abelianConductor_cyclotomic_four`: character
  conductors, `2`-exponents, and discriminant sum for `ℚ(i)/ℚ`.
* `TauCeti.ClassFieldTheory.multiset_abelianConductor_cyclotomic_eight`,
  `TauCeti.ClassFieldTheory.multiset_exponent_abelianConductor_cyclotomic_eight`, and
  `TauCeti.ClassFieldTheory.absNorm_finprod_finitePart_abelianConductor_cyclotomic_eight`:
  character conductors, `2`-exponent multiset `{0, 2, 3, 3}`, and discriminant norm `256` for
  `ℚ(ζ₈)/ℚ`.
* `TauCeti.ClassFieldTheory.absNorm_abelianConductor_finitePart_fixedField_cyclotomic_prime`,
  `TauCeti.ClassFieldTheory.abelianConductor_fixedField_ker_cyclotomic_prime_of_even`,
  `TauCeti.ClassFieldTheory.abelianConductor_fixedField_ker_cyclotomic_prime_of_odd`, and
  `TauCeti.ClassFieldTheory.finsum_exponent_abelianConductor_cyclotomic_prime`: subfield and
  character conductors and the discriminant exponent `p - 2` for `ℚ(ζ_p)/ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §11.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 3.11 (the conductor–discriminant
  formula).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField _root_.NumberField.InfinitePlace _root_.IntermediateField
  ComplexConjugate TauCeti.GlobalNumberFields TauCeti.Multiquadratic
open scoped IsMulCommutative

/-! ### Character and parity helpers for cyclotomic extensions -/

/-- A nontrivial homomorphism has proper kernel. -/
private theorem ker_ne_top_of_ne_one {G A : Type*} [Group G] [MulOneClass A] {χ : G →* A}
    (hχ : χ ≠ 1) : χ.ker ≠ ⊤ :=
  fun h ↦ hχ (by ext g; exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g))

/-- Every index-`2` subgroup of a finite commutative group is the kernel of a character into `Mˣ`
whenever `M` has enough roots of unity. -/
private theorem exists_ker_eq_of_index_eq_two {G : Type*} [CommGroup G] [Finite G]
    (M : Type*) [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent G)]
    {H : Subgroup G} (hH : H.index = 2) :
    ∃ χ : G →* Mˣ, χ.ker = H := by
  have hcard : Nat.card {φ : G →* Mˣ // H ≤ φ.ker} = 2 := by
    rw [← hH, Subgroup.index_eq_card, ← CommGroup.card_domRestrictHom_ker M H]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun φ ↦ by simp [IsConcreteLE.le_iff])
  have : Nontrivial {φ : G →* Mˣ // H ≤ φ.ker} :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨χ, hHχ⟩, hne⟩ := exists_ne (⟨1, fun _ _ ↦ rfl⟩ : {φ : G →* Mˣ // H ≤ φ.ker})
  have hχ1 : χ ≠ 1 := fun h ↦ hne (Subtype.ext h)
  have hk1 : χ.ker.index ≠ 1 := Subgroup.index_eq_one.not.mpr (ker_ne_top_of_ne_one hχ1)
  have hmul : H.relIndex χ.ker * χ.ker.index = 2 := hH ▸ Subgroup.relIndex_mul_index hHχ
  rcases (Nat.dvd_prime Nat.prime_two).mp ⟨_, hmul.symm.trans (mul_comm _ _)⟩ with hk | hk
  · exact absurd hk hk1
  · rw [hk] at hmul
    exact ⟨χ, le_antisymm (Subgroup.relIndex_eq_one.mp (by omega)) hHχ⟩

/-- A quadratic generator `x² = d` in a number field whose subfield `ℚ⟮x⟯` has nontrivial conductor
generates a degree-`2` extension of `ℚ`. -/
private theorem finrank_adjoin_sq_eq_two_of_abelianConductor_ne_one {L : Type} [Field L]
    [NumberField L] {d : ℤ} {x : L} (hx : x ^ 2 = (d : L))
    (hne : abelianConductor ℚ ℚ⟮x⟯ ≠ Modulus.one ℚ) :
    Module.finrank ℚ ℚ⟮x⟯ = 2 := by
  have hle : Module.finrank ℚ ℚ⟮x⟯ ≤ 2 := by
    rw [adjoin.finrank (IsIntegral.of_finite ℚ x)]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ x (by simp [hx]))
      (Polynomial.X_pow_sub_C_ne_zero two_pos (d : ℚ))).trans_eq
      (Polynomial.natDegree_X_pow_sub_C (n := 2) (a := (d : ℚ)))
  have hpos : 0 < Module.finrank ℚ ℚ⟮x⟯ := Module.finrank_pos
  have hne1 : Module.finrank ℚ ℚ⟮x⟯ ≠ 1 := fun h1 ↦ hne <| by
    rw [abelianConductor_congr (equivOfEq (finrank_eq_one_iff.mp h1)), abelianConductor_bot]
  omega

/-- **Total reality of a fixed field inside `ℚ(ζ_n)`.** For a subgroup `H` of `Gal(ℚ(ζ_n)/ℚ)`, the
fixed field `fixedField H` is totally real if and only if complex conjugation
`(galEquivZMod n F).symm (-1)` belongs to `H`. -/
theorem isTotallyReal_fixedField_iff_galEquivZMod_symm_neg_one_mem (n : ℕ) [NeZero n]
    (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (H : Subgroup Gal(F/ℚ)) :
    IsTotallyReal (fixedField H) ↔
      (IsCyclotomicExtension.Rat.galEquivZMod n F).symm (-1) ∈ H := by
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  set τ := (IsCyclotomicExtension.Rat.galEquivZMod n F).symm (-1)
  conv_rhs =>
    rw [← _root_.IntermediateField.fixingSubgroup_fixedField H,
      _root_.IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun hreal x hx ↦ ?_, fun hτ ↦ ?_⟩
  · let φ : F →+* ℂ := Classical.choice inferInstance
    let w : InfinitePlace (fixedField H) := InfinitePlace.mk (φ.comp (fixedField H).val.toRingHom)
    have hw : ComplexEmbedding.IsReal (φ.comp (fixedField H).val.toRingHom) :=
      InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal w)
    apply φ.injective
    rw [TauCeti.IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply
      n (K := F) φ]
    simpa [ComplexEmbedding.conjugate_coe_eq] using
      DFunLike.congr_fun (ComplexEmbedding.isReal_iff.mp hw) ⟨x, hx⟩
  · rw [isTotallyReal_iff]
    intro w
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext y
    let _ : Algebra (fixedField H) ℂ := w.embedding.toAlgebra
    let φ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[fixedField H] ℂ).toRingHom
    have hφ : φ y.1 = w.embedding y := (IsAlgClosed.lift : F →ₐ[fixedField H] ℂ).commutes y
    rw [ComplexEmbedding.conjugate_coe_eq, ← hφ,
      ← TauCeti.IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply
        n (K := F) φ,
      hτ y.1 y.2]

/-- **Total reality of a character's fixed field inside `ℚ(ζ_n)`.** The fixed field
`fixedField χ.ker` is totally real if and only if `χ` is even, i.e., trivial on complex conjugation
`(galEquivZMod n F).symm (-1)`. -/
theorem isTotallyReal_fixedField_ker_iff (n : ℕ) [NeZero n] (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] {A : Type*} [MulOneClass A] (χ : Gal(F/ℚ) →* A) :
    IsTotallyReal (fixedField χ.ker) ↔
      χ ((IsCyclotomicExtension.Rat.galEquivZMod n F).symm (-1)) = 1 := by
  rw [isTotallyReal_fixedField_iff_galEquivZMod_symm_neg_one_mem n F, MonoidHom.mem_ker]

/-! ### Check 1: The Gaussian field `ℚ(i) = ℚ(ζ₄)` -/

section CyclotomicFour

variable (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]

/-- The relative discriminant of `ℚ(ζ₄)/ℚ` has absolute norm `4`. -/
theorem absNorm_relDiscr_cyclotomic_four :
    Ideal.absNorm (relDiscr (𝓞 ℚ) (𝓞 F)) = 4 := by
  have : IsCyclotomicExtension {2 ^ 2} ℚ F := by norm_num; infer_instance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [TauCeti.NumberField.absNorm_relDiscr_ringOfIntegers_rat,
    IsCyclotomicExtension.Rat.discr_prime_pow 2 2 F]
  decide

/-- At the prime `v` of `𝓞 ℚ` above `2`, `relDiscr (𝓞 ℚ) (𝓞 ℚ(ζ₄))` has multiplicity `2`. -/
theorem multiplicity_relDiscr_cyclotomic_four {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = 2) :
    multiplicity v.asIdeal (relDiscr (𝓞 ℚ) (𝓞 F)) = 2 := by
  rw [Rat.HeightOneSpectrum.multiplicity_asIdeal, absNorm_relDiscr_cyclotomic_four F, hv,
    show (4 : ℕ) = 2 ^ 2 by norm_num,
    multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 2]

/-- The nontrivial character of `Gal(ℚ(ζ₄)/ℚ)` has conductor `(4)·∞`. -/
theorem abelianConductor_fixedField_ker_cyclotomic_four_of_ne_one {A : Type*} [MulOneClass A]
    {χ : Gal(F/ℚ) →* A} (hχ : χ ≠ 1) :
    abelianConductor ℚ (fixedField χ.ker) = ratModulus 4 (by norm_num) := by
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {4} ℚ F
  have hcard : Nat.card Gal(F/ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank ℚ F, IsCyclotomicExtension.finrank (n := 4) F
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have : Fact (Nat.card Gal(F/ℚ)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  have hbot : χ.ker = ⊥ :=
    (Subgroup.eq_bot_or_eq_top_of_prime_card χ.ker).resolve_right (ker_ne_top_of_ne_one hχ)
  rw [abelianConductor_congr (equivOfEq (hbot ▸ IntermediateField.fixedField_bot)),
    abelianConductor_top, abelianConductor_cyclotomic_eq_ratModulus 4 F (by norm_num) (by decide)]

/-- **The character conductors of `ℚ(ζ₄)/ℚ`** form the multiset `{(1), (4)·∞}`. -/
theorem multiset_abelianConductor_cyclotomic_four (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] [Fintype (Gal(F/ℚ) →* Mˣ)] :
    (Finset.univ.val.map fun χ : Gal(F/ℚ) →* Mˣ ↦ abelianConductor ℚ (fixedField χ.ker)) =
      {Modulus.one ℚ, ratModulus 4 (by norm_num)} := by
  classical
  have := IsCyclotomicExtension.isAbelianGalois {4} ℚ F
  have hcardG : Nat.card Gal(F/ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank ℚ F, IsCyclotomicExtension.finrank (n := 4) F
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hbot : (⊥ : Subgroup Gal(F/ℚ)).index = 2 := by rw [Subgroup.index_bot, hcardG]
  obtain ⟨χ₁, hχ₁⟩ := exists_ker_eq_of_index_eq_two M hbot
  have hχ₁_ne : χ₁ ≠ 1 := by
    rintro rfl
    rw [MonoidHom.ker_one] at hχ₁
    rw [← hχ₁, Subgroup.index_top] at hbot
    omega
  have huniv : (Finset.univ : Finset (Gal(F/ℚ) →* Mˣ)) = {1, χ₁} := by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [Finset.card_pair hχ₁_ne.symm, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Gal(F/ℚ) M, hcardG]
  have h1bot : fixedField (1 : Gal(F/ℚ) →* Mˣ).ker = (⊥ : IntermediateField ℚ F) := by
    simp [MonoidHom.ker_one]
  have hc0 : abelianConductor ℚ (fixedField (1 : Gal(F/ℚ) →* Mˣ).ker) = Modulus.one ℚ := by
    rw [abelianConductor_congr (equivOfEq h1bot), abelianConductor_bot]
  rw [huniv, Finset.insert_val_of_notMem (Finset.notMem_singleton.mpr hχ₁_ne.symm),
    Finset.singleton_val, Multiset.map_cons, Multiset.map_singleton, hc0,
    abelianConductor_fixedField_ker_cyclotomic_four_of_ne_one F hχ₁_ne]
  rfl

/-- **The `2`-exponent multiset of character conductors of `ℚ(ζ₄)/ℚ`** is `{0, 2}`. -/
theorem multiset_exponent_abelianConductor_cyclotomic_four (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] [Fintype (Gal(F/ℚ) →* Mˣ)]
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : Ideal.absNorm v.asIdeal = 2) :
    (Finset.univ.val.map fun χ : Gal(F/ℚ) →* Mˣ ↦
      (abelianConductor ℚ (fixedField χ.ker)).exponent v) = {0, 2} := by
  have hm4 : multiplicity 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 2]
  have hmap := congrArg (Multiset.map fun 𝔪 : Modulus ℚ ↦ 𝔪.exponent v)
    (multiset_abelianConductor_cyclotomic_four F M)
  rw [Multiset.map_map] at hmap
  simpa [Function.comp_def, hv, hm4] using hmap

/-- **Sum of character `2`-exponents for `ℚ(ζ₄)/ℚ`**: `0 + 2 = 2`. -/
theorem finsum_exponent_abelianConductor_cyclotomic_four (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = 2) :
    (∑ᶠ χ : Gal(F/ℚ) →* Mˣ, (abelianConductor ℚ (fixedField χ.ker)).exponent v) = 2 := by
  have := IsCyclotomicExtension.isAbelianGalois {4} ℚ F
  rw [← multiplicity_relDiscr_eq_finsum_exponent_abelianConductor M v,
    multiplicity_relDiscr_cyclotomic_four F hv]

/-- **Maximum of character `2`-exponents for `ℚ(ζ₄)/ℚ`**: `max(0, 2) = 2`. -/
theorem iSup_exponent_abelianConductor_cyclotomic_four (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = 2) :
    (⨆ χ : Gal(F/ℚ) →* Mˣ, (abelianConductor ℚ (fixedField χ.ker)).exponent v) = 2 := by
  have := IsCyclotomicExtension.isAbelianGalois {4} ℚ F
  rw [← exponent_abelianConductor_eq_iSup_fixedField_ker ℚ F M v,
    abelianConductor_cyclotomic_eq_ratModulus 4 F (by norm_num) (by decide),
    ratModulus_exponent, hv, show (4 : ℕ) = 2 ^ 2 by norm_num,
    multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 2]

end CyclotomicFour

/-! ### Check 2: The eighth cyclotomic field `ℚ(ζ₈) = ℚ(i, √2)` -/

section CyclotomicEight

variable (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {8} ℚ F]

/-- The relative discriminant of `ℚ(ζ₈)/ℚ` has absolute norm `256 = 2⁸`. -/
theorem absNorm_relDiscr_cyclotomic_eight :
    Ideal.absNorm (relDiscr (𝓞 ℚ) (𝓞 F)) = 256 := by
  have : IsCyclotomicExtension {2 ^ 3} ℚ F := by norm_num; infer_instance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [TauCeti.NumberField.absNorm_relDiscr_ringOfIntegers_rat,
    IsCyclotomicExtension.Rat.discr_prime_pow 2 3 F]
  decide

/-- At the prime `v` of `𝓞 ℚ` above `2`, `relDiscr (𝓞 ℚ) (𝓞 ℚ(ζ₈))` has multiplicity `8`. -/
theorem multiplicity_relDiscr_cyclotomic_eight {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = 2) :
    multiplicity v.asIdeal (relDiscr (𝓞 ℚ) (𝓞 F)) = 8 := by
  rw [Rat.HeightOneSpectrum.multiplicity_asIdeal, absNorm_relDiscr_cyclotomic_eight F, hv,
    show (256 : ℕ) = 2 ^ 8 by norm_num,
    multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 8]

/-- Each quadratic subfield `ℚ⟮x⟯` of `ℚ(ζ₈)` (`x² = d`) with conductor `𝔪 ≠ (1)` is cut out by a
character `χ : Gal(ℚ(ζ₈)/ℚ) →* Mˣ` whose fixed field has conductor `𝔪`. -/
private theorem exists_char_abelianConductor_eq_of_sq_eq (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] {d : ℤ} {x : F} (hx : x ^ 2 = (d : F))
    {𝔪 : Modulus ℚ} (h𝔪 : abelianConductor ℚ ℚ⟮x⟯ = 𝔪) (hne : 𝔪 ≠ Modulus.one ℚ) :
    ∃ χ : Gal(F/ℚ) →* Mˣ, abelianConductor ℚ (fixedField χ.ker) = 𝔪 := by
  have := IsCyclotomicExtension.isAbelianGalois {8} ℚ F
  have hfin : Module.finrank ℚ ℚ⟮x⟯ = 2 :=
    finrank_adjoin_sq_eq_two_of_abelianConductor_ne_one hx (h𝔪 ▸ hne)
  have hidx : ℚ⟮x⟯.fixingSubgroup.index = 2 := by
    rw [← finrank_eq_fixingSubgroup_index, hfin]
  obtain ⟨χ, hχ⟩ := exists_ker_eq_of_index_eq_two M hidx
  refine ⟨χ, ?_⟩
  rw [abelianConductor_congr (equivOfEq (hχ ▸ IsGalois.fixedField_fixingSubgroup ℚ⟮x⟯)), h𝔪]

/-- The moduli `(1)`, `(4)·∞`, `(8)`, `(8)·∞` are pairwise distinct. -/
private theorem ratModulus_four_eight_ne :
    Modulus.one ℚ ≠ ratModulus 4 (by norm_num) ∧
      Modulus.one ℚ ≠ ratFiniteModulus 8 (by norm_num) ∧
      Modulus.one ℚ ≠ ratModulus 8 (by norm_num) ∧
      ratModulus 4 (by norm_num) ≠ ratFiniteModulus 8 (by norm_num) ∧
      ratModulus 4 (by norm_num) ≠ ratModulus 8 (by norm_num) ∧
      ratFiniteModulus 8 (by norm_num) ≠ ratModulus 8 (by norm_num) := by
  have hn1 : Ideal.absNorm (Modulus.one ℚ).finitePart = 1 := by simp
  have hn4 : Ideal.absNorm (ratModulus 4 (by norm_num)).finitePart = 4 :=
    (eq_ratModulus_iff.mp rfl).1
  have hn8f : Ideal.absNorm (ratFiniteModulus 8 (by norm_num)).finitePart = 8 :=
    (eq_ratFiniteModulus_iff.mp rfl).1
  have hn8 : Ideal.absNorm (ratModulus 8 (by norm_num)).finitePart = 8 :=
    (eq_ratModulus_iff.mp rfl).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · have := congrArg (Ideal.absNorm ∘ Modulus.finitePart) h; dsimp at this; omega
  · have := congrArg (Ideal.absNorm ∘ Modulus.finitePart) h; dsimp at this; omega
  · have := congrArg (Ideal.absNorm ∘ Modulus.finitePart) h; dsimp at this; omega
  · have := congrArg (Ideal.absNorm ∘ Modulus.finitePart) h; dsimp at this; omega
  · have := congrArg (Ideal.absNorm ∘ Modulus.finitePart) h; dsimp at this; omega
  · have := congrArg (fun 𝔪 : Modulus ℚ ↦
      (⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩ : {w : InfinitePlace ℚ // w.IsReal}) ∈
        𝔪.infinitePart) h
    simp at this

/-- **The character conductors of `ℚ(ζ₈)/ℚ`** form the multiset `{(1), (4)·∞, (8), (8)·∞}`,
corresponding to `ℚ` and the three quadratic subfields `ℚ(i)`, `ℚ(√2)`, `ℚ(√-2)`. -/
theorem multiset_abelianConductor_cyclotomic_eight (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] [Fintype (Gal(F/ℚ) →* Mˣ)] :
    (Finset.univ.val.map fun χ : Gal(F/ℚ) →* Mˣ ↦ abelianConductor ℚ (fixedField χ.ker)) =
      {Modulus.one ℚ, ratModulus 4 (by norm_num),
        ratFiniteModulus 8 (by norm_num), ratModulus 8 (by norm_num)} := by
  classical
  have := IsCyclotomicExtension.isAbelianGalois {8} ℚ F
  have hζ := IsCyclotomicExtension.zeta_spec 8 ℚ F
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := ratModulus_four_eight_ne
  obtain ⟨x₁, -, hx₁⟩ := exists_mem_sq_eq_neg_one (F := (⊤ : IntermediateField ℚ F))
    (hζ.pow (by norm_num) (by norm_num : 8 = 2 * 4)) mem_top
  obtain ⟨x₂, -, hx₂⟩ := exists_mem_sq_eq_two (F := (⊤ : IntermediateField ℚ F)) hζ mem_top
  obtain ⟨x₃, -, hx₃⟩ := exists_mem_sq_eq_neg_two (F := (⊤ : IntermediateField ℚ F)) hζ mem_top
  obtain ⟨χ₁, hχ₁⟩ := exists_char_abelianConductor_eq_of_sq_eq F M (d := -1) (by simpa using hx₁)
    (abelianConductor_adjoin_sqrt_neg_one hx₁) h01.symm
  obtain ⟨χ₂, hχ₂⟩ := exists_char_abelianConductor_eq_of_sq_eq F M (d := 2) (by simpa using hx₂)
    (abelianConductor_adjoin_sqrt_two hx₂) h02.symm
  obtain ⟨χ₃, hχ₃⟩ := exists_char_abelianConductor_eq_of_sq_eq F M (d := -2) (by simpa using hx₃)
    (abelianConductor_adjoin_sqrt_neg_two hx₃) h03.symm
  have h1bot : fixedField (1 : Gal(F/ℚ) →* Mˣ).ker = (⊥ : IntermediateField ℚ F) := by
    simp [MonoidHom.ker_one]
  have hc0 : abelianConductor ℚ (fixedField (1 : Gal(F/ℚ) →* Mˣ).ker) = Modulus.one ℚ := by
    rw [abelianConductor_congr (equivOfEq h1bot), abelianConductor_bot]
  have hcard : Fintype.card (Gal(F/ℚ) →* Mˣ) = 4 := by
    rw [← Nat.card_eq_fintype_card, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Gal(F/ℚ) M,
      IsGalois.card_aut_eq_finrank ℚ F, IsCyclotomicExtension.finrank (n := 8) F
        (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hmem0 : (1 : Gal(F/ℚ) →* Mˣ) ∉ ({χ₁, χ₂, χ₃} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ h01 (hc0 ▸ h ▸ hχ₁), fun h ↦ h02 (hc0 ▸ h ▸ hχ₂), fun h ↦ h03 (hc0 ▸ h ▸ hχ₃)⟩
  have hmem1 : χ₁ ∉ ({χ₂, χ₃} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ h12 (hχ₁ ▸ h ▸ hχ₂), fun h ↦ h13 (hχ₁ ▸ h ▸ hχ₃)⟩
  have hmem2 : χ₂ ∉ ({χ₃} : Finset _) :=
    Finset.notMem_singleton.mpr fun h ↦ h23 (hχ₂ ▸ h ▸ hχ₃)
  have huniv : (Finset.univ : Finset (Gal(F/ℚ) →* Mˣ)) = {1, χ₁, χ₂, χ₃} := by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [Finset.card_insert_of_notMem hmem0, Finset.card_insert_of_notMem hmem1,
      Finset.card_insert_of_notMem hmem2, Finset.card_singleton, hcard]
  rw [huniv, Finset.insert_val_of_notMem hmem0, Finset.insert_val_of_notMem hmem1,
    Finset.insert_val_of_notMem hmem2, Finset.singleton_val, Multiset.map_cons,
    Multiset.map_cons, Multiset.map_cons, Multiset.map_singleton, hc0, hχ₁, hχ₂, hχ₃]
  rfl

/-- **The `2`-exponent multiset of character conductors of `ℚ(ζ₈)/ℚ`** is `{0, 2, 3, 3}`. -/
theorem multiset_exponent_abelianConductor_cyclotomic_eight (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] [Fintype (Gal(F/ℚ) →* Mˣ)]
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : Ideal.absNorm v.asIdeal = 2) :
    (Finset.univ.val.map fun χ : Gal(F/ℚ) →* Mˣ ↦
      (abelianConductor ℚ (fixedField χ.ker)).exponent v) = {0, 2, 3, 3} := by
  have hm4 : multiplicity 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 2]
  have hm8 : multiplicity 2 8 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
      multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 3]
  have hmap := congrArg (Multiset.map fun 𝔪 : Modulus ℚ ↦ 𝔪.exponent v)
    (multiset_abelianConductor_cyclotomic_eight F M)
  rw [Multiset.map_map] at hmap
  simpa [Function.comp_def, hv, hm4, hm8] using hmap

/-- **Sum of character `2`-exponents for `ℚ(ζ₈)/ℚ`**: `0 + 2 + 3 + 3 = 8`. -/
theorem finsum_exponent_abelianConductor_cyclotomic_eight (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = 2) :
    (∑ᶠ χ : Gal(F/ℚ) →* Mˣ, (abelianConductor ℚ (fixedField χ.ker)).exponent v) = 8 := by
  have := IsCyclotomicExtension.isAbelianGalois {8} ℚ F
  rw [← multiplicity_relDiscr_eq_finsum_exponent_abelianConductor M v,
    multiplicity_relDiscr_cyclotomic_eight F hv]

/-- **Maximum of character `2`-exponents for `ℚ(ζ₈)/ℚ`**: `max(0, 2, 3, 3) = 3`. -/
theorem iSup_exponent_abelianConductor_cyclotomic_eight (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = 2) :
    (⨆ χ : Gal(F/ℚ) →* Mˣ, (abelianConductor ℚ (fixedField χ.ker)).exponent v) = 3 := by
  have := IsCyclotomicExtension.isAbelianGalois {8} ℚ F
  rw [← exponent_abelianConductor_eq_iSup_fixedField_ker ℚ F M v,
    abelianConductor_cyclotomic_eq_ratModulus 8 F (by norm_num) (by decide),
    ratModulus_exponent, hv, show (8 : ℕ) = 2 ^ 3 by norm_num,
    multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 3]

/-- **Product versus least common multiple in `ℚ(ζ₈)/ℚ`.** The product of the finite parts of the
character conductors has absolute norm `256` (the discriminant norm), whereas the finite part of
`abelianConductor ℚ ℚ(ζ₈)` (their least common multiple) has absolute norm `8`. -/
theorem absNorm_finprod_finitePart_abelianConductor_cyclotomic_eight (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] :
    Ideal.absNorm (∏ᶠ χ : Gal(F/ℚ) →* Mˣ, (abelianConductor ℚ (fixedField χ.ker)).finitePart) =
      256 ∧ Ideal.absNorm (abelianConductor ℚ F).finitePart = 8 := by
  have := IsCyclotomicExtension.isAbelianGalois {8} ℚ F
  rw [← relDiscr_eq_finprod_finitePart_abelianConductor M, absNorm_relDiscr_cyclotomic_eight F,
    abelianConductor_cyclotomic_eq_ratModulus 8 F (by norm_num) (by decide),
    ratModulus_finitePart, Rat.RingOfIntegers.absNorm_span_natCast]
  exact ⟨rfl, rfl⟩

end CyclotomicEight

/-! ### Check 3: Prime cyclotomic fields `ℚ(ζ_p)` -/

section CyclotomicPrime

variable (p : ℕ) [hp : Fact p.Prime] (F : Type) [Field F] [NumberField F]
  [IsCyclotomicExtension {p} ℚ F]

/-- **Every nontrivial subfield of `ℚ(ζ_p)` has finite conductor norm `p`.** For any proper
subgroup `H ≠ ⊤` of `Gal(ℚ(ζ_p)/ℚ)`, the finite part of `abelianConductor ℚ (fixedField H)` has
absolute norm `p`. -/
theorem absNorm_abelianConductor_finitePart_fixedField_cyclotomic_prime
    {H : Subgroup Gal(F/ℚ)} (hH : H ≠ ⊤) :
    Ideal.absNorm (abelianConductor ℚ (fixedField H)).finitePart = p := by
  have := IsCyclotomicExtension.isAbelianGalois {p} ℚ F
  have := IsAbelianGalois.tower_bot ℚ (fixedField H) F
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hdvd : Ideal.absNorm (abelianConductor ℚ (fixedField H)).finitePart ∣ p :=
    (nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd (fixedField H) p F).mp
      ⟨(fixedField H).val⟩
  rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | hp'
  · exfalso
    obtain ⟨φ⟩ := (nonempty_algHom_cyclotomicField_iff (fixedField H) 1).mpr (h1 ▸ dvd_rfl)
    have : IsCyclotomicExtension {1} ℚ (CyclotomicField 1 ℚ) :=
      CyclotomicField.isCyclotomicExtension 1 ℚ
    have hle : Module.finrank ℚ (fixedField H) ≤ 1 := by
      have := LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) φ.injective
      rwa [IsCyclotomicExtension.finrank (n := 1) (CyclotomicField 1 ℚ)
        (Polynomial.cyclotomic.irreducible_rat one_pos), Nat.totient_one] at this
    have hpos : 0 < Module.finrank ℚ (fixedField H) := Module.finrank_pos
    have hbot : fixedField H = ⊥ := finrank_eq_one_iff.mp (by omega)
    exact hH (by rw [← _root_.IntermediateField.fixingSubgroup_fixedField H, hbot,
      fixingSubgroup_bot])
  · exact hp'

/-- At the prime `v` above `p`, every nontrivial subextension `ℚ(ζ_p)^H` (`H ≠ ⊤`) has conductor
exponent `1`. -/
theorem exponent_abelianConductor_fixedField_cyclotomic_prime {H : Subgroup Gal(F/ℚ)}
    (hH : H ≠ ⊤) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : Ideal.absNorm v.asIdeal = p) :
    (abelianConductor ℚ (fixedField H)).exponent v = 1 := by
  rw [Modulus.exponent_eq_multiplicity, Rat.HeightOneSpectrum.multiplicity_asIdeal,
    absNorm_abelianConductor_finitePart_fixedField_cyclotomic_prime p F hH, hv,
    Nat.multiplicity_self hp.out.one_lt]

/-- **An even nontrivial character of `Gal(ℚ(ζ_p)/ℚ)` has conductor `(p)`.** -/
theorem abelianConductor_fixedField_ker_cyclotomic_prime_of_even {A : Type*} [MulOneClass A]
    {χ : Gal(F/ℚ) →* A} (hχ : χ ≠ 1)
    (heven : χ ((IsCyclotomicExtension.Rat.galEquivZMod p F).symm (-1)) = 1) :
    abelianConductor ℚ (fixedField χ.ker) = ratFiniteModulus p hp.out.ne_zero := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have := IsCyclotomicExtension.isAbelianGalois {p} ℚ F
  have := IsAbelianGalois.tower_bot ℚ (fixedField χ.ker) F
  rw [abelianConductor_rat_eq_ratFiniteModulus_iff]
  exact ⟨absNorm_abelianConductor_finitePart_fixedField_cyclotomic_prime p F
    (ker_ne_top_of_ne_one hχ), (isTotallyReal_fixedField_ker_iff p F χ).mpr heven⟩

/-- **An odd character of `Gal(ℚ(ζ_p)/ℚ)` has conductor `(p)·∞`.** (Oddness implies `χ ≠ 1`.) -/
theorem abelianConductor_fixedField_ker_cyclotomic_prime_of_odd {A : Type*} [MulOneClass A]
    {χ : Gal(F/ℚ) →* A}
    (hodd : χ ((IsCyclotomicExtension.Rat.galEquivZMod p F).symm (-1)) ≠ 1) :
    abelianConductor ℚ (fixedField χ.ker) = ratModulus p hp.out.ne_zero := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have := IsCyclotomicExtension.isAbelianGalois {p} ℚ F
  have := IsAbelianGalois.tower_bot ℚ (fixedField χ.ker) F
  have hχ : χ ≠ 1 := fun h ↦ hodd (by simp [h])
  rw [abelianConductor_rat_eq_ratModulus_iff]
  exact ⟨absNorm_abelianConductor_finitePart_fixedField_cyclotomic_prime p F
    (ker_ne_top_of_ne_one hχ), (isTotallyReal_fixedField_ker_iff p F χ).not.mpr hodd⟩

/-- At the prime `v` above `p`, `relDiscr (𝓞 ℚ) (𝓞 ℚ(ζ_p))` has multiplicity `p - 2`. -/
theorem multiplicity_relDiscr_cyclotomic_prime {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = p) :
    multiplicity v.asIdeal (relDiscr (𝓞 ℚ) (𝓞 F)) = p - 2 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [TauCeti.NumberField.multiplicity_relDiscr_ringOfIntegers_rat,
    IsCyclotomicExtension.Rat.discr_prime p F, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg,
    Int.natAbs_one, one_pow, one_mul, Int.natAbs_pow, Int.natAbs_natCast, hv,
    multiplicity_pow_self_of_prime (Nat.prime_iff.mp hp.out) (p - 2)]

/-- **Conductor–discriminant sum for `ℚ(ζ_p)/ℚ`.** At the prime `v` above `p`, the `p - 2`
nontrivial characters of `Gal(ℚ(ζ_p)/ℚ)` each contribute exponent `1` and the trivial character
contributes `0`, summing to `p - 2 = multiplicity v (relDiscr (𝓞 ℚ) (𝓞 ℚ(ζ_p)))`. -/
theorem finsum_exponent_abelianConductor_cyclotomic_prime (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = p) :
    (∑ᶠ χ : Gal(F/ℚ) →* Mˣ, (abelianConductor ℚ (fixedField χ.ker)).exponent v) = p - 2 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have := IsCyclotomicExtension.isAbelianGalois {p} ℚ F
  rw [← multiplicity_relDiscr_eq_finsum_exponent_abelianConductor M v,
    multiplicity_relDiscr_cyclotomic_prime p F hv]

/-- **Character-conductor maximum for `ℚ(ζ_p)/ℚ` (`p` an odd prime).** At the prime `v` above an
odd prime `p`, the supremum of the character conductor exponents is `1`. -/
theorem iSup_exponent_abelianConductor_cyclotomic_prime (hp2 : p ≠ 2) (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(F/ℚ))] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : Ideal.absNorm v.asIdeal = p) :
    (⨆ χ : Gal(F/ℚ) →* Mˣ, (abelianConductor ℚ (fixedField χ.ker)).exponent v) = 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have := IsCyclotomicExtension.isAbelianGalois {p} ℚ F
  have hp_gt : 2 < p := lt_of_le_of_ne hp.out.two_le hp2.symm
  have hp4 : p % 4 ≠ 2 := fun h4 ↦ hp2 <| (hp.out.eq_one_or_self_of_dvd 2 ⟨p / 2, by omega⟩
    ).resolve_left (by norm_num) |>.symm
  rw [← exponent_abelianConductor_eq_iSup_fixedField_ker ℚ F M v,
    abelianConductor_cyclotomic_eq_ratModulus p F hp_gt hp4, ratModulus_exponent, hv,
    Nat.multiplicity_self hp.out.one_lt]

end CyclotomicPrime

end TauCeti.ClassFieldTheory
