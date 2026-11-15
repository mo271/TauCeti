/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion

import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
import TauCeti.RingTheory.Nilpotent.BCH

/-!
# The universal Baker–Campbell–Hausdorff element in free nilpotent Lie algebras

Word length equips a free Lie algebra `FreeLieAlgebra R S` over any commutative ring `R` with a
positive grading by `PositiveDegrees.naturals` (`instIsPositiveGradingHomogeneousSubmodule`). Its
degree ideals are Mathlib's zero-based lower central series ideals
(`naturals_degreeIdeal_eq_lowerCentralSeries`), and the associated positive-degree filtration on
the universal enveloping algebra `U(FreeLieAlgebra R S)` coincides with the filtration by powers of
the augmentation ideal (`positiveDegreeFiltration_eq_augmentation_pow`).

Over a commutative rational algebra `R : Type`, the canonical map embeds the free nilpotent Lie
algebra `FreeLieAlgebra R S ⧸ lowerCentralSeries c` into the truncated enveloping algebra
(`comap_augmentation_pow_ι_of_ratAlgebra`, `lowerCentralQuotientι_injective_of_ratAlgebra`), with
no basis construction on the free Lie algebra.

Over `ℚ`, the word-length completion of `FreeLieAlgebra ℚ S` carries the Baker–Campbell–Hausdorff
binary operation `completedBCH`, characterized by
`completedLieToU (completedBCH ξ η) = completedLog (completedExp u * completedExp v)`. At each
nilpotency class `c`, the free nilpotent quotient `FreeLieAlgebra ℚ S ⧸ lowerCentralSeries c`
carries the induced operation `bchQuotient c`, uniquely characterized by
`lowerCentralQuotientι (bchQuotient c z w) = log (exp (ι_c z) * exp (ι_c w))` and equivalently by
`exp (lowerCentralQuotientι (bchQuotient c z w)) = exp (ι_c z) * exp (ι_c w)`.

Evaluating `bchQuotient c` on the two canonical generators of `FreeLieAlgebra ℚ (Fin 2)` defines
the universal Baker–Campbell–Hausdorff element `bchElement c` (`exists_bch_exp_mul_exp`). Pushing
`bchElement c` forward along `FreeLieAlgebra.lift ℚ v` into any rational Lie algebra `L` gives a
class in `L ⧸ lowerCentralSeries c` whose nilpotent exponential in `U(L) ⧸ U⁺(L) ^ (c + 1)` equals
`exp (ι_c (v 0)) * exp (ι_c (v 1))` (`exp_lowerCentralQuotientι_mapQ_lift_bchElement`). Through
degree three, `bchElement 3` is the quotient class of
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)` (`bchElement_three`).

## Main definitions

* `TauCeti.FreeLieAlgebra.completedBCH`: the Baker–Campbell–Hausdorff operation on the word-length
  completion of `FreeLieAlgebra ℚ S`.
* `TauCeti.FreeLieAlgebra.bchQuotient`: the Baker–Campbell–Hausdorff operation on the class-`c`
  nilpotent quotient `FreeLieAlgebra ℚ S ⧸ lowerCentralSeries c`.
* `TauCeti.FreeLieAlgebra.bchElement`: the universal Baker–Campbell–Hausdorff element in
  `FreeLieAlgebra ℚ (Fin 2) ⧸ lowerCentralSeries c`.

## Main results

* `TauCeti.FreeLieAlgebra.comap_augmentation_pow_ι_of_ratAlgebra` and
  `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_injective_of_ratAlgebra`: over a commutative
  `ℚ`-algebra `R : Type`, `lowerCentralQuotientι` embeds the free nilpotent quotient into
  `U(F) ⧸ U⁺(F) ^ (c + 1)`.
* `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchQuotient` and
  `TauCeti.FreeLieAlgebra.eq_bchQuotient_iff_exp`: existence and uniqueness of `bchQuotient`.
* `TauCeti.FreeLieAlgebra.bchQuotient_assoc`, `TauCeti.FreeLieAlgebra.bchQuotient_zero_left`,
  `TauCeti.FreeLieAlgebra.bchQuotient_neg_left`, and
  `TauCeti.FreeLieAlgebra.bchQuotient_of_lie_eq_zero`: group-law and commuting identities on
  `bchQuotient`.
* `TauCeti.FreeLieAlgebra.factor_bchElement`,
  `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_mapQ_lift_bchElement`,
  `TauCeti.FreeLieAlgebra.exists_bch_exp_mul_exp`, and `TauCeti.FreeLieAlgebra.bchElement_three`:
  tower compatibility, universal evaluation, representative existence, and the degree-three formula
  for `bchElement`.

## References

Formal dependencies:
`TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`,
`TauCeti.AlgFiltration.isCompletedPrimitive_completedLog_completedExp_mul`,
`TauCeti.FreeLieAlgebra.degreeFiltration_eq_augmentation_pow`, and
`Ideal.log_exp_mul_exp_of_pow_four_eq_bot`.

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6, for the Campbell–Hausdorff series in
  the completed enveloping algebra of a free Lie algebra.
* C. Reutenauer, *Free Lie Algebras*, Oxford University Press (1993), Chapter 3.
-/

public section

namespace TauCeti.FreeLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section WordLengthGrading

/-- Word length is a positive grading of `FreeLieAlgebra R S` over any commutative ring `R`. -/
instance instIsPositiveGradingHomogeneousSubmodule (R S : Type*) [CommRing R] :
    IsPositiveGrading PositiveDegrees.naturals (homogeneousSubmodule R S) where
  eq_bot n hn := by
    rcases hn with hn | rfl
    · simp at hn
    · exact homogeneousSubmodule_zero R S

/-- For the word-length grading of `FreeLieAlgebra R S`, the degree ideal above order `c` is
Mathlib's zero-based `c`-th lower central series ideal. -/
theorem naturals_degreeIdeal_eq_lowerCentralSeries
    (R S : Type*) [CommRing R] (c : ℕ) :
    PositiveDegrees.naturals.degreeIdeal (homogeneousSubmodule R S) c =
      LieModule.lowerCentralSeries R (_root_.FreeLieAlgebra R S)
        (_root_.FreeLieAlgebra R S) c := by
  apply LieSubmodule.toSubmodule_injective
  rw [PositiveDegrees.naturals.degreeIdeal_toSubmodule,
    PositiveDegrees.naturals.degreeSubmodule_def,
    lowerCentralSeries_toSubmodule_eq_iSup, iSup_subtype]
  refine iSup_congr fun n => iSup_congr_Prop ?_ fun _ => rfl
  simp only [PositiveDegrees.naturals_degree, Nat.cast_lt]

/-- For the word-length grading of `FreeLieAlgebra R S`, the positive-degree filtration on
`U(FreeLieAlgebra R S)` coincides with the filtration by powers of the augmentation ideal. -/
theorem positiveDegreeFiltration_eq_augmentation_pow
    (R S : Type*) [CommRing R] (k : ℕ) :
    (UniversalEnvelopingAlgebra.positiveDegreeFiltration
        PositiveDegrees.naturals (homogeneousSubmodule R S)).ideal k =
      (HopfIdeal.augmentation R
        (_root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S))).toIdeal ^ k :=
  UniversalEnvelopingAlgebra.degreeFiltration_eq_augmentation_pow
    (homogeneousSubmodule R S) PositiveDegrees.naturals.degree
    (PositiveDegrees.naturals.eq_bot_of_degree_nonpos (homogeneousSubmodule R S))
    (_root_.FreeLieAlgebra.of R) (fun _ => 1) (lieSpan_range_of_eq_top R S)
    (fun s => by simpa using word_mem_homogeneousSubmodule R (FreeMagma.of s))
    (fun _ => by simp) k

end WordLengthGrading

section RationalInjectivity

/-- Over a commutative rational algebra `R : Type`, the Lie elements of `FreeLieAlgebra R S` sent
by `ι R` into the `(c + 1)`-st power of the augmentation ideal are precisely the `c`-th term of
the lower central series. -/
theorem comap_augmentation_pow_ι_of_ratAlgebra
    (R : Type) [CommRing R] [Algebra ℚ R] (S : Type*) (c : ℕ) :
    (((HopfIdeal.augmentation R
          (_root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S))).toIdeal ^
        (c + 1)).restrictScalars R).comap
        (_root_.UniversalEnvelopingAlgebra.ι R :
          _root_.FreeLieAlgebra R S →ₗ⁅R⁆
            _root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S)).toLinearMap =
      (LieModule.lowerCentralSeries R (_root_.FreeLieAlgebra R S)
        (_root_.FreeLieAlgebra R S) c).toSubmodule :=
  comap_augmentation_pow_ι R S
    (fun _ _ h =>
      (UniversalEnvelopingAlgebra.primitiveEquiv R (_root_.FreeLieAlgebra R S)).injective <|
        Subtype.ext <| by
          simpa only [UniversalEnvelopingAlgebra.coe_primitiveEquiv_apply] using h)
    c

/-- Over a commutative rational algebra `R : Type`, the canonical map embeds the class-`c` free
nilpotent quotient into the truncated universal enveloping algebra `U(F) ⧸ U⁺(F) ^ (c + 1)`. -/
theorem lowerCentralQuotientι_injective_of_ratAlgebra
    (R : Type) [CommRing R] [Algebra ℚ R] (S : Type*) (c : ℕ) :
    Function.Injective
      (UniversalEnvelopingAlgebra.lowerCentralQuotientι R (_root_.FreeLieAlgebra R S) c) :=
  (UniversalEnvelopingAlgebra.lowerCentralQuotientι_injective_iff R
      (_root_.FreeLieAlgebra R S) c).mpr
    (comap_augmentation_pow_ι_of_ratAlgebra R S c).le

end RationalInjectivity

section CompletedBCH

variable {S : Type*}

local notation "ℒ" => homogeneousSubmodule ℚ S
local notation "𝓕" =>
  UniversalEnvelopingAlgebra.positiveDegreeFiltration PositiveDegrees.naturals ℒ
local notation "ι̂" =>
  UniversalEnvelopingAlgebra.completedLieToU PositiveDegrees.naturals ℒ
local notation "ι̂_mem" =>
  UniversalEnvelopingAlgebra.completedLieToU_mem_completionIdeal_one PositiveDegrees.naturals ℒ

/-- The Baker–Campbell–Hausdorff binary operation on the word-length completion of
`FreeLieAlgebra ℚ S`: the unique completed Lie element whose image in the completed universal
enveloping algebra is `completedLog (completedExp (ι̂ ξ) * completedExp (ι̂ η))`. -/
noncomputable def completedBCH
    (ξ η : PositiveDegrees.naturals.completedLie ℒ) :
    PositiveDegrees.naturals.completedLie ℒ :=
  let hcomul :=
    UniversalEnvelopingAlgebra.positiveDegreeFiltration_ideal_le_comap_comul
      PositiveDegrees.naturals ℒ
  let u : (𝓕).completionIdeal 1 := ⟨ι̂ ξ, ι̂_mem ξ⟩
  let v : (𝓕).completionIdeal 1 := ⟨ι̂ η, ι̂_mem η⟩
  (UniversalEnvelopingAlgebra.completedPrimitiveEquiv PositiveDegrees.naturals ℒ).symm
    ⟨(𝓕).completedLog ⟨(𝓕).completedExp u * (𝓕).completedExp v,
        (𝓕).completedExp_mul_completedExp_sub_one_mem u v⟩,
      ((𝓕).mem_completedPrimitiveSubmodule ℚ hcomul _).mpr
        ((𝓕).isCompletedPrimitive_completedLog_completedExp_mul ℚ hcomul
          (UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU
            PositiveDegrees.naturals ℒ ξ)
          (UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU
            PositiveDegrees.naturals ℒ η))⟩

/-- `completedLieToU` maps `completedBCH ξ η` to `completedLog` of the product of the completed
exponentials of `ξ` and `η`. -/
@[simp]
theorem completedLieToU_completedBCH
    (ξ η : PositiveDegrees.naturals.completedLie ℒ) :
    ι̂ (completedBCH ξ η) =
      (𝓕).completedLog
        ⟨(𝓕).completedExp ⟨ι̂ ξ, ι̂_mem ξ⟩ * (𝓕).completedExp ⟨ι̂ η, ι̂_mem η⟩,
          AlgFiltration.completedExp_mul_completedExp_sub_one_mem _ _ _⟩ :=
  UniversalEnvelopingAlgebra.completedLieToU_completedPrimitiveEquiv_symm
    PositiveDegrees.naturals ℒ _

/-- The completed exponential of `completedLieToU (completedBCH ξ η)` is the product of the
completed exponentials of `completedLieToU ξ` and `completedLieToU η`. -/
theorem completedExp_completedLieToU_completedBCH
    (ξ η : PositiveDegrees.naturals.completedLie ℒ) :
    (𝓕).completedExp ⟨ι̂ (completedBCH ξ η), ι̂_mem (completedBCH ξ η)⟩ =
      (𝓕).completedExp ⟨ι̂ ξ, ι̂_mem ξ⟩ * (𝓕).completedExp ⟨ι̂ η, ι̂_mem η⟩ := by
  have hsub :
      (⟨ι̂ (completedBCH ξ η), ι̂_mem (completedBCH ξ η)⟩ : (𝓕).completionIdeal 1) =
        ⟨(𝓕).completedLog _, (𝓕).completedLog_mem _⟩ :=
    Subtype.ext (completedLieToU_completedBCH ξ η)
  rw [hsub, (𝓕).completedExp_completedLog]

end CompletedBCH

section QuotientBCH

variable {S : Type*}

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U)
local notation "γ" => LieModule.lowerCentralSeries ℚ F F
local notation "ℒ" => homogeneousSubmodule ℚ S

private theorem map_quotient_augmentation_pow_eq_bot (c : ℕ) :
    (((J).map (Ideal.Quotient.mk (J ^ (c + 1)))) ^ (c + 1)) = ⊥ := by
  let π := Ideal.Quotient.mk (J ^ (c + 1))
  have hpow : ∀ n : ℕ, ((J).map π) ^ (n + 1) ≤ (J ^ (n + 1)).map π := by
    intro n
    induction n with
    | zero => simp only [zero_add, Submodule.pow_one, le_rfl]
    | succ n ih =>
      refine (Submodule.pow_succ ((J).map π)).le.trans (Submodule.mul_le.mpr ?_)
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).mp (ih hx)
      obtain ⟨b, hb, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).mp hy
      have hab : a * b ∈ J ^ (n + 1 + 1) :=
        Submodule.pow_succ J ▸ Ideal.mul_mem_mul ha hb
      exact map_mul π a b ▸ Ideal.mem_map_of_mem π hab
  exact le_bot_iff.mp ((hpow c).trans (Ideal.map_quotient_self (J ^ (c + 1))).le)

private theorem lowerCentralQuotientι_mem_map_augmentation (c : ℕ) (z : F ⧸ γ c) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z ∈
      (J).map (Ideal.Quotient.mk (J ^ (c + 1))) := by
  obtain ⟨x, rfl⟩ := LieIdeal.surjective_mkQ _ z
  rw [LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
  exact Ideal.mem_map_of_mem _
    (HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F x))

/-- In `U(F) ⧸ U⁺(F) ^ (c + 1)`, the product of the nilpotent exponentials of two elements in the
image of `lowerCentralQuotientι` is unipotent, with `(exp u * exp v - 1) ^ (c + 1) = 0`. -/
theorem isNilpotent_exp_mul_exp_sub_one_lowerCentralQuotientι (c : ℕ) (z w : F ⧸ γ c) :
    IsNilpotent
      (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) *
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c w) - 1) :=
  ⟨c + 1,
    Ideal.exp_mul_exp_sub_one_pow_eq_zero _
      (map_quotient_augmentation_pow_eq_bot c)
      (lowerCentralQuotientι_mem_map_augmentation c z)
      (lowerCentralQuotientι_mem_map_augmentation c w)⟩

private theorem exp_quotient_mk_of_completionProjection_completedBCH (c : ℕ) (x y b : F)
    (hb : (PositiveDegrees.naturals.degreeIdeal ℒ c).mkQ b =
      LieIdeal.completionProjection
        (PositiveDegrees.naturals.degreeIdeal ℒ)
        (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) c
        (completedBCH
          (LieIdeal.toCompletion
            (PositiveDegrees.naturals.degreeIdeal ℒ)
            (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) x)
          (LieIdeal.toCompletion
            (PositiveDegrees.naturals.degreeIdeal ℒ)
            (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) y))) :
    IsNilpotent.exp
        (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
      IsNilpotent.exp
          (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
        IsNilpotent.exp
          (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) := by
  let d := PositiveDegrees.naturals
  let 𝓕 := UniversalEnvelopingAlgebra.positiveDegreeFiltration d ℒ
  let ξ : d.completedLie ℒ :=
    LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x
  let η : d.completedLie ℒ :=
    LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) y
  have hproj := congrArg (𝓕.projection c) (completedExp_completedLieToU_completedBCH ξ η)
  rw [map_mul, 𝓕.projection_completedExp, 𝓕.projection_completedExp,
    𝓕.projection_completedExp, UniversalEnvelopingAlgebra.projection_completedLieToU,
    ← hb, LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.truncatedLieToU_mk] at hproj
  have hξ : 𝓕.projection c (UniversalEnvelopingAlgebra.completedLieToU d ℒ ξ) =
      Ideal.Quotient.mk (𝓕.ideal (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
    rw [UniversalEnvelopingAlgebra.completedLieToU_toCompletion, 𝓕.projection_toCompletion]
  have hη : 𝓕.projection c (UniversalEnvelopingAlgebra.completedLieToU d ℒ η) =
      Ideal.Quotient.mk (𝓕.ideal (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ y) := by
    rw [UniversalEnvelopingAlgebra.completedLieToU_toCompletion, 𝓕.projection_toCompletion]
  rw [hξ, hη] at hproj
  have hnil (w : F) :
      IsNilpotent (Ideal.Quotient.mk (𝓕.ideal (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) := by
    refine ⟨c + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      positiveDegreeFiltration_eq_augmentation_pow]
    exact Ideal.pow_mem_pow
      (HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F w)) _
  let e := Ideal.quotEquivOfEq (positiveDegreeFiltration_eq_augmentation_pow ℚ S (c + 1))
  have hmap := congrArg e hproj
  rw [(hnil b).map_exp e, map_mul, (hnil x).map_exp e, (hnil y).map_exp e,
    Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk] at hmap
  exact hmap

/-- For any `x, y : FreeLieAlgebra ℚ S` and `c : ℕ`, there exists `b : FreeLieAlgebra ℚ S` whose
nilpotent exponential in `U(F) ⧸ U⁺(F) ^ (c + 1)` equals the product of the exponentials of `x`
and `y`. -/
theorem exists_exp_quotient_eq_exp_mul_exp (c : ℕ) (x y : F) :
    ∃ b : F,
      IsNilpotent.exp
          (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp
            (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) := by
  let d := PositiveDegrees.naturals
  obtain ⟨b, hb⟩ := (d.degreeIdeal ℒ c).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) c
      (completedBCH
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x)
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) y)))
  exact ⟨b, exp_quotient_mk_of_completionProjection_completedBCH c x y b hb⟩

/-- In the truncated enveloping algebra `U(FreeLieAlgebra ℚ S) ⧸ U⁺ ^ (c + 1)`, the finite
logarithm `log (exp (ι_c z) * exp (ι_c w))` lies in the image of `lowerCentralQuotientι`. -/
theorem exists_lowerCentralQuotientι_eq_log (c : ℕ) (z w : F ⧸ γ c) :
    ∃ q : F ⧸ γ c,
      UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c q =
        IsNilpotent.log
          (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) *
            IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c w)) := by
  obtain ⟨x, rfl⟩ := LieIdeal.surjective_mkQ _ z
  obtain ⟨y, rfl⟩ := LieIdeal.surjective_mkQ _ w
  obtain ⟨b, hb⟩ := exists_exp_quotient_eq_exp_mul_exp c x y
  refine ⟨LieSubmodule.Quotient.mk b, ?_⟩
  have hb' :
      IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (LieSubmodule.Quotient.mk b)) =
        IsNilpotent.exp
            (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (LieIdeal.mkQ _ x)) *
          IsNilpotent.exp
            (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (LieIdeal.mkQ _ y)) := by
    simpa only [LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using hb
  rw [← hb',
    IsNilpotent.log_exp
      (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c
        (LieSubmodule.Quotient.mk b))]

/-- The Baker–Campbell–Hausdorff operation on the class-`c` free nilpotent Lie algebra
`FreeLieAlgebra ℚ S ⧸ lowerCentralSeries c`: the unique class whose image in
`U(F) ⧸ U⁺(F) ^ (c + 1)` is `log (exp (ι_c z) * exp (ι_c w))`. -/
noncomputable def bchQuotient (c : ℕ) (z w : F ⧸ γ c) : F ⧸ γ c :=
  Classical.choose (exists_lowerCentralQuotientι_eq_log c z w)

/-- `lowerCentralQuotientι` maps `bchQuotient c z w` to `log (exp (ι_c z) * exp (ι_c w))`. -/
@[simp]
theorem lowerCentralQuotientι_bchQuotient (c : ℕ) (z w : F ⧸ γ c) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (bchQuotient c z w) =
      IsNilpotent.log
        (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) *
          IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c w)) :=
  Classical.choose_spec (exists_lowerCentralQuotientι_eq_log c z w)

/-- Exponentiating `lowerCentralQuotientι (bchQuotient c z w)` recovers the product of the
exponentials of `lowerCentralQuotientι z` and `lowerCentralQuotientι w`. -/
theorem exp_lowerCentralQuotientι_bchQuotient (c : ℕ) (z w : F ⧸ γ c) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (bchQuotient c z w)) =
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) *
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c w) := by
  rw [lowerCentralQuotientι_bchQuotient,
    IsNilpotent.exp_log (isNilpotent_exp_mul_exp_sub_one_lowerCentralQuotientι c z w)]

/-- Uniqueness characterization of `bchQuotient` in terms of `IsNilpotent.log`. -/
theorem eq_bchQuotient_iff (c : ℕ) (q z w : F ⧸ γ c) :
    q = bchQuotient c z w ↔
      UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c q =
        IsNilpotent.log
          (IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) *
            IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c w)) := by
  refine ⟨fun h => h ▸ lowerCentralQuotientι_bchQuotient c z w, fun h => ?_⟩
  apply lowerCentralQuotientι_injective_of_ratAlgebra ℚ S c
  rw [h, lowerCentralQuotientι_bchQuotient]

/-- Uniqueness characterization of `bchQuotient` in terms of `IsNilpotent.exp`. -/
theorem eq_bchQuotient_iff_exp (c : ℕ) (q z w : F ⧸ γ c) :
    q = bchQuotient c z w ↔
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c q) =
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) *
          IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c w) := by
  refine ⟨fun h => h ▸ exp_lowerCentralQuotientι_bchQuotient c z w, fun h => ?_⟩
  rw [eq_bchQuotient_iff, ← h,
    IsNilpotent.log_exp (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c q)]

/-- Under the canonical identification of `PositiveDegrees.naturals.degreeIdeal` with
`lowerCentralSeries`, the order-`c` projection of `completedBCH` on two Lie elements is
`bchQuotient c` of their quotient classes. -/
theorem quotEquivOfEq_completionProjection_completedBCH (c : ℕ) (x y : F) :
    (PositiveDegrees.naturals.degreeIdeal ℒ c).quotEquivOfEq (γ c)
        (naturals_degreeIdeal_eq_lowerCentralSeries ℚ S c)
        (LieIdeal.completionProjection
          (PositiveDegrees.naturals.degreeIdeal ℒ)
          (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) c
          (completedBCH
            (LieIdeal.toCompletion
              (PositiveDegrees.naturals.degreeIdeal ℒ)
              (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) x)
            (LieIdeal.toCompletion
              (PositiveDegrees.naturals.degreeIdeal ℒ)
              (PositiveDegrees.naturals.degreeIdeal_antitone ℒ) y))) =
      bchQuotient c (LieSubmodule.Quotient.mk x) (LieSubmodule.Quotient.mk y) := by
  let d := PositiveDegrees.naturals
  obtain ⟨b, hb⟩ := (d.degreeIdeal ℒ c).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) c
      (completedBCH
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x)
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) y)))
  rw [← hb, LieIdeal.mkQ_apply, LieIdeal.quotEquivOfEq_mk, eq_bchQuotient_iff_exp]
  simpa only [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    exp_quotient_mk_of_completionProjection_completedBCH c x y b hb

/-- `0` is a left identity for `bchQuotient`. -/
@[simp]
theorem bchQuotient_zero_left (c : ℕ) (z : F ⧸ γ c) :
    bchQuotient c 0 z = z := by
  symm
  rw [eq_bchQuotient_iff_exp, map_zero, IsNilpotent.exp_zero, one_mul]

/-- `0` is a right identity for `bchQuotient`. -/
@[simp]
theorem bchQuotient_zero_right (c : ℕ) (z : F ⧸ γ c) :
    bchQuotient c z 0 = z := by
  symm
  rw [eq_bchQuotient_iff_exp, map_zero, IsNilpotent.exp_zero, mul_one]

/-- `-z` is a left inverse for `z` under `bchQuotient`. -/
@[simp]
theorem bchQuotient_neg_left (c : ℕ) (z : F ⧸ γ c) :
    bchQuotient c (-z) z = 0 := by
  symm
  rw [eq_bchQuotient_iff_exp, map_zero, map_neg, IsNilpotent.exp_zero,
    IsNilpotent.exp_neg_mul_exp_self
      (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z)]

/-- `-z` is a right inverse for `z` under `bchQuotient`. -/
@[simp]
theorem bchQuotient_neg_right (c : ℕ) (z : F ⧸ γ c) :
    bchQuotient c z (-z) = 0 := by
  symm
  rw [eq_bchQuotient_iff_exp, map_zero, map_neg, IsNilpotent.exp_zero,
    IsNilpotent.exp_mul_exp_neg_self
      (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z)]

/-- `bchQuotient` is associative. -/
theorem bchQuotient_assoc (c : ℕ) (u v w : F ⧸ γ c) :
    bchQuotient c (bchQuotient c u v) w = bchQuotient c u (bchQuotient c v w) := by
  rw [eq_bchQuotient_iff_exp, exp_lowerCentralQuotientι_bchQuotient,
    exp_lowerCentralQuotientι_bchQuotient, exp_lowerCentralQuotientι_bchQuotient, mul_assoc]

/-- On commuting elements of the nilpotent quotient (`⁅z, w⁆ = 0`), `bchQuotient` reduces to
addition. -/
theorem bchQuotient_of_lie_eq_zero (c : ℕ) {z w : F ⧸ γ c} (hzw : ⁅z, w⁆ = 0) :
    bchQuotient c z w = z + w := by
  symm
  rw [eq_bchQuotient_iff_exp, map_add]
  have hlie := congrArg (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c) hzw
  rw [LieHom.map_lie, map_zero, LieRing.of_associative_ring_bracket, sub_eq_zero] at hlie
  exact IsNilpotent.exp_add_of_commute hlie
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z)
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c w)

/-- `bchQuotient` commutes with the lower-central-series quotient transitions across `c ≤ d`. -/
theorem factor_bchQuotient {c d : ℕ} (h : c ≤ d) (z w : F ⧸ γ d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) (bchQuotient d z w) =
      bchQuotient c
        (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) z)
        (LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F F h) w) := by
  let φ := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := J) (Nat.add_le_add_right h 1))
  rw [eq_bchQuotient_iff_exp, UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F h,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F h,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F h]
  rw [← (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F d
      (bchQuotient d z w)).map_exp φ,
    exp_lowerCentralQuotientι_bchQuotient, map_mul,
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F d z).map_exp φ,
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F d w).map_exp φ]

/-- Along any `ℚ`-Lie homomorphism `f : FreeLieAlgebra ℚ S →ₗ⁅ℚ⁆ L` into an arbitrary rational
Lie algebra `L`, the induced map on class-`c` quotients sends `bchQuotient c z w` to a class whose
nilpotent exponential in `U(L) ⧸ U⁺(L) ^ (c + 1)` equals the product of the exponentials of the
images of `z` and `w`. -/
theorem exp_lowerCentralQuotientι_mapQ_bchQuotient {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : F →ₗ⁅ℚ⁆ L) (c : ℕ)
    (hf : γ c ≤ LieIdeal.comap f (LieModule.lowerCentralSeries ℚ L L c) :=
      LieIdeal.map_le_iff_le_comap.mp (LieIdeal.map_lowerCentralSeries_le c))
    (z w : F ⧸ γ c) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c
          (LieIdeal.mapQ (γ c) (LieModule.lowerCentralSeries ℚ L L c) f hf
            (bchQuotient c z w))) =
      IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c
            (LieIdeal.mapQ (γ c) (LieModule.lowerCentralSeries ℚ L L c) f hf z)) *
        IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c
            (LieIdeal.mapQ (γ c) (LieModule.lowerCentralSeries ℚ L L c) f hf w)) := by
  have haug :
      J ≤ (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ L)).toIdeal.comap
        (UniversalEnvelopingAlgebra.map ℚ f).toRingHom := by
    rw [UniversalEnvelopingAlgebra.augmentation_toIdeal_eq_span_range_ι, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      UniversalEnvelopingAlgebra.map_ι]
    exact HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ L (f x))
  have hpow : ∀ n : ℕ,
      J ^ n ≤
        ((HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ L)).toIdeal ^ n).comap
          (UniversalEnvelopingAlgebra.map ℚ f).toRingHom := by
    intro n
    induction n with
    | zero =>
      rw [Submodule.pow_zero, Submodule.pow_zero, Ideal.one_eq_top, Ideal.one_eq_top]
      exact le_rfl
    | succ n ih =>
      rw [Submodule.pow_succ, Submodule.mul_le]
      intro x hx y hy
      rw [Ideal.mem_comap, map_mul, Submodule.pow_succ]
      exact Ideal.mul_mem_mul (ih hx) (haug hy)
  let φ := Ideal.quotientMap
    ((HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ L)).toIdeal ^ (c + 1))
    (UniversalEnvelopingAlgebra.map ℚ f).toRingHom (hpow (c + 1))
  have hcomm (q : F ⧸ γ c) :
      UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c
          (LieIdeal.mapQ (γ c) (LieModule.lowerCentralSeries ℚ L L c) f hf q) =
        φ (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c q) := by
    obtain ⟨x, rfl⟩ := LieIdeal.surjective_mkQ _ q
    rw [LieIdeal.mkQ_apply, LieIdeal.mapQ_apply,
      UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk,
      UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
    dsimp only [φ]
    rw [Ideal.quotientMap_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      UniversalEnvelopingAlgebra.map_ι]
  rw [hcomm (bchQuotient c z w), hcomm z, hcomm w,
    ← (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c
        (bchQuotient c z w)).map_exp φ,
    exp_lowerCentralQuotientι_bchQuotient, map_mul,
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z).map_exp φ,
    (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c w).map_exp φ]

/-- Functoriality of `bchQuotient` along any `ℚ`-Lie homomorphism between free Lie algebras. -/
theorem mapQ_bchQuotient {S₂ : Type*}
    (f : F →ₗ⁅ℚ⁆ _root_.FreeLieAlgebra ℚ S₂) (c : ℕ)
    (hf : γ c ≤
      LieIdeal.comap f
        (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ S₂)
          (_root_.FreeLieAlgebra ℚ S₂) c) :=
      LieIdeal.map_le_iff_le_comap.mp (LieIdeal.map_lowerCentralSeries_le c))
    (z w : F ⧸ γ c) :
    LieIdeal.mapQ (γ c)
        (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ S₂)
          (_root_.FreeLieAlgebra ℚ S₂) c)
        f hf (bchQuotient c z w) =
      bchQuotient c
        (LieIdeal.mapQ (γ c)
          (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ S₂)
            (_root_.FreeLieAlgebra ℚ S₂) c) f hf z)
        (LieIdeal.mapQ (γ c)
          (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ S₂)
            (_root_.FreeLieAlgebra ℚ S₂) c) f hf w) :=
  (eq_bchQuotient_iff_exp c _ _ _).mpr (exp_lowerCentralQuotientι_mapQ_bchQuotient f c hf z w)

/-- At class `0`, the nilpotent quotient is trivial and `bchQuotient 0 z w = 0`. -/
theorem bchQuotient_zero (z w : F ⧸ γ 0) : bchQuotient 0 z w = 0 := by
  obtain ⟨x, hx⟩ := LieIdeal.surjective_mkQ _ (bchQuotient 0 z w)
  rw [← hx, LieIdeal.mkQ_eq_zero, LieModule.lowerCentralSeries_zero]
  trivial

/-- At class `1`, the nilpotent quotient is abelian and `bchQuotient 1 z w = z + w`. -/
theorem bchQuotient_one (z w : F ⧸ γ 1) : bchQuotient 1 z w = z + w := by
  apply bchQuotient_of_lie_eq_zero
  obtain ⟨x, rfl⟩ := LieIdeal.surjective_mkQ _ z
  obtain ⟨y, rfl⟩ := LieIdeal.surjective_mkQ _ w
  rw [← LieHom.map_lie, LieIdeal.mkQ_eq_zero, LieModule.lowerCentralSeries_succ,
    LieModule.lowerCentralSeries_zero]
  exact LieSubmodule.lie_mem_lie trivial trivial

/-- At class `2`, `bchQuotient 2 z w = z + w + (1 / 2) • ⁅z, w⁆`. -/
theorem bchQuotient_two (z w : F ⧸ γ 2) :
    bchQuotient 2 z w = z + w + (1 / 2 : ℚ) • ⁅z, w⁆ := by
  symm
  rw [eq_bchQuotient_iff]
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot _
      (map_quotient_augmentation_pow_eq_bot 2)
      (lowerCentralQuotientι_mem_map_augmentation 2 z)
      (lowerCentralQuotientι_mem_map_augmentation 2 w)]
  simp only [map_add, _root_.map_smul, LieHom.map_lie]

/-- At class `3`, `bchQuotient 3 z w = z + w + (1 / 2) • ⁅z, w⁆ +
(1 / 12) • (⁅z, ⁅z, w⁆⁆ + ⁅w, ⁅w, z⁆⁆)`. -/
theorem bchQuotient_three (z w : F ⧸ γ 3) :
    bchQuotient 3 z w =
      z + w + (1 / 2 : ℚ) • ⁅z, w⁆ +
        (1 / 12 : ℚ) • (⁅z, ⁅z, w⁆⁆ + ⁅w, ⁅w, z⁆⁆) := by
  symm
  rw [eq_bchQuotient_iff]
  rw [Ideal.log_exp_mul_exp_of_pow_four_eq_bot _
      (map_quotient_augmentation_pow_eq_bot 3)
      (lowerCentralQuotientι_mem_map_augmentation 3 z)
      (lowerCentralQuotientι_mem_map_augmentation 3 w)]
  simp only [map_add, _root_.map_smul, LieHom.map_lie]

end QuotientBCH

section UniversalElement

local notation "F₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "U₂" => _root_.UniversalEnvelopingAlgebra ℚ F₂
local notation "J₂" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U₂)
local notation "γ₂" => LieModule.lowerCentralSeries ℚ F₂ F₂
local notation "X" => _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)
local notation "Y" => _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class at most `c`: the element
of `FreeLieAlgebra ℚ (Fin 2) ⧸ lowerCentralSeries c` combining the two free generators `of ℚ 0`
and `of ℚ 1`. -/
noncomputable def bchElement (c : ℕ) : F₂ ⧸ γ₂ c :=
  bchQuotient c (LieSubmodule.Quotient.mk X) (LieSubmodule.Quotient.mk Y)

/-- The image of `bchElement c` in `U(FreeLieAlgebra ℚ (Fin 2)) ⧸ U⁺ ^ (c + 1)` is the finite
logarithm of `exp (ι 0) * exp (ι 1)` modulo `U⁺ ^ (c + 1)`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c) =
      IsNilpotent.log
        (IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ Y))) := by
  simp only [bchElement, lowerCentralQuotientι_bchQuotient,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]

/-- Exponentiating `lowerCentralQuotientι (bchElement c)` gives the product of the exponentials of
the two canonical generators modulo `U⁺ ^ (c + 1)`. -/
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c)) =
      IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
        IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ Y)) := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    exp_lowerCentralQuotientι_bchQuotient c
      (LieSubmodule.Quotient.mk X) (LieSubmodule.Quotient.mk Y)

/-- Uniqueness characterization of `bchElement c` by its nilpotent exponential in
`U(FreeLieAlgebra ℚ (Fin 2)) ⧸ U⁺ ^ (c + 1)`. -/
theorem eq_bchElement_iff (c : ℕ) (q : F₂ ⧸ γ₂ c) :
    q = bchElement c ↔
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c q) =
        IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ Y)) := by
  simpa only [bchElement, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
    eq_bchQuotient_iff_exp c q (LieSubmodule.Quotient.mk X) (LieSubmodule.Quotient.mk Y)

/-- The universal Baker–Campbell–Hausdorff elements commute with the lower-central-series quotient
transitions across `c ≤ d`. -/
theorem factor_bchElement {c d : ℕ} (h : c ≤ d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F₂ F₂ h) (bchElement d) =
      bchElement c := by
  simpa only [bchElement, LieIdeal.factor_apply] using
    factor_bchQuotient h (LieSubmodule.Quotient.mk X) (LieSubmodule.Quotient.mk Y)

/-- Evaluating `bchElement c` in any rational Lie algebra `L` at `v : Fin 2 → L` via
`FreeLieAlgebra.lift ℚ v` yields a class in `L ⧸ lowerCentralSeries c` whose nilpotent exponential
in `U(L) ⧸ U⁺(L) ^ (c + 1)` equals `exp (ι_c (v 0)) * exp (ι_c (v 1))`. -/
theorem exp_lowerCentralQuotientι_mapQ_lift_bchElement {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (v : Fin 2 → L) (c : ℕ)
    (hv : γ₂ c ≤ LieIdeal.comap (_root_.FreeLieAlgebra.lift ℚ v)
        (LieModule.lowerCentralSeries ℚ L L c) :=
      LieIdeal.map_le_iff_le_comap.mp (LieIdeal.map_lowerCentralSeries_le c)) :
    IsNilpotent.exp
        (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c
          (LieIdeal.mapQ (γ₂ c) (LieModule.lowerCentralSeries ℚ L L c)
            (_root_.FreeLieAlgebra.lift ℚ v) hv (bchElement c))) =
      IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c
            (LieSubmodule.Quotient.mk (v 0))) *
        IsNilpotent.exp
          (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c
            (LieSubmodule.Quotient.mk (v 1))) := by
  simpa only [bchElement, LieIdeal.mapQ_apply, _root_.FreeLieAlgebra.lift_of_apply] using
    exp_lowerCentralQuotientι_mapQ_bchQuotient (_root_.FreeLieAlgebra.lift ℚ v) c hv
      (LieSubmodule.Quotient.mk X) (LieSubmodule.Quotient.mk Y)

/-- Evaluating `bchElement c` at two elements of `FreeLieAlgebra ℚ S` via `FreeLieAlgebra.lift`
recovers `bchQuotient c`. -/
theorem mapQ_lift_bchElement {S : Type*} (v : Fin 2 → _root_.FreeLieAlgebra ℚ S) (c : ℕ)
    (hv : γ₂ c ≤
      LieIdeal.comap (_root_.FreeLieAlgebra.lift ℚ v)
        (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ S)
          (_root_.FreeLieAlgebra ℚ S) c) :=
      LieIdeal.map_le_iff_le_comap.mp (LieIdeal.map_lowerCentralSeries_le c)) :
    LieIdeal.mapQ (γ₂ c)
        (LieModule.lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ S)
          (_root_.FreeLieAlgebra ℚ S) c)
        (_root_.FreeLieAlgebra.lift ℚ v) hv (bchElement c) =
      bchQuotient c (LieSubmodule.Quotient.mk (v 0)) (LieSubmodule.Quotient.mk (v 1)) := by
  simpa only [bchElement, LieIdeal.mapQ_apply, _root_.FreeLieAlgebra.lift_of_apply] using
    mapQ_bchQuotient (_root_.FreeLieAlgebra.lift ℚ v) c hv
      (LieSubmodule.Quotient.mk X) (LieSubmodule.Quotient.mk Y)

/-- Representative existence form of `bchElement`: for every `c : ℕ`, there exists
`b : FreeLieAlgebra ℚ (Fin 2)` such that `exp (ι b) = exp (ι (of 0)) * exp (ι (of 1))` in
`U(FreeLieAlgebra ℚ (Fin 2)) ⧸ U⁺ ^ (c + 1)`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : F₂,
      IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ Y)) :=
  exists_exp_quotient_eq_exp_mul_exp c X Y

/-- At class `0`, `bchElement 0 = 0`. -/
theorem bchElement_zero : bchElement 0 = 0 :=
  bchQuotient_zero _ _

/-- At class `1`, `bchElement 1` is the quotient class of `X + Y`. -/
theorem bchElement_one :
    bchElement 1 = LieSubmodule.Quotient.mk (X + Y) := by
  rw [bchElement, bchQuotient_one]
  simp only [← LieIdeal.mkQ_apply, map_add]

/-- At class `2`, `bchElement 2` is the quotient class of `X + Y + (1 / 2) • ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 = LieSubmodule.Quotient.mk (X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆) := by
  rw [bchElement, bchQuotient_two]
  simp only [← LieIdeal.mkQ_apply, map_add, _root_.map_smul, LieHom.map_lie]

/-- Through degree three (`c = 3`), `bchElement 3` is the quotient class of
`X + Y + (1 / 2) • ⁅X, Y⁆ + (1 / 12) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 =
      LieSubmodule.Quotient.mk
        (X + Y + (1 / 2 : ℚ) • ⁅X, Y⁆ +
          (1 / 12 : ℚ) • (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)) := by
  rw [bchElement, bchQuotient_three]
  simp only [← LieIdeal.mkQ_apply, map_add, _root_.map_smul, LieHom.map_lie]

end UniversalElement

end TauCeti.FreeLieAlgebra
