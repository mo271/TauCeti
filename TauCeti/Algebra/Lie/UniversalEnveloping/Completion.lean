/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Completion
public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.RingTheory.FilteredAlgebra.Bialgebra

import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Completed universal enveloping algebras of positively graded Lie algebras

Let `L` be a graded Lie algebra over a commutative ring `R`. Comultiplication on the universal
enveloping algebra `U(L)` preserves total Lie degree, so for any additive degree `d : Γ →+ ℤ`
with no negative-degree Lie components, `degreeFiltration ℒ d hneg` is compatible with both the
counit and the comultiplication of `U(L)`. Its completion therefore carries the completed counit,
completed comultiplication, and completed primitive and group-like predicates of
`TauCeti.AlgFiltration`.

When `(d, ℒ)` is a positive grading (`IsPositiveGrading d ℒ`), the canonical map `ι R : L → U(L)`
induces finite-order Lie homomorphisms `truncatedLieToU : d.truncatedLie ℒ k →ₗ⁅R⁆ U(L) ⧸ F^{k+1}`
and a completed Lie homomorphism `completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ Û(L)`. Every element in
the image of `completedLieToU` lies in the first completion ideal and is completed primitive over
an arbitrary commutative ring `R`.

Over a commutative rational algebra `R : Type`, homogeneous components of representatives of a
completed primitive element are primitive in `U(L)`
(`isPrimitiveElem_decompose_of_isCompletedPrimitive`), and `completedLieToU` identifies
`d.completedLie ℒ` linearly with the completed primitive submodule of `Û(L)`
(`isCompletedPrimitive_iff_mem_range_completedLieToU` and `completedPrimitiveEquiv`), with no
freeness or finite-rank assumption on `L`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.positiveDegreeFiltration`: the total-degree algebra
  filtration on `U(L)` associated to a positive Lie grading `(d, ℒ)`.
* `TauCeti.UniversalEnvelopingAlgebra.truncatedLieToU`: the finite-order Lie homomorphism
  `d.truncatedLie ℒ k →ₗ⁅R⁆ U(L) ⧸ F^{k+1}`.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieToU`: the completed Lie homomorphism
  `d.completedLie ℒ →ₗ⁅R⁆ Û(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveEquiv`: over a commutative `ℚ`-algebra
  `R : Type`, the linear isomorphism between `d.completedLie ℒ` and the completed primitive
  submodule of `Û(L)`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_ideal_le_comap_comul`: comultiplication
  preserves `degreeFiltration`.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_decompose_of_isCompletedPrimitive`:
  homogeneous components below the cutoff of any representative of a completed primitive element
  are primitive in `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU`: every image of
  `completedLieToU` is completed primitive over any commutative ring `R`.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`: over a
  commutative `ℚ`-algebra `R : Type`, completed primitive elements of `Û(L)` are precisely the
  range of `completedLieToU`.

## References

Formal dependencies: `TauCeti.AlgFiltration.IsCompletedPrimitive`,
`UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι`, and
`DirectSum.IsInternal.tensorProduct`.

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6, for completed enveloping algebras and
  their primitive elements.
* E. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), §8, for the underlying primitive classification over `ℚ`-algebras.
-/

public section

open Opposite
open scoped DirectSum TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section NonnegGrading

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Comultiplication carries each total-degree enveloping piece into the sum of tensor products of
pieces whose degrees add to `n`. -/
theorem comul_mem_iSup_homogeneousSubmodule (n : Γ) {u : U}
    (hu : u ∈ homogeneousSubmodule ℒ n) :
    Coalgebra.comul (R := R) u ∈
      ⨆ (a : Γ) (b : Γ) (_ : a + b = n),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ a) (homogeneousSubmodule ℒ b) := by
  let S : Γ → Submodule R (U ⊗[R] U) := fun m =>
    ⨆ (a : Γ) (b : Γ) (_ : a + b = m),
      Submodule.map₂ (TensorProduct.mk R U U)
        (homogeneousSubmodule ℒ a) (homogeneousSubmodule ℒ b)
  suffices hword : ∀ l : List (Σ i, ℒ i),
      Coalgebra.comul (R := R) (l.map (fun x => ι R (x.2 : L))).prod ∈
        S (l.map Sigma.fst).sum by
    refine ((homogeneousSubmodule_le_iff ℒ n ((S n).comap (Coalgebra.comul (R := R)))).mpr ?_) hu
    intro l hl
    simpa only [Submodule.mem_comap, ← hl] using hword l
  intro l
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def]
    apply Submodule.mem_iSup_of_mem (0 : Γ)
    apply Submodule.mem_iSup_of_mem (0 : Γ)
    rw [iSup_pos (add_zero (0 : Γ))]
    exact Submodule.apply_mem_map₂ _ SetLike.GradedOne.one_mem SetLike.GradedOne.one_mem
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Bialgebra.comul_mul,
      comul_ι, add_mul]
    have hx : ι R (x.2 : L) ∈ homogeneousSubmodule ℒ x.1 :=
      ι_mem_homogeneousSubmodule ℒ x.2.property
    have hleft : S (l.map Sigma.fst).sum ≤
        (S (x.1 + (l.map Sigma.fst).sum)).comap
          (LinearMap.mulLeft R (ι R (x.2 : L) ⊗ₜ[R] (1 : U))) := by
      refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => Submodule.map₂_le.mpr ?_
      intro u₁ hu₁ u₂ hu₂
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      apply Submodule.mem_iSup_of_mem (x.1 + a)
      apply Submodule.mem_iSup_of_mem b
      rw [iSup_pos (by rw [add_assoc, hab])]
      exact Submodule.apply_mem_map₂ _ (SetLike.mul_mem_graded hx hu₁) hu₂
    have hright : S (l.map Sigma.fst).sum ≤
        (S (x.1 + (l.map Sigma.fst).sum)).comap
          (LinearMap.mulLeft R ((1 : U) ⊗ₜ[R] ι R (x.2 : L))) := by
      refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => Submodule.map₂_le.mpr ?_
      intro u₁ hu₁ u₂ hu₂
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      apply Submodule.mem_iSup_of_mem a
      apply Submodule.mem_iSup_of_mem (x.1 + b)
      rw [iSup_pos (by rw [← add_assoc, add_comm a x.1, add_assoc, hab])]
      exact Submodule.apply_mem_map₂ _ hu₁ (SetLike.mul_mem_graded hx hu₂)
    exact add_mem (hleft ih) (hright ih)

private def primDefect : U →ₗ[R] U ⊗[R] U :=
  Coalgebra.comul (R := R) -
    ((TensorProduct.mk R U U).flip 1 + TensorProduct.mk R U U 1)

private theorem primDefect_apply (u : U) :
    primDefect (R := R) (L := L) u =
      Coalgebra.comul (R := R) u - (u ⊗ₜ[R] 1 + 1 ⊗ₜ[R] u) := (rfl)

private theorem primDefect_mem_iSup_homogeneousSubmodule (i : Γ) {u : U}
    (hu : u ∈ homogeneousSubmodule ℒ i) :
    primDefect (R := R) (L := L) u ∈
      ⨆ (a : Γ) (b : Γ) (_ : a + b = i),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ a) (homogeneousSubmodule ℒ b) := by
  rw [primDefect_apply]
  refine sub_mem (comul_mem_iSup_homogeneousSubmodule ℒ i hu) (add_mem ?_ ?_)
  · apply Submodule.mem_iSup_of_mem i
    apply Submodule.mem_iSup_of_mem (0 : Γ)
    rw [iSup_pos (add_zero i)]
    exact Submodule.apply_mem_map₂ _ hu SetLike.GradedOne.one_mem
  · apply Submodule.mem_iSup_of_mem (0 : Γ)
    apply Submodule.mem_iSup_of_mem i
    rw [iSup_pos (zero_add i)]
    exact Submodule.apply_mem_map₂ _ SetLike.GradedOne.one_mem hu

variable (d : Γ →+ ℤ) [DecidableEq Γ] [GradedLieAlgebra ℒ]

/-- Comultiplication preserves the total-degree filtration on `U(L)`. -/
theorem degreeFiltration_ideal_le_comap_comul (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal k ≤
      (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) := by
  let F := degreeFiltration ℒ d hneg
  rw [degreeFiltration_ideal_le_iff]
  intro n hn u hu
  have hmem := comul_mem_iSup_homogeneousSubmodule ℒ n hu
  have hbound :
      (⨆ (a : Γ) (b : Γ) (_ : a + b = n),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ a) (homogeneousSubmodule ℒ b)) ≤
      ((F.tensorProduct R F).ideal k).restrictScalars R := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => Submodule.map₂_le.mpr ?_
    intro u₁ hu₁ u₂ hu₂
    simp only [Submodule.restrictScalars_mem, TensorProduct.mk_apply]
    by_cases ha : d a < 0
    · have hu₁0 : u₁ = 0 := by
        simpa only [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg ha,
          Submodule.mem_bot] using hu₁
      simp [hu₁0]
    · by_cases hb : d b < 0
      · have hu₂0 : u₂ = 0 := by
          simpa only [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hb,
            Submodule.mem_bot] using hu₂
        simp [hu₂0]
      · have hda : ((d a).toNat : ℤ) ≤ d a := by omega
        have hdb : ((d b).toNat : ℤ) ≤ d b := by omega
        have hsum : d a + d b = d n := by simpa only [map_add] using congrArg d hab
        have hkpq : k ≤ (d a).toNat + (d b).toNat := by omega
        exact F.tmul_mem_tensorProduct_ideal R F hkpq
          (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hu₁ hda)
          (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hu₂ hdb)
  exact hbound hmem

/-- The bialgebra counit of `U(L)` vanishes on filtration order `1`. -/
theorem counit_eq_zero_of_mem_degreeFiltration_one (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {u : U} (hu : u ∈ (degreeFiltration ℒ d hneg).ideal 1) :
    Coalgebra.counit (R := R) u = 0 :=
  (HopfIdeal.mem_augmentation R U).mp
    (HopfIdeal.mem_toIdeal.mp (degreeFiltration_le_augmentation ℒ d hneg Nat.one_pos hu))

/-- When the Lie grading is supported in strictly positive degrees, the first degree ideal contains
the kernel of the counit. -/
theorem mem_degreeFiltration_one_of_counit_eq_zero (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    {u : U} (hu : Coalgebra.counit (R := R) u = 0) :
    u ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 :=
  augmentation_le_degreeFiltration_one ℒ d hpos
    (HopfIdeal.mem_toIdeal.mpr ((HopfIdeal.mem_augmentation R U).mpr hu))

private theorem tensorProduct_degreeFiltration_le_degreeTail
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (m : ℕ) :
    (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal m).restrictScalars R ≤
      TauCeti.DirectSum.degreeTail
        (fun p : Γ × Γ => Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ p.1) (homogeneousSubmodule ℒ p.2))
        (fun p => d p.1 + d p.2) m := by
  intro t ht
  have ht' := ((degreeFiltration ℒ d hneg).mem_tensorProduct_ideal_iff R
    (degreeFiltration ℒ d hneg)).mp ht
  refine (tensorFiltrationTail_le_iff _ _).mpr ?_ ht'
  intro p q hpq x hx y hy
  simp only [Submodule.restrictScalars_mem, degreeFiltration_ideal,
    TauCeti.GradedAlgebra.mem_degreeIdeal_iff, TauCeti.DirectSum.degreeTail_def] at hx hy
  refine Submodule.iSup_induction _ (motive := fun x => x ⊗ₜ[R] y ∈ _) hx (fun i x hx => ?_)
    (by simp) (fun x₁ x₂ h₁ h₂ =>
      by simpa only [TensorProduct.add_tmul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun x => x ⊗ₜ[R] y ∈ _) hx (fun hi x hx => ?_)
    (by simp) (fun x₁ x₂ h₁ h₂ =>
      by simpa only [TensorProduct.add_tmul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun y => x ⊗ₜ[R] y ∈ _) hy (fun j y hy => ?_)
    (by simp) (fun y₁ y₂ h₁ h₂ =>
      by simpa only [TensorProduct.tmul_add] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun y => x ⊗ₜ[R] y ∈ _) hy (fun hj y hy => ?_)
    (by simp) (fun y₁ y₂ h₁ h₂ =>
      by simpa only [TensorProduct.tmul_add] using add_mem h₁ h₂)
  exact TauCeti.DirectSum.le_degreeTail
    (fun r : Γ × Γ => Submodule.map₂ (TensorProduct.mk R U U)
      (homogeneousSubmodule ℒ r.1) (homogeneousSubmodule ℒ r.2))
    (fun r => d r.1 + d r.2) (i := (i, j)) (by dsimp only; omega)
    (Submodule.apply_mem_map₂ _ hx hy)

/-- If `u` is a completed primitive element of `(degreeFiltration ℒ d hneg).completion`, then
for any cutoff `k` with `d n ≤ k` and any representative `z` of the order-`k` projection of `u`,
the homogeneous component of `z` in degree `n` is primitive in `U(L)`. -/
theorem isPrimitiveElem_decompose_of_isCompletedPrimitive
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {u : (degreeFiltration ℒ d hneg).completion}
    (hu : (degreeFiltration ℒ d hneg).IsCompletedPrimitive R
      (degreeFiltration_ideal_le_comap_comul ℒ d hneg) u)
    {n : Γ} {k : ℕ} (hn : d n ≤ k) {z : U}
    (hz : Ideal.Quotient.mk ((degreeFiltration ℒ d hneg).ideal (k + 1)) z =
      (degreeFiltration ℒ d hneg).projection k u) :
    Bialgebra.IsPrimitiveElem R
      (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) z n : U) := by
  classical
  let F := degreeFiltration ℒ d hneg
  let ℋ := homogeneousSubmodule ℒ
  let 𝒯 : Γ × Γ → Submodule R (U ⊗[R] U) := fun p =>
    Submodule.map₂ (TensorProduct.mk R U U) (ℋ p.1) (ℋ p.2)
  let _ : _root_.DirectSum.Decomposition 𝒯 :=
    (_root_.DirectSum.IsInternal.tensorProduct ℋ ℋ
      (isInternal_homogeneousSubmodule ℒ)
      (isInternal_homogeneousSubmodule ℒ)).chooseDecomposition
  have hproj := congrArg ((F.tensorProduct R F).projection k)
    ((F.isCompletedPrimitive_iff R _ u).mp hu)
  rw [AlgFiltration.projection_completedComul, map_add,
    AlgFiltration.projection_includeLeftCompletion,
    AlgFiltration.projection_includeRightCompletion, ← hz] at hproj
  dsimp only [F] at hproj
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    ← map_add] at hproj
  have hdz_mem : primDefect (R := R) (L := L) z ∈
      TauCeti.DirectSum.degreeTail 𝒯 (fun p => d p.1 + d p.2) (k + 1) :=
    tensorProduct_degreeFiltration_le_degreeTail ℒ d hneg (k + 1)
      (Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa only [primDefect_apply, map_sub, sub_eq_zero] using hproj))
  -- Off-diagonal tensor components vanish on any total-degree slice `a + b = i`.
  have hvanish_ne (i : Γ) (w : U ⊗[R] U)
      (hw : w ∈ ⨆ (a : Γ) (b : Γ) (_ : a + b = i), 𝒯 (a, b))
      (p : Γ × Γ) (hp : p.1 + p.2 ≠ i) :
      (_root_.DirectSum.decompose 𝒯 w p : U ⊗[R] U) = 0 := by
    refine Submodule.iSup_induction _
      (motive := fun w => (_root_.DirectSum.decompose 𝒯 w p : U ⊗[R] U) = 0) hw
      (fun a w hw => ?_) (by simp) (fun w₁ w₂ h₁ h₂ => by simp [h₁, h₂])
    refine Submodule.iSup_induction _
      (motive := fun w => (_root_.DirectSum.decompose 𝒯 w p : U ⊗[R] U) = 0) hw
      (fun b w hw => ?_) (by simp) (fun w₁ w₂ h₁ h₂ => by simp [h₁, h₂])
    refine Submodule.iSup_induction _
      (motive := fun w => (_root_.DirectSum.decompose 𝒯 w p : U ⊗[R] U) = 0) hw
      (fun hab w hw => ?_) (by simp) (fun w₁ w₂ h₁ h₂ => by simp [h₁, h₂])
    exact _root_.DirectSum.decompose_of_mem_ne 𝒯 hw (by
      rintro rfl
      exact hp hab)
  -- Each bidegree `(p.1, p.2)` component of `primDefect zn` vanishes: when `p.1 + p.2 = n`
  -- it matches the vanishing component of `primDefect z` below `k + 1`.
  set zn : U := (_root_.DirectSum.decompose ℋ z n : U)
  have hprim_zero : primDefect (R := R) (L := L) zn = 0 := by
    apply (_root_.DirectSum.decomposeLinearEquiv 𝒯).injective
    apply _root_.DirectSum.ext
    intro p
    apply Subtype.ext
    simp only [_root_.DirectSum.decomposeLinearEquiv_apply, _root_.DirectSum.decompose_zero,
      _root_.DirectSum.zero_apply, ZeroMemClass.coe_zero]
    by_cases hp : p.1 + p.2 = n
    · have hsum_z : primDefect (R := R) (L := L) z =
          ∑ i ∈ (_root_.DirectSum.decompose ℋ z).support,
            primDefect (R := R) (L := L) (_root_.DirectSum.decompose ℋ z i : U) := by
        conv_lhs => rw [← _root_.DirectSum.sum_support_decompose ℋ z]
        rw [map_sum]
      have hdeg_p : d p.1 + d p.2 < ((k + 1 : ℕ) : ℤ) := by
        have hadd : d p.1 + d p.2 = d n := by simpa only [map_add] using congrArg d hp
        omega
      have hz_zero : (_root_.DirectSum.decompose 𝒯 (primDefect (R := R) (L := L) z) p :
          U ⊗[R] U) = 0 :=
        (TauCeti.DirectSum.mem_degreeTail_iff 𝒯 (fun r => d r.1 + d r.2)).mp hdz_mem p hdeg_p
      rw [hsum_z, _root_.DirectSum.decompose_sum, _root_.DirectSum.sum_apply,
        Submodule.coe_sum] at hz_zero
      rw [← hz_zero]
      symm
      refine Finset.sum_eq_single n (fun i _ hin => ?_) (fun hn_supp => ?_)
      · exact hvanish_ne i _
          (primDefect_mem_iSup_homogeneousSubmodule ℒ i
            (_root_.DirectSum.decompose ℋ z i).property)
          p (hp.trans_ne hin.symm)
      · have hzn0 : _root_.DirectSum.decompose ℋ z n = 0 :=
          DFinsupp.notMem_support_iff.mp hn_supp
        simp [hzn0]
    · exact hvanish_ne n _
        (primDefect_mem_iSup_homogeneousSubmodule ℒ n
          (_root_.DirectSum.decompose ℋ z n).property)
        p hp
  apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr
  rw [add_comm]
  exact sub_eq_zero.mp hprim_zero

end NonnegGrading

section PositiveGrading

variable {N R L : Type*} [AddCommMonoid N] [DecidableEq N]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The total-degree algebra filtration on `U(L)` associated to a positive Lie grading `(d, ℒ)`. -/
noncomputable abbrev positiveDegreeFiltration : TauCeti.AlgFiltration U :=
  degreeFiltration ℒ d.degree (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn.le)

/-- Comultiplication preserves `positiveDegreeFiltration`. -/
theorem positiveDegreeFiltration_ideal_le_comap_comul (k : ℕ) :
    (positiveDegreeFiltration d ℒ).ideal k ≤
      (((positiveDegreeFiltration d ℒ).tensorProduct R
        (positiveDegreeFiltration d ℒ)).ideal k).comap (Bialgebra.comulAlgHom R U) :=
  degreeFiltration_ideal_le_comap_comul ℒ d.degree _ k

/-- The bialgebra counit of `U(L)` vanishes on `(positiveDegreeFiltration d ℒ).ideal 1`. -/
theorem counit_eq_zero_of_mem_positiveDegreeFiltration_one
    {u : U} (hu : u ∈ (positiveDegreeFiltration d ℒ).ideal 1) :
    Coalgebra.counit (R := R) u = 0 :=
  counit_eq_zero_of_mem_degreeFiltration_one ℒ d.degree _ hu

/-- Elements of `U(L)` of counit `0` belong to `(positiveDegreeFiltration d ℒ).ideal 1`. -/
theorem mem_positiveDegreeFiltration_one_of_counit_eq_zero
    {u : U} (hu : Coalgebra.counit (R := R) u = 0) :
    u ∈ (positiveDegreeFiltration d ℒ).ideal 1 :=
  mem_degreeFiltration_one_of_counit_eq_zero ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) hu

/-- Canonical Lie images of elements in `d.degreeIdeal ℒ k` lie in filtration order `k + 1` of
`U(L)`. -/
theorem ι_mem_positiveDegreeFiltration_succ {k : ℕ} {x : L}
    (hx : x ∈ d.degreeIdeal ℒ k) :
    ι R x ∈ (positiveDegreeFiltration d ℒ).ideal (k + 1) := by
  have hx' : x ∈ (d.degreeIdeal ℒ k).toSubmodule := (LieSubmodule.mem_toSubmodule _).mpr hx
  rw [d.degreeIdeal_toSubmodule, d.degreeSubmodule_def] at hx'
  refine Submodule.iSup_induction _
    (motive := fun x => ι R x ∈ (positiveDegreeFiltration d ℒ).ideal (k + 1)) hx'
    (fun n x hx => ?_) (by simp) (fun x y hx hy => by simpa only [map_add] using add_mem hx hy)
  have hn : ((k + 1 : ℕ) : ℤ) ≤ d.degree n.val := by
    have := n.property
    omega
  exact ι_mem_degreeFiltration ℒ d.degree _ hx hn

/-- The finite-order Lie homomorphism from the order-`k` Lie truncation `L ⧸ d.degreeIdeal ℒ k`
into `U(L) ⧸ (positiveDegreeFiltration d ℒ).ideal (k + 1)`. -/
noncomputable def truncatedLieToU (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (positiveDegreeFiltration d ℒ).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ
    ((Ideal.Quotient.mkₐ R ((positiveDegreeFiltration d ℒ).ideal (k + 1))).toLieHom.comp (ι R))
    fun x hx => by
      rw [LieHom.mem_ker, LieHom.comp_apply, AlgHom.coe_toLieHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact ι_mem_positiveDegreeFiltration_succ d ℒ hx

/-- `truncatedLieToU` sends the quotient class of `x : L` to the class of `ι R x`. -/
@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU d ℒ k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((positiveDegreeFiltration d ℒ).ideal (k + 1)) (ι R x) := by
  rw [truncatedLieToU, LieIdeal.liftQ_apply, LieHom.comp_apply, AlgHom.coe_toLieHom,
    Ideal.Quotient.mkₐ_eq_mk]

/-- `truncatedLieToU` commutes with the quotient transition maps across orders `k ≤ l`. -/
theorem factor_truncatedLieToU {k l : ℕ} (h : k ≤ l) (z : d.truncatedLie ℒ l) :
    Ideal.Quotient.factor
        ((positiveDegreeFiltration d ℒ).antitone (Nat.add_le_add_right h 1))
        (truncatedLieToU d ℒ l z) =
      truncatedLieToU d ℒ k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) z) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ z
  rw [LieIdeal.mkQ_apply, LieIdeal.factor_apply, truncatedLieToU_mk, truncatedLieToU_mk,
    Ideal.Quotient.factor_mk]

/-- When `ι R : L → U(L)` is injective, each finite-order map `truncatedLieToU` is injective. -/
theorem truncatedLieToU_injective
    (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (truncatedLieToU d ℒ k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  intro x hx
  rw [LieHom.mem_ker, LieHom.comp_apply, AlgHom.coe_toLieHom, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hx
  have hmem : x ∈ (((positiveDegreeFiltration d ℒ).ideal (k + 1)).restrictScalars R).comap
      (ι R : L →ₗ⁅R⁆ U).toLinearMap := hx
  rw [comap_degreeFiltration_ι ℒ d.degree _ hι (k + 1), TauCeti.DirectSum.mem_degreeTail_iff]
    at hmem
  rw [d.mem_degreeIdeal_iff ℒ]
  intro n hn
  exact hmem n (by omega)

private noncomputable def completedLieToUFun (ξ : d.completedLie ℒ) :
    (positiveDegreeFiltration d ℒ).completion :=
  ⟨fun k => truncatedLieToU d ℒ k.unop
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k.unop ξ),
    ((positiveDegreeFiltration d ℒ).mem_completion_iff _).mpr fun {k l} h => by
      rw [factor_truncatedLieToU d ℒ h]
      exact congrArg (truncatedLieToU d ℒ k)
        (LieIdeal.factor_completionProjection
          (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) h ξ)⟩

private theorem projection_completedLieToUFun (k : ℕ) (ξ : d.completedLie ℒ) :
    (positiveDegreeFiltration d ℒ).projection k (completedLieToUFun d ℒ ξ) =
      truncatedLieToU d ℒ k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k ξ) :=
  (positiveDegreeFiltration d ℒ).projection_apply k (completedLieToUFun d ℒ ξ)

/-- The canonical Lie homomorphism from the completed Lie algebra `d.completedLie ℒ` into the
completed universal enveloping algebra `(positiveDegreeFiltration d ℒ).completion`. -/
noncomputable def completedLieToU :
    d.completedLie ℒ →ₗ⁅R⁆ (positiveDegreeFiltration d ℒ).completion where
  toFun := completedLieToUFun d ℒ
  map_add' ξ η := by
    apply (positiveDegreeFiltration d ℒ).completion_ext
    intro k
    rw [map_add, projection_completedLieToUFun, projection_completedLieToUFun,
      projection_completedLieToUFun, map_add, map_add]
  map_smul' r ξ := by
    rw [RingHom.id_apply]
    apply (positiveDegreeFiltration d ℒ).completion_ext
    intro k
    rw [← (positiveDegreeFiltration d ℒ).projectionₐ_apply (R := R) k (r • _),
      _root_.map_smul ((positiveDegreeFiltration d ℒ).projectionₐ (R := R) k) r _,
      (positiveDegreeFiltration d ℒ).projectionₐ_apply,
      projection_completedLieToUFun, projection_completedLieToUFun,
      _root_.map_smul
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k) r ξ,
      _root_.map_smul (truncatedLieToU d ℒ k) r _]
  map_lie' {ξ η} := by
    apply (positiveDegreeFiltration d ℒ).completion_ext
    intro k
    rw [LieRing.of_associative_ring_bracket, map_sub, map_mul, map_mul,
      projection_completedLieToUFun, projection_completedLieToUFun,
      projection_completedLieToUFun, ← LieRing.of_associative_ring_bracket,
      ← (truncatedLieToU d ℒ k).map_lie,
      ← (LieIdeal.completionProjection
        (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k).map_lie]

/-- The order-`k` projection of `completedLieToU` agrees with `truncatedLieToU` on the order-`k`
Lie projection. -/
@[simp]
theorem projection_completedLieToU (k : ℕ) (ξ : d.completedLie ℒ) :
    (positiveDegreeFiltration d ℒ).projection k (completedLieToU d ℒ ξ) =
      truncatedLieToU d ℒ k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k ξ) :=
  projection_completedLieToUFun d ℒ k ξ

/-- `completedLieToU` extends the canonical inclusion `ι R : L → U(L)` on completions. -/
@[simp]
theorem completedLieToU_toCompletion (x : L) :
    completedLieToU d ℒ
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (positiveDegreeFiltration d ℒ).toCompletion (ι R x) := by
  apply (positiveDegreeFiltration d ℒ).completion_ext
  intro k
  rw [projection_completedLieToU, LieIdeal.completionProjection_toCompletion, LieIdeal.mkQ_apply,
    truncatedLieToU_mk, AlgFiltration.projection_toCompletion]

/-- `completedLieToU` turns the completed Lie bracket into the associative commutator. -/
theorem completedLieToU_lie (ξ η : d.completedLie ℒ) :
    completedLieToU d ℒ ⁅ξ, η⁆ =
      completedLieToU d ℒ ξ * completedLieToU d ℒ η -
        completedLieToU d ℒ η * completedLieToU d ℒ ξ :=
  (completedLieToU d ℒ).map_lie ξ η

/-- Every image of `completedLieToU` belongs to the first completion ideal. -/
theorem completedLieToU_mem_completionIdeal_one (ξ : d.completedLie ℒ) :
    completedLieToU d ℒ ξ ∈ (positiveDegreeFiltration d ℒ).completionIdeal 1 := by
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, projection_completedLieToU]
  rw [Subsingleton.elim
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) 0 ξ) 0,
    map_zero]

/-- Every image of `completedLieToU` is completed primitive over any commutative ring `R`. -/
theorem isCompletedPrimitive_completedLieToU (ξ : d.completedLie ℒ) :
    (positiveDegreeFiltration d ℒ).IsCompletedPrimitive R
      (positiveDegreeFiltration_ideal_le_comap_comul d ℒ) (completedLieToU d ℒ ξ) := by
  let F := positiveDegreeFiltration d ℒ
  let hcomul := positiveDegreeFiltration_ideal_le_comap_comul d ℒ
  rw [AlgFiltration.isCompletedPrimitive_iff]
  apply (F.tensorProduct R F).completion_ext
  intro k
  obtain ⟨x, hx⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k ξ)
  have hproj : F.projection k (completedLieToU d ℒ ξ) =
      F.projection k (F.toCompletion (ι R x)) := by
    rw [projection_completedLieToU, ← hx, LieIdeal.mkQ_apply, truncatedLieToU_mk,
      AlgFiltration.projection_toCompletion]
  have hx_prim : F.IsCompletedPrimitive R hcomul (F.toCompletion (ι R x)) :=
    AlgFiltration.IsCompletedPrimitive.toCompletion (isPrimitiveElem_ι R L x)
  have hx_eq := (F.isCompletedPrimitive_iff R hcomul _).mp hx_prim
  have hx_k := congrArg ((F.tensorProduct R F).projection k) hx_eq
  dsimp only [F, hcomul] at hx_k hproj ⊢
  simpa only [AlgFiltration.projection_completedComul, map_add,
    AlgFiltration.projection_includeLeftCompletion,
    AlgFiltration.projection_includeRightCompletion, ← hproj] using hx_k

/-- When `ι R : L → U(L)` is injective, `completedLieToU` is injective. -/
theorem completedLieToU_injective_of_ι_injective
    (hι : Function.Injective (ι R : L → U)) :
    Function.Injective (completedLieToU d ℒ) := by
  intro ξ η h
  apply LieIdeal.completion_ext
  intro k
  apply truncatedLieToU_injective d ℒ hι k
  simpa only [projection_completedLieToU] using
    congrArg ((positiveDegreeFiltration d ℒ).projection k) h

private theorem exists_completedLieToU_projection_eq_sum (x : ∀ n, ℒ n) :
    ∃ ξ : d.completedLie ℒ, ∀ k : ℕ,
      (positiveDegreeFiltration d ℒ).projection k (completedLieToU d ℒ ξ) =
        Ideal.Quotient.mk ((positiveDegreeFiltration d ℒ).ideal (k + 1))
          (∑ n ∈ (d.finite_cutoff k).toFinset, ι R (x n : L)) := by
  let S : ℕ → L := fun k => ∑ n ∈ (d.finite_cutoff k).toFinset, (x n : L)
  have hcompat (k : ℕ) :
      LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k))
        ((d.degreeIdeal ℒ (k + 1)).mkQ (S (k + 1))) =
      (d.degreeIdeal ℒ k).mkQ (S k) := by
    rw [← LieHom.comp_apply, LieIdeal.factor_mkQ, ← sub_eq_zero, ← map_sub,
      LieIdeal.mkQ_eq_zero]
    have hsub : (d.finite_cutoff k).toFinset ⊆ (d.finite_cutoff (k + 1)).toFinset :=
      fun n hn => (d.finite_cutoff (k + 1)).mem_toFinset.mpr
        (d.cutoff_mono (Nat.le_succ k) ((d.finite_cutoff k).mem_toFinset.mp hn))
    have hdiff : S (k + 1) - S k =
        ∑ n ∈ (d.finite_cutoff (k + 1)).toFinset \ (d.finite_cutoff k).toFinset, (x n : L) :=
      (eq_sub_of_add_eq (Finset.sum_sdiff hsub)).symm
    rw [← LieSubmodule.mem_toSubmodule, d.degreeIdeal_toSubmodule, hdiff]
    refine Submodule.sum_mem _ fun n hn => ?_
    have hn₁ := (PositiveDegrees.mem_cutoff d).mp
      ((d.finite_cutoff (k + 1)).mem_toFinset.mp (Finset.mem_sdiff.mp hn).1)
    have hn₀ := mt (d.finite_cutoff k).mem_toFinset.mpr (Finset.mem_sdiff.mp hn).2
    simp only [PositiveDegrees.mem_cutoff, hn₁.1, true_and, not_le] at hn₀
    exact d.le_degreeSubmodule ℒ hn₀ (x n).property
  let liftHom : R →ₗ⁅R⁆ d.completedLie ℒ :=
    LieIdeal.completionLift (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
      (fun k =>
        { toFun := fun r : R => r • (d.degreeIdeal ℒ k).mkQ (S k)
          map_add' := fun r s => add_smul r s _
          map_smul' := fun a r => by simp [mul_smul]
          map_lie' := fun {r s} => by simp [LieRing.of_associative_ring_bracket, mul_comm r s] })
      (fun k => LieHom.ext fun r =>
        ((LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k))).map_smul r _).trans
          (congrArg (r • ·) (hcompat k)))
  refine ⟨liftHom 1, fun k => ?_⟩
  have h1 : LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k
      (liftHom 1) = (d.degreeIdeal ℒ k).mkQ (S k) := by
    simpa only [liftHom, LieIdeal.completionProjection_lift, LieHom.coe_mk] using
      one_smul R ((d.degreeIdeal ℒ k).mkQ (S k))
  rw [projection_completedLieToU, h1, LieIdeal.mkQ_apply, truncatedLieToU_mk]
  simp only [S, map_sum]

private theorem decompose_cutoff_sum_ι_eq (x : ∀ n, ℒ n) {k : ℕ} {n : N}
    (hnk : d.degree n ≤ k) :
    (_root_.DirectSum.decompose (homogeneousSubmodule ℒ)
        (∑ m ∈ (d.finite_cutoff k).toFinset, ι R (x m : L)) n : U) =
      ι R (x n : L) := by
  let ℋ := homogeneousSubmodule ℒ
  simp only [_root_.DirectSum.decompose_sum, _root_.DirectSum.sum_apply, Submodule.coe_sum]
  by_cases hmon : n ∈ d.monoid
  · have hn_mem : n ∈ (d.finite_cutoff k).toFinset :=
      (d.finite_cutoff k).mem_toFinset.mpr ((PositiveDegrees.mem_cutoff d).mpr ⟨hmon, hnk⟩)
    rw [Finset.sum_eq_single n]
    · exact _root_.DirectSum.decompose_of_mem_same ℋ
        (ι_mem_homogeneousSubmodule ℒ (x n).property)
    · intro m _ hmn
      exact _root_.DirectSum.decompose_of_mem_ne ℋ
        (ι_mem_homogeneousSubmodule ℒ (x m).property) hmn
    · exact fun h => (h hn_mem).elim
  · have hx0 : (x n : L) = 0 := by
      simpa only [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n (Or.inl hmon),
        Submodule.mem_bot] using (x n).property
    rw [hx0, map_zero]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm_mon := ((PositiveDegrees.mem_cutoff d).mp
      ((d.finite_cutoff k).mem_toFinset.mp hm)).1
    exact _root_.DirectSum.decompose_of_mem_ne ℋ
      (ι_mem_homogeneousSubmodule ℒ (x m).property) (fun h => hmon (h ▸ hm_mon))

private theorem decompose_rep_eq_of_projection
    (u : (positiveDegreeFiltration d ℒ).completion)
    {k : ℕ} {z z₀ : U} {n : N} (hnk : d.degree n ≤ k)
    (hz : Ideal.Quotient.mk ((positiveDegreeFiltration d ℒ).ideal (k + 1)) z =
      (positiveDegreeFiltration d ℒ).projection k u)
    (hz₀ : Ideal.Quotient.mk
        ((positiveDegreeFiltration d ℒ).ideal ((d.degree n).toNat + 1)) z₀ =
      (positiveDegreeFiltration d ℒ).projection (d.degree n).toNat u) :
    (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) z₀ n : U) =
      (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) z n : U) := by
  have hle : (d.degree n).toNat ≤ k := by omega
  have hfac := (positiveDegreeFiltration d ℒ).factor_projection hle u
  rw [← hz, ← hz₀, Ideal.Quotient.factor_mk] at hfac
  have hdiff_mem := Ideal.Quotient.eq.mp hfac
  have hdlt : d.degree n < (((d.degree n).toNat + 1 : ℕ) : ℤ) := by omega
  have hzero := (mem_degreeFiltration_ideal_iff ℒ d.degree _).mp hdiff_mem n hdlt
  have hzero' :
      (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) z n : U) -
        (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) z₀ n : U) = 0 := by
    simpa only [_root_.DirectSum.decompose_sub, _root_.DirectSum.sub_apply,
      Submodule.coe_sub] using hzero
  exact (sub_eq_zero.mp hzero').symm

end PositiveGrading

section Rational

universe v

variable {N : Type*} {R : Type} {L : Type v}
  [AddCommMonoid N] [DecidableEq N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Over a commutative rational algebra `R : Type`, `completedLieToU` is injective with no freeness
or flatness hypothesis on `L`. -/
theorem completedLieToU_injective : Function.Injective (completedLieToU d ℒ) :=
  completedLieToU_injective_of_ι_injective d ℒ fun _ _ h =>
    (primitiveEquiv R L).injective <| Subtype.ext <| by
      simpa only [coe_primitiveEquiv_apply] using h

/-- Over a commutative rational algebra `R : Type`, an element of the completed universal
enveloping algebra is completed primitive if and only if it belongs to the image of
`completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU
    (u : (positiveDegreeFiltration d ℒ).completion) :
    (positiveDegreeFiltration d ℒ).IsCompletedPrimitive R
        (positiveDegreeFiltration_ideal_le_comap_comul d ℒ) u ↔
      u ∈ Set.range (completedLieToU d ℒ) := by
  refine ⟨fun hu => ?_, ?_⟩
  · classical
    let F := positiveDegreeFiltration d ℒ
    let ℋ := homogeneousSubmodule ℒ
    let zCut : N → U := fun n =>
      Classical.choose (Ideal.Quotient.mk_surjective (F.projection (d.degree n).toNat u))
    have hzCut (n : N) :
        Ideal.Quotient.mk (F.ideal ((d.degree n).toNat + 1)) (zCut n) =
          F.projection (d.degree n).toNat u :=
      Classical.choose_spec (Ideal.Quotient.mk_surjective (F.projection (d.degree n).toNat u))
    have hprim_n (n : N) :
        Bialgebra.IsPrimitiveElem R (_root_.DirectSum.decompose ℋ (zCut n) n : U) :=
      isPrimitiveElem_decompose_of_isCompletedPrimitive ℒ d.degree _ hu
        (Int.self_le_toNat (d.degree n)) (hzCut n)
    let y : N → L := fun n =>
      Classical.choose
        ((_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι _).mp (hprim_n n))
    have hy (n : N) : ι R (y n) = (_root_.DirectSum.decompose ℋ (zCut n) n : U) :=
      Classical.choose_spec
        ((_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι _).mp (hprim_n n))
    let x : ∀ n, ℒ n := fun n => _root_.DirectSum.decompose ℒ (y n) n
    have hx_ι (n : N) : ι R (x n : L) = (_root_.DirectSum.decompose ℋ (zCut n) n : U) := by
      have hdec := coe_decompose_mkAlgHom_ι ℒ (y n) n
      have hsame := _root_.DirectSum.decompose_of_mem_same ℋ
        (_root_.DirectSum.decompose ℋ (zCut n) n).property
      rw [← ι_apply, hy n, hsame] at hdec
      exact hdec.symm
    obtain ⟨ξ, hξ⟩ := exists_completedLieToU_projection_eq_sum d ℒ x
    refine ⟨ξ, F.completion_ext fun k => ?_⟩
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (F.projection k u)
    rw [hξ k, ← hz]
    apply Ideal.Quotient.eq.mpr
    rw [mem_degreeFiltration_ideal_iff]
    intro n hn
    rw [_root_.DirectSum.decompose_sub, _root_.DirectSum.sub_apply, Submodule.coe_sub,
      sub_eq_zero, decompose_cutoff_sum_ι_eq d ℒ x (by omega), hx_ι n,
      decompose_rep_eq_of_projection d ℒ u (by omega) hz (hzCut n)]
  · rintro ⟨ξ, rfl⟩
    exact isCompletedPrimitive_completedLieToU d ℒ ξ

/-- Over a commutative rational algebra `R : Type`, `completedLieToU` identifies the completed Lie
algebra `d.completedLie ℒ` linearly with the submodule of completed primitive elements of the
completed universal enveloping algebra. -/
noncomputable def completedPrimitiveEquiv :
    d.completedLie ℒ ≃ₗ[R]
      (positiveDegreeFiltration d ℒ).completedPrimitiveSubmodule R
        (positiveDegreeFiltration_ideal_le_comap_comul d ℒ) :=
  LinearEquiv.ofBijective
    ((completedLieToU d ℒ).toLinearMap.codRestrict _ fun ξ =>
      ((positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R _ _).mpr
        (isCompletedPrimitive_completedLieToU d ℒ ξ))
    ⟨(LinearMap.injective_codRestrict_iff _).mpr (completedLieToU_injective d ℒ),
      fun u => by
        have hu := ((positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R _ u.1).mp u.2
        obtain ⟨ξ, hξ⟩ := (isCompletedPrimitive_iff_mem_range_completedLieToU d ℒ u.1).mp hu
        exact ⟨ξ, Subtype.ext hξ⟩⟩

/-- `completedPrimitiveEquiv` evaluates by `completedLieToU`. -/
@[simp]
theorem coe_completedPrimitiveEquiv_apply (ξ : d.completedLie ℒ) :
    (completedPrimitiveEquiv d ℒ ξ : (positiveDegreeFiltration d ℒ).completion) =
      completedLieToU d ℒ ξ := (rfl)

/-- Recovering a completed Lie element from `completedLieToU ξ` returns `ξ`. -/
@[simp]
theorem completedPrimitiveEquiv_symm_completedLieToU (ξ : d.completedLie ℒ)
    (h : completedLieToU d ℒ ξ ∈
      (positiveDegreeFiltration d ℒ).completedPrimitiveSubmodule R
        (positiveDegreeFiltration_ideal_le_comap_comul d ℒ)) :
    (completedPrimitiveEquiv d ℒ).symm ⟨completedLieToU d ℒ ξ, h⟩ = ξ := by
  apply (completedPrimitiveEquiv d ℒ).injective
  apply Subtype.ext
  simp

/-- The completed Lie element recovered from a completed primitive element maps back to it under
`completedLieToU`. -/
@[simp]
theorem completedLieToU_completedPrimitiveEquiv_symm
    (u : (positiveDegreeFiltration d ℒ).completedPrimitiveSubmodule R
      (positiveDegreeFiltration_ideal_le_comap_comul d ℒ)) :
    completedLieToU d ℒ ((completedPrimitiveEquiv d ℒ).symm u) = u := by
  simpa only [coe_completedPrimitiveEquiv_apply] using
    congrArg Subtype.val ((completedPrimitiveEquiv d ℒ).apply_symm_apply u)

/-- `completedPrimitiveEquiv` carries the Lie bracket on `d.completedLie ℒ` to the associative
commutator. -/
theorem coe_completedPrimitiveEquiv_lie (ξ η : d.completedLie ℒ) :
    (completedPrimitiveEquiv d ℒ ⁅ξ, η⁆ : (positiveDegreeFiltration d ℒ).completion) =
      (completedPrimitiveEquiv d ℒ ξ : (positiveDegreeFiltration d ℒ).completion) *
          (completedPrimitiveEquiv d ℒ η : (positiveDegreeFiltration d ℒ).completion) -
        (completedPrimitiveEquiv d ℒ η : (positiveDegreeFiltration d ℒ).completion) *
          (completedPrimitiveEquiv d ℒ ξ : (positiveDegreeFiltration d ℒ).completion) :=
  completedLieToU_lie d ℒ ξ η

/-- Recovering a completed Lie element from a commutator of completed primitive elements recovers
their Lie bracket. -/
theorem completedPrimitiveEquiv_symm_commutator
    (u v : (positiveDegreeFiltration d ℒ).completedPrimitiveSubmodule R
      (positiveDegreeFiltration_ideal_le_comap_comul d ℒ)) :
    (completedPrimitiveEquiv d ℒ).symm
        ⟨(u : (positiveDegreeFiltration d ℒ).completion) *
            (v : (positiveDegreeFiltration d ℒ).completion) -
          (v : (positiveDegreeFiltration d ℒ).completion) *
            (u : (positiveDegreeFiltration d ℒ).completion),
          ((positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R _ _).mpr
            ((((positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R _ u.1).mp
              u.property).commutator
            (((positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R _ v.1).mp
              v.property))⟩ =
      ⁅(completedPrimitiveEquiv d ℒ).symm u, (completedPrimitiveEquiv d ℒ).symm v⁆ := by
  apply (completedPrimitiveEquiv d ℒ).injective
  apply Subtype.ext
  rw [coe_completedPrimitiveEquiv_lie]
  simp only [LinearEquiv.apply_symm_apply]

end Rational

end TauCeti.UniversalEnvelopingAlgebra
