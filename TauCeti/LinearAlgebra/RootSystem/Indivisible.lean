/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import TauCeti.LinearAlgebra.RootSystem.Inversions.Length
import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber

/-!
# Indivisible roots of a root pairing

Let `P` be a (possibly non-reduced) root pairing. A root `a` is *indivisible* if `a / 2` is not a
root, written `∀ j, P.root i ≠ (2 : R) • P.root j`. Every automorphism of `P` preserves the
indivisible roots, so restricting the index type to `{i : ι // P.IsIndivisible i}` yields a
sub-pairing `P.indivisible` on the same weight and coweight modules.

For any finite root pairing whose coweight module has unique division, scalar multiples of a root
induce the same reflection, coreflection, reflection permutation, and Weyl-group generator. For a
finite crystallographic root pairing over a domain of characteristic zero, the linearly dependent
pairs of roots are classified by `±1`, `±2` multiples, so every root is either indivisible or
twice an indivisible root, the sub-pairing `P.indivisible` is reduced, and the restriction map on
automorphisms induces a canonical isomorphism `P.weylGroup ≃* P.indivisible.weylGroup` of Weyl
groups.

Over a field of characteristic zero, lifting a base across `RootPairing.restrictScalars'` extends
Mathlib's existence of a base (`RootPairing.nonempty_base`) to any finite reduced crystallographic
pairing without assuming the roots span (`RootPairing.nonempty_base_of_isReduced`). Over a linearly
ordered field, any regular coweight `v` determines a unique base whose positive roots are precisely
those positive on `v` (`RootPairing.existsUnique_base_of_forall_root'_ne_zero`).

## Main definitions

* `RootPairing.IsIndivisible`: predicate that a root is not twice another root.
* `RootPairing.indivisible`: the sub-pairing of indivisible roots on the same ambient modules.
* `RootPairing.autToIndivisible`: the restriction homomorphism `P.Aut →* P.indivisible.Aut`.
* `RootPairing.weylGroupEquivIndivisible`: the canonical isomorphism
  `P.weylGroup ≃* P.indivisible.weylGroup` for a finite crystallographic root pairing.
* `RootPairing.Base.ofRestrictScalars`: lifts a base of `P.restrictScalars' R` to a base of `P`.

## Main results

* `RootPairing.reflection_eq_of_root_eq_smul`, `RootPairing.coreflection_eq_of_root_eq_smul`,
  `RootPairing.reflectionPerm_eq_of_root_eq_smul`, and
  `RootPairing.weylGroup_ofIdx_eq_of_root_eq_smul`: a scalar multiple of a root induces the same
  reflection as the root itself.
* `RootPairing.root_eq_cases_of_not_linearIndependent`: two linearly dependent roots in a finite
  crystallographic root pairing are related by a factor in `{±1, ±2, ±1/2}`.
* `RootPairing.isIndivisible_or_exists_root_eq_two_smul`: every root of a finite crystallographic
  root pairing is either indivisible or twice an indivisible root.
* `RootPairing.instIsReducedIndivisible`: for a finite crystallographic root pairing over a domain
  of characteristic zero, `P.indivisible` is reduced.
* `RootPairing.nonempty_base_of_isReduced`: a finite reduced crystallographic root pairing over a
  field of characteristic zero has a base, without a spanning hypothesis.
* `RootPairing.existsUnique_base_of_forall_root'_ne_zero`: a regular coweight determines a unique
  base of a finite reduced crystallographic root pairing over a linearly ordered field.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1, no. 4 (the reduced
  subsystem of indivisible roots).
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  §1.1 and §6.1.
-/

public section

open Function Set Submodule

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-! ### Indivisible roots -/

/-- A root of `P` is *indivisible* if it is not twice another root. -/
def IsIndivisible (i : ι) : Prop :=
  ∀ j : ι, P.root i ≠ (2 : R) • P.root j

theorem isIndivisible_iff {i : ι} :
    P.IsIndivisible i ↔ ∀ j : ι, P.root i ≠ (2 : R) • P.root j :=
  Iff.rfl

variable {P} in
/-- Every automorphism of `P` preserves indivisibility of roots. -/
theorem IsIndivisible.indexEquiv (e : P.Aut) {i : ι} (hi : P.IsIndivisible i) :
    P.IsIndivisible (e.indexEquiv i) := by
  intro j hj
  refine hi (e.indexEquiv.symm j) ?_
  apply e.weightEquiv.injective
  have h1 : e.weightEquiv (P.root i) = P.root (e.indexEquiv i) := by
    simp [Equiv.weightEquiv_apply, Hom.root_weightMap_apply]
  have h2 : e.weightEquiv (P.root (e.indexEquiv.symm j)) = P.root j := by
    simp [Equiv.weightEquiv_apply, Hom.root_weightMap_apply]
  rw [map_smul, h1, h2]
  exact hj

@[simp]
theorem isIndivisible_indexEquiv_iff (e : P.Aut) (i : ι) :
    P.IsIndivisible (e.indexEquiv i) ↔ P.IsIndivisible i :=
  ⟨fun h ↦ by simpa using h.indexEquiv e⁻¹, fun h ↦ h.indexEquiv e⟩

@[simp]
theorem isIndivisible_reflectionPerm_iff (k i : ι) :
    P.IsIndivisible (P.reflectionPerm k i) ↔ P.IsIndivisible i := by
  simpa using P.isIndivisible_indexEquiv_iff (Equiv.reflection P k) i

theorem isIndivisible_reflectionPerm_self_iff (i : ι) :
    P.IsIndivisible (P.reflectionPerm i i) ↔ P.IsIndivisible i :=
  P.isIndivisible_reflectionPerm_iff i i

/-- Every root of a reduced root pairing over a characteristic-zero ring with unique division on the
weight module is indivisible. -/
theorem isIndivisible_of_isReduced [CharZero R] [HasUniqueDiv M] [P.IsReduced] (i : ι) :
    P.IsIndivisible i := by
  intro j hj
  have hmem : (2 : ℕ) • P.root j ∈ range P.root := ⟨i, by simpa [two_smul] using hj⟩
  exact P.nsmul_notMem_range_root hmem

/-- The sub-pairing of indivisible roots of `P` on the same weight and coweight modules. -/
noncomputable def indivisible : RootPairing {i : ι // P.IsIndivisible i} R M N where
  toLinearMap := P.toLinearMap
  isPerfPair_toLinearMap := P.isPerfPair_toLinearMap
  root := ⟨fun i ↦ P.root i.1, fun _ _ h ↦ Subtype.ext (P.root.injective h)⟩
  coroot := ⟨fun i ↦ P.coroot i.1, fun _ _ h ↦ Subtype.ext (P.coroot.injective h)⟩
  root_coroot_two i := P.root_coroot_two i.1
  reflectionPerm i :=
    (P.reflectionPerm i.1).subtypeEquiv fun a ↦ (P.isIndivisible_reflectionPerm_iff i.1 a).symm
  reflectionPerm_root i j := P.reflectionPerm_root i.1 j.1
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i.1 j.1

@[simp]
theorem indivisible_toLinearMap : P.indivisible.toLinearMap = P.toLinearMap :=
  (rfl)

@[simp]
theorem indivisible_root (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.root i = P.root i.1 :=
  (rfl)

@[simp]
theorem indivisible_coroot (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.coroot i = P.coroot i.1 :=
  (rfl)

@[simp]
theorem indivisible_root' (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.root' i = P.root' i.1 :=
  (rfl)

@[simp]
theorem indivisible_coroot' (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.coroot' i = P.coroot' i.1 :=
  (rfl)

@[simp]
theorem indivisible_pairing (i j : {i : ι // P.IsIndivisible i}) :
    P.indivisible.pairing i j = P.pairing i.1 j.1 :=
  (rfl)

@[simp]
theorem coe_indivisible_reflectionPerm (i j : {i : ι // P.IsIndivisible i}) :
    (P.indivisible.reflectionPerm i j : ι) = P.reflectionPerm i.1 j.1 :=
  (rfl)

@[simp]
theorem indivisible_reflection (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.reflection i = P.reflection i.1 := by
  ext x
  simp [reflection_apply]

@[simp]
theorem indivisible_coreflection (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.coreflection i = P.coreflection i.1 := by
  ext x
  simp [coreflection_apply]

instance instIsValuedInIndivisible (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    P.indivisible.IsValuedIn S where
  exists_value i j := P.exists_value i.1 j.1

/-- Restriction of an automorphism of `P` to the sub-pairing of indivisible roots, keeping the
underlying linear automorphisms of the weight and coweight modules unchanged. -/
noncomputable def autToIndivisible : P.Aut →* P.indivisible.Aut where
  toFun e :=
    { weightMap := e.weightMap
      coweightMap := e.coweightMap
      weight_coweight_transpose := e.weight_coweight_transpose
      indexEquiv :=
        e.indexEquiv.subtypeEquiv fun a ↦ (P.isIndivisible_indexEquiv_iff e a).symm
      root_weightMap := by ext i; exact congrFun e.root_weightMap i.1
      coroot_coweightMap := by ext i; exact congrFun e.coroot_coweightMap i.1
      bijective_weightMap := e.bijective_weightMap
      bijective_coweightMap := e.bijective_coweightMap }
  map_one' := by
    apply Equiv.weightHom_injective P.indivisible
    ext x
    rfl
  map_mul' e₁ e₂ := by
    apply Equiv.weightHom_injective P.indivisible
    ext x
    rfl

@[simp]
theorem autToIndivisible_weightEquiv (e : P.Aut) :
    (P.autToIndivisible e).weightEquiv = e.weightEquiv := by
  ext x
  rfl

@[simp]
theorem autToIndivisible_coweightEquiv (e : P.Aut) :
    (P.autToIndivisible e).coweightEquiv = e.coweightEquiv := by
  ext x
  rfl

@[simp]
theorem coe_autToIndivisible_indexEquiv (e : P.Aut) (i : {i : ι // P.IsIndivisible i}) :
    ((P.autToIndivisible e).indexEquiv i : ι) = e.indexEquiv i.1 :=
  (rfl)

theorem autToIndivisible_injective : Function.Injective P.autToIndivisible := by
  intro e₁ e₂ h
  apply Equiv.weightHom_injective P
  have := congrArg (fun f : P.indivisible.Aut ↦ f.weightEquiv) h
  simpa only [Equiv.weightHom_apply, autToIndivisible_weightEquiv] using this

@[simp]
theorem autToIndivisible_reflection (i : {i : ι // P.IsIndivisible i}) :
    P.autToIndivisible (Equiv.reflection P i.1) = Equiv.reflection P.indivisible i := by
  apply Equiv.weightHom_injective P.indivisible
  ext x
  simp [Equiv.weightHom_apply, Equiv.reflection_weightEquiv]

/-! ### Reflections of proportional roots -/

section Proportional

variable [Finite ι] [HasUniqueDiv N]

/-- A scalar multiple of a root induces the same reflection on weights as the root itself. -/
theorem reflection_eq_of_root_eq_smul {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : P.reflection j = P.reflection i := by
  have hc : t • P.coroot j = P.coroot i := P.smul_coroot_eq_of_root_eq_smul i j t h
  ext x
  simp only [reflection_apply, coroot', LinearMap.flip_apply]
  rw [h, ← hc, map_smul, smul_eq_mul, smul_smul, mul_comm]

/-- A scalar multiple of a root induces the same coreflection on coweights as the root itself. -/
theorem coreflection_eq_of_root_eq_smul {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : P.coreflection j = P.coreflection i := by
  have hc : t • P.coroot j = P.coroot i := P.smul_coroot_eq_of_root_eq_smul i j t h
  ext x
  simp only [coreflection_apply, root']
  rw [h, ← hc, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_comm]

/-- A scalar multiple of a root induces the same reflection permutation on roots as the root
itself. -/
theorem reflectionPerm_eq_of_root_eq_smul {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : P.reflectionPerm j = P.reflectionPerm i := by
  ext k
  apply P.root.injective
  rw [P.root_reflectionPerm, P.root_reflectionPerm, P.reflection_eq_of_root_eq_smul h]

/-- A scalar multiple of a root induces the same reflection automorphism as the root itself. -/
theorem equiv_reflection_eq_of_root_eq_smul {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : Equiv.reflection P j = Equiv.reflection P i := by
  apply Equiv.weightHom_injective P
  simpa only [Equiv.weightHom_apply, Equiv.reflection_weightEquiv] using
    P.reflection_eq_of_root_eq_smul h

/-- A scalar multiple of a root induces the same generator in the Weyl group as the root itself. -/
theorem weylGroup_ofIdx_eq_of_root_eq_smul {i j : ι} {t : R}
    (h : P.root j = t • P.root i) :
    weylGroup.ofIdx P j = weylGroup.ofIdx P i :=
  Subtype.ext (P.equiv_reflection_eq_of_root_eq_smul h)

end Proportional

/-! ### Finite crystallographic root pairings -/

section Crystallographic

variable [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic]

/-- Classification of linearly dependent pairs of roots in a finite crystallographic root pairing:
two linearly dependent roots are related by a factor in `{±1, ±2, ±1/2}`. -/
theorem root_eq_cases_of_not_linearIndependent {i j : ι}
    (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.root j = P.root i ∨ P.root j = -P.root i ∨
    P.root j = (2 : R) • P.root i ∨ P.root i = (2 : R) • P.root j ∨
    P.root j = (-2 : R) • P.root i ∨ P.root i = (-2 : R) • P.root j := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have hcw : P.pairingIn ℤ i j * P.pairingIn ℤ j i = 4 :=
    (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr h
  have hmem := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have hpair : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(2, 2), (-2, -2), (1, 4), (4, 1), (-1, -4), (-4, -1)} : Set (ℤ × ℤ)) := by
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hmem ⊢
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp_all
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpair
  rcases hpair with h1 | h1 | h1 | h1 | h1 | h1
  · left; exact congrArg P.root ((P.pairingIn_two_two_iff ℤ i j).mp h1).symm
  · right; left
    rw [(P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h1, neg_neg]
  · right; right; left; exact (P.pairingIn_one_four_iff ℤ i j).mp h1
  · right; right; right; left; exact (P.pairingIn_one_four_iff ℤ j i).mp h1.symm
  · right; right; right; right; left; exact (P.pairingIn_neg_one_neg_four_iff ℤ i j).mp h1
  · right; right; right; right; right; exact (P.pairingIn_neg_one_neg_four_iff ℤ j i).mp h1.symm

/-- If `2 • P.root i` is a root, then `i` is indivisible (since `4` is not a root multiple). -/
theorem isIndivisible_of_root_eq_two_smul {i j : ι}
    (h : P.root j = (2 : R) • P.root i) : P.IsIndivisible i := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : HasUniqueDiv M := .of_isTorsionFree R M
  intro k hk
  have h4 : P.root j = (4 : R) • P.root k := by
    rw [h, hk, smul_smul]
    norm_num
  have hdep : ¬ LinearIndependent R ![P.root k, P.root j] := by
    rw [LinearIndependent.pair_iff]
    push Not
    exact ⟨4, -1, by simp [h4], by norm_num⟩
  have hne := P.ne_zero k
  have hne_smul : ∀ a b : R, a ≠ b → a • P.root k ≠ b • P.root k := fun a b hab h ↦
    hab (smul_left_injective R hne h)
  rcases P.root_eq_cases_of_not_linearIndependent hdep with h1 | h1 | h1 | h1 | h1 | h1
  · exact hne_smul 4 1 (by norm_num) (by simpa [h4] using h1)
  · exact hne_smul 4 (-1) (by norm_num) (by simpa [h4, neg_smul] using h1)
  · exact hne_smul 4 2 (by norm_num) (by simpa [h4] using h1)
  · rw [h4, smul_smul] at h1
    have h24 : (2 : R) * 4 = 8 := by norm_num
    exact hne_smul 1 8 (by norm_num) (by simpa [h24] using h1)
  · exact hne_smul 4 (-2) (by norm_num) (by simpa [h4] using h1)
  · rw [h4, smul_smul] at h1
    have h24 : (-2 : R) * 4 = -8 := by norm_num
    exact hne_smul 1 (-8) (by norm_num) (by simpa [h24] using h1)

/-- Every root of a finite crystallographic root pairing is either indivisible or twice an
indivisible root. -/
theorem isIndivisible_or_exists_root_eq_two_smul (j : ι) :
    P.IsIndivisible j ∨ ∃ i : ι, P.IsIndivisible i ∧ P.root j = (2 : R) • P.root i := by
  by_cases hj : P.IsIndivisible j
  · exact Or.inl hj
  · rw [IsIndivisible] at hj
    push Not at hj
    obtain ⟨i, hi⟩ := hj
    exact Or.inr ⟨i, P.isIndivisible_of_root_eq_two_smul hi, hi⟩

/-- The sub-pairing of indivisible roots of a finite crystallographic root pairing is reduced. -/
instance instIsReducedIndivisible : P.indivisible.IsReduced where
  eq_or_eq_neg i j h := by
    have h' : ¬ LinearIndependent R ![P.root i.1, P.root j.1] := h
    rcases P.root_eq_cases_of_not_linearIndependent h' with h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr (by simp [h1])
    · exact absurd h1 (j.2 i.1)
    · exact absurd h1 (i.2 j.1)
    · exfalso
      apply j.2 (P.reflectionPerm i.1 i.1)
      simp [h1]
    · exfalso
      apply i.2 (P.reflectionPerm j.1 j.1)
      simp [h1]

/-- The indivisible roots span the same weight submodule as all roots. -/
@[simp]
theorem rootSpan_indivisible : P.indivisible.rootSpan R = P.rootSpan R := by
  refine le_antisymm (span_mono ?_) (span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  · rintro _ ⟨j, rfl⟩
    rcases P.isIndivisible_or_exists_root_eq_two_smul j with hj | ⟨i, hi, hij⟩
    · exact subset_span ⟨⟨j, hj⟩, rfl⟩
    · rw [hij]
      exact Submodule.smul_mem _ (2 : R) (subset_span ⟨⟨i, hi⟩, rfl⟩)

/-- Over a ring where `2` is invertible, the indivisible coroots span the same coweight submodule
as all coroots. -/
@[simp]
theorem corootSpan_indivisible [Invertible (2 : R)] :
    P.indivisible.corootSpan R = P.corootSpan R := by
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv N := .of_isTorsionFree R N
  refine le_antisymm (span_mono ?_) (span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  · rintro _ ⟨j, rfl⟩
    rcases P.isIndivisible_or_exists_root_eq_two_smul j with hj | ⟨i, hi, hij⟩
    · exact subset_span ⟨⟨j, hj⟩, rfl⟩
    · have hc : (2 : R) • P.coroot j = P.coroot i :=
        P.smul_coroot_eq_of_root_eq_smul i j 2 hij
      have hjeq : P.coroot j = (⅟(2 : R)) • P.coroot i := by
        rw [← hc, invOf_smul_smul]
      rw [hjeq]
      exact Submodule.smul_mem _ _ (subset_span ⟨⟨i, hi⟩, rfl⟩)

/-- Restriction of a Weyl-group element of `P` lies in the Weyl group of `P.indivisible`. -/
theorem autToIndivisible_mem_weylGroup {w : P.Aut} (hw : w ∈ P.weylGroup) :
    P.autToIndivisible w ∈ P.indivisible.weylGroup := by
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv N := .of_isTorsionFree R N
  induction hw using weylGroup.induction with
  | mem j =>
    rcases P.isIndivisible_or_exists_root_eq_two_smul j with hj | ⟨i, hi, hij⟩
    · rw [P.autToIndivisible_reflection ⟨j, hj⟩]
      exact P.indivisible.reflection_mem_weylGroup ⟨j, hj⟩
    · rw [P.equiv_reflection_eq_of_root_eq_smul hij, P.autToIndivisible_reflection ⟨i, hi⟩]
      exact P.indivisible.reflection_mem_weylGroup ⟨i, hi⟩
  | one =>
    rw [map_one]
    exact one_mem _
  | mul _ _ _ _ hg hh =>
    rw [map_mul]
    exact mul_mem hg hh

/-- The canonical isomorphism between the Weyl group of a finite crystallographic root pairing and
the Weyl group of its reduced sub-pairing of indivisible roots. -/
noncomputable def weylGroupEquivIndivisible : P.weylGroup ≃* P.indivisible.weylGroup :=
  MulEquiv.ofBijective
    ((P.autToIndivisible.domRestrict P.weylGroup).codRestrict
      P.indivisible.weylGroup fun w ↦ P.autToIndivisible_mem_weylGroup w.2)
    ⟨fun w₁ w₂ h ↦ Subtype.ext (P.autToIndivisible_injective (congrArg Subtype.val h)), by
      intro ⟨g, hg⟩
      induction hg using weylGroup.induction with
      | mem i =>
        refine ⟨weylGroup.ofIdx P i.1, Subtype.ext ?_⟩
        exact P.autToIndivisible_reflection i
      | one =>
        exact ⟨1, map_one _⟩
      | mul _ _ _ _ hg hh =>
        obtain ⟨u, hu⟩ := hg
        obtain ⟨v, hv⟩ := hh
        exact ⟨u * v, by rw [map_mul, hu, hv]; rfl⟩⟩

@[simp]
theorem coe_weylGroupEquivIndivisible (w : P.weylGroup) :
    ((P.weylGroupEquivIndivisible w : P.indivisible.weylGroup) : P.indivisible.Aut) =
      P.autToIndivisible (w : P.Aut) :=
  (rfl)

@[simp]
theorem weylGroupEquivIndivisible_ofIdx (i : {i : ι // P.IsIndivisible i}) :
    P.weylGroupEquivIndivisible (weylGroup.ofIdx P i.1) =
      weylGroup.ofIdx P.indivisible i :=
  Subtype.ext (P.autToIndivisible_reflection i)

@[simp]
theorem weylGroupEquivIndivisible_symm_ofIdx (i : {i : ι // P.IsIndivisible i}) :
    P.weylGroupEquivIndivisible.symm (weylGroup.ofIdx P.indivisible i) =
      weylGroup.ofIdx P i.1 := by
  rw [← P.weylGroupEquivIndivisible_ofIdx i, MulEquiv.symm_apply_apply]

theorem coe_weylGroupToPerm_weylGroupEquivIndivisible (w : P.weylGroup)
    (i : {i : ι // P.IsIndivisible i}) :
    (P.indivisible.weylGroupToPerm (P.weylGroupEquivIndivisible w) i : ι) =
      P.weylGroupToPerm w i.1 :=
  (rfl)

end Crystallographic

/-! ### Existence of bases without a spanning hypothesis -/

section BaseExistence

variable {R : Type*} [Field R] [Module R M] [Module R N] (P : RootPairing ι R M N)

/-- Every base of the restricted root system `P.restrictScalars' R` on the root and coroot spans
lifts to a base of `P` with the same support. -/
def Base.ofRestrictScalars [P.IsBalanced] (b : (P.restrictScalars' R).Base) : P.Base where
  support := b.support
  linearIndepOn_root :=
    b.linearIndepOn_root.map' (P.rootSpan R).subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  linearIndepOn_coroot :=
    b.linearIndepOn_coroot.map' (P.corootSpan R).subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  root_mem_or_neg_mem i := by
    have hmap : AddSubmonoid.map (P.rootSpan R).subtype.toAddMonoidHom
        (AddSubmonoid.closure ((P.restrictScalars' R).root '' b.support)) =
        AddSubmonoid.closure (P.root '' b.support) := by
      rw [AddMonoidHom.map_mclosure]
      congr 1
      ext x
      simp [restrictScalars']
      rfl
    rw [← hmap]
    rcases b.root_mem_or_neg_mem i with h | h
    · exact Or.inl ⟨(P.restrictScalars' R).root i, h, rfl⟩
    · exact Or.inr ⟨-(P.restrictScalars' R).root i, h, rfl⟩
  coroot_mem_or_neg_mem i := by
    have hmap : AddSubmonoid.map (P.corootSpan R).subtype.toAddMonoidHom
        (AddSubmonoid.closure ((P.restrictScalars' R).coroot '' b.support)) =
        AddSubmonoid.closure (P.coroot '' b.support) := by
      rw [AddMonoidHom.map_mclosure]
      congr 1
      ext x
      simp [restrictScalars']
      rfl
    rw [← hmap]
    rcases b.coroot_mem_or_neg_mem i with h | h
    · exact Or.inl ⟨(P.restrictScalars' R).coroot i, h, rfl⟩
    · exact Or.inr ⟨-(P.restrictScalars' R).coroot i, h, rfl⟩

@[simp]
theorem Base.ofRestrictScalars_support [P.IsBalanced] (b : (P.restrictScalars' R).Base) :
    (Base.ofRestrictScalars P b).support = b.support :=
  (rfl)

variable [CharZero R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Every finite reduced crystallographic root pairing over a field of characteristic zero admits a
base, even when the roots do not span the ambient weight space. -/
theorem nonempty_base_of_isReduced : Nonempty P.Base := by
  have : Fintype ι := Fintype.ofFinite ι
  let Q := P.restrictScalars' R
  have hQcryst : Q.IsCrystallographic :=
    ⟨fun i j ↦ by
      obtain ⟨z, hz⟩ := P.exists_value (S := ℤ) i j
      have hp : Q.pairing i j = P.pairing i j := by
        simpa using P.restrictScalars_pairing (K := R) i j
      exact ⟨z, hz.trans hp.symm⟩⟩
  have hQred : Q.IsReduced :=
    ⟨fun i j h ↦ by
      have h' : ¬ LinearIndependent R ![P.root i, P.root j] := by
        intro hli
        apply h
        have hcomp : (P.rootSpan R).subtype ∘ ![Q.root i, Q.root j] = ![P.root i, P.root j] := by
          ext k
          fin_cases k <;> rfl
        exact LinearIndependent.of_comp (P.rootSpan R).subtype (hcomp.symm ▸ hli)
      rcases IsReduced.eq_or_eq_neg (P := P) i j h' with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)⟩
  obtain ⟨b⟩ := RootPairing.nonempty_base Q
  exact ⟨Base.ofRestrictScalars P b⟩

/-- A regular coweight `v` of a finite reduced crystallographic root pairing over a linearly ordered
field determines a unique base whose positive roots are precisely those positive on `v`. -/
theorem existsUnique_base_of_forall_root'_ne_zero [LinearOrder R] [IsStrictOrderedRing R]
    {v : N} (hv : ∀ i, P.root' i v ≠ 0) :
    ∃! b : P.Base, ∀ i, b.IsPos i ↔ 0 < P.root' i v := by
  have : P.flip.IsReduced := P.flip_isReduced
  have : P.flip.IsCrystallographic :=
    ⟨fun i j ↦ by simpa using P.exists_value (S := ℤ) j i⟩
  obtain ⟨b₀⟩ := P.nonempty_base_of_isReduced
  have : Finite P.flip.weylGroup := P.flip.finite_weylGroup_of_base b₀.flip
  have hreg : IsRegularWeight P.flip v := (isRegularWeight_iff P.flip v).mpr hv
  obtain ⟨w, hw, -⟩ :=
    TauCeti.existsUnique_mem_openWeylChamber_of_finite_weylGroup P.flip b₀.flip hreg
  let b : P.Base := (b₀.flip.map (w : P.flip.Aut)).flip
  have hsupp_pos : ∀ i ∈ b.support, 0 < P.root' i v := by
    intro i hi
    classical
    simp only [b, Base.flip_support, Base.support_map_eq, Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact (TauCeti.mem_openWeylChamber_iff P.flip b₀.flip w v).mp hw j hj
  have hb : ∀ i, b.IsPos i ↔ 0 < P.root' i v := fun i ↦
    ⟨root'_pos_of_isPos hsupp_pos, fun hlt ↦ by
      by_contra hneg
      exact lt_asymm hlt (root'_neg_of_not_isPos hsupp_pos hneg)⟩
  refine ⟨b, hb, fun b' hb' ↦ ?_⟩
  ext i
  rw [TauCeti.mem_support_iff_isPos_and_forall_ne_add,
    TauCeti.mem_support_iff_isPos_and_forall_ne_add]
  simp only [hb, hb']

end BaseExistence

end RootPairing
