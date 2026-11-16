/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Indecomposable
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.Tactic.Module

/-!
# Indivisible roots and simple reflections in possibly non-reduced root pairings

For a crystallographic root pairing `P` that is neither assumed reduced nor assumed to span its
ambient weight and coweight modules (so `RootPairing.Base` may be empty, as for type `BC_n`, and
`RootPairing.IsRootSystem` need not hold, as for reductive groups with a positive-dimensional
central torus), passing to the *indivisible* roots `Φ_nd = {a ∈ Φ | ∀ b, a ≠ 2 b}` produces a
reduced crystallographic root pairing `P.indivisible` on the same ambient modules.

Given a linear functional `f` on the weight module taking nonzero values on every root, the
indecomposable positive roots `IsAddIndecomposable.baseOf P.root (f : M →+ R)` are indivisible,
each of their reflections permutes all positive roots linearly independent from it, their
reflections generate `P.weylGroup`, any two linearly independent roots are separated in sign by
`P.weylGroup`, and only `1 ∈ P.weylGroup` keeps every indecomposable positive root positive.

## Main definitions

* `RootPairing.IsIndivisible`: a root index `i` is indivisible if `P.root i ≠ 2 • P.root j` for all
  `j`.
* `RootPairing.indivisible`: the restricted `RootPairing` on `{i // P.IsIndivisible i}`.

## Main results

* `RootPairing.weylGroupToPerm_injective_of_isAnisotropic`,
  `RootPairing.finite_weylGroup_of_isAnisotropic`: faithfulness on root indices and finiteness of
  the Weyl group for finite anisotropic pairings over a domain, without spanning hypotheses.
* `RootPairing.reflection_eq_of_root_eq_smul`, `RootPairing.weylGroup.ofIdx_eq_of_root_eq_smul`:
  proportional roots define the same reflection and Weyl-group generator.
* `RootPairing.not_linearIndependent_root_iff`: in a finite crystallographic pairing in
  characteristic zero, two linearly dependent roots differ by a factor in `{±1, ±2, ±1/2}`.
* `RootPairing.instIsReducedIndivisible`: `P.indivisible` is reduced.
* `RootPairing.apply_root_reflectionPerm_pos_of_mem_baseOf`: the reflection in an indecomposable
  positive root preserves positivity of every positive root linearly independent from it.
* `RootPairing.closure_ofIdx_image_baseOf_eq_top`: the reflections in
  `IsAddIndecomposable.baseOf P.root (f : M →+ R)` generate `P.weylGroup`.
* `RootPairing.exists_weylGroup_apply_root_mul_neg`: any two linearly independent roots are given
  opposite `f`-signs by some element of `P.weylGroup`.
* `RootPairing.weylGroup.eq_one_of_forall_mem_baseOf_pos`: an element of `P.weylGroup` keeping
  every root of `IsAddIndecomposable.baseOf P.root (f : M →+ R)` `f`-positive is `1`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VI, §1, no. 3–7, Propositions 8, 13, 20.
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.1.2 and 6.1.11, pp. 108–115.
-/

public section

open Function IsAddIndecomposable Module Set

namespace RootPairing

variable {ι R M N : Type*}

section IsAnisotropic

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The action of the Weyl group of a finite anisotropic root pairing over a domain on its root
indices is faithful, whether or not the roots span the weight space. -/
theorem weylGroupToPerm_injective_of_isAnisotropic [Fintype ι] [IsDomain R] [P.IsAnisotropic] :
    Function.Injective P.weylGroupToPerm := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  refine weylGroup.eq_one_of_forall_smul_root_eq fun i ↦ ?_
  have hi : P.weylGroupToPerm w i = i := Equiv.Perm.ext_iff.mp hw i
  rw [P.weylGroup_apply_root, hi]

/-- The Weyl group of a finite anisotropic root pairing over a domain is finite, whether or not the
roots span the weight space. -/
theorem finite_weylGroup_of_isAnisotropic [Fintype ι] [IsDomain R] [P.IsAnisotropic] :
    Finite P.weylGroup :=
  Finite.of_injective P.weylGroupToPerm P.weylGroupToPerm_injective_of_isAnisotropic

/-- The action of the Weyl group of a finite crystallographic root pairing over a
characteristic-zero domain on its root indices is faithful. -/
theorem weylGroupToPerm_injective_of_isCrystallographic [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] : Function.Injective P.weylGroupToPerm := by
  let _ : Fintype ι := Fintype.ofFinite ι
  exact P.weylGroupToPerm_injective_of_isAnisotropic

/-- The Weyl group of a finite crystallographic root pairing over a characteristic-zero domain is
finite. -/
theorem finite_weylGroup_of_isCrystallographic [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] : Finite P.weylGroup := by
  let _ : Fintype ι := Fintype.ofFinite ι
  exact P.finite_weylGroup_of_isAnisotropic

end IsAnisotropic

section Proportional

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section ReflectionEq

variable [Finite ι] [CharZero R] [IsDomain R] {P}

/-- Proportional roots in a finite root pairing over a characteristic-zero domain induce the same
reflection on the weight module. -/
theorem reflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflection j = P.reflection i := by
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv N := .of_isTorsionFree R N
  have hc : t • P.coroot j = P.coroot i := P.smul_coroot_eq_of_root_eq_smul i j t h
  ext x
  have hsmul : P.toLinearMap x (P.coroot j) • P.root j =
      P.toLinearMap x (P.coroot i) • P.root i := by
    rw [h, ← hc, map_smul, smul_eq_mul, mul_smul, smul_comm]
  simp [reflection_apply, hsmul]

/-- Proportional roots in a finite root pairing over a characteristic-zero domain induce the same
automorphism. -/
theorem Equiv.reflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    Equiv.reflection P j = Equiv.reflection P i := by
  apply Equiv.weightHom_injective P
  simpa only [Equiv.weightHom_apply, Equiv.reflection_weightEquiv] using
    P.reflection_eq_of_root_eq_smul h

/-- Proportional roots in a finite root pairing over a characteristic-zero domain induce the same
permutation of root indices. -/
theorem reflectionPerm_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflectionPerm j = P.reflectionPerm i := by
  ext k
  apply P.root.injective
  simp [P.reflection_eq_of_root_eq_smul h]

/-- Proportional roots in a finite root pairing over a characteristic-zero domain define the same
reflection in the Weyl group. -/
theorem weylGroup.ofIdx_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    weylGroup.ofIdx P j = weylGroup.ofIdx P i :=
  Subtype.ext (Equiv.reflection_eq_of_root_eq_smul h)

end ReflectionEq

/-- A root index `i` is *indivisible* if `P.root i` is not twice another root (`Φ_nd` in
Bourbaki). -/
def IsIndivisible (i : ι) : Prop :=
  ∀ j, P.root i ≠ (2 : R) • P.root j

theorem isIndivisible_iff {i : ι} : P.IsIndivisible i ↔ ∀ j, P.root i ≠ (2 : R) • P.root j :=
  Iff.rfl

/-- In a reduced root pairing in characteristic zero, every root is indivisible. -/
theorem IsIndivisible.of_isReduced [CharZero R] [HasUniqueDiv M] [P.IsReduced] (i : ι) :
    P.IsIndivisible i := fun j hj ↦
  P.nsmul_notMem_range_root (n := 2) (i := j) ⟨i, by rw [hj, two_smul, two_smul]⟩

private theorem isIndivisible_of_aut (g : P.Aut) {i : ι} (h : P.IsIndivisible (g.indexEquiv i)) :
    P.IsIndivisible i := fun j hj ↦
  h (g.indexEquiv j) <| by
    rw [Equiv.root_indexEquiv_eq_smul, Equiv.root_indexEquiv_eq_smul, hj, smul_comm]

/-- Automorphisms of a root pairing preserve indivisibility of root indices. -/
@[simp]
theorem isIndivisible_aut_indexEquiv (g : P.Aut) (i : ι) :
    P.IsIndivisible (g.indexEquiv i) ↔ P.IsIndivisible i :=
  ⟨P.isIndivisible_of_aut g, fun h ↦
    P.isIndivisible_of_aut g⁻¹ (by
      have : g⁻¹.indexEquiv (g.indexEquiv i) = i := by
        change ((g⁻¹ * g).indexEquiv) i = i
        simp
      rwa [this])⟩

/-- The Weyl-group action on root indices preserves indivisibility. -/
theorem isIndivisible_weylGroupToPerm (w : P.weylGroup) (i : ι) :
    P.IsIndivisible (P.weylGroupToPerm w i) ↔ P.IsIndivisible i :=
  P.isIndivisible_aut_indexEquiv (w : P.Aut) i

/-- Root reflections preserve indivisibility of root indices. -/
@[simp]
theorem isIndivisible_reflectionPerm (i j : ι) :
    P.IsIndivisible (P.reflectionPerm i j) ↔ P.IsIndivisible j := by
  rw [← P.weylGroupToPerm_ofIdx_apply, P.isIndivisible_weylGroupToPerm]

/-- The restriction of a root pairing `P` to its indivisible roots `{i // P.IsIndivisible i}`. -/
noncomputable def indivisible : RootPairing {i : ι // P.IsIndivisible i} R M N where
  toLinearMap := P.toLinearMap
  root := (Embedding.subtype _).trans P.root
  coroot := (Embedding.subtype _).trans P.coroot
  root_coroot_two i := P.root_coroot_two i.1
  reflectionPerm i :=
    Equiv.Perm.subtypePerm (P.reflectionPerm i.1) fun j ↦ P.isIndivisible_reflectionPerm i.1 j
  reflectionPerm_root i j := P.reflectionPerm_root i.1 j.1
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i.1 j.1

@[simp]
theorem indivisible_root (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.root i = P.root i.1 :=
  (rfl)

@[simp]
theorem indivisible_coroot (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.coroot i = P.coroot i.1 :=
  (rfl)

@[simp]
theorem coe_indivisible_reflectionPerm (i j : {i : ι // P.IsIndivisible i}) :
    (P.indivisible.reflectionPerm i j : ι) = P.reflectionPerm i.1 j.1 :=
  (rfl)

@[simp]
theorem indivisible_pairing (i j : {i : ι // P.IsIndivisible i}) :
    P.indivisible.pairing i j = P.pairing i.1 j.1 :=
  (rfl)

instance instIsValuedInIndivisible (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    P.indivisible.IsValuedIn S where
  exists_value i j := by
    rw [indivisible_pairing]
    exact P.exists_value (S := S) i.1 j.1

private theorem linearIndependent_of_reflectionPerm {a b : ι}
    (hli : LinearIndependent R ![P.root a, P.root b]) :
    LinearIndependent R ![P.root a, P.root (P.reflectionPerm a b)] := by
  refine LinearIndependent.pair_iff.mpr fun c₁ c₂ hc ↦ ?_
  have hmap := congrArg (P.reflection a) hc
  simp only [map_add, map_smul, P.reflection_apply_self, ← root_reflectionPerm,
    P.reflectionPerm_self, smul_neg, ← neg_smul, map_zero] at hmap
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hli (-c₁) c₂ hmap
  exact ⟨neg_eq_zero.mp h1, h2⟩

/-- Reflecting a root `b` in `a` preserves linear independence of `{P.root a, P.root b}`. -/
theorem linearIndependent_root_reflectionPerm_iff (a b : ι) :
    LinearIndependent R ![P.root a, P.root (P.reflectionPerm a b)] ↔
      LinearIndependent R ![P.root a, P.root b] :=
  ⟨fun h ↦ by simpa using P.linearIndependent_of_reflectionPerm h,
    P.linearIndependent_of_reflectionPerm⟩

end Proportional

section Crystallographic

variable [CommRing R] [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]

/-- Two roots in a finite crystallographic root pairing over a characteristic-zero domain are
linearly dependent if and only if one is `±1` or `±2` times the other. -/
theorem not_linearIndependent_root_iff {i j : ι} :
    ¬ LinearIndependent R ![P.root i, P.root j] ↔
      i = j ∨ P.root j = -P.root i ∨ P.root j = (2 : R) • P.root i ∨
        P.root i = (2 : R) • P.root j ∨ P.root j = (-2 : R) • P.root i ∨
        P.root i = (-2 : R) • P.root j := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h4 : P.pairingIn ℤ i j * P.pairingIn ℤ j i = 4 :=
      (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr h
    have hmem := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    have hcases : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
        ({(2, 2), (-2, -2), (1, 4), (4, 1), (-1, -4), (-4, -1)} : Set (ℤ × ℤ)) := by
      rcases hmem with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' |
          h' | h' | h' <;> simp_all
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hcases
    rcases hcases with h' | h' | h' | h' | h' | h'
    · exact .inl ((P.pairingIn_two_two_iff ℤ i j).mp h')
    · exact .inr (.inl (neg_eq_iff_eq_neg.mp ((P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h').symm))
    · exact .inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ i j).mp h')))
    · exact .inr (.inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ j i).mp h'.symm))))
    · exact .inr (.inr (.inr (.inr (.inl ((P.pairingIn_neg_one_neg_four_iff ℤ i j).mp h')))))
    · exact .inr (.inr (.inr (.inr (.inr ((P.pairingIn_neg_one_neg_four_iff ℤ j i).mp h'.symm)))))
  · simp_rw [LinearIndependent.pair_iff, not_forall]
    rcases h with rfl | h | h | h | h | h
    · exact ⟨1, -1, by simp, by simp⟩
    · exact ⟨1, 1, by simp [h], by simp⟩
    · exact ⟨2, -1, by simp [h], by simp⟩
    · exact ⟨1, -2, by simp [h], by simp⟩
    · exact ⟨2, 1, by simp [h, neg_smul], by simp⟩
    · exact ⟨1, 2, by simp [h, neg_smul], by simp⟩

/-- If `P.root j = 2 • P.root i`, then `j` cannot be doubled again (`4 • P.root i` is never a
root). -/
theorem root_ne_two_smul_of_root_eq_two_smul {i j : ι} (h : P.root j = (2 : R) • P.root i)
    (k : ι) : P.root k ≠ (2 : R) • P.root j := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  intro hk
  have h4 : P.root k = (4 : R) • P.root i := by rw [hk, h, smul_smul]; norm_num
  have hdep : ¬ LinearIndependent R ![P.root i, P.root k] := by
    simp_rw [LinearIndependent.pair_iff, not_forall]
    exact ⟨4, -1, by simp [h4], by simp⟩
  have hcancel (a b : R) (hab : a • P.root i = b • P.root i) : a = b :=
    smul_left_injective R (P.ne_zero i) hab
  rcases P.not_linearIndependent_root_iff.mp hdep with rfl | h' | h' | h' | h' | h'
  · have := hcancel 1 4 (by simpa using h4); norm_num at this
  · have := hcancel 4 (-1) (by rw [← h4, h', neg_one_smul]); norm_num at this
  · have := hcancel 4 2 (h4.symm.trans h'); norm_num at this
  · have := hcancel 1 8 (by
      calc (1 : R) • P.root i = P.root i := one_smul _ _
        _ = (2 : R) • ((4 : R) • P.root i) := by rw [← h4, ← h']
        _ = (8 : R) • P.root i := by rw [smul_smul]; norm_num)
    norm_num at this
  · have := hcancel 4 (-2) (h4.symm.trans h'); norm_num at this
  · have := hcancel 1 (-8) (by
      calc (1 : R) • P.root i = P.root i := one_smul _ _
        _ = (-2 : R) • ((4 : R) • P.root i) := by rw [← h4, ← h']
        _ = (-8 : R) • P.root i := by rw [smul_smul]; norm_num)
    norm_num at this

/-- If `P.root j = 2 • P.root i`, then `i` is indivisible. -/
theorem isIndivisible_of_root_eq_two_smul {i j : ι} (h : P.root j = (2 : R) • P.root i) :
    P.IsIndivisible i := fun _ hk ↦
  P.root_ne_two_smul_of_root_eq_two_smul hk j h

/-- Every root of a finite crystallographic root pairing is either indivisible or twice an
indivisible root. -/
theorem exists_isIndivisible (i : ι) :
    ∃ j, P.IsIndivisible j ∧ (i = j ∨ P.root i = (2 : R) • P.root j) := by
  by_cases hi : P.IsIndivisible i
  · exact ⟨i, hi, .inl rfl⟩
  · simp only [IsIndivisible, not_forall, not_ne_iff] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨j, P.isIndivisible_of_root_eq_two_smul hj, .inr hj⟩

/-- Distinct non-opposite indivisible roots are linearly independent. -/
theorem linearIndependent_of_isIndivisible {i j : ι} (hi : P.IsIndivisible i)
    (hj : P.IsIndivisible j) (hne : i ≠ j) (hneg : P.root j ≠ -P.root i) :
    LinearIndependent R ![P.root i, P.root j] := by
  by_contra hdep
  rcases P.not_linearIndependent_root_iff.mp hdep with rfl | h | h | h | h | h
  · exact hne rfl
  · exact hneg h
  · exact hj i h
  · exact hi j h
  · refine hj (P.reflectionPerm i i) ?_
    simpa [neg_smul] using h
  · refine hi (P.reflectionPerm j j) ?_
    simpa [neg_smul] using h

instance instIsReducedIndivisible : P.indivisible.IsReduced where
  eq_or_eq_neg i j hdep := by
    by_cases hij : i = j
    · exact .inl (congrArg P.indivisible.root hij)
    · refine .inr ?_
      rw [indivisible_root, indivisible_root, ← neg_eq_iff_eq_neg]
      by_contra hneg
      have hdep' : ¬ LinearIndependent R ![P.root i.1, P.root j.1] := by
        simpa [indivisible_root] using hdep
      exact hdep' (P.linearIndependent_of_isIndivisible i.2 j.2 (Subtype.coe_ne_coe.mpr hij)
        (Ne.symm hneg))

end Crystallographic

section Ordered

variable [CommRing R] [LinearOrder R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- Every root in `IsAddIndecomposable.baseOf P.root (f : M →+ R)` is positive on `f`. -/
theorem apply_root_pos_of_mem_baseOf (f : Dual R M) {a : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) : 0 < f (P.root a) :=
  ha.1

section StrictOrdered

variable [IsStrictOrderedRing R]

/-- Every root in `IsAddIndecomposable.baseOf P.root (f : M →+ R)` is indivisible. -/
theorem isIndivisible_of_mem_baseOf (f : Dual R M) {a : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) : P.IsIndivisible a := by
  intro j hj
  have hj_pos : 0 < f (P.root j) := by
    have ha_pos : 0 < f (P.root a) := ha.1
    rw [hj, map_smul, smul_eq_mul] at ha_pos
    exact pos_of_mul_pos_right ha_pos zero_le_two
  have hzero := ha.2 j hj_pos j hj_pos (by rw [hj, two_smul])
  exact P.ne_zero j (hzero.elim id id)

variable [Finite ι]

/-- For a functional `f`, a root lies in the additive submonoid generated by
`baseOf P.root (f : M →+ R)` if and only if `f` is positive on it. -/
theorem root_mem_closure_baseOf_iff (f : Dual R M) {i : ι} :
    P.root i ∈ AddSubmonoid.closure (P.root '' baseOf P.root (f : M →+ R)) ↔
      0 < f (P.root i) := by
  rw [AddSubmonoid.closure_image_isAddIndecomposable_baseOf,
    AddSubmonoid.mem_closure_image_pos_iff P.root (f : M →+ R) i (P.ne_zero i)]
  rfl

variable [P.IsCrystallographic]

/-- Two `f`-positive roots, the first of which is indivisible, are linearly independent if and only
if the second is neither equal to nor twice the first. -/
theorem linearIndependent_iff_of_isIndivisible_of_pos (f : Dual R M) {a b : ι}
    (ha : P.IsIndivisible a) (ha_pos : 0 < f (P.root a)) (hb_pos : 0 < f (P.root b)) :
    LinearIndependent R ![P.root a, P.root b] ↔ b ≠ a ∧ P.root b ≠ (2 : R) • P.root a := by
  refine ⟨fun hli ↦ ⟨?_, ?_⟩, fun ⟨hne, htwo⟩ ↦ ?_⟩
  · rintro rfl
    exact (P.not_linearIndependent_root_iff.mpr (.inl rfl)) hli
  · intro h2
    exact (P.not_linearIndependent_root_iff.mpr (.inr (.inr (.inl h2)))) hli
  · by_contra hdep
    rcases P.not_linearIndependent_root_iff.mp hdep with rfl | h | h | h | h | h
    · exact hne rfl
    · have : f (P.root b) < 0 := by rw [h, map_neg]; exact neg_lt_zero.mpr ha_pos
      exact lt_asymm hb_pos this
    · exact htwo h
    · exact ha b h
    · have : f (P.root b) < 0 := by
        rw [h, map_smul, smul_eq_mul]
        nlinarith
      exact lt_asymm hb_pos this
    · have : f (P.root a) < 0 := by
        rw [h, map_smul, smul_eq_mul]
        nlinarith
      exact lt_asymm ha_pos this

omit [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private theorem exists_nat_sum_of_mem_closure {s : Finset ι}
    {x : M} (hx : x ∈ AddSubmonoid.closure (P.root '' (s : Set ι))) :
    ∃ c : s → ℕ, ∑ y : s, c y • P.root y.1 = x := by
  classical
  refine AddSubmonoid.closure_induction ?_ ⟨0, by simp⟩ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    refine ⟨Pi.single ⟨i, hi⟩ 1, ?_⟩
    rw [Fintype.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro y hy; simp [hy]
  · rintro _ _ _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩

private theorem linearIndepOn_int_baseOf (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) :
    LinearIndepOn ℤ P.root (baseOf P.root (f : M →+ R)) :=
  (P.linearIndepOn_root_baseOf' (S := R) f hf).restrict_scalars' ℤ

omit [Finite ι] [P.IsCrystallographic] in
private theorem exists_ne_pos_of_linearIndependent {s : Finset ι} {a b : ι} (ha_s : a ∈ s)
    {c : s → ℕ} (hc : ∑ x : s, c x • P.root x.1 = P.root b)
    (hli : LinearIndependent R ![P.root a, P.root b]) :
    ∃ x₀ : s, x₀.1 ≠ a ∧ 0 < c x₀ := by
  by_contra! honly
  have hb_eq : P.root b = c ⟨a, ha_s⟩ • P.root a := by
    rw [← hc, Finset.sum_eq_single ⟨a, ha_s⟩]
    · intro x _ hx
      rw [Nat.eq_zero_of_le_zero (honly x (Subtype.coe_ne_coe.mpr hx)), zero_smul]
    · simp
  have hrel : (c ⟨a, ha_s⟩ : R) • P.root a + (-1 : R) • P.root b = 0 := by
    simp [hb_eq, Nat.cast_smul_eq_nsmul]
  exact absurd (LinearIndependent.pair_iff.mp hli (c ⟨a, ha_s⟩) (-1) hrel).2 (by simp)

/-- Reflecting an `f`-positive root `b` in an element `a` of `baseOf P.root (f : M →+ R)`
linearly independent from `b` keeps `b` `f`-positive. -/
theorem apply_root_reflectionPerm_pos_of_mem_baseOf (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0)
    {a b : ι} (ha : a ∈ baseOf P.root (f : M →+ R)) (hb : 0 < f (P.root b))
    (hli : LinearIndependent R ![P.root a, P.root b]) :
    0 < f (P.root (P.reflectionPerm a b)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let s : Finset ι := Finset.univ.filter (· ∈ baseOf P.root (f : M →+ R))
  have hs_coe : (s : Set ι) = baseOf P.root (f : M →+ R) := by ext x; simp [s]
  have hb_mem : P.root b ∈ AddSubmonoid.closure (P.root '' (s : Set ι)) := by
    rw [hs_coe]; exact (P.root_mem_closure_baseOf_iff f).mpr hb
  obtain ⟨c, hc⟩ := P.exists_nat_sum_of_mem_closure hb_mem
  have ha_s : a ∈ s := by simp [s, ha]
  obtain ⟨x₀, hx₀_ne, hx₀_pos⟩ := P.exists_ne_pos_of_linearIndependent ha_s hc hli
  rw [← P.root_mem_closure_baseOf_iff f]
  let _ := P.indexNeg
  rcases mem_or_neg_mem_closure_baseOf P.root (f : M →+ R) (P.reflectionPerm a b) (hf _)
      (by rw [indexNeg_neg, root_reflectionPerm, reflection_apply_self]) with hpos | hneg
  · exact hpos
  · exfalso
    rw [← hs_coe] at hneg
    obtain ⟨d, hd⟩ := P.exists_nat_sum_of_mem_closure hneg
    let coeff : s → ℤ := fun x ↦
      (c x : ℤ) + (d x : ℤ) - if x.1 = a then P.pairingIn ℤ b a else 0
    have hsum : ∑ x : s, coeff x • P.root x.1 = 0 := by
      have hd' : ∑ x : s, (d x : ℤ) • P.root x.1 = -P.root (P.reflectionPerm a b) := by
        simpa [natCast_zsmul] using hd
      have hc' : ∑ x : s, (c x : ℤ) • P.root x.1 = P.root b := by simpa [natCast_zsmul] using hc
      have ha_sum : ∑ x : s, (if x.1 = a then P.pairingIn ℤ b a else 0) • P.root x.1 =
          P.pairingIn ℤ b a • P.root a := by
        rw [Finset.sum_eq_single ⟨a, ha_s⟩]
        · simp
        · intro x _ hx; simp [Subtype.coe_ne_coe.mpr hx]
        · simp
      simp_rw [coeff, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        hc', hd', ha_sum, root_reflectionPerm, P.reflection_apply_root' ℤ]
      abel
    have hli_int : LinearIndepOn ℤ P.root s := hs_coe.symm ▸ P.linearIndepOn_int_baseOf f hf
    have hx₀ : coeff x₀ = 0 := Fintype.linearIndependent_iff.mp hli_int coeff hsum x₀
    simp only [coeff, hx₀_ne, ↓reduceIte, sub_zero] at hx₀
    omega

private theorem exists_mem_closure_ofIdx_baseOf_of_pos
    (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) {j : ι}
    (hj : P.IsIndivisible j) (hj_pos : 0 < f (P.root j)) :
    ∃ w ∈ Subgroup.closure (weylGroup.ofIdx P '' baseOf P.root (f : M →+ R)),
      ∃ a ∈ baseOf P.root (f : M →+ R), P.weylGroupToPerm w a = j := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  set Δ := baseOf P.root (f : M →+ R)
  set W₀ := Subgroup.closure (weylGroup.ofIdx P '' Δ)
  let S : Set ι := {k | P.IsIndivisible k ∧ 0 < f (P.root k) ∧
    ∃ w ∈ W₀, P.weylGroupToPerm w k = j}
  obtain ⟨k, hk⟩ := S.toFinite.exists_minimalFor (fun k ↦ f (P.root k)) S
    ⟨j, hj, hj_pos, 1, one_mem W₀, rfl⟩
  obtain ⟨hk_ind, hk_pos, w, hw, hwk⟩ := hk.prop
  by_cases hk_mem : k ∈ Δ
  · exact ⟨w, hw, k, hk_mem, hwk⟩
  · exfalso
    let s : Finset ι := Finset.univ.filter (· ∈ Δ)
    have hs_coe : (s : Set ι) = Δ := by ext x; simp [s]
    have hk_cl : P.root k ∈ AddSubmonoid.closure (P.root '' (s : Set ι)) := by
      rw [hs_coe]; exact (P.root_mem_closure_baseOf_iff f).mpr hk_pos
    obtain ⟨c₀, hc₀⟩ := P.exists_nat_sum_of_mem_closure hk_cl
    let c : s → ℤ := fun x ↦ (c₀ x : ℤ)
    have hc : ∑ x : s, c x • P.root x.1 = P.root k := by simpa [c, natCast_zsmul] using hc₀
    have hc_pos : ¬ c ≤ 0 := fun hle ↦ P.ne_zero k <| by
      simp [← hc, fun x ↦ le_antisymm (hle x) (Nat.cast_nonneg _)]
    have hli_int : LinearIndepOn ℤ P.root s := hs_coe.symm ▸ P.linearIndepOn_int_baseOf f hf
    have hpair : Set.Pairwise (s : Set ι) fun x y ↦ P.pairingIn ℤ x y ≤ 0 :=
      hs_coe.symm ▸ P.baseOf_pairwise_pairing_le_zero (f : M →+ R) hf
    obtain ⟨⟨a, _⟩, _, hka_pos⟩ := P.exists_pos_pairingIn hli_int hpair hc hc_pos
    have ha : a ∈ Δ := by rwa [← hs_coe, Finset.mem_coe]
    have hli_ak : LinearIndependent R ![P.root a, P.root k] :=
      (P.linearIndependent_iff_of_isIndivisible_of_pos f (P.isIndivisible_of_mem_baseOf f ha)
        ha.1 hk_pos).mpr ⟨fun h ↦ hk_mem (h ▸ ha), hk_ind a⟩
    have hk'_mem : P.reflectionPerm a k ∈ S :=
      ⟨(P.isIndivisible_reflectionPerm a k).mpr hk_ind,
        P.apply_root_reflectionPerm_pos_of_mem_baseOf f hf ha hk_pos hli_ak,
        w * weylGroup.ofIdx P a, mul_mem hw (Subgroup.subset_closure (mem_image_of_mem _ ha)),
        by rw [P.weylGroupToPerm_mul_ofIdx_apply]; simpa using hwk⟩
    have hk'_lt : f (P.root (P.reflectionPerm a k)) < f (P.root k) := by
      rw [root_reflectionPerm, P.reflection_apply_root' ℤ, map_sub, map_zsmul, zsmul_eq_mul,
        sub_lt_self_iff]
      exact mul_pos (Int.cast_pos.mpr hka_pos) ha.1
    exact not_le.mpr hk'_lt (hk.le_of_le hk'_mem hk'_lt.le)

/-- Every indivisible root lies in the orbit of `baseOf P.root (f : M →+ R)` under the subgroup of
`P.weylGroup` generated by the reflections in `baseOf P.root (f : M →+ R)`. -/
theorem exists_mem_closure_ofIdx_baseOf_weylGroupToPerm_eq
    (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) {i : ι} (hi : P.IsIndivisible i) :
    ∃ w ∈ Subgroup.closure (weylGroup.ofIdx P '' baseOf P.root (f : M →+ R)),
      ∃ a ∈ baseOf P.root (f : M →+ R), P.weylGroupToPerm w a = i := by
  rcases (hf i).lt_or_gt with hneg | hgt
  · have hj_pos : 0 < f (P.root (P.reflectionPerm i i)) := by simpa using neg_pos.mpr hneg
    obtain ⟨w, hw, a, ha, hwa⟩ := P.exists_mem_closure_ofIdx_baseOf_of_pos f hf
      ((P.isIndivisible_reflectionPerm i i).mpr hi) hj_pos
    have hsa := Subgroup.subset_closure (mem_image_of_mem (weylGroup.ofIdx P) ha)
    refine ⟨w * weylGroup.ofIdx P a, mul_mem hw hsa, a, ha, ?_⟩
    let _ := P.indexNeg
    rw [P.weylGroupToPerm_mul_ofIdx_apply, ← indexNeg_neg, P.weylGroupToPerm_neg, hwa,
      ← indexNeg_neg, neg_neg]
  · exact P.exists_mem_closure_ofIdx_baseOf_of_pos f hf hi hgt

/-- The reflections in `IsAddIndecomposable.baseOf P.root (f : M →+ R)` generate `P.weylGroup`. -/
theorem closure_ofIdx_image_baseOf_eq_top (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) :
    Subgroup.closure (weylGroup.ofIdx P '' baseOf P.root (f : M →+ R)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  induction hg using weylGroup.induction with
  | mem i =>
    change weylGroup.ofIdx P i ∈ _
    obtain ⟨j, hj, hij⟩ := P.exists_isIndivisible i
    have hij_eq : weylGroup.ofIdx P i = weylGroup.ofIdx P j := by
      rcases hij with rfl | h2
      · rfl
      · exact weylGroup.ofIdx_eq_of_root_eq_smul h2
    rw [hij_eq]
    obtain ⟨w, hw, a, ha, rfl⟩ := P.exists_mem_closure_ofIdx_baseOf_weylGroupToPerm_eq f hf hj
    rw [weylGroup.ofIdx_weylGroupToPerm_eq_conj P]
    exact mul_mem (mul_mem hw (Subgroup.subset_closure (mem_image_of_mem _ ha))) (inv_mem hw)
  | one => exact one_mem _
  | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂

private theorem exists_weylGroup_apply_root_mul_neg_of_isIndivisible
    (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) {i j : ι}
    (hi : P.IsIndivisible i) (hli : LinearIndependent R ![P.root i, P.root j]) :
    ∃ w : P.weylGroup,
      f (P.root (P.weylGroupToPerm w i)) * f (P.root (P.weylGroupToPerm w j)) < 0 := by
  obtain ⟨u, _, a, ha, hua⟩ := P.exists_mem_closure_ofIdx_baseOf_weylGroupToPerm_eq f hf hi
  have hui : P.weylGroupToPerm u⁻¹ i = a := by
    rw [← hua, map_inv]
    exact Equiv.symm_apply_apply (P.weylGroupToPerm u) a
  set k := P.weylGroupToPerm u⁻¹ j
  have hli_ak : LinearIndependent R ![P.root a, P.root k] := by
    let φ : M ≃ₗ[R] M := ((u⁻¹ : P.weylGroup) : P.Aut).weightEquiv
    have heq : ![P.root a, P.root k] = φ ∘ ![P.root i, P.root j] := by
      ext m; fin_cases m
      · simp only [comp_apply, ← hui, ← P.weylGroup_apply_root]; rfl
      · simp only [comp_apply, k, ← P.weylGroup_apply_root]; rfl
    rw [heq]
    exact hli.map' φ.toLinearMap (LinearEquiv.ker _)
  rcases (hf k).lt_or_gt with hk_neg | hk_pos
  · exact ⟨u⁻¹, hui ▸ mul_neg_of_pos_of_neg ha.1 hk_neg⟩
  · refine ⟨weylGroup.ofIdx P a * u⁻¹, ?_⟩
    rw [P.weylGroupToPerm_ofIdx_mul_apply, P.weylGroupToPerm_ofIdx_mul_apply, hui]
    exact mul_neg_of_neg_of_pos (by simpa using neg_lt_zero.mpr ha.1)
      (P.apply_root_reflectionPerm_pos_of_mem_baseOf f hf ha hk_pos hli_ak)

/-- Any two linearly independent roots of a finite crystallographic root pairing are given opposite
signs on `f` by some element of `P.weylGroup`. -/
theorem exists_weylGroup_apply_root_mul_neg (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0)
    {i j : ι} (hli : LinearIndependent R ![P.root i, P.root j]) :
    ∃ w : P.weylGroup,
      f (P.root (P.weylGroupToPerm w i)) * f (P.root (P.weylGroupToPerm w j)) < 0 := by
  obtain ⟨i', hi', hi_eq⟩ := P.exists_isIndivisible i
  obtain ⟨j', hj', hj_eq⟩ := P.exists_isIndivisible j
  obtain ⟨ci, hci_pos, hci⟩ : ∃ ci : R, 0 < ci ∧ P.root i = ci • P.root i' := by
    rcases hi_eq with rfl | h2
    · exact ⟨1, one_pos, (one_smul R _).symm⟩
    · exact ⟨2, two_pos, h2⟩
  obtain ⟨cj, hcj_pos, hcj⟩ : ∃ cj : R, 0 < cj ∧ P.root j = cj • P.root j' := by
    rcases hj_eq with rfl | h2
    · exact ⟨1, one_pos, (one_smul R _).symm⟩
    · exact ⟨2, two_pos, h2⟩
  have hli' : LinearIndependent R ![P.root i', P.root j'] := by
    refine P.linearIndependent_of_isIndivisible hi' hj' (fun h ↦ ?_) (fun h ↦ ?_)
    · subst h
      have hrel : cj • P.root i + (-ci) • P.root j = 0 := by rw [hci, hcj]; module
      exact hcj_pos.ne' (LinearIndependent.pair_iff.mp hli cj (-ci) hrel).1
    · have hrel : cj • P.root i + ci • P.root j = 0 := by rw [hci, hcj, h]; module
      exact hcj_pos.ne' (LinearIndependent.pair_iff.mp hli cj ci hrel).1
  obtain ⟨w, hw⟩ := P.exists_weylGroup_apply_root_mul_neg_of_isIndivisible f hf hi' hli'
  refine ⟨w, ?_⟩
  have hwi : f (P.root (P.weylGroupToPerm w i)) = ci * f (P.root (P.weylGroupToPerm w i')) := by
    rw [← P.weylGroup_apply_root, ← P.weylGroup_apply_root, hci, smul_comm, map_smul, smul_eq_mul]
  have hwj : f (P.root (P.weylGroupToPerm w j)) = cj * f (P.root (P.weylGroupToPerm w j')) := by
    rw [← P.weylGroup_apply_root, ← P.weylGroup_apply_root, hcj, smul_comm, map_smul, smul_eq_mul]
  rw [hwi, hwj, show ci * f (P.root (P.weylGroupToPerm w i')) *
      (cj * f (P.root (P.weylGroupToPerm w j'))) =
      (ci * cj) * (f (P.root (P.weylGroupToPerm w i')) *
        f (P.root (P.weylGroupToPerm w j'))) by ring]
  exact mul_neg_of_pos_of_neg (mul_pos hci_pos hcj_pos) hw

private theorem exists_word_baseOf (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0)
    (g : P.weylGroup) :
    ∃ l : List ι, (∀ a ∈ l, a ∈ baseOf P.root (f : M →+ R)) ∧
      (l.map (weylGroup.ofIdx P)).prod = g := by
  have hg : g ∈ Subgroup.closure (weylGroup.ofIdx P '' baseOf P.root (f : M →+ R)) := by
    rw [P.closure_ofIdx_image_baseOf_eq_top f hf]
    exact Subgroup.mem_top g
  refine Subgroup.closure_induction ?_ ⟨[], by simp, by simp⟩ ?_ ?_ hg
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨[a], by simp [ha], by simp⟩
  · rintro _ _ _ _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, rfl⟩
    exact ⟨l₁ ++ l₂, List.forall_mem_append.mpr ⟨hl₁, hl₂⟩, by simp⟩
  · rintro _ _ ⟨l, hl, rfl⟩
    exact ⟨l.reverse, fun a ha ↦ hl a (List.mem_reverse.mp ha), by
      simp [List.prod_reverse_noncomm, Function.comp_def]⟩

private theorem exists_shorter_word_of_apply_root_neg
    (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) (l₀ : List ι)
    (hl₀ : ∀ b ∈ l₀, b ∈ baseOf P.root (f : M →+ R)) {k : ι} (hk_ind : P.IsIndivisible k)
    (hk_pos : 0 < f (P.root k))
    (hk_neg : f (P.root (P.weylGroupToPerm (l₀.map (weylGroup.ofIdx P)).prod k)) < 0) :
    ∃ l' : List ι, (∀ b ∈ l', b ∈ baseOf P.root (f : M →+ R)) ∧ l'.length < l₀.length ∧
      (l'.map (weylGroup.ofIdx P)).prod * weylGroup.ofIdx P k =
        (l₀.map (weylGroup.ofIdx P)).prod := by
  induction l₀ with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, Equiv.Perm.coe_one, id_eq] at hk_neg
    exact (lt_asymm hk_pos hk_neg).elim
  | cons b l₁ ih =>
    have hb : b ∈ baseOf P.root (f : M →+ R) := hl₀ b List.mem_cons_self
    have hl₁ : ∀ c ∈ l₁, c ∈ baseOf P.root (f : M →+ R) :=
      fun c hc ↦ hl₀ c (List.mem_cons_of_mem b hc)
    let u₁ := (l₁.map (weylGroup.ofIdx P)).prod
    simp only [List.map_cons, List.prod_cons, P.weylGroupToPerm_ofIdx_mul_apply] at hk_neg
    rcases (hf (P.weylGroupToPerm u₁ k)).lt_or_gt with hu₁_neg | hu₁_pos
    · obtain ⟨l', hl', hlen', heq'⟩ := ih hl₁ hu₁_neg
      refine ⟨b :: l', List.forall_mem_cons.mpr ⟨hb, hl'⟩, Nat.succ_lt_succ hlen', ?_⟩
      simp only [List.map_cons, List.prod_cons, mul_assoc, heq']
    · have heq_bk : P.weylGroupToPerm u₁ k = b := by
        by_contra hne
        have hli := (P.linearIndependent_iff_of_isIndivisible_of_pos f
          (P.isIndivisible_of_mem_baseOf f hb) hb.1 hu₁_pos).mpr
          ⟨hne, ((P.isIndivisible_weylGroupToPerm u₁ k).mpr hk_ind) b⟩
        exact lt_asymm (P.apply_root_reflectionPerm_pos_of_mem_baseOf f hf hb hu₁_pos hli) hk_neg
      refine ⟨l₁, hl₁, Nat.lt_succ_self _, ?_⟩
      have hconj := weylGroup.ofIdx_weylGroupToPerm_eq_conj P u₁ k
      rw [heq_bk] at hconj
      simp only [List.map_cons, List.prod_cons]
      calc u₁ * weylGroup.ofIdx P k
          = (u₁ * weylGroup.ofIdx P k * u₁⁻¹) * u₁ := by group
        _ = weylGroup.ofIdx P b * u₁ := by rw [← hconj]

/-- An element of `P.weylGroup` that keeps every root of `baseOf P.root (f : M →+ R)` `f`-positive
is the identity. -/
theorem weylGroup.eq_one_of_forall_mem_baseOf_pos (f : Dual R M) (hf : ∀ i, f (P.root i) ≠ 0)
    {w : P.weylGroup}
    (hw : ∀ a ∈ baseOf P.root (f : M →+ R), 0 < f (P.root (P.weylGroupToPerm w a))) :
    w = 1 := by
  classical
  set Δ := baseOf P.root (f : M →+ R)
  have hne : {n : ℕ | ∃ l : List ι, (∀ a ∈ l, a ∈ Δ) ∧ l.length = n ∧
      (l.map (weylGroup.ofIdx P)).prod = w}.Nonempty := by
    obtain ⟨l, hl, hp⟩ := P.exists_word_baseOf f hf w
    exact ⟨l.length, l, hl, rfl, hp⟩
  obtain ⟨l, hl, hlen, hprod⟩ := Nat.find_spec hne
  rcases List.eq_nil_or_concat l with rfl | ⟨l₀, a, hconcat⟩
  · simpa using hprod.symm
  · exfalso
    rw [List.concat_eq_append] at hconcat
    subst hconcat
    have hl₀ : ∀ b ∈ l₀, b ∈ Δ := (List.forall_mem_append.mp hl).1
    have ha : a ∈ Δ := (List.forall_mem_append.mp hl).2 a (List.mem_singleton_self a)
    set u := (l₀.map (weylGroup.ofIdx P)).prod
    have hw_eq : u * weylGroup.ofIdx P a = w := by simpa [u] using hprod
    have hua_neg : f (P.root (P.weylGroupToPerm u a)) < 0 := by
      have hwa : 0 < f (P.root (P.weylGroupToPerm (u * weylGroup.ofIdx P a) a)) :=
        hw_eq.symm ▸ hw a ha
      rw [P.weylGroupToPerm_mul_ofIdx_apply, ← P.weylGroup_apply_root,
        root_reflectionPerm, P.reflection_apply_self, smul_neg, P.weylGroup_apply_root,
        map_neg] at hwa
      exact neg_of_neg_pos hwa
    obtain ⟨l', hl', hlen', heq'⟩ :=
      P.exists_shorter_word_of_apply_root_neg f hf l₀ hl₀
        (P.isIndivisible_of_mem_baseOf f ha) ha.1 hua_neg
    have hl'_prod : (l'.map (weylGroup.ofIdx P)).prod = w := by
      calc (l'.map (weylGroup.ofIdx P)).prod
          = ((l'.map (weylGroup.ofIdx P)).prod * weylGroup.ofIdx P a) * weylGroup.ofIdx P a := by
              rw [mul_assoc, weylGroup.ofIdx_mul_self, mul_one]
        _ = u * weylGroup.ofIdx P a := by rw [heq']
        _ = w := hw_eq
    have hle := Nat.find_min' hne ⟨l', hl', rfl, hl'_prod⟩
    rw [← hlen, List.length_append, List.length_singleton] at hle
    omega

end StrictOrdered

end Ordered

end RootPairing
