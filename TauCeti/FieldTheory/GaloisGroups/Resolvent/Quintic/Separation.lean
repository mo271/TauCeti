/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Basic

import TauCeti.FieldTheory.AbelRuffini
import TauCeti.FieldTheory.GaloisGroups.Quintic
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Solvable

/-!
# Separation of the quintic `F₂₀` resolvent and Dummit's criterion

In `TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Solvable`, the solvability criterion for a
monic irreducible separable quintic `f` over a field `F` requires separate evidence that the
specialized `F₂₀` resolvent sextic `TauCeti.quinticF20Spec.specialize F f` is separable. Over
`𝔽₅` this hypothesis cannot be dropped: the Artin–Schreier quintic `X⁵ - X - 1` is irreducible and
separable, yet its resolvent sextic has a root of multiplicity five.

Following R. Chapman's 1992 note on Dummit's paper, this file removes the separation hypothesis
whenever `5 ≠ 0` in `F`: the Galois image of an irreducible separable quintic contains a `5`-cycle
which fixes one of the six cosets of `F₂₀` in `S₅` and cycles the remaining five. Any coincidence
among the six roots of the resolvent sextic propagates along this `5`-cycle until the five moving
values all coincide. Two explicit integral polynomial identities among the orbit values then force
`5 * x₁` to equal the sum of the roots of `f` (valid in every characteristic, including `2` and
`3`), placing a root of `f` in `F` once `5 ≠ 0` and contradicting irreducibility.

Once separation is established, three consequences follow immediately:

* **Dummit's group criterion without separation evidence**: away from characteristic `5`, the
  Galois group of a monic separable irreducible quintic is solvable if and only if its `F₂₀`
  resolvent sextic has a root in `F`.
* **The `(1, 5)`-factorization**: when that resolvent sextic has a root `a : F`, the Galois image
  lies between `5T1` and `5T3 = F₂₀`, so its orbits on `S₅ / F₂₀` have sizes `1` and `5`. By the
  resolvent factorization theorem, the sextic splits as `(X - C a) * g` with `g` monic irreducible
  of degree `5`; in particular, the root `a` in `F` is unique.
* **Dummit's radical criterion (Theorem 1)**: combining with the radical criterion in
  `TauCeti.FieldTheory.AbelRuffini`, over a field of characteristic zero a monic irreducible
  quintic has its roots expressible by radicals if and only if its `F₂₀` resolvent sextic has a
  root in `F`.

## Main results

* `TauCeti.separable_specialize_quinticF20Spec`: **Chapman's separation theorem** — over any field
  with `[NeZero (5 : F)]`, the `F₂₀` resolvent sextic of a monic separable irreducible quintic is
  separable.
* `TauCeti.isSolvable_gal_iff_exists_isRoot_quinticF20`: solvability of `f.Gal` via a root of the
  resolvent sextic in `F`, with no separation hypothesis.
* `TauCeti.exists_monic_irreducible_specialize_quinticF20Spec_eq_X_sub_C_mul`: when the resolvent
  sextic has a root `a : F`, it factors as `(X - C a) * g` with `g` monic irreducible of degree `5`.
* `TauCeti.eq_of_isRoot_specialize_quinticF20Spec`: a root of the resolvent sextic in `F` is
  unique.
* `TauCeti.forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20`: **Dummit's criterion
  for quintics** — in characteristic zero, all roots of a monic irreducible quintic lie in
  `solvableByRad F Ω` if and only if its resolvent sextic has a root in `F`.
* `TauCeti.exists_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20`: the single-root form of
  Dummit's criterion for irreducible quintics.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), Theorem 1,
  p. 389.
* R. Chapman, note on the distinctness of roots of Dummit's resolvent sextic (1992).
-/

public section

open Equiv Equiv.Perm Polynomial MulAction

namespace TauCeti

/-! ### Orbit representatives and the `5`-cycle action on `S₅ / F₂₀` -/

-- The five nontrivial coset representatives of `F₂₀` in `S₅`, ordered along the `5`-cycle
-- induced by left multiplication by `finRotate 5`.
private def cycleRep : Fin 5 → Perm (Fin 5)
  | 0 => swap 2 3
  | 1 => swap 3 4
  | 2 => swap 2 3 * swap 3 4
  | 3 => swap 2 4
  | 4 => swap 3 4 * swap 2 3

private theorem cycleRep_mem_orbitRepresentatives (k : Fin 5) :
    cycleRep k ∈ quinticF20OrbitRepresentatives := by
  fin_cases k <;> simp [cycleRep, mem_quinticF20OrbitRepresentatives]

private theorem mem_orbitRepresentatives_iff {σ : Perm (Fin 5)} :
    σ ∈ quinticF20OrbitRepresentatives ↔ σ = 1 ∨ ∃ k : Fin 5, σ = cycleRep k := by
  rw [mem_quinticF20OrbitRepresentatives]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inr ⟨3, rfl⟩
    · exact Or.inr ⟨2, rfl⟩
    · exact Or.inr ⟨4, rfl⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · exact Or.inl rfl
    · fin_cases k <;> simp [cycleRep]

private theorem cycleRep_ne_one (k : Fin 5) : cycleRep k ≠ 1 := by
  fin_cases k <;> decide

private theorem cycleRep_injective : Function.Injective cycleRep := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

-- The six orbit representatives map injectively to distinct renamed invariants.
private theorem rename_quinticF20Invariant_injOn :
    Set.InjOn (fun σ : Perm (Fin 5) => MvPolynomial.rename (⇑σ) quinticF20Invariant)
      (quinticF20OrbitRepresentatives : Set (Perm (Fin 5))) := by
  have himg : (quinticF20OrbitRepresentatives.image
      (fun σ : Perm (Fin 5) => MvPolynomial.rename (⇑σ) quinticF20Invariant)).card = 6 := by
    rw [← renameOrbit_quinticF20Invariant, card_renameOrbit_quinticF20Invariant]
  exact Finset.card_image_iff.mp (by rw [himg, card_quinticF20OrbitRepresentatives])

private theorem coset_eq_one_or_cycleRep (q : Perm (Fin 5) ⧸ quinticF20Spec.H) :
    q = ((1 : Perm (Fin 5)) : Perm (Fin 5) ⧸ quinticF20Spec.H) ∨
      ∃ k : Fin 5, q = (cycleRep k : Perm (Fin 5)) := by
  induction q using QuotientGroup.induction_on with | H σ =>
    have hmem : MvPolynomial.rename (⇑σ) quinticF20Invariant ∈
        MvPolynomial.renameOrbit quinticF20Invariant :=
      (MvPolynomial.mem_renameOrbit _ _).mpr ⟨σ, rfl⟩
    rw [renameOrbit_quinticF20Invariant, Finset.mem_image] at hmem
    obtain ⟨τ, hτ, hren⟩ := hmem
    have hcos :
        (σ : Perm (Fin 5) ⧸ quinticF20Spec.H) = (τ : Perm (Fin 5) ⧸ quinticF20Spec.H) := by
      rw [QuotientGroup.eq, ← quinticF20Spec.renameStabilizer_eq, quinticF20Spec_Φ]
      exact (MvPolynomial.rename_eq_rename_iff quinticF20Invariant σ τ).mp hren.symm
    rcases mem_orbitRepresentatives_iff.mp hτ with rfl | ⟨k, rfl⟩
    · exact Or.inl hcos
    · exact Or.inr ⟨k, hcos⟩

private theorem cycleRep_coset_ne_one (k : Fin 5) :
    (cycleRep k : Perm (Fin 5) ⧸ quinticF20Spec.H) ≠
      ((1 : Perm (Fin 5)) : Perm (Fin 5) ⧸ quinticF20Spec.H) := by
  intro h
  rw [QuotientGroup.eq, ← quinticF20Spec.renameStabilizer_eq, quinticF20Spec_Φ] at h
  have hren := (MvPolynomial.rename_eq_rename_iff quinticF20Invariant (cycleRep k) 1).mpr h
  have heq := rename_quinticF20Invariant_injOn (cycleRep_mem_orbitRepresentatives k)
    (mem_quinticF20OrbitRepresentatives.mpr (Or.inl rfl)) hren
  exact cycleRep_ne_one k heq

private theorem cycleRep_coset_injective :
    Function.Injective (fun k : Fin 5 => (cycleRep k : Perm (Fin 5) ⧸ quinticF20Spec.H)) := by
  intro i j hij
  rw [QuotientGroup.eq, ← quinticF20Spec.renameStabilizer_eq, quinticF20Spec_Φ] at hij
  have hren := (MvPolynomial.rename_eq_rename_iff quinticF20Invariant (cycleRep i) (cycleRep j)).mpr
    hij
  have heq := rename_quinticF20Invariant_injOn (cycleRep_mem_orbitRepresentatives i)
    (cycleRep_mem_orbitRepresentatives j) hren
  exact cycleRep_injective heq

-- Both generators of `5T3 = F₂₀` lie in `quinticF20Spec.H`.
private theorem finRotate_mem_quinticF20Spec_H : finRotate 5 ∈ quinticF20Spec.H := by
  rw [quinticF20Spec_H, referenceSubgroup_five_two]
  exact Subgroup.subset_closure (by simp)

private theorem formPerm_mem_quinticF20Spec_H :
    ([0, 1, 3, 2] : List (Fin 5)).formPerm ∈ quinticF20Spec.H := by
  rw [quinticF20Spec_H, referenceSubgroup_five_two]
  exact Subgroup.subset_closure (by simp)

private theorem finRotate_smul_cycleRep (k : Fin 5) :
    finRotate 5 • (cycleRep k : Perm (Fin 5) ⧸ quinticF20Spec.H) =
      (cycleRep (k + 1) : Perm (Fin 5) ⧸ quinticF20Spec.H) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  have hc : finRotate 5 ∈ quinticF20Spec.H := finRotate_mem_quinticF20Spec_H
  have hg : ([0, 1, 3, 2] : List (Fin 5)).formPerm ∈ quinticF20Spec.H :=
    formPerm_mem_quinticF20Spec_H
  have hmem : ∀ p : Perm (Fin 5),
      p = finRotate 5 ∨ p = ([0, 1, 3, 2] : List (Fin 5)).formPerm ∨
        p = finRotate 5 ^ 4 * ([0, 1, 3, 2] : List (Fin 5)).formPerm ^ 3 →
      p ∈ quinticF20Spec.H := by
    rintro p (rfl | rfl | rfl)
    · exact hc
    · exact hg
    · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hc 4) (Subgroup.pow_mem _ hg 3)
  rw [← inv_mem_iff, mul_inv_rev, inv_inv]
  fin_cases k
  · exact hmem _ (Or.inl (by decide))
  · exact hmem _ (Or.inr (Or.inr (by decide)))
  · exact hmem _ (Or.inr (Or.inr (by decide)))
  · exact hmem _ (Or.inr (Or.inl (by decide)))
  · exact hmem _ (Or.inr (Or.inl (by decide)))

private theorem rename_finRotate_mul_cycleRep (k : Fin 5) :
    MvPolynomial.rename (⇑(finRotate 5 * cycleRep k)) quinticF20Invariant =
      MvPolynomial.rename (⇑(cycleRep (k + 1))) quinticF20Invariant := by
  have h := finRotate_smul_cycleRep k
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    ← quinticF20Spec.renameStabilizer_eq, quinticF20Spec_Φ] at h
  exact (MvPolynomial.rename_eq_rename_iff quinticF20Invariant _ _).mpr h

private theorem rename_finRotate_quinticF20 :
    MvPolynomial.rename (⇑(finRotate 5)) quinticF20Invariant = quinticF20Invariant :=
  (rename_quinticF20Invariant_eq_self_iff (finRotate 5)).mpr
    (quinticF20Spec_H ▸ finRotate_mem_quinticF20Spec_H)

/-! ### Reference subgroups of degree five -/

private theorem finRotate_mem_referenceSubgroup_five (j : TransitiveGroupIndex 5) :
    finRotate 5 ∈ referenceSubgroup 5 j := by
  have h0 : finRotate 5 ∈ referenceSubgroup 5 ⟨0, by simp⟩ := by
    rw [referenceSubgroup_five_zero]
    exact Subgroup.subset_closure (Set.mem_singleton _)
  obtain ⟨j, hjlt⟩ := j
  rw [numTransitiveGroups_five] at hjlt
  interval_cases j
  · exact h0
  · exact referenceSubgroup_five_zero_le_referenceSubgroup_five_one h0
  · exact referenceSubgroup_five_zero_le_referenceSubgroup_five_two h0
  · rw [referenceSubgroup_five_three]
    exact referenceSubgroup_five_zero_le_alternatingGroup h0
  · rw [referenceSubgroup_five_four]
    exact Subgroup.mem_top _

private theorem referenceSubgroup_five_le_quinticF20Spec_H {j : TransitiveGroupIndex 5}
    (hj : (j : ℕ) < 3) : referenceSubgroup 5 j ≤ quinticF20Spec.H := by
  rw [quinticF20Spec_H]
  obtain ⟨j, hjlt⟩ := j
  interval_cases j
  · exact referenceSubgroup_five_zero_le_referenceSubgroup_five_two
  · exact referenceSubgroup_five_one_le_referenceSubgroup_five_two
  · exact le_rfl

private theorem exists_numbering_map_range_eq_referenceSubgroup
    {F : Type*} [Field F] {f : F[X]} (hsep : f.Separable) (hirr : Irreducible f)
    (hdeg : f.natDegree = 5) :
    let _ : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
    ∃ (j : TransitiveGroupIndex 5) (e : f.rootSet f.SplittingField ≃ Fin 5),
      HasGaloisLabel f j ∧
        (Gal.galActionHom f f.SplittingField).range.map
          (e.permCongrHom : _ →* Perm (Fin 5)) = referenceSubgroup 5 j := by
  let _ : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_five hsep hirr hdeg
  obtain ⟨e₀⟩ := nonempty_rootSet_equiv_fin hsep (SplittingField.splits f)
  let e₁ : f.rootSet f.SplittingField ≃ Fin 5 := e₀.trans (finCongr hdeg)
  have hl := hj.transitiveGroupLabel e₁
  obtain ⟨τ, hτ⟩ := hl.exists_map_permCongrHom_eq
  refine ⟨j, e₁.trans τ, hj, ?_⟩
  have hcomp : ((e₁.trans τ).permCongrHom : _ →* Perm (Fin 5)) =
      τ.permCongrHom.toMonoidHom.comp e₁.permCongrHom.toMonoidHom := by
    ext σ x
    simp
  rw [hcomp, ← Subgroup.map_map]
  exact hτ

/-! ### Cycle propagation and Chapman's polynomial identities -/

private theorem map_eval₂_rename_quinticF20Invariant
    {E : Type*} [CommRing E] (x : Fin 5 → E) (ϕ : E →+* E)
    (hϕx : ∀ i : Fin 5, ϕ (x i) = x (finRotate 5 i)) (σ : Perm (Fin 5)) :
    ϕ (MvPolynomial.eval₂ (Int.castRingHom E) x
        (MvPolynomial.rename (⇑σ) quinticF20Invariant)) =
      MvPolynomial.eval₂ (Int.castRingHom E) x
        (MvPolynomial.rename (⇑(finRotate 5 * σ)) quinticF20Invariant) := by
  rw [MvPolynomial.hom_eval₂,
    RingHom.ext_int (ϕ.comp (Int.castRingHom E)) (Int.castRingHom E),
    MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename]
  congr 1
  funext i
  exact hϕx (σ i)

-- Propagating a collision between the fixed invariant value and one of the five moving orbit values
-- along the `5`-cycle induced by `ϕ`.
private theorem eval_cycleRep_eq_of_one_eq
    {E : Type*} [CommRing E] (x : Fin 5 → E) (ϕ : E →+* E)
    (hϕx : ∀ i : Fin 5, ϕ (x i) = x (finRotate 5 i)) {i : Fin 5}
    (heq : MvPolynomial.eval₂ (Int.castRingHom E) x
        (MvPolynomial.rename (⇑(1 : Perm (Fin 5))) quinticF20Invariant) =
      MvPolynomial.eval₂ (Int.castRingHom E) x
        (MvPolynomial.rename (⇑(cycleRep i)) quinticF20Invariant)) :
    ∀ k l : Fin 5,
      MvPolynomial.eval₂ (Int.castRingHom E) x
          (MvPolynomial.rename (⇑(cycleRep k)) quinticF20Invariant) =
        MvPolynomial.eval₂ (Int.castRingHom E) x
          (MvPolynomial.rename (⇑(cycleRep l)) quinticF20Invariant) := by
  let v₀ := MvPolynomial.eval₂ (Int.castRingHom E) x
    (MvPolynomial.rename (⇑(1 : Perm (Fin 5))) quinticF20Invariant)
  let y : Fin 5 → E := fun k =>
    MvPolynomial.eval₂ (Int.castRingHom E) x
      (MvPolynomial.rename (⇑(cycleRep k)) quinticF20Invariant)
  have hfix : ϕ v₀ = v₀ := by
    dsimp only [v₀]
    rw [map_eval₂_rename_quinticF20Invariant x ϕ hϕx 1, mul_one, rename_finRotate_quinticF20]
    simp
  have hstep : ∀ k : Fin 5, ϕ (y k) = y (k + 1) := fun k => by
    dsimp only [y]
    rw [map_eval₂_rename_quinticF20Invariant x ϕ hϕx (cycleRep k), rename_finRotate_mul_cycleRep k]
  have hs : ∀ {a : Fin 5}, v₀ = y a → v₀ = y (a + 1) := fun h => by rw [← hfix, h, hstep]
  have e1 : v₀ = y (i + 1) := hs heq
  have e2 : v₀ = y (i + 2) := by simpa [add_assoc] using hs e1
  have e3 : v₀ = y (i + 3) := by simpa [add_assoc] using hs e2
  have e4 : v₀ = y (i + 4) := by simpa [add_assoc] using hs e3
  have hall : ∀ k : Fin 5, v₀ = y k := by
    intro k
    have hcases : ∀ k i : Fin 5,
        k = i ∨ k = i + 1 ∨ k = i + 2 ∨ k = i + 3 ∨ k = i + 4 := by decide
    rcases hcases k i with rfl | rfl | rfl | rfl | rfl
    · exact heq
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  intro k l
  exact (hall k).symm.trans (hall l)

-- Propagating a collision between two distinct moving orbit values along the `5`-cycle `ϕ`.
private theorem eval_cycleRep_eq_of_ne_eq
    {E : Type*} [CommRing E] (x : Fin 5 → E) (ϕ : E →+* E)
    (hϕx : ∀ i : Fin 5, ϕ (x i) = x (finRotate 5 i)) {i j : Fin 5} (hij : i ≠ j)
    (heq : MvPolynomial.eval₂ (Int.castRingHom E) x
        (MvPolynomial.rename (⇑(cycleRep i)) quinticF20Invariant) =
      MvPolynomial.eval₂ (Int.castRingHom E) x
        (MvPolynomial.rename (⇑(cycleRep j)) quinticF20Invariant)) :
    ∀ k l : Fin 5,
      MvPolynomial.eval₂ (Int.castRingHom E) x
          (MvPolynomial.rename (⇑(cycleRep k)) quinticF20Invariant) =
        MvPolynomial.eval₂ (Int.castRingHom E) x
          (MvPolynomial.rename (⇑(cycleRep l)) quinticF20Invariant) := by
  let y : Fin 5 → E := fun k =>
    MvPolynomial.eval₂ (Int.castRingHom E) x
      (MvPolynomial.rename (⇑(cycleRep k)) quinticF20Invariant)
  have hstep : ∀ k : Fin 5, ϕ (y k) = y (k + 1) := fun k => by
    dsimp only [y]
    rw [map_eval₂_rename_quinticF20Invariant x ϕ hϕx (cycleRep k), rename_finRotate_mul_cycleRep k]
  have hs : ∀ {a b : Fin 5}, y a = y b → y (a + 1) = y (b + 1) :=
    fun h => by rw [← hstep _, ← hstep _, h]
  have e1 : y (i + 1) = y (j + 1) := hs heq
  have e2 : y (i + 2) = y (j + 2) := by simpa [add_assoc] using hs e1
  have e3 : y (i + 3) = y (j + 3) := by simpa [add_assoc] using hs e2
  have e4 : y (i + 4) = y (j + 4) := by simpa [add_assoc] using hs e3
  have hshift : ∀ a : Fin 5, y a = y (a + (j - i)) := by
    intro a
    have hcases : ∀ a i : Fin 5,
        a = i ∨ a = i + 1 ∨ a = i + 2 ∨ a = i + 3 ∨ a = i + 4 := by decide
    rcases hcases a i with rfl | rfl | rfl | rfl | rfl
    · simpa [add_sub_cancel] using heq
    · have : i + 1 + (j - i) = j + 1 := by abel
      rw [this]; exact e1
    · have : i + 2 + (j - i) = j + 2 := by abel
      rw [this]; exact e2
    · have : i + 3 + (j - i) = j + 3 := by abel
      rw [this]; exact e3
    · have : i + 4 + (j - i) = j + 4 := by abel
      rw [this]; exact e4
  set d : Fin 5 := j - i
  have hd : d ≠ 0 := sub_ne_zero.mpr hij.symm
  have s1 : y 0 = y d := by simpa using hshift 0
  have s2 : y 0 = y (d + d) := s1.trans (hshift d)
  have s3 : y 0 = y (d + d + d) := s2.trans (hshift (d + d))
  have s4 : y 0 = y (d + d + d + d) := s3.trans (hshift (d + d + d))
  have hall : ∀ k : Fin 5, y 0 = y k := by
    intro k
    have hgen : ∀ d : Fin 5, d ≠ 0 → ∀ k : Fin 5,
        k = 0 ∨ k = d ∨ k = d + d ∨ k = d + d + d ∨ k = d + d + d + d := by decide
    rcases hgen d hd k with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact s1
    · exact s2
    · exact s3
    · exact s4
  intro k l
  exact (hall k).symm.trans (hall l)

private theorem chapman_identity_one {R : Type*} [CommRing R] (x : Fin 5 → R) :
    MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.rename (⇑(swap (2 : Fin 5) 3))
        quinticF20Invariant) -
      MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename (⇑(swap (2 : Fin 5) 3 * swap (3 : Fin 5) 4)) quinticF20Invariant) =
      (x 0 - x 3) * (x 2 - x 4) *
        ((x 1 - x 0) * (x 1 - x 3) - (x 1 - x 2) * (x 1 - x 4)) := by
  rw [eval₂_rename_quinticF20Invariant, eval₂_rename_quinticF20Invariant]
  have h1 : (swap (2 : Fin 5) 3) 0 = 0 ∧ (swap (2 : Fin 5) 3) 1 = 1 ∧
      (swap (2 : Fin 5) 3) 2 = 3 ∧ (swap (2 : Fin 5) 3) 3 = 2 ∧
      (swap (2 : Fin 5) 3) 4 = 4 := by decide
  have h2 : (swap (2 : Fin 5) 3 * swap (3 : Fin 5) 4) 0 = 0 ∧
      (swap (2 : Fin 5) 3 * swap (3 : Fin 5) 4) 1 = 1 ∧
      (swap (2 : Fin 5) 3 * swap (3 : Fin 5) 4) 2 = 3 ∧
      (swap (2 : Fin 5) 3 * swap (3 : Fin 5) 4) 3 = 4 ∧
      (swap (2 : Fin 5) 3 * swap (3 : Fin 5) 4) 4 = 2 := by decide
  simp only [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2,
    h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2]
  ring

private theorem chapman_identity_two {R : Type*} [CommRing R] (x : Fin 5 → R) :
    MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.rename (⇑(swap (2 : Fin 5) 4))
        quinticF20Invariant) -
      MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename (⇑(swap (3 : Fin 5) 4 * swap (2 : Fin 5) 3)) quinticF20Invariant) =
      (x 2 - x 3) * (x 0 - x 4) *
        ((x 1 - x 2) * (x 1 - x 3) - (x 1 - x 0) * (x 1 - x 4)) := by
  rw [eval₂_rename_quinticF20Invariant, eval₂_rename_quinticF20Invariant]
  have h1 : (swap (2 : Fin 5) 4) 0 = 0 ∧ (swap (2 : Fin 5) 4) 1 = 1 ∧
      (swap (2 : Fin 5) 4) 2 = 4 ∧ (swap (2 : Fin 5) 4) 3 = 3 ∧
      (swap (2 : Fin 5) 4) 4 = 2 := by decide
  have h2 : (swap (3 : Fin 5) 4 * swap (2 : Fin 5) 3) 0 = 0 ∧
      (swap (3 : Fin 5) 4 * swap (2 : Fin 5) 3) 1 = 1 ∧
      (swap (3 : Fin 5) 4 * swap (2 : Fin 5) 3) 2 = 4 ∧
      (swap (3 : Fin 5) 4 * swap (2 : Fin 5) 3) 3 = 2 ∧
      (swap (3 : Fin 5) 4 * swap (2 : Fin 5) 3) 4 = 3 := by decide
  simp only [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2,
    h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2]
  ring

-- Characteristic-uniform algebraic deduction (valid in every integral domain, including
-- characteristics `2` and `3`).
private theorem five_mul_eq_sum_of_chapman_eq {R : Type*} [CommRing R] [IsDomain R]
    {x : Fin 5 → R} (hx : Function.Injective x)
    (h1 : MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename (⇑(swap (2 : Fin 5) 3)) quinticF20Invariant) =
      MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename (⇑(swap (2 : Fin 5) 3 * swap (3 : Fin 5) 4)) quinticF20Invariant))
    (h2 : MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename (⇑(swap (2 : Fin 5) 4)) quinticF20Invariant) =
      MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename (⇑(swap (3 : Fin 5) 4 * swap (2 : Fin 5) 3)) quinticF20Invariant)) :
    5 * x 1 = ∑ i : Fin 5, x i := by
  have hne : ∀ {i j : Fin 5}, i ≠ j → x i - x j ≠ 0 :=
    fun hij h => hij (hx (sub_eq_zero.mp h))
  have hid1 := chapman_identity_one x
  rw [sub_eq_zero.mpr h1] at hid1
  have hbr1 : (x 1 - x 0) * (x 1 - x 3) - (x 1 - x 2) * (x 1 - x 4) = 0 :=
    (mul_eq_zero.mp hid1.symm).resolve_left (mul_ne_zero (hne (by decide)) (hne (by decide)))
  have hid2 := chapman_identity_two x
  rw [sub_eq_zero.mpr h2] at hid2
  have hbr2 : (x 1 - x 2) * (x 1 - x 3) - (x 1 - x 0) * (x 1 - x 4) = 0 :=
    (mul_eq_zero.mp hid2.symm).resolve_left (mul_ne_zero (hne (by decide)) (hne (by decide)))
  set a := x 1 - x 0
  set b := x 1 - x 2
  set c := x 1 - x 3
  set d := x 1 - x 4
  have hcd : c + d = 0 := by
    have hsub : (a - b) * (c + d) = 0 := by linear_combination hbr1 - hbr2
    have hab_ne : a - b ≠ 0 := by
      have : a - b = x 2 - x 0 := by simp [a, b]
      rw [this]
      exact hne (by decide)
    exact (mul_eq_zero.mp hsub).resolve_left hab_ne
  have hab : a + b = 0 := by
    have hadd : (a + b) * (c - d) = 0 := by linear_combination hbr1 + hbr2
    have hcd_ne : c - d ≠ 0 := by
      have : c - d = x 4 - x 3 := by simp [c, d]
      rw [this]
      exact hne (by decide)
    exact (mul_eq_zero.mp hadd).resolve_right hcd_ne
  rw [Fin.sum_univ_five]
  linear_combination hab + hcd

-- Any subgroup `G ≤ quinticF20Spec.H` containing `finRotate 5` splits `S₅ / F₂₀` into two orbits:
-- the fixed point `{1 · H}` and the `5`-cycle `{cycleRep k · H}`.
private theorem orbits_quinticF20Spec_of_le
    {G : Subgroup (Perm (Fin 5))} (hrot : finRotate 5 ∈ G) (hG_le : G ≤ quinticF20Spec.H) :
    let q₀ : Perm (Fin 5) ⧸ quinticF20Spec.H := ((1 : Perm (Fin 5)) : _)
    let q₁ : Fin 5 → Perm (Fin 5) ⧸ quinticF20Spec.H := fun k => (cycleRep k : Perm (Fin 5))
    let ω₀ : MulAction.orbitRel.Quotient G (Perm (Fin 5) ⧸ quinticF20Spec.H) := Quotient.mk _ q₀
    let ω₁ : MulAction.orbitRel.Quotient G (Perm (Fin 5) ⧸ quinticF20Spec.H) :=
      Quotient.mk _ (q₁ 0)
    ω₀ ≠ ω₁ ∧
      (∀ ω, ω = ω₀ ∨ ω = ω₁) ∧
      MulAction.orbit G (q₁ 0) = Set.range q₁ := by
  intro q₀ q₁ ω₀ ω₁
  have hfix : ∀ g : G, g • q₀ = q₀ := by
    intro g
    rw [subgroup_smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
      mul_one, inv_mem_iff]
    exact hG_le g.2
  have hmem_orbit₁ : ∀ k : Fin 5, q₁ k ∈ MulAction.orbit G (q₁ 0) := by
    let r : G := ⟨finRotate 5, hrot⟩
    have hstep : ∀ k : Fin 5, q₁ k ∈ MulAction.orbit G (q₁ 0) →
        q₁ (k + 1) ∈ MulAction.orbit G (q₁ 0) := by
      rintro k ⟨g, hg⟩
      refine ⟨r * g, ?_⟩
      dsimp only at hg ⊢
      rw [mul_smul, hg]
      exact finRotate_smul_cycleRep k
    have h0 : q₁ 0 ∈ MulAction.orbit G (q₁ 0) := ⟨1, one_smul _ _⟩
    have h1 := hstep 0 h0
    have h2 := hstep 1 h1
    have h3 := hstep 2 h2
    have h4 := hstep 3 h3
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hq₀_not_mem : q₀ ∉ MulAction.orbit G (q₁ 0) := by
    rintro ⟨g, hg⟩
    have h1 : q₁ 0 = g⁻¹ • q₀ := by
      have := congrArg (g⁻¹ • ·) hg
      simpa using this
    rw [hfix g⁻¹] at h1
    exact cycleRep_coset_ne_one 0 h1
  refine ⟨fun h => hq₀_not_mem (Quotient.exact h), fun ω => ?_, ?_⟩
  · induction ω using Quotient.inductionOn with | h x =>
      rcases coset_eq_one_or_cycleRep x with rfl | ⟨k, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Quotient.sound (hmem_orbit₁ k))
  · ext x
    constructor
    · intro hx
      rcases coset_eq_one_or_cycleRep x with rfl | ⟨k, rfl⟩
      · exact absurd hx hq₀_not_mem
      · exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact hmem_orbit₁ k

/-! ### Main theorems -/

/-- **Separation of the quintic `F₂₀` resolvent** (Chapman's note on Dummit's *Solving solvable
quintics*). Over a field in which `5 ≠ 0`, the specialized resolvent sextic of a monic separable
irreducible quintic is separable.

The hypothesis `[NeZero (5 : F)]` cannot be dropped: over `𝔽₅`, the Artin–Schreier quintic
`X⁵ - X - 1` is irreducible and separable while its resolvent sextic is `(X - 3)(X - 2)⁵`. -/
theorem separable_specialize_quinticF20Spec
    {F : Type*} [Field F] [NeZero (5 : F)] {f : F[X]}
    (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (quinticF20Spec.specialize F f).Separable := by
  let E := f.SplittingField
  let _ : Fact ((f.map (algebraMap F E)).Splits) := ⟨SplittingField.splits f⟩
  let _ : IsGalois F E := IsGalois.of_separable_splitting_field hsep
  obtain ⟨j, e, -, heG⟩ := exists_numbering_map_range_eq_referenceSubgroup hsep hirr hdeg
  let x : Fin 5 → E := fun i => (e.symm i : E)
  have hx_inj : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  -- Lift `finRotate 5 ∈ referenceSubgroup 5 j` to an automorphism `ϕ : E ≃ₐ[F] E`.
  have hrot_mem : finRotate 5 ∈
      (Gal.galActionHom f E).range.map (e.permCongrHom : _ →* Perm (Fin 5)) :=
    heG ▸ finRotate_mem_referenceSubgroup_five j
  simp only [Subgroup.mem_map, MonoidHom.mem_range] at hrot_mem
  obtain ⟨_, ⟨g, rfl⟩, hϕ_eq⟩ := hrot_mem
  obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective f E g
  have hϕx : ∀ i : Fin 5, ϕ.toRingHom (x i) = x (finRotate 5 i) := by
    intro i
    have hi := congrArg (fun p : Perm (Fin 5) => p i) hϕ_eq
    simp only [x]
    rw [← hi]
    simp [Gal.galActionHom_restrict]
  -- Reduce separability of the resolvent sextic to injectivity of `val` on the 6 representatives.
  let val : Perm (Fin 5) → E := fun σ =>
    MvPolynomial.eval₂ (Int.castRingHom E) x (MvPolynomial.rename (⇑σ) quinticF20Invariant)
  rw [← Polynomial.separable_map (algebraMap F E),
    quinticF20Spec.map_specialize_eq_galResolvent_numbering hf hdeg e,
    quinticF20Spec_Φ, ← MvPolynomial.map_universalResolvent_eq_galResolvent,
    universalResolvent_quinticF20Invariant, Polynomial.map_prod]
  have hprod :
      (∏ σ ∈ quinticF20OrbitRepresentatives,
        (X - C (MvPolynomial.rename (⇑σ) quinticF20Invariant)).map
          (MvPolynomial.eval₂Hom (Int.castRingHom E) x)) =
      ∏ σ ∈ quinticF20OrbitRepresentatives, (X - C (val σ)) :=
    Finset.prod_congr rfl fun σ _ => by simp [val]
  rw [hprod, Polynomial.separable_prod_X_sub_C_iff']
  intro σ hσ τ hτ hval
  by_contra hne
  -- Propagate any collision along the `5`-cycle `ϕ` to make all five moving values coincide.
  have halleq : ∀ k l : Fin 5, val (cycleRep k) = val (cycleRep l) := by
    rcases mem_orbitRepresentatives_iff.mp hσ with rfl | ⟨i, rfl⟩ <;>
      rcases mem_orbitRepresentatives_iff.mp hτ with rfl | ⟨j, rfl⟩
    · exact absurd rfl hne
    · exact eval_cycleRep_eq_of_one_eq x ϕ.toRingHom hϕx hval
    · exact eval_cycleRep_eq_of_one_eq x ϕ.toRingHom hϕx hval.symm
    · exact eval_cycleRep_eq_of_ne_eq x ϕ.toRingHom hϕx (fun hij => hne (by rw [hij])) hval
  have h5x1 : 5 * x 1 = ∑ i : Fin 5, x i :=
    five_mul_eq_sum_of_chapman_eq hx_inj (halleq 0 2) (halleq 3 4)
  -- The sum of all five roots is fixed by every `F`-automorphism of `E`, hence lies in `F`.
  have hsum_fixed : ∀ ψ : E ≃ₐ[F] E, ψ (∑ i : Fin 5, x i) = ∑ i : Fin 5, x i := by
    intro ψ
    rw [map_sum]
    let π := e.permCongrHom (Gal.galActionHom f E (Gal.restrict f E ψ))
    refine Fintype.sum_bijective (⇑π) π.bijective _ _ fun i => ?_
    simp [x, π, Gal.galActionHom_restrict]
  obtain ⟨s, hs⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hsum_fixed
  have h5_ne_E : (5 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 5]
    exact (map_ne_zero_iff (algebraMap F E) (algebraMap F E).injective).mpr (NeZero.ne (5 : F))
  have hx1_eq : x 1 = algebraMap F E (s / 5) := by
    rw [map_div₀, map_ofNat]
    exact eq_div_of_mul_eq h5_ne_E (by rw [mul_comm, h5x1, hs])
  have hroot : f.IsRoot (s / 5) := by
    rw [Polynomial.IsRoot, ← map_eq_zero_iff (algebraMap F E) (algebraMap F E).injective,
      ← Polynomial.eval₂_at_apply, ← hx1_eq]
    simpa [aeval_def] using aeval_eq_zero_of_mem_rootSet (e.symm 1).2
  exact hirr.not_isRoot_of_natDegree_ne_one (by omega) hroot

/-- **The `(1, 5)`-factorization of the quintic resolvent sextic.** Over a field with `5 ≠ 0`,
if the `F₂₀` resolvent sextic of a monic separable irreducible quintic `f` has a root `a : F`,
then it factors as `(X - C a) * g` for a monic irreducible quintic `g : F[X]`. -/
theorem exists_monic_irreducible_specialize_quinticF20Spec_eq_X_sub_C_mul
    {F : Type*} [Field F] [NeZero (5 : F)] {f : F[X]}
    (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    {a : F} (ha : (quinticF20Spec.specialize F f).IsRoot a) :
    ∃ g : F[X], g.Monic ∧ Irreducible g ∧ g.natDegree = 5 ∧
      quinticF20Spec.specialize F f = (X - C a) * g := by
  classical
  let _ : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  have hsep_res : (quinticF20Spec.specialize F f).Separable :=
    separable_specialize_quinticF20Spec hf hsep hirr hdeg
  have hres : ResolventSeparationEvidence quinticF20Spec f := ⟨hsep_res⟩
  obtain ⟨j, e, hj, heG⟩ := exists_numbering_map_range_eq_referenceSubgroup hsep hirr hdeg
  have hjlt : (j : ℕ) < 3 :=
    (hj.exists_isRoot_specialize_quinticF20Spec_iff hf hres).mp ⟨a, ha⟩
  let G : Subgroup (Perm (Fin 5)) :=
    (Gal.galActionHom f f.SplittingField).range.map (e.permCongrHom : _ →* Perm (Fin 5))
  have hG : G = referenceSubgroup 5 j := heG
  have hrot : finRotate 5 ∈ G := hG ▸ finRotate_mem_referenceSubgroup_five j
  have hG_le : G ≤ quinticF20Spec.H := hG ▸ referenceSubgroup_five_le_quinticF20Spec_H hjlt
  let q₀ : Perm (Fin 5) ⧸ quinticF20Spec.H := ((1 : Perm (Fin 5)) : _)
  let q₁ : Fin 5 → Perm (Fin 5) ⧸ quinticF20Spec.H := fun k => (cycleRep k : Perm (Fin 5))
  let ω₀ : MulAction.orbitRel.Quotient G (Perm (Fin 5) ⧸ quinticF20Spec.H) := Quotient.mk _ q₀
  let ω₁ : MulAction.orbitRel.Quotient G (Perm (Fin 5) ⧸ quinticF20Spec.H) :=
    Quotient.mk _ (q₁ 0)
  obtain ⟨hω_ne, hω_all, horbit₁⟩ := orbits_quinticF20Spec_of_le hrot hG_le
  -- Transport the two orbits of sizes `1` and `5` to the monic irreducible factors of the sextic.
  let Φ := quinticF20Spec.orbitQuotientEquivFactors hf hdeg e hres
  let p₀ := Φ ω₀
  let p₁ := Φ ω₁
  have hp_ne : p₀ ≠ p₁ := fun h => hω_ne (Φ.injective h)
  have hp_all : ∀ p : (quinticF20Spec.specialize F f).Factors, p = p₀ ∨ p = p₁ := by
    intro p
    rcases hω_all (Φ.symm p) with h | h
    · exact Or.inl (by rw [← Φ.apply_symm_apply p, h])
    · exact Or.inr (by rw [← Φ.apply_symm_apply p, h])
  have hp₁_deg : (p₁ : F[X]).natDegree = 5 := by
    have hcard := quinticF20Spec.natCard_orbit_eq_natDegree_factor hf hdeg e hres ω₁
    rw [← hcard]
    dsimp only [ω₁]
    rw [MulAction.orbitRel.Quotient.orbit_mk, horbit₁,
      ← Nat.card_congr (Equiv.ofInjective q₁ cycleRep_coset_injective)]
    simp
  let pa : (quinticF20Spec.specialize F f).Factors :=
    ⟨X - C a, irreducible_X_sub_C a, monic_X_sub_C a, dvd_iff_isRoot.mpr ha⟩
  have hpa_eq : pa = p₀ := by
    rcases hp_all pa with h | h
    · exact h
    · have hdeg_eq : (pa : F[X]).natDegree = (p₁ : F[X]).natDegree :=
        congrArg (fun (q : (quinticF20Spec.specialize F f).Factors) => (q : F[X]).natDegree) h
      simp [pa, hp₁_deg] at hdeg_eq
  have hp₀_val : (p₀ : F[X]) = X - C a := by rw [← hpa_eq]
  have _ : Finite (quinticF20Spec.specialize F f).Factors :=
    Polynomial.Factors.finite (quinticF20Spec.monic_specialize F f).ne_zero
  let _ : Fintype (quinticF20Spec.specialize F f).Factors := Fintype.ofFinite _
  have huniv : (Finset.univ : Finset (quinticF20Spec.specialize F f).Factors) = {p₀, p₁} := by
    ext p
    simp [hp_all p]
  have hassoc : Associated ((X - C a) * (p₁ : F[X])) (quinticF20Spec.specialize F f) := by
    have hprod := Polynomial.Factors.associated_prod hsep_res.squarefree
    rw [huniv, Finset.prod_pair hp_ne, hp₀_val] at hprod
    exact hprod
  have heq : quinticF20Spec.specialize F f = (X - C a) * (p₁ : F[X]) :=
    (eq_of_monic_of_associated ((monic_X_sub_C a).mul p₁.monic)
      (quinticF20Spec.monic_specialize F f) hassoc).symm
  exact ⟨(p₁ : F[X]), p₁.monic, p₁.irreducible, hp₁_deg, heq⟩

/-- Over a field with `5 ≠ 0`, the `F₂₀` resolvent sextic of a monic separable irreducible
quintic has at most one root in `F`. -/
theorem eq_of_isRoot_specialize_quinticF20Spec
    {F : Type*} [Field F] [NeZero (5 : F)] {f : F[X]}
    (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5)
    {a b : F} (ha : (quinticF20Spec.specialize F f).IsRoot a)
    (hb : (quinticF20Spec.specialize F f).IsRoot b) : a = b := by
  obtain ⟨g, -, hgirr, hgdeg, hfac⟩ :=
    exists_monic_irreducible_specialize_quinticF20Spec_eq_X_sub_C_mul hf hsep hirr hdeg ha
  have hmul : (b - a) * g.eval b = 0 := by
    have := hb
    rw [Polynomial.IsRoot, hfac, eval_mul, eval_sub, eval_X, eval_C] at this
    exact this
  rcases mul_eq_zero.mp hmul with hba | hgb
  · exact (sub_eq_zero.mp hba).symm
  · exact absurd hgb (hgirr.not_isRoot_of_natDegree_ne_one (by omega))

/-- **Dummit's solvability criterion for quintics (group form, without separation hypothesis).**
Over a field with `5 ≠ 0`, a monic separable irreducible quintic has solvable Galois group if and
only if its `F₂₀` resolvent sextic has a root in the base field. -/
theorem isSolvable_gal_iff_exists_isRoot_quinticF20
    {F : Type*} [Field F] [NeZero (5 : F)] {f : F[X]}
    (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    Group.IsSolvable f.Gal ↔ ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a :=
  isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec hf hsep hirr hdeg
    ⟨separable_specialize_quinticF20Spec hf hsep hirr hdeg⟩

/-- **Dummit's criterion for quintics** (Dummit, *Solving solvable quintics*, Theorem 1, with
Chapman's separation argument). In characteristic zero, all roots of a monic irreducible quintic
in a separably closed extension `Ω` (such as `AlgebraicClosure F`) lie in `solvableByRad F Ω` if
and only if its `F₂₀` resolvent sextic has a root in the base field. -/
theorem forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20
    {F : Type*} (Ω : Type*) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω]
    {f : F[X]} (hf : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (∀ x ∈ f.rootSet Ω, x ∈ solvableByRad F Ω) ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  have : NeZero (5 : F) := ⟨by norm_num⟩
  rw [← isSolvable_gal_iff_forall_rootSet_mem_solvableByRad Ω f,
    isSolvable_gal_iff_exists_isRoot_quinticF20 hf hirr.separable hirr hdeg]

/-- **Dummit's criterion for quintics (single-root form).** In characteristic zero, a monic
irreducible quintic has a root in `solvableByRad F Ω` (for any separably closed extension `Ω`)
if and only if its `F₂₀` resolvent sextic has a root in the base field. -/
theorem exists_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20
    {F : Type*} (Ω : Type*) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω]
    {f : F[X]} (hf : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (∃ x ∈ f.rootSet Ω, x ∈ solvableByRad F Ω) ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  have : NeZero (5 : F) := ⟨by norm_num⟩
  rw [← isSolvable_gal_iff_exists_rootSet_mem_solvableByRad Ω hirr,
    isSolvable_gal_iff_exists_isRoot_quinticF20 hf hirr.separable hirr hdeg]

end TauCeti
