/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Action
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Negative-root products for Chevalley data

For every valid Dynkin type and every Chevalley datum, each element of the negative-root subgroup
is a product with one factor from each negative root subgroup, in any enumeration without
repetition. This holds on the admissible lattice and in the datum's point group over every
commutative value ring, including nonreduced rings and fields of bad characteristic. It supplies
the existence half of negative-root coordinates without asserting uniqueness for general data or
generation of the ambient Chevalley group.

Rather than repeating the commutator-collection case analysis on negative roots, we choose a word
in the pinned simple Weyl representatives spelling the longest Weyl-group element `w₀`. Conjugation
by that word exchanges the positive and negative root subgroups up to integral signs on additive
parameters, transporting `ChevalleyDatum.mem_positiveSubgroup_iff_exists_prod` from
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection` directly to arbitrary enumerations
of the negative roots.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17 and Lemma 19.
* R. W. Carter, *Simple Groups of Lie Type*, §§5.3 and 6.4.
-/

public section

open scoped Pointwise
open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

attribute [local instance high] Algebra.toModule

private noncomputable def weylWordGL (w : List (Fin t.rank)) (A : CommAlgCat.{v} ℤ) :
    LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice) :=
  (w.map fun i => kostantWeylGL (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    D.representation D.lattice D.representation_mem_lattice
    (D.isNilpotent_representation_rootGenerator (.inl i))
    (D.isNilpotent_representation_rootGenerator (.inr i)) A).prod

private noncomputable def weylWordSign : List (Fin t.rank) → Fin t.numRoots → ℤˣ
  | [], _ => 1
  | i :: w, γ =>
      t.chevalleyWeylSign ht (t.simpleIndex ht i)
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht w) γ) *
      weylWordSign w γ

private theorem weylWordGL_conj_chevalleyRootSubgroup (w : List (Fin t.rank))
    (γ : Fin t.numRoots) (A : CommAlgCat.{v} ℤ) (u : A) :
    MulAut.conj (D.weylWordGL w A)
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator γ A (ofAdd u)) =
      chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht w) γ) A
        (ofAdd (((weylWordSign (ht := ht) w γ : ℤ) : A) * u)) := by
  induction w with
  | nil =>
    simp [weylWordGL, weylWordSign]
  | cons i w ih =>
    simp only [weylWordGL, List.map_cons, List.prod_cons, map_mul, MulAut.mul_apply] at ih ⊢
    rw [ih, MulAut.conj_apply,
      kostantWeylGL_conj_chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator i,
      geckWeylWordProd_cons, RootPairing.weylGroupToPerm_ofIdx_mul_apply, weylWordSign]
    simp only [Units.val_mul, Int.cast_mul, mul_assoc]

private theorem map_iSup_chevalleyRootSubgroup_conj_weylWordGL (w : List (Fin t.rank))
    (S : Set (Fin t.numRoots)) (A : CommAlgCat.{v} ℤ) :
    Subgroup.map (MulAut.conj (D.weylWordGL w A))
        (⨆ γ ∈ S, (chevalleyRootSubgroup D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A).range) =
      ⨆ γ ∈ (t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht w) '' S,
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator γ A).range := by
  induction w with
  | nil =>
    ext x
    simp [weylWordGL]
  | cons i w ih =>
    simp only [weylWordGL, List.map_cons, List.prod_cons] at ih ⊢
    rw [TauCeti.map_conj_eq_conj_smul, map_mul, mul_smul, ← TauCeti.map_conj_eq_conj_smul,
      ← TauCeti.map_conj_eq_conj_smul, ih,
      map_iSup_chevalleyRootSubgroup_conj_kostantWeylGL D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator i]
    have himg : (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) ''
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht w) '' S) =
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht (i :: w)) '' S := by
      rw [← Set.image_comp, geckWeylWordProd_cons]
      exact Set.image_congr fun δ _ =>
        (RootPairing.weylGroupToPerm_ofIdx_mul_apply _ _ _ δ).symm
    rw [himg]

/-- Every element of the negative lattice subgroup has a root-product expression, for every valid
Dynkin type. The list enumerates all negative roots without repetition, in any order; no field or
characteristic restriction is needed. -/
theorem mem_negativeSubgroup_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : CommAlgCat.{v} ℤ)
    (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice)) :
    g ∈ D.negativeSubgroup A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A (u γ)).prod =
        g := by
  constructor
  · intro hg
    let P := t.simplyConnectedRootDatum ht
    let b := t.simplyConnectedBase ht
    let _ := t.isReduced_simplyConnectedRootDatum ht
    obtain ⟨l₀, hl₀⟩ := t.geckWeylWordProd_surjective ht (longestElement P b)
    let σ : Equiv.Perm (Fin t.numRoots) := P.weylGroupToPerm (longestElement P b)
    have hσ_inv : Function.Involutive σ := weylGroupToPerm_longestElement_involutive P b
    have hneg_eq : negRoots (t.rationalRootSystem ht) (t.rationalBase ht) = negRoots P b := by
      rw [← compl_posRoots, posRoots_rationalRootSystem, compl_posRoots]
    have hconj_sub : Subgroup.map (MulAut.conj (D.weylWordGL l₀ A)) (D.positiveSubgroup A) =
        D.negativeSubgroup A := by
      rw [D.positiveSubgroup_eq_iSup, D.negativeSubgroup_eq_iSup,
        D.map_iSup_chevalleyRootSubgroup_conj_weylWordGL l₀ _ A, hl₀,
        posRoots_rationalRootSystem, hneg_eq, image_weylGroupToPerm_longestElement_posRoots P b]
    obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp (hconj_sub.symm ▸ hg)
    simp only [MonoidHom.coe_ofClass] at hqg
    have hl' : (l.map σ).Nodup := hl.map σ.injective
    have hcover' : ∀ γ, γ ∈ l.map σ ↔
        γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      intro γ
      rw [posRoots_rationalRootSystem]
      constructor
      · intro hγ
        obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
        exact mapsTo_negRoots_posRoots_longestElement P b (hneg_eq ▸ (hcover δ).mp hδ)
      · intro hγ
        refine List.mem_map.mpr ⟨σ γ, ?_, hσ_inv γ⟩
        exact (hcover (σ γ)).mpr
          (hneg_eq.symm ▸ mapsTo_posRoots_negRoots_longestElement P b hγ)
    obtain ⟨v, hv⟩ := (D.mem_positiveSubgroup_iff_exists_prod (l.map σ) hl' hcover' A q).mp hq
    refine ⟨fun δ =>
      ofAdd (((weylWordSign (ht := ht) l₀ (σ δ) : ℤ) : A) * toAdd (v (σ δ))), ?_⟩
    have hprod := congrArg (MulAut.conj (D.weylWordGL l₀ A)) hv
    rw [hqg, map_list_prod, List.map_map, List.map_map] at hprod
    refine (congrArg List.prod (List.map_congr_left fun δ _ => ?_)).symm.trans hprod
    dsimp only [Function.comp_def]
    rw [← ofAdd_toAdd (v (σ δ)), D.weylWordGL_conj_chevalleyRootSubgroup l₀ (σ δ) A, hl₀]
    exact congrArg₂
      (fun γ z => chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator γ A z)
      (hσ_inv δ) rfl
  · rintro ⟨u, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    exact D.chevalleyRootSubgroup_mem_negativeSubgroup A ((hcover γ).mp hγ) (u γ)

/-- Every negative point of a Chevalley datum is an ordered product with one factor from each
negative root subgroup, in any duplicate-free enumeration of the negative roots. -/
theorem mem_negativePoints_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (g : D.points A) :
    g ∈ D.negativePoints A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => D.rootSubgroupPoints γ A (u γ)).prod = g := by
  constructor
  · intro hg
    obtain ⟨q, hq, hmatrix⟩ := D.mem_negativePoints_iff.mp hg
    obtain ⟨u, hu⟩ :=
      (D.mem_negativeSubgroup_iff_exists_prod l hl hcover (CommAlgCat.of ℤ A) q).mp hq
    refine ⟨u, (D.points A).subtype_injective ?_⟩
    have h := congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply,
      D.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe, hmatrix] using h
  · rintro ⟨u, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    exact D.rootSubgroupPoints_mem_negativePoints A ((hcover γ).mp hγ) (u γ)

end TauCeti.DynkinType.ChevalleyDatum
