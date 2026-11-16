/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2

/-!
# Positive-root products for Chevalley data

For every valid Dynkin type and every Chevalley datum, each element of the positive-root subgroup
is a product with one factor from each positive root subgroup, in any enumeration without
repetition. This works on the admissible lattice and in the datum's point group over every
commutative value ring, including rings with nilpotents and fields of bad characteristic. It is
the existence part of positive-root coordinates, without asserting uniqueness for general data or
generation of the whole Chevalley group.

Outside type `G₂`, height-raising commutators collect factors in any order via
`DynkinType.mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod`. In type `G₂`, the
native six-root table order collects factors via
`DynkinType.mem_biSup_posRoots_g2_iff_exists_list_prod_map`, identified with `posRoots` of the
rational system by `DynkinType.mem_posRoots_rational_g2_iff`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, §5.3.
-/

public section

open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

attribute [local instance high] Algebra.toModule

/-- Every element of the positive lattice subgroup has a root-product expression, for every valid
Dynkin type. The list enumerates all positive roots without repetition, in any order; no field or
characteristic restriction is needed. -/
theorem mem_positiveSubgroup_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : CommAlgCat.{v} ℤ)
    (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice)) :
    g ∈ D.positiveSubgroup A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A (u γ)).prod =
        g := by
  classical
  rw [D.positiveSubgroup_eq_iSup A]
  by_cases htG2 : t = G2
  · subst t
    let toSix : {γ // γ ∈ l} → Fin 6 := fun γ =>
      ⟨γ.1.val, (mem_posRoots_rational_g2_iff ht γ.1).mp ((hcover γ.1).mp γ.2)⟩
    let fromSix : Fin 6 → Fin G2.numRoots := fun i => Fin.castAdd 6 i
    have htoSix_inj : Function.Injective toSix := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin 6 → ℕ) hab))
    have hl₆ : (l.attach.map toSix).Nodup := hl.attach.map htoSix_inj
    have hcover₆ : ∀ i : Fin 6, i ∈ l.attach.map toSix := fun i =>
      List.mem_map.mpr ⟨⟨fromSix i,
        (hcover _).mpr ((mem_posRoots_rational_g2_iff ht _).mpr i.isLt)⟩,
        List.mem_attach _ _, Fin.ext rfl⟩
    have hl₆_cast : (l.attach.map toSix).map fromSix = l := by
      rw [List.map_map]
      refine (List.map_congr_left fun γ _ => ?_).trans
        ((List.attach_map_val (l := l) (f := fun x => x)).trans l.map_id)
      exact Fin.ext rfl
    generalize l.attach.map toSix = l₆ at hl₆ hcover₆ hl₆_cast
    rw [mem_biSup_posRoots_g2_iff_exists_list_prod_map D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A l₆ hl₆ hcover₆ g]
    constructor
    · rintro ⟨f, hf⟩
      refine ⟨fun γ => if h : (γ : ℕ) < 6 then ofAdd (f ⟨γ.val, h⟩) else 1, ?_⟩
      rw [← hl₆_cast, List.map_map]
      refine (congrArg List.prod (List.map_congr_left fun i _ => ?_)).trans hf
      dsimp only [Function.comp_def, fromSix]
      exact congrArg _ (dite_eq_left i.isLt)
    · rintro ⟨u, hu⟩
      refine ⟨fun i => toAdd (u (fromSix i)), ?_⟩
      rw [← hu, ← hl₆_cast, List.map_map]
      simp only [ofAdd_toAdd]
      rfl
  · have := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) htG2
    rw [mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A l hl hcover g]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨fun γ => ofAdd (u γ), hu⟩
    · rintro ⟨u, hu⟩
      refine ⟨fun γ => toAdd (u γ), ?_⟩
      simpa only [ofAdd_toAdd] using hu

/-- Every positive point of a Chevalley datum is an ordered product with one factor from each
positive root subgroup, in any duplicate-free enumeration of the positive roots. -/
theorem mem_positivePoints_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => D.rootSubgroupPoints γ A (u γ)).prod = g := by
  constructor
  · intro hg
    obtain ⟨q, hq, hmatrix⟩ := D.mem_positivePoints_iff.mp hg
    obtain ⟨u, hu⟩ :=
      (D.mem_positiveSubgroup_iff_exists_prod l hl hcover (CommAlgCat.of ℤ A) q).mp hq
    refine ⟨u, (D.points A).subtype_injective ?_⟩
    have h := congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply,
      D.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe, hmatrix] using h
  · rintro ⟨u, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    exact D.rootSubgroupPoints_mem_positivePoints A ((hcover γ).mp hγ) (u γ)

end TauCeti.DynkinType.ChevalleyDatum
