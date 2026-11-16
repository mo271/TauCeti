/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite.Collection
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct

/-!
# Negative-root coordinates in full-weight Chevalley groups

For the full-weight Chevalley datum of every valid Dynkin type, multiplication of the negative
root subgroups in any order without repetitions is a bijection onto the negative point subgroup
over every commutative ring. The parameters are indexed only by negative roots: there are no
unused coordinates at positive roots. The resulting equivalence and its inverse commute with
changes of the value ring, including noninjective ring maps.

This combines `ChevalleyDatum.mem_negativePoints_iff_exists_prod` with the integral uniqueness
theorem `DynkinType.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj_of_mem_negRoots`,
paralleling the positive-root coordinate API in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates`. It supplies coordinates for the
lower-unitriangular unipotent factor in opposite Bruhat and big-cell factorizations without
identifying the ambient point group with its elementary subgroup.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17, and Chapter 5, Theorem 7.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v w

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

local notation "NegativeRoot" =>
  {γ // γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)}

/-- Multiply negative-root parameters in the order of `l`, as an element of the negative point
subgroup. This is a map of sets, not an assertion that coordinates add under multiplication. -/
noncomputable def negativeRootProduct (l : List NegativeRoot) (A : Type v) [CommRing A]
    (u : NegativeRoot → A) : D.negativePoints A :=
  ⟨(l.map fun γ => D.rootSubgroupPoints γ.1 A (ofAdd (u γ))).prod,
    Subgroup.list_prod_mem _ fun _ hg => by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hg
      exact D.rootSubgroupPoints_mem_negativePoints A γ.2 _⟩

/-- The negative-root product has the stated ordered factors in the datum point group. -/
@[simp]
theorem coe_negativeRootProduct (l : List NegativeRoot) (A : Type v) [CommRing A]
    (u : NegativeRoot → A) :
    (D.negativeRootProduct l A u : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ.1 A (ofAdd (u γ))).prod :=
  (rfl)

/-- Evaluating the negative-root product at the zero parameter tuple gives the identity point. -/
@[simp]
theorem negativeRootProduct_zero (l : List NegativeRoot) (A : Type v) [CommRing A] :
    D.negativeRootProduct l A 0 = 1 := by
  apply Subtype.ext
  simp [coe_negativeRootProduct]

/-- Changing the value ring applies the ring map to each negative-root coordinate. -/
theorem map_negativeRootProduct (l : List NegativeRoot)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (u : NegativeRoot → A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f
        (D.negativeRootProduct l A u : D.points A) =
      (D.negativeRootProduct l B (fun γ => f (u γ)) : D.points B) := by
  simp only [coe_negativeRootProduct, map_list_prod, List.map_map, Function.comp_def,
    D.map_rootSubgroupPoints, toAdd_ofAdd]

/-- Every negative point of a Chevalley datum has coordinates in any enumeration of the negative
roots, for every valid Dynkin type. No field or characteristic restriction is required. -/
theorem negativeRootProduct_surjective (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Surjective (D.negativeRootProduct l A) := by
  intro g
  have hroots : ∀ γ, γ ∈ l.map Subtype.val ↔
      γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    intro γ
    constructor
    · rintro hγ
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ
      exact γ.2
    · intro hγ
      exact List.mem_map.mpr ⟨⟨γ, hγ⟩, hcover _, rfl⟩
  obtain ⟨u, hu⟩ := (D.mem_negativePoints_iff_exists_prod (l.map Subtype.val)
    (hl.map Subtype.val_injective) hroots A g.1).mp g.2
  refine ⟨fun γ => (u γ.1).toAdd, Subtype.ext ?_⟩
  simpa only [coe_negativeRootProduct, List.map_map, Function.comp_def, ofAdd_toAdd] using hu

end TauCeti.DynkinType.ChevalleyDatum

namespace TauCeti.DynkinType

universe v w

variable (t : DynkinType) (ht : t.Valid)

local notation "D" => t.scChevalleyDatum ht
local notation "NegativeRoot" =>
  {γ // γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)}

/-- In the full-weight model, an ordered enumeration of all negative roots without repetitions
gives an injective parameter map over every commutative value ring. -/
theorem scChevalleyDatum_negativeRootProduct_injective (l : List NegativeRoot) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    Function.Injective ((D).negativeRootProduct l A) := by
  classical
  intro u v huv
  let extend := fun (u : NegativeRoot → A) (γ : Fin t.numRoots) =>
    if h : γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) then u ⟨γ, h⟩ else 0
  have heq := congrArg (fun g : (D).negativePoints A => (g : (D).points A)) huv
  have hprod (u : NegativeRoot → A) :
      ((l.map Subtype.val).map fun γ => (D).rootSubgroupPoints γ A
        (ofAdd (extend u γ))).prod = ((D).negativeRootProduct l A u : (D).points A) := by
    simp only [ChevalleyDatum.coe_negativeRootProduct, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro γ _
    simp only [extend, dite_eq_left γ.2]
  have hparams := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj_of_mem_negRoots ht A
    (hl.map Subtype.val_injective)
    (by rintro γ hγ; obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hγ; exact γ.2)).mp
      ((hprod u).trans (heq.trans (hprod v).symm))
  funext γ
  simpa only [extend, dite_eq_left γ.2] using
    hparams γ.1 (List.mem_map.mpr ⟨γ, hcover γ, rfl⟩)

/-- Negative-root coordinates for the full-weight Chevalley datum of every valid Dynkin type over
an arbitrary commutative ring. The list enumerates all negative roots, in any order without
repetitions. -/
noncomputable def scNegativeRootEquiv (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A] :
    (NegativeRoot → A) ≃ (D).negativePoints A :=
  Equiv.ofBijective ((D).negativeRootProduct l A)
    ⟨t.scChevalleyDatum_negativeRootProduct_injective ht l hl hcover A,
      (D).negativeRootProduct_surjective l hl hcover A⟩

/-- The coordinate equivalence multiplies the given negative-root parameters in the specified
order. -/
@[simp]
theorem scNegativeRootEquiv_apply (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) (A : Type v) [CommRing A]
    (u : NegativeRoot → A) :
    t.scNegativeRootEquiv ht l hl hcover A u = (D).negativeRootProduct l A u :=
  (rfl)

/-- Extracting coordinates from an ordered negative-root product recovers its parameters. -/
@[simp]
theorem scNegativeRootEquiv_symm_negativeRootProduct
    (l : List NegativeRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (u : NegativeRoot → A) :
    (t.scNegativeRootEquiv ht l hl hcover A).symm ((D).negativeRootProduct l A u) = u :=
  (t.scNegativeRootEquiv ht l hl hcover A).symm_apply_apply u

/-- The negative-root coordinates of the identity point are all zero. -/
@[simp]
theorem scNegativeRootEquiv_symm_one
    (l : List NegativeRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] :
    (t.scNegativeRootEquiv ht l hl hcover A).symm 1 = 0 := by
  rw [← (D).negativeRootProduct_zero l A, scNegativeRootEquiv_symm_negativeRootProduct]

/-- Multiplying the extracted negative-root coordinates reproduces the original negative point. -/
@[simp]
theorem negativeRootProduct_scNegativeRootEquiv_symm
    (l : List NegativeRoot) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type v) [CommRing A] (g : (D).negativePoints A) :
    (D).negativeRootProduct l A ((t.scNegativeRootEquiv ht l hl hcover A).symm g) = g :=
  (t.scNegativeRootEquiv ht l hl hcover A).apply_symm_apply g

/-- Extracting negative-root coordinates after scalar change applies the ring map coordinatewise,
even under noninjective homomorphisms such as reduction modulo a prime. -/
@[simp]
theorem scNegativeRootEquiv_symm_map (l : List NegativeRoot)
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    (g : (D).negativePoints A) :
    (t.scNegativeRootEquiv ht l hl hcover B).symm
        ⟨((D).pointsPresentation A).map ((D).pointsPresentation B) f (g : (D).points A),
          (D).map_negativePoints_le f (Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩)⟩ =
      fun γ => f ((t.scNegativeRootEquiv ht l hl hcover A).symm g γ) := by
  apply (t.scNegativeRootEquiv ht l hl hcover B).injective
  simp only [Equiv.apply_symm_apply, scNegativeRootEquiv_apply]
  apply Subtype.ext
  rw [← (D).map_negativeRootProduct l f]
  exact congrArg (((D).pointsPresentation A).map ((D).pointsPresentation B) f)
    (congrArg Subtype.val
      ((t.scNegativeRootEquiv ht l hl hcover A).apply_symm_apply g).symm)

end TauCeti.DynkinType
