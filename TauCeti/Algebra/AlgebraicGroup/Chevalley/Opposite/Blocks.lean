/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Blocks
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Weight blocks of negative Chevalley points

Every negative point of a Chevalley datum is lower unitriangular in the blocks of its actual
weight spaces, using the dual of the same height-compatible weight-block ranking used for
positive points. In particular, its restriction to each weight block is the identity, including
weight spaces of multiplicity greater than one. This supplies the lower-unitriangular matrix
factor used in big-cell LDU decompositions without assuming root coordinates or a Bruhat
decomposition.

The root-matrix calculation is `blockUnitriangular_toDual_kostantRootSubgroupMatrix`; closure
under group operations extends it to all negative points over every commutative value ring,
paralleling the upper-unitriangular treatment in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Blocks`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17, and Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type v) [CommRing A]

attribute [local instance high] Algebra.toModule

/-- Negative Chevalley points are lower unitriangular in their weight-space blocks, expressed
using the order dual of `orderedWeightBlock`. The blocks are indexed by distinct weights, not by
individual basis vectors. -/
theorem blockUnitriangular_of_mem_negativePoints {g : D.points A}
    (hg : g ∈ D.negativePoints A) :
    Matrix.BlockUnitriangular
      ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A)
      (OrderDual.toDual ∘ orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.negativePoints_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨γ, hγ, u, rfl⟩ := hg
    rw [D.coe_rootSubgroupPoints,
      ← kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator,
      basisMatrix_kostantRootSubgroupParam]
    exact blockUnitriangular_toDual_kostantRootSubgroupMatrix (t.chevalleySystem ht)
      (t.lieBasis ht).h D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      D.basis D.weight (t.weightDegree ht) γ _ D.isCartanWeightVector_basis
      (t.lie_lieBasis_h_chevalleySystem ht γ) (t.weightDegree_root_neg ht hγ) _
  -- Reconcile the order instances on the finite dual block index via `blockUnitriangular_iff`.
  | one => simpa only [Subgroup.coe_one, Units.val_one, Matrix.blockUnitriangular_iff] using
      (Matrix.blockUnitriangular_one
        (R := A) (b := OrderDual.toDual ∘ orderedWeightBlock (t.weightDegree ht) D.weight))
  | mul g h _ _ hg hh =>
    simpa only [Subgroup.coe_mul, Units.val_mul, Matrix.blockUnitriangular_iff] using hg.mul hh
  | inv g _ hg =>
    simpa only [Subgroup.coe_inv, Matrix.coe_units_inv, Matrix.blockUnitriangular_iff] using hg.inv

/-- On each entire weight space, a negative point has the identity matrix block. -/
theorem coe_apply_eq_one_apply_of_mem_negativePoints_of_weight_eq {g : D.points A}
    (hg : g ∈ D.negativePoints A) {i j : Fin D.dim} (hij : D.weight i = D.weight j) :
    ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) i j =
      (1 : Matrix (Fin D.dim) (Fin D.dim) A) i j :=
  (D.blockUnitriangular_of_mem_negativePoints A hg).apply_of_eq
    (congrArg OrderDual.toDual ((orderedWeightBlock_eq_iff _ _).mpr hij))

end TauCeti.DynkinType.ChevalleyDatum
