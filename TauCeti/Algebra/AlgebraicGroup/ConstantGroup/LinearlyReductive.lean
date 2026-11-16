/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
import Mathlib.RepresentationTheory.Invariants
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Representation
import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.FiniteSubgroup
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact

/-!
# Linear reductivity of finite constant groups

Over a field `k`, the constant affine group attached to a finite group `G` is linearly reductive if
and only if `(Nat.card G : k) ≠ 0`. In one direction, linear reductivity implies invertibility of
the order of every finite subgroup of rational points; in the other, Reynolds averaging via
`Representation.averageMap` on `(Comodule.basePointsRepresentation M).comp (toPoints k G)` lifts
invariant vectors along surjective comodule morphisms. This is the affine-group form of Maschke's
theorem, and supplies the component-group input for characterizing linear reductivity of
disconnected affine groups.

## Main declarations

* `TauCeti.ConstantGroup.natCast_card_ne_zero_of_isLinearlyReductive_coordinateRing`: linear
  reductivity of `coordinateRing k G` implies `(Nat.card G : k) ≠ 0`.
* `TauCeti.ConstantGroup.isLinearlyReductive_coordinateRing_of_natCast_card_ne_zero`: conversely,
  invertibility of `Nat.card G` in `k` implies linear reductivity of `coordinateRing k G`.
* `TauCeti.ConstantGroup.isLinearlyReductive_coordinateRing_iff` and
  `TauCeti.ConstantGroup.linearlyReductiveCommHopfAlgProperty_coordinateRing_iff`: the resulting
  equivalences.

## References

* M. Nagata, *Complete reducibility of rational representations of a matric group*,
  J. Math. Kyoto Univ. **1** (1961), 87–99.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.3.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.l.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.ConstantGroup

universe u v

section Field

variable {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]

/-- If the constant group attached to a finite group `G` is linearly reductive over `k`, then the
order of `G` is nonzero in `k`. -/
theorem natCast_card_ne_zero_of_isLinearlyReductive_coordinateRing
    (h : Coalgebra.IsLinearlyReductive.{u, max u v, u} k (coordinateRing k G)) :
    (Nat.card G : k) ≠ 0 := by
  let e := (pointsMulEquiv k G).toEquiv
  let _ : Finite (WithConv (coordinateRing k G →ₐ[k] k)) := Finite.of_equiv G e
  have heq : Nat.card (⊤ : Subgroup (WithConv (coordinateRing k G →ₐ[k] k))) = Nat.card G :=
    Nat.card_congr (Subgroup.topEquiv.toEquiv.trans e.symm)
  simpa only [heq] using HopfAlgebra.natCast_card_ne_zero_of_isLinearlyReductive h ⊤

/-- **Maschke's theorem for finite constant groups.** If the order of a finite group `G` is
nonzero in the field `k`, then the coordinate Hopf algebra of the constant group attached to `G`
is linearly reductive over `k`. -/
theorem isLinearlyReductive_coordinateRing_of_natCast_card_ne_zero
    (hcard : (Nat.card G : k) ≠ 0) :
    Coalgebra.IsLinearlyReductive.{u, max u v, u} k (coordinateRing k G) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (by rwa [Fintype.card_eq_nat_card])
  let _ : AddCommGroup (coordinateRing k G) := inferInstance
  rw [Coalgebra.isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective]
  intro M N f hf n
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  let φ : Comodule.Hom k (coordinateRing k G) M N := CategoryTheory.ConcreteCategory.hom f.hom
  obtain ⟨m₀, hm₀⟩ := hf n.1
  let ρM : Representation k G M :=
    (Comodule.basePointsRepresentation (R := k) (H := coordinateRing k G) M).comp (toPoints k G)
  let m : M := ρM.averageMap m₀
  have hm : m ∈ Comodule.fixedSubcomodule k (coordinateRing k G) M :=
    mem_fixedSubcomodule_iff_forall_basePointsRepresentation_toPoints.mpr
      (ρM.averageMap_invariant m₀)
  have hm_eq : m = (Nat.card G : k)⁻¹ • ∑ g : G,
      Comodule.basePointsRepresentation (H := coordinateRing k G) M (toPoints k G g) m₀ := by
    simp [m, ρM, GroupAlgebra.average, map_sum, invOf_eq_inv]
  have hfm : φ m = n.1 := by
    rw [hm_eq]
    exact φ.map_inv_natCard_smul_sum_basePointsRepresentation_of_mem_fixedSubcomodule
      hcard (toPoints k G) hm₀ n.2
  exact ⟨⟨m, hm⟩, Subtype.ext ((φ.fixedMap_apply ⟨m, hm⟩).trans hfm)⟩

end Field

/-- Over a field `k`, the coordinate Hopf algebra of a finite constant group `G` is linearly
reductive if and only if `(Nat.card G : k) ≠ 0`. -/
@[simp]
theorem isLinearlyReductive_coordinateRing_iff (k : Type u) [Field k]
    (G : Type v) [Group G] [Finite G] :
    Coalgebra.IsLinearlyReductive.{u, max u v, u} k (coordinateRing k G) ↔
      (Nat.card G : k) ≠ 0 :=
  ⟨natCast_card_ne_zero_of_isLinearlyReductive_coordinateRing,
    isLinearlyReductive_coordinateRing_of_natCast_card_ne_zero⟩

/-- A finite constant group over a field `k` satisfies `linearlyReductiveCommHopfAlgProperty` if
and only if `(Nat.card G : k) ≠ 0`. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateRing_iff (k : Type u) [Field k]
    (G : Type v) [Group G] [Finite G] :
    linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.of k (coordinateRing k G)) ↔
      (Nat.card G : k) ≠ 0 :=
  (linearlyReductiveCommHopfAlgProperty_iff k _).trans (isLinearlyReductive_coordinateRing_iff k G)

end TauCeti.ConstantGroup
