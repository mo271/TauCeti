/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Reductive.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Lie
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.IdentityComponent
import TauCeti.Algebra.Lie.Reductive.CompleteReducibility

/-!
# Complete reducibility for reductive affine groups

Over a field of characteristic zero, every finite-dimensional rational
representation of a reductive affine group is completely reducible. After extension to an
algebraic closure, the Lie algebra has central
radical, and its center acts semisimply because it comes from the radical torus of the group.
Complete reducibility for reductive Lie algebras therefore applies to the differentiated
representation. Connectedness identifies Lie-stable subspaces with subrepresentations, so the
complements are rational subrepresentations. Linear reductivity descends from the algebraic
closure to the original field. Together with the converse for smooth geometrically connected
groups, this gives the equivalence between reductivity and linear reductivity in characteristic
zero; combining with the identity-component reduction yields Milne's Corollary 22.43 for arbitrary
finite-type affine groups. Every rational representation, including an infinite-dimensional one, is
therefore completely reducible.

The Lie-algebra inputs are `reductiveCommHopfAlgProperty.hasCentralRadical_lieAlgebra` and
`reductiveCommHopfAlgProperty.isSemisimple_differential_of_mem_center`. The passage back to
comodules uses `Comodule.isCompletelyReducible_iff_forall_differential_mem`. The differentiated
Lie action is assembled as in `TauCeti.Algebra.AlgebraicGroup.Representation.CompleteReducibility`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 22, including Corollary 22.43.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* `TauCeti.Algebra.Lie.Reductive.CompleteReducibility`, for complete reducibility with
  semisimple central action.
-/

public section

namespace TauCeti

universe u w

section AlgClosed

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

namespace Comodule

/-- Every finite-dimensional rational representation of a reductive affine group over an
algebraically closed field of characteristic zero is completely reducible. -/
private theorem isCompletelyReducible_of_reductive_of_isAlgClosed
    (hH : reductiveCommHopfAlgProperty k H)
    {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M] :
    IsCompletelyReducible k H M := by
  let _ : ConnectedSpace (PrimeSpectrum H) := hH.geometricallyConnected.connectedSpace k H.obj
  let _ := hH.hasCentralRadical_lieAlgebra
  let _ : LieRing (Module.End k M) := LieRing.ofAssociativeRing
  let _ : LieRingModule (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    LieRingModule.compLieHom M (differential (R := k) (H := H) (M := M))
  let _ : LieModule k (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    LieModule.compLieHom M (differential (R := k) (H := H) (M := M))
  have hlie (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M) :
      ⁅d, m⁆ = differential (R := k) (H := H) (M := M) d m := by
    rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]
  have hcentral (z : LieAlgebra.center k (Derivation k H (Bialgebra.CounitAlgebra k H k))) :
      (LieModule.toEnd k _ M z).IsSemisimple := by
    convert hH.isSemisimple_differential_of_mem_center M z.val z.property using 1
    ext m
    exact hlie z.val m
  let _ := complementedLattice_lieSubmodule_of_isSemisimple_center hcentral
  refine isCompletelyReducible_iff_forall_differential_mem.2 fun W hW ↦ ?_
  let N : LieSubmodule k (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    { W with lie_mem := fun {d _} hm ↦ (hlie d _).symm ▸ hW d _ hm }
  obtain ⟨P, hP⟩ := exists_isCompl N
  refine ⟨P.toSubmodule, fun d m hm ↦ hlie d m ▸ P.lie_mem hm, ?_⟩
  exact LieSubmodule.isCompl_toSubmodule.mpr hP

end Comodule

end AlgClosed

section ArbitraryField

variable {k : Type u} [Field k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A reductive affine group over any field of characteristic zero is linearly reductive.
Neither algebraic closedness nor a splitting hypothesis is required. -/
theorem reductiveCommHopfAlgProperty.linearlyReductive
    (hH : reductiveCommHopfAlgProperty k H) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  apply linearlyReductiveCommHopfAlgProperty.of_baseChange (AlgebraicClosure k)
  rw [linearlyReductiveCommHopfAlgProperty_iff]
  apply Coalgebra.IsLinearlyReductive.of_forall_isCompletelyReducible (AlgebraicClosure k)
  intro M _ _ _ _
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup (AlgebraicClosure k)
  exact Comodule.isCompletelyReducible_of_reductive_of_isAlgClosed hH.algebraicClosureBaseChange

/-- Every rational representation of a reductive affine group in characteristic zero is
completely reducible over the original field, without a finite-dimensionality assumption. -/
theorem Comodule.isCompletelyReducible_of_reductive
    (hH : reductiveCommHopfAlgProperty k H)
    {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M] :
    Comodule.IsCompletelyReducible k H M :=
  ((linearlyReductiveCommHopfAlgProperty_iff k H.obj).mp hH.linearlyReductive).isCompletelyReducible

open reductiveCommHopfAlgProperty in
/-- For geometrically connected affine groups in characteristic zero, reductivity and complete
reducibility of all finite-dimensional rational representations are equivalent. Smoothness
is automatic by Cartier's theorem. -/
theorem reductiveCommHopfAlgProperty_iff_linearlyReductive
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    reductiveCommHopfAlgProperty k H ↔ linearlyReductiveCommHopfAlgProperty k H.obj := by
  refine ⟨fun hH ↦ hH.linearlyReductive, fun hH ↦ ?_⟩
  exact of_smooth_of_geometricallyConnected_of_baseChange_linearlyReductive
    ((smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H.obj))
    hconnected (hH.baseChange (AlgebraicClosure k))

/-- **Milne, *Algebraic Groups*, Corollary 22.43.** Over a field `k` of characteristic zero, an
affine group of finite type (not necessarily connected) is linearly reductive if and only if its
geometric identity component over `AlgebraicClosure k` is reductive. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      reductiveCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.identityComponent
          ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H)) :=
  (linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_charZero H).trans
    (reductiveCommHopfAlgProperty_iff_linearlyReductive _
      (FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent _)).symm

end ArbitraryField

end TauCeti
