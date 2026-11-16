/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.Int
public import TauCeti.GroupTheory.Amenable.Prod
import Mathlib.GroupTheory.NoncommPiCoprod
import TauCeti.GroupTheory.Amenable.Multiplicative

/-!
# Amenability of commutative groups

Every commutative topological additive or multiplicative group is amenable, with no hypothesis on
its rank, its torsion or its topology.

A finite subset `s` of a commutative additive group `A` is the image of the standard generators
under the homomorphism `(s → ℤ) →+ A` sending `n` to `∑ x ∈ s, n x • x`. This is Mathlib's
`AddMonoidHom.noncommPiCoprod` of the maps `zmultiplesHom A x`, whose commutation hypothesis holds
because `A` is commutative. Its source is a finite power of `ℤ` with the discrete topology, so it
is additively amenable by `TauCeti.AddAmenable.int` and `TauCeti.AddAmenable.pi`, and the
homomorphism is continuous for every topology on `A`. Every finite subset of `A` therefore lies in
the image of a continuous additive homomorphism from an amenable additive group, which is the
directed-union criterion `TauCeti.AddAmenable.of_forall_finset_subset_range`.

Transporting through `Additive G` (`TauCeti.addAmenable_additive_iff`) immediately yields the
multiplicative counterpart `TauCeti.Amenable.of_commGroup`.

## Main results

* `TauCeti.AddAmenable.of_addCommGroup`: every commutative topological additive group is amenable.
* `TauCeti.Amenable.of_commGroup`: every commutative topological group is amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every commutative topological additive group is amenable, whatever its additive group
topology. -/
instance (priority := 100) AddAmenable.of_addCommGroup {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A := by
  classical
  have hcomm (s : Finset A) : Pairwise fun x y : s => ∀ m n : ℤ,
      AddCommute (zmultiplesHom A x m) (zmultiplesHom A y n) := fun _ _ _ _ _ => .all _ _
  -- For a finite set `s`, the additive homomorphism `n ↦ ∑ x ∈ s, n x • x` out of `s → ℤ`.
  let φ (s : Finset A) : (s → ℤ) →ₜ+ A :=
    ⟨AddMonoidHom.noncommPiCoprod (fun x : s => zmultiplesHom A x) (hcomm s),
      continuous_of_discreteTopology⟩
  refine .of_forall_finset_subset_range φ fun s =>
    ⟨s, fun x hx => ⟨Pi.single ⟨x, hx⟩ 1,
      (AddMonoidHom.noncommPiCoprod_single (ϕ := fun y : s => zmultiplesHom A y)
        (hcomm := hcomm s) ⟨x, hx⟩ 1).trans (one_smul ℤ x)⟩⟩

/-- Every commutative topological group is amenable, whatever its group topology. -/
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  (addAmenable_additive_iff G).1 inferInstance

end TauCeti
