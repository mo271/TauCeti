/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Int
public import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# Amenability of commutative groups

Every commutative topological group — additive (`AddCommGroup`) or multiplicative (`CommGroup`) —
is amenable, with no hypothesis on its rank, torsion, or group topology.

For an additive commutative group `A`:
1. Every finitely generated additive subgroup `K ≤ A` is an `AddCommGroup` with `AddGroup.FG K`, so
   `TauCeti.exists_fin_surjective_zmultiplesPiHom` exhibits `K` as a surjective homomorphic image
   of `Fin n → ℤ`. Equipping `ℤ` with the discrete topology makes `Fin n → ℤ` a finite product of
   discrete amenable additive groups (`TauCeti.AddAmenable.int`, `TauCeti.AddAmenable.pi`), and the
   homomorphism `(Fin n → ℤ) →+ K` is continuous for the subspace topology on `K`, so
   `TauCeti.AddAmenable.of_surjective` gives `AddAmenable K`.
2. Since every finitely generated additive subgroup of `A` is amenable,
   `TauCeti.AddAmenable.of_forall_fg` gives `AddAmenable A`.

In particular, `ℝ` (with either its standard topology or the discrete topology), `ℚ`, `ℂ`, every
topological vector space, and every abelian group are `AddAmenable`. Transporting along `Additive`
(`TauCeti.addAmenable_additive_iff`) immediately yields `TauCeti.Amenable.of_commGroup` for all
multiplicative commutative topological groups.

## Main results

* `TauCeti.AddAmenable.of_addCommGroup`: every additive commutative topological group is amenable.
* `TauCeti.Amenable.of_commGroup`: every multiplicative commutative topological group is amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every additive commutative topological group is amenable, whatever its additive group
topology. -/
instance (priority := 100) AddAmenable.of_addCommGroup {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A :=
  .of_forall_fg fun K hK => by
    have : AddGroup.FG K := (AddGroup.fg_iff_addSubgroup_fg K).2 hK
    obtain ⟨n, τ, hτ⟩ := exists_fin_surjective_zmultiplesPiHom K
    let : TopologicalSpace ℤ := ⊥
    have : DiscreteTopology ℤ := discreteTopology_bot ℤ
    have : IsTopologicalAddGroup ℤ := ⟨⟩
    exact .of_surjective ⟨zmultiplesPiHom τ fun _ _ => .all _ _,
      continuous_of_discreteTopology⟩ hτ

/-- Every commutative topological group is amenable, whatever its group topology. -/
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  addAmenable_additive_iff.1 inferInstance

end TauCeti
