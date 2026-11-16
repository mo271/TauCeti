/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Artinian.Ring

/-!
# Ideal-power torsion of Artinian modules

Every element of an Artinian module `M` over a commutative ring `R` is killed by a power of the
Jacobson radical `J(R)`: the cyclic submodule `R ∙ x` is isomorphic to `R ⧸ ann(x)`, which is an
Artinian ring, so its Jacobson radical is nilpotent and contains the image of `J(R)`.

Over a local ring `(R, 𝔪)`, it follows that every Artinian `R`-module is `𝔪`-power torsion, with
no Noetherian hypothesis on `R`. In particular, every Artinian `R`-module carries the canonical
module action of the `𝔪`-adic completion `R̂` constructed in
`TauCeti/RingTheory/AdicCompletion/Torsion.lean`.

## Main results

* `TauCeti.mem_primaryComponent_jacobson_of_isArtinian` and
  `TauCeti.primaryComponent_jacobson_eq_top_of_isArtinian`: every Artinian module over a
  commutative ring is `J(R)`-power torsion.
* `TauCeti.mem_primaryComponent_maximalIdeal_of_isArtinian` and
  `TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian`: every Artinian module over a
  commutative local ring is `𝔪`-power torsion.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1 and Remark 47.7.9, Tag 0EGL.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

namespace TauCeti

open IsLocalRing Submodule

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsArtinian R M]

/-- Every element of an Artinian module over a commutative ring is killed by a power of the
Jacobson radical. -/
theorem mem_primaryComponent_jacobson_of_isArtinian (x : M) :
    x ∈ (Ring.jacobson R).primaryComponent M := by
  set I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M x)
  have hj : Function.Injective (I.liftQ (LinearMap.toSpanSingleton R M x) le_rfl) :=
    LinearMap.ker_eq_bot.mp (I.ker_liftQ_eq_bot _ le_rfl le_rfl)
  have : IsArtinian R (R ⧸ I) := isArtinian_of_injective _ hj
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_tower R inferInstance
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson (R ⧸ I)
  have hmap : (Ring.jacobson R).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr (Ring.le_comap_jacobson (Ideal.Quotient.mk I))
  have hpow : Ring.jacobson R ^ n ≤ I := by
    rw [← Ideal.mk_ker (I := I), ← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
    exact le_bot_iff.mp ((Ideal.pow_right_mono hmap n).trans
      (by simpa only [Ideal.zero_eq_bot] using hn.le))
  refine ((Ring.jacobson R).primaryComponent_mem M x).mpr ⟨n, ?_⟩
  rw [mem_torsionBySet_iff]
  intro r
  exact LinearMap.mem_ker.mp (hpow r.prop)

/-- Every Artinian module over a commutative ring coincides with the primary component of the
Jacobson radical. -/
theorem primaryComponent_jacobson_eq_top_of_isArtinian :
    (Ring.jacobson R).primaryComponent M = ⊤ :=
  eq_top_iff'.mpr mem_primaryComponent_jacobson_of_isArtinian

end CommRing

section LocalRing

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [IsArtinian R M]

/-- Every element of an Artinian module over a commutative local ring is killed by a power of the
maximal ideal. No Noetherian hypothesis on the ring is needed. -/
theorem mem_primaryComponent_maximalIdeal_of_isArtinian (x : M) :
    x ∈ (maximalIdeal R).primaryComponent M :=
  ringJacobson_eq_maximalIdeal R ▸ mem_primaryComponent_jacobson_of_isArtinian x

/-- Every Artinian module over a commutative local ring is maximal-ideal-power torsion. -/
theorem primaryComponent_maximalIdeal_eq_top_of_isArtinian :
    (maximalIdeal R).primaryComponent M = ⊤ :=
  eq_top_iff'.mpr mem_primaryComponent_maximalIdeal_of_isArtinian

end LocalRing

end TauCeti
