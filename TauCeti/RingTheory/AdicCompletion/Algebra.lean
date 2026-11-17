/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# The powers of the extended ideal in the adic completion of a ring

Let `I` be a finitely generated ideal of a commutative ring `R` and `R̂ = AdicCompletion I R`.
The kernel of the projection `R̂ → R ⧸ I ^ n` is the extension `I ^ n R̂` of `I ^ n`. Mathlib
records the case `n = 1` (`AdicCompletion.ker_evalOneₐ_eq_map`); the general case identifies
the `I R̂`-adic filtration of `R̂` with the kernels of the projections, so that
`R̂ ⧸ I ^ n R̂ ≃ R ⧸ I ^ n`. Consequently the canonical map `R → R̂` identifies `I ^ n` with the
preimage of `I ^ n R̂`, and every element of `R̂` is congruent modulo `I ^ n R̂` to the image of an
element of `R`, so the image of `R` is dense in `R̂` for the `I R̂`-adic topology.

If `R` is Hausdorff for the `I`-adic topology, then `R → R̂` is injective, so `R̂` has the
exponential characteristic of `R`.

## Main results

* `AdicCompletion.ker_evalₐ_eq_map_pow`: the kernel of `R̂ → R ⧸ I ^ n` is `I ^ n R̂`.
* `AdicCompletion.quotientMapPowAlgEquiv`: the isomorphism of `R`-algebras
  `R̂ ⧸ I ^ n R̂ ≃ R ⧸ I ^ n`.
* `AdicCompletion.algebraMap_mem_map_pow_iff`: the image of `x ∈ R` lies in `I ^ n R̂` if and
  only if `x ∈ I ^ n`.
* `AdicCompletion.exists_sub_algebraMap_mem_map_pow`: every element of `R̂` is congruent
  modulo `I ^ n R̂` to the image of an element of `R`.
* `AdicCompletion.quotientMap_algebraMap_bijective`: the map `R ⧸ I ^ n → R̂ ⧸ (I R̂) ^ n` induced
  by `R → R̂` is bijective.
* `AdicCompletion.quotientMapSupPowAlgEquiv`: for any ideal `J` of `R`, the isomorphism of
  `R`-algebras `R̂ ⧸ (J R̂ + (I R̂) ^ n) ≃ R ⧸ (J + I ^ n)`.
* `AdicCompletion.denseRange_algebraMap`: the image of `R` is dense in `R̂` for the `I R̂`-adic
  topology.
* `AdicCompletion.expChar`: the `I`-adic completion of an `I`-adically Hausdorff ring has the
  exponential characteristic of the ring.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.2.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- For a finitely generated ideal `I`, the kernel of the projection of the adic completion
onto `R ⧸ I ^ n` is the extension of `I ^ n` to the completion. -/
theorem ker_evalₐ_eq_map_pow (fg : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (eval I R n).ker
  · have eq : (I ^ n • ⊤ : Ideal R) = I ^ n := by simp
    rw [RingHom.mem_ker, ← factor_eval_eq_evalₐ I x eq.le, LinearMap.mem_ker]
    -- The factor map is the quotient equivalence from which `evalₐ` is built.
    exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R eq).injective
  · simp [← pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]

/-- For a finitely generated ideal `I`, the adic completion modulo the extension of `I ^ n` is
`R ⧸ I ^ n`: the isomorphism is induced by the projection `R̂ → R ⧸ I ^ n`. -/
noncomputable def quotientMapPowAlgEquiv (fg : I.FG) (n : ℕ) :
    (AdicCompletion I R ⧸ (I ^ n).map (algebraMap R (AdicCompletion I R))) ≃ₐ[R] R ⧸ I ^ n :=
  (Ideal.quotientEquivAlgOfEq R (ker_evalₐ_eq_map_pow fg n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

/-- The isomorphism `R̂ ⧸ I ^ n R̂ ≃ R ⧸ I ^ n` sends the class of `x` to its projection. -/
@[simp]
theorem quotientMapPowAlgEquiv_mk (fg : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    quotientMapPowAlgEquiv fg n (Ideal.Quotient.mk _ x) = evalₐ I n x := by
  simp [quotientMapPowAlgEquiv]

/-- An element of `R` maps into the extension of `I ^ n` to the adic completion if and only if it
lies in `I ^ n`. -/
@[simp]
theorem algebraMap_mem_map_pow_iff (n : ℕ) {x : R} :
    algebraMap R (AdicCompletion I R) x ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) ↔
      x ∈ I ^ n := by
  refine ⟨fun h ↦ ?_, Ideal.mem_map_of_mem _⟩
  have hker : (I ^ n).map (algebraMap R (AdicCompletion I R)) ≤ RingHom.ker (evalₐ I n) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp [algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem, hy]
  simpa [algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem] using hker h

/-- For a finitely generated ideal `I`, every element of the adic completion is congruent modulo
the extension of `I ^ n` to the image of an element of `R`. -/
theorem exists_sub_algebraMap_mem_map_pow (fg : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    ∃ y : R, x - algebraMap R (AdicCompletion I R) y ∈
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨y, ?_⟩
  rw [← ker_evalₐ_eq_map_pow fg, RingHom.mem_ker, map_sub, ← hy]
  exact sub_eq_zero.mpr (evalₐ_of I n y).symm

/-- For a finitely generated ideal `I`, the map `R ⧸ I ^ n → R̂ ⧸ (I R̂) ^ n` induced by the
canonical map `R → R̂` is bijective: `R` and its `I`-adic completion have the same reductions. -/
theorem quotientMap_algebraMap_bijective (fg : I.FG) (n : ℕ)
    {H : I ^ n ≤ ((I.map (algebraMap R (AdicCompletion I R))) ^ n).comap
      (algebraMap R (AdicCompletion I R))} :
    Function.Bijective (Ideal.quotientMap _ (algebraMap R (AdicCompletion I R)) H) := by
  refine ⟨Ideal.quotientMap_injective' fun x hx ↦ ?_, fun x ↦ ?_⟩
  · rwa [Ideal.mem_comap, ← Ideal.map_pow, algebraMap_mem_map_pow_iff] at hx
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
    rw [Ideal.map_pow] at hy
    exact ⟨Ideal.Quotient.mk _ y, (Ideal.Quotient.eq.mpr hy).symm⟩

/-- For a finitely generated ideal `I` and any ideal `J` of `R`, the kernel of the composite
`R̂ → R ⧸ I ^ n → R ⧸ (J ⊔ I ^ n)` is `J R̂ ⊔ (I R̂) ^ n`. -/
theorem ker_factorₐ_comp_evalₐ_eq_map_sup_pow (fg : I.FG) (J : Ideal R) (n : ℕ) :
    RingHom.ker ((Ideal.Quotient.factorₐ R (le_sup_right : I ^ n ≤ J ⊔ I ^ n)).comp
        (evalₐ I n) : AdicCompletion I R →ₐ[R] R ⧸ (J ⊔ I ^ n)) =
      J.map (algebraMap R (AdicCompletion I R)) ⊔
        (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  let ψ : AdicCompletion I R →ₐ[R] R ⧸ (J ⊔ I ^ n) :=
    (Ideal.Quotient.factorₐ R (le_sup_right : I ^ n ≤ J ⊔ I ^ n)).comp (evalₐ I n)
  have hψ_alg (r : R) :
      ψ (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk (J ⊔ I ^ n) r := by
    simp [ψ, algebraMap_apply, evalₐ_of]
  rw [← Ideal.map_pow, ← Ideal.map_sup]
  have hle : (J ⊔ I ^ n).map (algebraMap R (AdicCompletion I R)) ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ_alg, Ideal.Quotient.eq_zero_iff_mem]
    exact hr
  refine le_antisymm (fun x hx ↦ ?_) hle
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
  have hy' : x - algebraMap R (AdicCompletion I R) y ∈
      (J ⊔ I ^ n).map (algebraMap R (AdicCompletion I R)) :=
    Ideal.map_mono le_sup_right hy
  have hψy : ψ (algebraMap R (AdicCompletion I R) y) = 0 := by
    have hsub : ψ (x - algebraMap R (AdicCompletion I R) y) = 0 := hle hy'
    rw [map_sub, RingHom.mem_ker.mp hx, zero_sub, neg_eq_zero] at hsub
    exact hsub
  have hy_mem : y ∈ J ⊔ I ^ n := by
    rwa [hψ_alg, Ideal.Quotient.eq_zero_iff_mem] at hψy
  simpa only [sub_add_cancel] using add_mem hy' (Ideal.mem_map_of_mem _ hy_mem)

/-- For a finitely generated ideal `I` and any ideal `J` of `R`, the quotient of the `I`-adic
completion by `J R̂ ⊔ (I R̂) ^ n` is isomorphic as an `R`-algebra to `R ⧸ (J ⊔ I ^ n)`. -/
noncomputable def quotientMapSupPowAlgEquiv (fg : I.FG) (J : Ideal R) (n : ℕ) :
    (AdicCompletion I R ⧸
      (J.map (algebraMap R (AdicCompletion I R)) ⊔
        (I.map (algebraMap R (AdicCompletion I R))) ^ n)) ≃ₐ[R]
      R ⧸ (J ⊔ I ^ n) :=
  (Ideal.quotientEquivAlgOfEq R (ker_factorₐ_comp_evalₐ_eq_map_sup_pow fg J n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      ((Ideal.Quotient.factor_surjective (le_sup_right : I ^ n ≤ J ⊔ I ^ n)).comp
        (surjective_evalₐ I n)))

/-- The isomorphism `R̂ ⧸ (J R̂ ⊔ (I R̂) ^ n) ≃ R ⧸ (J ⊔ I ^ n)` sends the class of `x` to the
quotient class of its projection `evalₐ I n x`. -/
@[simp]
theorem quotientMapSupPowAlgEquiv_mk (fg : I.FG) (J : Ideal R) (n : ℕ) (x : AdicCompletion I R) :
    quotientMapSupPowAlgEquiv fg J n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.factor (le_sup_right : I ^ n ≤ J ⊔ I ^ n) (evalₐ I n x) := by
  simp [quotientMapSupPowAlgEquiv]
  rfl

open Topology in
/-- For a finitely generated ideal `I`, the image of `R` is dense in the adic completion for the
adic topology of the extension of `I`. -/
theorem denseRange_algebraMap [TopologicalSpace (AdicCompletion I R)] (fg : I.FG)
    (hI : IsAdic (I.map (algebraMap R (AdicCompletion I R)))) :
    DenseRange (algebraMap R (AdicCompletion I R)) := by
  refine fun x ↦ mem_closure_iff_nhds.mpr fun U hU ↦ ?_
  obtain ⟨n, -, hn⟩ := (hI.hasBasis_nhds x).mem_iff.mp hU
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
  rw [Ideal.map_pow] at hy
  refine ⟨_, hn ⟨_, neg_mem hy, ?_⟩, y, rfl⟩
  simp only [neg_sub, add_sub_cancel]

/-- The completion of an `I`-adically Hausdorff ring has the exponential characteristic of the
ring, since the ring embeds into it. -/
instance expChar [IsHausdorff I R] (p : ℕ) [ExpChar R p] :
    ExpChar (AdicCompletion I R) p :=
  expChar_of_injective_algebraMap (of_injective I R) p

end AdicCompletion
