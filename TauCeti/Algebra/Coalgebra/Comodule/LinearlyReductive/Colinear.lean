/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Algebra.Coalgebra.Comodule.Induced
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Invariant lifting and linear reductivity along unital colinear maps

Let `q : C →ₐc[k] D` be a morphism of bialgebras over a field `k`, with `C` linearly reductive,
and let `σ : D →ₗ[k] C` be a unital `k`-linear map (`σ 1 = 1`) intertwining
`(q ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D`. Pushing the coaction of a right `D`-comodule `M` along `σ`
lands in the induced `C`-comodule `Ind_q M` (`TauCeti.Comodule.lTensor_coact_mem_induced`); this
map into induced comodules (which asserts only membership in `Ind_q M`, not injectivity) lifts
`D`-invariant elements in the range of any `D`-comodule morphism to `D`-invariant preimages, and
hence transfers surjectivity on invariants from `C` to `D`.

When `D` is a commutative Hopf algebra, exactness on invariants characterizes linear reductivity,
so linear reductivity descends from `C` to `D`. For affine group schemes `H ≤ G`, such a unital
left `O(H)`-colinear linear map `O(H) →ₗ[k] O(G)` arises whenever the coset quotient `G / H`
admits a global section, for instance when `H = G°` over an algebraically closed field.

## Main declarations

* `TauCeti.Comodule.Hom.exists_fixed_preimage_of_unital_colinear`: invariant preimage lifting along
  any morphism of right `D`-comodules via a unital left-colinear linear map from `D` into a
  linearly reductive bialgebra `C`.
* `TauCeti.Comodule.Hom.fixedMap_surjective_of_unital_colinear`: surjectivity on invariants
  descends from a linearly reductive bialgebra `C` to any bialgebra `D` along a bialgebra morphism
  admitting a unital left-colinear linear map.
* `TauCeti.Coalgebra.IsLinearlyReductive.of_unital_colinear`: linear reductivity descends from a
  bialgebra `C` to a commutative Hopf algebra `D` along a bialgebra morphism admitting a unital
  left-colinear linear map.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.3.3–I.3.4 and I.4.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.l.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x y z

namespace Comodule

attribute [local instance] cofree

/-- Applying `inducedMap q φ` to `(id ⊗ σ)(ρ m₀)` for a preimage `m₀` of a `D`-fixed vector `n`
produces a `C`-fixed element of `Ind_q N` with underlying tensor `n ⊗ 1`. -/
private theorem inducedMap_lTensor_coact_fixed {R : Type u} [CommRing R]
    {C : Type v} {D : Type w} [Semiring C] [Bialgebra R C] [Module.Flat R C]
    [Semiring D] [Bialgebra R D]
    {q : C →ₗc[R] D} {σ : D →ₗ[R] C} (hσ1 : σ 1 = 1)
    (hσ : ∀ x : D,
      ((q : C →ₗ[R] D).rTensor C) (Coalgebra.comul (R := R) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := R) x))
    {M : Type x} {N : Type y} [AddCommMonoid M] [Module R M] [Comodule R D M]
    [AddCommMonoid N] [Module R N] [Comodule R D N]
    (φ : Hom R D M N) {m₀ : M} {n : N} (hm₀ : φ m₀ = n)
    (hn : n ∈ fixedSubcomodule R D N) :
    let t : induced q M :=
      ⟨σ.lTensor M (coact (R := R) (C := D) m₀), lTensor_coact_mem_induced hσ m₀⟩
    (inducedMap q φ t : N ⊗[R] C) = n ⊗ₜ[R] (1 : C) ∧
      inducedMap q φ t ∈ fixedSubcomodule R C (induced q N) := by
  intro t
  have hy_coe : (inducedMap q φ t : N ⊗[R] C) = n ⊗ₜ[R] (1 : C) := by
    rw [coe_inducedMap_apply]
    simp only [t]
    rw [← LinearMap.lTensor_rTensor_comm, LinearMap.rTensor_def,
      φ.map_coact_apply m₀, hm₀, mem_fixedSubcomodule.mp hn, LinearMap.lTensor_tmul, hσ1]
  refine ⟨hy_coe,
    ((Subcomodule.subtype (induced q N)).mem_fixedSubcomodule_iff_of_injective
      (fun _ _ h ↦ Subtype.ext (by simpa only [Subcomodule.subtype_apply] using h)) _).mp ?_⟩
  rw [Subcomodule.subtype_apply, hy_coe, mem_fixedSubcomodule, cofree_coact]
  simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]

/-- Over a field `k`, if a linearly reductive bialgebra `C` maps to a bialgebra `D` via
`q : C →ₐc[k] D` admitting a unital `k`-linear map `σ : D →ₗ[k] C` that intertwines
`(q ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D`, then every `D`-fixed vector in the image of a morphism of
right `D`-comodules lifts to a `D`-fixed preimage. -/
theorem Hom.exists_fixed_preimage_of_unital_colinear {k : Type u} [Field k]
    {C : Type v} {D : Type w} [Semiring C] [Bialgebra k C] [Semiring D] [Bialgebra k D]
    (q : C →ₐc[k] D) (σ : D →ₗ[k] C) (hσ1 : σ 1 = 1)
    (hσ : ∀ x : D,
      ((q.toCoalgHom : C →ₗ[k] D).rTensor C) (Coalgebra.comul (R := k) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := k) x))
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C)
    {M : Type x} {N : Type y} [AddCommMonoid M] [Module k M] [Comodule k D M]
    [AddCommMonoid N] [Module k N] [Comodule k D N]
    (φ : Hom k D M N) {n : N} (hn : n ∈ fixedSubcomodule k D N)
    (hnrange : n ∈ LinearMap.range φ.toLinearMap) :
    ∃ m ∈ fixedSubcomodule k D M, φ m = n := by
  let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Free k C := Module.Free.of_divisionRing k C
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  obtain ⟨m₀, hm₀⟩ := hnrange
  let t : induced q.toCoalgHom M :=
    ⟨σ.lTensor M (coact (R := k) (C := D) m₀), lTensor_coact_mem_induced hσ m₀⟩
  obtain ⟨hy_coe, hy_fixed⟩ := inducedMap_lTensor_coact_fixed hσ1 hσ φ hm₀ hn
  obtain ⟨x, hx_fixed, hxy⟩ :=
    (inducedMap q.toCoalgHom φ).exists_fixed_preimage_of_isLinearlyReductive hC hy_fixed ⟨t, rfl⟩
  let m : M := TensorProduct.rid k M ((Coalgebra.counit (R := k) (A := C)).lTensor M x)
  have hm_fixed : m ∈ fixedSubcomodule k D M := by
    let _ : Comodule k D (induced q.toCoalgHom M) := Corestrict q.toCoalgHom
    have hx_corestrict : x ∈ fixedSubcomodule k D (induced q.toCoalgHom M) :=
      mem_fixedSubcomodule_corestrict q.toCoalgHom (map_one q) hx_fixed
    simpa only [inducedEval_apply] using
      (inducedEval q.toCoalgHom).mem_fixedSubcomodule hx_corestrict
  have hφm : φ m = n := by
    have hnat := LinearMap.congr_fun
      (rid_comp_lTensor_counit_comp_rTensor (C := C) φ.toLinearMap) (x : M ⊗[k] C)
    simp only [LinearMap.comp_apply] at hnat
    calc
      φ m = TensorProduct.rid k N
          ((Coalgebra.counit (R := k) (A := C)).lTensor N (φ.toLinearMap.rTensor C x)) :=
        hnat.symm
      _ = TensorProduct.rid k N
          ((Coalgebra.counit (R := k) (A := C)).lTensor N (n ⊗ₜ[k] (1 : C))) := by
        rw [← coe_inducedMap_apply q.toCoalgHom φ x, hxy, hy_coe]
      _ = n := by simp
  exact ⟨m, hm_fixed, hφm⟩

/-- Over a field `k`, if a linearly reductive bialgebra `C` maps to a bialgebra `D` via
`q : C →ₐc[k] D` admitting a unital `k`-linear map `σ : D →ₗ[k] C` that intertwines
`(q ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D`, then every surjective morphism of right `D`-comodules
remains surjective on `D`-fixed vectors. -/
theorem Hom.fixedMap_surjective_of_unital_colinear {k : Type u} [Field k]
    {C : Type v} {D : Type w} [Semiring C] [Bialgebra k C] [Semiring D] [Bialgebra k D]
    (q : C →ₐc[k] D) (σ : D →ₗ[k] C) (hσ1 : σ 1 = 1)
    (hσ : ∀ x : D,
      ((q.toCoalgHom : C →ₗ[k] D).rTensor C) (Coalgebra.comul (R := k) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := k) x))
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C)
    {M : Type x} {N : Type y} [AddCommMonoid M] [Module k M] [Comodule k D M]
    [AddCommMonoid N] [Module k N] [Comodule k D N]
    (φ : Hom k D M N) (hφ : Function.Surjective φ) :
    Function.Surjective φ.fixedMap := by
  intro n
  obtain ⟨m, hm, hφm⟩ :=
    φ.exists_fixed_preimage_of_unital_colinear q σ hσ1 hσ hC n.2 (hφ n.1)
  exact ⟨⟨m, hm⟩, Subtype.ext ((φ.fixedMap_apply ⟨m, hm⟩).trans hφm)⟩

end Comodule

namespace Coalgebra

/-- Linear reductivity descends from a bialgebra `C` over a field `k` to any commutative Hopf
algebra `D` along a bialgebra morphism `q : C →ₐc[k] D` admitting a unital `k`-linear map
`σ : D →ₗ[k] C` that intertwines `(q ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D`. -/
theorem IsLinearlyReductive.of_unital_colinear {k : Type u} [Field k]
    {C : Type v} {D : Type w} [Semiring C] [Bialgebra k C] [CommSemiring D] [HopfAlgebra k D]
    (q : C →ₐc[k] D) (σ : D →ₗ[k] C) (hσ1 : σ 1 = 1)
    (hσ : ∀ x : D,
      ((q.toCoalgHom : C →ₗ[k] D).rTensor C) (Coalgebra.comul (R := k) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := k) x))
    (hC : IsLinearlyReductive.{u, v, u} k C) :
    IsLinearlyReductive.{u, w, z} k D := by
  have hD : IsLinearlyReductive.{u, w, u} k D := by
    rw [isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective]
    intro M N f hf
    exact Comodule.Hom.fixedMap_surjective_of_unital_colinear q σ hσ1 hσ hC f.hom hf
  apply IsLinearlyReductive.of_forall_isCompletelyReducible
  intro V _ _ _ _
  exact hD.isCompletelyReducible

end Coalgebra

end TauCeti
