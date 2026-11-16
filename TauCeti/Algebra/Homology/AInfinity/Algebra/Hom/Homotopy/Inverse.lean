/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Equivalence
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Homotopy
import Mathlib.Tactic.LinearCombination

/-!
# Homotopy inverses of A-infinity morphisms

Over an arbitrary commutative ring `R`, homotopy equivalences of `A∞` algebras are governed by their
linear parts: an `A∞` morphism `f : A ⟶ B` is an `A∞` homotopy equivalence if and only if its
arity-one component `f₁ = f.linearPart : (A, m₁) ⟶ (B, m₁)` admits a graded chain-homotopy inverse
(`TauCeti.AInfinityHom.isHomotopyEquiv_iff_linearPart`).

To prove sufficiency, we first upgrade a graded chain-homotopy equivalence `(f₁, g₁, s_A, s_{B,0})`
by Vogt's lemma so that `f₁ s_A - s_B f₁` is bounded by a degree-`(-2)` map `ω`, and then construct
the suspended Taylor components of a right `A∞` homotopy inverse `g` together with a homotopy
`f ∘ g ~ id_B` inductively by word length along the conilpotence filtration of `Tᶜ(sB)`.  Applying
the same construction to `g` produces a right homotopy inverse `f'` to `g`, from which homotopy
algebra upgrades `g` to a two-sided `A∞` homotopy inverse of `f`
(`TauCeti.AInfinityHom.exists_homotopy_inverse_of_linearPart`).

Over a field `K`, every `A∞` algebra contracts onto a minimal `A∞` structure on its cohomology via
homological transfer (`TauCeti.AInfinityAlgebra.cohomologyContraction`), and any quasi-isomorphism
between minimal `A∞` algebras is a strict-bar `A∞` isomorphism.  Combining these transfer
equivalences with symmetry, transitivity, and horizontal composition of homotopies shows that every
quasi-isomorphism of `A∞` algebras over a field is an `A∞` homotopy equivalence
(`TauCeti.AInfinityHom.IsQuasiIso.isHomotopyEquiv`), so `f.IsHomotopyEquiv ↔ f.IsQuasiIso`
(`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`).

## Main results

* `TauCeti.AInfinityHom.exists_homotopy_inverse_of_linearPart` and
  `TauCeti.AInfinityHom.isHomotopyEquiv_iff_linearPart`: over any commutative ring, an `A∞`
  morphism is a homotopy equivalence if and only if its linear part is a graded chain-homotopy
  equivalence, and any graded chain-homotopy inverse lifts to a two-sided `A∞` homotopy inverse.
* `TauCeti.AInfinityAlgebra.isHomotopyEquiv_transferInclusion` and
  `TauCeti.AInfinityAlgebra.isHomotopyEquiv_transferProjection`: homological transfer along a
  graded special contraction produces `A∞` homotopy equivalences.
* `TauCeti.AInfinityHom.IsQuasiIso.isHomotopyEquiv` and
  `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: **Whitehead theorem for `A∞` algebras
  over a field**; every quasi-isomorphism is an `A∞` homotopy equivalence.
* `TauCeti.AInfinityAlgebra.isHomotopyEquiv_minimalModelInclusion` and
  `TauCeti.AInfinityAlgebra.isHomotopyEquiv_minimalModelProjection`: over a field, the inclusion and
  projection of the minimal model on cohomology are `A∞` homotopy equivalences.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Section 1.3.
* M. Kontsevich and Y. Soibelman, *Deformations of associative algebras and Deligne's conjecture*,
  Section 4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uK uA uB uH

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- If `f ∘ g ~ id_B` and `g` itself has a right homotopy inverse `f'` (`g ∘ f' ~ id_A`), then
`g ∘ f ~ id_A`, so `g` is a two-sided homotopy inverse to `f`. -/
private theorem homotopic_comp_id_of_right_homotopy_inverses
    {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : (f.comp g).Homotopic (AInfinityHom.id BB))
    (hgf' : (g.comp f').Homotopic (AInfinityHom.id AA)) :
    (g.comp f).Homotopic (AInfinityHom.id AA) := by
  have h1 : (g.comp f).Homotopic ((g.comp f).comp (g.comp f')) :=
    (Homotopic.of_eq (comp_id (g.comp f)).symm).trans (hgf'.symm.compRight (g.comp f))
  have h2 : ((g.comp f).comp (g.comp f')).Homotopic (g.comp f') := by
    rw [comp_assoc, ← comp_assoc f]
    exact ((hfg.compLeft f').compRight g).trans (Homotopic.of_eq (by rw [id_comp]))
  exact (h1.trans h2).trans hgf'

/-! ### Arity-by-arity lifting of graded chain-homotopy equivalences -/

section Lifting

open ReducedTensorWords

/-- The linear part of an `A∞` morphism intertwines `differential`. -/
private theorem differential_comp_linearPart (f : AInfinityHom AA BB) :
    BB.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ AA.differential := by
  ext a
  simp only [LinearMap.comp_apply, AInfinityAlgebra.differential_apply, f.linearPart_m_one]

/-- Vogt's coherence upgrade at the chain level: given a graded chain-homotopy equivalence
`(f₁, g₁, sA, sB₀)`, modifying `sB₀` by `(f₁ ∘ sA - sB₀ ∘ f₁) ∘ g₁` yields a chain homotopy `sB`
for `id - f₁ ∘ g₁` together with `ω = -(f₁ ∘ sA - sB₀ ∘ f₁) ∘ sA` of degree `-2` satisfying
`dB ∘ ω - ω ∘ dA = f₁ ∘ sA - sB ∘ f₁`. -/
private theorem exists_coherent_chain_homotopy
    {f₁ : A →ₗ[R] B} {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB₀ : B →ₗ[R] B}
    (hf₁_hom : LinearMap.IsHomogeneous f₁ AA.grading.piece BB.grading.piece 0)
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB₀_hom : LinearMap.IsHomogeneous sB₀ BB.grading.piece BB.grading.piece (-1))
    (hf₁_d : BB.differential ∘ₗ f₁ = f₁ ∘ₗ AA.differential)
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f₁)
    (hsB₀_eq : BB.differential ∘ₗ sB₀ + sB₀ ∘ₗ BB.differential = LinearMap.id - f₁ ∘ₗ g₁) :
    ∃ (sB : B →ₗ[R] B) (ω : A →ₗ[R] B),
      LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1) ∧
      LinearMap.IsHomogeneous ω AA.grading.piece BB.grading.piece (-2) ∧
      BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f₁ ∘ₗ g₁ ∧
      BB.differential ∘ₗ ω - ω ∘ₗ AA.differential = f₁ ∘ₗ sA - sB ∘ₗ f₁ := by
  let Δ₁ : A →ₗ[R] B := f₁ ∘ₗ sA - sB₀ ∘ₗ f₁
  have hfsA : LinearMap.IsHomogeneous (f₁ ∘ₗ sA) AA.grading.piece BB.grading.piece (-1) := by
    simpa only [add_zero] using hf₁_hom.comp hsA_hom
  have hsBf : LinearMap.IsHomogeneous (sB₀ ∘ₗ f₁) AA.grading.piece BB.grading.piece (-1) := by
    simpa only [zero_add] using hsB₀_hom.comp hf₁_hom
  have hΔ₁_hom : LinearMap.IsHomogeneous Δ₁ AA.grading.piece BB.grading.piece (-1) :=
    hfsA.sub hsBf
  have hΔ₁_d : BB.differential ∘ₗ Δ₁ + Δ₁ ∘ₗ AA.differential = 0 := by
    refine LinearMap.ext fun a ↦ ?_
    have hA := LinearMap.congr_fun hsA_eq a
    have hB := LinearMap.congr_fun hsB₀_eq (f₁ a)
    have hf (x : A) : BB.differential (f₁ x) = f₁ (AA.differential x) :=
      LinearMap.congr_fun hf₁_d x
    simp only [Δ₁, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_sub] at hA hB ⊢
    have hfA := congrArg f₁ hA
    simp only [map_add, map_sub] at hfA
    rw [hf (sA a), ← hf a]
    linear_combination (norm := abel) hfA - hB
  let sB : B →ₗ[R] B := sB₀ + Δ₁ ∘ₗ g₁
  let ω : A →ₗ[R] B := -(Δ₁ ∘ₗ sA)
  have hΔg : LinearMap.IsHomogeneous (Δ₁ ∘ₗ g₁) BB.grading.piece BB.grading.piece (-1) := by
    simpa only [zero_add] using hΔ₁_hom.comp hg₁_hom
  have hΔs : LinearMap.IsHomogeneous (Δ₁ ∘ₗ sA) AA.grading.piece BB.grading.piece (-2) := by
    simpa only [show (-1 : ℤ) + (-1) = -2 by ring] using hΔ₁_hom.comp hsA_hom
  refine ⟨sB, ω, hsB₀_hom.add hΔg, hΔs.neg, ?_, ?_⟩
  · refine LinearMap.ext fun b ↦ ?_
    have hB := LinearMap.congr_fun hsB₀_eq b
    have hΔ := LinearMap.congr_fun hΔ₁_d (g₁ b)
    have hg : AA.differential (g₁ b) = g₁ (BB.differential b) := LinearMap.congr_fun hg₁_d b
    simp only [sB, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_add, ← hg] at hB hΔ ⊢
    linear_combination (norm := abel) hB + hΔ
  · refine LinearMap.ext fun a ↦ ?_
    have hΔ := LinearMap.congr_fun hΔ₁_d (sA a)
    have hA := LinearMap.congr_fun hsA_eq a
    have hsum := congrArg Δ₁ hA
    simp only [ω, sB, Δ₁, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply, map_neg, map_add,
      map_sub] at hΔ hsum ⊢
    linear_combination (norm := abel) -hΔ + hsum

/-- Exact algebraic cancellation of a single length-`k` obstruction pair `(U, V)` satisfying
`dA (U z) + U (b₁ z) = 0` and `dB (V z) - V (b₁ z) = f₁ (U z)`. -/
private theorem perturbation_cancel_apply
    {f₁ : A →ₗ[R] B} {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B} {ω : A →ₗ[R] B}
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f₁)
    (hsB_eq : BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f₁ ∘ₗ g₁)
    (hω_eq : BB.differential ∘ₗ ω - ω ∘ₗ AA.differential = f₁ ∘ₗ sA - sB ∘ₗ f₁)
    {U : ReducedTensorWords R B →ₗ[R] A} {V : ReducedTensorWords R B →ₗ[R] B}
    {z : ReducedTensorWords R B}
    (hU : AA.differential (U z) + U (BB.unaryBarDifferential z) = 0)
    (hV : BB.differential (V z) - V (BB.unaryBarDifferential z) = f₁ (U z)) :
    let δγ := -(g₁ ∘ₗ V + sA ∘ₗ U)
    let δη := sB ∘ₗ V - ω ∘ₗ U
    (AA.differential (δγ z) - δγ (BB.unaryBarDifferential z) = -U z) ∧
      (f₁ (δγ z) - (BB.differential (δη z) + δη (BB.unaryBarDifferential z)) = -V z) := by
  have hUb : U (BB.unaryBarDifferential z) = -AA.differential (U z) :=
    eq_neg_of_add_eq_zero_right hU
  have hVb : V (BB.unaryBarDifferential z) = BB.differential (V z) - f₁ (U z) := by
    linear_combination (norm := abel) -hV
  have hgV : AA.differential (g₁ (V z)) = g₁ (BB.differential (V z)) :=
    LinearMap.congr_fun hg₁_d (V z)
  have hsAU := LinearMap.congr_fun hsA_eq (U z)
  have hsBV := LinearMap.congr_fun hsB_eq (V z)
  have hωU := LinearMap.congr_fun hω_eq (U z)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hsAU hsBV hωU
  refine ⟨?_, ?_⟩
  · simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.comp_apply, map_neg, map_add,
      hgV, hUb, hVb, map_sub]
    linear_combination (norm := abel) -hsAU
  · simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      map_neg, map_add, map_sub, hUb, hVb]
    linear_combination (norm := abel) -hsBV + hωU

/-- `ReducedTensorWords.map` preserves the word-length filtration. -/
private theorem map_mem_filtration (φ : B →ₗ[R] B) {n : ℕ} {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B n) :
    ReducedTensorWords.map (R := R) φ z ∈ filtration R B n := by
  have h : filtration R B n ≤ (filtration R B n).comap (ReducedTensorWords.map (R := R) φ) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, ReducedTensorWords.map_of]
    exact of_mem_filtration R B hk _
  exact h hz

/-- `lengthProj` commutes with `unaryBarDifferential`. -/
private theorem lengthProj_comp_unaryBarDifferential (k : {k : ℕ // 0 < k}) :
    lengthProj R B k ∘ₗ BB.unaryBarDifferential = BB.unaryBarDifferential ∘ₗ lengthProj R B k := by
  have hlet : (BB.differential ∘ₗ letter R B) ∘ₗ lengthProj R B ⟨1, Nat.one_pos⟩ =
      BB.differential ∘ₗ letter R B := by
    refine linearMap_ext R B fun m x ↦ ?_
    simp only [LinearMap.comp_apply]
    by_cases hm : m = ⟨1, Nat.one_pos⟩
    · subst hm; rw [lengthProj_of_self]
    · rw [lengthProj_of_of_ne R B hm, map_zero, letter_of_of_ne_one R B hm, map_zero]
  rw [BB.unaryBarDifferential_eq_gradedCoderiv]
  exact lengthProj_comp_gradedCoderiv (BB.grading.shift 1) 1 hlet rfl

/-- Adding a perturbation `δγ` that vanishes on `filtration R B n` leaves `coalgHom R γ` unchanged
on `filtration R B n` and adds `ofLetter R A (δγ z)` on `filtration R B (n + 1)`. -/
private theorem coalgHom_add_apply_of_mem_filtration
    {γ δγ : ReducedTensorWords R B →ₗ[R] A} {n : ℕ}
    (hδγ : ∀ w ∈ filtration R B n, δγ w = 0) :
    (∀ w ∈ filtration R B n, coalgHom R (γ + δγ) w = coalgHom R γ w) ∧
      ∀ z ∈ filtration R B (n + 1),
        coalgHom R (γ + δγ) z = coalgHom R γ z + ofLetter R A (δγ z) := by
  have hle : ∀ w ∈ filtration R B n, coalgHom R (γ + δγ) w = coalgHom R γ w := fun w hw ↦
    (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun u hu ↦ by
        simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom, LinearMap.add_apply,
          hδγ u hu, add_zero]) hw
  refine ⟨hle, fun z hz ↦ eq_of_deconcatenation_eq_of_letter_eq R A ?_ ?_⟩
  · rw [(isCoalgHom_coalgHom _).deconcatenation_apply, map_add,
      (isCoalgHom_coalgHom _).deconcatenation_apply, deconcatenation_ofLetter, add_zero]
    obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
    rw [← hw]; clear hw
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
          hle u.1 u.2, hle v.1 v.2]
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [map_add, ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
      ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom, letter_ofLetter,
      LinearMap.add_apply]

/-- Two `gradedCoderivAlong` homotopies whose left coalgebra maps and Taylor maps agree on
`filtration R B n` agree on `filtration R B n`. -/
private theorem gradedCoderivAlong_congr_of_mem_filtration
    {P₁ P₂ : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B}
    (hP₁ : IsCoalgHom R P₁) (hP₂ : IsCoalgHom R P₂)
    {η₁ η₂ : ReducedTensorWords R B →ₗ[R] B} {n : ℕ}
    (hP : ∀ w ∈ filtration R B n, P₁ w = P₂ w)
    (hη : ∀ w ∈ filtration R B n, η₁ w = η₂ w) :
    ∀ w ∈ filtration R B n,
      gradedCoderivAlong (BB.grading.shift 1) 1 P₁ LinearMap.id η₁ w =
        gradedCoderivAlong (BB.grading.shift 1) 1 P₂ LinearMap.id η₂ w := by
  suffices ∀ k ≤ n, ∀ w ∈ filtration R B k,
      gradedCoderivAlong (BB.grading.shift 1) 1 P₁ LinearMap.id η₁ w =
        gradedCoderivAlong (BB.grading.shift 1) 1 P₂ LinearMap.id η₂ w from this n le_rfl
  intro k hkn
  induction k with
  | zero =>
      intro w hw
      rw [filtration_zero, Submodule.mem_bot] at hw
      simp only [hw, map_zero]
  | succ k ih =>
      intro w hw
      have ih' := ih (Nat.le_of_succ_le hkn)
      refine eq_of_deconcatenation_eq_of_letter_eq R B ?_ ?_
      · rw [(isGradedCoderivationAlong_gradedCoderivAlong _ _ hP₁ (isCoalgHom_id B) _
            ).deconcatenation_apply,
          (isGradedCoderivationAlong_gradedCoderivAlong _ _ hP₂ (isCoalgHom_id B) _
            ).deconcatenation_apply]
        obtain ⟨t, ht⟩ := map_deconcatenation_filtration_succ_le R B k ⟨w, hw, rfl⟩
        rw [← ht]; clear ht
        induction t using TensorProduct.inductionOn with
        | tmul u v =>
            have hτu : ReducedTensorWords.map (R := R)
                ((BB.grading.shift 1).koszulTwist 1) u.1 ∈ filtration R B n :=
              filtration_monotone R B (Nat.le_of_succ_le hkn) (map_mem_filtration _ u.2)
            simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
              LinearMap.rTensor_tmul, LinearMap.id_apply, ih' u.1 u.2, ih' v.1 v.2, hP _ hτu]
        | add x y hx hy =>
            simp only [map_add] at hx hy ⊢
            rw [add_add_add_comm, hx, hy, add_add_add_comm]
      · simp only [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
          hη w (filtration_monotone R B hkn hw)]

/-- Adding a perturbation `δη` vanishing on `filtration R B n` while updating `P₁` to `P₂` agreeing
with `P₁` on `filtration R B n` shifts `gradedCoderivAlong` by `ofLetter R B (δη z)` on
`filtration R B (n + 1)`. -/
private theorem gradedCoderivAlong_add_of_mem_filtration
    {P₁ P₂ : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B}
    (hP₁ : IsCoalgHom R P₁) (hP₂ : IsCoalgHom R P₂)
    {η δη : ReducedTensorWords R B →ₗ[R] B} {n : ℕ}
    (hP : ∀ w ∈ filtration R B n, P₁ w = P₂ w)
    (hδη : ∀ w ∈ filtration R B n, δη w = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    gradedCoderivAlong (BB.grading.shift 1) 1 P₂ LinearMap.id (η + δη) z =
      gradedCoderivAlong (BB.grading.shift 1) 1 P₁ LinearMap.id η z + ofLetter R B (δη z) := by
  have hle : ∀ w ∈ filtration R B n,
      gradedCoderivAlong (BB.grading.shift 1) 1 P₂ LinearMap.id (η + δη) w =
        gradedCoderivAlong (BB.grading.shift 1) 1 P₁ LinearMap.id η w :=
    gradedCoderivAlong_congr_of_mem_filtration hP₂ hP₁ (fun w hw ↦ (hP w hw).symm)
      (fun u hu ↦ by rw [LinearMap.add_apply, hδη u hu, add_zero])
  refine eq_of_deconcatenation_eq_of_letter_eq R B ?_ ?_
  · rw [(isGradedCoderivationAlong_gradedCoderivAlong _ _ hP₂ (isCoalgHom_id B) _
        ).deconcatenation_apply, map_add,
      (isGradedCoderivationAlong_gradedCoderivAlong _ _ hP₁ (isCoalgHom_id B) _
        ).deconcatenation_apply, deconcatenation_ofLetter, add_zero]
    obtain ⟨t, ht⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
    rw [← ht]; clear ht
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
        have hτu := map_mem_filtration ((BB.grading.shift 1).koszulTwist 1) u.2
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
          LinearMap.rTensor_tmul, LinearMap.id_apply, hle u.1 u.2, hle v.1 v.2, (hP _ hτu).symm]
    | add x y hx hy =>
        simp only [map_add] at hx hy ⊢
        rw [add_add_add_comm, hx, hy, add_add_add_comm]
  · rw [map_add, ← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
      ← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong, letter_ofLetter,
      LinearMap.add_apply]

/-- When the morphism Taylor defect `AA.taylor ∘ coalgHom γ - γ ∘ BB.barDifferential` vanishes on
`filtration R B n`, the bar-level defect `M = b_A ∘ G - G ∘ b_B` vanishes on `filtration R B n` and
equals `ofLetter R A (mDef z)` on `filtration R B (n + 1)`. -/
private theorem barDefectM_of_mem_filtration {γ : ReducedTensorWords R B →ₗ[R] A}
    (hγ_hom : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0) {n : ℕ}
    (hm : ∀ w ∈ filtration R B n, (AA.taylor ∘ₗ coalgHom R γ - γ ∘ₗ BB.barDifferential) w = 0) :
    let G := coalgHom R γ
    let M := AA.barDifferential ∘ₗ G - G ∘ₗ BB.barDifferential
    (∀ w ∈ filtration R B n, M w = 0) ∧
      ∀ z ∈ filtration R B (n + 1),
        M z = ofLetter R A ((AA.taylor ∘ₗ G - γ ∘ₗ BB.barDifferential) z) := by
  intro G M
  have hG : IsCoalgHom R G := isCoalgHom_coalgHom γ
  have hG_hom := isHomogeneous_coalgHom hγ_hom
  have hM_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 G G M := by
    have hMeq : M = AA.barDifferential ∘ₗ G + (-1 : R) • (G ∘ₗ BB.barDifferential) :=
      LinearMap.ext fun x ↦ by
        simp only [M, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
          neg_one_smul, sub_eq_add_neg]
    rw [hMeq]
    exact (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hG hG_hom).add
      ((hG.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential).smul (-1 : R))
  have hM_let : letter R A ∘ₗ M = AA.taylor ∘ₗ G - γ ∘ₗ BB.barDifferential := by
    rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, AA.letter_comp_barDifferential,
      ← LinearMap.comp_assoc, letter_comp_coalgHom]
  have hM_zero : ∀ w ∈ filtration R B n, M w = 0 := fun w hw ↦
    hM_cod.apply_eq_of_mem_filtration (isGradedCoderivationAlong_zero _ _ G G)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun u hu ↦ by
        rw [← LinearMap.comp_apply (letter R A), hM_let, hm u hu, LinearMap.zero_apply, map_zero])
      hw
  refine ⟨hM_zero, fun z hz ↦ eq_of_deconcatenation_eq_of_letter_eq R A ?_ ?_⟩
  · rw [hM_cod.deconcatenation_apply, deconcatenation_ofLetter]
    obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
    rw [← hw]; clear hw
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
          LinearMap.rTensor_tmul, hM_zero u.1 u.2, hM_zero v.1 v.2,
          TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
    | add x y hx hy =>
        simp only [map_add] at hx hy ⊢
        rw [add_add_add_comm, hx, hy, add_zero]
  · rw [← LinearMap.comp_apply (letter R A), hM_let, letter_ofLetter]

/-- Deconcatenation of the bar-level homotopy defect
`E = (P - id) - (b_B ∘ H + H ∘ b_B)` on `filtration R B (n + 1)` when `b_B` commutes with `P` on
`filtration R B n`. -/
private theorem deconcatenation_barDefectE_of_mem_filtration
    {P H : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B}
    (hP : IsCoalgHom R P)
    (hP_hom : LinearMap.IsHomogeneous P (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0)
    (hH : IsGradedCoderivationAlong (BB.grading.shift 1) 1 P LinearMap.id H)
    (hH_hom : LinearMap.IsHomogeneous H (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1))
    {n : ℕ} (hP_int : ∀ u ∈ filtration R B n, BB.barDifferential (P u) = P (BB.barDifferential u))
    {w : ReducedTensorWords R B} (hw : w ∈ filtration R B (n + 1)) :
    let E := (P - LinearMap.id) - (BB.barDifferential ∘ₗ H + H ∘ₗ BB.barDifferential)
    deconcatenation R B (E w) =
      TensorProduct.map E LinearMap.id (deconcatenation R B w) +
        TensorProduct.map P E (deconcatenation R B w) := by
  intro E
  set τ := ReducedTensorWords.map (R := R) ((BB.grading.shift 1).koszulTwist 1)
  have hτP : ∀ u, τ (P u) = P (τ u) := fun u ↦ by
    simpa only [τ, mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hP_hom.map_koszulTwist_comp 1) u
  have hττ : ∀ u, τ (τ u) = u := fun u ↦ by
    simp only [τ, ← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]
  have hτH : ∀ u, τ (H u) = -H (τ u) := fun u ↦ by
    simpa only [τ, one_mul, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hH_hom.map_koszulTwist_comp 1) u
  have hτb : ∀ u, τ (BB.barDifferential u) = -BB.barDifferential (τ u) := fun u ↦
    eq_neg_of_add_eq_zero_right
      (LinearMap.congr_fun BB.isHomogeneous_barDifferential.anticommute_map_koszulTwist_one u)
  set Δb := TensorProduct.map BB.barDifferential LinearMap.id +
    TensorProduct.map LinearMap.id BB.barDifferential ∘ₗ LinearMap.rTensor _ τ
  set ΔH := TensorProduct.map H LinearMap.id +
    TensorProduct.map P H ∘ₗ LinearMap.rTensor _ τ
  have hLHS : deconcatenation R B (E w) =
      TensorProduct.map P P (deconcatenation R B w) -
        (LinearMap.id : _ →ₗ[R] _) (deconcatenation R B w) -
        (Δb ∘ₗ ΔH + ΔH ∘ₗ Δb) (deconcatenation R B w) := by
    simp only [E, Δb, ΔH, τ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add, hP.deconcatenation_apply,
      (isGradedCoderivationAlong_id_id_iff.2
        BB.isGradedCoderivation_barDifferential).deconcatenation_apply,
      hH.deconcatenation_apply]
    abel
  obtain ⟨t, ht⟩ := map_deconcatenation_filtration_succ_le R B n ⟨w, hw, rfl⟩
  rw [hLHS, sub_eq_iff_eq_add, sub_eq_iff_eq_add, ← LinearMap.add_apply, ← LinearMap.add_apply,
    ← LinearMap.add_apply, ← ht, ← LinearMap.comp_apply, ← LinearMap.comp_apply]
  refine LinearMap.congr_fun (TensorProduct.ext' fun u v ↦ ?_) t
  have hPu : BB.barDifferential (P (τ u)) = P (BB.barDifferential (τ u)) :=
    hP_int _ (map_mem_filtration ((BB.grading.shift 1).koszulTwist 1) u.2)
  simp only [Δb, ΔH, E, TensorProduct.mapIncl, Submodule.coe_subtype, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, TensorProduct.map_tmul,
    LinearMap.rTensor_tmul, map_add, hτP, hτH, hτb, hττ, hPu, map_neg]
  simp only [TensorProduct.neg_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- When both `mDef` and `eDef` vanish on `filtration R B n`, the bar-level homotopy defect
`E = (F ∘ G - id) - (b_B ∘ H + H ∘ b_B)` vanishes on `filtration R B n` and equals
`ofLetter R B (eDef z)` on `filtration R B (n + 1)`. -/
private theorem barDefectE_of_mem_filtration (f : AInfinityHom AA BB)
    {γ : ReducedTensorWords R B →ₗ[R] A} {η : ReducedTensorWords R B →ₗ[R] B}
    (hγ_hom : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0)
    (hη_hom : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1)) {n : ℕ}
    (hM_zero : ∀ w ∈ filtration R B n,
      (AA.barDifferential ∘ₗ coalgHom R γ - coalgHom R γ ∘ₗ BB.barDifferential) w = 0)
    (he : ∀ w ∈ filtration R B n,
      (f.taylor ∘ₗ coalgHom R γ - letter R B -
        (BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R γ) LinearMap.id η + η ∘ₗ BB.barDifferential)) w = 0) :
    let G := coalgHom R γ
    let H := gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ G) LinearMap.id η
    let E := (f.barMap ∘ₗ G - LinearMap.id) - (BB.barDifferential ∘ₗ H + H ∘ₗ BB.barDifferential)
    (∀ w ∈ filtration R B n, E w = 0) ∧
      ∀ z ∈ filtration R B (n + 1),
        E z = ofLetter R B ((f.taylor ∘ₗ G - letter R B -
          (BB.taylor ∘ₗ H + η ∘ₗ BB.barDifferential)) z) := by
  intro G H E
  have hP : IsCoalgHom R (f.barMap ∘ₗ G) := f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ)
  have hP_hom : LinearMap.IsHomogeneous (f.barMap ∘ₗ G) (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom hγ_hom)
  have hH : IsGradedCoderivationAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ G) LinearMap.id H :=
    isGradedCoderivationAlong_gradedCoderivAlong _ _ hP (isCoalgHom_id B) η
  have hH_hom := isHomogeneous_gradedCoderivAlong (q := 1) hP_hom
    (LinearMap.isHomogeneous_id _) hη_hom
  have hP_int : ∀ u ∈ filtration R B n,
      BB.barDifferential ((f.barMap ∘ₗ G) u) = (f.barMap ∘ₗ G) (BB.barDifferential u) :=
    fun u hu ↦ by
      have hMu := hM_zero u hu
      simp only [G, LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero] at hMu ⊢
      rw [f.barDifferential_barMap, hMu]
  have hE_let : letter R B ∘ₗ E = f.taylor ∘ₗ G - letter R B -
      (BB.taylor ∘ₗ H + η ∘ₗ BB.barDifferential) := by
    simp only [E, H, LinearMap.comp_sub, LinearMap.comp_add, ← LinearMap.comp_assoc,
      f.taylor_def, LinearMap.comp_id, BB.letter_comp_barDifferential,
      letter_comp_gradedCoderivAlong]
  have hΔ_zero : ∀ {k : ℕ} {w : ReducedTensorWords R B}, w ∈ filtration R B (k + 1) →
      (∀ u ∈ filtration R B k, E u = 0) →
      TensorProduct.map E LinearMap.id (deconcatenation R B w) +
        TensorProduct.map (f.barMap ∘ₗ G) E (deconcatenation R B w) = 0 := fun hw hEk ↦ by
    obtain ⟨t, ht⟩ := map_deconcatenation_filtration_succ_le R B _ ⟨_, hw, rfl⟩
    rw [← ht, ← LinearMap.add_apply, ← LinearMap.comp_apply]
    refine LinearMap.congr_fun (TensorProduct.ext' (h := 0) fun u v ↦ ?_) t
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.zero_apply,
      TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype, LinearMap.id_apply,
      hEk u.1 u.2, hEk v.1 v.2, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  have hE_zero : ∀ k ≤ n, ∀ w ∈ filtration R B k, E w = 0 := fun k ↦ by
    induction k with
    | zero =>
        intro _ w hw
        rw [filtration_zero, Submodule.mem_bot] at hw
        simp only [hw, map_zero]
    | succ k ih =>
        intro hkn w hw
        have hw' := filtration_monotone R B (Nat.succ_le_succ (Nat.le_of_succ_le hkn)) hw
        refine eq_of_deconcatenation_eq_of_letter_eq R B ?_ ?_
        · rw [deconcatenation_barDefectE_of_mem_filtration hP hP_hom hH hH_hom hP_int hw',
            map_zero, hΔ_zero hw (ih (Nat.le_of_succ_le hkn))]
        · rw [← LinearMap.comp_apply (letter R B), hE_let, he w (filtration_monotone R B hkn hw),
            map_zero]
  refine ⟨hE_zero n le_rfl, fun z hz ↦ eq_of_deconcatenation_eq_of_letter_eq R B ?_ ?_⟩
  · rw [deconcatenation_barDefectE_of_mem_filtration hP hP_hom hH hH_hom hP_int hz,
      deconcatenation_ofLetter, hΔ_zero hz (hE_zero n le_rfl)]
  · rw [← LinearMap.comp_apply (letter R B), hE_let, letter_ofLetter]

/-- Obstruction cycle equations on `filtration R B (n + 1)`: when `mDef` and `eDef` vanish on
`filtration R B n`, on `z ∈ filtration R B (n + 1)` they satisfy `dA (mDef z) + mDef (b₁ z) = 0`
and `dB (eDef z) - eDef (b₁ z) = f₁ (mDef z)` with respect to `b₁ = BB.unaryBarDifferential`. -/
private theorem taylorDefect_cycle_eqs_of_mem_filtration (f : AInfinityHom AA BB)
    {γ : ReducedTensorWords R B →ₗ[R] A} {η : ReducedTensorWords R B →ₗ[R] B}
    (hγ_hom : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0)
    (hη_hom : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1)) {n : ℕ}
    (hm : ∀ w ∈ filtration R B n, (AA.taylor ∘ₗ coalgHom R γ - γ ∘ₗ BB.barDifferential) w = 0)
    (he : ∀ w ∈ filtration R B n,
      (f.taylor ∘ₗ coalgHom R γ - letter R B -
        (BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R γ) LinearMap.id η + η ∘ₗ BB.barDifferential)) w = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    let G := coalgHom R γ
    let H := gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ G) LinearMap.id η
    let mDef := AA.taylor ∘ₗ G - γ ∘ₗ BB.barDifferential
    let eDef := f.taylor ∘ₗ G - letter R B - (BB.taylor ∘ₗ H + η ∘ₗ BB.barDifferential)
    (AA.differential (mDef z) + mDef (BB.unaryBarDifferential z) = 0) ∧
      (BB.differential (eDef z) - eDef (BB.unaryBarDifferential z) = f.linearPart (mDef z)) := by
  intro G H mDef eDef
  set M := AA.barDifferential ∘ₗ G - G ∘ₗ BB.barDifferential
  set E := (f.barMap ∘ₗ G - LinearMap.id) - (BB.barDifferential ∘ₗ H + H ∘ₗ BB.barDifferential)
  obtain ⟨hM_zero, hM_succ'⟩ := barDefectM_of_mem_filtration (AA := AA) (BB := BB) hγ_hom hm
  obtain ⟨hE_zero, hE_succ'⟩ := barDefectE_of_mem_filtration f hγ_hom hη_hom hM_zero he
  have hM_succ : ∀ u ∈ filtration R B (n + 1), M u = ofLetter R A (mDef u) := hM_succ'
  have hE_succ : ∀ u ∈ filtration R B (n + 1), E u = ofLetter R B (eDef u) := hE_succ'
  have hz_u : BB.unaryBarDifferential z ∈ filtration R B (n + 1) :=
    BB.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩
  have hz_h : BB.higherBarDifferential z ∈ filtration R B n :=
    BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩
  have hbz : BB.barDifferential z = BB.unaryBarDifferential z + BB.higherBarDifferential z := by
    rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply]
  have hbA (a : A) : AA.barDifferential (ofLetter R A a) = ofLetter R A (AA.differential a) := by
    rw [AA.barDifferential_ofLetter, AA.differential_apply]
  have hbB (b : B) : BB.barDifferential (ofLetter R B b) = ofLetter R B (BB.differential b) := by
    rw [BB.barDifferential_ofLetter, BB.differential_apply]
  have hMb : AA.barDifferential (M z) + M (BB.barDifferential z) = 0 := by
    have h1 := LinearMap.congr_fun AA.barDifferential_sq (G z)
    have h2 := LinearMap.congr_fun BB.barDifferential_sq z
    simp only [M, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      map_sub] at h1 h2 ⊢
    rw [h1, h2, map_zero]; abel
  have hEb : BB.barDifferential (E z) - E (BB.barDifferential z) = f.barMap (M z) := by
    have h1 := LinearMap.congr_fun BB.barDifferential_sq (H z)
    have h2 := LinearMap.congr_fun BB.barDifferential_sq z
    simp only [E, M, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_sub, map_add,
      f.barDifferential_barMap] at h1 h2 ⊢
    rw [h1, h2, map_zero]; abel
  rw [hbz, map_add, hM_zero _ hz_h, add_zero, hM_succ z hz, hM_succ _ hz_u, hbA] at hMb
  rw [hbz, map_add, hE_zero _ hz_h, add_zero, hE_succ z hz, hE_succ _ hz_u, hbB,
    hM_succ z hz, f.barMap_ofLetter] at hEb
  exact ⟨by simpa only [map_add, letter_ofLetter, map_zero] using congrArg (letter R A) hMb,
    by simpa only [map_sub, letter_ofLetter] using congrArg (letter R B) hEb⟩

/-- Data carried at filtration stage `n` of the right-homotopy-inverse construction: suspended
Taylor maps `(γ, η)` of degrees `0` and `-1` whose morphism and homotopy Taylor defects vanish on
`filtration R B (n + 1)`. -/
private structure LiftStage (f : AInfinityHom AA BB) where
  γ : ReducedTensorWords R B →ₗ[R] A
  η : ReducedTensorWords R B →ₗ[R] B
  hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  hη : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1)

/-- Base stage (`n = 0`, valid on `filtration R B 1`): `γ₀ = g₁ ∘ letter` and
`η₀ = -sB ∘ letter`. -/
private noncomputable def liftStageBase (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1)) :
    LiftStage f where
  γ := g₁ ∘ₗ letter R B
  η := -(sB ∘ₗ letter R B)
  hγ := by
    simpa only [add_zero] using (LinearMap.isHomogeneous_shift_piece_iff.2 hg₁_hom).comp
      (isHomogeneous_letter (BB.grading.shift 1))
  hη := by
    have h : LinearMap.IsHomogeneous (sB ∘ₗ letter R B) (gradedPiece (BB.grading.shift 1))
        (BB.grading.shift 1).piece (-1) := by
      simpa only [zero_add] using (LinearMap.isHomogeneous_shift_piece_iff.2 hsB_hom).comp
        (isHomogeneous_letter (BB.grading.shift 1))
    exact h.neg

private theorem liftStageBase_defects (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsB_eq : BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁) :
    let S := liftStageBase f hg₁_hom hsB_hom
    (∀ z ∈ filtration R B 1, (AA.taylor ∘ₗ coalgHom R S.γ - S.γ ∘ₗ BB.barDifferential) z = 0) ∧
    (∀ z ∈ filtration R B 1,
      (f.taylor ∘ₗ coalgHom R S.γ - letter R B -
        (BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R S.γ) LinearMap.id S.η + S.η ∘ₗ BB.barDifferential)) z = 0) := by
  intro S
  refine ⟨apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_),
    apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_)⟩
  · have hg := LinearMap.congr_fun hg₁_d b
    simp only [S, liftStageBase, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      coalgHom_ofLetter, letter_ofLetter, AA.taylor_ofLetter, BB.barDifferential_ofLetter,
      ← AA.differential_apply, ← BB.differential_apply] at hg ⊢
    exact sub_eq_zero.2 hg
  · have hs := LinearMap.congr_fun hsB_eq b
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hs
    simp only [S, liftStageBase, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.neg_apply, LinearMap.zero_apply, coalgHom_ofLetter,
      gradedCoderivAlong_ofLetter, letter_ofLetter, f.taylor_def, f.barMap_ofLetter, map_neg,
      BB.taylor_ofLetter, BB.barDifferential_ofLetter, ← BB.differential_apply]
    linear_combination (norm := abel) hs

/-- Homogeneity of the length-`(n + 2)` projected defect maps `U` and `V` at stage `S`. -/
private theorem isHomogeneous_liftStageStep_UV (f : AInfinityHom AA BB) (n : ℕ)
    (S : LiftStage f) :
    let π := lengthProj R B ⟨n + 2, Nat.succ_pos _⟩
    let G := coalgHom R S.γ
    let H := gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ G) LinearMap.id S.η
    LinearMap.IsHomogeneous ((AA.taylor ∘ₗ G - S.γ ∘ₗ BB.barDifferential) ∘ₗ π)
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 1 ∧
    LinearMap.IsHomogeneous
      ((f.taylor ∘ₗ G - letter R B - (BB.taylor ∘ₗ H + S.η ∘ₗ BB.barDifferential)) ∘ₗ π)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
  intro π G H
  have hG_hom := isHomogeneous_coalgHom S.hγ
  have hπ_hom := isHomogeneous_lengthProj (BB.grading.shift 1) ⟨n + 2, Nat.succ_pos _⟩
  have hm₁ : LinearMap.IsHomogeneous (AA.taylor ∘ₗ G) (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 1 := by
    simpa only [zero_add] using (AA.taylor_isSuspension.isHomogeneous AA.m_degree).comp hG_hom
  have hm₂ : LinearMap.IsHomogeneous (S.γ ∘ₗ BB.barDifferential) (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 1 := by
    simpa only [add_zero] using S.hγ.comp BB.isHomogeneous_barDifferential
  have hP_hom : LinearMap.IsHomogeneous (f.barMap ∘ₗ G) (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp hG_hom
  have hH_hom := isHomogeneous_gradedCoderivAlong (q := 1) hP_hom
    (LinearMap.isHomogeneous_id _) S.hη
  have he₁ : LinearMap.IsHomogeneous (f.taylor ∘ₗ G) (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
    simpa only [add_zero] using f.isHomogeneous_taylor.comp hG_hom
  have he₂ : LinearMap.IsHomogeneous (BB.taylor ∘ₗ H) (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
    simpa only [neg_add_cancel] using (BB.taylor_isSuspension.isHomogeneous BB.m_degree).comp hH_hom
  have he₃ : LinearMap.IsHomogeneous (S.η ∘ₗ BB.barDifferential) (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
    simpa only [add_neg_cancel] using S.hη.comp BB.isHomogeneous_barDifferential
  exact ⟨by simpa only [zero_add] using (hm₁.sub hm₂).comp hπ_hom,
    by simpa only [zero_add] using
      ((he₁.sub (isHomogeneous_letter (BB.grading.shift 1))).sub (he₂.add he₃)).comp hπ_hom⟩

/-- Inductive step from `filtration R B (n + 1)` to `filtration R B (n + 2)`. -/
private noncomputable def liftStageStep (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B} {ω : A →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hω_hom : LinearMap.IsHomogeneous ω AA.grading.piece BB.grading.piece (-2))
    (n : ℕ) (S : LiftStage f) : LiftStage f :=
  let π := lengthProj R B ⟨n + 2, Nat.succ_pos _⟩
  let G := coalgHom R S.γ
  let H := gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ G) LinearMap.id S.η
  let U := (AA.taylor ∘ₗ G - S.γ ∘ₗ BB.barDifferential) ∘ₗ π
  let V := (f.taylor ∘ₗ G - letter R B - (BB.taylor ∘ₗ H + S.η ∘ₗ BB.barDifferential)) ∘ₗ π
  { γ := S.γ + -(g₁ ∘ₗ V + sA ∘ₗ U)
    η := S.η + (sB ∘ₗ V - ω ∘ₗ U)
    hγ := by
      obtain ⟨hU_hom, hV_hom⟩ := isHomogeneous_liftStageStep_UV f n S
      have h1 : LinearMap.IsHomogeneous (g₁ ∘ₗ V) (gradedPiece (BB.grading.shift 1))
          (AA.grading.shift 1).piece 0 := by
        simpa only [add_zero] using (LinearMap.isHomogeneous_shift_piece_iff.2 hg₁_hom).comp hV_hom
      have h2 : LinearMap.IsHomogeneous (sA ∘ₗ U) (gradedPiece (BB.grading.shift 1))
          (AA.grading.shift 1).piece 0 := by
        simpa only [add_neg_cancel] using
          (LinearMap.isHomogeneous_shift_piece_iff.2 hsA_hom).comp hU_hom
      exact S.hγ.add (h1.add h2).neg
    hη := by
      obtain ⟨hU_hom, hV_hom⟩ := isHomogeneous_liftStageStep_UV f n S
      have h1 : LinearMap.IsHomogeneous (sB ∘ₗ V) (gradedPiece (BB.grading.shift 1))
          (BB.grading.shift 1).piece (-1) := by
        simpa only [zero_add] using (LinearMap.isHomogeneous_shift_piece_iff.2 hsB_hom).comp hV_hom
      have h2 : LinearMap.IsHomogeneous (ω ∘ₗ U) (gradedPiece (BB.grading.shift 1))
          (BB.grading.shift 1).piece (-1) := by
        simpa only [show (1 : ℤ) + (-2) = -1 by ring] using
          (LinearMap.isHomogeneous_shift_piece_iff.2 hω_hom).comp hU_hom
      exact S.hη.add (h1.sub h2) }

/-- `liftStageStep` agrees with `S` on `filtration R B (n + 1)`. -/
private theorem liftStageStep_agrees (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B} {ω : A →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hω_hom : LinearMap.IsHomogeneous ω AA.grading.piece BB.grading.piece (-2))
    (n : ℕ) (S : LiftStage f) :
    let S' := liftStageStep f hg₁_hom hsA_hom hsB_hom hω_hom n S
    (∀ w ∈ filtration R B (n + 1), S'.γ w = S.γ w) ∧
    (∀ w ∈ filtration R B (n + 1), S'.η w = S.η w) := by
  intro S'
  have hπ : ∀ w ∈ filtration R B (n + 1),
      lengthProj R B ⟨n + 2, Nat.succ_pos _⟩ w = 0 := fun w hw ↦
    lengthProj_apply_eq_zero_of_mem_filtration R B (Nat.lt_succ_self (n + 1)) hw
  exact ⟨fun w hw ↦ by
      simp only [S', liftStageStep, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        hπ w hw, map_zero, add_zero, neg_zero],
    fun w hw ↦ by
      simp only [S', liftStageStep, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        hπ w hw, map_zero, sub_self, add_zero]⟩

private theorem bar_add_of_mem_filtration (f : AInfinityHom AA BB)
    (γ : ReducedTensorWords R B →ₗ[R] A) {δγ : ReducedTensorWords R B →ₗ[R] A}
    (η : ReducedTensorWords R B →ₗ[R] B) {δη : ReducedTensorWords R B →ₗ[R] B} {n : ℕ}
    (hδγ : ∀ w ∈ filtration R B (n + 1), δγ w = 0)
    (hδη : ∀ w ∈ filtration R B (n + 1), δη w = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 2)) :
    coalgHom R (γ + δγ) z = coalgHom R γ z + ofLetter R A (δγ z) ∧
      gradedCoderivAlong (BB.grading.shift 1) 1
        (f.barMap ∘ₗ coalgHom R (γ + δγ)) LinearMap.id (η + δη) z =
        gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R γ) LinearMap.id η z + ofLetter R B (δη z) := by
  obtain ⟨hG_eq, hG_add⟩ := coalgHom_add_apply_of_mem_filtration (γ := γ) hδγ
  exact ⟨hG_add z hz, gradedCoderivAlong_add_of_mem_filtration
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ))
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (γ + δγ)))
    (fun w hw ↦ by rw [LinearMap.comp_apply, LinearMap.comp_apply, (hG_eq w hw).symm]) hδη hz⟩

/-- `liftStageStep` kills both Taylor defects on `filtration R B (n + 2)`. -/
private theorem liftStageStep_defects (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B} {ω : A →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hω_hom : LinearMap.IsHomogeneous ω AA.grading.piece BB.grading.piece (-2))
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart)
    (hsB_eq : BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁)
    (hω_eq : BB.differential ∘ₗ ω - ω ∘ₗ AA.differential = f.linearPart ∘ₗ sA - sB ∘ₗ f.linearPart)
    (n : ℕ) (S : LiftStage f)
    (hm : ∀ w ∈ filtration R B (n + 1),
      (AA.taylor ∘ₗ coalgHom R S.γ - S.γ ∘ₗ BB.barDifferential) w = 0)
    (he : ∀ w ∈ filtration R B (n + 1),
      (f.taylor ∘ₗ coalgHom R S.γ - letter R B -
        (BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R S.γ) LinearMap.id S.η + S.η ∘ₗ BB.barDifferential)) w = 0) :
    let S' := liftStageStep f hg₁_hom hsA_hom hsB_hom hω_hom n S
    (∀ z ∈ filtration R B (n + 2),
      (AA.taylor ∘ₗ coalgHom R S'.γ - S'.γ ∘ₗ BB.barDifferential) z = 0) ∧
    (∀ z ∈ filtration R B (n + 2),
      (f.taylor ∘ₗ coalgHom R S'.γ - letter R B -
        (BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R S'.γ) LinearMap.id S'.η +
          S'.η ∘ₗ BB.barDifferential)) z = 0) := by
  intro S'
  set π := lengthProj R B ⟨n + 2, Nat.succ_pos _⟩; set G := coalgHom R S.γ
  set H := gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ G) LinearMap.id S.η
  set mDef := AA.taylor ∘ₗ G - S.γ ∘ₗ BB.barDifferential
  set eDef := f.taylor ∘ₗ G - letter R B - (BB.taylor ∘ₗ H + S.η ∘ₗ BB.barDifferential)
  set U := mDef ∘ₗ π; set V := eDef ∘ₗ π
  set δγ := -(g₁ ∘ₗ V + sA ∘ₗ U); set δη := sB ∘ₗ V - ω ∘ₗ U
  have hπ_zero : ∀ w ∈ filtration R B (n + 1), π w = 0 := fun w hw ↦
    lengthProj_apply_eq_zero_of_mem_filtration R B (Nat.lt_succ_self (n + 1)) hw
  have hδγ_zero : ∀ w ∈ filtration R B (n + 1), δγ w = 0 := fun w hw ↦ by
    simp only [δγ, U, V, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.comp_apply,
      hπ_zero w hw, map_zero, add_zero, neg_zero]
  have hδη_zero : ∀ w ∈ filtration R B (n + 1), δη w = 0 := fun w hw ↦ by
    simp only [δη, U, V, LinearMap.sub_apply, LinearMap.comp_apply, hπ_zero w hw, map_zero,
      sub_self]
  have hcan : ∀ z, (AA.differential (δγ z) - δγ (BB.unaryBarDifferential z) = -U z) ∧
      (f.linearPart (δγ z) - (BB.differential (δη z) + δη (BB.unaryBarDifferential z)) =
        -V z) := fun z ↦ by
    have hπb : π (BB.unaryBarDifferential z) = BB.unaryBarDifferential (π z) :=
      LinearMap.congr_fun (lengthProj_comp_unaryBarDifferential ⟨n + 2, Nat.succ_pos _⟩) z
    have hcyc := taylorDefect_cycle_eqs_of_mem_filtration f S.hγ S.hη hm he
      (lengthProj_mem_filtration R B ⟨n + 2, Nat.succ_pos _⟩ z)
    exact perturbation_cancel_apply hg₁_d hsA_eq hsB_eq hω_eq
      (by simpa only [U, LinearMap.comp_apply, hπb] using hcyc.1)
      (by simpa only [V, U, LinearMap.comp_apply, hπb] using hcyc.2)
  have hS'γ : S'.γ = S.γ + δγ := rfl; have hS'η : S'.η = S.η + δη := rfl
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hm_π : U z = mDef z := apply_lengthProj_of_mem_filtration R B hm hz
    have hcan₁ := (hcan z).1; rw [hS'γ]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      (bar_add_of_mem_filtration f S.γ S.η hδγ_zero hδη_zero hz).1, map_add,
      AA.taylor_ofLetter, ← AA.differential_apply, LinearMap.add_apply,
      BB.barDifferential_eq_unary_add_higher,
      hδγ_zero _ (BB.higherBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩), add_zero]
    simp only [mDef, G, LinearMap.sub_apply, LinearMap.comp_apply,
      BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add] at hm_π
    linear_combination (norm := abel) hcan₁ - hm_π
  · have he_π : V z = eDef z := apply_lengthProj_of_mem_filtration R B he hz
    have hcan₂ := (hcan z).2
    obtain ⟨hG_add, hH_add⟩ := bar_add_of_mem_filtration f S.γ S.η hδγ_zero hδη_zero hz
    rw [hS'γ, hS'η]
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      hG_add, hH_add, map_add, ← f.linearPart_apply,
      BB.taylor_ofLetter, ← BB.differential_apply, BB.barDifferential_eq_unary_add_higher,
      hδη_zero _ (BB.higherBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩), add_zero]
    simp only [eDef, G, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, BB.barDifferential_eq_unary_add_higher, map_add] at he_π
    linear_combination (norm := abel) hcan₂ - he_π

/-- Recursive sequence of `LiftStage f` stages across all word lengths. -/
private noncomputable def liftStageSeq (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B} {ω : A →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hω_hom : LinearMap.IsHomogeneous ω AA.grading.piece BB.grading.piece (-2)) :
    ℕ → LiftStage f
  | 0 => liftStageBase f hg₁_hom hsB_hom
  | n + 1 =>
      liftStageStep f hg₁_hom hsA_hom hsB_hom hω_hom n
        (liftStageSeq f hg₁_hom hsA_hom hsB_hom hω_hom n)

private theorem liftStageSeq_spec (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B} {ω : A →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hω_hom : LinearMap.IsHomogeneous ω AA.grading.piece BB.grading.piece (-2))
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart)
    (hsB_eq : BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁)
    (hω_eq : BB.differential ∘ₗ ω - ω ∘ₗ AA.differential = f.linearPart ∘ₗ sA - sB ∘ₗ f.linearPart)
    (n : ℕ) :
    let S := liftStageSeq f hg₁_hom hsA_hom hsB_hom hω_hom
    (∀ z ∈ filtration R B (n + 1),
      (AA.taylor ∘ₗ coalgHom R (S n).γ - (S n).γ ∘ₗ BB.barDifferential) z = 0) ∧
    (∀ z ∈ filtration R B (n + 1),
      (f.taylor ∘ₗ coalgHom R (S n).γ - letter R B -
        (BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R (S n).γ) LinearMap.id (S n).η +
          (S n).η ∘ₗ BB.barDifferential)) z = 0) ∧
    (∀ w ∈ filtration R B (n + 1), (S (n + 1)).γ w = (S n).γ w) ∧
    (∀ w ∈ filtration R B (n + 1), (S (n + 1)).η w = (S n).η w) := by
  intro S
  induction n with
  | zero =>
      obtain ⟨hm₀, he₀⟩ := liftStageBase_defects f hg₁_hom hsB_hom hg₁_d hsB_eq
      obtain ⟨hγ_eq, hη_eq⟩ := liftStageStep_agrees f hg₁_hom hsA_hom hsB_hom hω_hom 0 (S 0)
      exact ⟨hm₀, he₀, hγ_eq, hη_eq⟩
  | succ k ih =>
      obtain ⟨hm_prev, he_prev, _, _⟩ := ih
      obtain ⟨hm_k, he_k⟩ := liftStageStep_defects f hg₁_hom hsA_hom hsB_hom hω_hom
        hg₁_d hsA_eq hsB_eq hω_eq k (S k) hm_prev he_prev
      obtain ⟨hγ_eq, hη_eq⟩ := liftStageStep_agrees f hg₁_hom hsA_hom hsB_hom hω_hom
        (k + 1) (S (k + 1))
      exact ⟨hm_k, he_k, hγ_eq, hη_eq⟩

private theorem filtrationLimit_apply_of_succ_eq {M : Type*} [AddCommGroup M] [Module R M]
    {φ : ℕ → (ReducedTensorWords R B →ₗ[R] M)}
    (hφ : ∀ n, ∀ w ∈ filtration R B (n + 1), φ (n + 1) w = φ n w) (n : ℕ)
    {w : ReducedTensorWords R B} (hw : w ∈ filtration R B (n + 1)) :
    filtrationLimit φ w = φ n w := by
  have hstab : ∀ k, ∀ z ∈ filtration R B k, φ (k + 1) z = φ k z := fun k z hz ↦
    hφ k z (filtration_monotone R B k.le_succ hz)
  rw [filtrationLimit_apply_of_mem_filtration hstab hw, hφ n w hw]

/-- Filtration limit of `(liftStageSeq ... n).γ` assembled into an `A∞` morphism `g : BB ⟶ AA`. -/
private theorem exists_hom_of_liftStageSeq (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B} {ω : A →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hω_hom : LinearMap.IsHomogeneous ω AA.grading.piece BB.grading.piece (-2))
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart)
    (hsB_eq : BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁)
    (hω_eq :
      BB.differential ∘ₗ ω - ω ∘ₗ AA.differential = f.linearPart ∘ₗ sA - sB ∘ₗ f.linearPart) :
    let S := liftStageSeq f hg₁_hom hsA_hom hsB_hom hω_hom
    ∃ g : AInfinityHom BB AA, g.linearPart = g₁ ∧
      ∀ n, ∀ w ∈ filtration R B (n + 1), g.barMap w = coalgHom R (S n).γ w := by
  intro S
  have hspec := liftStageSeq_spec f hg₁_hom hsA_hom hsB_hom hω_hom hg₁_d hsA_eq hsB_eq hω_eq
  set γLim := filtrationLimit fun n ↦ (S n).γ
  have hγLim_eq : ∀ (n : ℕ) {w : ReducedTensorWords R B},
      w ∈ filtration R B (n + 1) → γLim w = (S n).γ w :=
    filtrationLimit_apply_of_succ_eq fun n ↦ (hspec n).2.2.1
  have hGLim_eq : ∀ n, ∀ w ∈ filtration R B (n + 1),
      coalgHom R γLim w = coalgHom R (S n).γ w := fun n w hw ↦
    (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun u hu ↦ by simp only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
        hγLim_eq n hu]) hw
  have hγLim_hom := isHomogeneous_filtrationLimit
    (fun n z hz ↦ (hspec n).2.2.1 z (filtration_monotone R B n.le_succ hz)) fun n ↦ (S n).hγ
  have hmLim : AA.taylor ∘ₗ coalgHom R γLim = γLim ∘ₗ BB.barDifferential := by
    refine LinearMap.ext fun z ↦ sub_eq_zero.1 ?_
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    have hn1 := filtration_monotone R B n.le_succ hn
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hGLim_eq n z hn1,
      hγLim_eq n (BB.barDifferential_mem_filtration hn1)]
    exact (hspec n).1 z hn1
  refine ⟨AInfinityHom.ofTaylor γLim hγLim_hom hmLim, LinearMap.ext fun b ↦ ?_, fun n w hw ↦ ?_⟩
  · rw [linearPart_apply, taylor_ofTaylor, hγLim_eq 0 (ofLetter_mem_filtration R B b)]
    simp only [S, liftStageSeq, liftStageBase, LinearMap.comp_apply, letter_ofLetter]
  · rw [barMap_ofTaylor, hGLim_eq n w hw]

/-- Assembling the filtration limit produces a right `A∞` homotopy inverse `g : BB ⟶ AA` with
`g.linearPart = g₁` and `(f.comp g).Homotopic (AInfinityHom.id BB)`. -/
private theorem exists_right_homotopy_inverse_of_linearPart (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB₀ : B →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB₀_hom : LinearMap.IsHomogeneous sB₀ BB.grading.piece BB.grading.piece (-1))
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart)
    (hsB₀_eq :
      BB.differential ∘ₗ sB₀ + sB₀ ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁) :
    ∃ g : AInfinityHom BB AA,
      g.linearPart = g₁ ∧ (f.comp g).Homotopic (AInfinityHom.id BB) := by
  obtain ⟨sB, ω, hsB_hom, hω_hom, hsB_eq, hω_eq⟩ := exists_coherent_chain_homotopy
    f.isHomogeneous_linearPart hg₁_hom hsA_hom hsB₀_hom f.differential_comp_linearPart hg₁_d
    hsA_eq hsB₀_eq
  have hspec := liftStageSeq_spec f hg₁_hom hsA_hom hsB_hom hω_hom hg₁_d hsA_eq hsB_eq hω_eq
  obtain ⟨g, hg_lin, hg_bar⟩ := exists_hom_of_liftStageSeq f hg₁_hom hsA_hom hsB_hom hω_hom
    hg₁_d hsA_eq hsB_eq hω_eq
  set S := liftStageSeq f hg₁_hom hsA_hom hsB_hom hω_hom
  set ηLim := filtrationLimit fun n ↦ (S n).η
  have hηLim_eq : ∀ (n : ℕ) {w : ReducedTensorWords R B},
      w ∈ filtration R B (n + 1) → ηLim w = (S n).η w :=
    filtrationLimit_apply_of_succ_eq fun n ↦ (hspec n).2.2.2
  have hηLim_hom := isHomogeneous_filtrationLimit
    (fun n z hz ↦ (hspec n).2.2.2 z (filtration_monotone R B n.le_succ hz)) fun n ↦ (S n).hη
  set HLim := gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp g).barMap LinearMap.id ηLim
  have hHLim_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1
      (f.comp g).barMap (AInfinityHom.id BB).barMap HLim := by
    rw [AInfinityHom.barMap_id]
    exact isGradedCoderivationAlong_gradedCoderivAlong _ 1
      (f.comp g).isCoalgHom_barMap (isCoalgHom_id B) ηLim
  refine ⟨g, hg_lin, (Homotopy.ofCoderivation HLim hHLim_cod
    (isHomogeneous_gradedCoderivAlong (q := 1) (f.comp g).isHomogeneous_barMap
      (LinearMap.isHomogeneous_id _) hηLim_hom)
    (LinearMap.ext fun z ↦ sub_eq_zero.1 ?_)).homotopic⟩
  obtain ⟨n, hn⟩ := exists_mem_filtration R B z
  have hn1 := filtration_monotone R B n.le_succ hn
  have hH_eq : HLim z = gradedCoderivAlong (BB.grading.shift 1) 1
      (f.barMap ∘ₗ coalgHom R (S n).γ) LinearMap.id (S n).η z :=
    gradedCoderivAlong_congr_of_mem_filtration (f.comp g).isCoalgHom_barMap
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (S n).γ))
      (fun w hw ↦ by simp only [barMap_comp, LinearMap.comp_apply, hg_bar n w hw])
      (fun w hw ↦ hηLim_eq n hw) z hn1
  have hH_let : letter R B ∘ₗ HLim = ηLim := letter_comp_gradedCoderivAlong _ _ _ _ _
  have he_n : (f.taylor ∘ₗ coalgHom R (S n).γ - letter R B -
      (BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
        (f.barMap ∘ₗ coalgHom R (S n).γ) LinearMap.id (S n).η +
        (S n).η ∘ₗ BB.barDifferential)) z = 0 := (hspec n).2.1 z hn1
  rw [hH_let]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, taylor_comp,
    taylor_id, hg_bar n z hn1, hH_eq, hηLim_eq n (BB.barDifferential_mem_filtration hn1)] at he_n ⊢
  linear_combination (norm := abel) he_n

end Lifting

/-- **Lifting a graded chain-homotopy inverse to an `A∞` homotopy inverse.**  Over any commutative
ring `R`, if the linear part `f.linearPart` of `f : AA ⟶ BB` admits a degree-zero chain-homotopy
inverse `g₁ : B →ₗ[R] A` witnessed by degree-`(-1)` homotopies `sA` and `sB`, then `g₁` extends to
a genuine `A∞` morphism `g : BB ⟶ AA` with `g.linearPart = g₁` which is a two-sided `A∞` homotopy
inverse to `f`. -/
theorem exists_homotopy_inverse_of_linearPart (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart)
    (hsB_eq : BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁) :
    ∃ g : AInfinityHom BB AA,
      g.linearPart = g₁ ∧
        (g.comp f).Homotopic (AInfinityHom.id AA) ∧
        (f.comp g).Homotopic (AInfinityHom.id BB) := by
  obtain ⟨g, hg_lin, hfg⟩ := exists_right_homotopy_inverse_of_linearPart f
    hg₁_hom hsA_hom hsB_hom hg₁_d hsA_eq hsB_eq
  obtain ⟨f', _, hgf'⟩ := exists_right_homotopy_inverse_of_linearPart g
    f.isHomogeneous_linearPart hsB_hom hsA_hom f.differential_comp_linearPart
    (by rwa [hg_lin]) (by rwa [hg_lin])
  exact ⟨g, hg_lin, homotopic_comp_id_of_right_homotopy_inverses hfg hgf', hfg⟩

/-- An `A∞` morphism whose linear part admits a graded chain-homotopy inverse is an `A∞` homotopy
equivalence. -/
theorem isHomotopyEquiv_of_linearPart (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_hom : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_hom : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_hom : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁_d : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA_eq : AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart)
    (hsB_eq : BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁) :
    f.IsHomotopyEquiv := by
  obtain ⟨g, _, hgf, hfg⟩ := exists_homotopy_inverse_of_linearPart f
    hg₁_hom hsA_hom hsB_hom hg₁_d hsA_eq hsB_eq
  exact isHomotopyEquiv_def _ |>.2 ⟨g, hgf, hfg⟩

/-- An `A∞` homotopy equivalence induces a graded chain-homotopy equivalence on linear parts. -/
theorem IsHomotopyEquiv.exists_linearPart_homotopy_inverse {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) :
    ∃ (g₁ : B →ₗ[R] A) (sA : A →ₗ[R] A) (sB : B →ₗ[R] B),
      LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0 ∧
      LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1) ∧
      LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1) ∧
      AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential ∧
      AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart ∧
      BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁ := by
  obtain ⟨g, hA', hB'⟩ := (isHomotopyEquiv_def f).1 hf
  obtain ⟨hA⟩ := (homotopic_def _ _).1 hA'
  obtain ⟨hB⟩ := (homotopic_def _ _).1 hB'
  have hsA_hom : LinearMap.IsHomogeneous (-hA.linearHomotopy)
      AA.grading.piece AA.grading.piece (-1) :=
    (LinearMap.isHomogeneous_def.2 fun p a ha ↦ by
      simpa only [sub_eq_add_neg] using hA.linearHomotopy_mem ha).neg
  have hsB_hom : LinearMap.IsHomogeneous (-hB.linearHomotopy)
      BB.grading.piece BB.grading.piece (-1) :=
    (LinearMap.isHomogeneous_def.2 fun p b hb ↦ by
      simpa only [sub_eq_add_neg] using hB.linearHomotopy_mem hb).neg
  refine ⟨g.linearPart, -hA.linearHomotopy, -hB.linearHomotopy,
    g.isHomogeneous_linearPart, hsA_hom, hsB_hom, g.differential_comp_linearPart, ?_, ?_⟩
  · refine LinearMap.ext fun a ↦ ?_
    have h := hA.linearPart_sub_linearPart a
    simp only [linearPart_comp, linearPart_id, LinearMap.comp_apply, LinearMap.id_apply,
      ← AA.differential_apply] at h
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_neg]
    linear_combination (norm := abel) h
  · refine LinearMap.ext fun b ↦ ?_
    have h := hB.linearPart_sub_linearPart b
    simp only [linearPart_comp, linearPart_id, LinearMap.comp_apply, LinearMap.id_apply,
      ← BB.differential_apply] at h
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_neg]
    linear_combination (norm := abel) h

/-- **Characterization of `A∞` homotopy equivalences over a commutative ring**: an `A∞` morphism
`f : AA ⟶ BB` is a homotopy equivalence if and only if its linear part `f.linearPart` admits a
graded chain-homotopy inverse. -/
theorem isHomotopyEquiv_iff_linearPart (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ (g₁ : B →ₗ[R] A) (sA : A →ₗ[R] A) (sB : B →ₗ[R] B),
        LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0 ∧
        LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1) ∧
        LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1) ∧
        AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential ∧
        AA.differential ∘ₗ sA + sA ∘ₗ AA.differential = LinearMap.id - g₁ ∘ₗ f.linearPart ∧
        BB.differential ∘ₗ sB + sB ∘ₗ BB.differential = LinearMap.id - f.linearPart ∘ₗ g₁ :=
  ⟨IsHomotopyEquiv.exists_linearPart_homotopy_inverse,
    fun ⟨_, _, _, hg₁, hsA, hsB, hd, hA, hB⟩ ↦ isHomotopyEquiv_of_linearPart f hg₁ hsA hsB hd hA hB⟩

end AInfinityHom

/-! ### Homological transfer produces homotopy equivalences -/

namespace AInfinityAlgebra

variable {H : Type uH} [AddCommGroup H] [Module R H]
  (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H ℤ} {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

/-- The transferred inclusion from homological transfer is an `A∞` homotopy equivalence. -/
theorem isHomotopyEquiv_transferInclusion :
    (𝒜.transferInclusion c hh hincl hproj).IsHomotopyEquiv :=
  (AInfinityHom.isHomotopyEquiv_def _).2
    ⟨𝒜.transferProjection c hh hincl hproj,
      AInfinityHom.Homotopic.of_eq (𝒜.transferProjection_comp_transferInclusion c hh hincl hproj),
      (𝒜.transferHomotopy c hh hincl hproj).homotopic.symm⟩

/-- The transferred projection from homological transfer is an `A∞` homotopy equivalence. -/
theorem isHomotopyEquiv_transferProjection :
    (𝒜.transferProjection c hh hincl hproj).IsHomotopyEquiv :=
  (AInfinityHom.isHomotopyEquiv_def _).2
    ⟨𝒜.transferInclusion c hh hincl hproj,
      (𝒜.transferHomotopy c hh hincl hproj).homotopic.symm,
      AInfinityHom.Homotopic.of_eq (𝒜.transferProjection_comp_transferInclusion c hh hincl hproj)⟩

end AInfinityAlgebra

end CommRing

/-! ### Quasi-isomorphisms over a field are homotopy equivalences -/

section Field

variable {K : Type uK} {A : Type uA} {B : Type uB}
  [Field K]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

namespace AInfinityHom

variable {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

/-- **Whitehead theorem for `A∞` algebras over a field**: every quasi-isomorphism of `A∞` algebras
over a field `K` is an `A∞` homotopy equivalence. -/
theorem IsQuasiIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.IsHomotopyEquiv := by
  let IA := AA.transferInclusion AA.cohomologyContraction
    AA.isHomogeneous_cohomologyContraction_homotopy
    AA.isHomogeneous_cohomologyContraction_incl
    AA.isHomogeneous_cohomologyContraction_proj
  let PA := AA.transferProjection AA.cohomologyContraction
    AA.isHomogeneous_cohomologyContraction_homotopy
    AA.isHomogeneous_cohomologyContraction_incl
    AA.isHomogeneous_cohomologyContraction_proj
  let IB := BB.transferInclusion BB.cohomologyContraction
    BB.isHomogeneous_cohomologyContraction_homotopy
    BB.isHomogeneous_cohomologyContraction_incl
    BB.isHomogeneous_cohomologyContraction_proj
  let PB := BB.transferProjection BB.cohomologyContraction
    BB.isHomogeneous_cohomologyContraction_homotopy
    BB.isHomogeneous_cohomologyContraction_incl
    BB.isHomogeneous_cohomologyContraction_proj
  let φ := PB.comp (f.comp IA)
  have hIA_qiso : IA.IsQuasiIso := AA.isQuasiIso_transferInclusion _ _ _ _
  have hPB_qiso : PB.IsQuasiIso := BB.isQuasiIso_transferProjection _ _ _ _
  have hφ_heq : φ.IsHomotopyEquiv :=
    ((hPB_qiso.comp (hf.comp hIA_qiso)).isIso
      (AA.isMinimal_transfer _ _ _ _ rfl) (BB.isMinimal_transfer _ _ _ _ rfl)).isHomotopyEquiv
  have hcomp_heq : (IB.comp (φ.comp PA)).IsHomotopyEquiv :=
    (BB.isHomotopyEquiv_transferInclusion _ _ _ _).comp
      (hφ_heq.comp (AA.isHomotopyEquiv_transferProjection _ _ _ _))
  have hA : Homotopic (AInfinityHom.id AA) (IA.comp PA) :=
    (AA.transferHomotopy _ _ _ _).homotopic
  have hB : Homotopic (AInfinityHom.id BB) (IB.comp PB) :=
    (BB.transferHomotopy _ _ _ _).homotopic
  have hhom : f.Homotopic (IB.comp (φ.comp PA)) := by
    have hassoc : IB.comp (φ.comp PA) = (IB.comp PB).comp (f.comp (IA.comp PA)) := by
      simp only [φ, comp_assoc]
    rw [hassoc]
    exact (Homotopic.of_eq (by rw [id_comp, comp_id])).symm.trans
      (hB.comp ((Homotopic.refl f).comp hA))
  exact hhom.isHomotopyEquiv_iff.2 hcomp_heq

/-- Over a field, every quasi-isomorphism `f : AA ⟶ BB` of `A∞` algebras admits a two-sided `A∞`
inverse up to homotopy. -/
theorem IsQuasiIso.exists_homotopy_inverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    ∃ g : AInfinityHom BB AA,
      (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB) :=
  (isHomotopyEquiv_def f).1 hf.isHomotopyEquiv

/-- Over a field, an `A∞` morphism is a homotopy equivalence if and only if it is a
quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end AInfinityHom

namespace AInfinityAlgebra

/-- Over a field, the inclusion from the minimal model on cohomology is an `A∞` homotopy
equivalence. -/
theorem isHomotopyEquiv_minimalModelInclusion (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelInclusion.IsHomotopyEquiv :=
  𝒜.isQuasiIso_minimalModelInclusion.isHomotopyEquiv

/-- Over a field, the projection onto the minimal model on cohomology is an `A∞` homotopy
equivalence. -/
theorem isHomotopyEquiv_minimalModelProjection (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelProjection.IsHomotopyEquiv :=
  𝒜.isQuasiIso_minimalModelProjection.isHomotopyEquiv

end AInfinityAlgebra

end Field

end TauCeti
