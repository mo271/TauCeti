/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Transformation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology

/-!
# Homotopy inverses of morphisms of A-infinity algebras

A morphism `f : AA ⟶ BB` of `A∞` algebras is a *homotopy equivalence* (`IsHomotopyEquiv`) when
there is a morphism `g : BB ⟶ AA` together with homotopies `id ⇒ g ∘ f` and `id ⇒ f ∘ g`.

Projecting onto single letters shows that `f.linearPart` is then a graded chain-homotopy
equivalence between `(A, m₁)` and `(B, m₁)`.  Over an arbitrary commutative ring, a bare
quasi-isomorphism need not have a chain-homotopy inverse even for `A∞` algebras with only `m₁`, so
this condition on `f.linearPart` cannot be weakened without splitting hypotheses.  Conversely, when
`f.linearPart` has a graded chain-homotopy inverse `g₁`, an `A∞` homotopy inverse `g` extending
`g₁` is built arity by arity by killing successive obstructions in the Hom complexes from
`Tᶜ(sB)` to `sA` and `sB`:

1. At arity `n + 1`, an approximate coalgebra morphism `Gₙ` and coderivation homotopy `Hₙ` leave a
   morphism defect `Dₙ = b_A ∘ Gₙ - Gₙ ∘ b_B` and a homotopy defect
   `Eₙ = (id - F ∘ Gₙ) - (b_B ∘ Hₙ + Hₙ ∘ b_B)` vanishing up to length `n`.  Because `b² = 0`
   and the higher part of `b_B` lowers word length, their length-`(n + 1)` letter components form a
   cocycle `O` and a cochain `Ω` bounding `f₁ ∘ O` for the unary bar differential of `BB`.  The
   chain-homotopy equivalence `f₁ ⇄ g₁` simultaneously trivialises `O` and `Ω`, advancing `(Gₙ, Hₙ)`
   to length `n + 1`; passing the stabilising Taylor maps to the limit yields a right homotopy
   inverse `g` and `Homotopy (id BB) (f.comp g)`.
2. The same obstruction step applied in `reducedTransformationComplex` shows that postcomposition
   with `f` reflects coboundaries of closed degree-zero transformations, hence reflects `Homotopy`.
   Precomposing `Homotopy (id BB) (f.comp g)` with `f` gives a homotopy from `f ∘ id` to
   `f ∘ (g ∘ f)`, which therefore lifts to `Homotopy (id AA) (g.comp f)`.

Over a field, `cohomologyContraction` contracts the unary complexes of `AA` and `BB` onto their
cohomologies, turning the cohomology equivalence of any quasi-isomorphism `f` into a graded
chain-homotopy inverse of `f.linearPart`.  Every `A∞` quasi-isomorphism over a field is therefore
an `A∞` homotopy equivalence.

## Main definitions

* `TauCeti.AInfinityHom.IsHomotopyEquiv`: an `A∞` morphism with a two-sided homotopy inverse.

## Main results

* `TauCeti.AInfinityHom.exists_rightHomotopyInverse_of_chainHomotopyEquiv` and
  `TauCeti.AInfinityHom.exists_homotopyInverse_of_chainHomotopyEquiv`: lifting a graded
  chain-homotopy inverse of `f.linearPart` to a right, hence two-sided, `A∞` homotopy inverse.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.exists_reducedTransformation_eq_of_compRight` and
  `TauCeti.AInfinityHom.IsHomotopyEquiv.nonempty_homotopy_comp_iff`: postcomposition with a
  homotopy equivalence reflects `Homotopy`.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff`: over any commutative ring, `f` is an `A∞` homotopy
  equivalence if and only if `f.linearPart` is a graded chain-homotopy equivalence.
* `TauCeti.AInfinityHom.Homotopy.isHomotopyEquiv_iff`, `TauCeti.AInfinityHom.IsHomotopyEquiv.comp`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv.of_precomp`, and
  `TauCeti.AInfinityHom.IsHomotopyEquiv.of_postcomp`: homotopy invariance, composition, and
  two-out-of-three for `A∞` homotopy equivalences.
* `TauCeti.AInfinityHom.IsQuasiIso.isHomotopyEquiv` and
  `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: over a field, the `A∞` homotopy
  equivalences are precisely the quasi-isomorphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.7.
* K. Lefèvre-Hasegawa, *Sur les A∞-catégories*, Section 1.3.
* V. Lyubashenko, *Category of A∞-categories*, Homology Homotopy Appl. 5 (2003), Sections 1--2.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

open ReducedTensorWords

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-! ### Homotopy equivalences of `A∞` algebras -/

/-- An `A∞` morphism `f : AA ⟶ BB` is a **homotopy equivalence** when there is an `A∞` morphism
`g : BB ⟶ AA` together with homotopies from `id` to `g ∘ f` and from `id` to `f ∘ g`. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (AInfinityHom.id AA) (g.comp f)) ∧
      Nonempty (Homotopy (AInfinityHom.id BB) (f.comp g))

/-- An `A∞` morphism is a homotopy equivalence exactly when it admits a two-sided homotopy
inverse. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        Nonempty (Homotopy (AInfinityHom.id AA) (g.comp f)) ∧
          Nonempty (Homotopy (AInfinityHom.id BB) (f.comp g)) :=
  Iff.rfl

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA, ⟨by rw [comp_id]; exact Homotopy.refl _⟩,
    ⟨by rw [comp_id]; exact Homotopy.refl _⟩⟩

/-- Every `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv := by
  obtain ⟨g, hg₁, hg₂⟩ := (isIso_def f).1 hf
  exact ⟨g, ⟨hg₁ ▸ Homotopy.refl _⟩, ⟨hg₂ ▸ Homotopy.refl _⟩⟩

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism: homotopic morphisms induce equal maps
on cohomology, so a homotopy inverse induces a two-sided inverse on cohomology. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨g.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · have h := DFunLike.congr_fun hL.cohomologyMap_eq x
    rwa [cohomologyMap_id, NonUnitalAlgHom.coe_id, id_eq, cohomologyMap_comp,
      NonUnitalAlgHom.comp_apply, eq_comm] at h
  · have h := DFunLike.congr_fun hR.cohomologyMap_eq y
    rwa [cohomologyMap_id, NonUnitalAlgHom.coe_id, id_eq, cohomologyMap_comp,
      NonUnitalAlgHom.comp_apply, eq_comm] at h

private theorem differential_comp_linearPart (f : AInfinityHom AA BB) :
    BB.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ AA.differential :=
  LinearMap.ext fun a ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AInfinityAlgebra.differential_apply,
      AInfinityAlgebra.differential_apply, f.linearPart_m_one]

/-- Projecting a homotopy inverse and its two homotopies onto single letters yields a graded
chain-homotopy inverse of `f.linearPart` between `(A, m₁)` and `(B, m₁)`. -/
theorem IsHomotopyEquiv.exists_chainHomotopyEquiv {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) :
    ∃ (g₁ : B →ₗ[R] A) (sA : A →ₗ[R] A) (sB : B →ₗ[R] B),
      LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0 ∧
        LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1) ∧
        LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1) ∧
        AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential ∧
        LinearMap.id - g₁ ∘ₗ f.linearPart =
          AA.differential ∘ₗ sA + sA ∘ₗ AA.differential ∧
        LinearMap.id - f.linearPart ∘ₗ g₁ =
          BB.differential ∘ₗ sB + sB ∘ₗ BB.differential := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf
  refine ⟨g.linearPart, hL.linearHomotopy, hR.linearHomotopy, g.isHomogeneous_linearPart,
    LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
      simpa only [sub_eq_add_neg] using hL.linearHomotopy_mem ha,
    LinearMap.isHomogeneous_def.2 fun _ _ hb ↦ by
      simpa only [sub_eq_add_neg] using hR.linearHomotopy_mem hb,
    differential_comp_linearPart g, ?_, ?_⟩
  · refine LinearMap.ext fun a ↦ ?_
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, linearPart_id,
      linearPart_comp, AInfinityAlgebra.differential_apply] using hL.linearPart_sub_linearPart a
  · refine LinearMap.ext fun b ↦ ?_
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, linearPart_id,
      linearPart_comp, AInfinityAlgebra.differential_apply] using hR.linearPart_sub_linearPart b

/-- Between minimal `A∞` algebras, every homotopy equivalence is an `A∞` isomorphism: when both
differentials vanish, the chain homotopies vanish, so `f.linearPart` is bijective. -/
theorem IsHomotopyEquiv.isIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv)
    (hA : AA.IsMinimal) (hB : BB.IsMinimal) : f.IsIso := by
  obtain ⟨g₁, sA, sB, -, -, -, -, hsA, hsB⟩ := hf.exists_chainHomotopyEquiv
  rw [(AA.isMinimal_def).1 hA] at hsA
  rw [(BB.isMinimal_def).1 hB] at hsB
  simp only [LinearMap.zero_comp, LinearMap.comp_zero, add_zero, sub_eq_zero] at hsA hsB
  rw [isIso_iff_linearPart_bijective]
  refine Function.bijective_iff_has_inverse.2 ⟨g₁, fun a ↦ ?_, fun b ↦ ?_⟩
  · exact (LinearMap.congr_fun hsA a).symm
  · exact (LinearMap.congr_fun hsB b).symm

/-- Between minimal `A∞` algebras, the homotopy equivalences are exactly the `A∞` isomorphisms. -/
theorem isHomotopyEquiv_iff_isIso_of_isMinimal (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    {f : AInfinityHom AA BB} : f.IsHomotopyEquiv ↔ f.IsIso :=
  ⟨fun hf ↦ hf.isIso hA hB, IsIso.isHomotopyEquiv⟩

/-! ### The Hom-complex obstruction step and stabilising Taylor maps -/

/-- The algebraic engine of arity-by-arity obstruction killing.  Given a graded chain-homotopy
inverse `(g₁, sA, sB)` of `f.linearPart`, a cocycle `O : Tᶜ(sC) ⟶ sA` of suspended degree `p + 1`
for `CC.unaryBarDifferential` with sign `ε`, and a cochain `Ω : Tᶜ(sC) ⟶ sB` of suspended degree
`p` bounding `f.linearPart ∘ O`, produces cochains `α : Tᶜ(sC) ⟶ sA` of degree `p` and
`β : Tᶜ(sC) ⟶ sB` of degree `p - 1` simultaneously killing `O` and `Ω` and vanishing on every
word annihilated by both `O` and `Ω`. -/
private theorem exists_obstruction_kill (f : AInfinityHom AA BB) {g₁ : B →ₗ[R] A}
    {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_deg : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_deg : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁ : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA : LinearMap.id - g₁ ∘ₗ f.linearPart = AA.differential ∘ₗ sA + sA ∘ₗ AA.differential)
    (hsB : LinearMap.id - f.linearPart ∘ₗ g₁ = BB.differential ∘ₗ sB + sB ∘ₗ BB.differential)
    (CC : AInfinityAlgebra R C) (p : ℤ) (ε : R)
    {O : ReducedTensorWords R C →ₗ[R] A} {Ω : ReducedTensorWords R C →ₗ[R] B}
    (hO_deg : LinearMap.IsHomogeneous O (gradedPiece (CC.grading.shift 1))
      (AA.grading.shift 1).piece (p + 1))
    (hΩ_deg : LinearMap.IsHomogeneous Ω (gradedPiece (CC.grading.shift 1))
      (BB.grading.shift 1).piece p)
    (hO : AA.differential ∘ₗ O + ε • (O ∘ₗ CC.unaryBarDifferential) = 0)
    (hΩ : BB.differential ∘ₗ Ω - ε • (Ω ∘ₗ CC.unaryBarDifferential) = f.linearPart ∘ₗ O) :
    ∃ (α : ReducedTensorWords R C →ₗ[R] A) (β : ReducedTensorWords R C →ₗ[R] B),
      LinearMap.IsHomogeneous α (gradedPiece (CC.grading.shift 1))
        (AA.grading.shift 1).piece p ∧
        LinearMap.IsHomogeneous β (gradedPiece (CC.grading.shift 1))
          (BB.grading.shift 1).piece (p - 1) ∧
        (∀ w, O w = 0 → Ω w = 0 → α w = 0 ∧ β w = 0) ∧
        AA.differential ∘ₗ α - ε • (α ∘ₗ CC.unaryBarDifferential) = O ∧
        f.linearPart ∘ₗ α - (BB.differential ∘ₗ β + ε • (β ∘ₗ CC.unaryBarDifferential)) = Ω := by
  set dA := AA.differential
  set dB := BB.differential
  set dC := CC.unaryBarDifferential
  set f₁ := f.linearPart
  have hf₁ : dB ∘ₗ f₁ = f₁ ∘ₗ dA := differential_comp_linearPart f
  let α₀ : ReducedTensorWords R C →ₗ[R] A := sA ∘ₗ O + g₁ ∘ₗ Ω
  let z : ReducedTensorWords R C →ₗ[R] B := f₁ ∘ₗ α₀ - Ω
  have hα₀ : LinearMap.IsHomogeneous α₀ (gradedPiece (CC.grading.shift 1))
      (AA.grading.shift 1).piece p := by
    refine LinearMap.IsHomogeneous.add ?_ ?_
    · simpa only [add_neg_cancel_right] using
        (LinearMap.isHomogeneous_shift_piece_iff.2 hsA_deg).comp hO_deg
    · simpa only [add_zero] using
        (LinearMap.isHomogeneous_shift_piece_iff.2 hg₁_deg).comp hΩ_deg
  have hz : LinearMap.IsHomogeneous z (gradedPiece (CC.grading.shift 1))
      (BB.grading.shift 1).piece p := by
    refine LinearMap.IsHomogeneous.sub ?_ hΩ_deg
    simpa only [add_zero] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 f.isHomogeneous_linearPart).comp hα₀
  have hα₀_eq : dA ∘ₗ α₀ - ε • (α₀ ∘ₗ dC) = O := by
    have hO' : ε • (O ∘ₗ dC) = -(dA ∘ₗ O) := eq_neg_of_add_eq_zero_right hO
    calc dA ∘ₗ (sA ∘ₗ O + g₁ ∘ₗ Ω) - ε • ((sA ∘ₗ O + g₁ ∘ₗ Ω) ∘ₗ dC)
        = (dA ∘ₗ sA) ∘ₗ O - sA ∘ₗ (ε • (O ∘ₗ dC)) +
            g₁ ∘ₗ (dB ∘ₗ Ω - ε • (Ω ∘ₗ dC)) := by
          simp only [LinearMap.comp_add, LinearMap.add_comp, smul_add, LinearMap.comp_smul,
            LinearMap.comp_sub, ← LinearMap.comp_assoc, hg₁]
          abel
      _ = (dA ∘ₗ sA + sA ∘ₗ dA) ∘ₗ O + (g₁ ∘ₗ f₁) ∘ₗ O := by
          rw [hO', LinearMap.comp_neg, sub_neg_eq_add, hΩ, LinearMap.add_comp]
          simp only [LinearMap.comp_assoc]
      _ = O := by rw [← hsA, LinearMap.sub_comp, LinearMap.id_comp, sub_add_cancel]
  have hz_eq : dB ∘ₗ z - ε • (z ∘ₗ dC) = 0 := by
    calc dB ∘ₗ (f₁ ∘ₗ α₀ - Ω) - ε • ((f₁ ∘ₗ α₀ - Ω) ∘ₗ dC)
        = f₁ ∘ₗ (dA ∘ₗ α₀ - ε • (α₀ ∘ₗ dC)) - (dB ∘ₗ Ω - ε • (Ω ∘ₗ dC)) := by
          simp only [LinearMap.comp_sub, LinearMap.sub_comp, smul_sub, LinearMap.comp_smul,
            ← LinearMap.comp_assoc, hf₁]
          abel
      _ = 0 := by rw [hα₀_eq, hΩ, sub_self]
  refine ⟨α₀ - g₁ ∘ₗ z, sB ∘ₗ z, ?_, ?_, ?_, ?_, ?_⟩
  · refine hα₀.sub ?_
    simpa only [add_zero] using (LinearMap.isHomogeneous_shift_piece_iff.2 hg₁_deg).comp hz
  · simpa only [sub_eq_add_neg] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 hsB_deg).comp hz
  · intro w hwO hwΩ
    have hα₀w : α₀ w = 0 := by simp [α₀, hwO, hwΩ]
    have hzw : z w = 0 := by simp [z, hα₀w, hwΩ]
    exact ⟨by simp [hα₀w, hzw], by simp [hzw]⟩
  · calc dA ∘ₗ (α₀ - g₁ ∘ₗ z) - ε • ((α₀ - g₁ ∘ₗ z) ∘ₗ dC)
        = (dA ∘ₗ α₀ - ε • (α₀ ∘ₗ dC)) - g₁ ∘ₗ (dB ∘ₗ z - ε • (z ∘ₗ dC)) := by
          simp only [LinearMap.comp_sub, LinearMap.sub_comp, smul_sub, LinearMap.comp_smul,
            ← LinearMap.comp_assoc, hg₁]
          abel
      _ = O := by rw [hα₀_eq, hz_eq, LinearMap.comp_zero, sub_zero]
  · have hβ_eq : dB ∘ₗ (sB ∘ₗ z) + ε • ((sB ∘ₗ z) ∘ₗ dC) = z - (f₁ ∘ₗ g₁) ∘ₗ z := by
      calc dB ∘ₗ (sB ∘ₗ z) + ε • ((sB ∘ₗ z) ∘ₗ dC)
          = (dB ∘ₗ sB) ∘ₗ z + sB ∘ₗ (ε • (z ∘ₗ dC)) := by
            simp only [LinearMap.comp_smul, LinearMap.comp_assoc]
        _ = (dB ∘ₗ sB + sB ∘ₗ dB) ∘ₗ z := by
            rw [← sub_eq_zero.1 hz_eq]
            simp only [LinearMap.add_comp, LinearMap.comp_assoc]
        _ = z - (f₁ ∘ₗ g₁) ∘ₗ z := by rw [← hsB, LinearMap.sub_comp, LinearMap.id_comp]
    rw [hβ_eq, LinearMap.comp_sub, ← LinearMap.comp_assoc]
    simp only [z]
    abel

/-! ### Constructing a right homotopy inverse -/

private theorem isGradedCoderivationAlong_barDifferential_sub
    {G : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A} (hG : IsCoalgHom R G)
    (hG₀ : LinearMap.IsHomogeneous G (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0) :
    IsGradedCoderivationAlong (BB.grading.shift 1) 1 G G
      (AA.barDifferential ∘ₗ G - G ∘ₗ BB.barDifferential) := by
  have h : AA.barDifferential ∘ₗ G - G ∘ₗ BB.barDifferential =
      AA.barDifferential ∘ₗ G + (-1 : R) • (G ∘ₗ BB.barDifferential) :=
    LinearMap.ext fun z ↦ by
      rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, neg_one_smul,
        sub_eq_add_neg]
  rw [h]
  exact (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hG hG₀).add
    ((hG.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential).smul (-1))

/-- One arity step in the construction of a right homotopy inverse of `f`: extends Taylor maps
`(gₙ, hₙ)` satisfying the morphism and homotopy equations up to tensor length `n` to `(gₙ₊₁, hₙ₊₁)`
satisfying them up to tensor length `n + 1` and agreeing with `(gₙ, hₙ)` up to length `n`. -/
private theorem rightInverse_step (f : AInfinityHom AA BB) {g₁ : B →ₗ[R] A}
    {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_deg : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_deg : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁ : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA : LinearMap.id - g₁ ∘ₗ f.linearPart = AA.differential ∘ₗ sA + sA ∘ₗ AA.differential)
    (hsB : LinearMap.id - f.linearPart ∘ₗ g₁ = BB.differential ∘ₗ sB + sB ∘ₗ BB.differential)
    (n : ℕ) {gn : ReducedTensorWords R B →ₗ[R] A} {hn : ReducedTensorWords R B →ₗ[R] B}
    (hgn_deg : LinearMap.IsHomogeneous gn (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0)
    (hhn_deg : LinearMap.IsHomogeneous hn (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    (hDn : ∀ z ∈ filtration R B n,
      (AA.barDifferential ∘ₗ coalgHom R gn - coalgHom R gn ∘ₗ BB.barDifferential) z = 0)
    (hEn : ∀ z ∈ filtration R B n,
      (((LinearMap.id : Module.End R (ReducedTensorWords R B)) - f.barMap ∘ₗ coalgHom R gn) -
        (BB.barDifferential ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
            (f.barMap ∘ₗ coalgHom R gn) hn +
          gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
            (f.barMap ∘ₗ coalgHom R gn) hn ∘ₗ BB.barDifferential)) z = 0) :
    ∃ (gn' : ReducedTensorWords R B →ₗ[R] A) (hn' : ReducedTensorWords R B →ₗ[R] B),
      LinearMap.IsHomogeneous gn' (gradedPiece (BB.grading.shift 1))
        (AA.grading.shift 1).piece 0 ∧
        LinearMap.IsHomogeneous hn' (gradedPiece (BB.grading.shift 1))
          (BB.grading.shift 1).piece (-1) ∧
        (∀ z ∈ filtration R B n, gn' z = gn z ∧ hn' z = hn z) ∧
        (∀ z ∈ filtration R B (n + 1),
          (AA.barDifferential ∘ₗ coalgHom R gn' - coalgHom R gn' ∘ₗ BB.barDifferential) z = 0) ∧
        (∀ z ∈ filtration R B (n + 1),
          (((LinearMap.id : Module.End R (ReducedTensorWords R B)) - f.barMap ∘ₗ coalgHom R gn') -
            (BB.barDifferential ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
                (f.barMap ∘ₗ coalgHom R gn') hn' +
              gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
                (f.barMap ∘ₗ coalgHom R gn') hn' ∘ₗ BB.barDifferential)) z = 0) := by
  -- Stage 1: on `filtration R B (n + 1)` both defects `Dn` and `En` land in single letters; their
  -- length-`(n + 1)` letter projections form a cocycle `O` and a cochain `Ω` bounding `f₁ ∘ O`.
  set Gn := coalgHom R gn
  set Hn := gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ Gn) hn
  set Dn := AA.barDifferential ∘ₗ Gn - Gn ∘ₗ BB.barDifferential
  set En := ((LinearMap.id : Module.End R (ReducedTensorWords R B)) - f.barMap ∘ₗ Gn) -
    (BB.barDifferential ∘ₗ Hn + Hn ∘ₗ BB.barDifferential)
  set P := lengthProj R B ⟨n + 1, n.succ_pos⟩
  have hGn_coalg : IsCoalgHom R Gn := isCoalgHom_coalgHom gn
  have hGn_deg : LinearMap.IsHomogeneous Gn (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0 := isHomogeneous_coalgHom hgn_deg
  have hFGn_coalg : IsCoalgHom R (f.barMap ∘ₗ Gn) := f.isCoalgHom_barMap.comp hGn_coalg
  have hFGn_deg : LinearMap.IsHomogeneous (f.barMap ∘ₗ Gn) (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp hGn_deg
  have hHn_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ Gn)
      Hn := isGradedCoderivationAlong_gradedCoderivAlong (isCoalgHom_id B) hFGn_coalg hn
  have hHn_deg : LinearMap.IsHomogeneous Hn (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) :=
    isHomogeneous_gradedCoderivAlong (LinearMap.isHomogeneous_id _) hFGn_deg hhn_deg
  have hDn_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 Gn Gn Dn :=
    isGradedCoderivationAlong_barDifferential_sub hGn_coalg hGn_deg
  have hDn_ofLetter : ∀ v ∈ filtration R B (n + 1), Dn v = ofLetter R A (letter R A (Dn v)) :=
    fun _ hv ↦ hDn_cod.apply_eq_ofLetter_of_mem_filtration_succ hDn hv
  have hFGn_intertwine : ∀ z ∈ filtration R B n,
      BB.barDifferential ((f.barMap ∘ₗ Gn) z) = (f.barMap ∘ₗ Gn) (BB.barDifferential z) := by
    intro z hz
    have h0 := sub_eq_zero.1 (hDn z hz)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h0 ⊢
    rw [f.barDifferential_barMap, h0]
  have hEn_ofLetter : ∀ v ∈ filtration R B (n + 1), En v = ofLetter R B (letter R B (En v)) :=
    fun _ hv ↦ hHn_cod.sub_comp_add_comp_apply_eq_ofLetter_of_mem_filtration_succ hHn_deg
      (by decide) BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential
      (by decide) BB.isGradedCoderivation_barDifferential (isCoalgHom_id B) hFGn_coalg
      (LinearMap.isHomogeneous_id _) (fun _ _ ↦ rfl) hFGn_intertwine hEn hv
  let O : ReducedTensorWords R B →ₗ[R] A := -(letter R A ∘ₗ Dn ∘ₗ P)
  let Ω : ReducedTensorWords R B →ₗ[R] B := letter R B ∘ₗ En ∘ₗ P
  have hDn_deg : LinearMap.IsHomogeneous Dn (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 1 := by
    refine LinearMap.IsHomogeneous.sub ?_ ?_
    · simpa only [zero_add] using AA.isHomogeneous_barDifferential.comp hGn_deg
    · simpa only [add_zero] using hGn_deg.comp BB.isHomogeneous_barDifferential
  have hEn_deg : LinearMap.IsHomogeneous En (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    refine ((LinearMap.isHomogeneous_id _).sub hFGn_deg).sub (LinearMap.IsHomogeneous.add ?_ ?_)
    · simpa only [neg_add_cancel] using BB.isHomogeneous_barDifferential.comp hHn_deg
    · simpa only [add_neg_cancel] using hHn_deg.comp BB.isHomogeneous_barDifferential
  have hO_deg : LinearMap.IsHomogeneous O (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece (0 + 1) := by
    refine LinearMap.IsHomogeneous.neg ?_
    simpa only [zero_add, add_zero] using
      (isHomogeneous_letter (AA.grading.shift 1)).comp
        (hDn_deg.comp (isHomogeneous_lengthProj (BB.grading.shift 1) _))
  have hΩ_deg : LinearMap.IsHomogeneous Ω (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
    simpa only [zero_add, add_zero] using
      (isHomogeneous_letter (BB.grading.shift 1)).comp
        (hEn_deg.comp (isHomogeneous_lengthProj (BB.grading.shift 1) _))
  have hO_cocycle : AA.differential ∘ₗ O + (1 : R) • (O ∘ₗ BB.unaryBarDifferential) = 0 := by
    rw [one_smul]
    refine LinearMap.ext fun w ↦ ?_
    set u := P w
    have hu : u ∈ filtration R B (n + 1) := lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ w
    have hsq : AA.barDifferential (Dn u) + Dn (BB.barDifferential u) = 0 := by
      simp only [Dn, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
      rw [← LinearMap.comp_apply AA.barDifferential AA.barDifferential, AA.barDifferential_sq,
        ← LinearMap.comp_apply BB.barDifferential BB.barDifferential, BB.barDifferential_sq]
      simp only [LinearMap.zero_apply, map_zero]
      abel
    have h1 : letter R A (AA.barDifferential (Dn u)) = AA.differential (letter R A (Dn u)) := by
      conv_lhs => rw [hDn_ofLetter u hu]
      rw [AA.barDifferential_ofLetter, letter_ofLetter, AInfinityAlgebra.differential_apply]
    have h2 : Dn (BB.barDifferential u) = Dn (P (BB.unaryBarDifferential w)) := by
      rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
        hDn _ (BB.higherBarDifferential_filtration n ⟨u, hu, rfl⟩), add_zero,
        ← LinearMap.comp_apply P BB.unaryBarDifferential,
        BB.lengthProj_comp_unaryBarDifferential, LinearMap.comp_apply]
    have h3 := congrArg (letter R A) hsq
    rw [map_add, map_zero, h1, h2] at h3
    dsimp only [u] at h3
    simp only [O, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.zero_apply, map_neg]
    rw [← neg_add, h3, neg_zero]
  have hΩ_bound :
      BB.differential ∘ₗ Ω - (1 : R) • (Ω ∘ₗ BB.unaryBarDifferential) = f.linearPart ∘ₗ O := by
    rw [one_smul]
    refine LinearMap.ext fun w ↦ ?_
    set u := P w
    have hu : u ∈ filtration R B (n + 1) := lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ w
    have hsq : BB.barDifferential (En u) - En (BB.barDifferential u) = -f.barMap (Dn u) := by
      simp only [En, Dn, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap]
      rw [← LinearMap.comp_apply BB.barDifferential BB.barDifferential,
        ← LinearMap.comp_apply BB.barDifferential BB.barDifferential, BB.barDifferential_sq]
      simp only [LinearMap.zero_apply, map_zero]
      abel
    have h1 : letter R B (BB.barDifferential (En u)) = BB.differential (letter R B (En u)) := by
      conv_lhs => rw [hEn_ofLetter u hu]
      rw [BB.barDifferential_ofLetter, letter_ofLetter, AInfinityAlgebra.differential_apply]
    have h2 : En (BB.barDifferential u) = En (P (BB.unaryBarDifferential w)) := by
      rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
        hEn _ (BB.higherBarDifferential_filtration n ⟨u, hu, rfl⟩), add_zero,
        ← LinearMap.comp_apply P BB.unaryBarDifferential,
        BB.lengthProj_comp_unaryBarDifferential, LinearMap.comp_apply]
    have h3 : letter R B (-f.barMap (Dn u)) = -f.linearPart (letter R A (Dn u)) := by
      conv_lhs => rw [map_neg, hDn_ofLetter u hu, f.barMap_ofLetter, letter_ofLetter]
    have h4 := congrArg (letter R B) hsq
    rw [map_sub, h1, h2, h3] at h4
    simpa only [Ω, O, u, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      map_neg] using h4
  -- Stage 2: kill `(O, Ω)` with `(α, β)` supported above length `n`, and update `(gn, hn)`.
  obtain ⟨α, β, hα_deg, hβ_deg, hvanish, hα_eq, hβ_eq⟩ :=
    exists_obstruction_kill f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB BB 0 1
      hO_deg hΩ_deg hO_cocycle hΩ_bound
  rw [one_smul] at hα_eq hβ_eq
  rw [zero_sub] at hβ_deg
  have hαβ_zero : ∀ z ∈ filtration R B n, α z = 0 ∧ β z = 0 := by
    intro z hz
    have hPz : P z = 0 := lengthProj_apply_eq_zero_of_mem_filtration R B n.lt_succ_self hz
    exact hvanish z (by simp [O, hPz]) (by simp [Ω, hPz])
  set gn' := gn + α
  set hn' := hn - β
  set Gn' := coalgHom R gn'
  set Hn' := gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ Gn') hn'
  have hgn'_eq : ∀ z ∈ filtration R B n, gn' z = gn z := fun z hz ↦ by
    simp [gn', (hαβ_zero z hz).1]
  have hhn'_eq : ∀ z ∈ filtration R B n, hn' z = hn z := fun z hz ↦ by
    simp [hn', (hαβ_zero z hz).2]
  have hGn'_eq : ∀ z ∈ filtration R B n, Gn' z = Gn z := fun z hz ↦
    (isCoalgHom_coalgHom gn').apply_eq_of_mem_filtration hGn_coalg
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom, hgn'_eq w hw]) hz
  have hGn'_sub : ∀ v ∈ filtration R B (n + 1), (Gn' - Gn) v = ofLetter R A (α v) := by
    intro v hv
    have h := ((isCoalgHom_coalgHom gn').isGradedCoderivationAlong_sub
      (G := BB.grading.shift 1) hGn_coalg)
      |>.apply_eq_ofLetter_of_mem_filtration_succ
        (fun z hz ↦ by rw [LinearMap.sub_apply, hGn'_eq z hz, sub_self]) hv
    rw [h]
    congr 1
    rw [LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
      ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom]
    simp [gn']
  -- Stage 3: the updated morphism and homotopy defects vanish on `filtration R B (n + 1)`.
  have hDn'_zero : ∀ z ∈ filtration R B (n + 1),
      (AA.barDifferential ∘ₗ Gn' - Gn' ∘ₗ BB.barDifferential) z = 0 := by
    set Dn' := AA.barDifferential ∘ₗ Gn' - Gn' ∘ₗ BB.barDifferential
    have hDn'_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 Gn' Gn' Dn' :=
      isGradedCoderivationAlong_barDifferential_sub (isCoalgHom_coalgHom gn')
        (isHomogeneous_coalgHom (hgn_deg.add hα_deg))
    have hDn'_n : ∀ z ∈ filtration R B n, Dn' z = 0 := fun z hz ↦ by
      rw [← hDn z hz]
      simp only [Dn', Dn, LinearMap.sub_apply, LinearMap.comp_apply, hGn'_eq z hz,
        hGn'_eq _ (BB.barDifferential_mem_filtration hz)]
    intro z hz
    rw [hDn'_cod.apply_eq_ofLetter_of_mem_filtration_succ hDn'_n hz]
    suffices letter R A (Dn' z) = 0 by rw [this, map_zero]
    have hsub : Dn' z - Dn z =
        AA.barDifferential ((Gn' - Gn) z) - (Gn' - Gn) (BB.barDifferential z) := by
      simp only [Dn', Dn, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
      abel
    have h1 : letter R A (AA.barDifferential ((Gn' - Gn) z)) = AA.differential (α z) := by
      rw [hGn'_sub z hz, AA.barDifferential_ofLetter, letter_ofLetter,
        AInfinityAlgebra.differential_apply]
    have h2 : letter R A ((Gn' - Gn) (BB.barDifferential z)) = α (BB.unaryBarDifferential z) := by
      rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
        hGn'_sub _ (BB.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
        LinearMap.sub_apply,
        hGn'_eq _ (BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩), sub_self, add_zero,
        letter_ofLetter]
    have h3 := congrArg (letter R A) hsub
    rw [map_sub, map_sub, h1, h2] at h3
    have h4 := LinearMap.congr_fun hα_eq z
    simp only [O, P, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply] at h4
    have hPz : letter R A (Dn (P z)) = letter R A (Dn z) :=
      apply_lengthProj_of_mem_filtration R B (f := letter R A ∘ₗ Dn)
        (fun w hw ↦ by rw [LinearMap.comp_apply, hDn w hw, map_zero]) hz
    rw [hPz] at h4
    rw [sub_eq_iff_eq_add'.1 h3, h4, add_neg_cancel]
  have hHn'_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ Gn')
      Hn' :=
    isGradedCoderivationAlong_gradedCoderivAlong (isCoalgHom_id B)
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom gn')) hn'
  have hHn'_deg : LinearMap.IsHomogeneous Hn' (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) := by
    refine isHomogeneous_gradedCoderivAlong (LinearMap.isHomogeneous_id _) ?_ (hhn_deg.sub hβ_deg)
    simpa only [add_zero] using
      f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom (hgn_deg.add hα_deg))
  have hHn'_eq : ∀ z ∈ filtration R B n, Hn' z = Hn z := fun z hz ↦
    hHn'_cod.apply_eq_of_mem_filtration hHn_cod (fun _ _ ↦ rfl)
      (fun w hw ↦ by simp only [LinearMap.comp_apply, hGn'_eq w hw])
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
          ← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong, hhn'_eq w hw]) hz
  have hHn'_sub : ∀ v ∈ filtration R B (n + 1), (Hn' - Hn) v = -ofLetter R B (β v) := by
    intro v hv
    have h := hHn'_cod.sub_apply_eq_ofLetter_of_mem_filtration_succ hHn_cod (fun _ _ ↦ rfl)
      (fun w hw ↦ by simp only [LinearMap.comp_apply, hGn'_eq w hw]) hHn'_eq hv
    rw [h, ← map_neg]
    congr 1
    rw [LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply (letter R B),
      letter_comp_gradedCoderivAlong, ← LinearMap.comp_apply (letter R B),
      letter_comp_gradedCoderivAlong]
    simp [hn']
  refine ⟨gn', hn', hgn_deg.add hα_deg, hhn_deg.sub hβ_deg,
    fun z hz ↦ ⟨hgn'_eq z hz, hhn'_eq z hz⟩, hDn'_zero, ?_⟩
  set En' := ((LinearMap.id : Module.End R (ReducedTensorWords R B)) - f.barMap ∘ₗ Gn') -
    (BB.barDifferential ∘ₗ Hn' + Hn' ∘ₗ BB.barDifferential)
  have hFGn'_intertwine : ∀ z ∈ filtration R B n,
      BB.barDifferential ((f.barMap ∘ₗ Gn') z) = (f.barMap ∘ₗ Gn') (BB.barDifferential z) := by
    intro z hz
    have h0 := sub_eq_zero.1 (hDn'_zero z (filtration_monotone R B n.le_succ hz))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h0 ⊢
    rw [f.barDifferential_barMap, h0]
  have hEn'_n : ∀ z ∈ filtration R B n, En' z = 0 := fun z hz ↦ by
    rw [← hEn z hz]
    simp only [En', En, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      hGn'_eq z hz, hHn'_eq z hz, hHn'_eq _ (BB.barDifferential_mem_filtration hz)]
  intro z hz
  have hEn'_let : En' z = ofLetter R B (letter R B (En' z)) :=
    hHn'_cod.sub_comp_add_comp_apply_eq_ofLetter_of_mem_filtration_succ hHn'_deg (by decide)
      BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
      BB.isGradedCoderivation_barDifferential (isCoalgHom_id B)
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom gn')) (LinearMap.isHomogeneous_id _)
      (fun _ _ ↦ rfl) hFGn'_intertwine hEn'_n hz
  rw [hEn'_let]
  suffices letter R B (En' z) = 0 by rw [this, map_zero]
  have hsub : En' z - En z = -f.barMap ((Gn' - Gn) z) - BB.barDifferential ((Hn' - Hn) z) -
      (Hn' - Hn) (BB.barDifferential z) := by
    simp only [En', En, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub]
    abel
  have h1 : letter R B (f.barMap ((Gn' - Gn) z)) = f.linearPart (α z) := by
    rw [hGn'_sub z hz, f.barMap_ofLetter, letter_ofLetter]
  have h2 : letter R B (BB.barDifferential ((Hn' - Hn) z)) = -BB.differential (β z) := by
    rw [hHn'_sub z hz, map_neg, BB.barDifferential_ofLetter, map_neg, letter_ofLetter,
      AInfinityAlgebra.differential_apply]
  have h3 : letter R B ((Hn' - Hn) (BB.barDifferential z)) = -β (BB.unaryBarDifferential z) := by
    rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
      hHn'_sub _ (BB.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
      LinearMap.sub_apply,
      hHn'_eq _ (BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩), sub_self, add_zero,
      map_neg, letter_ofLetter]
  have h4 := congrArg (letter R B) hsub
  simp only [map_sub, map_neg, h1, h2, h3] at h4
  have h5 := LinearMap.congr_fun hβ_eq z
  simp only [Ω, P, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at h5
  have hPz : letter R B (En (P z)) = letter R B (En z) :=
    apply_lengthProj_of_mem_filtration R B (f := letter R B ∘ₗ En)
      (fun w hw ↦ by rw [LinearMap.comp_apply, hEn w hw, map_zero]) hz
  rw [hPz] at h5
  have h6 : letter R B (En' z) - letter R B (En z) = -letter R B (En z) := by
    rw [h4, ← h5]
    abel
  exact sub_eq_neg_self.1 h6

private structure RightInverseApprox (f : AInfinityHom AA BB) (n : ℕ) where
  g : ReducedTensorWords R B →ₗ[R] A
  h : ReducedTensorWords R B →ₗ[R] B
  g_deg : LinearMap.IsHomogeneous g (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  h_deg : LinearMap.IsHomogeneous h (gradedPiece (BB.grading.shift 1))
    (BB.grading.shift 1).piece (-1)
  D_zero : ∀ z ∈ filtration R B n,
    (AA.barDifferential ∘ₗ coalgHom R g - coalgHom R g ∘ₗ BB.barDifferential) z = 0
  E_zero : ∀ z ∈ filtration R B n,
    (((LinearMap.id : Module.End R (ReducedTensorWords R B)) - f.barMap ∘ₗ coalgHom R g) -
      (BB.barDifferential ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
          (f.barMap ∘ₗ coalgHom R g) h +
        gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
          (f.barMap ∘ₗ coalgHom R g) h ∘ₗ BB.barDifferential)) z = 0

/-- **Right homotopy inverse from a graded chain-homotopy equivalence.**  Every graded
chain-homotopy inverse `g₁` of `f.linearPart` lifts to an `A∞` morphism `g : BB ⟶ AA` with
`g.linearPart = g₁` together with a homotopy `id_B ⇒ f ∘ g`. -/
theorem exists_rightHomotopyInverse_of_chainHomotopyEquiv (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_deg : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_deg : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁ : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA : LinearMap.id - g₁ ∘ₗ f.linearPart = AA.differential ∘ₗ sA + sA ∘ₗ AA.differential)
    (hsB : LinearMap.id - f.linearPart ∘ₗ g₁ = BB.differential ∘ₗ sB + sB ∘ₗ BB.differential) :
    ∃ g : AInfinityHom BB AA,
      g.linearPart = g₁ ∧ Nonempty (Homotopy (AInfinityHom.id BB) (f.comp g)) := by
  let g₀ : ReducedTensorWords R B →ₗ[R] A := g₁ ∘ₗ letter R B
  let h₀ : ReducedTensorWords R B →ₗ[R] B := sB ∘ₗ letter R B
  let base : RightInverseApprox f 1 :=
    { g := g₀
      h := h₀
      g_deg := by
        simpa only [add_zero] using (LinearMap.isHomogeneous_shift_piece_iff.2 hg₁_deg).comp
          (isHomogeneous_letter (BB.grading.shift 1))
      h_deg := by
        simpa only [zero_add] using (LinearMap.isHomogeneous_shift_piece_iff.2 hsB_deg).comp
          (isHomogeneous_letter (BB.grading.shift 1))
      D_zero := apply_eq_zero_of_mem_filtration_one R B <| LinearMap.ext fun b ↦ by
        simp only [g₀, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
          coalgHom_ofLetter, letter_ofLetter, AA.barDifferential_ofLetter,
          BB.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply]
        rw [← LinearMap.comp_apply AA.differential g₁, hg₁, LinearMap.comp_apply, sub_self]
      E_zero := apply_eq_zero_of_mem_filtration_one R B <| LinearMap.ext fun b ↦ by
        have hb := LinearMap.congr_fun hsB b
        simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
          LinearMap.comp_apply, AInfinityAlgebra.differential_apply] at hb
        simp only [g₀, h₀, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
          LinearMap.comp_apply, LinearMap.zero_apply, coalgHom_ofLetter,
          gradedCoderivAlong_ofLetter, letter_ofLetter, f.barMap_ofLetter,
          BB.barDifferential_ofLetter]
        rw [← map_sub, ← map_add, hb, sub_self] }
  let next : ∀ k (s : RightInverseApprox f (k + 1)),
      {s' : RightInverseApprox f (k + 2) //
        ∀ z ∈ filtration R B (k + 1), s'.g z = s.g z ∧ s'.h z = s.h z} := fun k s ↦
    let hex := rightInverse_step f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB (k + 1)
      s.g_deg s.h_deg s.D_zero s.E_zero
    let gn' := Classical.choose hex
    let hspec := Classical.choose_spec hex
    let hn' := Classical.choose hspec
    let hspec' := Classical.choose_spec hspec
    ⟨⟨gn', hn', hspec'.1, hspec'.2.1, hspec'.2.2.2.1, hspec'.2.2.2.2⟩, hspec'.2.2.1⟩
  let seq : ∀ k, RightInverseApprox f (k + 1) := fun k ↦
    Nat.rec base (fun m ih ↦ (next m ih).1) k
  have hseq_eq : ∀ k, ∀ z ∈ filtration R B (k + 1),
      (seq (k + 1)).g z = (seq k).g z ∧ (seq (k + 1)).h z = (seq k).h z :=
    fun k ↦ (next k (seq k)).2
  let gt : ℕ → ReducedTensorWords R B →ₗ[R] A := fun n ↦ (seq (n - 1)).g
  let ht : ℕ → ReducedTensorWords R B →ₗ[R] B := fun n ↦ (seq (n - 1)).h
  have hgt_stab : ∀ n, ∀ z ∈ filtration R B n, gt (n + 1) z = gt n z := by
    rintro (_ | k) z hz
    · rfl
    · exact (hseq_eq k z hz).1
  have hht_stab : ∀ n, ∀ z ∈ filtration R B n, ht (n + 1) z = ht n z := by
    rintro (_ | k) z hz
    · rfl
    · exact (hseq_eq k z hz).2
  set g_taylor := limitMap R B gt
  set h_taylor := limitMap R B ht
  have hg_deg : LinearMap.IsHomogeneous g_taylor (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0 :=
    isHomogeneous_limitMap hgt_stab fun n ↦ (seq (n - 1)).g_deg
  have hh_deg : LinearMap.IsHomogeneous h_taylor (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1) :=
    isHomogeneous_limitMap hht_stab fun n ↦ (seq (n - 1)).h_deg
  have hG_eq : ∀ k, ∀ z ∈ filtration R B (k + 1),
      coalgHom R g_taylor z = coalgHom R (seq k).g z := fun k z hz ↦
    (isCoalgHom_coalgHom g_taylor).apply_eq_of_mem_filtration (isCoalgHom_coalgHom (seq k).g)
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          limitMap_apply_of_mem_filtration hgt_stab hw]
        rfl) hz
  have hg_bar : AA.taylor ∘ₗ coalgHom R g_taylor = g_taylor ∘ₗ BB.barDifferential := by
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨k, hk⟩ := exists_mem_filtration R B z
    have hz : z ∈ filtration R B (k + 1) := filtration_monotone R B k.le_succ hk
    have hbz : BB.barDifferential z ∈ filtration R B (k + 1) := BB.barDifferential_mem_filtration hz
    have h0 := congrArg (letter R A) (sub_eq_zero.1 ((seq k).D_zero z hz))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h0
    rw [← LinearMap.comp_apply (letter R A) AA.barDifferential, AA.letter_comp_barDifferential,
      ← LinearMap.comp_apply (letter R A) (coalgHom R (seq k).g), letter_comp_coalgHom] at h0
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hG_eq k z hz, h0,
      limitMap_apply_of_mem_filtration hgt_stab hbz]
    rfl
  let g : AInfinityHom BB AA := ofTaylor g_taylor hg_deg hg_bar
  have hg_lin : g.linearPart = g₁ := LinearMap.ext fun b ↦ by
    have hb : ofLetter R B b ∈ filtration R B 1 := ofLetter_mem_filtration R B b
    have hgt1 : gt 1 = g₀ := rfl
    rw [linearPart_apply, taylor_ofTaylor, limitMap_apply_of_mem_filtration hgt_stab hb, hgt1,
      LinearMap.comp_apply, letter_ofLetter]
  set H := gradedCoderivAlong (BB.grading.shift 1) 1 (AInfinityHom.id BB).barMap
    (f.comp g).barMap h_taylor
  have hH_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1
      (AInfinityHom.id BB).barMap (f.comp g).barMap H :=
    isGradedCoderivationAlong_gradedCoderivAlong (AInfinityHom.id BB).isCoalgHom_barMap
      (f.comp g).isCoalgHom_barMap h_taylor
  have hH_deg : LinearMap.IsHomogeneous H (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) :=
    isHomogeneous_gradedCoderivAlong (AInfinityHom.id BB).isHomogeneous_barMap
      (f.comp g).isHomogeneous_barMap hh_deg
  have hH_eq : ∀ k, ∀ z ∈ filtration R B (k + 1),
      H z = gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R (seq k).g) (seq k).h z := fun k z hz ↦
    hH_cod.apply_eq_of_mem_filtration
      (isGradedCoderivationAlong_gradedCoderivAlong (isCoalgHom_id B)
        (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (seq k).g)) (seq k).h)
      (fun w _ ↦ by rw [barMap_id])
      (fun w hw ↦ by
        simp only [g, barMap_comp, barMap_ofTaylor, LinearMap.comp_apply, hG_eq k w hw])
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
          ← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
          limitMap_apply_of_mem_filtration hht_stab hw]
        rfl) hz
  have hH_bar : (AInfinityHom.id BB).barMap - (f.comp g).barMap =
      BB.barDifferential ∘ₗ H + H ∘ₗ BB.barDifferential := by
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨k, hk⟩ := exists_mem_filtration R B z
    have hz : z ∈ filtration R B (k + 1) := filtration_monotone R B k.le_succ hk
    have hbz : BB.barDifferential z ∈ filtration R B (k + 1) := BB.barDifferential_mem_filtration hz
    have h0 := sub_eq_zero.1 ((seq k).E_zero z hz)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at h0
    simp only [g, barMap_id, barMap_comp, barMap_ofTaylor, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, hG_eq k z hz, hH_eq k z hz, hH_eq k _ hbz]
    exact h0
  exact ⟨g, hg_lin, ⟨⟨H, hH_cod, hH_deg, hH_bar⟩⟩⟩

/-! ### Faithfulness of postcomposition on `Homotopy` -/

private noncomputable def transDiffNegOne (φ₁ φ₂ : AInfinityHom CC AA) :
    reducedTransformationCochains φ₁ φ₂ (-1) →ₗ[R] reducedTransformationCochains φ₁ φ₂ 0 :=
  reducedTransformationDifferential φ₁ φ₂ (-1)

private noncomputable def transDiffNegTwo (ψ₁ ψ₂ : AInfinityHom CC BB) :
    reducedTransformationCochains ψ₁ ψ₂ (-2) →ₗ[R] reducedTransformationCochains ψ₁ ψ₂ (-1) :=
  reducedTransformationDifferential ψ₁ ψ₂ (-2)

private theorem reducedTransformationDifferential_transDiffNegOne {φ₁ φ₂ : AInfinityHom CC AA}
    (H : reducedTransformationCochains φ₁ φ₂ (-1)) :
    reducedTransformationDifferential φ₁ φ₂ 0 (transDiffNegOne φ₁ φ₂ H) = 0 :=
  reducedTransformationDifferential_reducedTransformationDifferential (-1) H

private theorem transDiffNegOne_transDiffNegTwo {ψ₁ ψ₂ : AInfinityHom CC BB}
    (M : reducedTransformationCochains ψ₁ ψ₂ (-2)) :
    transDiffNegOne ψ₁ ψ₂ (transDiffNegTwo ψ₁ ψ₂ M) = 0 :=
  reducedTransformationDifferential_reducedTransformationDifferential (-2) M

private theorem transDiffNegOne_compRight (f : AInfinityHom AA BB) {φ₁ φ₂ : AInfinityHom CC AA}
    (H : reducedTransformationCochains φ₁ φ₂ (-1)) :
    transDiffNegOne (f.comp φ₁) (f.comp φ₂)
        (reducedTransformationCochains.compRight f (-1) H) =
      reducedTransformationCochains.compRight f 0 (transDiffNegOne φ₁ φ₂ H) :=
  reducedTransformationDifferential_compRight f H

private theorem coe_transDiffNegOne {φ₁ φ₂ : AInfinityHom CC AA}
    (H : reducedTransformationCochains φ₁ φ₂ (-1)) :
    (transDiffNegOne φ₁ φ₂ H : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) =
      AA.barDifferential ∘ₗ H +
        (H : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) ∘ₗ CC.barDifferential :=
  coe_reducedTransformationDifferential_neg_one H

private theorem coe_transDiffNegTwo {ψ₁ ψ₂ : AInfinityHom CC BB}
    (M : reducedTransformationCochains ψ₁ ψ₂ (-2)) :
    (transDiffNegTwo ψ₁ ψ₂ M : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) =
      BB.barDifferential ∘ₗ M -
        (M : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) ∘ₗ CC.barDifferential := by
  have hneg2 : ((-2 : ℤ).negOnePow : ℤ) = 1 := by decide
  rw [transDiffNegTwo, coe_reducedTransformationDifferential, Units.smul_def, hneg2, one_zsmul]

/-- One arity step in `reducedTransformationComplex`: extends cochains `(Hₙ, Mₙ)` killing a closed
degree-zero transformation `D₀` and its `compRight f` witness `K₀` up to tensor length `n` to
`(Hₙ₊₁, Mₙ₊₁)` killing them up to length `n + 1` and agreeing with `Hₙ` up to length `n`. -/
private theorem transformation_step (f : AInfinityHom AA BB) {g₁ : B →ₗ[R] A}
    {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_deg : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_deg : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁ : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA : LinearMap.id - g₁ ∘ₗ f.linearPart = AA.differential ∘ₗ sA + sA ∘ₗ AA.differential)
    (hsB : LinearMap.id - f.linearPart ∘ₗ g₁ = BB.differential ∘ₗ sB + sB ∘ₗ BB.differential)
    {φ₁ φ₂ : AInfinityHom CC AA} {D₀ : reducedTransformationCochains φ₁ φ₂ 0}
    (hD₀ : reducedTransformationDifferential φ₁ φ₂ 0 D₀ = 0)
    {K₀ : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1)}
    (hK₀ : transDiffNegOne (f.comp φ₁) (f.comp φ₂) K₀ =
      reducedTransformationCochains.compRight f 0 D₀)
    (n : ℕ) {Hn : reducedTransformationCochains φ₁ φ₂ (-1)}
    {Mn : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-2)}
    (hDn : ∀ z ∈ filtration R C n,
      ((D₀ - transDiffNegOne φ₁ φ₂ Hn : reducedTransformationCochains φ₁ φ₂ 0) :
        ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z = 0)
    (hEn : ∀ z ∈ filtration R C n,
      ((reducedTransformationCochains.compRight f (-1) Hn - K₀ -
        transDiffNegTwo (f.comp φ₁) (f.comp φ₂) Mn :
          reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1)) :
            ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) z = 0) :
    ∃ (Hn' : reducedTransformationCochains φ₁ φ₂ (-1))
      (Mn' : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-2)),
      (∀ z ∈ filtration R C n,
        reducedTransformationCochains.taylor Hn' z =
          reducedTransformationCochains.taylor Hn z) ∧
      (∀ z ∈ filtration R C (n + 1),
        ((D₀ - transDiffNegOne φ₁ φ₂ Hn' : reducedTransformationCochains φ₁ φ₂ 0) :
          ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z = 0) ∧
      (∀ z ∈ filtration R C (n + 1),
        ((reducedTransformationCochains.compRight f (-1) Hn' - K₀ -
          transDiffNegTwo (f.comp φ₁) (f.comp φ₂) Mn' :
            reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1)) :
              ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) z = 0) := by
  -- Stage 1: extract the length-`(n + 1)` Taylor obstructions `(O, Ω)` from `(Dn, En)`.
  set Dn : reducedTransformationCochains φ₁ φ₂ 0 := D₀ - transDiffNegOne φ₁ φ₂ Hn
  set En : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1) :=
    reducedTransformationCochains.compRight f (-1) Hn - K₀ -
      transDiffNegTwo (f.comp φ₁) (f.comp φ₂) Mn
  set P := lengthProj R C ⟨n + 1, n.succ_pos⟩
  have hDn_ofLetter : ∀ v ∈ filtration R C (n + 1),
      (Dn : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) v =
        ofLetter R A (reducedTransformationCochains.taylor Dn v) := fun v hv ↦ by
    rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply]
    exact (reducedTransformationCochains.isGradedCoderivationAlong Dn)
      |>.apply_eq_ofLetter_of_mem_filtration_succ hDn hv
  have hEn_ofLetter : ∀ v ∈ filtration R C (n + 1),
      (En : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) v =
        ofLetter R B (reducedTransformationCochains.taylor En v) := fun v hv ↦ by
    rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply]
    exact (reducedTransformationCochains.isGradedCoderivationAlong En)
      |>.apply_eq_ofLetter_of_mem_filtration_succ hEn hv
  have hdDn : reducedTransformationDifferential φ₁ φ₂ 0 Dn = 0 := by
    rw [map_sub, hD₀, reducedTransformationDifferential_transDiffNegOne, sub_self]
  have hdEn : transDiffNegOne (f.comp φ₁) (f.comp φ₂) En =
      -reducedTransformationCochains.compRight f 0 Dn := by
    rw [map_sub, map_sub, transDiffNegOne_compRight, hK₀, transDiffNegOne_transDiffNegTwo, sub_zero,
      map_sub]
    abel
  let O : ReducedTensorWords R C →ₗ[R] A := reducedTransformationCochains.taylor Dn ∘ₗ P
  let Ω : ReducedTensorWords R C →ₗ[R] B := -(reducedTransformationCochains.taylor En ∘ₗ P)
  have hO_deg : LinearMap.IsHomogeneous O (gradedPiece (CC.grading.shift 1))
      (AA.grading.shift 1).piece (-1 + 1) := by
    simpa only [neg_add_cancel, add_zero] using
      (reducedTransformationCochains.isHomogeneous_taylor Dn).comp
        (isHomogeneous_lengthProj (CC.grading.shift 1) _)
  have hΩ_deg : LinearMap.IsHomogeneous Ω (gradedPiece (CC.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
    refine LinearMap.IsHomogeneous.neg ?_
    simpa only [zero_add] using
      (reducedTransformationCochains.isHomogeneous_taylor En).comp
        (isHomogeneous_lengthProj (CC.grading.shift 1) _)
  have hO_cocycle : AA.differential ∘ₗ O + (-1 : R) • (O ∘ₗ CC.unaryBarDifferential) = 0 := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    refine LinearMap.ext fun w ↦ ?_
    set u := P w
    have hu : u ∈ filtration R C (n + 1) := lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ w
    have hintertwine := LinearMap.congr_fun
      ((reducedTransformationDifferential_zero_eq_zero_iff Dn).1 hdDn) u
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hintertwine
    have h1 : letter R A (AA.barDifferential
        ((Dn : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) u)) =
        AA.differential (reducedTransformationCochains.taylor Dn u) := by
      rw [hDn_ofLetter u hu, AA.barDifferential_ofLetter, letter_ofLetter,
        AInfinityAlgebra.differential_apply]
    have h2 : (Dn : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) (CC.barDifferential u) =
        (Dn : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A)
          (P (CC.unaryBarDifferential w)) := by
      rw [CC.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
        hDn _ (CC.higherBarDifferential_filtration n ⟨u, hu, rfl⟩), add_zero,
        ← LinearMap.comp_apply P CC.unaryBarDifferential,
        CC.lengthProj_comp_unaryBarDifferential, LinearMap.comp_apply]
    have h3 := congrArg (letter R A) hintertwine
    rw [h1, h2] at h3
    simpa only [O, u, reducedTransformationCochains.taylor_def, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.zero_apply, sub_eq_zero] using h3
  have hΩ_bound :
      BB.differential ∘ₗ Ω - (-1 : R) • (Ω ∘ₗ CC.unaryBarDifferential) = f.linearPart ∘ₗ O := by
    rw [neg_one_smul, sub_neg_eq_add]
    refine LinearMap.ext fun w ↦ ?_
    set u := P w
    have hu : u ∈ filtration R C (n + 1) := lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ w
    have hrel := LinearMap.congr_fun (Subtype.coe_inj.2 hdEn) u
    rw [coe_transDiffNegOne, reducedTransformationCochains.coe_neg,
      reducedTransformationCochains.coe_compRight, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply] at hrel
    have h1 : letter R B (BB.barDifferential
        ((En : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) u)) =
        BB.differential (reducedTransformationCochains.taylor En u) := by
      rw [hEn_ofLetter u hu, BB.barDifferential_ofLetter, letter_ofLetter,
        AInfinityAlgebra.differential_apply]
    have h2 : (En : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) (CC.barDifferential u) =
        (En : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B)
          (P (CC.unaryBarDifferential w)) := by
      rw [CC.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
        hEn _ (CC.higherBarDifferential_filtration n ⟨u, hu, rfl⟩), add_zero,
        ← LinearMap.comp_apply P CC.unaryBarDifferential,
        CC.lengthProj_comp_unaryBarDifferential, LinearMap.comp_apply]
    have h3 : letter R B (-f.barMap
        ((Dn : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) u)) =
        -f.linearPart (reducedTransformationCochains.taylor Dn u) := by
      rw [map_neg, hDn_ofLetter u hu, f.barMap_ofLetter, letter_ofLetter]
    have h4 := congrArg (letter R B) hrel
    rw [map_add, h1, h2, h3] at h4
    have h5 := congrArg Neg.neg h4
    simpa only [Ω, O, u, reducedTransformationCochains.taylor_def, LinearMap.add_apply,
      LinearMap.neg_apply, LinearMap.comp_apply, neg_add, neg_neg, map_neg] using h5
  -- Stage 2: kill `(O, Ω)` with `(α, β)` and form the cochain increments `(ΔH, ΔM)`.
  obtain ⟨α, β, hα_deg, hβ_deg, hvanish, hα_eq, hβ_eq⟩ :=
    exists_obstruction_kill f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB CC (-1) (-1)
      hO_deg hΩ_deg hO_cocycle hΩ_bound
  rw [neg_one_smul, sub_neg_eq_add] at hα_eq
  rw [neg_one_smul, ← sub_eq_add_neg] at hβ_eq
  have hβ_deg' : LinearMap.IsHomogeneous β (gradedPiece (CC.grading.shift 1))
      (BB.grading.shift 1).piece (-2) := hβ_deg
  have hαβ_zero : ∀ z ∈ filtration R C n, α z = 0 ∧ β z = 0 := by
    intro z hz
    have hPz : P z = 0 := lengthProj_apply_eq_zero_of_mem_filtration R C n.lt_succ_self hz
    exact hvanish z (by simp [O, hPz]) (by simp [Ω, hPz])
  let ΔH : reducedTransformationCochains φ₁ φ₂ (-1) :=
    reducedTransformationCochains.ofTaylor φ₁ φ₂ α hα_deg
  let ΔM : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-2) :=
    reducedTransformationCochains.ofTaylor (f.comp φ₁) (f.comp φ₂) β hβ_deg'
  have hΔH_zero : ∀ z ∈ filtration R C n,
      (ΔH : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z = 0 := fun z hz ↦ by
    simpa only [LinearMap.zero_apply] using
      (reducedTransformationCochains.isGradedCoderivationAlong ΔH).apply_eq_of_mem_filtration
        (isGradedCoderivationAlong_zero _ _ _ _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun w hw ↦ by
          rw [← LinearMap.comp_apply, ← reducedTransformationCochains.taylor_def,
            reducedTransformationCochains.taylor_ofTaylor, (hαβ_zero w hw).1,
            LinearMap.zero_apply, map_zero]) hz
  have hΔM_zero : ∀ z ∈ filtration R C n,
      (ΔM : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) z = 0 := fun z hz ↦ by
    simpa only [LinearMap.zero_apply] using
      (reducedTransformationCochains.isGradedCoderivationAlong ΔM).apply_eq_of_mem_filtration
        (isGradedCoderivationAlong_zero _ _ _ _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun w hw ↦ by
          rw [← LinearMap.comp_apply, ← reducedTransformationCochains.taylor_def,
            reducedTransformationCochains.taylor_ofTaylor, (hαβ_zero w hw).2,
            LinearMap.zero_apply, map_zero]) hz
  have hΔH_ofLetter : ∀ v ∈ filtration R C (n + 1),
      (ΔH : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) v =
        ofLetter R A (α v) := fun v hv ↦ by
    rw [(reducedTransformationCochains.isGradedCoderivationAlong ΔH)
      |>.apply_eq_ofLetter_of_mem_filtration_succ hΔH_zero hv,
      ← LinearMap.comp_apply (letter R A), ← reducedTransformationCochains.taylor_def,
      reducedTransformationCochains.taylor_ofTaylor]
  have hΔM_ofLetter : ∀ v ∈ filtration R C (n + 1),
      (ΔM : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) v =
        ofLetter R B (β v) := fun v hv ↦ by
    rw [(reducedTransformationCochains.isGradedCoderivationAlong ΔM)
      |>.apply_eq_ofLetter_of_mem_filtration_succ hΔM_zero hv,
      ← LinearMap.comp_apply (letter R B), ← reducedTransformationCochains.taylor_def,
      reducedTransformationCochains.taylor_ofTaylor]
  -- Stage 3: verify that `Hn + ΔH` and `Mn + ΔM` kill both defects on `filtration R C (n + 1)`.
  refine ⟨Hn + ΔH, Mn + ΔM, fun z hz ↦ ?_, ?_, ?_⟩
  · rw [reducedTransformationCochains.taylor_add, LinearMap.add_apply,
      reducedTransformationCochains.taylor_ofTaylor, (hαβ_zero z hz).1, add_zero]
  · set Dn' : reducedTransformationCochains φ₁ φ₂ 0 :=
      D₀ - transDiffNegOne φ₁ φ₂ (Hn + ΔH)
    have hDn'_eq : Dn' = Dn - transDiffNegOne φ₁ φ₂ ΔH := by
      simp only [Dn', Dn, map_add]
      abel
    have hDn'_n : ∀ z ∈ filtration R C n,
        (Dn' : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z = 0 := fun z hz ↦ by
      rw [hDn'_eq, reducedTransformationCochains.coe_sub, LinearMap.sub_apply, hDn z hz,
        zero_sub, neg_eq_zero, coe_transDiffNegOne, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.comp_apply, hΔH_zero z hz, map_zero,
        hΔH_zero _ (CC.barDifferential_mem_filtration hz), add_zero]
    intro z hz
    rw [(reducedTransformationCochains.isGradedCoderivationAlong Dn')
      |>.apply_eq_ofLetter_of_mem_filtration_succ hDn'_n hz]
    suffices reducedTransformationCochains.taylor Dn' z = 0 by
      rw [← LinearMap.comp_apply (letter R A), ← reducedTransformationCochains.taylor_def,
        this, map_zero]
    have hdΔH : reducedTransformationCochains.taylor (transDiffNegOne φ₁ φ₂ ΔH) z =
        AA.differential (α z) + α (CC.unaryBarDifferential z) := by
      rw [reducedTransformationCochains.taylor_def, coe_transDiffNegOne,
        LinearMap.comp_apply, LinearMap.add_apply, map_add, LinearMap.comp_apply,
        LinearMap.comp_apply, hΔH_ofLetter z hz, AA.barDifferential_ofLetter, letter_ofLetter,
        AInfinityAlgebra.differential_apply, CC.barDifferential_eq_unary_add_higher,
        LinearMap.add_apply, map_add,
        hΔH_zero _ (CC.higherBarDifferential_filtration n ⟨z, hz, rfl⟩), add_zero,
        hΔH_ofLetter _ (CC.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
        letter_ofLetter]
    have hPz : reducedTransformationCochains.taylor Dn (P z) =
        reducedTransformationCochains.taylor Dn z :=
      apply_lengthProj_of_mem_filtration R C (f := reducedTransformationCochains.taylor Dn)
        (fun w hw ↦ by rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply,
          hDn w hw, map_zero]) hz
    have h4 := LinearMap.congr_fun hα_eq z
    simp only [O, P, LinearMap.add_apply, LinearMap.comp_apply] at h4
    rw [hPz] at h4
    rw [hDn'_eq, reducedTransformationCochains.taylor_sub, LinearMap.sub_apply, hdΔH, h4, sub_self]
  · set En' : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1) :=
      reducedTransformationCochains.compRight f (-1) (Hn + ΔH) - K₀ -
        transDiffNegTwo (f.comp φ₁) (f.comp φ₂) (Mn + ΔM)
    have hEn'_eq : En' = En + reducedTransformationCochains.compRight f (-1) ΔH -
        transDiffNegTwo (f.comp φ₁) (f.comp φ₂) ΔM := by
      simp only [En', En, map_add]
      abel
    have hEn'_n : ∀ z ∈ filtration R C n,
        (En' : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) z = 0 := fun z hz ↦ by
      rw [hEn'_eq, reducedTransformationCochains.coe_sub, Submodule.coe_add, LinearMap.sub_apply,
        LinearMap.add_apply, hEn z hz, zero_add, reducedTransformationCochains.coe_compRight,
        LinearMap.comp_apply, hΔH_zero z hz, map_zero, zero_sub, neg_eq_zero, coe_transDiffNegTwo,
        LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hΔM_zero z hz, map_zero,
        hΔM_zero _ (CC.barDifferential_mem_filtration hz), sub_zero]
    intro z hz
    rw [(reducedTransformationCochains.isGradedCoderivationAlong En')
      |>.apply_eq_ofLetter_of_mem_filtration_succ hEn'_n hz]
    suffices reducedTransformationCochains.taylor En' z = 0 by
      rw [← LinearMap.comp_apply (letter R B), ← reducedTransformationCochains.taylor_def,
        this, map_zero]
    have hfΔH : reducedTransformationCochains.taylor
        (reducedTransformationCochains.compRight f (-1) ΔH) z = f.linearPart (α z) := by
      rw [reducedTransformationCochains.taylor_def, reducedTransformationCochains.coe_compRight,
        LinearMap.comp_apply, LinearMap.comp_apply, hΔH_ofLetter z hz, f.barMap_ofLetter,
        letter_ofLetter]
    have hdΔM : reducedTransformationCochains.taylor
        (transDiffNegTwo (f.comp φ₁) (f.comp φ₂) ΔM) z =
        BB.differential (β z) - β (CC.unaryBarDifferential z) := by
      rw [reducedTransformationCochains.taylor_def, coe_transDiffNegTwo, LinearMap.comp_apply,
        LinearMap.sub_apply, map_sub, LinearMap.comp_apply, LinearMap.comp_apply,
        hΔM_ofLetter z hz, BB.barDifferential_ofLetter, letter_ofLetter,
        AInfinityAlgebra.differential_apply, CC.barDifferential_eq_unary_add_higher,
        LinearMap.add_apply, map_add,
        hΔM_zero _ (CC.higherBarDifferential_filtration n ⟨z, hz, rfl⟩), add_zero,
        hΔM_ofLetter _ (CC.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
        letter_ofLetter]
    have hPz : reducedTransformationCochains.taylor En (P z) =
        reducedTransformationCochains.taylor En z :=
      apply_lengthProj_of_mem_filtration R C (f := reducedTransformationCochains.taylor En)
        (fun w hw ↦ by rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply,
          hEn w hw, map_zero]) hz
    have h5 := LinearMap.congr_fun hβ_eq z
    simp only [Ω, P, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply] at h5
    rw [hPz] at h5
    rw [hEn'_eq, reducedTransformationCochains.taylor_sub,
      reducedTransformationCochains.taylor_add, LinearMap.sub_apply, LinearMap.add_apply,
      hfΔH, hdΔM, add_sub_assoc, h5, add_neg_cancel]

private theorem exists_reducedTransformation_eq_of_chainHomotopyEquiv (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_deg : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_deg : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁ : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA : LinearMap.id - g₁ ∘ₗ f.linearPart = AA.differential ∘ₗ sA + sA ∘ₗ AA.differential)
    (hsB : LinearMap.id - f.linearPart ∘ₗ g₁ = BB.differential ∘ₗ sB + sB ∘ₗ BB.differential)
    {φ₁ φ₂ : AInfinityHom CC AA} {D₀ : reducedTransformationCochains φ₁ φ₂ 0}
    (hD₀ : reducedTransformationDifferential φ₁ φ₂ 0 D₀ = 0)
    {K₀ : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1)}
    (hK₀ : reducedTransformationDifferential (f.comp φ₁) (f.comp φ₂) (-1) K₀ =
      reducedTransformationCochains.compRight f 0 D₀) :
    ∃ H : reducedTransformationCochains φ₁ φ₂ (-1),
      reducedTransformationDifferential φ₁ φ₂ (-1) H = D₀ := by
  let State (n : ℕ) :=
    {p : reducedTransformationCochains φ₁ φ₂ (-1) ×
        reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-2) //
      (∀ z ∈ filtration R C n,
        ((D₀ - transDiffNegOne φ₁ φ₂ p.1 : reducedTransformationCochains φ₁ φ₂ 0) :
          ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z = 0) ∧
      (∀ z ∈ filtration R C n,
        ((reducedTransformationCochains.compRight f (-1) p.1 - K₀ -
          transDiffNegTwo (f.comp φ₁) (f.comp φ₂) p.2 :
            reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1)) :
              ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) z = 0)}
  have base : State 0 := ⟨(0, 0),
    apply_eq_zero_of_mem_filtration_zero R C _,
    apply_eq_zero_of_mem_filtration_zero R C _⟩
  let next : ∀ n (s : State n),
      {s' : State (n + 1) // ∀ z ∈ filtration R C n,
        reducedTransformationCochains.taylor s'.1.1 z =
          reducedTransformationCochains.taylor s.1.1 z} := fun n s ↦
    let hex := transformation_step f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB hD₀ hK₀ n s.2.1 s.2.2
    let Hn' := Classical.choose hex
    let hspec := Classical.choose_spec hex
    let Mn' := Classical.choose hspec
    let hspec' := Classical.choose_spec hspec
    ⟨⟨(Hn', Mn'), hspec'.2.1, hspec'.2.2⟩, hspec'.1⟩
  let seq : ∀ n, State n := fun n ↦ Nat.rec base (fun m ih ↦ (next m ih).1) n
  let ht : ℕ → ReducedTensorWords R C →ₗ[R] A :=
    fun n ↦ reducedTransformationCochains.taylor (seq n).1.1
  have hht_stab : ∀ n, ∀ z ∈ filtration R C n, ht (n + 1) z = ht n z :=
    fun n ↦ (next n (seq n)).2
  let H : reducedTransformationCochains φ₁ φ₂ (-1) :=
    reducedTransformationCochains.ofTaylor φ₁ φ₂ (limitMap R C ht)
      (isHomogeneous_limitMap hht_stab fun n ↦
        reducedTransformationCochains.isHomogeneous_taylor (seq n).1.1)
  have hH_eq : ∀ n, ∀ z ∈ filtration R C n,
      (H : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z =
        ((seq n).1.1 : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z := fun n z hz ↦
    (reducedTransformationCochains.isGradedCoderivationAlong H).apply_eq_of_mem_filtration
      (reducedTransformationCochains.isGradedCoderivationAlong (seq n).1.1)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply, ← reducedTransformationCochains.taylor_def,
          ← LinearMap.comp_apply, ← reducedTransformationCochains.taylor_def,
          reducedTransformationCochains.taylor_ofTaylor,
          limitMap_apply_of_mem_filtration hht_stab hw]) hz
  refine ⟨H, Subtype.ext (LinearMap.ext fun z ↦ ?_)⟩
  obtain ⟨n, hn⟩ := exists_mem_filtration R C z
  have h0 := sub_eq_zero.1 ((seq n).2.1 z hn)
  rw [coe_transDiffNegOne, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply] at h0
  rw [coe_reducedTransformationDifferential_neg_one, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, hH_eq n z hn, hH_eq n _ (CC.barDifferential_mem_filtration hn)]
  exact h0.symm

private theorem nonempty_homotopy_comp_iff_of_chainHomotopyEquiv (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_deg : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_deg : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁ : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA : LinearMap.id - g₁ ∘ₗ f.linearPart = AA.differential ∘ₗ sA + sA ∘ₗ AA.differential)
    (hsB : LinearMap.id - f.linearPart ∘ₗ g₁ = BB.differential ∘ₗ sB + sB ∘ₗ BB.differential)
    (φ₁ φ₂ : AInfinityHom CC AA) :
    Nonempty (Homotopy (f.comp φ₁) (f.comp φ₂)) ↔ Nonempty (Homotopy φ₁ φ₂) := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun ⟨h⟩ ↦ ⟨h.compRight f⟩⟩
  let D₀ : reducedTransformationCochains φ₁ φ₂ 0 :=
    ⟨φ₁.barMap - φ₂.barMap, barMap_sub_barMap_mem_reducedTransformationCochains φ₁ φ₂⟩
  let K₀ : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1) :=
    (Homotopy.equivCochains h).1
  have hK₀ : reducedTransformationDifferential (f.comp φ₁) (f.comp φ₂) (-1) K₀ =
      reducedTransformationCochains.compRight f 0 D₀ := by
    apply Subtype.ext
    rw [(Homotopy.equivCochains h).2, reducedTransformationCochains.coe_compRight,
      barMap_comp, barMap_comp, LinearMap.comp_sub]
  obtain ⟨H, hH⟩ := exists_reducedTransformation_eq_of_chainHomotopyEquiv f
    hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB (reducedTransformationDifferential_barMap_sub_barMap φ₁ φ₂)
    hK₀
  exact ⟨Homotopy.equivCochains.symm ⟨H, congrArg Subtype.val hH⟩⟩

/-! ### Two-sided homotopy inverses, composition, and two-out-of-three -/

/-- **Two-sided `A∞` homotopy inverse from a graded chain-homotopy equivalence.**  Every graded
chain-homotopy inverse `g₁` of `f.linearPart` lifts to an `A∞` morphism `g : BB ⟶ AA` with
`g.linearPart = g₁` together with homotopies `id_A ⇒ g ∘ f` and `id_B ⇒ f ∘ g`. -/
theorem exists_homotopyInverse_of_chainHomotopyEquiv (f : AInfinityHom AA BB)
    {g₁ : B →ₗ[R] A} {sA : A →ₗ[R] A} {sB : B →ₗ[R] B}
    (hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0)
    (hsA_deg : LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1))
    (hsB_deg : LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1))
    (hg₁ : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential)
    (hsA : LinearMap.id - g₁ ∘ₗ f.linearPart = AA.differential ∘ₗ sA + sA ∘ₗ AA.differential)
    (hsB : LinearMap.id - f.linearPart ∘ₗ g₁ = BB.differential ∘ₗ sB + sB ∘ₗ BB.differential) :
    ∃ g : AInfinityHom BB AA,
      g.linearPart = g₁ ∧
        Nonempty (Homotopy (AInfinityHom.id AA) (g.comp f)) ∧
        Nonempty (Homotopy (AInfinityHom.id BB) (f.comp g)) := by
  obtain ⟨g, hg_lin, ⟨hR⟩⟩ :=
    exists_rightHomotopyInverse_of_chainHomotopyEquiv f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB
  have hRf : Nonempty (Homotopy (f.comp (AInfinityHom.id AA)) (f.comp (g.comp f))) := by
    have h1 : (AInfinityHom.id BB).comp f = f.comp (AInfinityHom.id AA) := by rw [id_comp, comp_id]
    have h2 : (f.comp g).comp f = f.comp (g.comp f) := comp_assoc f g f
    exact ⟨h1 ▸ h2 ▸ hR.compLeft f⟩
  exact ⟨g, hg_lin,
    (nonempty_homotopy_comp_iff_of_chainHomotopyEquiv f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB
      (AInfinityHom.id AA) (g.comp f)).1 hRf,
    ⟨hR⟩⟩

/-- **Characterisation of `A∞` homotopy equivalences over a commutative ring.**  An `A∞` morphism
`f : AA ⟶ BB` is a homotopy equivalence if and only if its linear part `f.linearPart` is a graded
chain-homotopy equivalence between `(A, m₁)` and `(B, m₁)`. -/
theorem isHomotopyEquiv_iff (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ (g₁ : B →ₗ[R] A) (sA : A →ₗ[R] A) (sB : B →ₗ[R] B),
        LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0 ∧
          LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1) ∧
          LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1) ∧
          AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential ∧
          LinearMap.id - g₁ ∘ₗ f.linearPart =
            AA.differential ∘ₗ sA + sA ∘ₗ AA.differential ∧
          LinearMap.id - f.linearPart ∘ₗ g₁ =
            BB.differential ∘ₗ sB + sB ∘ₗ BB.differential :=
  ⟨IsHomotopyEquiv.exists_chainHomotopyEquiv,
    fun ⟨_, _, _, hg₁_deg, hsA_deg, hsB_deg, hg₁, hsA, hsB⟩ ↦
      let ⟨g, _, hL, hR⟩ :=
        exists_homotopyInverse_of_chainHomotopyEquiv f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB
      ⟨g, hL, hR⟩⟩

/-- Postcomposition with a homotopy equivalence `f` reflects coboundaries of closed degree-zero
reduced transformations. -/
theorem IsHomotopyEquiv.exists_reducedTransformation_eq_of_compRight {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) {φ₁ φ₂ : AInfinityHom CC AA}
    {D₀ : reducedTransformationCochains φ₁ φ₂ 0}
    (hD₀ : reducedTransformationDifferential φ₁ φ₂ 0 D₀ = 0)
    {K₀ : reducedTransformationCochains (f.comp φ₁) (f.comp φ₂) (-1)}
    (hK₀ : reducedTransformationDifferential (f.comp φ₁) (f.comp φ₂) (-1) K₀ =
      reducedTransformationCochains.compRight f 0 D₀) :
    ∃ H : reducedTransformationCochains φ₁ φ₂ (-1),
      reducedTransformationDifferential φ₁ φ₂ (-1) H = D₀ := by
  obtain ⟨_, _, _, hg₁_deg, hsA_deg, hsB_deg, hg₁, hsA, hsB⟩ := hf.exists_chainHomotopyEquiv
  exact exists_reducedTransformation_eq_of_chainHomotopyEquiv f
    hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB hD₀ hK₀

/-- Postcomposition with a homotopy equivalence reflects and preserves `Homotopy`. -/
theorem IsHomotopyEquiv.nonempty_homotopy_comp_iff {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) (φ₁ φ₂ : AInfinityHom CC AA) :
    Nonempty (Homotopy (f.comp φ₁) (f.comp φ₂)) ↔ Nonempty (Homotopy φ₁ φ₂) := by
  obtain ⟨_, _, _, hg₁_deg, hsA_deg, hsB_deg, hg₁, hsA, hsB⟩ := hf.exists_chainHomotopyEquiv
  exact nonempty_homotopy_comp_iff_of_chainHomotopyEquiv f
    hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB φ₁ φ₂

private theorem isHomotopyEquiv_of_linearPart_sub {f f' : AInfinityHom AA BB}
    {t : A →ₗ[R] B} (ht_deg : LinearMap.IsHomogeneous t AA.grading.piece BB.grading.piece (-1))
    (ht : f.linearPart - f'.linearPart = BB.differential ∘ₗ t + t ∘ₗ AA.differential)
    (hf : f.IsHomotopyEquiv) : f'.IsHomotopyEquiv := by
  obtain ⟨g₁, sA, sB, hg₁_deg, hsA_deg, hsB_deg, hg₁, hsA, hsB⟩ := hf.exists_chainHomotopyEquiv
  refine (isHomotopyEquiv_iff f').2 ⟨g₁, sA + g₁ ∘ₗ t, sB + t ∘ₗ g₁, hg₁_deg, ?_, ?_, hg₁, ?_, ?_⟩
  · refine hsA_deg.add ?_
    simpa only [add_zero] using hg₁_deg.comp ht_deg
  · refine hsB_deg.add ?_
    simpa only [zero_add] using ht_deg.comp hg₁_deg
  · calc LinearMap.id - g₁ ∘ₗ f'.linearPart
        = (LinearMap.id - g₁ ∘ₗ f.linearPart) + g₁ ∘ₗ (f.linearPart - f'.linearPart) := by
            rw [LinearMap.comp_sub]
            abel
      _ = AA.differential ∘ₗ (sA + g₁ ∘ₗ t) + (sA + g₁ ∘ₗ t) ∘ₗ AA.differential := by
            rw [hsA, ht]
            simp only [LinearMap.comp_add, LinearMap.add_comp, ← LinearMap.comp_assoc, hg₁]
            simp only [LinearMap.comp_assoc]
            abel
  · calc LinearMap.id - f'.linearPart ∘ₗ g₁
        = (LinearMap.id - f.linearPart ∘ₗ g₁) + (f.linearPart - f'.linearPart) ∘ₗ g₁ := by
            rw [LinearMap.sub_comp]
            abel
      _ = BB.differential ∘ₗ (sB + t ∘ₗ g₁) + (sB + t ∘ₗ g₁) ∘ₗ BB.differential := by
            rw [hsB, ht]
            simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc, hg₁]
            abel

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopy.isHomotopyEquiv_iff {f f' : AInfinityHom AA BB} (h : Homotopy f f') :
    f.IsHomotopyEquiv ↔ f'.IsHomotopyEquiv := by
  have ht_deg : LinearMap.IsHomogeneous h.linearHomotopy AA.grading.piece BB.grading.piece (-1) :=
    LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
      simpa only [sub_eq_add_neg] using h.linearHomotopy_mem ha
  have ht : f.linearPart - f'.linearPart =
      BB.differential ∘ₗ h.linearHomotopy + h.linearHomotopy ∘ₗ AA.differential :=
    LinearMap.ext fun a ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        AInfinityAlgebra.differential_apply] using h.linearPart_sub_linearPart a
  refine ⟨isHomotopyEquiv_of_linearPart_sub ht_deg ht,
    isHomotopyEquiv_of_linearPart_sub ht_deg.neg ?_⟩
  rw [← neg_sub, ht, LinearMap.comp_neg, LinearMap.neg_comp, neg_add]

/-- The composite of two `A∞` homotopy equivalences is an `A∞` homotopy equivalence. -/
theorem IsHomotopyEquiv.comp {k : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hk : k.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (k.comp f).IsHomotopyEquiv := by
  obtain ⟨g₁, sA, sB, hg₁_deg, hsA_deg, hsB_deg, hg₁, hsA, hsB⟩ := hf.exists_chainHomotopyEquiv
  obtain ⟨l₁, tB, tC, hl₁_deg, htB_deg, htC_deg, hl₁, htB, htC⟩ := hk.exists_chainHomotopyEquiv
  set dA := AA.differential
  set dB := BB.differential
  set dC := CC.differential
  set f₁ := f.linearPart
  set k₁ := k.linearPart
  have hf₁ : dB ∘ₗ f₁ = f₁ ∘ₗ dA := differential_comp_linearPart f
  have hk₁ : dC ∘ₗ k₁ = k₁ ∘ₗ dB := differential_comp_linearPart k
  refine (isHomotopyEquiv_iff (k.comp f)).2
    ⟨g₁ ∘ₗ l₁, sA + g₁ ∘ₗ tB ∘ₗ f₁, tC + k₁ ∘ₗ sB ∘ₗ l₁,
      by simpa only [add_zero] using hg₁_deg.comp hl₁_deg, ?_, ?_,
      by rw [← LinearMap.comp_assoc, hg₁, LinearMap.comp_assoc, hl₁, LinearMap.comp_assoc],
      ?_, ?_⟩
  · refine hsA_deg.add ?_
    simpa only [zero_add, add_zero] using hg₁_deg.comp (htB_deg.comp f.isHomogeneous_linearPart)
  · refine htC_deg.add ?_
    simpa only [zero_add, add_zero] using k.isHomogeneous_linearPart.comp (hsB_deg.comp hl₁_deg)
  · rw [linearPart_comp]
    calc LinearMap.id - (g₁ ∘ₗ l₁) ∘ₗ (k₁ ∘ₗ f₁)
        = (LinearMap.id - g₁ ∘ₗ f₁) + g₁ ∘ₗ (LinearMap.id - l₁ ∘ₗ k₁) ∘ₗ f₁ := by
            simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
              LinearMap.comp_assoc]
            abel
      _ = dA ∘ₗ (sA + g₁ ∘ₗ tB ∘ₗ f₁) + (sA + g₁ ∘ₗ tB ∘ₗ f₁) ∘ₗ dA := by
            rw [hsA, htB]
            simp only [LinearMap.comp_add, LinearMap.add_comp, ← LinearMap.comp_assoc, hg₁]
            simp only [LinearMap.comp_assoc, hf₁]
            abel
  · rw [linearPart_comp]
    calc LinearMap.id - (k₁ ∘ₗ f₁) ∘ₗ (g₁ ∘ₗ l₁)
        = (LinearMap.id - k₁ ∘ₗ l₁) + k₁ ∘ₗ (LinearMap.id - f₁ ∘ₗ g₁) ∘ₗ l₁ := by
            simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
              LinearMap.comp_assoc]
            abel
      _ = dC ∘ₗ (tC + k₁ ∘ₗ sB ∘ₗ l₁) + (tC + k₁ ∘ₗ sB ∘ₗ l₁) ∘ₗ dC := by
            rw [htC, hsB]
            simp only [LinearMap.comp_add, LinearMap.add_comp, ← LinearMap.comp_assoc, hk₁]
            simp only [LinearMap.comp_assoc, hl₁]
            abel

/-- **Two-out-of-three for `A∞` homotopy equivalences (right cancellation).**  If `f` and `k ∘ f`
are homotopy equivalences, then `k` is a homotopy equivalence. -/
theorem IsHomotopyEquiv.of_precomp {k : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) (hkf : (k.comp f).IsHomotopyEquiv) : k.IsHomotopyEquiv := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf
  have hg : g.IsHomotopyEquiv := ⟨f, ⟨hR⟩, ⟨hL⟩⟩
  have hk : Homotopy k ((k.comp f).comp g) := by
    simpa only [comp_id, comp_assoc] using hR.compRight k
  exact hk.isHomotopyEquiv_iff.2 (hkf.comp hg)

/-- **Two-out-of-three for `A∞` homotopy equivalences (left cancellation).**  If `k` and `k ∘ f`
are homotopy equivalences, then `f` is a homotopy equivalence. -/
theorem IsHomotopyEquiv.of_postcomp {k : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hk : k.IsHomotopyEquiv) (hkf : (k.comp f).IsHomotopyEquiv) : f.IsHomotopyEquiv := by
  obtain ⟨l, ⟨hL⟩, ⟨hR⟩⟩ := hk
  have hl : l.IsHomotopyEquiv := ⟨k, ⟨hR⟩, ⟨hL⟩⟩
  have hf : Homotopy f (l.comp (k.comp f)) := by
    simpa only [id_comp, comp_assoc] using hL.compLeft f
  exact hf.isHomotopyEquiv_iff.2 (hl.comp hkf)

end CommRing

/-! ### Homotopy inverses of quasi-isomorphisms over a field -/

section Field

variable {K : Type uR} {A : Type uA} {B : Type uB}
  [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

/-- Over a field, the linear part of any `A∞` quasi-isomorphism admits a graded chain-homotopy
inverse built from `cohomologyContraction` on the source and target. -/
theorem IsQuasiIso.exists_chainHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    ∃ (g₁ : B →ₗ[K] A) (sA : A →ₗ[K] A) (sB : B →ₗ[K] B),
      LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0 ∧
        LinearMap.IsHomogeneous sA AA.grading.piece AA.grading.piece (-1) ∧
        LinearMap.IsHomogeneous sB BB.grading.piece BB.grading.piece (-1) ∧
        AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential ∧
        LinearMap.id - g₁ ∘ₗ f.linearPart =
          AA.differential ∘ₗ sA + sA ∘ₗ AA.differential ∧
        LinearMap.id - f.linearPart ∘ₗ g₁ =
          BB.differential ∘ₗ sB + sB ∘ₗ BB.differential := by
  set cA := AA.cohomologyContraction
  set cB := BB.cohomologyContraction
  set e := hf.cohomologyLinearEquiv
  set f₁ := f.linearPart
  have hf₁_comm : BB.differential ∘ₗ f₁ = f₁ ∘ₗ AA.differential := differential_comp_linearPart f
  have hcomp : cB.proj ∘ₗ f₁ ∘ₗ cA.incl = e.toLinearMap := LinearMap.ext fun x ↦ by
    have hx : cA.incl x ∈ AA.cycles := AA.cohomologyContraction_incl_mem_cycles x
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      BB.cohomologyContraction_proj_of_mem_cycles (f.linearPart_mem_cycles hx),
      ← f.cohomologyMap_cohomologyClass hx, AA.cohomologyClass_cohomologyContraction_incl,
      LinearEquiv.coe_coe, hf.cohomologyLinearEquiv_apply]
  have he_symm_deg : LinearMap.IsHomogeneous e.symm.toLinearMap
      BB.cohomologyGrading.piece AA.cohomologyGrading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hy ↦ by
      rw [add_zero, LinearEquiv.coe_coe, ← hf.cohomologyMapInv_apply]
      exact hf.cohomologyMapInv_mem_cohomologyGrading_piece hy
  set g₁ : B →ₗ[K] A := cA.incl ∘ₗ e.symm.toLinearMap ∘ₗ cB.proj
  have hg₁_deg : LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0 := by
    simpa only [add_zero] using AA.isHomogeneous_cohomologyContraction_incl.comp
      (he_symm_deg.comp BB.isHomogeneous_cohomologyContraction_proj)
  have hdA_incl : AA.differential ∘ₗ cA.incl = 0 := by
    simpa only [LinearMap.comp_zero] using cA.dM_comp_incl
  have hproj_dB : cB.proj ∘ₗ BB.differential = 0 := by
    simpa only [LinearMap.zero_comp] using cB.proj_comp_dM
  have hg₁_comm : AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential := LinearMap.ext fun b ↦ by
    dsimp only [g₁]
    have h1 := LinearMap.congr_fun hdA_incl (e.symm (cB.proj b))
    have h2 := LinearMap.congr_fun hproj_dB b
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe] at h1 h2 ⊢
    rw [h1, h2, map_zero, map_zero]
  set rA := LinearMap.id - g₁ ∘ₗ f₁
  set rB := LinearMap.id - f₁ ∘ₗ g₁
  have hrA_deg : LinearMap.IsHomogeneous rA AA.grading.piece AA.grading.piece 0 := by
    refine (LinearMap.isHomogeneous_id _).sub ?_
    simpa only [add_zero] using hg₁_deg.comp f.isHomogeneous_linearPart
  have hrB_deg : LinearMap.IsHomogeneous rB BB.grading.piece BB.grading.piece 0 := by
    refine (LinearMap.isHomogeneous_id _).sub ?_
    simpa only [add_zero] using f.isHomogeneous_linearPart.comp hg₁_deg
  have hrA_comm : AA.differential ∘ₗ rA = rA ∘ₗ AA.differential := LinearMap.ext fun a ↦ by
    dsimp only [rA]
    have h1 := LinearMap.congr_fun hf₁_comm a
    have h2 := LinearMap.congr_fun hg₁_comm (f₁ a)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1 h2 ⊢
    rw [map_sub, h2, h1]
  have hrB_comm : BB.differential ∘ₗ rB = rB ∘ₗ BB.differential := LinearMap.ext fun b ↦ by
    dsimp only [rB]
    have h1 := LinearMap.congr_fun hg₁_comm b
    have h2 := LinearMap.congr_fun hf₁_comm (g₁ b)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1 h2 ⊢
    rw [map_sub, h2, h1]
  have hrA_incl : rA ∘ₗ cA.incl = 0 := LinearMap.ext fun x ↦ by
    have hx : cB.proj (f₁ (cA.incl x)) = e x := LinearMap.congr_fun hcomp x
    rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hx,
      LinearEquiv.coe_coe, e.symm_apply_apply, sub_self]
  have hproj_rB : cB.proj ∘ₗ rB = 0 := LinearMap.ext fun y ↦ by
    have hy : cB.proj (f₁ (cA.incl (e.symm (cB.proj y)))) = cB.proj y := by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
        (LinearMap.congr_fun hcomp (e.symm (cB.proj y))).trans (e.apply_symm_apply (cB.proj y))
    rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.sub_apply, map_sub,
      LinearMap.id_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, hy, sub_self]
  refine ⟨g₁, rA ∘ₗ cA.homotopy, cB.homotopy ∘ₗ rB, hg₁_deg,
    by simpa only [add_zero] using hrA_deg.comp AA.isHomogeneous_cohomologyContraction_homotopy,
    by simpa only [zero_add] using BB.isHomogeneous_cohomologyContraction_homotopy.comp hrB_deg,
    hg₁_comm, ?_, ?_⟩
  · refine LinearMap.ext fun a ↦ ?_
    have h1 := congrArg rA (LinearMap.congr_fun cA.dM_comp_homotopy_add_homotopy_comp_dM a)
    have h2 := LinearMap.congr_fun hrA_incl (cA.proj a)
    have h3 := LinearMap.congr_fun hrA_comm (cA.homotopy a)
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, map_add, map_sub] at h1 h2 h3 ⊢
    rw [h2, sub_zero, ← h3] at h1
    exact h1.symm
  · refine LinearMap.ext fun b ↦ ?_
    have h1 := LinearMap.congr_fun cB.dM_comp_homotopy_add_homotopy_comp_dM (rB b)
    have h2 := LinearMap.congr_fun hproj_rB b
    have h3 := LinearMap.congr_fun hrB_comm b
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply] at h1 h2 h3 ⊢
    rw [h2, map_zero, sub_zero, h3] at h1
    exact h1.symm

/-- **Existence of an `A∞` homotopy inverse over a field.**  Every `A∞` quasi-isomorphism over a
field admits a two-sided `A∞` homotopy inverse. -/
theorem IsQuasiIso.exists_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    ∃ g : AInfinityHom BB AA,
      Nonempty (Homotopy (AInfinityHom.id AA) (g.comp f)) ∧
        Nonempty (Homotopy (AInfinityHom.id BB) (f.comp g)) := by
  obtain ⟨_, _, _, hg₁_deg, hsA_deg, hsB_deg, hg₁, hsA, hsB⟩ := hf.exists_chainHomotopyEquiv
  obtain ⟨g, -, hL, hR⟩ :=
    exists_homotopyInverse_of_chainHomotopyEquiv f hg₁_deg hsA_deg hsB_deg hg₁ hsA hsB
  exact ⟨g, hL, hR⟩

/-- **Every `A∞` quasi-isomorphism over a field is an `A∞` homotopy equivalence.** -/
theorem IsQuasiIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.IsHomotopyEquiv :=
  hf.exists_homotopyInverse

/-- **Over a field, an `A∞` morphism is a homotopy equivalence if and only if it is a
quasi-isomorphism.** -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end Field

end AInfinityHom

end TauCeti
