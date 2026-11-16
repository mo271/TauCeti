/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
public import TauCeti.LinearAlgebra.TensorCoalgebra.Homotopy

/-!
# The homotopy relation and homotopy equivalences of A-infinity morphisms

For `A∞` morphisms `f g : A ⟶ B`, a homotopy `Homotopy f g` is an odd `(F, G)`-coderivation `H` of
degree `-1` between the reduced bar constructions satisfying `F - G = b_B ∘ H + H ∘ b_A`.  Because
the co-Leibniz rule depends on both endpoints `F` and `G`, neither `-H` nor the sum `H₁ + H₂` of
composable homotopies satisfies the co-Leibniz rule on the nose.  Using the second-order coalgebra
homotopy operators `TauCeti.ReducedTensorWords.gradedCoderivAlongSymm` and
`TauCeti.ReducedTensorWords.gradedCoderivAlongTrans`, this file equips `AInfinityHom.Homotopy` with
symmetry, transitivity, and horizontal composition, packages the resulting propositional equivalence
relation `TauCeti.AInfinityHom.Homotopic`, and defines `A∞` homotopy equivalences
(`TauCeti.AInfinityHom.IsHomotopyEquiv`).

On single letters the degree-`(-2)` commutator corrections vanish, so the arity-one components of
`h.symm` and `h₁.trans h₂` are simply `-h.linearHomotopy` and `h₁.linearHomotopy +
h₂.linearHomotopy`.  Consequently `Homotopic` is a congruence for composition of `A∞` morphisms,
descends to equality on cohomology, and gives `IsHomotopyEquiv` closure under composition and the
two-out-of-three property.

## Main definitions

* `TauCeti.AInfinityHom.Homotopy.symm`: symmetry of homotopies of `A∞` morphisms.
* `TauCeti.AInfinityHom.Homotopy.trans`: transitivity of homotopies of `A∞` morphisms.
* `TauCeti.AInfinityHom.Homotopy.comp`: horizontal composition of homotopies across
  `AInfinityHom.comp`.
* `TauCeti.AInfinityHom.Homotopic`: the propositional homotopy relation `Nonempty (Homotopy f g)`.
* `TauCeti.AInfinityHom.Homotopic.setoid`: the `Setoid` of `A∞` morphisms up to homotopy.
* `TauCeti.AInfinityHom.IsHomotopyEquiv`: an `A∞` morphism admitting a two-sided inverse up to
  homotopy.

## Main results

* `TauCeti.AInfinityHom.Homotopy.linearHomotopy_symm` and
  `TauCeti.AInfinityHom.Homotopy.linearHomotopy_trans`: on single letters, `symm` negates and
  `trans` adds the arity-one chain homotopies.
* `TauCeti.AInfinityHom.Homotopic.equivalence`: `Homotopic` is an equivalence relation.
* `TauCeti.AInfinityHom.Homotopic.compLeft`, `TauCeti.AInfinityHom.Homotopic.compRight`, and
  `TauCeti.AInfinityHom.Homotopic.comp`: composition of `A∞` morphisms respects `Homotopic`.
* `TauCeti.AInfinityHom.Homotopic.cohomologyMap_eq` and
  `TauCeti.AInfinityHom.Homotopic.isQuasiIso_iff`: homotopic morphisms induce the same map on
  cohomology and are quasi-isomorphisms together.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.comp`, `TauCeti.AInfinityHom.IsHomotopyEquiv.of_precomp`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv.of_postcomp`, `TauCeti.AInfinityHom.IsIso.isHomotopyEquiv`,
  and `TauCeti.AInfinityHom.IsHomotopyEquiv.isQuasiIso`: closure, two-out-of-three, and comparison
  with strict-bar isomorphisms and quasi-isomorphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Section 1.3.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology Homotopy Appl. 5 (2003), Section 2.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

namespace Homotopy

/-! ### Arity-one components of identity and whiskering -/

/-- The zero homotopy has zero arity-one component. -/
@[simp]
theorem linearHomotopy_refl (f : AInfinityHom AA BB) : (refl f).linearHomotopy = 0 := by
  ext a
  simp only [linearHomotopy_apply, taylor_refl, LinearMap.zero_apply]

/-- Postcomposing a homotopy with a morphism `k` postcomposes its arity-one component with
`k.linearPart`. -/
@[simp]
theorem linearHomotopy_compRight {f g : AInfinityHom AA BB} (h : Homotopy f g)
    (k : AInfinityHom BB CC) :
    (h.compRight k).linearHomotopy = k.linearPart ∘ₗ h.linearHomotopy := by
  ext a
  simp only [linearHomotopy_apply, taylor_compRight, LinearMap.comp_apply, barHomotopy_ofLetter,
    AInfinityHom.linearPart_apply]

/-- Precomposing a homotopy with a morphism `k` precomposes its arity-one component with
`k.linearPart`. -/
@[simp]
theorem linearHomotopy_compLeft {f g : AInfinityHom AA BB} (h : Homotopy f g)
    (k : AInfinityHom CC AA) :
    (h.compLeft k).linearHomotopy = h.linearHomotopy ∘ₗ k.linearPart := by
  ext a
  simp only [linearHomotopy_apply, taylor_compLeft, LinearMap.comp_apply, barMap_ofLetter]

/-! ### Symmetry and transitivity of homotopies -/

/-- The inverse homotopy from `g` to `f` built from a homotopy `h : Homotopy f g` via the
second-order coalgebra homotopy operator `gradedCoderivAlongSymm`. -/
noncomputable def symm {f g : AInfinityHom AA BB} (h : Homotopy f g) : Homotopy g f where
  barHomotopy := ReducedTensorWords.gradedCoderivAlongSymm (AA.grading.shift 1)
    AA.barDifferential BB.barDifferential f.barMap h.barHomotopy
  isGradedCoderivationAlong_barHomotopy :=
    ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlongSymm
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential AA.barDifferential_sq
      BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential BB.barDifferential_sq
      f.isCoalgHom_barMap f.isHomogeneous_barMap f.barDifferential_comp_barMap
      h.isGradedCoderivationAlong_barHomotopy h.isHomogeneous_barHomotopy h.barMap_sub_barMap
  isHomogeneous_barHomotopy :=
    ReducedTensorWords.isHomogeneous_gradedCoderivAlongSymm
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential
      BB.isHomogeneous_barDifferential f.isHomogeneous_barMap h.isHomogeneous_barHomotopy
  barMap_sub_barMap :=
    ReducedTensorWords.sub_eq_comp_add_comp_gradedCoderivAlongSymm
      AA.barDifferential_sq BB.barDifferential_sq h.barMap_sub_barMap

/-- The underlying bar coderivation of `h.symm` is `gradedCoderivAlongSymm`. -/
@[simp]
theorem barHomotopy_symm {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    h.symm.barHomotopy = ReducedTensorWords.gradedCoderivAlongSymm (AA.grading.shift 1)
      AA.barDifferential BB.barDifferential f.barMap h.barHomotopy := (rfl)

/-- On single letters, the inverse homotopy negates the arity-one chain homotopy. -/
@[simp]
theorem linearHomotopy_symm {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    h.symm.linearHomotopy = -h.linearHomotopy := by
  ext a
  have hcomp := LinearMap.congr_fun
    (ReducedTensorWords.gradedCoderivAlongSymm_comp_ofLetter
      (bN := BB.barDifferential) (F := f.barMap) (D := h.barHomotopy)
      AA.isGradedCoderivation_barDifferential) a
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, barHomotopy_ofLetter] at hcomp
  rw [linearHomotopy_apply, taylor_def, LinearMap.comp_apply, barHomotopy_symm, hcomp, map_neg,
    ReducedTensorWords.letter_ofLetter, LinearMap.neg_apply]

/-- The composite homotopy from `f` to `k` built from `h₁ : Homotopy f g` and `h₂ : Homotopy g k`
via the second-order coalgebra homotopy operator `gradedCoderivAlongTrans`. -/
noncomputable def trans {f g k : AInfinityHom AA BB} (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    Homotopy f k where
  barHomotopy := ReducedTensorWords.gradedCoderivAlongTrans (AA.grading.shift 1)
    AA.barDifferential BB.barDifferential f.barMap h₁.barHomotopy h₂.barHomotopy
  isGradedCoderivationAlong_barHomotopy :=
    ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlongTrans
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential
      BB.isGradedCoderivation_barDifferential f.isCoalgHom_barMap f.isHomogeneous_barMap
      f.barDifferential_comp_barMap k.barDifferential_comp_barMap
      h₁.isGradedCoderivationAlong_barHomotopy h₁.isHomogeneous_barHomotopy h₁.barMap_sub_barMap
      h₂.isGradedCoderivationAlong_barHomotopy h₂.isHomogeneous_barHomotopy h₂.barMap_sub_barMap
  isHomogeneous_barHomotopy :=
    ReducedTensorWords.isHomogeneous_gradedCoderivAlongTrans
      AA.isHomogeneous_barDifferential BB.isHomogeneous_barDifferential f.isHomogeneous_barMap
      h₁.isHomogeneous_barHomotopy h₂.isHomogeneous_barHomotopy
  barMap_sub_barMap :=
    ReducedTensorWords.sub_eq_comp_add_comp_gradedCoderivAlongTrans
      AA.barDifferential_sq BB.barDifferential_sq h₁.barMap_sub_barMap h₂.barMap_sub_barMap

/-- The underlying bar coderivation of `h₁.trans h₂` is `gradedCoderivAlongTrans`. -/
@[simp]
theorem barHomotopy_trans {f g k : AInfinityHom AA BB}
    (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    (h₁.trans h₂).barHomotopy = ReducedTensorWords.gradedCoderivAlongTrans (AA.grading.shift 1)
      AA.barDifferential BB.barDifferential f.barMap h₁.barHomotopy h₂.barHomotopy := (rfl)

/-- On single letters, transitivity of homotopies adds the arity-one chain homotopies. -/
@[simp]
theorem linearHomotopy_trans {f g k : AInfinityHom AA BB}
    (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    (h₁.trans h₂).linearHomotopy = h₁.linearHomotopy + h₂.linearHomotopy := by
  ext a
  have hcomp := LinearMap.congr_fun
    (ReducedTensorWords.gradedCoderivAlongTrans_comp_ofLetter
      (bN := BB.barDifferential) (F := f.barMap) (H₁ := h₁.barHomotopy) (H₂ := h₂.barHomotopy)
      AA.isGradedCoderivation_barDifferential) a
  simp only [LinearMap.comp_apply, LinearMap.add_apply, barHomotopy_ofLetter] at hcomp
  rw [linearHomotopy_apply, taylor_def, LinearMap.comp_apply, barHomotopy_trans, hcomp, map_add,
    ReducedTensorWords.letter_ofLetter, ReducedTensorWords.letter_ofLetter, LinearMap.add_apply]

/-- Horizontal composition of homotopies across `AInfinityHom.comp`: combines `hf.compRight g₀`
from `g₀ ∘ f₀` to `g₀ ∘ f₁` with `hg.compLeft f₁` from `g₀ ∘ f₁` to `g₁ ∘ f₁`. -/
noncomputable def comp {g₀ g₁ : AInfinityHom BB CC} {f₀ f₁ : AInfinityHom AA BB}
    (hg : Homotopy g₀ g₁) (hf : Homotopy f₀ f₁) : Homotopy (g₀.comp f₀) (g₁.comp f₁) :=
  (hf.compRight g₀).trans (hg.compLeft f₁)

/-- On single letters, horizontal composition of homotopies acts by `g₀₁ h_f + h_g f₁₁`. -/
@[simp]
theorem linearHomotopy_comp {g₀ g₁ : AInfinityHom BB CC} {f₀ f₁ : AInfinityHom AA BB}
    (hg : Homotopy g₀ g₁) (hf : Homotopy f₀ f₁) :
    (hg.comp hf).linearHomotopy =
      g₀.linearPart ∘ₗ hf.linearHomotopy + hg.linearHomotopy ∘ₗ f₁.linearPart := by
  rw [comp, linearHomotopy_trans, linearHomotopy_compRight, linearHomotopy_compLeft]

end Homotopy

/-! ### The propositional homotopy relation -/

/-- Two `A∞` morphisms `f` and `g` are **homotopic** when there exists a `Homotopy f g`. -/
def Homotopic (f g : AInfinityHom AA BB) : Prop :=
  Nonempty (Homotopy f g)

/-- Two `A∞` morphisms are homotopic exactly when the type of homotopies between them is
nonempty. -/
theorem homotopic_def (f g : AInfinityHom AA BB) :
    f.Homotopic g ↔ Nonempty (Homotopy f g) :=
  Iff.rfl

/-- Any explicit `Homotopy f g` witnesses `f.Homotopic g`. -/
theorem Homotopy.homotopic {f g : AInfinityHom AA BB} (h : Homotopy f g) : f.Homotopic g :=
  ⟨h⟩

namespace Homotopic

/-- Every `A∞` morphism is homotopic to itself via the zero homotopy. -/
@[refl]
theorem refl (f : AInfinityHom AA BB) : f.Homotopic f :=
  ⟨Homotopy.refl f⟩

/-- Equal `A∞` morphisms are homotopic. -/
theorem of_eq {f g : AInfinityHom AA BB} (h : f = g) : f.Homotopic g :=
  h ▸ refl f

/-- Homotopy of `A∞` morphisms is symmetric. -/
@[symm]
theorem symm {f g : AInfinityHom AA BB} (h : f.Homotopic g) : g.Homotopic f :=
  h.map Homotopy.symm

/-- Homotopy of `A∞` morphisms is transitive. -/
@[trans]
theorem trans {f g k : AInfinityHom AA BB} (h₁ : f.Homotopic g) (h₂ : g.Homotopic k) :
    f.Homotopic k :=
  h₁.map2 Homotopy.trans h₂

/-- `AInfinityHom.Homotopic` is an equivalence relation. -/
theorem equivalence (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) :
    Equivalence (Homotopic (AA := AA) (BB := BB)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

instance : IsEquiv (AInfinityHom AA BB) Homotopic where
  refl := refl
  symm _ _ := symm
  trans _ _ _ := trans

/-- The `Setoid` of `A∞` morphisms from `AA` to `BB` modulo homotopy. -/
def setoid (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) :
    Setoid (AInfinityHom AA BB) where
  r := Homotopic
  iseqv := equivalence AA BB

/-- Two `A∞` morphisms are related by `Homotopic.setoid` if and only if they are homotopic. -/
@[simp]
theorem setoid_r (f g : AInfinityHom AA BB) :
    (setoid AA BB).r f g ↔ f.Homotopic g :=
  Iff.rfl

/-- Postcomposing homotopic `A∞` morphisms with `k` yields homotopic morphisms. -/
theorem compRight {f g : AInfinityHom AA BB} (h : f.Homotopic g) (k : AInfinityHom BB CC) :
    (k.comp f).Homotopic (k.comp g) :=
  h.map fun D ↦ D.compRight k

/-- Precomposing homotopic `A∞` morphisms with `k` yields homotopic morphisms. -/
theorem compLeft {f g : AInfinityHom AA BB} (h : f.Homotopic g) (k : AInfinityHom CC AA) :
    (f.comp k).Homotopic (g.comp k) :=
  h.map fun D ↦ D.compLeft k

/-- Composition of `A∞` morphisms respects homotopy in both arguments. -/
theorem comp {g₀ g₁ : AInfinityHom BB CC} {f₀ f₁ : AInfinityHom AA BB}
    (hg : g₀.Homotopic g₁) (hf : f₀.Homotopic f₁) :
    (g₀.comp f₀).Homotopic (g₁.comp f₁) :=
  hg.map2 Homotopy.comp hf

/-- Homotopic `A∞` morphisms induce the same morphism of cohomology algebras. -/
theorem cohomologyMap_eq {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.cohomologyMap = g.cohomologyMap := by
  obtain ⟨D⟩ := h
  exact D.cohomologyMap_eq

/-- Homotopic `A∞` morphisms induce the same strict morphism of cohomology `A∞` algebras. -/
theorem cohomologyStrictHom_eq {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.cohomologyStrictHom = g.cohomologyStrictHom := by
  ext c
  simp only [coe_cohomologyStrictHom, h.cohomologyMap_eq]

/-- Homotopic `A∞` morphisms are quasi-isomorphisms together. -/
theorem isQuasiIso_iff {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.IsQuasiIso ↔ g.IsQuasiIso := by
  obtain ⟨D⟩ := h
  exact D.isQuasiIso_iff

end Homotopic

/-! ### Homotopy equivalences of `A∞` algebras -/

/-- An `A∞` morphism `f : AA ⟶ BB` is a **homotopy equivalence** when there exists an `A∞`
morphism `g : BB ⟶ AA` such that `g ∘ f` is homotopic to `id AA` and `f ∘ g` is homotopic to
`id BB`. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB)

/-- Unfolding characterization of `AInfinityHom.IsHomotopyEquiv`. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ g : AInfinityHom BB AA,
      (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB) :=
  Iff.rfl

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA, Homotopic.of_eq (comp_id _), Homotopic.of_eq (comp_id _)⟩

/-- Homotopy equivalences of `A∞` algebras are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  obtain ⟨f', hf₁, hf₂⟩ := hf
  refine ⟨f'.comp g', ?_, ?_⟩
  · have h1 : ((f'.comp g').comp (g.comp f)).Homotopic (f'.comp f) := by
      rw [comp_assoc, ← comp_assoc g']
      exact ((hg₁.compLeft f).compRight f').trans (Homotopic.of_eq (by rw [id_comp]))
    exact h1.trans hf₁
  · have h1 : ((g.comp f).comp (f'.comp g')).Homotopic (g.comp g') := by
      rw [comp_assoc, ← comp_assoc f]
      exact ((hf₂.compLeft g').compRight g).trans (Homotopic.of_eq (by rw [id_comp]))
    exact h1.trans hg₂

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopic.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    exact ⟨k, (h.symm.compRight k).trans hk₁, (h.symm.compLeft k).trans hk₂⟩
  · rintro ⟨k, hk₁, hk₂⟩
    exact ⟨k, (h.compRight k).trans hk₁, (h.compLeft k).trans hk₂⟩

/-- Two out of three for homotopy equivalences: if `f` and `g ∘ f` are homotopy equivalences, then
so is `g`. -/
theorem IsHomotopyEquiv.of_precomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : g.IsHomotopyEquiv := by
  obtain ⟨f', _, hf₂⟩ := hf
  obtain ⟨k, hk₁, hk₂⟩ := hgf
  have hgk : (g.comp (f.comp k)).Homotopic (AInfinityHom.id CC) := by
    rw [← comp_assoc]
    exact hk₂
  have hkg : ((f.comp k).comp g).Homotopic (AInfinityHom.id BB) := by
    have h1 : ((f.comp k).comp g).Homotopic (((f.comp k).comp g).comp (f.comp f')) :=
      (Homotopic.of_eq (comp_id _).symm).trans (hf₂.symm.compRight _)
    have h2 : (((f.comp k).comp g).comp (f.comp f')).Homotopic (f.comp f') := by
      have hassoc :
          ((f.comp k).comp g).comp (f.comp f') = f.comp ((k.comp (g.comp f)).comp f') := by
        simp only [comp_assoc]
      rw [hassoc]
      exact ((hk₁.compLeft f').compRight f).trans (Homotopic.of_eq (by rw [id_comp]))
    exact (h1.trans h2).trans hf₂
  exact ⟨f.comp k, hkg, hgk⟩

/-- Two out of three for homotopy equivalences: if `g` and `g ∘ f` are homotopy equivalences, then
so is `f`. -/
theorem IsHomotopyEquiv.of_postcomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : f.IsHomotopyEquiv := by
  obtain ⟨g', hg₁, _⟩ := hg
  obtain ⟨k, hk₁, hk₂⟩ := hgf
  have hkf : ((k.comp g).comp f).Homotopic (AInfinityHom.id AA) := by
    rw [comp_assoc]
    exact hk₁
  have hfk : (f.comp (k.comp g)).Homotopic (AInfinityHom.id BB) := by
    have h1 : (f.comp (k.comp g)).Homotopic ((g'.comp g).comp (f.comp (k.comp g))) :=
      (Homotopic.of_eq (id_comp _).symm).trans (hg₁.symm.compLeft _)
    have h2 : ((g'.comp g).comp (f.comp (k.comp g))).Homotopic (g'.comp g) := by
      have hassoc :
          (g'.comp g).comp (f.comp (k.comp g)) = g'.comp (((g.comp f).comp k).comp g) := by
        simp only [comp_assoc]
      rw [hassoc]
      exact ((hk₂.compLeft g).compRight g').trans (Homotopic.of_eq (by rw [id_comp]))
    exact (h1.trans h2).trans hg₁
  exact ⟨k.comp g, hkf, hfk⟩

/-- Every `A∞` isomorphism is an `A∞` homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv := by
  rw [isIso_def] at hf
  obtain ⟨g, hg₁, hg₂⟩ := hf
  exact ⟨g, Homotopic.of_eq hg₁, Homotopic.of_eq hg₂⟩

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨g, hg₁, hg₂⟩ := hf
  rw [isQuasiIso_def]
  have h1 := hg₁.cohomologyMap_eq
  have h2 := hg₂.cohomologyMap_eq
  rw [cohomologyMap_comp, cohomologyMap_id] at h1 h2
  exact Function.bijective_iff_has_inverse.2
    ⟨g.cohomologyMap, fun x ↦ DFunLike.congr_fun h1 x, fun y ↦ DFunLike.congr_fun h2 y⟩

end AInfinityHom

end TauCeti
