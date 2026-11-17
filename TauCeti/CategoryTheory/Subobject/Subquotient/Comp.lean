/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import TauCeti.CategoryTheory.Subobject.Subquotient.Basic
import TauCeti.CategoryTheory.Subobject.Image
import TauCeti.CategoryTheory.Subobject.Pullback

/-!
# Composition, functoriality, and homology subquotient presentations

Building on `TauCeti.CategoryTheory.Subobject.Subquotient.Basic`, this file develops:

* associative composition `TauCeti.SubquotientPresentation.comp` of nested subquotient
  presentations with unit `refl`;
* functoriality `TauCeti.SubquotientPresentation.map` under ambient morphisms `A ⟶ A'` preserving
  the upper and lower subobjects, together with the canonical comparison isomorphism
  `TauCeti.SubquotientPresentation.isoOfEq` for presentations with equal lower and upper subobjects;
* the canonical homology presentation `TauCeti.SubquotientPresentation.ofShortComplex` of
  `S.homology` as `kernelSubobject S.g / imageSubobject S.f` inside `S.X₂`.

## Main definitions

* `TauCeti.SubquotientPresentation.comp`: composition of nested subquotient presentations.
* `TauCeti.SubquotientPresentation.map`: morphism induced on subquotients by a morphism of ambient
  objects preserving `upper` and `lower`.
* `TauCeti.SubquotientPresentation.isoOfEq`: canonical isomorphism between two presentations with
  the same lower and upper subobjects.
* `TauCeti.SubquotientPresentation.ofShortComplex`: the canonical presentation of `S.homology` as
  `kernelSubobject S.g / imageSubobject S.f` inside `S.X₂`.

## References

* [The Stacks Project, Tag 011N](https://stacks.math.columbia.edu/tag/011N)
* E. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg systems*,
  arXiv:2408.05989 (2024), Lemma 2.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C]

namespace SubquotientPresentation

section Abelian

variable [Abelian C]

section Comp

variable {A X Y : C} (p : SubquotientPresentation A X) (q : SubquotientPresentation X Y)

private lemma ofLE_comp_liftTo_comp_π :
    Subobject.ofLE (p.lift q.lower) (p.lift q.upper) (p.lift_monotone q.le) ≫
      (p.liftTo q.upper ≫ q.π) = 0 := by
  rw [ofLE_comp_liftTo_assoc p q.le, q.ofLE_comp_π, comp_zero]

private lemma isIso_cokernelDesc_comp :
    IsIso (cokernel.desc (Subobject.ofLE (p.lift q.lower) (p.lift q.upper) (p.lift_monotone q.le))
      (p.liftTo q.upper ≫ q.π) (ofLE_comp_liftTo_comp_π p q)) := by
  let ι := Subobject.ofLE (p.lift q.lower) (p.lift q.upper) (p.lift_monotone q.le)
  let φ : (p.lift q.upper : C) ⟶ Y := p.liftTo q.upper ≫ q.π
  let g : cokernel ι ⟶ Y := cokernel.desc ι φ (ofLE_comp_liftTo_comp_π p q)
  have hEpi : Epi g := by
    have : Epi (cokernel.π ι ≫ g) := by
      simpa only [g, cokernel.π_desc] using epi_comp (p.liftTo q.upper) q.π
    exact epi_of_epi (cokernel.π ι) g
  have hMono : Mono g := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro W t ht
    -- Pull `t` back along `cokernel.π ι` to test vanishing at `(p.lift q.upper : C)`.
    let e₁ : Limits.pullback (cokernel.π ι) t ⟶ (p.lift q.upper : C) :=
      Limits.pullback.fst (cokernel.π ι) t
    let e₂ : Limits.pullback (cokernel.π ι) t ⟶ W := Limits.pullback.snd (cokernel.π ι) t
    have hcond : e₁ ≫ cokernel.π ι = e₂ ≫ t := Limits.pullback.condition
    have : Epi e₂ := Abelian.epi_pullback_of_epi_f (cokernel.π ι) t
    have hφ0 : (e₁ ≫ p.liftTo q.upper) ≫ q.π = 0 := by
      have : e₁ ≫ cokernel.π ι ≫ g = 0 := by
        rw [← Category.assoc, hcond, Category.assoc, ht, comp_zero]
      simpa only [g, cokernel.π_desc, Category.assoc] using this
    have hfacLower : q.lower.Factors (e₁ ≫ p.liftTo q.upper ≫ q.upper.arrow) := by
      have hker : (kernelSubobject q.π).Factors (e₁ ≫ p.liftTo q.upper) :=
        kernelSubobject_factors q.π _ hφ0
      rw [q.kernelSubobject_π] at hker
      let u := (Subobject.mk (Subobject.ofLE q.lower q.upper q.le)).factorThru
        (e₁ ≫ p.liftTo q.upper) hker
      have hu : (u ≫ (Subobject.underlyingIso (Subobject.ofLE q.lower q.upper q.le)).hom) ≫
          q.lower.arrow = e₁ ≫ p.liftTo q.upper ≫ q.upper.arrow := by
        rw [Category.assoc, ← Subobject.ofLE_arrow q.le,
          Subobject.underlyingIso_hom_comp_eq_mk_assoc]
        simp [u, Category.assoc]
      exact hu ▸ Subobject.factors_comp_arrow _
    have hfacLift : (p.lift q.lower).Factors (e₁ ≫ (p.lift q.upper).arrow) := by
      rw [p.factors_lift_iff]
      have hf : p.upper.Factors (e₁ ≫ (p.lift q.upper).arrow) := by
        have h : (e₁ ≫ Subobject.ofLE (p.lift q.upper) p.upper (p.lift_le_upper q.upper)) ≫
            p.upper.arrow = e₁ ≫ (p.lift q.upper).arrow := by
          simp
        exact h ▸ Subobject.factors_comp_arrow _
      refine ⟨hf, ?_⟩
      have hft : p.upper.factorThru (e₁ ≫ (p.lift q.upper).arrow) hf =
          e₁ ≫ Subobject.ofLE (p.lift q.upper) p.upper (p.lift_le_upper q.upper) := by
        rw [← cancel_mono p.upper.arrow]
        simp
      rw [hft, Category.assoc, ← p.liftTo_arrow q.upper]
      exact hfacLower
    let v := (p.lift q.lower).factorThru (e₁ ≫ (p.lift q.upper).arrow) hfacLift
    have he₁ : v ≫ ι = e₁ := by
      rw [← cancel_mono (p.lift q.upper).arrow, Category.assoc, Subobject.ofLE_arrow]
      exact (p.lift q.lower).factorThru_arrow _ hfacLift
    have he₂t : e₂ ≫ t = 0 := by
      rw [← hcond, ← he₁, Category.assoc, cokernel.condition, comp_zero]
    exact (cancel_epi e₂).1 (by simpa using he₂t)
  exact isIso_of_mono_of_epi g

/-- The canonical isomorphism `cokernel (ofLE (p.lift q.lower) (p.lift q.upper)) ≅ Y` for the
composite of two subquotient presentations. -/
noncomputable def compIso :
    cokernel (Subobject.ofLE (p.lift q.lower) (p.lift q.upper) (p.lift_monotone q.le)) ≅ Y :=
  have := isIso_cokernelDesc_comp p q
  asIso (cokernel.desc (Subobject.ofLE (p.lift q.lower) (p.lift q.upper) (p.lift_monotone q.le))
    (p.liftTo q.upper ≫ q.π) (ofLE_comp_liftTo_comp_π p q))

/-- Compose a subquotient presentation `p` of `X` in `A` with a subquotient presentation `q` of `Y`
in `X`, producing a presentation of `Y` in `A` with lower `p.lift q.lower` and upper
`p.lift q.upper`. -/
noncomputable abbrev comp : SubquotientPresentation A Y where
  lower := p.lift q.lower
  upper := p.lift q.upper
  le := p.lift_monotone q.le
  iso := compIso p q

@[simp, reassoc]
lemma comp_π : (p.comp q).π = p.liftTo q.upper ≫ q.π := by
  dsimp [π, comp, compIso]
  exact cokernel.π_desc _ _ _

@[simp]
lemma comp_lift (K : Subobject Y) : (p.comp q).lift K = p.lift (q.lift K) := by
  refine le_antisymm ?_ ?_
  · have hfac : (p.lift (q.lift K)).Factors ((p.comp q).lift K).arrow := by
      have hself : ((p.comp q).lift K).Factors ((p.comp q).lift K).arrow := Subobject.factors_self _
      rw [(p.comp q).factors_lift_iff] at hself
      obtain ⟨hqu, hK⟩ := hself
      rw [p.factors_lift_iff]
      have hpu : p.upper.Factors ((p.comp q).lift K).arrow :=
        Subobject.factors_of_le _ (p.lift_le_upper q.upper) hqu
      refine ⟨hpu, ?_⟩
      rw [q.factors_lift_iff]
      have hft : p.upper.factorThru ((p.comp q).lift K).arrow hpu =
          (p.lift q.upper).factorThru ((p.comp q).lift K).arrow hqu ≫
            Subobject.ofLE (p.lift q.upper) p.upper (p.lift_le_upper q.upper) := by
        rw [← cancel_mono p.upper.arrow]
        simp
      have hquX : q.upper.Factors (p.upper.factorThru ((p.comp q).lift K).arrow hpu ≫ p.π) := by
        have h : ((p.lift q.upper).factorThru ((p.comp q).lift K).arrow hqu ≫ p.liftTo q.upper) ≫
            q.upper.arrow = p.upper.factorThru ((p.comp q).lift K).arrow hpu ≫ p.π := by
          rw [Category.assoc, p.liftTo_arrow, ← Category.assoc, hft]
        exact h ▸ Subobject.factors_comp_arrow _
      refine ⟨hquX, ?_⟩
      have hft' : q.upper.factorThru (p.upper.factorThru ((p.comp q).lift K).arrow hpu ≫ p.π)
          hquX = (p.lift q.upper).factorThru ((p.comp q).lift K).arrow hqu ≫ p.liftTo q.upper := by
        rw [← cancel_mono q.upper.arrow]
        simp [hft]
      rw [hft', Category.assoc, ← comp_π]
      exact hK
    exact Subobject.le_of_comm ((p.lift (q.lift K)).factorThru _ hfac) (by simp)
  · have hfac : ((p.comp q).lift K).Factors (p.lift (q.lift K)).arrow := by
      have hself : (p.lift (q.lift K)).Factors (p.lift (q.lift K)).arrow := Subobject.factors_self _
      rw [p.factors_lift_iff] at hself
      obtain ⟨hpu, hqK⟩ := hself
      rw [q.factors_lift_iff] at hqK
      obtain ⟨hqu, hK⟩ := hqK
      rw [(p.comp q).factors_lift_iff]
      have hplqu : (p.comp q).upper.Factors (p.lift (q.lift K)).arrow :=
        (p.factors_lift_iff q.upper _).2 ⟨hpu, hqu⟩
      refine ⟨hplqu, ?_⟩
      have hft : (p.comp q).upper.factorThru (p.lift (q.lift K)).arrow hplqu ≫ p.liftTo q.upper =
          q.upper.factorThru (p.upper.factorThru (p.lift (q.lift K)).arrow hpu ≫ p.π) hqu := by
        rw [← cancel_mono q.upper.arrow]
        simp only [Category.assoc, p.liftTo_arrow, Subobject.factorThru_arrow]
        rw [← Category.assoc]
        congr 1
        rw [← cancel_mono p.upper.arrow]
        simp
      rw [comp_π, ← Category.assoc, hft]
      exact hK
    exact Subobject.le_of_comm (((p.comp q).lift K).factorThru _ hfac) (by simp)

@[simp]
lemma comp_transIso {Z : C} (e : Y ≅ Z) :
    p.comp (q.transIso e) = (p.comp q).transIso e := by
  refine ext rfl ?_
  rw [Subobject.isoOfEq_hom, Subobject.ofLE_refl, Category.id_comp, transIso_π, comp_π, comp_π,
    transIso_π, Category.assoc]

@[simp]
lemma refl_comp {A X : C} (p : SubquotientPresentation A X) : (refl A).comp p = p := by
  refine ext (refl_lift p.upper) ?_
  rw [comp_π]
  congr 1
  rw [← cancel_mono p.upper.arrow, liftTo_arrow, refl_π]
  simp

@[simp]
lemma comp_refl {A X : C} (p : SubquotientPresentation A X) : p.comp (refl X) = p := by
  refine ext p.lift_top ?_
  rw [comp_π, refl_π, p.liftTo_arrow]
  rfl

lemma comp_assoc {Z : C} (r : SubquotientPresentation Y Z) :
    (p.comp q).comp r = p.comp (q.comp r) := by
  refine ext (p.comp_lift q r.upper) ?_
  rw [comp_π, comp_π, comp_π, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono r.upper.arrow]
  simp only [Category.assoc, liftTo_arrow, comp_π]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono q.upper.arrow]
  simp only [Category.assoc, Subobject.ofLE_arrow, liftTo_arrow]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono p.upper.arrow]
  simp

end Comp

section Map

variable {A A' X X' : C}

/-- The restriction of `f : A ⟶ A'` to `(p.upper : C) ⟶ (p'.upper : C)` when
`p.upper ≤ (Subobject.pullback f).obj p'.upper`. -/
noncomputable def mapUpper (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper) :
    (p.upper : C) ⟶ (p'.upper : C) :=
  p'.upper.factorThru (p.upper.arrow ≫ f)
    ((pullback_factors_iff f p'.upper p.upper.arrow).1
      (Subobject.factors_of_le _ hZ (Subobject.factors_self _)))

@[reassoc (attr := simp)]
lemma mapUpper_arrow (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper) :
    p.mapUpper p' f hZ ≫ p'.upper.arrow = p.upper.arrow ≫ f :=
  p'.upper.factorThru_arrow _ _

/-- The morphism `X ⟶ X'` induced by a morphism `f : A ⟶ A'` mapping `p.upper` into `p'.upper`
and `p.lower` into `p'.lower`. -/
noncomputable def map (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower) : X ⟶ X' :=
  have hB' : p.lower ≤ (Subobject.pullback f).obj p'.lower :=
    (Subobject.existsPullbackAdj f).gc _ _ |>.1 hB
  let fLower : (p.lower : C) ⟶ (p'.lower : C) :=
    p'.lower.factorThru (p.lower.arrow ≫ f)
      ((pullback_factors_iff f p'.lower p.lower.arrow).1
        (Subobject.factors_of_le _ hB' (Subobject.factors_self _)))
  have hsq : Subobject.ofLE p.lower p.upper p.le ≫ p.mapUpper p' f hZ =
      fLower ≫ Subobject.ofLE p'.lower p'.upper p'.le := by
    rw [← cancel_mono p'.upper.arrow]
    simp [fLower]
  p.iso.inv ≫ cokernel.desc (Subobject.ofLE p.lower p.upper p.le) (p.mapUpper p' f hZ ≫ p'.π)
    (by rw [reassoc_of% hsq, p'.ofLE_comp_π, comp_zero])

@[reassoc (attr := simp)]
lemma π_map (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower) :
    p.π ≫ p.map p' f hZ hB = p.mapUpper p' f hZ ≫ p'.π := by
  simp [π, map]

/-- Uniqueness of the morphism induced on subquotients. -/
lemma map_eq_of_comm (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower)
    {u : (p.upper : C) ⟶ (p'.upper : C)} (hu : u ≫ p'.upper.arrow = p.upper.arrow ≫ f)
    {g : X ⟶ X'} (hg : p.π ≫ g = u ≫ p'.π) : p.map p' f hZ hB = g := by
  have hu' : u = p.mapUpper p' f hZ := by
    rw [← cancel_mono p'.upper.arrow, hu, mapUpper_arrow]
  exact (cancel_epi p.π).1 (by rw [π_map, hg, hu'])

@[simp]
lemma map_id (p : SubquotientPresentation A X)
    (hZ : p.upper ≤ (Subobject.pullback (𝟙 A)).obj p.upper)
    (hB : (Subobject.exists (𝟙 A)).obj p.lower ≤ p.lower) :
    p.map p (𝟙 A) hZ hB = 𝟙 X :=
  p.map_eq_of_comm p (𝟙 A) hZ hB (u := 𝟙 _) (by simp) (by simp)

lemma map_comp {A'' X'' : C} (p : SubquotientPresentation A X)
    (p' : SubquotientPresentation A' X') (p'' : SubquotientPresentation A'' X'')
    (f : A ⟶ A') (f' : A' ⟶ A'')
    (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower)
    (hZ' : p'.upper ≤ (Subobject.pullback f').obj p''.upper)
    (hB' : (Subobject.exists f').obj p'.lower ≤ p''.lower)
    (hZ'' : p.upper ≤ (Subobject.pullback (f ≫ f')).obj p''.upper)
    (hB'' : (Subobject.exists (f ≫ f')).obj p.lower ≤ p''.lower) :
    p.map p'' (f ≫ f') hZ'' hB'' = p.map p' f hZ hB ≫ p'.map p'' f' hZ' hB' :=
  p.map_eq_of_comm p'' (f ≫ f') hZ'' hB'' (u := p.mapUpper p' f hZ ≫ p'.mapUpper p'' f' hZ')
    (by simp [Category.assoc]) (by simp [Category.assoc])

@[simp]
lemma map_refl (f : A ⟶ A')
    (hZ : (refl A).upper ≤ (Subobject.pullback f).obj (refl A').upper)
    (hB : (Subobject.exists f).obj (refl A).lower ≤ (refl A').lower) :
    (refl A).map (refl A') f hZ hB = f :=
  (refl A).map_eq_of_comm (refl A') f hZ hB
    (u := (⊤ : Subobject A).arrow ≫ f ≫ inv (⊤ : Subobject A').arrow)
    (by simp) (by simp)

lemma map_transIso {Y Y' : C} (p : SubquotientPresentation A X)
    (p' : SubquotientPresentation A' X') (e : X ≅ Y) (e' : X' ≅ Y')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower) :
    (p.transIso e).map (p'.transIso e') f hZ hB = e.inv ≫ p.map p' f hZ hB ≫ e'.hom :=
  (p.transIso e).map_eq_of_comm (p'.transIso e') f hZ hB (u := p.mapUpper p' f hZ)
    (p.mapUpper_arrow p' f hZ)
    (by rw [transIso_π, transIso_π, Category.assoc, Iso.hom_inv_id_assoc, p.π_map_assoc])

/-- Two subquotient presentations inside the same object `A` with equal lower and upper subobjects
present canonically isomorphic objects. -/
noncomputable def isoOfEq {Y : C} (p : SubquotientPresentation A X)
    (q : SubquotientPresentation A Y) (hlower : p.lower = q.lower) (hupper : p.upper = q.upper) :
    X ≅ Y where
  hom := p.map q (𝟙 A) (by rw [Subobject.pullback_id, hupper])
    (((Subobject.existsPullbackAdj (𝟙 A)).gc _ _).2 (by rw [Subobject.pullback_id, hlower]))
  inv := q.map p (𝟙 A) (by rw [Subobject.pullback_id, hupper])
    (((Subobject.existsPullbackAdj (𝟙 A)).gc _ _).2 (by rw [Subobject.pullback_id, hlower]))
  hom_inv_id := by
    rw [← p.map_comp q p (𝟙 A) (𝟙 A) _ _ _ _ (by rw [Category.id_comp, Subobject.pullback_id])
      (((Subobject.existsPullbackAdj _).gc _ _).2
        (by rw [Category.id_comp, Subobject.pullback_id]))]
    simp only [Category.id_comp, map_id]
  inv_hom_id := by
    rw [← q.map_comp p q (𝟙 A) (𝟙 A) _ _ _ _ (by rw [Category.id_comp, Subobject.pullback_id])
      (((Subobject.existsPullbackAdj _).gc _ _).2
        (by rw [Category.id_comp, Subobject.pullback_id]))]
    simp only [Category.id_comp, map_id]

@[simp]
lemma isoOfEq_refl (p : SubquotientPresentation A X) :
    p.isoOfEq p rfl rfl = Iso.refl X := by
  ext
  dsimp [isoOfEq]
  exact p.map_id _ _

lemma isoOfEq_symm {Y : C} (p : SubquotientPresentation A X) (q : SubquotientPresentation A Y)
    (hlower : p.lower = q.lower) (hupper : p.upper = q.upper) :
    (p.isoOfEq q hlower hupper).symm = q.isoOfEq p hlower.symm hupper.symm := by
  ext
  rfl

lemma isoOfEq_trans {Y Z : C} (p : SubquotientPresentation A X) (q : SubquotientPresentation A Y)
    (r : SubquotientPresentation A Z) (hl₁ : p.lower = q.lower) (hu₁ : p.upper = q.upper)
    (hl₂ : q.lower = r.lower) (hu₂ : q.upper = r.upper) :
    p.isoOfEq q hl₁ hu₁ ≪≫ q.isoOfEq r hl₂ hu₂ =
      p.isoOfEq r (hl₁.trans hl₂) (hu₁.trans hu₂) := by
  ext
  dsimp [isoOfEq]
  rw [← p.map_comp q r (𝟙 A) (𝟙 A) _ _ _ _
    (by rw [Category.id_comp, Subobject.pullback_id, hu₁, hu₂])
    (((Subobject.existsPullbackAdj _).gc _ _).2
      (by rw [Category.id_comp, Subobject.pullback_id, hl₁, hl₂]))]
  simp only [Category.id_comp]

lemma isoOfEq_transIso {Y Z : C} (p : SubquotientPresentation A X)
    (q : SubquotientPresentation A Y) (e : Y ≅ Z)
    (hlower : p.lower = q.lower) (hupper : p.upper = q.upper) :
    p.isoOfEq (q.transIso e) hlower hupper = p.isoOfEq q hlower hupper ≪≫ e := by
  ext
  simpa [isoOfEq] using
    (p.map_transIso q (Iso.refl X) e (𝟙 A) (by rw [Subobject.pullback_id, hupper])
      (((Subobject.existsPullbackAdj (𝟙 A)).gc _ _).2 (by rw [Subobject.pullback_id, hlower])))

@[reassoc]
lemma isoOfEq_hom_comp_map {Y Y' : C}
    (p : SubquotientPresentation A X) (q : SubquotientPresentation A Y)
    (p' : SubquotientPresentation A' X') (q' : SubquotientPresentation A' Y')
    (hl : p.lower = q.lower) (hu : p.upper = q.upper)
    (hl' : p'.lower = q'.lower) (hu' : p'.upper = q'.upper)
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower)
    (hZq : q.upper ≤ (Subobject.pullback f).obj q'.upper)
    (hBq : (Subobject.exists f).obj q.lower ≤ q'.lower) :
    (p.isoOfEq q hl hu).hom ≫ q.map q' f hZq hBq =
      p.map p' f hZ hB ≫ (p'.isoOfEq q' hl' hu').hom := by
  dsimp [isoOfEq]
  rw [← p.map_comp q q' (𝟙 A) f _ _ hZq hBq
      (by rw [Category.id_comp, ← hu']; exact hZ)
      (by rw [Category.id_comp, ← hl']; exact hB),
    ← p.map_comp p' q' f (𝟙 A') hZ hB _ _
      (by rw [Category.comp_id, ← hu']; exact hZ)
      (by rw [Category.comp_id, ← hl']; exact hB)]
  simp only [Category.id_comp, Category.comp_id]

/-- Lifting preserves the upper pullback inequality for induced subquotient maps. -/
lemma lift_le_pullback_lift (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower)
    {K : Subobject X} {K' : Subobject X'}
    (hK : K ≤ (Subobject.pullback (p.map p' f hZ hB)).obj K') :
    p.lift K ≤ (Subobject.pullback f).obj (p'.lift K') := by
  have hfac : (p'.lift K').Factors ((p.lift K).arrow ≫ f) := by
    rw [p'.factors_lift_iff]
    have hf' : p'.upper.Factors ((p.lift K).arrow ≫ f) := by
      have h : (Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K) ≫ p.mapUpper p' f hZ) ≫
          p'.upper.arrow = (p.lift K).arrow ≫ f := by
        simp
      exact h ▸ Subobject.factors_comp_arrow _
    refine ⟨hf', ?_⟩
    have hft : p'.upper.factorThru ((p.lift K).arrow ≫ f) hf' =
        Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K) ≫ p.mapUpper p' f hZ := by
      rw [← cancel_mono p'.upper.arrow]
      simp
    rw [hft, Category.assoc, ← p.π_map p' f hZ hB, ← Category.assoc, ← p.liftTo_arrow K,
      Category.assoc]
    have hKf : K'.Factors (K.arrow ≫ p.map p' f hZ hB) :=
      (pullback_factors_iff _ _ _).1 (Subobject.factors_of_le _ hK (Subobject.factors_self _))
    exact Subobject.factors_of_factors_right (p.liftTo K) hKf
  exact Subobject.le_pullback_of_comm f ((p'.lift K').factorThru _ hfac) (by simp)

/-- Lifting preserves the lower image inequality for induced subquotient maps. -/
lemma exists_lift_le_lift (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower)
    {I : Subobject X} {I' : Subobject X'}
    (hI : (Subobject.exists (p.map p' f hZ hB)).obj I ≤ I') :
    (Subobject.exists f).obj (p.lift I) ≤ p'.lift I' :=
  (Subobject.existsPullbackAdj f).gc _ _ |>.2
    (p.lift_le_pullback_lift p' f hZ hB hI')
  where
    hI' : I ≤ (Subobject.pullback (p.map p' f hZ hB)).obj I' :=
      (Subobject.existsPullbackAdj _).gc _ _ |>.1 hI

/-- Composition of presentations commutes with `map`. -/
lemma map_comp_presentation {Y Y' : C}
    (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')
    (q : SubquotientPresentation X Y) (q' : SubquotientPresentation X' Y')
    (f : A ⟶ A') (hZ : p.upper ≤ (Subobject.pullback f).obj p'.upper)
    (hB : (Subobject.exists f).obj p.lower ≤ p'.lower)
    (hqZ : q.upper ≤ (Subobject.pullback (p.map p' f hZ hB)).obj q'.upper)
    (hqB : (Subobject.exists (p.map p' f hZ hB)).obj q.lower ≤ q'.lower) :
    (p.comp q).map (p'.comp q') f
      (p.lift_le_pullback_lift p' f hZ hB hqZ)
      (p.exists_lift_le_lift p' f hZ hB hqB) =
      q.map q' (p.map p' f hZ hB) hqZ hqB := by
  have hZcomp := p.lift_le_pullback_lift p' f hZ hB hqZ
  have hBcomp := p.exists_lift_le_lift p' f hZ hB hqB
  refine (p.comp q).map_eq_of_comm (p'.comp q') f hZcomp hBcomp
    (u := (p.comp q).mapUpper (p'.comp q') f hZcomp) (mapUpper_arrow _ _ _ _) ?_
  have hsq : (p.comp q).mapUpper (p'.comp q') f hZcomp ≫ p'.liftTo q'.upper =
      p.liftTo q.upper ≫ q.mapUpper q' (p.map p' f hZ hB) hqZ := by
    rw [← cancel_mono q'.upper.arrow]
    simp only [Category.assoc, liftTo_arrow, liftTo_arrow_assoc, mapUpper_arrow,
      p.π_map p' f hZ hB]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono p'.upper.arrow]
    simp only [Category.assoc, Subobject.ofLE_arrow, mapUpper_arrow, Subobject.ofLE_arrow_assoc]
    exact (p.comp q).mapUpper_arrow (p'.comp q') f hZcomp
  rw [comp_π, comp_π, Category.assoc, q.π_map, reassoc_of% hsq]

end Map

section ShortComplex

lemma imageSubobject_le_kernelSubobject (S : ShortComplex C) :
    imageSubobject S.f ≤ kernelSubobject S.g :=
  imageSubobject_le S.f (factorThruKernelSubobject S.g S.f S.zero) (by simp)

/-- The canonical isomorphism between `cokernel (ofLE (imageSubobject S.f) (kernelSubobject S.g))`
and `S.homology`. -/
noncomputable def ofShortComplexIso (S : ShortComplex C) :
    cokernel (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
      (imageSubobject_le_kernelSubobject S)) ≅ S.homology := by
  let hle := imageSubobject_le_kernelSubobject S
  let ψ : (kernelSubobject S.g : C) ⟶ S.homology :=
    (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ
  have htoCycles : factorThruImageSubobject S.f ≫ Subobject.ofLE _ _ hle ≫
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv = S.toCycles := by
    rw [← cancel_mono S.iCycles]
    simp
  have hw : Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) hle ≫ ψ = 0 := by
    rw [← cancel_epi (factorThruImageSubobject S.f), comp_zero]
    simpa [ψ, Category.assoc] using
      (congrArg (· ≫ S.homologyπ) htoCycles).trans S.toCycles_comp_homologyπ
  have hinv : S.toCycles ≫ S.cyclesIsoKernel.hom ≫ (kernelSubobjectIso S.g).inv ≫
      cokernel.π (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) hle) = 0 := by
    rw [← htoCycles]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, cokernel.condition,
      comp_zero]
  exact
    { hom := cokernel.desc _ ψ hw
      inv := S.descHomology (S.cyclesIsoKernel.hom ≫ (kernelSubobjectIso S.g).inv ≫
        cokernel.π _) hinv
      hom_inv_id := by
        refine (cancel_epi (cokernel.π _)).1 ?_
        rw [Category.comp_id, cokernel.π_desc_assoc]
        simp only [ψ, Category.assoc, ShortComplex.π_descHomology, Iso.inv_hom_id_assoc,
          Iso.hom_inv_id_assoc]
      inv_hom_id := by
        rw [← cancel_epi S.homologyπ]
        simp only [ShortComplex.π_descHomology_assoc, cokernel.π_desc, Category.comp_id,
          ψ, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] }

/-- The canonical subquotient presentation of `S.homology` as
`kernelSubobject S.g / imageSubobject S.f` inside `S.X₂`. -/
noncomputable abbrev ofShortComplex (S : ShortComplex C) :
    SubquotientPresentation S.X₂ S.homology where
  lower := imageSubobject S.f
  upper := kernelSubobject S.g
  le := imageSubobject_le_kernelSubobject S
  iso := ofShortComplexIso S

@[simp, reassoc]
lemma ofShortComplex_π (S : ShortComplex C) :
    (ofShortComplex S).π = (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ := by
  dsimp [π, ofShortComplex, ofShortComplexIso]
  exact cokernel.π_desc _ _ _

lemma ofShortComplex_upper_le_pullback {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ofShortComplex S₁).upper ≤ (Subobject.pullback φ.τ₂).obj (ofShortComplex S₂).upper := by
  dsimp [ofShortComplex]
  rw [Subobject.pullback_kernelSubobject]
  exact le_kernelSubobject _ _ (by rw [φ.comm₂₃, kernelSubobject_arrow_comp_assoc, zero_comp])

lemma exists_ofShortComplex_lower_le {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (Subobject.exists φ.τ₂).obj (ofShortComplex S₁).lower ≤ (ofShortComplex S₂).lower := by
  dsimp [ofShortComplex]
  rw [Subobject.exists_obj_imageSubobject, ← φ.comm₁₂]
  exact imageSubobject_comp_le _ _

/-- The morphism induced on `ofShortComplex` by a morphism of short complexes `φ` is
`ShortComplex.homologyMap φ`. -/
lemma map_ofShortComplex {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ofShortComplex S₁).map (ofShortComplex S₂) φ.τ₂
      (ofShortComplex_upper_le_pullback φ) (exists_ofShortComplex_lower_le φ) =
      ShortComplex.homologyMap φ := by
  let u : (kernelSubobject S₁.g : C) ⟶ (kernelSubobject S₂.g : C) :=
    (kernelSubobjectIso S₁.g).hom ≫ S₁.cyclesIsoKernel.inv ≫ ShortComplex.cyclesMap φ ≫
      S₂.cyclesIsoKernel.hom ≫ (kernelSubobjectIso S₂.g).inv
  refine (ofShortComplex S₁).map_eq_of_comm (ofShortComplex S₂) φ.τ₂
    (ofShortComplex_upper_le_pullback φ) (exists_ofShortComplex_lower_le φ) (u := u) ?_ ?_
  · dsimp [ofShortComplex, u]
    simp only [Category.assoc, kernelSubobject_arrow', ShortComplex.cyclesIsoKernel_hom,
      kernel.lift_ι, ShortComplex.cyclesMap_i, ShortComplex.cyclesIsoKernel_inv,
      ShortComplex.liftCycles_i_assoc, kernelSubobject_arrow_assoc]
  · rw [ofShortComplex_π, ofShortComplex_π]
    dsimp only [u]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      ShortComplex.homologyπ_naturality]

/-- When both differentials of a short complex `S` vanish, `ofShortComplex S` is the identity
presentation transported along `(S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf`. -/
lemma ofShortComplex_eq_refl_transIso (S : ShortComplex C) (hf : S.f = 0) (hg : S.g = 0) :
    ofShortComplex S =
      (refl S.X₂).transIso ((S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf) := by
  have hupper : (ofShortComplex S).upper =
      ((refl S.X₂).transIso ((S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf)).upper := by
    simp [hg]
  refine ext hupper ?_
  rw [transIso_π, refl_π, ofShortComplex_π]
  simp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.asIsoHomologyπ_hom, ← Category.assoc]
  congr 1
  rw [← cancel_mono S.iCycles]
  simp [Category.assoc]

end ShortComplex

end Abelian

end SubquotientPresentation

end TauCeti
