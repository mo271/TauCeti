/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import TauCeti.CategoryTheory.Exact.Resolution.HasFiniteResolution
import TauCeti.CategoryTheory.Exact.Resolution.ProjectiveResolution

/-!
# Left derived functors and bounds on projective dimension

Let `F : C ⥤ D` be an additive functor between abelian categories. When `C` has enough projectives,
an object `X` of projective dimension at most `d` has a projective resolution vanishing above
degree `d`, so the left derived functors `LₙF(X)` vanish for `n > d`
(`CategoryTheory.Functor.isZero_leftDerived_of_hasProjectiveDimensionLE`).

Conversely, suppose that `F` preserves finite colimits and projective objects. If `LᵢF(X) = 0` for
every `i > 0`, then `F` carries any projective resolution `P` of `X` to a projective resolution of
`F(X)` (`CategoryTheory.ProjectiveResolution.mapOfIsZeroLeftDerived`): right exactness preserves
the cokernel presentation `P₁ ⟶ P₀ ⟶ X ⟶ 0`, and the vanishing of `LᵢF(X)` makes `F(P)` exact in
positive degrees. If `X` has projective dimension at most `d`, only `L₁F(X), …, L_d F(X)` need to
vanish (`CategoryTheory.Functor.hasProjectiveDimensionLE_obj_of_isZero_leftDerived`), since the
higher left derived functors vanish automatically; applying `F` to a projective resolution of `X`
of length `d` then produces one of `F(X)` of length `d`, without requiring enough projectives in
`D`.

When `F ⊣ G` is an adjunction with `G` fully faithful, the counit `F(G(Y)) ⟶ Y` is an isomorphism,
so `pd_D Y ≤ d` follows from `pd_C G(Y) ≤ d` and the vanishing of `LᵢF(G(Y))` for `1 ≤ i ≤ d`
(`CategoryTheory.Adjunction.hasProjectiveDimensionLE_of_isZero_leftDerived`). Applied to scalar
extension and restriction along a surjective ring homomorphism `A →+* B`, this says that a
`B`-module `M` with `Tor_i^A(B, M) = 0` for `1 ≤ i ≤ d` satisfies `pd_B M ≤ pd_A M`.

## Main definitions and results

* `CategoryTheory.Functor.isZero_leftDerived_of_hasProjectiveDimensionLE`: if `pd X ≤ d`, then
  `LₙF(X) = 0` for `n > d`.
* `CategoryTheory.ProjectiveResolution.mapOfIsZeroLeftDerived`: a right exact additive functor
  preserving projectives maps a projective resolution of `X` to one of `F(X)` whenever
  `L_{n+1}F(X) = 0` for all `n`.
* `CategoryTheory.Functor.hasProjectiveDimensionLE_obj_of_isZero_leftDerived`: if `pd X ≤ d` and
  `L_{i+1}F(X) = 0` for `i < d`, then `pd F(X) ≤ d`.
* `CategoryTheory.Adjunction.hasProjectiveDimensionLE_of_isZero_leftDerived`: for `F ⊣ G` with `G`
  fully faithful, if `pd G(Y) ≤ d` and `L_{i+1}F(G(Y)) = 0` for `i < d`, then `pd Y ≤ d`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4 and 4.1.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits ObjectProperty TauCeti.ExactStructure

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **Left derived functors vanish above the projective dimension.** If `X` has projective
dimension at most `d`, then `LₙF(X) = 0` for every additive functor `F` and every `n > d`. -/
theorem Functor.isZero_leftDerived_of_hasProjectiveDimensionLE [EnoughProjectives C]
    (F : C ⥤ D) [F.Additive] (X : C) (d : ℕ) [hX : HasProjectiveDimensionLE X d] {n : ℕ}
    (hn : d < n) : IsZero ((F.leftDerived n).obj X) := by
  obtain ⟨r, hr⟩ := exists_finiteResolution_isProjective_length_eq_iff.mpr hX
  let P := r.toProjectiveResolution (le_refl _)
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F n)
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _
    (F.map_isZero (r.isZero_toProjectiveResolution_X_of_length_lt (le_refl _) (hr ▸ hn)))

/-- **Mapping a projective resolution along an acyclic right exact functor.** If `F : C ⥤ D`
is additive, preserves finite colimits and projective objects, and `L_{n+1}F(X) = 0` for every `n`,
then `F` carries any projective resolution `P` of `X` to a projective resolution of `F(X)`. -/
@[expose]
def ProjectiveResolution.mapOfIsZeroLeftDerived [HasProjectiveResolutions C] {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    [F.PreservesProjectiveObjects] (hF : ∀ n, IsZero ((F.leftDerived (n + 1)).obj X)) :
    ProjectiveResolution (F.obj X) := by
  let ε := (ChainComplex.toSingle₀Equiv P.complex X P.π).1
  have hzero : ((F.mapHomologicalComplex _).obj P.complex).d 1 0 ≫ F.map ε = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, ← F.map_comp,
      (ChainComplex.toSingle₀Equiv P.complex X P.π).2, F.map_zero]
  have hcok : (ShortComplex.mk (((F.mapHomologicalComplex _).obj P.complex).d 1 0)
      (F.map ε) hzero).Exact ∧ Epi (F.map ε) :=
    (ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).mpr
      ⟨CokernelCofork.mapIsColimit _ P.isColimitCokernelCofork F⟩
  have := hcok.2
  refine ChainComplex.toProjectiveResolution ((F.mapHomologicalComplex _).obj P.complex)
    (F.map ε) hzero (fun n ↦ F.projective_obj_of_projective (P.projective n)) hcok.1
    fun n ↦ ?_
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hF n).of_iso (P.isoLeftDerivedObj F (n + 1)).symm

@[simp]
theorem ProjectiveResolution.mapOfIsZeroLeftDerived_complex [HasProjectiveResolutions C] {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    [F.PreservesProjectiveObjects] (hF : ∀ n, IsZero ((F.leftDerived (n + 1)).obj X)) :
    (P.mapOfIsZeroLeftDerived F hF).complex = (F.mapHomologicalComplex _).obj P.complex :=
  (rfl)

@[simp]
theorem ProjectiveResolution.mapOfIsZeroLeftDerived_π_f_zero [HasProjectiveResolutions C] {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    [F.PreservesProjectiveObjects] (hF : ∀ n, IsZero ((F.leftDerived (n + 1)).obj X)) :
    (P.mapOfIsZeroLeftDerived F hF).π.f 0 =
      F.map (ChainComplex.toSingle₀Equiv P.complex X P.π).1 := by
  simp only [mapOfIsZeroLeftDerived, ChainComplex.toProjectiveResolution,
    ChainComplex.toSingle₀Equiv_apply_coe]
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **A right exact functor preserving projectives preserves projective dimension bounds on acyclic
objects.** If `X` has projective dimension at most `d` and `L_{i+1}F(X) = 0` for `i < d`, then
`F(X)` has projective dimension at most `d`. Enough projectives in `D` are not needed. -/
theorem Functor.hasProjectiveDimensionLE_obj_of_isZero_leftDerived [EnoughProjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
    (X : C) (d : ℕ) [hX : HasProjectiveDimensionLE X d]
    (hF : ∀ i < d, IsZero ((F.leftDerived (i + 1)).obj X)) :
    HasProjectiveDimensionLE (F.obj X) d := by
  obtain ⟨r, hr⟩ := exists_finiteResolution_isProjective_length_eq_iff.mpr hX
  let P := r.toProjectiveResolution (le_refl _)
  have hF' (n : ℕ) : IsZero ((F.leftDerived (n + 1)).obj X) := by
    by_cases hn : n < d
    · exact hF n hn
    · exact F.isZero_leftDerived_of_hasProjectiveDimensionLE X d (by lia)
  let Q := P.mapOfIsZeroLeftDerived F hF'
  have hQ : IsZero (Q.complex.X (d + 1)) :=
    F.map_isZero (r.isZero_toProjectiveResolution_X_of_length_lt (le_refl _) (by lia))
  have hlen := (Q.toFiniteResolution hQ).hasFiniteResolutionOfLength
  rw [Q.length_toFiniteResolution hQ] at hlen
  exact hlen.hasProjectiveDimensionLE

/-- **Descent of projective dimension along a fully faithful right adjoint.** Let `F ⊣ G` with `G`
fully faithful and `F` additive and preserving projective objects. If `G(Y)` has projective
dimension at most `d` and `L_{i+1}F(G(Y)) = 0` for `i < d`, then `Y` has projective dimension at
most `d`. -/
theorem Adjunction.hasProjectiveDimensionLE_of_isZero_leftDerived [EnoughProjectives C]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [F.PreservesProjectiveObjects]
    [G.Full] [G.Faithful] (Y : D) (d : ℕ) [HasProjectiveDimensionLE (G.obj Y) d]
    (hF : ∀ i < d, IsZero ((F.leftDerived (i + 1)).obj (G.obj Y))) :
    HasProjectiveDimensionLE Y d := by
  have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  have : HasProjectiveDimensionLE ((G ⋙ F).obj Y) d :=
    F.hasProjectiveDimensionLE_obj_of_isZero_leftDerived (G.obj Y) d hF
  exact hasProjectiveDimensionLT_of_iso (asIso (adj.counit.app Y)) (d + 1)

end CategoryTheory
