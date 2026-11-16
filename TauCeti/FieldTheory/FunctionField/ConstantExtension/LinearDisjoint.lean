/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Degrees after a linearly disjoint extension of constants

Let `F' = F · k'` in a common overfield, with `F` and `k'` linearly disjoint over `k`.
For every intermediate field `C` of `F/k` with `F/C` algebraic, a `C`-basis of `F` remains a
basis of `F'` over `k' · C`. In particular, `[F' : k'(x)] = [F : k(x)]` for every `x ∈ F` (and
`[F' : k'(X)] = [F : k(X)]` when `F` and `F'` carry compatible `RatFunc`-algebra structures).
The extension `k'/k` can be transcendental; no perfectness or exact-constants hypothesis
is needed once linear disjointness is supplied.

Linear independence is transported by
`IntermediateField.LinearDisjoint.linearIndependent_adjoin_algebraMap_comp`.
Spanning uses algebraicity of `F/C`: adjoining the algebraic image of `F` to `k' · C`
already gives the whole field compositum. A transcendental element also remains
transcendental, so a linearly disjoint extension of constants of a one-variable function
field is again a one-variable function field.

## Main results

* `TauCeti.constantExtensionBasisOfLinearDisjoint` and `TauCeti.ratFuncConstantExtensionBasis`:
  transport a basis over `C` (when `F/C` is algebraic) or over `RatFunc k` (when `F/k(X)` is
  algebraic).
* `TauCeti.finrank_over_adjoin_simple_eq_of_linearDisjoint` and
  `TauCeti.finrank_ratFunc_eq_of_linearDisjoint`: preserve the degree over `k(x)` and over
  `RatFunc k` without finiteness or algebraicity hypotheses.
* `IntermediateField.LinearDisjoint.transcendental_algebraMap_X`: preserve transcendence of the
  image of `RatFunc.X` over the enlarged constant field.
* `TauCeti.IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint`: preserve the
  one-variable function-field property under an arbitrary linearly disjoint extension of constants.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
  Proposition 3.6.1(c), for the algebraic constant-extension specialization.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A basis of an algebraic extension `F/C` stays a basis over `k' · C` in the linearly disjoint
constant compositum `F' = F · k'`. The constants `k'/k` need not be algebraic. -/
noncomputable def constantExtensionBasisOfLinearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (IntermediateField.adjoin k' (Set.range (algebraMap C F'))) F' :=
  Module.Basis.mk (H.linearIndependent_adjoin_algebraMap_comp C b.linearIndependent)
    (span_range_basis_of_isAlgebraic_constantCompositum h C b).ge

/-- The transported basis consists of the images of the original basis vectors. -/
@[simp]
theorem constantExtensionBasisOfLinearDisjoint_apply
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    constantExtensionBasisOfLinearDisjoint H h C b i = algebraMap F F' (b i) :=
  Module.Basis.mk_apply _ _ i

/-- An arbitrary linearly disjoint extension of constants preserves the degree over a
simple intermediate field: `[F · k' : k'(x)] = [F : k(x)]`. -/
theorem finrank_over_adjoin_simple_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (x : F) :
    Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F := by
  by_cases hfin : FiniteDimensional k⟮x⟯ F
  · have := hfin
    let b := Module.finBasis k⟮x⟯ F
    have hdegree := Module.finrank_eq_card_basis (constantExtensionBasisOfLinearDisjoint H h k⟮x⟯ b)
    rwa [IntermediateField.range_algebraMap_adjoin_simple,
      IntermediateField.adjoin_adjoin_right, Fintype.card_fin] at hdegree
  · have hfin' : ¬ FiniteDimensional k'⟮algebraMap F F' x⟯ F' := fun h' ↦ hfin <| by
      have := h'
      have hle := H.lift_rank_le_lift_rank_adjoin_algebraMap k⟮x⟯
      rw [IntermediateField.range_algebraMap_adjoin_simple,
        IntermediateField.adjoin_adjoin_right] at hle
      exact Module.rank_lt_aleph0_iff.mp <| Cardinal.lift_lt_aleph0.mp <|
        hle.trans_lt (Cardinal.lift_lt_aleph0.mpr (Module.rank_lt_aleph0 _ _))
    rw [Module.finrank_of_not_finite hfin', Module.finrank_of_not_finite hfin]

/-- Extending constants linearly disjointly, even transcendently, preserves the one-variable
function-field property. -/
theorem IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin hx
  have := finiteDimensional_adjoin_simple_of_constantCompositum_eq_top (k := k) h x
  exact (H.transcendental_algebraMap hx).isFunctionField_adjoin.finite_extension

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- Under a linearly disjoint extension of constants, the image of the rational-function
variable `RatFunc.X` remains transcendental over the enlarged constant field `k'`. -/
theorem _root_.IntermediateField.LinearDisjoint.transcendental_algebraMap_X
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F) :
    Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
  H.transcendental_algebraMap <|
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X

variable [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

/-- **Basis transport over `RatFunc` along a linearly disjoint constant extension.**
If `F' = F · k'` linearly disjointly over `k`, `F` is algebraic over `RatFunc k`, and
`RatFunc.X` acts compatibly on `F` and `F'`, then any `RatFunc k`-basis of `F` maps to a
`RatFunc k'`-basis of `F'`. The constant extension `k'/k` may be transcendental. -/
noncomputable def ratFuncConstantExtensionBasis
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) :
    Module.Basis ι (RatFunc k') F' :=
  let hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  let hx' : Transcendental k' (algebraMap (RatFunc k') F' RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  let e₁ := RatFunc.algEquivOfTranscendental _ hx
  let b₁ := b.mapCoeffs e₁.toRingEquiv fun c x ↦ by
    simp [Algebra.smul_def, e₁, coe_algEquivOfTranscendental_algebraMap_X_apply]
  let _ : Algebra.IsAlgebraic k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    isAlgebraic_adjoin_algebraMap_X_iff.mpr inferInstance
  let hC' : IntermediateField.adjoin k'
      (Set.range (algebraMap k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F')) =
      k'⟮algebraMap (RatFunc k') F' RatFunc.X⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple,
      IntermediateField.adjoin_adjoin_right, hXF']
  let e₂ := (IntermediateField.equivOfEq hC').trans
    (RatFunc.algEquivOfTranscendental _ hx').symm
  (constantExtensionBasisOfLinearDisjoint H h _ b₁).mapCoeffs e₂.toRingEquiv fun c x ↦ by
    have hc : algebraMap (RatFunc k') F' (e₂ c) = (c : F') := by
      rw [← coe_algEquivOfTranscendental_algebraMap_X_apply (k := k') (F := F') (e₂ c)]
      simp [e₂]
    simp [Algebra.smul_def, hc]

/-- `ratFuncConstantExtensionBasis` sends each basis vector to its image in `F'`. -/
@[simp]
theorem ratFuncConstantExtensionBasis_apply
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    ratFuncConstantExtensionBasis H h hXF' b i = algebraMap F F' (b i) := by
  simp [ratFuncConstantExtensionBasis]

/-- **A linearly disjoint constant extension preserves the degree over `RatFunc`.**
If `F' = F · k'` linearly disjointly over `k` and `RatFunc.X` acts compatibly on `F` and `F'`,
then `[F' : k'(X)] = [F : k(X)]`. Neither algebraicity nor separability is required. -/
theorem finrank_ratFunc_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F := by
  rw [← finrank_adjoin_algebraMap_X (k := k') (F := F'), ← hXF',
    finrank_over_adjoin_simple_eq_of_linearDisjoint H h,
    finrank_adjoin_algebraMap_X]

end RatFunc

end TauCeti
