/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic

import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Global trivialization of the cotangent bundle of a torus

For a finite family of positive periods `p : ι → ℝ`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus,
modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` so that each tangent space `TangentSpace _ x` is
`ι → ℝ`. Every constant vector `v : ι → ℝ` defines an analytic vector field on `Tⁿ`
(`AddCircle.torusVectorField`, `AddCircle.contMDiff_torusVectorField`), obtained by pushing forward
the constant vector `v` along the covering `(ι → ℝ) → Tⁿ`.

Pairing covectors on any manifold with a smooth vector field is smooth
(`TauCeti.CotangentBundle.contMDiff_snd_apply`). Specialising to the coordinate vector fields
`Pi.single i 1` on `Tⁿ` and the dual coordinate time forms `TauCeti.torusTimeForm p i` yields the
canonical global trivialization

`T*Tⁿ ≃ₘ Tⁿ × (ι → ℝ)`, `z ↦ (z.proj, fun i ↦ z.2 (Pi.single i 1))`

(`TauCeti.CotangentBundle.torusDiffeomorph`), whose inverse sends `(x, c)` to the covector
`∑ i, c i • dt_i(x)` over `x`.

## Main definitions

* `AddCircle.torusVectorField p v`: the constant vector field `v : ι → ℝ` on `∀ i, AddCircle (p i)`.
* `TauCeti.CotangentBundle.torusDiffeomorph p`: the smooth diffeomorphism
  `CotangentBundle (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ≃ₘ
    ((∀ i, AddCircle (p i)) × (ι → ℝ))`.

## Main results

* `AddCircle.contMDiff_torusVectorField`: `AddCircle.torusVectorField p v` is `C^n` for every `n`,
  including analytic.
* `TauCeti.CotangentBundle.contMDiff_snd_apply`: pairing covectors on `T*M` with a `C^n` vector
  field on `M` is `C^n`.
* `TauCeti.CotangentBundle.torusDiffeomorph_fst`, `TauCeti.CotangentBundle.torusDiffeomorph_snd`,
  `TauCeti.CotangentBundle.proj_torusDiffeomorph_symm`,
  `TauCeti.CotangentBundle.torusDiffeomorph_symm_snd_apply`: coordinate formulas for
  `torusDiffeomorph` and its inverse.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff

namespace AddCircle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- The constant vector field with value `v : ι → ℝ` on the torus `∀ i, AddCircle (p i)`. In the
product charts of the torus, each tangent space is `ι → ℝ`. -/
def torusVectorField (v : ι → ℝ) (x : ∀ i, AddCircle (p i)) :
    TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x :=
  v

/-- `AddCircle.torusVectorField p v` evaluates to `v` at every point of the torus. -/
@[simp]
theorem torusVectorField_apply (v : ι → ℝ) (x : ∀ i, AddCircle (p i)) :
    torusVectorField p v x = v :=
  (rfl)

/-- Every constant vector field `AddCircle.torusVectorField p v` is a `C^n` section of the tangent
bundle of `∀ i, AddCircle (p i)`, for every `n`, including analytic. -/
theorem contMDiff_torusVectorField (v : ι → ℝ) {n : ℕ∞ω} :
    ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).tangent n
      (fun x ↦ (⟨x, torusVectorField p v x⟩ :
        TangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))) := by
  -- Through the covering map `(ι → ℝ) → ∀ i, AddCircle (p i)`, a surjective analytic local
  -- diffeomorphism with identity derivative, the field is the pushed-forward constant vector `v`.
  rw [← (isLocalDiffeomorph_piMap_coe p ω).contMDiff_comp_iff (piMap_coe_surjective p) le_top]
  refine (contMDiffOn_univ.1 (((contMDiff_piMap_coe p ω).contMDiffOn (s := univ)
    ).contMDiffOn_totalSpaceMk_mfderiv_apply (m := n) le_top isOpen_univ v)).congr fun t ↦ ?_
  simp only [mfderiv_piMap_coe, comp_apply]
  -- `ContinuousLinearMap.id ℝ (ι → ℝ) v` is `v` by definition inside the tangent-bundle fibre.
  rfl

end AddCircle

namespace TauCeti

namespace CotangentBundle

section Pairing

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- Pairing covectors on `M` with a `C^n` vector field `V` on `M` defines a `C^n` scalar function
`z ↦ z.2 (V z.proj)` on `CotangentBundle I M`. -/
theorem contMDiff_snd_apply {n : ℕ∞ω} [IsManifold I (n + 1) M] {V : ∀ x : M, TangentSpace I x}
    (hV : ContMDiff I I.tangent n fun x ↦ (⟨x, V x⟩ : TangentBundle I M)) :
    ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) 𝓘(𝕜, 𝕜) n
      (fun z : CotangentBundle I M ↦ z.2 (V z.proj)) := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact (Bundle.Trivial.contMDiff_mk_iff.1
    (ContMDiff.clm_bundle_apply (E₂ := Bundle.Trivial M 𝕜) contMDiff_id
      (hV.comp (contMDiff_proj _)))).2

end Pairing

section Torus

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

private def toTorus
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    (∀ i, AddCircle (p i)) × (ι → ℝ) :=
  open scoped Classical in (z.proj, fun i ↦ z.2 (Pi.single i 1))

private def ofTorus (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  ⟨q.1, ∑ i, q.2 i • SmoothForm.degreeOneEquiv (torusTimeForm p i) q.1⟩

private theorem ofTorus_snd_apply (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) q.1) :
    (ofTorus p q).2 v = ∑ i, q.2 i * v i := by
  -- Unfold `ofTorus p q` over `q.1` to the linear combination of coordinate time forms.
  change (∑ i, q.2 i • SmoothForm.degreeOneEquiv (torusTimeForm p i) q.1) v = ∑ i, q.2 i * v i
  rw [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    SmoothForm.degreeOneEquiv_apply_apply, torusTimeForm_apply]

private theorem ofTorus_toTorus
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    ofTorus p (toTorus p z) = z := by
  classical
  obtain ⟨x, α⟩ := z
  ext : 1
  · rfl
  · refine heq_of_eq (ContinuousLinearMap.ext fun v ↦ ?_)
    have hv : (∑ i, (v i : ℝ) • (Pi.single i 1 : TangentSpace
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x)) = v := by
      let w : ι → ℝ := v
      have hv₀ : ∑ i, w i • Pi.single (M := fun _ : ι ↦ ℝ) i 1 = w := by
        ext j
        rw [Finset.sum_apply]
        simp [Pi.single_apply]
      exact hv₀
    calc (ofTorus p (toTorus p ⟨x, α⟩)).2 v
        = ∑ i, (toTorus p ⟨x, α⟩).2 i * v i := ofTorus_snd_apply p (toTorus p ⟨x, α⟩) v
      _ = ∑ i, v i • α (Pi.single i 1) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hi : (toTorus p ⟨x, α⟩).2 i = α (Pi.single i 1) := rfl
          rw [hi, smul_eq_mul, mul_comm]
      _ = α (∑ i, (v i : ℝ) • Pi.single i 1) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ (α.map_smul (v i) _).symm
      _ = α v := congrArg α hv

private theorem toTorus_ofTorus (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    toTorus p (ofTorus p q) = q := by
  classical
  obtain ⟨x, c⟩ := q
  refine Prod.ext rfl (funext fun i ↦ ?_)
  have hi : (toTorus p (ofTorus p (x, c))).2 i =
      (ofTorus p (x, c)).2 (Pi.single (M := fun _ : ι ↦ ℝ) i 1) := rfl
  rw [hi, ofTorus_snd_apply p (x, c) (Pi.single (M := fun _ : ι ↦ ℝ) i 1)]
  -- Read `Pi.single i 1 : TangentSpace _ x` as a function `ι → ℝ`.
  change ∑ j, c j * Pi.single (M := fun _ : ι ↦ ℝ) i 1 j = c i
  simp [Pi.single_apply]

/-- **Global trivialization of the cotangent bundle of a torus.** On `Tⁿ = ∀ i, AddCircle (p i)`,
evaluating a covector on the coordinate tangent vectors `Pi.single i 1` gives a smooth
diffeomorphism `T*Tⁿ ≃ₘ Tⁿ × (ι → ℝ)`, with inverse `(x, c) ↦ (x, ∑ i, c i • dt_i(x))`. -/
def torusDiffeomorph :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))
      ≃ₘ⟮(ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ),
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)⟯
      ((∀ i, AddCircle (p i)) × (ι → ℝ)) where
  toFun := toTorus p
  invFun := ofTorus p
  left_inv := ofTorus_toTorus p
  right_inv := toTorus_ofTorus p
  contMDiff_toFun := by
    classical
    exact (contMDiff_proj _).prodMk <| contMDiff_pi_module_iff.2 fun i ↦
      contMDiff_snd_apply (AddCircle.contMDiff_torusVectorField p (Pi.single i 1))
  contMDiff_invFun :=
    ContMDiff.sum_sectionAlong _ _ contMDiff_fst fun i _ ↦
      ContMDiff.smul_totalSpace (a := fun q : (∀ j, AddCircle (p j)) × (ι → ℝ) ↦ q.2 i)
        (g := fun q : (∀ j, AddCircle (p j)) × (ι → ℝ) ↦
          (⟨q.1, SmoothForm.degreeOneEquiv (torusTimeForm p i) q.1⟩ :
            CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ j, AddCircle (p j))))
        ((contDiff_apply ℝ (fun _ : ι ↦ ℝ) i).contMDiff.comp contMDiff_snd)
        ((SmoothForm.degreeOneEquiv (torusTimeForm p i)).contMDiff.comp contMDiff_fst)

/-- The first component of `torusDiffeomorph p z` is the base point `z.proj`. -/
@[simp]
theorem torusDiffeomorph_fst
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    (torusDiffeomorph p z).1 = z.proj :=
  (rfl)

/-- The second component of `torusDiffeomorph p z` is `fun i ↦ z.2 (Pi.single i 1)`. -/
@[simp]
theorem torusDiffeomorph_snd [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    (torusDiffeomorph p z).2 = fun i ↦ z.2 (Pi.single i 1) := by
  funext i
  -- `(torusDiffeomorph p z).2` is `(toTorus p z).2`, which uses `Classical.decEq ι`.
  change (toTorus p z).2 i = z.2 (Pi.single i 1)
  dsimp only [toTorus]
  congr 2
  exact Subsingleton.elim _ _

/-- The `i`-th coordinate of `(torusDiffeomorph p z).2` evaluates `z.2` on `Pi.single i 1`. -/
@[simp]
theorem torusDiffeomorph_snd_apply [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) (i : ι) :
    (torusDiffeomorph p z).2 i = z.2 (Pi.single i 1) :=
  congrFun (torusDiffeomorph_snd p z) i

/-- `(torusDiffeomorph p).symm q` lies over `q.1`. -/
@[simp]
theorem proj_torusDiffeomorph_symm (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    ((torusDiffeomorph p).symm q).proj = q.1 :=
  (rfl)

/-- The covector of `(torusDiffeomorph p).symm q` pairs with `v : ι → ℝ` as `∑ i, q.2 i * v i`. -/
@[simp]
theorem torusDiffeomorph_symm_snd_apply (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) q.1) :
    ((torusDiffeomorph p).symm q).2 v = ∑ i, q.2 i * v i :=
  ofTorus_snd_apply p q v

/-- Evaluating the covector of `(torusDiffeomorph p).symm q` on `Pi.single i 1` recovers `q.2 i`. -/
@[simp]
theorem torusDiffeomorph_symm_snd_apply_single [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) (i : ι) :
    ((torusDiffeomorph p).symm q).2 (Pi.single i 1) = q.2 i := by
  rw [torusDiffeomorph_symm_snd_apply p q (Pi.single i 1)]
  -- Read `Pi.single i 1 : TangentSpace _ q.1` as a function `ι → ℝ`.
  change ∑ j, q.2 j * Pi.single (M := fun _ : ι ↦ ℝ) i 1 j = q.2 i
  simp [Pi.single_apply]

end Torus

end CotangentBundle

end TauCeti
