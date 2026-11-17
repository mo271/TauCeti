/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Basic

/-!
# The affine chart `D₊(X)` of a coefficient subalgebra

Let `R` be a commutative ring, `B` a commutative `R`-algebra, and `M : ℕ → Submodule R B` an
increasing, exhaustive graded family of `R`-submodules (`SetLike.GradedMonoid M`) containing `1` in
degree one. Evaluation at `1` identifies the degree-zero homogeneous localization of the coefficient
subalgebra `TauCeti.coeffSubalgebra M ⊆ B[X]` away from the degree-one element `X` with `B`.

## Main results

* `TauCeti.coeffSubalgebra.awayXEquiv`: the ring isomorphism
  `HomogeneousLocalization.Away (coeffSubalgebra.grade M) (coeffSubalgebra.X M h1) ≃+* B`.
* `TauCeti.coeffSubalgebra.awayXEquiv_mk`: evaluation of `awayXEquiv` on fractions `b Xⁿ / Xⁿ`.

## References

* [The Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
-/

public section

namespace TauCeti

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (M : ℕ → Submodule R B) [SetLike.GradedMonoid M] (h1 : (1 : B) ∈ M 1)

private noncomputable def coeffSubalgebra.awayXHom :
    HomogeneousLocalization.Away (coeffSubalgebra.grade M) (coeffSubalgebra.X M h1) →+* B :=
  (IsLocalization.Away.lift (coeffSubalgebra.X M h1) (g := (coeffSubalgebra.evalOne M).toRingHom)
    (by simp [coeffSubalgebra.evalOne_X])).comp
    (algebraMap (HomogeneousLocalization.Away (coeffSubalgebra.grade M) (coeffSubalgebra.X M h1))
      (Localization.Away (coeffSubalgebra.X M h1)))

private theorem coeffSubalgebra.awayXHom_mk (n : ℕ) (a : coeffSubalgebra M)
    (ha : a ∈ coeffSubalgebra.grade M (n • 1)) :
    coeffSubalgebra.awayXHom M h1
      (HomogeneousLocalization.Away.mk (coeffSubalgebra.grade M)
        (coeffSubalgebra.X_mem_grade_one M h1) n a ha) = coeffSubalgebra.evalOne M a := by
  rw [awayXHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  simp [coeffSubalgebra.evalOne_X]

/-- **The affine chart `D₊(X)` of `coeffSubalgebra M` is `Spec B`.** For an increasing, exhaustive
graded family `M` of `R`-submodules of a commutative `R`-algebra `B` containing `1` in degree one,
evaluation at `1` identifies the degree-zero localization away from `X` with `B`. -/
noncomputable def coeffSubalgebra.awayXEquiv (hM : Monotone M) (hex : (⨆ n, M n) = ⊤) :
    HomogeneousLocalization.Away (coeffSubalgebra.grade M) (coeffSubalgebra.X M h1) ≃+* B :=
  RingEquiv.ofBijective (coeffSubalgebra.awayXHom M h1)
    ⟨by
      -- Injectivity: on `a / Xⁿ` with `a = b Xⁿ`, the image is `b`; if `b = 0` then `a = 0`.
      intro z₁ z₂ hz
      rw [← sub_eq_zero] at hz ⊢
      rw [← map_sub] at hz
      obtain ⟨n, a, ha, hmk⟩ := HomogeneousLocalization.Away.mk_surjective
        (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1) (z₁ - z₂)
      rw [← hmk] at hz ⊢
      rw [coeffSubalgebra.awayXHom_mk] at hz
      have ha0 : a = 0 := by
        rw [← coeffSubalgebra.coeff_eq_zero_iff_of_mem_grade ha,
          ← coeffSubalgebra.eval_one_of_mem_grade ha, ← coeffSubalgebra.evalOne_apply]
        exact hz
      ext
      simp [HomogeneousLocalization.Away.val_mk, ha0, Localization.mk_zero],
    by
      -- Surjectivity: every `b ∈ B` lies in some `M n`, and `b Xⁿ / Xⁿ` maps to `b`.
      intro b
      have hb : b ∈ ⨆ n, M n := hex.symm ▸ Submodule.mem_top
      obtain ⟨n, hbn⟩ := (Submodule.mem_iSup_of_directed M hM.directed_le).mp hb
      refine ⟨HomogeneousLocalization.Away.mk (coeffSubalgebra.grade M)
        (coeffSubalgebra.X_mem_grade_one M h1) n
        (coeffSubalgebra.monomial M n b hbn)
        (by simpa [smul_eq_mul] using coeffSubalgebra.monomial_mem_grade n b hbn), ?_⟩
      rw [coeffSubalgebra.awayXHom_mk, coeffSubalgebra.evalOne_monomial]⟩

@[simp]
theorem coeffSubalgebra.awayXEquiv_mk (hM : Monotone M) (hex : (⨆ n, M n) = ⊤)
    (n : ℕ) (b : B) (hb : b ∈ M n) :
    coeffSubalgebra.awayXEquiv M h1 hM hex
      (HomogeneousLocalization.Away.mk (coeffSubalgebra.grade M)
        (coeffSubalgebra.X_mem_grade_one M h1) n
        (coeffSubalgebra.monomial M n b hb)
        (by simpa [smul_eq_mul] using coeffSubalgebra.monomial_mem_grade n b hb)) = b := by
  change coeffSubalgebra.awayXHom M h1 _ = b
  rw [coeffSubalgebra.awayXHom_mk, coeffSubalgebra.evalOne_monomial]

end TauCeti
