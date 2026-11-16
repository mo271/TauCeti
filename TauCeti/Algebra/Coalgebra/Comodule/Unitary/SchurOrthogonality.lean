/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Unitarization
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Dual
public import TauCeti.Algebra.Coalgebra.Subcomodule.Schur
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The unitarizing matrix and weighted Schur orthogonality

Let `A` be a complex Hopf star algebra, that is a complex Hopf algebra with a compatible star
structure whose comultiplication is a star map (`TauCeti.StarCoalgebra ℂ A`), and let
`h : A →ₗ[ℂ] ℂ` be an invariant integral. For finite comodules `M` and `N` with bases `b` and `c`
and coefficient matrices `u` and `v`, applying `h` to products `v r j * star (u s l)` (under left
invariance and `uᴴ * u = 1`) or `star (h (star (u i j) * v k l))` (under right invariance and
`v * vᴴ = 1`) produces scalar matrices intertwining `u` and `v`. In particular, whenever
`Hom ℂ A M N = 0`, all such Haar pairings between coefficients of `M` and `N` vanish.

When `u` is unitary, the entrywise conjugate `ū = u.map star` is the coefficient matrix of the dual
comodule `Module.Dual ℂ M` in the dual basis `b.dualBasis`, though `ū` itself need not be unitary
when the antipode is not involutive. If `h` is a nonzero positive right invariant integral, the
Haar Gram matrix `G` of `ū` is positive definite and satisfies `ūᴴ G ū = G`. Scaling `G` by
`√(Tr(G⁻¹) / Tr(G))` produces `TauCeti.Comodule.haarUnitarizingMatrix h b`, a positive definite
matrix `Ft` normalized by `Tr Ft = Tr Ft⁻¹` and satisfying `ūᴴ Ft ū = Ft` as well as
`ū Ft⁻¹ ūᴴ = Ft⁻¹`.

When `M` is simple (`IsSimpleOrder (Subcomodule ℂ A M)`), Schur's lemma forces any positive
definite matrix `Ft` satisfying `Tr Ft = Tr Ft⁻¹` and `ūᴴ Ft ū = Ft` to be unique — in particular
independent of `h` — and transforms `Ft` across orthonormal changes of basis by the entrywise
conjugate unitary matrix. If `h` is both left and right invariant and positive, Schur's lemma
applied to both Haar intertwining families together with `ū Ft⁻¹ ūᴴ = Ft⁻¹` yields the two weighted
Schur orthogonality relations:

* `h (star (u i j) * u k l) = δ_{j, l} * h 1 * (Ft⁻¹ i k / Tr Ft⁻¹)`,
* `h (u i j * star (u k l)) = δ_{i, k} * h 1 * (Ft j l / Tr Ft)`.

When `h 1 = 1`, these give the normalized weighted Schur orthogonality formulas, and `Ft` is
uniquely determined by them as well.

## Main declarations

* `LinearMap.IsLeftInvariantIntegral.coefficientMatrix_mul_map_apply_mul_star` and
  `LinearMap.IsRightInvariantIntegral.coefficientMatrix_mul_map_star_apply_star_mul`: the left and
  right Haar intertwining matrices.
* `LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero`,
  `LinearMap.IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero`,
  `LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero_of_isSimpleOrder`, and
  `LinearMap.IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero_of_isSimpleOrder`:
  orthogonality of matrix coefficients of comodules with no nonzero or bijective intertwiner.
* `TauCeti.Comodule.haarUnitarizingMatrix`: the positive definite unitarizing matrix `Ft` of `ū`,
  normalized by `Tr Ft = Tr Ft⁻¹`.
* `TauCeti.Comodule.posDef_haarUnitarizingMatrix`,
  `TauCeti.Comodule.trace_haarUnitarizingMatrix_eq_trace_inv`,
  `TauCeti.Comodule.conjTranspose_map_star_mul_haarUnitarizingMatrix_mul`, and
  `TauCeti.Comodule.map_star_mul_inv_haarUnitarizingMatrix_mul_conjTranspose`: positivity, trace
  normalization, and conjugate-unitarization identities for `Ft`.
* `TauCeti.Comodule.eq_of_posDef_of_trace_eq_of_conjTranspose_map_star_mul_eq` and
  `TauCeti.Comodule.existsUnique_posDef_trace_eq_conjTranspose_map_star_mul_eq`: uniqueness and
  unique existence of `Ft` for a simple comodule.
* `OrthonormalBasis.haarUnitarizingMatrix_eq`: transformation of `Ft` under an orthonormal change
  of basis.
* `TauCeti.Comodule.apply_star_coefficientMatrix_mul`,
  `TauCeti.Comodule.apply_coefficientMatrix_mul_star`, and
  `TauCeti.Comodule.schur_orthogonality`: the two weighted Schur orthogonality relations.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 3.2.9 and
  Theorem 5.4.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.4.2.
-/

public section

open Module Matrix TauCeti TauCeti.Comodule
open scoped ComplexOrder

/-! ### Haar intertwining matrices and distinct-comodule orthogonality -/

namespace LinearMap

section Bialgebra

variable {R A M N ι κ : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
  [Bialgebra R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N]
  {h : A →ₗ[R] R}

/-- **Left-Haar intertwining identity.** For a left invariant integral `h` and a basis `b` whose
coefficient matrix `u` satisfies `uᴴ * u = 1`, the scalar matrix `(r, s) ↦ h (v r j * star (u s l))`
intertwines `u` with the coefficient matrix `v` of `c` for every fixed `j` and `l`. -/
theorem IsLeftInvariantIntegral.coefficientMatrix_mul_map_apply_mul_star
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (hl : h.IsLeftInvariantIntegral) {b : Basis ι R M} (c : Basis κ R N)
    (hu : (coefficientMatrix (C := A) b)ᴴ * coefficientMatrix (C := A) b = 1) (j : κ) (l : ι) :
    coefficientMatrix (C := A) c *
        (Matrix.of fun r s ↦ h (coefficientMatrix (C := A) c r j *
          star (coefficientMatrix (C := A) b s l))).map (algebraMap R A) =
      (Matrix.of fun r s ↦ h (coefficientMatrix (C := A) c r j *
        star (coefficientMatrix (C := A) b s l))).map (algebraMap R A) *
          coefficientMatrix (C := A) b := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  let rv (m q : κ) : Coalgebra.Repr R (v m q) κ :=
    ⟨Finset.univ, fun r ↦ v m r, fun r ↦ v r q, (comul_coefficientMatrix_eq_sum c m q).symm⟩
  let ru (p s : ι) : Coalgebra.Repr R (u p s) ι :=
    ⟨Finset.univ, fun q ↦ u p q, fun q ↦ u q s, (comul_coefficientMatrix_eq_sum b p s).symm⟩
  ext m s
  have hslice (p : ι) :
      ∑ r, ∑ q, h (v r j * star (u q l)) • (v m r * star (u p q)) =
        h (v m j * star (u p l)) • (1 : A) := by
    simpa [rv, ru] using hl.sum_sum_mul (rv m j) (ru p l).star
  have hsum := congrArg (fun f : ι → A ↦ ∑ p, f p * u p s) (funext hslice)
  simp only [Finset.sum_mul, smul_mul_assoc, one_mul] at hsum
  have hlhs :
      ∑ p, ∑ r, ∑ q, h (v r j * star (u q l)) • (v m r * star (u p q) * u p s) =
        (v * (Matrix.of fun r s' ↦ h (v r j * star (u s' l))).map (algebraMap R A)) m s := by
    calc _ = ∑ r, ∑ q, h (v r j * star (u q l)) •
            (v m r * ∑ p, star (u p q) * u p s) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [Finset.sum_comm]
          simp [Finset.mul_sum, Finset.smul_sum, mul_assoc]
      _ = ∑ r, h (v r j * star (u s l)) • v m r := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          have hunit (q : ι) : ∑ p, star (u p q) * u p s = (1 : Matrix ι ι A) q s := by
            simpa only [Matrix.mul_apply, conjTranspose_apply] using congrFun (congrFun hu q) s
          simp [hunit, Matrix.one_apply]
      _ = _ := by
          simp [Matrix.mul_apply, Algebra.smul_def, Algebra.commutes]
  have hrhs :
      ∑ p, h (v m j * star (u p l)) • u p s =
        ((Matrix.of fun r s' ↦ h (v r j * star (u s' l))).map (algebraMap R A) * u) m s := by
    simp [Matrix.mul_apply, Algebra.smul_def]
  exact hlhs.symm.trans (hsum.trans hrhs)

/-- **Orthogonality in the second Haar form.** If every comodule morphism from `M` to `N` is zero,
any left invariant integral vanishes on products `v r j * star (u s l)` whenever `uᴴ * u = 1`. -/
theorem IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero
    [Fintype ι] [Finite κ] [DecidableEq ι]
    (hl : h.IsLeftInvariantIntegral) {b : Basis ι R M} (c : Basis κ R N)
    (hu : (coefficientMatrix (C := A) b)ᴴ * coefficientMatrix (C := A) b = 1)
    (hHom : ∀ f : Hom R A M N, f = 0) (r j : κ) (s l : ι) :
    h (coefficientMatrix (C := A) c r j * star (coefficientMatrix (C := A) b s l)) = 0 := by
  classical
  cases nonempty_fintype κ
  set L : Matrix κ ι R :=
    Matrix.of fun r' s' ↦ h (coefficientMatrix (C := A) c r' j *
      star (coefficientMatrix (C := A) b s' l))
  let f : Hom R A M N :=
    ⟨Matrix.toLin b c L, (b.map_coact_iff_coefficientMatrix c (Matrix.toLin b c L)).mpr
      (by simpa only [LinearMap.toMatrix_toLin] using
        hl.coefficientMatrix_mul_map_apply_mul_star c hu j l)⟩
  have hf0 : LinearMap.toMatrix b c f.toLinearMap = 0 := by
    rw [hHom f, Hom.zero_toLinearMap, map_zero]
  simpa [f, L] using congrFun (congrFun hf0 r) s

/-- **Right-Haar intertwining identity.** For a right invariant integral `h` and a basis `c` whose
coefficient matrix `v` satisfies `v * vᴴ = 1`, the scalar matrix
`(q, p) ↦ star (h (star (u i p) * v k q))` intertwines `u` with `v` for every fixed `i` and `k`. -/
theorem IsRightInvariantIntegral.coefficientMatrix_mul_map_star_apply_star_mul
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι R M) {c : Basis κ R N}
    (hv : coefficientMatrix (C := A) c * (coefficientMatrix (C := A) c)ᴴ = 1) (i : ι) (k : κ) :
    coefficientMatrix (C := A) c *
        (Matrix.of fun q p ↦ star (h (star (coefficientMatrix (C := A) b i p) *
          coefficientMatrix (C := A) c k q))).map (algebraMap R A) =
      (Matrix.of fun q p ↦ star (h (star (coefficientMatrix (C := A) b i p) *
        coefficientMatrix (C := A) c k q))).map (algebraMap R A) *
          coefficientMatrix (C := A) b := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  let ru (i' p : ι) : Coalgebra.Repr R (u i' p) ι :=
    ⟨Finset.univ, fun s ↦ u i' s, fun s ↦ u s p, (comul_coefficientMatrix_eq_sum b i' p).symm⟩
  let rv (k' r : κ) : Coalgebra.Repr R (v k' r) κ :=
    ⟨Finset.univ, fun q ↦ v k' q, fun q ↦ v q r, (comul_coefficientMatrix_eq_sum c k' r).symm⟩
  ext m p
  have hslice (r : κ) :
      ∑ s, ∑ q, h (star (u i s) * v k q) • (star (u s p) * v q r) =
        h (star (u i p) * v k r) • (1 : A) := by
    simpa [ru, rv] using hr.sum_sum_mul (ru i p).star (rv k r)
  have hsum := congrArg (fun f : κ → A ↦ star (∑ r, f r * star (v m r))) (funext hslice)
  simp only [Finset.sum_mul, smul_mul_assoc, one_mul, star_sum, star_smul, star_star] at hsum
  have hlhs :
      ∑ r, ∑ s, ∑ q, star (h (star (u i s) * v k q)) •
          star (star (u s p) * v q r * star (v m r)) =
        ((Matrix.of fun q p' ↦ star (h (star (u i p') * v k q))).map (algebraMap R A) * u) m p := by
    have hunit (q : κ) : ∑ r, v q r * star (v m r) = (1 : Matrix κ κ A) q m := by
      simpa only [Matrix.mul_apply, conjTranspose_apply] using congrFun (congrFun hv q) m
    calc _ = ∑ s, ∑ q, star (h (star (u i s) * v k q)) •
            star (star (u s p) * ∑ r, v q r * star (v m r)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [Finset.sum_comm]
          simp [Finset.mul_sum, star_sum, Finset.smul_sum, mul_assoc]
      _ = ∑ s, star (h (star (u i s) * v k m)) • u s p := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          simp [hunit, Matrix.one_apply, apply_ite]
      _ = _ := by
          simp [Matrix.mul_apply, Algebra.smul_def]
  have hrhs :
      ∑ r, star (h (star (u i p) * v k r)) • v m r =
        (v * (Matrix.of fun q p' ↦ star (h (star (u i p') * v k q))).map
          (algebraMap R A)) m p := by
    simp [Matrix.mul_apply, Algebra.smul_def, -algebraMap_star_comm, Algebra.commutes]
  exact hrhs.symm.trans (hsum.symm.trans hlhs)

/-- **Orthogonality in the first Haar form.** If every comodule morphism from `M` to `N` is zero,
any right invariant integral vanishes on products `star (u i j) * v k l` whenever `v * vᴴ = 1`. -/
theorem IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι R M) {c : Basis κ R N}
    (hv : coefficientMatrix (C := A) c * (coefficientMatrix (C := A) c)ᴴ = 1)
    (hHom : ∀ f : Hom R A M N, f = 0) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 := by
  classical
  cases nonempty_fintype ι
  set Rmat : Matrix κ ι R :=
    Matrix.of fun q p ↦ star (h (star (coefficientMatrix (C := A) b i p) *
      coefficientMatrix (C := A) c k q))
  let f : Hom R A M N :=
    ⟨Matrix.toLin b c Rmat, (b.map_coact_iff_coefficientMatrix c (Matrix.toLin b c Rmat)).mpr
      (by simpa only [LinearMap.toMatrix_toLin] using
        hr.coefficientMatrix_mul_map_star_apply_star_mul b hv i k)⟩
  have hf0 : LinearMap.toMatrix b c f.toLinearMap = 0 := by
    rw [hHom f, Hom.zero_toLinearMap, map_zero]
  have hstar0 : star (h (star (coefficientMatrix (C := A) b i j) *
      coefficientMatrix (C := A) c k l)) = 0 := by
    simpa [f, Rmat] using congrFun (congrFun hf0 l) j
  exact star_eq_zero.mp hstar0

end Bialgebra

section SimpleBialgebra

variable {R A M N ι κ : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A]
  [Bialgebra R A] [Module.Projective R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M] [IsSimpleOrder (Subcomodule R A M)]
  [AddCommGroup N] [Module R N] [Comodule R A N] [IsSimpleOrder (Subcomodule R A N)]
  {h : A →ₗ[R] R}

/-- **Schur orthogonality for inequivalent simple comodules** (second Haar form). If `M` and `N`
are simple comodules over a projective star bialgebra admitting no bijective comodule morphism
`M → N`, any left invariant integral vanishes on `v r j * star (u s l)` whenever `uᴴ * u = 1`. -/
theorem IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero_of_isSimpleOrder
    [Fintype ι] [Finite κ] [DecidableEq ι]
    (hl : h.IsLeftInvariantIntegral) {b : Basis ι R M} (c : Basis κ R N)
    (hu : (coefficientMatrix (C := A) b)ᴴ * coefficientMatrix (C := A) b = 1)
    (hNoniso : ∀ f : Hom R A M N, ¬Function.Bijective f) (r j : κ) (s l : ι) :
    h (coefficientMatrix (C := A) c r j * star (coefficientMatrix (C := A) b s l)) = 0 :=
  hl.apply_coefficientMatrix_mul_star_eq_zero c hu
    (fun f ↦ f.eq_zero_or_bijective.resolve_right (hNoniso f)) r j s l

/-- **Schur orthogonality for inequivalent simple comodules** (first Haar form). If `M` and `N`
are simple comodules over a projective star bialgebra admitting no bijective comodule morphism
`M → N`, any right invariant integral vanishes on `star (u i j) * v k l` whenever `v * vᴴ = 1`. -/
theorem IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero_of_isSimpleOrder
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι R M) {c : Basis κ R N}
    (hv : coefficientMatrix (C := A) c * (coefficientMatrix (C := A) c)ᴴ = 1)
    (hNoniso : ∀ f : Hom R A M N, ¬Function.Bijective f) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 :=
  hr.apply_star_coefficientMatrix_mul_eq_zero b hv
    (fun f ↦ f.eq_zero_or_bijective.resolve_right (hNoniso f)) i j k l

end SimpleBialgebra

end LinearMap

/-! ### The normalized positive definite unitarizing matrix -/

namespace TauCeti.Comodule

section Coalgebra

variable {A M ι : Type*} [Semiring A] [StarRing A] [Algebra ℂ A] [Coalgebra ℂ A]
  [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι]

/-- The unnormalized Haar Gram matrix of the entrywise conjugate `u.map star`. -/
private noncomputable def conjHaarGramMatrix (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) : Matrix ι ι ℂ :=
  (((coefficientMatrix (C := A) b).map star)ᴴ * (coefficientMatrix (C := A) b).map star).map h

private theorem conjHaarGramMatrix_apply (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) (j l : ι) :
    conjHaarGramMatrix h b j l =
      h (∑ i, coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b i l)) := by
  simp [conjHaarGramMatrix, Matrix.mul_apply]

/-- **The normalized unitarizing matrix** `Ft` of a finite basis `b` with respect to `h`: the Haar
Gram matrix `G` of the entrywise conjugate `(coefficientMatrix b).map star`, scaled by
`√(re(Tr G⁻¹) / re(Tr G))` so that `Tr Ft = Tr Ft⁻¹`. -/
noncomputable def haarUnitarizingMatrix [DecidableEq ι] (h : A →ₗ[ℂ] ℂ)
    (b : Basis ι ℂ M) : Matrix ι ι ℂ :=
  let G := (((coefficientMatrix (C := A) b).map star)ᴴ *
    (coefficientMatrix (C := A) b).map star).map h
  Real.sqrt (G⁻¹.trace.re / G.trace.re) • G

/-- Explicit unfolding of `TauCeti.Comodule.haarUnitarizingMatrix`. -/
theorem haarUnitarizingMatrix_def [DecidableEq ι] (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) :
    haarUnitarizingMatrix h b =
      let G := (((coefficientMatrix (C := A) b).map star)ᴴ *
        (coefficientMatrix (C := A) b).map star).map h
      Real.sqrt (G⁻¹.trace.re / G.trace.re) • G := by
  rfl

end Coalgebra

/-- Two positive definite matrices with `Tr F = Tr F⁻¹` that differ by a scalar on a nonempty index
type are equal. -/
private theorem eq_of_posDef_of_trace_eq_of_eq_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.PosDef) (ht₁ : F₁.trace = F₁⁻¹.trace)
    (hF₂ : F₂.PosDef) (ht₂ : F₂.trace = F₂⁻¹.trace) {c : ℂ} (hc : F₂ = c • F₁) :
    F₁ = F₂ := by
  have htr₁ : 0 < F₁.trace := hF₁.trace_pos
  have htr₂ : 0 < F₂.trace := hF₂.trace_pos
  have htr₁_ne : F₁.trace ≠ 0 := htr₁.ne'
  have hc_trace : F₂.trace = c * F₁.trace := by rw [hc, Matrix.trace_smul, smul_eq_mul]
  have hc_ne : c ≠ 0 := fun h0 ↦ htr₂.ne' (by simp [hc_trace, h0])
  have hdet₁ : IsUnit F₁.det := (Matrix.isUnit_iff_isUnit_det F₁).mp hF₁.isUnit
  have hinv₂ : F₂⁻¹ = c⁻¹ • F₁⁻¹ := by
    rw [hc]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc_ne, one_smul,
      Matrix.mul_nonsing_inv F₁ hdet₁]
  have hsq : c * F₁.trace = c⁻¹ * F₁.trace := by
    calc c * F₁.trace = F₂.trace := hc_trace.symm
      _ = F₂⁻¹.trace := ht₂
      _ = c⁻¹ * F₁⁻¹.trace := by rw [hinv₂, Matrix.trace_smul, smul_eq_mul]
      _ = c⁻¹ * F₁.trace := by rw [← ht₁]
  have hcc : c * c = 1 := by
    have h1 : c = c⁻¹ := mul_right_cancel₀ htr₁_ne hsq
    exact (inv_mul_cancel₀ hc_ne) ▸ congrArg (· * c) h1
  rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
  · simp [hc]
  · exfalso
    have hneg : F₂.trace = -F₁.trace := by simpa using hc_trace
    have : (0 : ℂ) < 0 := by
      calc (0 : ℂ) < F₁.trace + F₂.trace := add_pos htr₁ htr₂
        _ = 0 := by rw [hneg, add_neg_cancel]
    exact lt_irrefl 0 this

section UnitarizingMatrix

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι]

attribute [local instance] Comodule.dual

/-- For a basis with unitary coefficient matrix, the Haar Gram matrix of the dual basis in the
dual comodule is `(((coefficientMatrix b).map star)ᴴ * (coefficientMatrix b).map star).map h`. -/
theorem haarGramMatrix_dualBasis_of_mem_unitary [FiniteDimensional ℂ M] [DecidableEq ι]
    (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    haarGramMatrix h b.dualBasis =
      (((coefficientMatrix (C := A) b).map star)ᴴ *
        (coefficientMatrix (C := A) b).map star).map h := by
  ext j l
  simp [haarGramMatrix_apply, b.coefficientMatrix_dualBasis_of_mem_unitary hu, Matrix.mul_apply]

/-- Any invertible scalar matrix `F` preserved under `ūᴴ F ū = F` for a unitary coefficient matrix
`u` satisfies the dual identity `ū F⁻¹ ūᴴ = F⁻¹`. -/
theorem map_star_mul_inv_mul_conjTranspose_of_conjTranspose_map_star_mul_eq [DecidableEq ι]
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {F : Matrix ι ι ℂ} (hF : IsUnit F)
    (hinv : ((coefficientMatrix (C := A) b).map star)ᴴ * F.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = F.map (algebraMap ℂ A)) :
    (coefficientMatrix (C := A) b).map star * F⁻¹.map (algebraMap ℂ A) *
        ((coefficientMatrix (C := A) b).map star)ᴴ =
      F⁻¹.map (algebraMap ℂ A) := by
  have : FiniteDimensional ℂ M := Module.Finite.of_basis b
  set f := algebraMap ℂ A
  set ub := (coefficientMatrix (C := A) b).map star
  have hdet : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hFF : F.map f * F⁻¹.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv F hdet, Matrix.map_one f (map_zero f) (map_one f)]
  have hFinvF : F⁻¹.map f * F.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul F hdet, Matrix.map_one f (map_zero f) (map_one f)]
  have hleft : (F⁻¹.map f * ubᴴ * F.map f) * ub = 1 := by
    calc (F⁻¹.map f * ubᴴ * F.map f) * ub
        = F⁻¹.map f * (ubᴴ * F.map f * ub) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinv, hFinvF]
  have hright_S : ub * ub.map (HopfAlgebra.antipode ℂ) = 1 := by
    have hub : coefficientMatrix (C := A) b.dualBasis = ub :=
      b.coefficientMatrix_dualBasis_of_mem_unitary hu
    simpa only [hub] using coefficientMatrix_mul_map_antipode (C := A) b.dualBasis
  have hLR : F⁻¹.map f * ubᴴ * F.map f = ub.map (HopfAlgebra.antipode ℂ) :=
    left_inv_eq_right_inv hleft hright_S
  have hright : ub * (F⁻¹.map f * ubᴴ * F.map f) = 1 := hLR.symm ▸ hright_S
  calc ub * F⁻¹.map f * ubᴴ
      = ub * (F⁻¹.map f * ubᴴ * F.map f) * F⁻¹.map f := by
        simp only [Matrix.mul_assoc, hFF, Matrix.mul_one]
    _ = F⁻¹.map f := by rw [hright, Matrix.one_mul]

variable [StarModule ℂ A]

/-- **Uniqueness of the unitarizing matrix.** For a simple comodule `M` with a unitary coefficient
matrix `u` in basis `b`, there is at most one positive definite matrix `F` satisfying
`Tr F = Tr F⁻¹` and `ūᴴ F ū = F`. -/
theorem eq_of_posDef_of_trace_eq_of_conjTranspose_map_star_mul_eq
    [IsSimpleOrder (Subcomodule ℂ A M)] [DecidableEq ι]
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {F₁ F₂ : Matrix ι ι ℂ}
    (hF₁ : F₁.PosDef) (ht₁ : F₁.trace = F₁⁻¹.trace)
    (hinv₁ : ((coefficientMatrix (C := A) b).map star)ᴴ * F₁.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = F₁.map (algebraMap ℂ A))
    (hF₂ : F₂.PosDef) (ht₂ : F₂.trace = F₂⁻¹.trace)
    (hinv₂ : ((coefficientMatrix (C := A) b).map star)ᴴ * F₂.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = F₂.map (algebraMap ℂ A)) :
    F₁ = F₂ := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  set f := algebraMap ℂ A
  set u := coefficientMatrix (C := A) b
  set ub := u.map star
  set X : Matrix ι ι ℂ := F₁⁻¹ * F₂
  have hXmap : X.map f = F₁⁻¹.map f * F₂.map f := Matrix.map_mul
  have hdual₁ :=
    map_star_mul_inv_mul_conjTranspose_of_conjTranspose_map_star_mul_eq b hu hF₁.isUnit hinv₁
  -- Combine `ū F₁⁻¹ ūᴴ = F₁⁻¹` and `ūᴴ F₂ ū = F₂` to see that `X = F₁⁻¹ F₂` commutes with `ū`.
  have hcomm_ub : ub * X.map f = X.map f * ub := by
    have hmul : ub * F₁⁻¹.map f * ubᴴ * (F₂.map f * ub) = F₁⁻¹.map f * (F₂.map f * ub) :=
      congrArg (· * (F₂.map f * ub)) hdual₁
    calc ub * X.map f
        = ub * F₁⁻¹.map f * (ubᴴ * F₂.map f * ub) := by
          rw [hinv₂, hXmap, Matrix.mul_assoc]
      _ = (ub * F₁⁻¹.map f * ubᴴ) * (F₂.map f * ub) := by simp only [Matrix.mul_assoc]
      _ = F₁⁻¹.map f * (F₂.map f * ub) := hmul
      _ = X.map f * ub := by rw [← Matrix.mul_assoc, ← hXmap]
  -- Entrywise star turns commutation with `ū` into commutation of `X.map star` with `u`.
  have hcomm_u : u * (X.map star).map f = (X.map star).map f * u := by
    ext i k
    have hik := congrArg star (congrFun (congrFun hcomm_ub i) k)
    simp only [f, ub, Matrix.mul_apply, Matrix.map_apply, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, smul_mul_assoc, one_mul, mul_one, star_sum, star_smul, star_star] at hik ⊢
    exact hik
  obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm_u
  have hX : X = star c • 1 := by
    ext i j
    have hij := congrArg star (congrFun (congrFun hc i) j)
    simpa [Matrix.one_apply, apply_ite] using hij
  have hF₂_eq : F₂ = star c • F₁ := by
    have hdet₁ : IsUnit F₁.det := (Matrix.isUnit_iff_isUnit_det F₁).mp hF₁.isUnit
    calc F₂ = F₁ * X := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv F₁ hdet₁, Matrix.one_mul]
      _ = star c • F₁ := by rw [hX, Matrix.mul_smul, Matrix.mul_one]
  exact eq_of_posDef_of_trace_eq_of_eq_smul hF₁ ht₁ hF₂ ht₂ hF₂_eq

variable {h : A →ₗ[ℂ] ℂ}

private theorem posDef_conjHaarGramMatrix [DecidableEq ι] (hr : h.IsRightInvariantIntegral)
    (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (conjHaarGramMatrix h b).PosDef := by
  have : FiniteDimensional ℂ M := Module.Finite.of_basis b
  have hG : haarGramMatrix h b.dualBasis = conjHaarGramMatrix h b :=
    haarGramMatrix_dualBasis_of_mem_unitary h b hu
  rw [← hG]
  exact posDef_haarGramMatrix (fun a ↦ hr.map_star_mul_self_pos h0 hpos) b.dualBasis

/-- For a nonzero positive right invariant integral, the unitarizing matrix of a basis with unitary
coefficient matrix is positive definite. -/
theorem posDef_haarUnitarizingMatrix [DecidableEq ι] (hr : h.IsRightInvariantIntegral)
    (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (haarUnitarizingMatrix h b).PosDef := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨Subsingleton.elim _ _, fun x hx ↦ False.elim (hx (Subsingleton.elim x 0))⟩
  · have hG := posDef_conjHaarGramMatrix hr h0 hpos b hu
    have ht₁ : 0 < (conjHaarGramMatrix h b).trace.re :=
      (Complex.pos_iff.mp hG.trace_pos).1
    have ht₂ : 0 < (conjHaarGramMatrix h b)⁻¹.trace.re :=
      (Complex.pos_iff.mp hG.inv.trace_pos).1
    have hsqrt : 0 < Real.sqrt ((conjHaarGramMatrix h b)⁻¹.trace.re /
        (conjHaarGramMatrix h b).trace.re) :=
      Real.sqrt_pos.mpr (div_pos ht₂ ht₁)
    exact hG.smul hsqrt

/-- The unitarizing matrix is normalized so that its trace equals the trace of its inverse. -/
theorem trace_haarUnitarizingMatrix_eq_trace_inv [DecidableEq ι] (hr : h.IsRightInvariantIntegral)
    (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (haarUnitarizingMatrix h b).trace = (haarUnitarizingMatrix h b)⁻¹.trace := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Matrix.trace]
  · set G := conjHaarGramMatrix h b
    have hG : G.PosDef := posDef_conjHaarGramMatrix hr h0 hpos b hu
    have htrG : 0 < G.trace := hG.trace_pos
    have htrGinv : 0 < G⁻¹.trace := hG.inv.trace_pos
    obtain ⟨ht₁, _⟩ := Complex.pos_iff.mp htrG
    obtain ⟨ht₂, _⟩ := Complex.pos_iff.mp htrGinv
    set r : ℝ := Real.sqrt (G⁻¹.trace.re / G.trace.re)
    have hr_pos : 0 < r := Real.sqrt_pos.mpr (div_pos ht₂ ht₁)
    have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
    have hEq : haarUnitarizingMatrix h b = (r : ℂ) • G := by
      ext i j
      simp [haarUnitarizingMatrix_def, G, conjHaarGramMatrix, r, Complex.real_smul]
    have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
    have hInv : (haarUnitarizingMatrix h b)⁻¹ = (r : ℂ)⁻¹ • G⁻¹ := by
      rw [hEq]
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hr_ne, one_smul,
        Matrix.mul_nonsing_inv G hGdet]
    have hG_re : G.trace = (G.trace.re : ℂ) := Complex.eq_re_of_ofReal_le htrG.le
    have hGinv_re : G⁻¹.trace = (G⁻¹.trace.re : ℂ) := Complex.eq_re_of_ofReal_le htrGinv.le
    have hreal : r * G.trace.re = r⁻¹ * G⁻¹.trace.re := by
      have hs₁ : (Real.sqrt G.trace.re) ≠ 0 := (Real.sqrt_pos.mpr ht₁).ne'
      have hs₂ : (Real.sqrt G⁻¹.trace.re) ≠ 0 := (Real.sqrt_pos.mpr ht₂).ne'
      have hr_div : r = Real.sqrt G⁻¹.trace.re / Real.sqrt G.trace.re :=
        Real.sqrt_div ht₂.le G.trace.re
      rw [hr_div, inv_div]
      field_simp [hs₁, hs₂]
      rw [Real.sq_sqrt ht₁.le, Real.sq_sqrt ht₂.le, mul_comm]
    rw [hInv, hEq, Matrix.trace_smul, Matrix.trace_smul, hG_re, hGinv_re]
    simpa [smul_eq_mul] using congrArg Complex.ofReal hreal

variable [StarCoalgebra ℂ A]

private theorem conjTranspose_map_star_mul_conjHaarGramMatrix_mul [DecidableEq ι]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ((coefficientMatrix (C := A) b).map star)ᴴ *
        (conjHaarGramMatrix h b).map (algebraMap ℂ A) *
          (coefficientMatrix (C := A) b).map star =
      (conjHaarGramMatrix h b).map (algebraMap ℂ A) := by
  have : FiniteDimensional ℂ M := Module.Finite.of_basis b
  have hG : haarGramMatrix h b.dualBasis = conjHaarGramMatrix h b :=
    haarGramMatrix_dualBasis_of_mem_unitary h b hu
  have hdu := b.coefficientMatrix_dualBasis_of_mem_unitary hu
  rw [← hG, ← hdu]
  exact conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul hr b.dualBasis

/-- **Haar invariance of the unitarizing matrix.** For a right invariant integral `h` and a basis
`b` with unitary coefficient matrix `u`, the entrywise conjugate `ū = u.map star` preserves
`haarUnitarizingMatrix h b`: `ūᴴ Ft ū = Ft`. -/
theorem conjTranspose_map_star_mul_haarUnitarizingMatrix_mul [DecidableEq ι]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ((coefficientMatrix (C := A) b).map star)ᴴ *
        (haarUnitarizingMatrix h b).map (algebraMap ℂ A) *
          (coefficientMatrix (C := A) b).map star =
      (haarUnitarizingMatrix h b).map (algebraMap ℂ A) := by
  set r : ℂ := (Real.sqrt (((conjHaarGramMatrix h b)⁻¹.trace.re) /
    (conjHaarGramMatrix h b).trace.re) : ℂ)
  have hmap : (haarUnitarizingMatrix h b).map (algebraMap ℂ A) =
      r • (conjHaarGramMatrix h b).map (algebraMap ℂ A) := by
    have hFt : haarUnitarizingMatrix h b =
        Real.sqrt ((conjHaarGramMatrix h b)⁻¹.trace.re / (conjHaarGramMatrix h b).trace.re) •
          conjHaarGramMatrix h b := rfl
    ext i j
    simp [hFt, r, Complex.real_smul, Algebra.algebraMap_eq_smul_one, smul_smul]
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul,
    conjTranspose_map_star_mul_conjHaarGramMatrix_mul hr b hu]

/-- The inverse of `haarUnitarizingMatrix h b` satisfies `ū Ft⁻¹ ūᴴ = Ft⁻¹`. -/
theorem map_star_mul_inv_haarUnitarizingMatrix_mul_conjTranspose [DecidableEq ι]
    (hr : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (coefficientMatrix (C := A) b).map star *
        (haarUnitarizingMatrix h b)⁻¹.map (algebraMap ℂ A) *
          ((coefficientMatrix (C := A) b).map star)ᴴ =
      (haarUnitarizingMatrix h b)⁻¹.map (algebraMap ℂ A) :=
  map_star_mul_inv_mul_conjTranspose_of_conjTranspose_map_star_mul_eq b hu
    (posDef_haarUnitarizingMatrix hr h0 hpos b hu).isUnit
    (conjTranspose_map_star_mul_haarUnitarizingMatrix_mul hr b hu)

/-- **Existence and uniqueness of the normalized unitarizing matrix.** For a simple comodule `M`
with unitary coefficient matrix `u` over a complex Hopf star algebra admitting a nonzero positive
right invariant integral, there is a unique positive definite matrix `Ft` satisfying
`Tr Ft = Tr Ft⁻¹` and `ūᴴ Ft ū = Ft`, namely `haarUnitarizingMatrix h b`. -/
theorem existsUnique_posDef_trace_eq_conjTranspose_map_star_mul_eq
    [IsSimpleOrder (Subcomodule ℂ A M)] [DecidableEq ι]
    (hr : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) := by
  refine ⟨haarUnitarizingMatrix h b,
    ⟨posDef_haarUnitarizingMatrix hr h0 hpos b hu,
      trace_haarUnitarizingMatrix_eq_trace_inv hr h0 hpos b hu,
      conjTranspose_map_star_mul_haarUnitarizingMatrix_mul hr b hu⟩, ?_⟩
  rintro F ⟨hF, ht, hinv⟩
  exact (eq_of_posDef_of_trace_eq_of_conjTranspose_map_star_mul_eq b hu
    (posDef_haarUnitarizingMatrix hr h0 hpos b hu)
    (trace_haarUnitarizingMatrix_eq_trace_inv hr h0 hpos b hu)
    (conjTranspose_map_star_mul_haarUnitarizingMatrix_mul hr b hu) hF ht hinv).symm

/-- On a simple comodule with unitary coefficient matrix, `haarUnitarizingMatrix h b` does not
depend on the choice of nonzero positive right invariant integral `h`. -/
theorem haarUnitarizingMatrix_eq_haarUnitarizingMatrix
    [IsSimpleOrder (Subcomodule ℂ A M)] [DecidableEq ι]
    {h₁ h₂ : A →ₗ[ℂ] ℂ}
    (hr₁ : h₁.IsRightInvariantIntegral) (h0₁ : h₁ ≠ 0) (hpos₁ : ∀ a, 0 ≤ h₁ (star a * a))
    (hr₂ : h₂.IsRightInvariantIntegral) (h0₂ : h₂ ≠ 0) (hpos₂ : ∀ a, 0 ≤ h₂ (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    haarUnitarizingMatrix h₁ b = haarUnitarizingMatrix h₂ b :=
  eq_of_posDef_of_trace_eq_of_conjTranspose_map_star_mul_eq b hu
    (posDef_haarUnitarizingMatrix hr₁ h0₁ hpos₁ b hu)
    (trace_haarUnitarizingMatrix_eq_trace_inv hr₁ h0₁ hpos₁ b hu)
    (conjTranspose_map_star_mul_haarUnitarizingMatrix_mul hr₁ b hu)
    (posDef_haarUnitarizingMatrix hr₂ h0₂ hpos₂ b hu)
    (trace_haarUnitarizingMatrix_eq_trace_inv hr₂ h0₂ hpos₂ b hu)
    (conjTranspose_map_star_mul_haarUnitarizingMatrix_mul hr₂ b hu)

end UnitarizingMatrix

end TauCeti.Comodule

/-! ### Orthonormal change of basis for the unitarizing matrix -/

namespace OrthonormalBasis

variable {A H ι κ : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  [StarCoalgebra ℂ A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Comodule ℂ A H]
  [IsSimpleOrder (Subcomodule ℂ A H)] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {h : A →ₗ[ℂ] ℂ}

/-- Under an orthonormal change of basis `c` from `b` with scalar change-of-basis matrix `U`, the
normalized unitarizing matrix `Ft` transforms by `Wᴴ Ft W`, where `W = U.map star` is the entrywise
complex conjugate of `U`. -/
theorem haarUnitarizingMatrix_eq (hr : h.IsRightInvariantIntegral) (h0 : h ≠ 0)
    (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : OrthonormalBasis ι ℂ H) (c : OrthonormalBasis κ ℂ H)
    (hu : coefficientMatrix (C := A) b.toBasis ∈ unitary (Matrix ι ι A)) :
    haarUnitarizingMatrix h c.toBasis =
      ((b.toBasis.toMatrix c.toBasis).map star)ᴴ *
        haarUnitarizingMatrix h b.toBasis *
          (b.toBasis.toMatrix c.toBasis).map star := by
  set U : Matrix ι κ ℂ := b.toBasis.toMatrix c.toBasis
  set W : Matrix ι κ ℂ := U.map star
  set Ft := haarUnitarizingMatrix h b.toBasis
  have hFt : Ft.PosDef := posDef_haarUnitarizingMatrix hr h0 hpos b.toBasis hu
  have htFt : Ft.trace = Ft⁻¹.trace :=
    trace_haarUnitarizingMatrix_eq_trace_inv hr h0 hpos b.toBasis hu
  have hinvFt := conjTranspose_map_star_mul_haarUnitarizingMatrix_mul hr b.toBasis hu
  have hc_unit : coefficientMatrix (C := A) c.toBasis ∈ unitary (Matrix κ κ A) :=
    (b.coefficientMatrix_mem_unitary_iff c).mp hu
  have hW : W = U.map (starRingEnd ℂ) := rfl
  have hWW₁ : Wᴴ * W = 1 := by
    rw [hW, ← Matrix.conjTranspose_map (starRingEnd ℂ) (fun _ ↦ rfl), ← Matrix.map_mul]
    simp [U]
  have hWW₂ : W * Wᴴ = 1 := by
    rw [hW, ← Matrix.conjTranspose_map (starRingEnd ℂ) (fun _ ↦ rfl), ← Matrix.map_mul]
    simp [U]
  have hWinj : Function.Injective W.mulVec := fun x y hxy ↦ by
    simpa [mulVec_mulVec, hWW₁] using congrArg Wᴴ.mulVec hxy
  set Fc : Matrix κ κ ℂ := Wᴴ * Ft * W
  have hFc_pos : Fc.PosDef := hFt.conjTranspose_mul_mul_same hWinj
  have hdetFt : IsUnit Ft.det := (Matrix.isUnit_iff_isUnit_det Ft).mp hFt.isUnit
  have hFc_inv : Fc⁻¹ = Wᴴ * Ft⁻¹ * W := by
    refine Matrix.inv_eq_right_inv ?_
    calc (Wᴴ * Ft * W) * (Wᴴ * Ft⁻¹ * W)
        = Wᴴ * Ft * (W * Wᴴ) * Ft⁻¹ * W := by simp only [Matrix.mul_assoc]
      _ = Wᴴ * (Ft * Ft⁻¹) * W := by simp only [hWW₂, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv Ft hdetFt, Matrix.mul_one, hWW₁]
  have hFc_trace : Fc.trace = Fc⁻¹.trace := by
    rw [hFc_inv, Matrix.trace_mul_cycle Wᴴ Ft W, Matrix.trace_mul_cycle Wᴴ Ft⁻¹ W,
      hWW₂, Matrix.one_mul, Matrix.one_mul, htFt]
  -- Entrywise star on `v = Uᴴ u U` gives `v.map star = Wᴴ ū W`, giving unitarization for `Fc`.
  set f := algebraMap ℂ A
  have hstar_f : Function.Semiconj f star star := algebraMap_star_comm
  have hWF : (W.map f) * (W.map f)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_map _ hstar_f, ← Matrix.map_mul, hWW₂,
      Matrix.map_one f (map_zero f) (map_one f)]
  have hvc : (coefficientMatrix (C := A) c.toBasis).map star =
      (W.map f)ᴴ * (coefficientMatrix (C := A) b.toBasis).map star * W.map f := by
    rw [b.coefficientMatrix_eq_conjTranspose_mul c]
    ext r s
    simp [W, U, f, Matrix.mul_apply, Algebra.algebraMap_eq_smul_one, star_sum, star_smul]
  have hFc_map : Fc.map f = (W.map f)ᴴ * Ft.map f * W.map f := by
    simp only [Fc, Matrix.map_mul, Matrix.conjTranspose_map _ hstar_f]
  have hFc_inv_eq :
      ((coefficientMatrix (C := A) c.toBasis).map star)ᴴ * Fc.map f *
          (coefficientMatrix (C := A) c.toBasis).map star =
        Fc.map f := by
    set ub := (coefficientMatrix (C := A) b.toBasis).map star
    have hinvFt' : ubᴴ * Ft.map f * ub = Ft.map f := hinvFt
    rw [hvc, hFc_map]
    calc ((W.map f)ᴴ * ub * W.map f)ᴴ * ((W.map f)ᴴ * Ft.map f * W.map f) *
            ((W.map f)ᴴ * ub * W.map f)
        = (W.map f)ᴴ * ubᴴ * (W.map f * (W.map f)ᴴ) * Ft.map f *
            (W.map f * (W.map f)ᴴ) * ub * W.map f := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (W.map f)ᴴ * (ubᴴ * Ft.map f * ub) * W.map f := by
          simp only [hWF, Matrix.mul_one, Matrix.mul_assoc]
      _ = (W.map f)ᴴ * Ft.map f * W.map f := by rw [hinvFt']
  exact eq_of_posDef_of_trace_eq_of_conjTranspose_map_star_mul_eq c.toBasis hc_unit
    (posDef_haarUnitarizingMatrix hr h0 hpos c.toBasis hc_unit)
    (trace_haarUnitarizingMatrix_eq_trace_inv hr h0 hpos c.toBasis hc_unit)
    (conjTranspose_map_star_mul_haarUnitarizingMatrix_mul hr c.toBasis hc_unit)
    hFc_pos hFc_trace hFc_inv_eq

end OrthonormalBasis

/-! ### Weighted Schur orthogonality -/

namespace TauCeti.Comodule

section SchurOrthogonality

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  [StarCoalgebra ℂ A] [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι] {h : A →ₗ[ℂ] ℂ}

/-- **Second weighted Schur orthogonality relation** (unnormalized form). For a simple comodule `M`
with unitary coefficient matrix `u` in basis `b` and a nonzero positive two-sided invariant
integral `h`,
`h (u i j * star (u k l)) = if i = k then h 1 * (Ft j l / Tr Ft) else 0`,
where `Ft = haarUnitarizingMatrix h b`. -/
theorem apply_coefficientMatrix_mul_star (hl : h.IsLeftInvariantIntegral)
    (hr : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j k l : ι) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
      if i = k then
        h 1 * (haarUnitarizingMatrix h b j l / (haarUnitarizingMatrix h b).trace)
      else 0 := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  set u := coefficientMatrix (C := A) b
  have hu₁ : uᴴ * u = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).1
  have hu₂ : u * uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  -- By left-Haar intertwining and Schur's lemma, `(i, k) ↦ h (u i j * star (u k l))` is scalar.
  obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_coefficientMatrix_mul_eq
    (hl.coefficientMatrix_mul_map_apply_mul_star b hu₁ j l)
  have hentry (i' k' : ι) : h (u i' j * star (u k' l)) = if i' = k' then c else 0 := by
    simpa [Matrix.one_apply] using congrFun (congrFun hc i') k'
  -- Summing the diagonal over `i'` relates `c` to the conjugate Gram matrix `G`.
  set G := conjHaarGramMatrix h b
  have hG_entry : G j l = (Fintype.card ι : ℂ) * c := by
    simp [G, u, conjHaarGramMatrix_apply, hentry]
  have hG_trace : G.trace = (Fintype.card ι : ℂ) * h 1 := by
    calc G.trace = ∑ j', h (∑ i', u i' j' * star (u i' j')) := by
          simp [Matrix.trace, G, u, conjHaarGramMatrix_apply]
      _ = ∑ i', h (∑ j', u i' j' * star (u i' j')) := by
          simp_rw [map_sum]
          rw [Finset.sum_comm]
      _ = ∑ _i' : ι, h 1 := by
          refine Finset.sum_congr rfl fun i' _ ↦ ?_
          have hrow : ∑ j', u i' j' * star (u i' j') = (1 : A) := by
            simpa only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq] using
              congrFun (congrFun hu₂ i') i'
          rw [hrow]
      _ = (Fintype.card ι : ℂ) * h 1 := by simp
  have hG_pos : G.PosDef := posDef_conjHaarGramMatrix hr h0 hpos b hu
  have ht₁ : 0 < G.trace.re := (Complex.pos_iff.mp hG_pos.trace_pos).1
  have ht₂ : 0 < G⁻¹.trace.re := (Complex.pos_iff.mp hG_pos.inv.trace_pos).1
  set r : ℝ := Real.sqrt (G⁻¹.trace.re / G.trace.re)
  have hr_ne : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos ht₂ ht₁)).ne'
  have hd_ne : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh1_ne : h 1 ≠ 0 := right_ne_zero_of_mul (hG_trace ▸ hG_pos.trace_pos.ne')
  have hc_eq : c = h 1 * (haarUnitarizingMatrix h b j l / (haarUnitarizingMatrix h b).trace) := by
    have hFt_eq : haarUnitarizingMatrix h b = r • G := rfl
    have hFt_jl : haarUnitarizingMatrix h b j l = (r : ℂ) * G j l := by
      rw [hFt_eq, Matrix.smul_apply, Complex.real_smul]
    have hFt_tr : (haarUnitarizingMatrix h b).trace = (r : ℂ) * G.trace := by
      rw [hFt_eq, Matrix.trace_smul, Complex.real_smul]
    rw [hFt_jl, hFt_tr, mul_div_mul_left _ _ hr_ne, hG_entry, hG_trace]
    field_simp [hd_ne, hh1_ne]
  rw [hentry, hc_eq]

/-- **First weighted Schur orthogonality relation** (unnormalized form). For a simple comodule `M`
with unitary coefficient matrix `u` in basis `b` and a nonzero positive right invariant integral
`h`,
`h (star (u i j) * u k l) = if j = l then h 1 * (Ft⁻¹ i k / Tr Ft⁻¹) else 0`,
where `Ft = haarUnitarizingMatrix h b`. -/
theorem apply_star_coefficientMatrix_mul
    (hr : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
      if j = l then
        h 1 * ((haarUnitarizingMatrix h b)⁻¹ i k / (haarUnitarizingMatrix h b)⁻¹.trace)
      else 0 := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  set u := coefficientMatrix (C := A) b
  set Ft := haarUnitarizingMatrix h b
  have hu₂ : u * uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  -- Right-Haar intertwining and Schur's lemma make
  -- `(l, j) ↦ star (h (star (u i j) * u k l))` scalar.
  have hd_mat (i' k' : ι) : ∃ d : ℂ, ∀ j' l' : ι,
      h (star (u i' j') * u k' l') = if j' = l' then d else 0 := by
    obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_coefficientMatrix_mul_eq
      (hr.coefficientMatrix_mul_map_star_apply_star_mul b hu₂ i' k')
    refine ⟨star c, fun j' l' ↦ ?_⟩
    have hlj := congrArg star (congrFun (congrFun hc l') j')
    simpa [u, Matrix.one_apply, apply_ite, eq_comm] using hlj
  obtain ⟨d, hd⟩ := hd_mat i k
  -- Apply `h` to the `(i, k)` entry of `ū Ft⁻¹ ūᴴ = Ft⁻¹` to solve for `d`.
  have hdual := map_star_mul_inv_haarUnitarizingMatrix_mul_conjTranspose hr h0 hpos b hu
  have hik := congrArg h (congrFun (congrFun hdual i) k)
  have hlhs :
      h (((u.map star) * Ft⁻¹.map (algebraMap ℂ A) * (u.map star)ᴴ) i k) =
        Ft⁻¹.trace * d := by
    simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, star_star,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, Finset.sum_mul, smul_mul_assoc, mul_one,
      map_sum, map_smul, smul_eq_mul, hd]
    calc ∑ l', ∑ j', Ft⁻¹ j' l' * (if j' = l' then d else 0)
        = ∑ l', Ft⁻¹ l' l' * d := by
          refine Finset.sum_congr rfl fun l' _ ↦ ?_
          simp
      _ = Ft⁻¹.trace * d := by rw [← Finset.sum_mul]; rfl
  have hrhs : h ((Ft⁻¹.map (algebraMap ℂ A)) i k) = Ft⁻¹ i k * h 1 := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hFt_inv_tr_ne : Ft⁻¹.trace ≠ 0 :=
    (posDef_haarUnitarizingMatrix hr h0 hpos b hu).inv.trace_pos.ne'
  have hd_eq : d = h 1 * (Ft⁻¹ i k / Ft⁻¹.trace) := by
    have hmul : Ft⁻¹.trace * d = Ft⁻¹ i k * h 1 := hlhs.symm.trans (hik.trans hrhs)
    apply mul_left_cancel₀ hFt_inv_tr_ne
    calc Ft⁻¹.trace * d = Ft⁻¹ i k * h 1 := hmul
      _ = Ft⁻¹.trace * (h 1 * (Ft⁻¹ i k / Ft⁻¹.trace)) := by
        field_simp [hFt_inv_tr_ne]
  rw [hd j l, hd_eq]

/-- **Weighted Schur orthogonality.** Let `A` be a complex Hopf star algebra, `h : A →ₗ[ℂ] ℂ` a
positive normalized (`h 1 = 1`) two-sided invariant integral, and `M` a simple comodule with a
finite basis `b` whose coefficient matrix `u` is unitary. Then there exists a unique positive
definite matrix `Ft : Matrix ι ι ℂ` with `Tr Ft = Tr Ft⁻¹` such that

* `h (star (u i j) * u k l) = if j = l then Ft⁻¹ i k / Tr Ft⁻¹ else 0`, and
* `h (u i j * star (u k l)) = if i = k then Ft j l / Tr Ft else 0`

for all `i, j, k, l : ι`; namely `Ft = haarUnitarizingMatrix h b`. -/
theorem schur_orthogonality (h1 : h 1 = 1) (hl : h.IsLeftInvariantIntegral)
    (hr : h.IsRightInvariantIntegral) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  have h0 : h ≠ 0 := fun hz ↦ one_ne_zero (h1.symm.trans (by simp [hz]))
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  set Ft₀ := haarUnitarizingMatrix h b
  have hFt₀_pos : Ft₀.PosDef := posDef_haarUnitarizingMatrix hr h0 hpos b hu
  have hFt₀_tr : Ft₀.trace = Ft₀⁻¹.trace :=
    trace_haarUnitarizingMatrix_eq_trace_inv hr h0 hpos b hu
  have h1_mul (i j k l : ι) :
      h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
        if j = l then Ft₀⁻¹ i k / Ft₀⁻¹.trace else 0 := by
    simpa [Ft₀, h1] using apply_star_coefficientMatrix_mul hr h0 hpos b hu i j k l
  have h2_mul (i j k l : ι) :
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₀ j l / Ft₀.trace else 0 := by
    simpa [Ft₀, h1] using apply_coefficientMatrix_mul_star hl hr h0 hpos b hu i j k l
  refine ⟨Ft₀, ⟨hFt₀_pos, hFt₀_tr, h1_mul, h2_mul⟩, ?_⟩
  rintro Ft ⟨hFt_pos, hFt_tr, _, hFt_mul₂⟩
  obtain ⟨i₀⟩ := b.index_nonempty
  have hFt_tr_ne : Ft.trace ≠ 0 := hFt_pos.trace_pos.ne'
  have hsmul : Ft = (Ft.trace / Ft₀.trace) • Ft₀ := by
    ext j l
    have heq : Ft j l / Ft.trace = Ft₀ j l / Ft₀.trace := by
      have a := hFt_mul₂ i₀ j i₀ l
      have b' := h2_mul i₀ j i₀ l
      simpa using a.symm.trans b'
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc Ft j l = (Ft j l / Ft.trace) * Ft.trace := (div_mul_cancel₀ _ hFt_tr_ne).symm
      _ = (Ft₀ j l / Ft₀.trace) * Ft.trace := by rw [heq]
      _ = Ft.trace / Ft₀.trace * Ft₀ j l := by ring
  exact (eq_of_posDef_of_trace_eq_of_eq_smul hFt₀_pos hFt₀_tr hFt_pos hFt_tr hsmul).symm

end SchurOrthogonality

section UnitaryComodule

variable {A H ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  [StarCoalgebra ℂ A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [Comodule ℂ A H] [IsSimpleOrder (Subcomodule ℂ A H)] [Fintype ι] [DecidableEq ι]
  {h : A →ₗ[ℂ] ℂ}

/-- **Weighted Schur orthogonality** for a simple finite-dimensional unitary comodule in any
orthonormal basis. -/
theorem IsUnitary.schur_orthogonality (hH : IsUnitary ℂ A H)
    (h1 : h 1 = 1) (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral)
    (hpos : ∀ a, 0 ≤ h (star a * a)) (b : OrthonormalBasis ι ℂ H) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b.toBasis i j) *
            coefficientMatrix (C := A) b.toBasis k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b.toBasis i j *
            star (coefficientMatrix (C := A) b.toBasis k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  Comodule.schur_orthogonality h1 hl hr hpos b.toBasis (hH.coefficientMatrix_mem_unitary b)

end UnitaryComodule

end TauCeti.Comodule
