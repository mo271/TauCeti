/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import Mathlib.Analysis.Analytic.Order
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Holomorphic stalks are unique factorization domains

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is a unique factorization domain (factorial local ring). By Mathlib's
`UniqueFactorizationMonoid.instIsIntegrallyClosed`, every holomorphic stalk is therefore also
integrally closed (normal).

The proof is by induction on the complex dimension `n = finrank ℂ E` using Rückert's abstract
factorial descent (`RingHom.IsRueckert.uniqueFactorizationMonoid`):

* For `n = 0`, the point is isolated and evaluation identifies `𝒪_{V, x}` with `ℂ`
  (`evalEquivOfNhdsEqPure`), which is a field and hence a UFD.
* On `V × ℂ`, the evaluation map `evalVertical x₀ w₀ : 𝒪_{V, x₀}[X] →+* 𝒪_{V × ℂ, (x₀, w₀)}`
  satisfies the Rückert hypotheses (`isRueckert_evalVertical`) for the set of polynomials
  distinguished at the maximal ideal of `𝒪_{V, x₀}`:
  - injectivity (`evalVertical_injective`) and divisibility reflection
    (`evalVertical_dvd_iff_of_isDistinguishedAt`) come from Weierstrass division;
  - closure under monic divisors follows from `Polynomial.IsDistinguishedAt.of_dvd` because the
    maximal ideal is prime, hence radical;
  - general position in the last variable is achieved at the *same* base point `(x₀, w₀)` by the
    affine coordinate change `y ↦ (x₀, w₀) + L (y - (x₀, w₀))`
    (`ContinuousLinearEquiv.holomorphicStalkAut`), deduced from
    `AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top` by translating along the
    vertical line (`exists_holomorphicStalkAut_map_residue_verticalPowerSeries_ne_zero`);
  - Weierstrass preparation (`existsUnique_weierstrassPreparation`) then writes the transformed
    germ as a unit multiple of a distinguished polynomial.
* Charts identify the stalk of any finite-dimensional complex manifold without boundary with a
  stalk of a model space in `Type` (`exists_ringEquiv_stalk_modelSpace`), and `smoothStalkIso`
  transfers factoriality to Mathlib's complex-smooth structure sheaf.

On `E × ℂ`, the file also exposes the divisibility and factorization dictionary between
distinguished polynomials in `𝒪_{E, x₀}[X]` and holomorphic germs in `𝒪_{E × ℂ, (x₀, w₀)}`:
reflection of units, associates, prime ideals, primality, irreducibility, relative primality
(with arbitrary second polynomial factor, e.g. a formal derivative), squarefreeness, divisors of
vertical-regular germs, and unique factorization of any vertical-regular germ into irreducible
distinguished polynomials and a unit.

## Main declarations

In `namespace TauCeti.holomorphicStructureSheaf`:

* `exists_holomorphicStalkAut_map_residue_verticalPowerSeries_ne_zero`: every nonzero germ at
  `(x₀, w₀)` becomes regular in the last variable after a point-fixing affine change of coordinates
  (without assuming finite-dimensionality).
* `map_residue_verticalPowerSeries_ne_zero_of_dvd`: any divisor of a vertical-regular germ is
  vertical-regular (without assuming finite-dimensionality).
* `associated_evalVertical_iff_of_isDistinguishedAt`,
  `isUnit_evalVertical_iff_of_isDistinguishedAt`: associates and units among distinguished
  polynomials (without assuming finite-dimensionality).
* `isRueckert_evalVertical`: `evalVertical x₀ w₀` satisfies `RingHom.IsRueckert` for the
  distinguished polynomials at the maximal ideal of `𝒪_{E, x₀}`.
* `stalkUniqueFactorizationMonoid`: holomorphic stalks are UFDs.
* `smoothStalkUniqueFactorizationMonoid`: so are stalks of Mathlib's complex-smooth structure
  sheaf.
* `existsUnique_isDistinguishedAt_associated_of_dvd`,
  `existsUnique_isDistinguishedAt_associated_of_dvd_evalVertical`: every divisor of a
  vertical-regular germ (or distinguished polynomial) is associated to a unique distinguished
  polynomial.
* `isPrime_span_evalVertical_iff_of_isDistinguishedAt`,
  `prime_evalVertical_iff_of_isDistinguishedAt`,
  `irreducible_evalVertical_iff_of_isDistinguishedAt`,
  `isRelPrime_evalVertical_iff_of_isDistinguishedAt`,
  `squarefree_evalVertical_iff_of_isDistinguishedAt`: equivalence of primality, irreducibility,
  relative primality, and squarefreeness in `𝒪_{E, x₀}[X]` and `𝒪_{E × ℂ, (x₀, w₀)}`.
* `existsUnique_multiset_isDistinguishedAt_irreducible_evalVertical`: unique factorization of a
  vertical-regular germ as a product of irreducible distinguished polynomials times a unit germ.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Ch. II, (2.10).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Ch. VI.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open Filter Module Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

/-! ### General normed-space facts (without finite-dimensionality) -/

section NormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **General position at a fixed point.** Every nonzero holomorphic germ `f` at `(x₀, w₀)`
becomes regular in the vertical variable after a point-fixing affine change of coordinates
`y ↦ (x₀, w₀) + L (y - (x₀, w₀))`, without assuming finite-dimensionality of `E`. -/
theorem exists_holomorphicStalkAut_map_residue_verticalPowerSeries_ne_zero {x₀ : E} {w₀ : ℂ}
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)} (hf : f ≠ 0) :
    ∃ L : (E × ℂ) ≃L[ℂ] (E × ℂ),
      (verticalPowerSeries x₀ w₀ (L.holomorphicStalkAut (x₀, w₀) f)).map
        (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 := by
  obtain ⟨F, hF, hfF⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) f
  obtain ⟨L, ⟨x₁, w₁⟩, hLq, hslice⟩ := hF.exists_continuousLinearEquiv_analyticOrderAt_ne_top
    ((eq_zero_iff_of_toFilterGerm_eq (hfF _ le_rfl)).not.1 hf)
  refine ⟨L, (map_residue_verticalPowerSeries_ne_zero_iff (g := L.holomorphicStalkAut (x₀, w₀) f)
    (G := fun y ↦ F ((x₀, w₀) + L (y - (x₀, w₀)))) ?_).2 ?_⟩
  · simp only [ContinuousLinearEquiv.toFilterGerm_holomorphicStalkAut, hfF _ le_rfl,
      Germ.coe_compTendsto]
    rfl
  · -- Along `w ↦ (x₀, w)`, the affine map `(x₀, w₀) + L (· - (x₀, w₀))` translates the vertical
    -- line `t ↦ L (x₁, t)` by `w ↦ w₁ + (w - w₀)`, which has derivative `1 ≠ 0`.
    have heq : (fun w : ℂ ↦ F ((x₀, w₀) + L ((x₀, w) - (x₀, w₀)))) =
        (fun t : ℂ ↦ F (L (x₁, t))) ∘ (fun w : ℂ ↦ w₁ + (w - w₀)) := by
      ext w
      rw [Prod.mk_sub_mk, sub_self, ← hLq, ← map_add, Prod.mk_add_mk, add_zero]
      rfl
    have hg : AnalyticAt ℂ (fun w : ℂ ↦ w₁ + (w - w₀)) w₀ := by fun_prop
    have hg' : deriv (fun w : ℂ ↦ w₁ + (w - w₀)) w₀ ≠ 0 := by
      have hd : HasDerivAt (fun w : ℂ ↦ w₁ + (w - w₀)) 1 w₀ :=
        ((hasDerivAt_id w₀).sub_const w₀).const_add w₁
      rw [hd.deriv]
      exact one_ne_zero
    rw [heq, analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    simpa using hslice

/-- Every divisor of a holomorphic germ whose vertical power series has nonzero reduction modulo
the maximal ideal also has nonzero reduction modulo the maximal ideal. -/
theorem map_residue_verticalPowerSeries_ne_zero_of_dvd {x₀ : E} {w₀ : ℂ}
    {f g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0)
    (hgf : g ∣ f) :
    (verticalPowerSeries x₀ w₀ g).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 := by
  rintro hg0
  obtain ⟨h, rfl⟩ := hgf
  apply hf
  rw [map_mul, map_mul, hg0, zero_mul]

/-- Two distinguished polynomials over `𝒪_{E, x₀}` have associated images under `evalVertical x₀ w₀`
if and only if they are equal (without assuming finite-dimensionality of `E`). -/
theorem associated_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hQ : Q.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Associated (evalVertical x₀ w₀ P) (evalVertical x₀ w₀ Q) ↔ P = Q :=
  ⟨fun ⟨u, hu⟩ ↦
    (weierstrassPreparation_unique hP u.isUnit hu.symm hQ isUnit_one (mul_one _).symm).1,
    by rintro rfl; exact Associated.refl _⟩

/-- A distinguished polynomial over `𝒪_{E, x₀}` maps to a unit under `evalVertical x₀ w₀` if and
only if it is `1` (without assuming finite-dimensionality of `E`). -/
theorem isUnit_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    IsUnit (evalVertical x₀ w₀ P) ↔ P = 1 := by
  rw [← associated_one_iff_isUnit, ← map_one (evalVertical x₀ w₀)]
  exact associated_evalVertical_iff_of_isDistinguishedAt hP Polynomial.isDistinguishedAt_one

end NormedSpace

/-! ### Rückert hypotheses and dimension induction -/

section Rueckert

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- On `V × ℂ` with `V` finite-dimensional, `evalVertical x₀ w₀` satisfies the Rückert hypotheses
(`RingHom.IsRueckert`) for the set of polynomials distinguished at the maximal ideal of
`𝒪_{V, x₀}`. -/
theorem isRueckert_evalVertical [FiniteDimensional ℂ V] (x₀ : V) (w₀ : ℂ) :
    (evalVertical x₀ w₀).IsRueckert
      {P | P.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x₀))} where
  injective := evalVertical_injective x₀ w₀
  monic hw := hw.monic
  mem_of_dvd hw hp hpw :=
    hw.of_dvd (IsLocalRing.maximalIdeal.isMaximal _).isPrime.isRadical hp hpw
  dvd_iff hw p := (evalVertical_dvd_iff_of_isDistinguishedAt hw).symm
  exists_dvd_sub hw b := by
    obtain ⟨⟨q, r⟩, ⟨-, hdiv⟩, -⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hw b
    exact ⟨r, q, by rw [hdiv, add_sub_cancel_right]⟩
  exists_mul_eq hb := by
    obtain ⟨L, hL⟩ := exists_holomorphicStalkAut_map_residue_verticalPowerSeries_ne_zero hb
    obtain ⟨⟨P, u⟩, ⟨hP, hu, hfac⟩, -⟩ := existsUnique_weierstrassPreparation hL
    refine ⟨L.holomorphicStalkAut (x₀, w₀), hu.unit⁻¹, P, hP, ?_⟩
    rw [hfac, mul_left_comm]
    simp

/-- On a zero-dimensional complex normed space, evaluation identifies every holomorphic stalk
with `ℂ`, which is a unique factorization domain. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq_zero [FiniteDimensional ℂ V]
    (hV : finrank ℂ V = 0) (x : V) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) := by
  have : Subsingleton V := finrank_zero_iff.1 hV
  exact (evalEquivOfNhdsEqPure 𝓘(ℂ, V) V (congrFun (nhds_discrete V) x)).symm.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

/-- Holomorphic stalks of a finite-dimensional complex normed space are unique factorization
domains, by induction on the dimension through Rückert's factorial descent. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ x : V,
        UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x)
  | 0, _, _, _, _, hV, x => uniqueFactorizationMonoid_stalk_of_finrank_eq_zero hV x
  | n + 1, V, _, _, _, hV, x => by
    let e : V ≃L[ℂ] (Fin n → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hV])
    have : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk (e x).1) :=
      uniqueFactorizationMonoid_stalk_of_finrank_eq n (Fin n → ℂ) (by simp) (e x).1
    have hprod : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ) ((Fin n → ℂ) × ℂ)).presheaf.stalk
          (e x)) :=
      (isRueckert_evalVertical (e x).1 (e x).2).uniqueFactorizationMonoid
    exact (RingEquiv.ofBijective _ (e.holomorphicStalkPullback_bijective x)).toMulEquiv
      |>.uniqueFactorizationMonoid hprod

end Rueckert

/-! ### Factoriality of holomorphic stalks on complex manifolds -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a unique factorization domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  obtain ⟨V, _, _, _, v, -, ⟨φ⟩⟩ := exists_ringEquiv_stalk_modelSpace (I := I) x
  have hV := uniqueFactorizationMonoid_stalk_of_finrank_eq _ V rfl v
  exact φ.toMulEquiv.uniqueFactorizationMonoid hV

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorization domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end Manifold

/-! ### Divisibility, primality, and factorization for distinguished polynomials -/

section DistinguishedFactorization

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Every divisor of a holomorphic germ regular in the vertical variable is associated to a unique
distinguished polynomial over `𝒪_{E, x₀}`. -/
theorem existsUnique_isDistinguishedAt_associated_of_dvd {x₀ : E} {w₀ : ℂ}
    {f g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0)
    (hgf : g ∣ f) :
    ∃! Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X],
      Q.IsDistinguishedAt
          (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ∧
        Associated (evalVertical x₀ w₀ Q) g := by
  have hg := map_residue_verticalPowerSeries_ne_zero_of_dvd hf hgf
  obtain ⟨⟨Q, u⟩, ⟨hQ, hu, hg_eq⟩, -⟩ := existsUnique_weierstrassPreparation hg
  have hassoc : Associated (evalVertical x₀ w₀ Q) g := ⟨hu.unit, hg_eq.symm⟩
  refine ⟨Q, ⟨hQ, hassoc⟩, ?_⟩
  rintro Q' ⟨hQ', hassoc'⟩
  exact (associated_evalVertical_iff_of_isDistinguishedAt hQ' hQ).mp (hassoc'.trans hassoc.symm)

/-- Every divisor of `evalVertical x₀ w₀ P` for a distinguished polynomial `P` is associated to a
unique distinguished polynomial `Q`, which divides `P` in `𝒪_{E, x₀}[X]`. -/
theorem existsUnique_isDistinguishedAt_associated_of_dvd_evalVertical {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hg : g ∣ evalVertical x₀ w₀ P) :
    ∃! Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X],
      Q.IsDistinguishedAt
          (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ∧
        Q ∣ P ∧ Associated (evalVertical x₀ w₀ Q) g :=
  (isRueckert_evalVertical x₀ w₀).existsUnique_associated_of_dvd_apply hP hg

/-- For a distinguished polynomial `P`, the principal ideal `(evalVertical x₀ w₀ P)` in
`𝒪_{E × ℂ, (x₀, w₀)}` is prime if and only if `(P)` in `𝒪_{E, x₀}[X]` is prime. -/
theorem isPrime_span_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (Ideal.span {evalVertical x₀ w₀ P}).IsPrime ↔ (Ideal.span {P}).IsPrime :=
  (isRueckert_evalVertical x₀ w₀).isPrime_span_apply_iff hP

/-- For a distinguished polynomial `P`, `evalVertical x₀ w₀ P` is prime in `𝒪_{E × ℂ, (x₀, w₀)}`
if and only if `P` is prime in `𝒪_{E, x₀}[X]`. -/
theorem prime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Prime (evalVertical x₀ w₀ P) ↔ Prime P :=
  (isRueckert_evalVertical x₀ w₀).prime_apply_iff hP

/-- For a distinguished polynomial `P`, `evalVertical x₀ w₀ P` is irreducible in
`𝒪_{E × ℂ, (x₀, w₀)}` if and only if `P` is irreducible in `𝒪_{E, x₀}[X]`. -/
theorem irreducible_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P :=
  (isRueckert_evalVertical x₀ w₀).irreducible_apply_iff hP

/-- A distinguished polynomial `P` and an arbitrary polynomial `Q : 𝒪_{E, x₀}[X]` (for instance,
`Polynomial.derivative P`) are relatively prime in `𝒪_{E, x₀}[X]` if and only if their images
under `evalVertical x₀ w₀` are relatively prime in `𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem isRelPrime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]) :
    IsRelPrime (evalVertical x₀ w₀ P) (evalVertical x₀ w₀ Q) ↔ IsRelPrime P Q :=
  (isRueckert_evalVertical x₀ w₀).isRelPrime_apply_iff hP Q

/-- A distinguished polynomial `P` is squarefree in `𝒪_{E, x₀}[X]` if and only if
`evalVertical x₀ w₀ P` is squarefree in `𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem squarefree_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Squarefree (evalVertical x₀ w₀ P) ↔ Squarefree P :=
  (isRueckert_evalVertical x₀ w₀).squarefree_apply_iff hP

/-- **Unique Weierstrass factorization into irreducible distinguished polynomials.** Every
holomorphic germ `f` at `(x₀, w₀)` regular in the vertical variable factors uniquely as
`f = (s.map (evalVertical x₀ w₀)).prod * u`, where `s` is a multiset of irreducible distinguished
polynomials over `𝒪_{E, x₀}` and `u` is a unit germ at `(x₀, w₀)`. -/
theorem existsUnique_multiset_isDistinguishedAt_irreducible_evalVertical {x₀ : E} {w₀ : ℂ}
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0) :
    ∃! su : Multiset (((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]) ×
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
      (∀ Q ∈ su.1, Q.IsDistinguishedAt
          (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ∧
          Irreducible Q) ∧
        IsUnit su.2 ∧ f = (su.1.map (evalVertical x₀ w₀)).prod * su.2 := by
  obtain ⟨⟨P, u⟩, ⟨hP, hu, hf_eq⟩, -⟩ := existsUnique_weierstrassPreparation hf
  have hm : (IsLocalRing.maximalIdeal
      ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)).IsRadical :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime.isRadical
  obtain ⟨s, ⟨hs, hs_prod⟩, huniq_s⟩ := hP.existsUnique_multiset_irreducible_prod_eq hm
  refine ⟨(s, u), ⟨hs, hu, ?_⟩, ?_⟩
  · rw [← map_multiset_prod, hs_prod, hf_eq]
  · rintro ⟨t, v⟩ ⟨ht, hv, hft⟩
    have ht_dist : t.prod.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) :=
      Polynomial.isDistinguishedAt_multiset_prod fun Q hQ ↦ (ht Q hQ).1
    obtain ⟨htP, hvu⟩ := weierstrassPreparation_unique ht_dist hv
      (by rwa [map_multiset_prod]) hP hu hf_eq
    exact Prod.ext (huniq_s t ⟨ht, htP⟩) hvu

end DistinguishedFactorization

end TauCeti.holomorphicStructureSheaf
