/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Module.GradedModule.PieceFinite
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The Hilbert–Serre theorem for integer-graded modules over Artinian rings

Let `A` be a commutative Artinian ring and let `M` be a finitely generated module over the
polynomial ring `MvPolynomial σ A` in finitely many variables (`[Fintype σ]`), equipped with an
internal `ℤ`-grading `ℳ : ℤ → Submodule A M` compatible with the homogeneous polynomial grading.
This file proves the Hilbert–Serre theorem (`TauCeti.hilbertSerre`):

1. Every homogeneous piece `ℳ d` is a finitely generated `A`-module of finite `A`-length
   (`Module.length A (ℳ d) ≠ ⊤`), and `ℳ d = ⊥` for all `d` below a uniform integer `d₀`.
2. For *every* integer `d₀`, multiplying the shifted Hilbert series
   `∑_{n ≥ 0} length_A(ℳ (d₀ + n)) Xⁿ ∈ ℤ⟦X⟧` by `(1 - X) ^ Fintype.card σ` yields an integer
   polynomial `h : ℤ[X]` (`TauCeti.InternalGrading.exists_hilbertSeries_mul_one_sub_X_pow_eq`).
3. Consequently, `G := InternalGrading.ofDecomposition ℳ` admits a unique rational Hilbert
   polynomial `G.hilbertPoly : ℚ[X]` of degree `< Fintype.card σ` agreeing with
   `d ↦ length_A(ℳ d)` for all sufficiently large `d : ℤ`; moreover `G.hilbertPoly` belongs to
   `TauCeti.ringChooseSpan (Polynomial.X : ℚ[X])` and therefore takes integer values at *all*
   integers (`TauCeti.InternalGrading.hasHilbertPoly_mvPolynomial`).

No characteristic assumption is placed on `A`: the rational binomial polynomial lives over `ℚ`
after casting the integer numerator `h : ℤ[X]`. Restricting scalars along `MvPolynomial.aeval`
extends the theorem to any commutative `ℕ`-graded `A`-algebra generated over `A` by finitely many
degree-one elements (`TauCeti.hilbertSerre_of_adjoin_grade_one`), and specializing `A` to a field
`k` expresses the coefficients as `Module.finrank k (ℳ d)` (`TauCeti.hilbertSerre_field`).

The file also develops the general calculus of `InternalGrading.HasHilbertPoly` and
`InternalGrading.hilbertPoly` over an arbitrary ring `A`: uniqueness, vanishing on bounded-above
gradings, invariance under homogeneous linear equivalences, variable translation under
`InternalGrading.shift`, and additivity on degree-zero short exact sequences.

## Main definitions

* `TauCeti.InternalGrading.HasHilbertPoly`: eventual finite length and polynomiality of
  `d ↦ Module.length A (G.piece d)`.
* `TauCeti.InternalGrading.hilbertPoly`: the unique `ℚ[X]` witnessing `G.HasHilbertPoly` (or `0` if
  none exists).

## Main results

* `TauCeti.LinearMap.IsHomogeneous.injective_restrict`,
  `TauCeti.LinearMap.IsHomogeneous.surjective_restrict`, and
  `TauCeti.LinearMap.IsHomogeneous.exact_restrict`: degree-zero homogeneous maps preserve
  injectivity, surjectivity, and exactness on each homogeneous piece.
* `TauCeti.InternalGrading.hilbertPoly_shift` and
  `TauCeti.InternalGrading.hilbertPoly_eq_add_of_exact`: shift and short-exact additivity of
  `hilbertPoly`.
* `TauCeti.InternalGrading.length_piece_add_length_ker_piece`: four-term exact length identity for
  a homogeneous endomorphism of arbitrary degree `r`.
* `TauCeti.InternalGrading.exists_hilbertSeries_mul_one_sub_X_pow_eq` and
  `TauCeti.InternalGrading.hasHilbertPoly_mvPolynomial`: Hilbert–Serre for bundled internal
  gradings.
* `TauCeti.hilbertSerre`, `TauCeti.hilbertSerre_of_adjoin_grade_one`, and
  `TauCeti.hilbertSerre_field`: Hilbert–Serre for `ℤ`-decompositions over polynomial rings,
  standard graded algebras, and fields.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley (1969),
  Theorem 11.1.
* [The Stacks Project, Proposition 10.58.7 (00K0)](https://stacks.math.columbia.edu/tag/00K0)
-/

public section

open scoped Polynomial PowerSeries

namespace TauCeti

namespace LinearMap.IsHomogeneous

section PieceExact

/-- A degree-zero homogeneous injective linear map restricts to an injection on every piece. -/
theorem injective_restrict {R ι M N : Type*} [Semiring R] [AddMonoid ι]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {f : M →ₗ[R] N} {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N}
    (hf : IsHomogeneous f ℳ 𝒩 0) (hinj : Function.Injective f) (k : ι) :
    Function.Injective (hf.restrict k) := fun _ _ h ↦
  Subtype.ext (hinj (by simpa only [hf.coe_restrict_apply] using congrArg Subtype.val h))

/-- A degree-zero homogeneous surjective linear map between modules with direct-sum decompositions
restricts to a surjection on every piece. -/
theorem surjective_restrict {R ι M N : Type*} [DecidableEq ι] [Semiring R] [AddMonoid ι]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {g : M →ₗ[R] N} {ℳ : ι → Submodule R M} [DirectSum.Decomposition ℳ]
    {𝒩 : ι → Submodule R N} [DirectSum.Decomposition 𝒩]
    (hg : IsHomogeneous g ℳ 𝒩 0) (hsurj : Function.Surjective g) (k : ι) :
    Function.Surjective (hg.restrict k) := fun y ↦ by
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨DirectSum.decompose ℳ x k, ?_⟩
  rw [hg.restrict_decompose, hx]
  exact Subtype.ext (DirectSum.decompose_of_mem_same 𝒩 y.2)

/-- An exact pair of degree-zero homogeneous linear maps restricts to an exact pair on every piece,
provided the first two modules carry direct-sum decompositions. -/
theorem exact_restrict {R ι M N P : Type*} [DecidableEq ι] [Semiring R] [AddMonoid ι]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    {ℳ : ι → Submodule R M} [DirectSum.Decomposition ℳ]
    {𝒩 : ι → Submodule R N} [DirectSum.Decomposition 𝒩]
    {𝒞 : ι → Submodule R P}
    (hf : IsHomogeneous f ℳ 𝒩 0) (hg : IsHomogeneous g 𝒩 𝒞 0)
    (hfg : Function.Exact f g) (k : ι) :
    Function.Exact (hf.restrict k) (hg.restrict k) := fun y ↦ by
  constructor
  · intro hy
    have hgy : g (y : N) = 0 := by
      simpa only [hg.coe_restrict_apply, ZeroMemClass.coe_zero] using congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (hfg (y : N)).1 hgy
    refine ⟨DirectSum.decompose ℳ x k, ?_⟩
    rw [hf.restrict_decompose, hx]
    exact Subtype.ext (DirectSum.decompose_of_mem_same 𝒩 y.2)
  · rintro ⟨x, rfl⟩
    exact Subtype.ext <| by
      rw [hg.coe_restrict_apply, hf.coe_restrict_apply, hfg.apply_apply_eq_zero,
        ZeroMemClass.coe_zero]

end PieceExact

end LinearMap.IsHomogeneous

namespace InternalGrading

section HilbertPolyAPI

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- An internally `ℤ`-graded `A`-module has a Hilbert polynomial if its homogeneous pieces
eventually have finite `A`-length and those lengths are given by evaluating a rational polynomial
`P : ℚ[X]`. Requiring `Module.length A (G.piece d) ≠ ⊤` prevents infinite-length pieces from
matching `P = 0` via the junk value `(⊤ : ℕ∞).toNat = 0`. -/
def HasHilbertPoly (G : InternalGrading A M ℤ) : Prop :=
  ∃ (P : ℚ[X]) (N : ℤ), ∀ d ≥ N,
    Module.length A (G.piece d) ≠ ⊤ ∧
      P.eval (d : ℚ) = ((Module.length A (G.piece d)).toNat : ℚ)

theorem hasHilbertPoly_def (G : InternalGrading A M ℤ) :
    G.HasHilbertPoly ↔ ∃ (P : ℚ[X]) (N : ℤ), ∀ d ≥ N,
      Module.length A (G.piece d) ≠ ⊤ ∧
        P.eval (d : ℚ) = ((Module.length A (G.piece d)).toNat : ℚ) :=
  Iff.rfl

/-- The Hilbert polynomial in `ℚ[X]` of an internally `ℤ`-graded `A`-module, or `0` if none
exists. -/
noncomputable def hilbertPoly (G : InternalGrading A M ℤ) : ℚ[X] :=
  open Classical in
  if h : G.HasHilbertPoly then h.choose else 0

/-- When `G.HasHilbertPoly` holds, `G.hilbertPoly` eventually agrees with the piece lengths of
`G`. -/
theorem HasHilbertPoly.exists_forall_ge_eval_hilbertPoly {G : InternalGrading A M ℤ}
    (hG : G.HasHilbertPoly) :
    ∃ N : ℤ, ∀ d ≥ N,
      Module.length A (G.piece d) ≠ ⊤ ∧
        G.hilbertPoly.eval (d : ℚ) = ((Module.length A (G.piece d)).toNat : ℚ) := by
  rw [hilbertPoly, dite_eq_left hG]
  exact hG.choose_spec

/-- When `G` has no Hilbert polynomial, `G.hilbertPoly` takes the junk value `0`. -/
theorem hilbertPoly_eq_zero_of_not_hasHilbertPoly {G : InternalGrading A M ℤ}
    (hG : ¬G.HasHilbertPoly) : G.hilbertPoly = 0 := by
  rw [hilbertPoly, dite_eq_right hG]

/-- Any rational polynomial that eventually agrees with finite piece lengths of `G` equals
`G.hilbertPoly`. -/
theorem hilbertPoly_eq_of_eventually_eq {G : InternalGrading A M ℤ} {P : ℚ[X]} {N : ℤ}
    (hP : ∀ d ≥ N,
      Module.length A (G.piece d) ≠ ⊤ ∧
        P.eval (d : ℚ) = ((Module.length A (G.piece d)).toNat : ℚ)) :
    G.hilbertPoly = P := by
  have hG : G.HasHilbertPoly := ⟨P, N, hP⟩
  obtain ⟨N₀, hN₀⟩ := hG.exists_forall_ge_eval_hilbertPoly
  refine Polynomial.eq_of_forall_ge_eval_intCast_eq (max N₀ N) fun d hd ↦ ?_
  rw [(hN₀ d ((le_max_left N₀ N).trans hd)).2, (hP d ((le_max_right N₀ N).trans hd)).2]

/-- The Hilbert polynomial of `G` is uniquely determined by eventual agreement with piece
lengths. -/
theorem HasHilbertPoly.existsUnique {G : InternalGrading A M ℤ} (hG : G.HasHilbertPoly) :
    ∃! P : ℚ[X], ∃ N : ℤ, ∀ d ≥ N,
      Module.length A (G.piece d) ≠ ⊤ ∧
        P.eval (d : ℚ) = ((Module.length A (G.piece d)).toNat : ℚ) := by
  refine ⟨G.hilbertPoly, hG.exists_forall_ge_eval_hilbertPoly, ?_⟩
  rintro P ⟨N, hP⟩
  exact (G.hilbertPoly_eq_of_eventually_eq hP).symm

/-- A grading with only finitely many nonzero pieces has Hilbert polynomial `0`. -/
theorem hasHilbertPoly_of_finite_piece_ne_bot {G : InternalGrading A M ℤ}
    (hfin : {d : ℤ | G.piece d ≠ ⊥}.Finite) : G.HasHilbertPoly := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨0, B + 1, fun d hd ↦ ?_⟩
  have hbot : G.piece d = ⊥ := by
    by_contra hne
    exact (hB hne).not_gt (by omega)
  rw [hbot]
  simp

/-- When only finitely many homogeneous pieces are nonzero, `G.hilbertPoly = 0`. -/
theorem hilbertPoly_eq_zero_of_finite_piece_ne_bot {G : InternalGrading A M ℤ}
    (hfin : {d : ℤ | G.piece d ≠ ⊥}.Finite) : G.hilbertPoly = 0 := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine G.hilbertPoly_eq_of_eventually_eq (N := B + 1) fun d hd ↦ ?_
  have hbot : G.piece d = ⊥ := by
    by_contra hne
    exact (hB hne).not_gt (by omega)
  rw [hbot]
  simp

/-- A trivial graded module has a Hilbert polynomial. -/
theorem hasHilbertPoly_of_subsingleton [Subsingleton M] (G : InternalGrading A M ℤ) :
    G.HasHilbertPoly :=
  ⟨0, 0, fun _ _ ↦ by simp⟩

@[simp]
theorem hilbertPoly_of_subsingleton [Subsingleton M] (G : InternalGrading A M ℤ) :
    G.hilbertPoly = 0 :=
  G.hilbertPoly_eq_of_eventually_eq (N := 0) fun _ _ ↦ by simp

section Map

variable {N : Type*} [AddCommGroup N] [Module A N]

private theorem length_map_piece (G : InternalGrading A M ℤ) (e : M ≃ₗ[A] N) (d : ℤ) :
    Module.length A ((G.map e).piece d) = Module.length A (G.piece d) := by
  rw [map_piece]
  exact (Submodule.equivMapOfInjective e.toLinearMap e.injective (G.piece d)).symm.length_eq

/-- Transporting an internal grading across a linear equivalence preserves `HasHilbertPoly`. -/
@[simp]
theorem hasHilbertPoly_map_iff (G : InternalGrading A M ℤ) (e : M ≃ₗ[A] N) :
    (G.map e).HasHilbertPoly ↔ G.HasHilbertPoly := by
  simp only [HasHilbertPoly, length_map_piece]

/-- Transporting an internal grading across a linear equivalence preserves `hilbertPoly`. -/
@[simp]
theorem hilbertPoly_map (G : InternalGrading A M ℤ) (e : M ≃ₗ[A] N) :
    (G.map e).hilbertPoly = G.hilbertPoly := by
  by_cases hG : G.HasHilbertPoly
  · obtain ⟨N₀, hN₀⟩ := hG.exists_forall_ge_eval_hilbertPoly
    refine (G.map e).hilbertPoly_eq_of_eventually_eq (N := N₀) fun d hd ↦ ?_
    rw [length_map_piece]
    exact hN₀ d hd
  · rw [hilbertPoly_eq_zero_of_not_hasHilbertPoly hG,
      hilbertPoly_eq_zero_of_not_hasHilbertPoly (mt (G.hasHilbertPoly_map_iff e).1 hG)]

end Map

/-- Shifting an internal grading by `c : ℤ` preserves `HasHilbertPoly`. -/
@[simp]
theorem hasHilbertPoly_shift_iff (G : InternalGrading A M ℤ) (c : ℤ) :
    (G.shift c).HasHilbertPoly ↔ G.HasHilbertPoly := by
  constructor
  · rintro ⟨P, N, hP⟩
    refine ⟨P.comp (Polynomial.X - Polynomial.C (c : ℚ)), N + c, fun d hd ↦ ?_⟩
    obtain ⟨hlen, hev⟩ := hP (d - c) (by omega)
    rw [shift_piece, sub_add_cancel] at hlen hev
    refine ⟨hlen, ?_⟩
    simpa [Int.cast_sub] using hev
  · rintro ⟨P, N, hP⟩
    refine ⟨P.comp (Polynomial.X + Polynomial.C (c : ℚ)), N - c, fun d hd ↦ ?_⟩
    obtain ⟨hlen, hev⟩ := hP (d + c) (by omega)
    rw [shift_piece]
    refine ⟨hlen, ?_⟩
    simpa [Int.cast_add] using hev

/-- Shifting an internal grading by `c : ℤ` translates the variable of `hilbertPoly` by `+ c`. -/
@[simp]
theorem hilbertPoly_shift (G : InternalGrading A M ℤ) (c : ℤ) :
    (G.shift c).hilbertPoly =
      G.hilbertPoly.comp (Polynomial.X + Polynomial.C (c : ℚ)) := by
  by_cases hG : G.HasHilbertPoly
  · obtain ⟨N, hN⟩ := hG.exists_forall_ge_eval_hilbertPoly
    refine (G.shift c).hilbertPoly_eq_of_eventually_eq (N := N - c) fun d hd ↦ ?_
    obtain ⟨hlen, hev⟩ := hN (d + c) (by omega)
    rw [shift_piece]
    refine ⟨hlen, ?_⟩
    simpa [Int.cast_add] using hev
  · rw [hilbertPoly_eq_zero_of_not_hasHilbertPoly (mt (G.hasHilbertPoly_shift_iff c).1 hG),
      hilbertPoly_eq_zero_of_not_hasHilbertPoly hG, Polynomial.zero_comp]

section Exact

variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module A N] [Module A P]
  {G : InternalGrading A M ℤ} {H : InternalGrading A N ℤ} {K : InternalGrading A P ℤ}
  {f : M →ₗ[A] N} {g : N →ₗ[A] P}

/-- In a short exact sequence of degree-zero homogeneous linear maps, if the outer graded modules
have Hilbert polynomials, then so does the middle one. -/
theorem HasHilbertPoly.of_exact (hf : LinearMap.IsHomogeneous f G.piece H.piece 0)
    (hg : LinearMap.IsHomogeneous g H.piece K.piece 0) (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hex : Function.Exact f g)
    (hG : G.HasHilbertPoly) (hK : K.HasHilbertPoly) : H.HasHilbertPoly := by
  obtain ⟨N₁, hN₁⟩ := hG.exists_forall_ge_eval_hilbertPoly
  obtain ⟨N₂, hN₂⟩ := hK.exists_forall_ge_eval_hilbertPoly
  refine ⟨G.hilbertPoly + K.hilbertPoly, max N₁ N₂, fun d hd ↦ ?_⟩
  obtain ⟨hGd, hevG⟩ := hN₁ d ((le_max_left N₁ N₂).trans hd)
  obtain ⟨hKd, hevK⟩ := hN₂ d ((le_max_right N₁ N₂).trans hd)
  have hadd := Module.length_eq_add_of_exact (hf.restrict d) (hg.restrict d)
    (hf.injective_restrict hinj d) (hg.surjective_restrict hsurj d) (hf.exact_restrict hg hex d)
  refine ⟨hadd ▸ WithTop.add_ne_top.2 ⟨hGd, hKd⟩, ?_⟩
  rw [Polynomial.eval_add, hevG, hevK, hadd, ENat.toNat_add hGd hKd, Nat.cast_add]

/-- **Additivity of Hilbert polynomials in short exact sequences.** Given a degree-zero homogeneous
short exact sequence `0 → M → N → P → 0` whose outer modules have Hilbert polynomials,
`H.hilbertPoly = G.hilbertPoly + K.hilbertPoly`. -/
theorem hilbertPoly_eq_add_of_exact (hf : LinearMap.IsHomogeneous f G.piece H.piece 0)
    (hg : LinearMap.IsHomogeneous g H.piece K.piece 0) (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hex : Function.Exact f g)
    (hG : G.HasHilbertPoly) (hK : K.HasHilbertPoly) :
    H.hilbertPoly = G.hilbertPoly + K.hilbertPoly := by
  obtain ⟨N₁, hN₁⟩ := hG.exists_forall_ge_eval_hilbertPoly
  obtain ⟨N₂, hN₂⟩ := hK.exists_forall_ge_eval_hilbertPoly
  refine H.hilbertPoly_eq_of_eventually_eq (N := max N₁ N₂) fun d hd ↦ ?_
  obtain ⟨hGd, hevG⟩ := hN₁ d ((le_max_left N₁ N₂).trans hd)
  obtain ⟨hKd, hevK⟩ := hN₂ d ((le_max_right N₁ N₂).trans hd)
  have hadd := Module.length_eq_add_of_exact (hf.restrict d) (hg.restrict d)
    (hf.injective_restrict hinj d) (hg.surjective_restrict hsurj d) (hf.exact_restrict hg hex d)
  refine ⟨hadd ▸ WithTop.add_ne_top.2 ⟨hGd, hKd⟩, ?_⟩
  rw [Polynomial.eval_add, hevG, hevK, hadd, ENat.toNat_add hGd hKd, Nat.cast_add]

end Exact

end HilbertPolyAPI

section EndomorphismLength

/-- **Four-term length identity for a homogeneous endomorphism.** Let `μ : M →ₗ[S] M` be
homogeneous of degree `r` with respect to an internal `A`-grading `G`. Splitting
`0 → ker μ → M → M → M ⧸ range μ → 0` through `range μ` in degrees `d` and `d + r` yields
`length_A(M_{d + r}) + length_A((ker μ)_d) = length_A(M_d) + length_A((M ⧸ range μ)_{d + r})` in
`ℕ∞`. -/
theorem length_piece_add_length_ker_piece {ι A S M : Type*} [DecidableEq ι]
    [AddRightCancelMonoid ι] [Ring A] [Ring S] [SMul A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (G : InternalGrading A M ι) {r : ι} {μ : M →ₗ[S] M}
    (hμ : LinearMap.IsHomogeneous μ G.piece G.piece r) (d : ι) :
    Module.length A (G.piece (d + r)) + Module.length A ((G.ker hμ).piece d) =
      Module.length A (G.piece d) +
        Module.length A ((G.quotient (_root_.LinearMap.range μ) hμ.isHomogeneous_range).piece
          (d + r)) := by
  let U := _root_.LinearMap.range μ
  let I := G.submodule U hμ.isHomogeneous_range
  let Q := G.quotient U hμ.isHomogeneous_range
  let ι₁ : (G.ker hμ).piece d →ₗ[A] G.piece d :=
    { toFun z := ⟨z.1.1, (G.mem_ker_piece hμ).1 z.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let μ₁ : G.piece d →ₗ[A] I.piece (d + r) :=
    { toFun x := ⟨⟨μ x.1, ⟨x.1, rfl⟩⟩,
        (G.mem_submodule_piece U hμ.isHomogeneous_range).2 (hμ.map_mem x.2)⟩
      map_add' x y := Subtype.ext (Subtype.ext (map_add μ x.1 y.1))
      map_smul' a x := Subtype.ext (Subtype.ext (map_smul (μ.restrictScalars A) a x.1)) }
  have hι₁ : Function.Injective ι₁ := fun _ _ h ↦
    Subtype.ext (Subtype.ext (congrArg (·.1) h))
  have hμ₁ : Function.Surjective μ₁ := fun y ↦ by
    obtain ⟨x, hx⟩ := y.1.2
    refine ⟨DirectSum.decompose G.piece x d, Subtype.ext (Subtype.ext ?_)⟩
    change μ (DirectSum.decompose G.piece x d : M) = (y.1 : M)
    rw [hμ.map_decompose d x, hx,
      DirectSum.decompose_of_mem_same G.piece
        ((G.mem_submodule_piece U hμ.isHomogeneous_range).1 y.2)]
  have hex₁ : Function.Exact ι₁ μ₁ := fun x ↦
    ⟨fun h ↦ ⟨⟨⟨x.1, congrArg (Subtype.val ∘ Subtype.val) h⟩, (G.mem_ker_piece hμ).2 x.2⟩, rfl⟩,
      fun ⟨z, hz⟩ ↦ Subtype.ext (Subtype.ext (hz ▸ z.1.2))⟩
  have hlen₁ := Module.length_eq_add_of_exact ι₁ μ₁ hι₁ hμ₁ hex₁
  have hi₂ : LinearMap.IsHomogeneous (U.subtype.restrictScalars A) I.piece G.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      rw [add_zero]
      exact (G.mem_submodule_piece U hμ.isHomogeneous_range).1 hx
  have hq₂ : LinearMap.IsHomogeneous (U.mkQ.restrictScalars A) G.piece Q.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      rw [add_zero]
      exact G.mk_mem_quotient_piece U hμ.isHomogeneous_range hx
  have hex₂ : Function.Exact (U.subtype.restrictScalars A) (U.mkQ.restrictScalars A) :=
    fun y ↦ by simp
  have hlen₂ := Module.length_eq_add_of_exact (hi₂.restrict (d + r)) (hq₂.restrict (d + r))
    (hi₂.injective_restrict (Submodule.subtype_injective U) (d + r))
    (hq₂.surjective_restrict (Submodule.mkQ_surjective U) (d + r))
    (hi₂.exact_restrict hq₂ hex₂ (d + r))
  rw [hlen₁, hlen₂]
  ac_rfl

end EndomorphismLength

section MvPolynomialHilbertSeries

private theorem powerSeries_eq_polynomial_of_forall_gt_eq_zero {f : ℕ → ℤ} (N : ℕ)
    (hf : ∀ n > N, f n = 0) :
    ∃ h : ℤ[X], PowerSeries.mk f = h.toPowerSeries := by
  refine ⟨∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (f i), PowerSeries.ext fun n ↦ ?_⟩
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
  by_cases hn : n ≤ N
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      exact Polynomial.coeff_monomial_of_ne (f b) hbn.symm
    · intro hmem
      exact False.elim (hmem (Finset.mem_range.2 (by omega)))
  · rw [hf n (by omega), Finset.sum_eq_zero]
    intro b hb
    exact Polynomial.coeff_monomial_of_ne (f b) (by rw [Finset.mem_range] at hb; omega)

private theorem hilbertSeries_mul_one_sub_X {A S M : Type*} [CommRing A] [IsArtinianRing A]
    [Ring S] [SMul A S] [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (G : InternalGrading A M ℤ) {μ : M →ₗ[S] M}
    (hμ : LinearMap.IsHomogeneous μ G.piece G.piece 1)
    (hfinM : ∀ d : ℤ, Module.Finite A (G.piece d))
    (hfinK : ∀ d : ℤ, Module.Finite A ((G.ker hμ).piece d))
    (hfinQ : ∀ d : ℤ, Module.Finite A
      ((G.quotient (_root_.LinearMap.range μ) hμ.isHomogeneous_range).piece d))
    (d₀ : ℤ) :
    let lM := fun d : ℤ ↦ ((Module.length A (G.piece d)).toNat : ℤ)
    let lK := fun d : ℤ ↦ ((Module.length A ((G.ker hμ).piece d)).toNat : ℤ)
    let lQ := fun d : ℤ ↦
      ((Module.length A
        ((G.quotient (_root_.LinearMap.range μ) hμ.isHomogeneous_range).piece d)).toNat : ℤ)
    (PowerSeries.mk fun n : ℕ ↦ lM (d₀ + n)) * (1 - PowerSeries.X) =
      (PowerSeries.mk fun n : ℕ ↦ lQ (d₀ + n)) -
        PowerSeries.X * (PowerSeries.mk fun n : ℕ ↦ lK (d₀ + n)) +
        PowerSeries.C (lM (d₀ - 1) - lK (d₀ - 1)) := by
  intro lM lK lQ
  have hrel (d : ℤ) : lM (d + 1) + lK d = lM d + lQ (d + 1) := by
    have _ := hfinM (d + 1); have _ := hfinM d
    have _ := hfinK d; have _ := hfinQ (d + 1)
    have h := G.length_piece_add_length_ker_piece hμ d
    have htoNat := congrArg ENat.toNat h
    rw [ENat.toNat_add Module.length_ne_top Module.length_ne_top,
      ENat.toNat_add Module.length_ne_top Module.length_ne_top] at htoNat
    dsimp only [lM, lK, lQ]
    exact_mod_cast htoNat
  ext n
  cases n with
  | zero =>
    have h0 := hrel (d₀ - 1)
    rw [sub_add_cancel] at h0
    simp only [mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_zero_C,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_mul_X, Nat.cast_zero, add_zero]
    omega
  | succ m =>
    have hm := hrel (d₀ + m)
    simp only [mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_succ_C,
      Nat.cast_add, Nat.cast_one, ← add_assoc]
    omega

private theorem smul_eq_rename_some_aeval_of_X_none_smul_eq_zero {A α N : Type*} [CommRing A]
    [AddCommGroup N] [Module (MvPolynomial (Option α) A) N]
    (hX : ∀ y : N, (MvPolynomial.X none : MvPolynomial (Option α) A) • y = 0)
    (q : MvPolynomial (Option α) A) (y : N) :
    q • y =
      (MvPolynomial.rename Option.some
        (MvPolynomial.aeval (fun o ↦ o.elim 0 (MvPolynomial.X (R := A))) q)) • y := by
  induction q using MvPolynomial.induction_on generalizing y with
  | C a => simp
  | add p₁ p₂ h₁ h₂ => simp only [map_add, add_smul, h₁, h₂]
  | mul_X p o hp =>
    cases o with
    | none =>
      rw [mul_comm, mul_smul, hX, map_mul, MvPolynomial.aeval_X, Option.elim_none,
        zero_mul, map_zero, zero_smul]
    | some i =>
      rw [mul_comm, mul_smul, hp, map_mul, MvPolynomial.aeval_X, Option.elim_some,
        map_mul, MvPolynomial.rename_X, mul_smul]

private theorem finite_compHom_rename_some {A α N : Type*} [CommRing A] [AddCommGroup N]
    [Module (MvPolynomial (Option α) A) N] [Module.Finite (MvPolynomial (Option α) A) N]
    (hX : ∀ y : N, (MvPolynomial.X none : MvPolynomial (Option α) A) • y = 0) :
    @Module.Finite (MvPolynomial α A) N _ _
      (Module.compHom N (MvPolynomial.rename (R := A) Option.some).toRingHom) := by
  let _ : Module (MvPolynomial α A) N :=
    Module.compHom N (MvPolynomial.rename (R := A) Option.some).toRingHom
  let ψ : MvPolynomial (Option α) A →+* MvPolynomial α A :=
    (MvPolynomial.aeval (fun o ↦ o.elim 0 (MvPolynomial.X (R := A)))).toRingHom
  let f : N →ₛₗ[ψ] N :=
    { toFun := id
      map_add' _ _ := rfl
      map_smul' q y := smul_eq_rename_some_aeval_of_X_none_smul_eq_zero hX q y }
  exact Module.Finite.of_surjective f Function.surjective_id

private theorem exists_hilbertSeries_empty {A σ M : Type*} [CommRing A] [IsEmpty σ]
    [AddCommGroup M] [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M] [Module.Finite (MvPolynomial σ A) M]
    (G : InternalGrading A M ℤ) (d₀ : ℤ) :
    ∃ h : ℤ[X],
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (G.piece (d₀ + n))).toNat : ℤ)) =
        h.toPowerSeries := by
  have : Module.Finite A (MvPolynomial σ A) :=
    Module.Finite.of_surjective (Algebra.ofId A (MvPolynomial σ A)).toLinearMap
      (MvPolynomial.C_surjective σ)
  have : Module.Finite A M := Module.Finite.trans (MvPolynomial σ A) M
  obtain ⟨B, hB⟩ := G.finite_piece_ne_bot.bddAbove
  refine powerSeries_eq_polynomial_of_forall_gt_eq_zero (B - d₀).toNat fun n hn ↦ ?_
  have hbot : G.piece (d₀ + n) = ⊥ := by
    by_contra hne
    exact (hB hne).not_gt (by omega)
  rw [hbot]
  simp

private theorem _root_.TauCeti.isScalarTower_compHom {A B C N : Type*} [CommSemiring A]
    [Semiring B] [Semiring C] [Algebra A B] [Algebra A C] [AddCommMonoid N]
    [Module A N] [Module C N] [IsScalarTower A C N] (φ : B →ₐ[A] C) :
    @IsScalarTower A B N _ (Module.compHom N φ.toRingHom).toSMul _ := by
  let _ : Module B N := Module.compHom N φ.toRingHom
  refine ⟨fun a b x ↦ ?_⟩
  change φ (a • b) • x = a • (φ b • x)
  rw [map_smul, smul_assoc]

private theorem exists_hilbertSeries_option_step {A α : Type*} [CommRing A] [IsArtinianRing A]
    [Fintype α]
    (ih : ∀ {N : Type w} [AddCommGroup N] [Module A N] [Module (MvPolynomial α A) N]
      [IsScalarTower A (MvPolynomial α A) N] [Module.Finite (MvPolynomial α A) N]
      (H : InternalGrading A N ℤ),
      (∀ (i : ℕ) (j : ℤ), ∀ p ∈ MvPolynomial.homogeneousSubmodule α A i,
        ∀ y ∈ H.piece j, p • y ∈ H.piece (j + i)) →
      ∀ d₀ : ℤ, ∃ h : ℤ[X],
        (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (H.piece (d₀ + n))).toNat : ℤ)) *
          (1 - PowerSeries.X) ^ Fintype.card α = h.toPowerSeries)
    {M : Type w} [AddCommGroup M] [Module A M] [Module (MvPolynomial (Option α) A) M]
    [IsScalarTower A (MvPolynomial (Option α) A) M]
    [Module.Finite (MvPolynomial (Option α) A) M]
    (G : InternalGrading A M ℤ)
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ p ∈ MvPolynomial.homogeneousSubmodule (Option α) A i,
      ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i))
    (d₀ : ℤ) :
    ∃ h : ℤ[X],
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (G.piece (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ Fintype.card (Option α) = h.toPowerSeries := by
  let μ : M →ₗ[MvPolynomial (Option α) A] M :=
    _root_.LinearMap.lsmul (MvPolynomial (Option α) A) M (MvPolynomial.X none)
  have hμ : LinearMap.IsHomogeneous μ G.piece G.piece 1 :=
    LinearMap.isHomogeneous_def.2 fun p m hm ↦
      hsmul 1 p _ (MvPolynomial.isHomogeneous_X A none) m hm
  let K := _root_.LinearMap.ker μ
  let Q := M ⧸ _root_.LinearMap.range μ
  have : Module.Finite (MvPolynomial (Option α) A) K := Module.IsNoetherian.finite _ _
  let _ : Module (MvPolynomial α A) K :=
    Module.compHom K (MvPolynomial.rename (R := A) Option.some).toRingHom
  let _ : Module (MvPolynomial α A) Q :=
    Module.compHom Q (MvPolynomial.rename (R := A) Option.some).toRingHom
  have : IsScalarTower A (MvPolynomial α A) K :=
    isScalarTower_compHom (MvPolynomial.rename Option.some)
  have : IsScalarTower A (MvPolynomial α A) Q :=
    isScalarTower_compHom (MvPolynomial.rename Option.some)
  have : Module.Finite (MvPolynomial α A) K :=
    finite_compHom_rename_some fun z ↦ Subtype.ext z.2
  have : Module.Finite (MvPolynomial α A) Q :=
    finite_compHom_rename_some fun y ↦ Submodule.Quotient.induction_on _ y fun m ↦
      (Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩
  have hsmulK (i : ℕ) (j : ℤ) (p : MvPolynomial α A)
      (hp : p ∈ MvPolynomial.homogeneousSubmodule α A i) (z : K) (hz : z ∈ (G.ker hμ).piece j) :
      p • z ∈ (G.ker hμ).piece (j + i) :=
    (G.mem_ker_piece hμ).2 (hsmul i j _ hp.rename_isHomogeneous (z : M) ((G.mem_ker_piece hμ).1 hz))
  have hsmulQ (i : ℕ) (j : ℤ) (p : MvPolynomial α A)
      (hp : p ∈ MvPolynomial.homogeneousSubmodule α A i) (y : Q)
      (hy : y ∈ (G.quotient (_root_.LinearMap.range μ) hμ.isHomogeneous_range).piece j) :
      p • y ∈ (G.quotient (_root_.LinearMap.range μ) hμ.isHomogeneous_range).piece (j + i) := by
    obtain ⟨m, hm, rfl⟩ := (G.mem_quotient_piece_iff _ hμ.isHomogeneous_range).1 hy
    exact G.mk_mem_quotient_piece _ hμ.isHomogeneous_range
      (hsmul i j _ hp.rename_isHomogeneous m hm)
  obtain ⟨hK, hhK⟩ := ih (G.ker hμ) hsmulK d₀
  obtain ⟨hQ, hhQ⟩ := ih (G.quotient (_root_.LinearMap.range μ) hμ.isHomogeneous_range) hsmulQ d₀
  have hstep := hilbertSeries_mul_one_sub_X G hμ
    (gradedPiecesFinite_mvPolynomial G.piece hsmul).1
    (gradedPiecesFinite_mvPolynomial (G.ker hμ).piece hsmulK).1
    (gradedPiecesFinite_mvPolynomial
      (G.quotient (_root_.LinearMap.range μ) hμ.isHomogeneous_range).piece hsmulQ).1 d₀
  let c : ℤ := ((Module.length A (G.piece (d₀ - 1))).toNat : ℤ) -
    ((Module.length A ((G.ker hμ).piece (d₀ - 1))).toNat : ℤ)
  refine ⟨hQ - Polynomial.X * hK + Polynomial.C c * (1 - Polynomial.X) ^ Fintype.card α, ?_⟩
  rw [Fintype.card_option, pow_succ', ← mul_assoc, hstep, add_mul, sub_mul, mul_assoc, hhQ, hhK]
  simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_one, Polynomial.coe_X, Polynomial.coe_C]
  rfl

/-- **Hilbert–Serre series rationality.** Over a commutative Artinian ring `A`, every finitely
generated internally `ℤ`-graded `MvPolynomial σ A`-module (`[Fintype σ]`) has finite-length pieces,
and for *every* starting degree `d₀ : ℤ` its shifted Hilbert series multiplied by
`(1 - X) ^ Fintype.card σ` is an integer polynomial `h : ℤ[X]`. -/
theorem exists_hilbertSeries_mul_one_sub_X_pow_eq {A : Type u} [CommRing A] [IsArtinianRing A]
    {σ : Type v} [Fintype σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (G : InternalGrading A M ℤ)
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ p ∈ MvPolynomial.homogeneousSubmodule σ A i,
      ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i))
    (d₀ : ℤ) :
    (∀ d : ℤ, Module.length A (G.piece d) ≠ ⊤) ∧
      ∃ h : ℤ[X],
        (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (G.piece (d₀ + n))).toNat : ℤ)) *
          (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries := by
  refine ⟨fun d ↦ by
    have _ := (gradedPiecesFinite_mvPolynomial G.piece hsmul).1 d
    exact Module.length_ne_top, ?_⟩
  revert M G hsmul d₀
  refine Fintype.induction_empty_option (P := fun (τ : Type v) (_ : Fintype τ) ↦
    ∀ {M : Type w} [AddCommGroup M] [Module A M] [Module (MvPolynomial τ A) M]
      [IsScalarTower A (MvPolynomial τ A) M] [Module.Finite (MvPolynomial τ A) M]
      (G : InternalGrading A M ℤ),
      (∀ (i : ℕ) (j : ℤ), ∀ p ∈ MvPolynomial.homogeneousSubmodule τ A i,
        ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i)) →
      ∀ d₀ : ℤ, ∃ h : ℤ[X],
        (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (G.piece (d₀ + n))).toNat : ℤ)) *
          (1 - PowerSeries.X) ^ Fintype.card τ = h.toPowerSeries) ?_ ?_ ?_ σ
  · intro α β _ e ihα M _ _ _ _ _ G hsmul d₀
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    let _ : Module (MvPolynomial α A) M :=
      Module.compHom M (MvPolynomial.rename (R := A) e).toRingHom
    have : IsScalarTower A (MvPolynomial α A) M := isScalarTower_compHom (MvPolynomial.rename e)
    let φ : MvPolynomial β A →+* MvPolynomial α A := (MvPolynomial.rename (R := A) e.symm).toRingHom
    let f : M →ₛₗ[φ] M :=
      { toFun := id
        map_add' _ _ := rfl
        map_smul' q m := by
          change q • m = (MvPolynomial.rename e (MvPolynomial.rename e.symm q)) • m
          rw [MvPolynomial.rename_rename, e.self_comp_symm, MvPolynomial.rename_id,
            AlgHom.coe_id, id_eq] }
    have : Module.Finite (MvPolynomial α A) M :=
      Module.Finite.of_surjective f Function.surjective_id
    obtain ⟨h, hh⟩ := ihα G (fun i j p hp m hm ↦ hsmul i j _ hp.rename_isHomogeneous m hm) d₀
    exact ⟨h, Fintype.ofEquiv_card e.symm ▸ hh⟩
  · intro M _ _ _ _ _ G _ d₀
    obtain ⟨h, hh⟩ := exists_hilbertSeries_empty (σ := PEmpty) G d₀
    exact ⟨h, by simpa using hh⟩
  · intro α _ ih M _ _ _ _ _ G hsmul d₀
    exact exists_hilbertSeries_option_step ih G hsmul d₀

/-- **Hilbert–Serre for bundled internal gradings (`[Fintype σ]`).** A finitely generated
internally `ℤ`-graded `MvPolynomial σ A`-module over a commutative Artinian ring `A` has a Hilbert
polynomial of degree `< Fintype.card σ` belonging to `TauCeti.ringChooseSpan (Polynomial.X : ℚ[X])`.
-/
theorem hasHilbertPoly_and_degree_lt_card_mvPolynomial {A : Type u} [CommRing A]
    [IsArtinianRing A] {σ : Type v} [Fintype σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (G : InternalGrading A M ℤ)
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ p ∈ MvPolynomial.homogeneousSubmodule σ A i,
      ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i)) :
    G.HasHilbertPoly ∧
      G.hilbertPoly.degree < (Fintype.card σ : WithBot ℕ) ∧
      G.hilbertPoly ∈ ringChooseSpan (Polynomial.X : ℚ[X]) := by
  obtain ⟨hlen, h, hseries⟩ := G.exists_hilbertSeries_mul_one_sub_X_pow_eq hsmul 0
  let hℚ : ℚ[X] := h.map (Int.castRingHom ℚ)
  have hQ : (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (G.piece ((0 : ℤ) + n))).toNat : ℚ)) *
      (1 - PowerSeries.X) ^ Fintype.card σ = (hℚ : ℚ⟦X⟧) := by
    have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hseries
    rw [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X,
      ← Polynomial.polynomial_map_coe] at hmap
    exact Eq.trans (congrArg (· * _) (PowerSeries.ext fun n ↦ by simp)) hmap
  set P₀ : ℚ[X] := Polynomial.hilbertPoly hℚ (Fintype.card σ)
  have hev (d : ℤ) (hd : (hℚ.natDegree : ℤ) + 1 ≤ d) :
      Module.length A (G.piece d) ≠ ⊤ ∧
        P₀.eval (d : ℚ) = ((Module.length A (G.piece d)).toNat : ℚ) := by
    refine ⟨hlen d, ?_⟩
    have hd' : (0 : ℤ) + hℚ.natDegree < d := by omega
    have hcomp := Polynomial.eval_hilbertPoly_comp_X_sub_intCast
      (f := fun k ↦ ((Module.length A (G.piece k)).toNat : ℚ))
      (p := hℚ) (d₀ := 0) (e := Fintype.card σ) hQ hd'
    simpa only [P₀, Int.cast_zero, map_zero, sub_zero, Polynomial.comp_X] using hcomp
  have hPeq : G.hilbertPoly = P₀ := G.hilbertPoly_eq_of_eventually_eq hev
  refine ⟨⟨P₀, _, hev⟩, ?_, ?_⟩
  · rw [hPeq]
    exact Polynomial.degree_hilbertPoly_lt _ _
  · rw [hPeq]
    exact Polynomial.hilbertPoly_map_intCast_mem_ringChooseSpan h (Fintype.card σ)

/-- **Hilbert–Serre for bundled internal gradings (`[Finite σ]`).** A finitely generated internally
`ℤ`-graded `MvPolynomial σ A`-module over a commutative Artinian ring `A` has a Hilbert polynomial
in `TauCeti.ringChooseSpan (Polynomial.X : ℚ[X])`, which takes integer values at all integers. -/
theorem hasHilbertPoly_mvPolynomial {A : Type u} [CommRing A] [IsArtinianRing A]
    {σ : Type v} [Finite σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (G : InternalGrading A M ℤ)
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ p ∈ MvPolynomial.homogeneousSubmodule σ A i,
      ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i)) :
    G.HasHilbertPoly ∧
      G.hilbertPoly ∈ ringChooseSpan (Polynomial.X : ℚ[X]) ∧
      ∀ m : ℤ, ∃ z : ℤ, (z : ℚ) = G.hilbertPoly.eval (m : ℚ) := by
  cases nonempty_fintype σ
  obtain ⟨hG, -, hspan⟩ := G.hasHilbertPoly_and_degree_lt_card_mvPolynomial hsmul
  exact ⟨hG, hspan, exists_intCast_eq_eval_of_mem_ringChooseSpan hspan⟩

end MvPolynomialHilbertSeries

end InternalGrading

section Headline

/-- **Hilbert–Serre theorem.** A finitely generated `ℤ`-graded module `M` over a standard polynomial
ring `MvPolynomial σ A` (`[Fintype σ]`) with commutative Artinian coefficients `A` has finite-length
pieces, vanishes below a uniform degree `d₀`, has shifted Hilbert series `h(X) / (1 - X)^(#σ)` for
an integer polynomial `h : ℤ[X]`, and agrees for `d ≥ N` with a rational polynomial `P : ℚ[X]` of
degree `< Fintype.card σ`. -/
theorem hilbertSerre (A : Type u) [CommRing A] [IsArtinianRing A]
    (σ : Type v) [Fintype σ] (M : Type w) [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i →
        ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) :
    (∀ d, Module.Finite A (ℳ d) ∧ Module.length A (ℳ d) ≠ ⊤) ∧
      ∃ (d₀ : ℤ) (h : Polynomial ℤ) (P : Polynomial ℚ) (N : ℤ),
        (∀ d < d₀, ℳ d = ⊥) ∧
        (PowerSeries.mk (fun n : ℕ =>
          ((Module.length A (ℳ (d₀ + n))).toNat : ℤ))) *
          (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries ∧
        P.degree < (Fintype.card σ : WithBot ℕ) ∧
        ∀ d, N ≤ d → P.eval (d : ℚ) = ((Module.length A (ℳ d)).toNat : ℚ) := by
  obtain ⟨hfin, d₀, hd₀⟩ := gradedPiecesFinite_mvPolynomial ℳ hgraded
  let G := InternalGrading.ofDecomposition ℳ
  have hGgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i →
        ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i) := by
    dsimp only [G]
    rwa [InternalGrading.ofDecomposition_piece]
  obtain ⟨hlen, h, hseries⟩ := G.exists_hilbertSeries_mul_one_sub_X_pow_eq hGgraded d₀
  obtain ⟨hG, hdeg, -⟩ := G.hasHilbertPoly_and_degree_lt_card_mvPolynomial hGgraded
  obtain ⟨N, hN⟩ := hG.exists_forall_ge_eval_hilbertPoly
  dsimp only [G] at hlen hseries hN
  rw [InternalGrading.ofDecomposition_piece] at hlen hseries hN
  exact ⟨fun d ↦ ⟨hfin d, hlen d⟩, d₀, h, G.hilbertPoly, N, hd₀, hseries, hdeg,
    fun d hd ↦ (hN d hd).2⟩

/-- **Hilbert–Serre for standard graded algebras.** Let `B` be a commutative `A`-algebra over a
commutative Artinian ring `A`, equipped with a `SetLike.GradedMonoid` family `ℬ : ℕ → Submodule A B`
and generated over `A` by finitely many degree-one elements `v : σ → B` (`[Fintype σ]`). Every
finitely generated `ℤ`-graded `B`-module `M` compatible with `ℬ` satisfies the conclusions of
`hilbertSerre` with exponent `Fintype.card σ`. -/
theorem hilbertSerre_of_adjoin_grade_one (A : Type u) [CommRing A] [IsArtinianRing A]
    {B : Type*} [CommRing B] [Algebra A B] (ℬ : ℕ → Submodule A B) [SetLike.GradedMonoid ℬ]
    {σ : Type v} [Fintype σ] (v : σ → B) (hv : ∀ i, v i ∈ ℬ 1)
    (hadj : Algebra.adjoin A (Set.range v) = ⊤)
    (M : Type w) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ), ∀ b ∈ ℬ i, ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) :
    (∀ d, Module.Finite A (ℳ d) ∧ Module.length A (ℳ d) ≠ ⊤) ∧
      ∃ (d₀ : ℤ) (h : Polynomial ℤ) (P : Polynomial ℚ) (N : ℤ),
        (∀ d < d₀, ℳ d = ⊥) ∧
        (PowerSeries.mk (fun n : ℕ =>
          ((Module.length A (ℳ (d₀ + n))).toNat : ℤ))) *
          (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries ∧
        P.degree < (Fintype.card σ : WithBot ℕ) ∧
        ∀ d, N ≤ d → P.eval (d : ℚ) = ((Module.length A (ℳ d)).toNat : ℚ) := by
  let φ : MvPolynomial σ A →+* B := (MvPolynomial.aeval v).toRingHom
  have hφ : Function.Surjective φ := by
    change Function.Surjective (MvPolynomial.aeval v)
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hadj
  let _ : Module (MvPolynomial σ A) M := Module.compHom M φ
  have : IsScalarTower A (MvPolynomial σ A) M := isScalarTower_compHom (MvPolynomial.aeval v)
  have : RingHomSurjective φ := ⟨hφ⟩
  let f : M →ₛₗ[φ] M := { toFun := id, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have : Module.Finite (MvPolynomial σ A) M :=
    (f.finite_iff_of_bijective Function.bijective_id).2 ‹Module.Finite B M›
  exact hilbertSerre A σ M ℳ fun i j p hp m hm ↦
    hgraded i j (MvPolynomial.aeval v p) (hp.aeval_mem hv) m hm

/-- **Hilbert–Serre over a field.** Over any field `k` (of arbitrary characteristic), the piece
lengths of a finitely generated `ℤ`-graded `MvPolynomial σ k`-module equal `Module.finrank k (ℳ d)`,
giving the rational Hilbert series and eventual dimension polynomial of degree `< Fintype.card σ`.
-/
theorem hilbertSerre_field (k : Type u) [Field k]
    (σ : Type v) [Fintype σ] (M : Type w) [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ k),
      p ∈ MvPolynomial.homogeneousSubmodule σ k i →
        ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) :
    (∀ d, Module.Finite k (ℳ d)) ∧
      ∃ (d₀ : ℤ) (h : Polynomial ℤ) (P : Polynomial ℚ) (N : ℤ),
        (∀ d < d₀, ℳ d = ⊥) ∧
        (PowerSeries.mk (fun n : ℕ => (Module.finrank k (ℳ (d₀ + n)) : ℤ))) *
          (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries ∧
        P.degree < (Fintype.card σ : WithBot ℕ) ∧
        ∀ d, N ≤ d → P.eval (d : ℚ) = (Module.finrank k (ℳ d) : ℚ) := by
  obtain ⟨hfin, d₀, h, P, N, hd₀, hseries, hdeg, hev⟩ := hilbertSerre k σ M ℳ hgraded
  have hlen (d : ℤ) : (Module.length k (ℳ d)).toNat = Module.finrank k (ℳ d) := by
    have _ := (hfin d).1
    rw [Module.length_eq_finrank, ENat.toNat_natCast]
  simp_rw [hlen] at hseries hev
  exact ⟨fun d ↦ (hfin d).1, d₀, h, P, N, hd₀, hseries, hdeg, hev⟩

end Headline

end TauCeti
