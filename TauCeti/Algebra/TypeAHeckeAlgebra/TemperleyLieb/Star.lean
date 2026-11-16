/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.TemperleyLieb.Trace
public import TauCeti.RingTheory.TraceFunctional.Positive
import Mathlib.Algebra.Star.LinearMap
import TauCeti.Algebra.TemperleyLieb.SpinPositivity

/-!
# Real-parameter star transport and continuous-range positivity on the Temperley–Lieb quotient

In the real-parameter involution of `TauCeti.Algebra.TypeAHeckeAlgebra.Star`, where
`Fact (IsSelfAdjoint (q : R))`, every Hecke generator `T i` is self-adjoint. Hence `δ = q + q⁻¹`
is self-adjoint, the surjective quotient map `toTemperleyLieb` preserves `star`, and the normalized
eigenprojections `eigenprojection q s i = s⁻¹ • (T i + q⁻¹)` (when `(s : R) = q + q⁻¹`) are
orthogonal star projections mapping onto the normalized Jones projections `s⁻¹ • e i`.

On the infinite Hecke algebra, `ocneanuTrace R q z` conjugates under `star` to
`ocneanuTrace R q (star z)`. At any self-adjoint `s : Rˣ`, the Temperley–Lieb parameter
`temperleyLiebOcneanuParam q s = s⁻¹ - q⁻¹` is self-adjoint, so `temperleyLiebFiniteRadical` is
star-stable and `finiteQuotientTemperleyLiebEquiv` upgrades to a trace-intertwining star algebra
isomorphism `finiteQuotientTemperleyLiebStarEquiv`.

Over `ℂ`, a positive real parameter `0 < r` with `(q : ℂ) = r` gives loop parameter
`δ = r + r⁻¹ ≥ 2`, sweeping out the entire continuous Powers / Temperley–Lieb index range
`τ = (r + r⁻¹)⁻² ∈ (0, 1 / 4]`. Transporting spin-model positivity from
`TauCeti.Algebra.TemperleyLieb.SpinPositivity` yields unconditional positivity of both the
Temperley–Lieb pullback trace and `ocneanuTrace ℂ q ((r + r⁻¹)⁻¹ - r⁻¹)` on every finite stage,
packaging the restricted Ocneanu trace as a normalized tracial `StarPositiveFunctional` whose GNS
null space is `temperleyLiebFiniteRadical`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.toTemperleyLiebStarAlgHom`: `toTemperleyLieb` bundled as a star
  algebra homomorphism in the real-parameter fiber.
* `TauCeti.TypeAHeckeAlgebra.finiteQuotientStrandInclStarAlgHom`: the star algebra tower inclusion
  on finite Hecke trace-radical quotients.
* `TauCeti.TypeAHeckeAlgebra.finiteQuotientTemperleyLiebStarEquiv`: the star algebra isomorphism
  between finite Hecke and Temperley–Lieb trace-radical quotients.
* `TauCeti.TypeAHeckeAlgebra.temperleyLiebPositiveTrace`: the bundled `StarPositiveFunctional` on
  `TypeAHeckeAlgebra ℂ q n` for positive real `q = r > 0`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star`: `ocneanuTrace R q z (star x) =
  star (ocneanuTrace R q (star z) x)` in the real-parameter fiber.
* `TauCeti.TypeAHeckeAlgebra.isStarProjection_eigenprojection`: `eigenprojection q s i` is a star
  projection.
* `TauCeti.TypeAHeckeAlgebra.surjOn_inv_add_inv_sq`: `r ↦ ((r + r⁻¹) ^ 2)⁻¹` maps `(0, ∞)` onto
  `(0, 1 / 4]`.
* `TauCeti.TypeAHeckeAlgebra.ocneanuTrace_temperleyLieb_star_mul_self_nonneg`: unconditional
  positivity of `ocneanuTrace` on `n` strands at `z = (r + r⁻¹)⁻¹ - r⁻¹` for `r > 0`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4, 5, and 11.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [Fact (IsSelfAdjoint (q : R))]

/-- In the real-parameter involution, `ocneanuTrace R q z` conjugates under `star` to
`ocneanuTrace R q (star z)`. -/
@[simp]
theorem ocneanuTrace_star (z : R) (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q z (star x) = star (ocneanuTrace R q (star z) x) := by
  let τ' : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R :=
    (star (WithConv.toConv (ocneanuTrace R q (star z)))).ofConv
  have happly (y : InfiniteTypeAHeckeAlgebra R q) :
      τ' y = star (ocneanuTrace R q (star z) (star y)) := by
    simp [τ']
  have hτ : IsMarkovTrace (star z) (ocneanuTrace R q (star z)) :=
    isMarkovTrace_ocneanuTrace (star z)
  have hτ' : IsMarkovTrace z τ' :=
    { map_one := by simp [happly]
      map_mul_comm a b := by simp only [happly, star_mul, hτ.map_mul_comm (star b)]
      map_mul_T {n a} ha := by
        have hsa : star a ∈ stage R q (n + 1) := star_mem_stage_iff.mpr ha
        rw [happly, star_mul, star_T, hτ.map_mul_comm (T q n), hτ.map_mul_T hsa, star_mul,
          star_star, ← happly, mul_comm] }
  have heq := LinearMap.congr_fun hτ'.eq_ocneanuTrace (star x)
  simpa only [happly, star_star] using heq.symm

/-- At a self-adjoint parameter `z`, `ocneanuTrace R q z` preserves the real-parameter involution.
-/
theorem ocneanuTrace_star_of_isSelfAdjoint {z : R} (hz : IsSelfAdjoint z)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q z (star x) = star (ocneanuTrace R q z x) := by
  rw [ocneanuTrace_star, hz.star_eq]

end TauCeti.InfiniteTypeAHeckeAlgebra

namespace TauCeti.TypeAHeckeAlgebra

open InfiniteTypeAHeckeAlgebra

section StarRing

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} {n : ℕ}
variable [hq : Fact (IsSelfAdjoint (q : R))]

/-- When `q` is self-adjoint, its inverse `q⁻¹` is self-adjoint as well. -/
theorem isSelfAdjoint_val_inv : IsSelfAdjoint (↑q⁻¹ : R) := by
  simpa only [Ring.inverse_unit] using hq.out.ringInverse

/-- When `q` is self-adjoint, the loop parameter `δ = q + q⁻¹` is self-adjoint. -/
theorem isSelfAdjoint_add_inv {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) : IsSelfAdjoint δ :=
  hδ ▸ hq.out.add isSelfAdjoint_val_inv

/-- In the real-parameter convention, `toTemperleyLieb` commutes with `star`. -/
@[simp]
theorem toTemperleyLieb_star {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) [Fact (IsSelfAdjoint δ)]
    (x : TypeAHeckeAlgebra R q n) :
    toTemperleyLieb n hδ (star x) = star (toTemperleyLieb n hδ x) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by simp [adjoin_range_T]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [star_T, toTemperleyLieb_T, ← algebraMap_star_comm, isSelfAdjoint_val_inv.star_eq]
  | algebraMap r => simp [← algebraMap_star_comm]
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

variable (n) in
/-- `toTemperleyLieb` bundled as a star algebra homomorphism in the real-parameter fiber. -/
def toTemperleyLiebStarAlgHom {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) [Fact (IsSelfAdjoint δ)] :
    TypeAHeckeAlgebra R q n →⋆ₐ[R] TemperleyLieb R δ n :=
  { toTemperleyLieb n hδ with map_star' := toTemperleyLieb_star hδ }

/-- Forgetting star compatibility recovers `toTemperleyLieb`. -/
@[simp]
theorem toAlgHom_toTemperleyLiebStarAlgHom {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint δ)] :
    (toTemperleyLiebStarAlgHom n hδ).toAlgHom = toTemperleyLieb n hδ := (rfl)

/-- Evaluating `toTemperleyLiebStarAlgHom` agrees with `toTemperleyLieb`. -/
@[simp]
theorem toTemperleyLiebStarAlgHom_apply {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint δ)] (x : TypeAHeckeAlgebra R q n) :
    toTemperleyLiebStarAlgHom n hδ x = toTemperleyLieb n hδ x := (rfl)

/-- `toTemperleyLiebStarAlgHom` is surjective. -/
theorem toTemperleyLiebStarAlgHom_surjective {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint δ)] :
    Function.Surjective (toTemperleyLiebStarAlgHom n hδ) :=
  toTemperleyLieb_surjective hδ

/-- For self-adjoint `s : Rˣ`, `eigenprojection q s i` is self-adjoint in the real-parameter fiber.
-/
theorem isSelfAdjoint_eigenprojection {s : Rˣ} (hs_sa : IsSelfAdjoint (s : R))
    (i : Fin (n - 1)) : IsSelfAdjoint (eigenprojection q s i) := by
  have hsinv : IsSelfAdjoint (↑s⁻¹ : R) := by
    simpa only [Ring.inverse_unit] using hs_sa.ringInverse
  rw [IsSelfAdjoint, eigenprojection_def, star_smul, hsinv.star_eq, star_add, star_T,
    ← algebraMap_star_comm, (isSelfAdjoint_val_inv (q := q)).star_eq]

/-- In the real-parameter fiber, `eigenprojection q s i` is a star projection when
`(s : R) = q + q⁻¹`. -/
theorem isStarProjection_eigenprojection {s : Rˣ} (hs : (s : R) = (q : R) + ↑q⁻¹)
    (i : Fin (n - 1)) : IsStarProjection (eigenprojection q s i) :=
  ⟨isIdempotentElem_eigenprojection hs i,
    isSelfAdjoint_eigenprojection (isSelfAdjoint_add_inv hs) i⟩

/-- In `TemperleyLieb R s n` with self-adjoint `s`, the normalized Jones projection `s⁻¹ • e i` is
a star projection. -/
theorem isStarProjection_smul_e (s : Rˣ) [hs_sa : Fact (IsSelfAdjoint (s : R))]
    (i : Fin (n - 1)) : IsStarProjection ((↑s⁻¹ : R) • TemperleyLieb.e (s : R) i) := by
  have hsinv : IsSelfAdjoint (↑s⁻¹ : R) := by
    simpa only [Ring.inverse_unit] using hs_sa.out.ringInverse
  exact ⟨isIdempotentElem_smul_e s i, by
    rw [IsSelfAdjoint, star_smul, hsinv.star_eq, TemperleyLieb.star_e]⟩

/-- For self-adjoint `s : Rˣ`, `temperleyLiebOcneanuParam q s` is self-adjoint. -/
theorem isSelfAdjoint_temperleyLiebOcneanuParam {s : Rˣ} (hs_sa : IsSelfAdjoint (s : R)) :
    IsSelfAdjoint (temperleyLiebOcneanuParam q s) := by
  have hsinv : IsSelfAdjoint (↑s⁻¹ : R) := by
    simpa only [Ring.inverse_unit] using hs_sa.ringInverse
  rw [temperleyLiebOcneanuParam_def]
  exact hsinv.sub (isSelfAdjoint_val_inv (q := q))

/-- At self-adjoint `s : Rˣ`, `temperleyLiebFiniteRadical` is invariant under the real-parameter
involution. -/
instance instIsStarTemperleyLiebFiniteRadical (s : Rˣ) [hs_sa : Fact (IsSelfAdjoint (s : R))]
    (n : ℕ) : (temperleyLiebFiniteRadical (q := q) s n).IsStar := by
  rw [temperleyLiebFiniteRadical, finiteRadical_def]
  refine LinearMap.isStar_traceRadical _ _ fun x ↦ ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, toInfinite_star]
  exact ocneanuTrace_star_of_isSelfAdjoint
    (isSelfAdjoint_temperleyLiebOcneanuParam (q := q) hs_sa.out) (toInfinite R q n x)

/-- At a self-adjoint loop parameter, the trace radical of any Temperley–Lieb Markov trace is
star-stable. -/
theorem isStar_temperleyLieb_traceRadical {δ : R} [Fact (IsSelfAdjoint δ)]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R δ tr) (n : ℕ) :
    ((tr n).traceRadical (htr.map_mul_comm n)).IsStar :=
  (tr n).isStar_traceRadical (htr.map_mul_comm n) (htr.map_star n)

/-- Forward tower map between finite Hecke trace-radical quotients bundled as a star algebra
homomorphism. -/
noncomputable def finiteQuotientStrandInclStarAlgHom (s : Rˣ) (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))] (n : ℕ) :
    TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n →⋆ₐ[R]
      TypeAHeckeAlgebra R q (n + 1) ⧸ temperleyLiebFiniteRadical (q := q) s (n + 1) :=
  Ideal.quotientStarAlgHom (temperleyLiebFiniteRadical (q := q) s (n + 1))
    { strandIncl R q n with map_star' := strandIncl_star }
    (comap_finiteRadical_temperleyLieb_strandIncl hs n).ge

/-- Evaluating `finiteQuotientStrandInclStarAlgHom` agrees with `finiteQuotientStrandIncl`. -/
@[simp]
theorem finiteQuotientStrandInclStarAlgHom_apply (s : Rˣ) (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))] (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) :
    finiteQuotientStrandInclStarAlgHom s hs n x = finiteQuotientStrandIncl s hs n x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientStrandInclStarAlgHom, Ideal.quotientStarAlgHom_mk, finiteQuotientStrandIncl_mk]
  rfl

/-- **Star algebra isomorphism between the finite Hecke trace-radical quotient and the
Temperley–Lieb trace-radical quotient in the real-parameter fiber.** -/
noncomputable def finiteQuotientTemperleyLiebStarEquiv {s : Rˣ} (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))]
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) ≃⋆ₐ[R]
      TemperleyLieb R (s : R) n ⧸ (tr n).traceRadical (htr.map_mul_comm n) :=
  Ideal.quotientStarAlgEquivOfSurjective ((tr n).traceRadical (htr.map_mul_comm n))
    (toTemperleyLiebStarAlgHom n hs)
    (by
      rw [toAlgHom_toTemperleyLiebStarAlgHom]
      exact finiteRadical_temperleyLieb_eq_comap hs htr n)
    (toTemperleyLiebStarAlgHom_surjective hs)

/-- `finiteQuotientTemperleyLiebStarEquiv` acts on quotient representatives by `toTemperleyLieb`.
-/
@[simp]
theorem finiteQuotientTemperleyLiebStarEquiv_mk {s : Rˣ} (hs : (s : R) = (q : R) + ↑q⁻¹)
    [Fact (IsSelfAdjoint (s : R))]
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] (x : TypeAHeckeAlgebra R q n) :
    finiteQuotientTemperleyLiebStarEquiv hs htr
        (Ideal.Quotient.mk (temperleyLiebFiniteRadical (q := q) s n) x) =
      Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) (toTemperleyLieb n hs x) :=
  Ideal.quotientStarAlgEquivOfSurjective_mk ((tr n).traceRadical (htr.map_mul_comm n))
    (toTemperleyLiebStarAlgHom n hs) _ (toTemperleyLiebStarAlgHom_surjective hs) x

/-- `finiteQuotientTemperleyLiebStarEquiv` intertwines the quotient traces up to `s ^ n`. -/
@[simp]
theorem quotientTrace_finiteQuotientTemperleyLiebStarEquiv {s : Rˣ}
    (hs : (s : R) = (q : R) + ↑q⁻¹) [Fact (IsSelfAdjoint (s : R))]
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) :
    (tr n).quotientTrace (htr.map_mul_comm n) (finiteQuotientTemperleyLiebStarEquiv hs htr x) =
      (s : R) ^ n * temperleyLiebFiniteQuotientTrace s n x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientTemperleyLiebStarEquiv_mk, LinearMap.quotientTrace_mk,
    temperleyLiebFiniteQuotientTrace, finiteQuotientTrace_mk,
    temperleyLieb_trace_eq_mul_ocneanuTrace hs htr n x]

end StarRing

section ContinuousRangePositivity

open scoped ComplexOrder

/-- For any positive real `r`, `r + r⁻¹ ≥ 2`. -/
theorem two_le_add_inv_of_pos {r : ℝ} (hr : 0 < r) : 2 ≤ r + r⁻¹ := by
  have hsq : 0 ≤ (r - 1) ^ 2 := sq_nonneg (r - 1)
  have hmul : 2 * r ≤ r ^ 2 + 1 := by linarith
  have hdiv := (le_div_iff₀ hr).mpr hmul
  have hne : r ≠ 0 := hr.ne'
  have heq : (r ^ 2 + 1) / r = r + r⁻¹ := by field_simp
  rwa [heq] at hdiv

/-- For `0 < r`, the Jones projection parameter `((r + r⁻¹) ^ 2)⁻¹` lies in `(0, 1 / 4]`. -/
theorem inv_add_inv_sq_mem_Ioc {r : ℝ} (hr : 0 < r) :
    ((r + r⁻¹) ^ 2)⁻¹ ∈ Set.Ioc (0 : ℝ) (1 / 4) := by
  have h2 : 2 ≤ r + r⁻¹ := two_le_add_inv_of_pos hr
  have h4 : (4 : ℝ) ≤ (r + r⁻¹) ^ 2 := by nlinarith
  refine ⟨inv_pos.mpr (by positivity), ?_⟩
  rw [one_div]
  exact inv_anti₀ (by positivity) h4

/-- Positive real Hecke parameters `r > 0` exhaust the continuous Powers / Temperley–Lieb index
range `τ ∈ (0, 1 / 4]` under `r ↦ ((r + r⁻¹) ^ 2)⁻¹`. -/
theorem surjOn_inv_add_inv_sq :
    Set.SurjOn (fun r : ℝ ↦ ((r + r⁻¹) ^ 2)⁻¹) (Set.Ioi 0) (Set.Ioc 0 (1 / 4)) := by
  rintro τ ⟨hτ0, hτ4⟩
  let δ : ℝ := (√τ)⁻¹
  have hsqrt_pos : 0 < √τ := Real.sqrt_pos.mpr hτ0
  have hδ2 : 2 ≤ δ := by
    have hle : √τ ≤ 1 / 2 := by nlinarith [Real.sq_sqrt hτ0.le, Real.sqrt_nonneg τ]
    have hinv := inv_anti₀ hsqrt_pos hle
    simpa [δ] using hinv
  let r : ℝ := (δ + √(δ ^ 2 - 4)) / 2
  have hdisc : 0 ≤ δ ^ 2 - 4 := by nlinarith
  have hr_pos : 0 < r := by
    have h0 : 0 ≤ √(δ ^ 2 - 4) := Real.sqrt_nonneg _
    dsimp [r]
    linarith
  refine ⟨r, hr_pos, ?_⟩
  let r' : ℝ := (δ - √(δ ^ 2 - 4)) / 2
  have hrr' : r * r' = 1 := by
    dsimp [r, r']
    have hsq : √(δ ^ 2 - 4) ^ 2 = δ ^ 2 - 4 := Real.sq_sqrt hdisc
    nlinarith
  have hinv_r : r⁻¹ = r' := inv_eq_of_mul_eq_one_right hrr'
  have hsum : r + r⁻¹ = δ := by
    rw [hinv_r]
    dsimp [r, r']
    ring
  dsimp only
  rw [hsum]
  dsimp [δ]
  rw [inv_pow, Real.sq_sqrt hτ0.le, inv_inv]

/-- **Continuous-range positivity on the Temperley–Lieb pullback.** For a positive real Hecke
parameter `0 < r` and loop value `δ = r + r⁻¹`, pulling back any Temperley–Lieb Markov trace along
`toTemperleyLieb` yields a positive semidefinite Hermitian form on every number of strands. -/
theorem temperleyLieb_pullback_star_mul_self_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδr : δ = r + r⁻¹)
    (hδ : (δ : ℂ) = (q : ℂ) + ↑q⁻¹) [Fact (IsSelfAdjoint (δ : ℂ))]
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : TemperleyLieb.IsMarkovTrace ℂ (δ : ℂ) tr) (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    0 ≤ tr n (toTemperleyLieb n hδ (star x * x)) := by
  have h2 : 2 ≤ δ := hδr ▸ two_le_add_inv_of_pos hr
  rw [map_mul, toTemperleyLieb_star]
  exact htr.map_star_mul_self_nonneg_of_two_le h2 (toTemperleyLieb n hδ x)

/-- **Continuous-range positivity of the Ocneanu trace.** For `0 < r` with `(s : ℂ) = r + r⁻¹` and
`(s : ℂ) = q + q⁻¹`, `ocneanuTrace ℂ q (s⁻¹ - q⁻¹)` is positive semidefinite on every finite Hecke
algebra `TypeAHeckeAlgebra ℂ q n`. -/
theorem ocneanuTrace_temperleyLieb_star_mul_self_nonneg {q s : ℂˣ}
    [Fact (IsSelfAdjoint (q : ℂ))] {r : ℝ} (hr : 0 < r)
    (hsr : (s : ℂ) = ((r + r⁻¹ : ℝ) : ℂ)) (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹)
    (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    0 ≤ ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) (toInfinite ℂ q n (star x * x)) := by
  let δ : ℝ := r + r⁻¹
  have hδ_pos : 0 < δ := by linarith [two_le_add_inv_of_pos hr]
  let s₀ : ℂˣ := Units.mk0 (δ : ℂ) (Complex.ofReal_ne_zero.mpr hδ_pos.ne')
  have hs_eq : s = s₀ := Units.ext hsr
  subst hs_eq
  have : Fact (IsSelfAdjoint (δ : ℂ)) := ⟨Complex.conj_ofReal δ⟩
  let htr := TemperleyLieb.isMarkovTrace_markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
  rw [← mul_temperleyLieb_trace_eq_ocneanuTrace hs htr n (star x * x)]
  have hsinv : (↑s₀⁻¹ : ℂ) = ((δ⁻¹ : ℝ) : ℂ) := by
    apply Units.inv_eq_of_mul_eq_one_right
    -- Unfold `(s₀ : ℂ)` of `Units.mk0` to `(δ : ℂ)`.
    change (δ : ℂ) * ((δ⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hδ_pos.ne', Complex.ofReal_one]
  rw [hsinv, ← Complex.ofReal_pow]
  have hpow : (0 : ℂ) ≤ ((δ⁻¹ ^ n : ℝ) : ℂ) := Complex.zero_le_real.mpr (by positivity)
  have htr_nonneg :
      0 ≤ TemperleyLieb.markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
        (toTemperleyLieb n hs (star x * x)) :=
    temperleyLieb_pullback_star_mul_self_nonneg hr rfl hs htr n x
  exact mul_nonneg hpow htr_nonneg

/-- Bundled `StarPositiveFunctional` on `TypeAHeckeAlgebra ℂ q n` induced by `ocneanuTrace` at the
Temperley–Lieb parameter `z = (r + r⁻¹)⁻¹ - q⁻¹` for `0 < r`. -/
noncomputable def temperleyLiebPositiveTrace {q s : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {r : ℝ} (hr : 0 < r) (hsr : (s : ℂ) = ((r + r⁻¹ : ℝ) : ℂ))
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) ∘ₗ (toInfinite ℂ q n).toLinearMap
  square_nonneg x := ocneanuTrace_temperleyLieb_star_mul_self_nonneg hr hsr hs n x

/-- Underlying linear map of `temperleyLiebPositiveTrace`. -/
@[simp]
theorem toLinearMap_temperleyLiebPositiveTrace {q s : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {r : ℝ} (hr : 0 < r) (hsr : (s : ℂ) = ((r + r⁻¹ : ℝ) : ℂ))
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    (temperleyLiebPositiveTrace hr hsr hs n).toLinearMap =
      ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) ∘ₗ (toInfinite ℂ q n).toLinearMap := (rfl)

/-- Evaluating `temperleyLiebPositiveTrace` recovers `ocneanuTrace` along `toInfinite`. -/
@[simp]
theorem temperleyLiebPositiveTrace_apply {q s : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {r : ℝ} (hr : 0 < r) (hsr : (s : ℂ) = ((r + r⁻¹ : ℝ) : ℂ))
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    temperleyLiebPositiveTrace hr hsr hs n x =
      ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s) (toInfinite ℂ q n x) := (rfl)

/-- `temperleyLiebPositiveTrace` is normalized at `1`. -/
theorem temperleyLiebPositiveTrace_one {q s : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {r : ℝ} (hr : 0 < r) (hsr : (s : ℂ) = ((r + r⁻¹ : ℝ) : ℂ))
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    temperleyLiebPositiveTrace hr hsr hs n 1 = 1 := by
  simp

/-- The GNS null space of `temperleyLiebPositiveTrace` is the underlying complex submodule of
`temperleyLiebFiniteRadical`. -/
theorem nullSubmodule_temperleyLiebPositiveTrace {q s : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {r : ℝ} (hr : 0 < r) (hsr : (s : ℂ) = ((r + r⁻¹ : ℝ) : ℂ))
    (hs : (s : ℂ) = (q : ℂ) + ↑q⁻¹) (n : ℕ) :
    (temperleyLiebPositiveTrace hr hsr hs n).nullSubmodule =
      (temperleyLiebFiniteRadical (q := q) s n).restrictScalars ℂ := by
  have hcomm := (ocneanuTrace ℂ q (temperleyLiebOcneanuParam q s)).comp_algHom_mul_comm
    (isMarkovTrace_ocneanuTrace (q := q) (temperleyLiebOcneanuParam q s)).map_mul_comm
    (toInfinite ℂ q n)
  rw [(temperleyLiebPositiveTrace hr hsr hs n).nullSubmodule_eq_traceRadical hcomm,
    temperleyLiebFiniteRadical, finiteRadical_def]
  ext x
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_traceRadical,
    toLinearMap_temperleyLiebPositiveTrace]

end ContinuousRangePositivity

end TauCeti.TypeAHeckeAlgebra
