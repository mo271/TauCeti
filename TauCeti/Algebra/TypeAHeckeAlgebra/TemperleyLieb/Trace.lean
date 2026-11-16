/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Embedding
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.Algebra.TypeAHeckeAlgebra.TemperleyLieb.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.TraceRadical
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Markov traces, eigenprojections, and trace radicals on the Temperley–Lieb quotient

Let `q : Rˣ` and `δ = q + q⁻¹`. The surjective algebra map
`TauCeti.TypeAHeckeAlgebra.toTemperleyLieb` sends `T i + q⁻¹` to the unnormalized Temperley–Lieb
generator `e i`. Replacing `q` by `-q` in the spin-model construction
`TauCeti.TemperleyLieb.markovTrace` exhibits a unique unnormalized Markov trace on
`TemperleyLieb R δ` over every commutative ring `R`, without requiring `δ` to be a unit. Pulling
this trace back along `toTemperleyLieb` identifies the preimage of the Temperley–Lieb trace radical
with the radical of the pullback trace, places Jones's relation (11.6) inside that radical, and
transfers exact tower pullback of radicals and negligibility of Jones–Wenzl preimages.

When `s : Rˣ` satisfies `(s : R) = q + q⁻¹`, two further structures become available:

* **Normalized eigenprojections.** The elements `eigenprojection s i = s⁻¹ • (T i + q⁻¹)` on the
  finite Hecke presentation are idempotents decomposing `T i = q • P i - q⁻¹ • (1 - P i)` and
  mapping under `toTemperleyLieb` to the normalized Jones projections `s⁻¹ • e i`, which satisfy
  `P i * P j * P i = s⁻² • P i` for adjacent `i, j` (Jones parameter `τ = δ⁻²`).
* **Comparison with the Ocneanu trace.** Rescaling any Temperley–Lieb Markov trace `tr` at loop
  value `s` by `(s⁻¹) ^ n` produces a normalized Markov tower on the finite Hecke algebras with
  Markov parameter `z = s⁻¹ - q⁻¹` (corresponding to projection parameter `η = s⁻²`). By Ocneanu
  uniqueness on finite towers (`TauCeti.TypeAHeckeAlgebra.eq_ocneanuTrace_toInfinite`),
  `(s⁻¹) ^ n * tr n (toTemperleyLieb n hs x) = ocneanuTrace R q (s⁻¹ - q⁻¹) (toInfinite R q n x)`.
  Consequently `finiteRadical` at `z = s⁻¹ - q⁻¹` is the exact preimage of the Temperley–Lieb
  trace radical, pulls back exactly along `strandIncl` in **all** degrees `n : ℕ`, and gives
  canonical trace-intertwining algebra isomorphisms between the finite Hecke trace-radical
  quotients and the Temperley–Lieb trace-radical quotients compatible with the tower inclusions.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.eigenprojection`: the element `s⁻¹ • (T i + q⁻¹)` on `n` strands.
* `TauCeti.TypeAHeckeAlgebra.temperleyLiebOcneanuParam`: the Ocneanu parameter `s⁻¹ - q⁻¹`
  selected by the Temperley–Lieb quotient when `(s : R) = q + q⁻¹`.
* `TauCeti.TypeAHeckeAlgebra.finiteQuotientStrandIncl`: the injective forward tower map on finite
  Hecke trace-radical quotients at `z = s⁻¹ - q⁻¹`.
* `TauCeti.TypeAHeckeAlgebra.finiteQuotientTemperleyLiebEquiv`: the algebra isomorphism between the
  finite Hecke trace-radical quotient at `z = s⁻¹ - q⁻¹` and the Temperley–Lieb trace-radical
  quotient.

## Main results

* `TauCeti.TypeAHeckeAlgebra.existsUnique_temperleyLieb_isMarkovTrace`: existence and uniqueness of
  the unnormalized Temperley–Lieb Markov trace at `δ = q + q⁻¹` via `q ↦ -q`.
* `TauCeti.TypeAHeckeAlgebra.mul_temperleyLieb_trace_eq_ocneanuTrace`: rescaled Temperley–Lieb
  Markov traces agree with `ocneanuTrace` at `z = s⁻¹ - q⁻¹`.
* `TauCeti.TypeAHeckeAlgebra.finiteRadical_temperleyLieb_eq_comap`: `finiteRadical` at
  `z = s⁻¹ - q⁻¹` is the preimage of the Temperley–Lieb trace radical under `toTemperleyLieb`.
* `TauCeti.TypeAHeckeAlgebra.comap_finiteRadical_temperleyLieb_strandIncl`: exact pullback of
  `finiteRadical` along `strandIncl` for every `n : ℕ`.
* `TauCeti.TypeAHeckeAlgebra.quotientTrace_finiteQuotientTemperleyLiebEquiv` and
  `TauCeti.TypeAHeckeAlgebra.finiteQuotientTemperleyLiebEquiv_finiteQuotientStrandIncl`: trace and
  tower compatibility of `finiteQuotientTemperleyLiebEquiv`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5 and 11.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}

section Eigenprojection

variable (q) in
/-- The normalized generator combination `s⁻¹ • (T i + q⁻¹)` in the finite Hecke algebra. When
`(s : R) = q + q⁻¹`, this is the idempotent eigenprojection of `T i` for the eigenvalue `q`, and
its image in the Temperley–Lieb quotient is the normalized Jones projection `s⁻¹ • e i`. -/
def eigenprojection (s : Rˣ) (i : Fin (n - 1)) : TypeAHeckeAlgebra R q n :=
  (↑s⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R))

/-- Unfold `eigenprojection` in terms of `T i`. -/
theorem eigenprojection_def (s : Rˣ) (i : Fin (n - 1)) :
    eigenprojection q s i = (↑s⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R)) := (rfl)

/-- Embedding into the infinite Hecke algebra preserves `eigenprojection`. -/
@[simp]
theorem toInfinite_eigenprojection (s : Rˣ) (i : Fin (n - 1)) :
    toInfinite R q n (eigenprojection q s i) =
      (↑s⁻¹ : R) • (InfiniteTypeAHeckeAlgebra.T q i + algebraMap R _ (↑q⁻¹ : R)) := by
  simp [eigenprojection_def]

/-- Tower strand inclusions send `eigenprojection` to the corresponding generator one level up. -/
@[simp]
theorem strandIncl_eigenprojection (s : Rˣ) (i : Fin (n - 1)) :
    strandIncl R q n (eigenprojection q s i) = eigenprojection q s (Fin.castLE (by omega) i) := by
  simp [eigenprojection_def]

variable {s : Rˣ}

/-- When `(s : R) = q + q⁻¹`, `eigenprojection q s i` is idempotent. -/
theorem isIdempotentElem_eigenprojection (hs : (s : R) = (q : R) + ↑q⁻¹) (i : Fin (n - 1)) :
    IsIdempotentElem (eigenprojection q s i) := by
  rw [IsIdempotentElem]
  apply toInfinite_injective R q n
  simpa only [map_mul, toInfinite_eigenprojection] using
    (InfiniteTypeAHeckeAlgebra.isIdempotentElem_eigenprojection s hs i).eq

/-- Spectral decomposition `T i = q • P i - q⁻¹ • (1 - P i)` on the finite presentation. -/
theorem T_eq_smul_eigenprojection_sub_smul (hs : (s : R) = (q : R) + ↑q⁻¹) (i : Fin (n - 1)) :
    T q i = (q : R) • eigenprojection q s i - (↑q⁻¹ : R) • (1 - eigenprojection q s i) := by
  apply toInfinite_injective R q n
  simpa only [map_sub, map_smul, map_one, toInfinite_T, toInfinite_eigenprojection] using
    InfiniteTypeAHeckeAlgebra.T_eq_smul_eigenprojection_sub_smul s hs i

/-- Spectral decomposition `T i⁻¹ = q⁻¹ • P i - q • (1 - P i)` of the inverse generator. -/
theorem val_inv_unitT_eq_smul_eigenprojection_sub_smul (hs : (s : R) = (q : R) + ↑q⁻¹)
    (i : Fin (n - 1)) :
    (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) =
      (↑q⁻¹ : R) • eigenprojection q s i - (q : R) • (1 - eigenprojection q s i) := by
  apply toInfinite_injective R q n
  simpa only [val_inv_unitT, InfiniteTypeAHeckeAlgebra.val_inv_unitT, map_sub, map_smul, map_one,
     AlgHom.commutes, toInfinite_T, toInfinite_eigenprojection] using
    InfiniteTypeAHeckeAlgebra.val_inv_unitT_eq_smul_eigenprojection_sub_smul s hs i

/-- The Temperley–Lieb quotient sends `eigenprojection q s i` to the normalized Jones projection
`s⁻¹ • e i`. -/
@[simp]
theorem toTemperleyLieb_eigenprojection (hs : (s : R) = (q : R) + ↑q⁻¹) (i : Fin (n - 1)) :
    toTemperleyLieb n hs (eigenprojection q s i) = (↑s⁻¹ : R) • TemperleyLieb.e (s : R) i := by
  rw [eigenprojection_def, map_smul, toTemperleyLieb_T_add_algebraMap]

/-- In `TemperleyLieb R s n`, the rescaled generator `s⁻¹ • e i` is idempotent. -/
theorem isIdempotentElem_smul_e (s : Rˣ) (i : Fin (n - 1)) :
    IsIdempotentElem ((↑s⁻¹ : R) • TemperleyLieb.e (s : R) i) := by
  rw [IsIdempotentElem, smul_mul_smul_comm, TemperleyLieb.e_mul_self, smul_smul, mul_assoc,
    s.inv_mul, mul_one]

/-- Adjacent normalized Jones projections `P i = s⁻¹ • e i` in `TemperleyLieb R s n` satisfy the
Jones relation `P i * P j * P i = (s⁻¹) ^ 2 • P i` with parameter `τ = s⁻²`. -/
theorem smul_e_mul_smul_e_mul_smul_e (s : Rˣ) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    ((↑s⁻¹ : R) • TemperleyLieb.e (s : R) i) * ((↑s⁻¹ : R) • TemperleyLieb.e (s : R) j) *
        ((↑s⁻¹ : R) • TemperleyLieb.e (s : R) i) =
      ((↑s⁻¹ : R) ^ 2) • ((↑s⁻¹ : R) • TemperleyLieb.e (s : R) i) := by
  simp only [smul_mul_assoc, mul_smul_comm, TemperleyLieb.e_mul_e_mul_e h, smul_smul]
  ring_nf

/-- Jones's relator (11.6) is `(q * s) ^ 3` times the normalized projection defect
`P i * P j * P i - s⁻² • P i`. -/
theorem jonesRelator_eq_smul_eigenprojection (s : Rˣ) (i j : Fin (n - 1)) :
    jonesRelator q i j =
      ((q : R) ^ 3 * (s : R) ^ 3) •
        (eigenprojection q s i * eigenprojection q s j * eigenprojection q s i -
          ((↑s⁻¹ : R) ^ 2) • eigenprojection q s i) := by
  have hs3 : (s : R) ^ 3 * (↑s⁻¹ : R) ^ 3 = 1 := by rw [← mul_pow, s.mul_inv, one_pow]
  rw [jonesRelator_eq_smul]
  simp only [eigenprojection_def, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  match_scalars <;> grind

end Eigenprojection

section SpinTrace

/-- Negating the spin parameter `p = -q` converts the spin-model loop convention `-(p + p⁻¹)` into
the Hecke quotient loop convention `q + q⁻¹`. -/
theorem neg_neg_add_inv_neg (q : Rˣ) :
    -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) = (q : R) + ↑q⁻¹ := by
  rw [inv_neg, Units.val_neg, Units.val_neg]
  ring

/-- Rewriting `δ = q + q⁻¹` in the sign convention `δ = -(p + p⁻¹)` required by
`TauCeti.TemperleyLieb.markovTrace` at `p = -q`. -/
theorem eq_neg_add_inv_neg_of_eq_add_inv {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) :
    δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) :=
  hδ.trans (neg_neg_add_inv_neg q).symm

/-- Over every commutative ring `R`, the Temperley–Lieb tower at `δ = q + q⁻¹` admits a unique
unnormalized Markov trace, realized by the spin model at `-q`. -/
theorem existsUnique_temperleyLieb_isMarkovTrace {δ : R} (hδ : δ = (q : R) + ↑q⁻¹) :
    ∃! tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R, TemperleyLieb.IsMarkovTrace R δ tr :=
  let hδ' := eq_neg_add_inv_neg_of_eq_add_inv hδ
  ⟨fun _ ↦ TemperleyLieb.markovTrace (-q) hδ',
    TemperleyLieb.isMarkovTrace_markovTrace (-q) hδ',
    fun _ htr ↦ htr.eq_markovTrace (-q) hδ'⟩

end SpinTrace

section UnnormalizedPullback

variable {δ : R} (hδ : δ = (q : R) + ↑q⁻¹)
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- Because `toTemperleyLieb` is surjective, the trace radical of any Temperley–Lieb Markov trace
pulls back to the radical of the composite trace on `TypeAHeckeAlgebra R q n`. -/
theorem comap_traceRadical_toTemperleyLieb (htr : TemperleyLieb.IsMarkovTrace R δ tr) (n : ℕ) :
    Ideal.comap (toTemperleyLieb n hδ) ((tr n).traceRadical (htr.map_mul_comm n)) =
      ((tr n) ∘ₗ (toTemperleyLieb n hδ).toLinearMap).traceRadical
        ((tr n).comp_algHom_mul_comm (htr.map_mul_comm n) (toTemperleyLieb n hδ)) :=
  LinearMap.comap_traceRadical_of_surjective _ (htr.map_mul_comm n) (toTemperleyLieb n hδ) rfl
    (toTemperleyLieb_surjective hδ)

/-- Adjacent Jones relators lie in the preimage of the Temperley–Lieb trace radical. -/
theorem jonesRelator_mem_comap_traceRadical (htr : TemperleyLieb.IsMarkovTrace R δ tr)
    {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    jonesRelator q i j ∈
      Ideal.comap (toTemperleyLieb n hδ) ((tr n).traceRadical (htr.map_mul_comm n)) := by
  rw [Ideal.mem_comap, toTemperleyLieb_jonesRelator hδ h]
  exact zero_mem _

/-- From one strand upward, the preimage of the Temperley–Lieb trace radical pulls back along
`strandIncl`, without requiring `δ` to be a unit. -/
theorem comap_comap_traceRadical_strandIncl (htr : TemperleyLieb.IsMarkovTrace R δ tr) (n : ℕ) :
    Ideal.comap (strandIncl R q (n + 1))
        (Ideal.comap (toTemperleyLieb (n + 2) hδ)
          ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))) =
      Ideal.comap (toTemperleyLieb (n + 1) hδ)
        ((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) := by
  ext x
  simp only [Ideal.mem_comap, toTemperleyLieb_strandIncl, htr.strandIncl_mem_traceRadical_iff]

/-- Any Hecke lift of the `n`-strand Jones–Wenzl projection lies in the preimage of the
Temperley–Lieb trace radical if and only if the next quantum integer `qInt R δ (n + 1)` vanishes. -/
theorem mem_comap_traceRadical_iff_qInt_eq_zero (htr : TemperleyLieb.IsMarkovTrace R δ tr)
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) {x : TypeAHeckeAlgebra R q n}
    (hx : toTemperleyLieb n hδ x = TemperleyLieb.jonesWenzl δ n) :
    x ∈ Ideal.comap (toTemperleyLieb n hδ) ((tr n).traceRadical (htr.map_mul_comm n)) ↔
      qInt R δ (n + 1) = 0 := by
  rw [Ideal.mem_comap, hx, htr.jonesWenzl_mem_traceRadical_iff h]

end UnnormalizedPullback

section OcneanuComparison

variable (q) in
/-- The Ocneanu Markov parameter `z = s⁻¹ - q⁻¹` corresponding to the Temperley–Lieb quotient when
`(s : R) = q + q⁻¹`. -/
def temperleyLiebOcneanuParam (s : Rˣ) : R :=
  (↑s⁻¹ : R) - ↑q⁻¹

/-- Unfold `temperleyLiebOcneanuParam`. -/
theorem temperleyLiebOcneanuParam_def (s : Rˣ) :
    temperleyLiebOcneanuParam q s = (↑s⁻¹ : R) - ↑q⁻¹ := (rfl)

/-- When `(s : R) = q + q⁻¹`, the Ocneanu parameter `s⁻¹ - q⁻¹` corresponds to the projection
parameter `η = (s⁻¹) ^ 2` in `z = q * η - q⁻¹ * (1 - η)`. -/
theorem temperleyLiebOcneanuParam_eq_projection_param {s : Rˣ}
    (hs : (s : R) = (q : R) + ↑q⁻¹) :
    temperleyLiebOcneanuParam q s =
      (q : R) * (↑s⁻¹ : R) ^ 2 - (↑q⁻¹ : R) * (1 - (↑s⁻¹ : R) ^ 2) := by
  have hs' : (s : R) * ↑s⁻¹ = 1 := s.mul_inv
  rw [hs] at hs'
  rw [temperleyLiebOcneanuParam_def]
  linear_combination -(↑s⁻¹ : R) * hs'

/-- At `z = temperleyLiebOcneanuParam q s`, appending the normalized eigenprojection of the last
generator multiplies `ocneanuTrace` by `(s⁻¹) ^ 2`. -/
theorem ocneanuTrace_mul_eigenprojection {s : Rˣ} (hs : (s : R) = (q : R) + ↑q⁻¹) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q (n + 1)) :
    ocneanuTrace R q (temperleyLiebOcneanuParam q s)
        (x * (↑s⁻¹ : R) • (InfiniteTypeAHeckeAlgebra.T q n + algebraMap R _ (↑q⁻¹ : R))) =
      (↑s⁻¹ : R) ^ 2 * ocneanuTrace R q (temperleyLiebOcneanuParam q s) x :=
  (isMarkovTrace_ocneanuTrace (temperleyLiebOcneanuParam q s)).map_mul_eigenprojection s hs
    (temperleyLiebOcneanuParam_eq_projection_param hs) hx

variable {s : Rˣ}

/-- **Rescaled Temperley–Lieb Markov traces agree with the Ocneanu trace.** For `(s : R) = q + q⁻¹`
and any unnormalized Markov trace `tr` on `TemperleyLieb R s`, multiplying `tr n` on `n` strands
by `(s⁻¹) ^ n` yields the restriction of `ocneanuTrace R q (s⁻¹ - q⁻¹)` along `toInfinite`. -/
theorem mul_temperleyLieb_trace_eq_ocneanuTrace (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    (↑s⁻¹ : R) ^ n * tr n (toTemperleyLieb n hs x) =
      ocneanuTrace R q (temperleyLiebOcneanuParam q s) (toInfinite R q n x) := by
  have hs' : (↑s⁻¹ : R) * s = 1 := s.inv_mul
  let φ : ∀ m, TypeAHeckeAlgebra R q m →ₗ[R] R :=
    fun m ↦ ((↑s⁻¹ : R) ^ m) • (tr m ∘ₗ (toTemperleyLieb m hs).toLinearMap)
  refine eq_ocneanuTrace_toInfinite (z := temperleyLiebOcneanuParam q s) φ ?_ ?_ ?_ ?_ n x
  · simp [φ, htr.map_one]
  · intro m y
    rcases m with _ | m
    · obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one (by omega) y
      simp only [φ, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, map_smul, map_one, htr.map_one, pow_zero, smul_eq_mul]
      linear_combination r * hs'
    · simp only [φ, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        toTemperleyLieb_strandIncl, htr.map_strandIncl, smul_eq_mul, pow_succ]
      linear_combination (↑s⁻¹ : R) ^ (m + 1) * tr (m + 1) (toTemperleyLieb (m + 1) hs y) * hs'
  · intro m a b
    simp only [φ, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      htr.map_mul_comm]
  · intro m y
    simp only [φ, temperleyLiebOcneanuParam_def, LinearMap.smul_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, map_mul, toTemperleyLieb_strandIncl, toTemperleyLieb_T, mul_sub,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_sub, map_smul,
      htr.map_strandIncl_mul_e_last, htr.map_strandIncl, smul_eq_mul, pow_succ]
    linear_combination
      -(↑q⁻¹ : R) * (↑s⁻¹ : R) ^ (m + 1) * tr (m + 1) (toTemperleyLieb (m + 1) hs y) * hs'

/-- Unnormalized form of `mul_temperleyLieb_trace_eq_ocneanuTrace`: on `n` strands, a
Temperley–Lieb Markov trace equals `s ^ n` times `ocneanuTrace R q (s⁻¹ - q⁻¹)`. -/
theorem temperleyLieb_trace_eq_mul_ocneanuTrace (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    tr n (toTemperleyLieb n hs x) =
      (s : R) ^ n * ocneanuTrace R q (temperleyLiebOcneanuParam q s) (toInfinite R q n x) := by
  rw [← mul_temperleyLieb_trace_eq_ocneanuTrace hs htr n x, ← mul_assoc, ← mul_pow, s.mul_inv,
    one_pow, one_mul]

/-- Direct spin-model specialization of `mul_temperleyLieb_trace_eq_ocneanuTrace` at `-q`. -/
theorem mul_markovTrace_toTemperleyLieb_eq_ocneanuTrace (hs : (s : R) = (q : R) + ↑q⁻¹)
    (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    (↑s⁻¹ : R) ^ n *
        TemperleyLieb.markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
          (toTemperleyLieb n hs x) =
      ocneanuTrace R q (temperleyLiebOcneanuParam q s) (toInfinite R q n x) :=
  mul_temperleyLieb_trace_eq_ocneanuTrace hs
    (TemperleyLieb.isMarkovTrace_markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)) n x

/-- Abbreviation for the finite trace radical of `ocneanuTrace` at `temperleyLiebOcneanuParam q s`.
-/
noncomputable abbrev temperleyLiebFiniteRadical (s : Rˣ) (n : ℕ) :
    Ideal (TypeAHeckeAlgebra R q n) :=
  finiteRadical (isMarkovTrace_ocneanuTrace (q := q) (temperleyLiebOcneanuParam q s)).map_mul_comm n

/-- Abbreviation for the finite quotient trace of `ocneanuTrace` at
`temperleyLiebOcneanuParam q s`. -/
noncomputable abbrev temperleyLiebFiniteQuotientTrace (s : Rˣ) (n : ℕ) :
    TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n →ₗ[R] R :=
  finiteQuotientTrace
    (isMarkovTrace_ocneanuTrace (q := q) (temperleyLiebOcneanuParam q s)).map_mul_comm n

/-- Linear-map form of `mul_temperleyLieb_trace_eq_ocneanuTrace`. -/
private theorem smul_comp_toTemperleyLieb_eq_comp_toInfinite (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ) :
    ((↑s⁻¹ : R) ^ n) • ((tr n) ∘ₗ (toTemperleyLieb n hs).toLinearMap) =
      ocneanuTrace R q (temperleyLiebOcneanuParam q s) ∘ₗ (toInfinite R q n).toLinearMap := by
  ext x
  exact mul_temperleyLieb_trace_eq_ocneanuTrace hs htr n x

/-- **The finite Hecke trace radical at `z = s⁻¹ - q⁻¹` is the preimage of the Temperley–Lieb trace
radical.** -/
theorem finiteRadical_temperleyLieb_eq_comap (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ) :
    temperleyLiebFiniteRadical (q := q) s n =
      Ideal.comap (toTemperleyLieb n hs) ((tr n).traceRadical (htr.map_mul_comm n)) := by
  rw [comap_traceRadical_toTemperleyLieb hs htr n]
  let τ₀ := (tr n) ∘ₗ (toTemperleyLieb n hs).toLinearMap
  have hτ₀ := (tr n).comp_algHom_mul_comm (htr.map_mul_comm n) (toTemperleyLieb n hs)
  have hunit : IsUnit ((↑s⁻¹ : R) ^ n) := ((s⁻¹) ^ n).isUnit
  rw [← τ₀.traceRadical_smul_of_isUnit hτ₀ hunit]
  have heq := smul_comp_toTemperleyLieb_eq_comp_toInfinite hs htr n
  ext x
  simp only [temperleyLiebFiniteRadical, finiteRadical_def, LinearMap.mem_traceRadical, ← heq]
  rfl

/-- The kernel of `toTemperleyLieb` is contained in `temperleyLiebFiniteRadical`. -/
theorem ker_toTemperleyLieb_le_finiteRadical (hs : (s : R) = (q : R) + ↑q⁻¹) (n : ℕ) :
    RingHom.ker (toTemperleyLieb n hs) ≤ temperleyLiebFiniteRadical (q := q) s n := by
  let htr := TemperleyLieb.isMarkovTrace_markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
  rw [finiteRadical_temperleyLieb_eq_comap hs htr n]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
  exact zero_mem _

/-- Every adjacent Jones relator belongs to `temperleyLiebFiniteRadical`. -/
theorem jonesRelator_mem_finiteRadical (hs : (s : R) = (q : R) + ↑q⁻¹)
    {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    jonesRelator q i j ∈ temperleyLiebFiniteRadical (q := q) s n :=
  ker_toTemperleyLieb_le_finiteRadical hs n (toTemperleyLieb_jonesRelator hs h)

/-- Any Hecke lift of the `n`-strand Jones–Wenzl projection lies in `temperleyLiebFiniteRadical`
if and only if `qInt R s (n + 1) = 0`. -/
theorem mem_finiteRadical_iff_qInt_eq_zero (hs : (s : R) = (q : R) + ↑q⁻¹)
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R (s : R) k)) {x : TypeAHeckeAlgebra R q n}
    (hx : toTemperleyLieb n hs x = TemperleyLieb.jonesWenzl (s : R) n) :
    x ∈ temperleyLiebFiniteRadical (q := q) s n ↔ qInt R (s : R) (n + 1) = 0 := by
  let htr := TemperleyLieb.isMarkovTrace_markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
  rw [finiteRadical_temperleyLieb_eq_comap hs htr n]
  exact mem_comap_traceRadical_iff_qInt_eq_zero hs htr h hx

/-- On at most one strand, the finite radical of any Markov trace on the Hecke algebra is trivial,
because the algebra is isomorphic to `R` and the trace is normalized at `1`. -/
theorem finiteRadical_eq_bot_of_le_one {z : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (hτ : IsMarkovTrace z τ) {n : ℕ} (hn : n ≤ 1) :
    finiteRadical hτ.map_mul_comm n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := algebraMap_surjective_of_le_one hn x
  have hr0 : r = 0 := by
    have h1 := (mem_finiteRadical hτ.map_mul_comm).mp hx 1
    rwa [mul_one, AlgHom.commutes, hτ.map_algebraMap] at h1
  simp [hr0]

/-- **Exact tower pullback of finite Hecke trace radicals at `z = s⁻¹ - q⁻¹`.** For every `n : ℕ`,
including `n = 0`, pulling back `temperleyLiebFiniteRadical` along `strandIncl` recovers the
previous finite radical. -/
@[simp]
theorem comap_finiteRadical_temperleyLieb_strandIncl (hs : (s : R) = (q : R) + ↑q⁻¹) (n : ℕ) :
    Ideal.comap (strandIncl R q n) (temperleyLiebFiniteRadical (q := q) s (n + 1)) =
      temperleyLiebFiniteRadical (q := q) s n := by
  rcases n with _ | n
  · have hτ := isMarkovTrace_ocneanuTrace (q := q) (temperleyLiebOcneanuParam q s)
    rw [temperleyLiebFiniteRadical, temperleyLiebFiniteRadical,
      finiteRadical_eq_bot_of_le_one hτ le_rfl, finiteRadical_eq_bot_of_le_one hτ (by omega)]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot, map_eq_zero_iff _ (strandIncl_injective R q 0)]
  · let htr := TemperleyLieb.isMarkovTrace_markovTrace (-q) (eq_neg_add_inv_neg_of_eq_add_inv hs)
    rw [finiteRadical_temperleyLieb_eq_comap hs htr (n + 2),
      finiteRadical_temperleyLieb_eq_comap hs htr (n + 1),
      comap_comap_traceRadical_strandIncl hs htr n]

/-- Forward tower map between finite Hecke trace-radical quotients at `z = s⁻¹ - q⁻¹`. -/
noncomputable def finiteQuotientStrandIncl (s : Rˣ) (hs : (s : R) = (q : R) + ↑q⁻¹) (n : ℕ) :
    TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n →ₐ[R]
      TypeAHeckeAlgebra R q (n + 1) ⧸ temperleyLiebFiniteRadical (q := q) s (n + 1) :=
  Ideal.quotientMapₐ (temperleyLiebFiniteRadical (q := q) s (n + 1)) (strandIncl R q n)
    (comap_finiteRadical_temperleyLieb_strandIncl hs n).ge

/-- Evaluation of `finiteQuotientStrandIncl` on quotient representatives. -/
@[simp]
theorem finiteQuotientStrandIncl_mk (hs : (s : R) = (q : R) + ↑q⁻¹) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    finiteQuotientStrandIncl s hs n
        (Ideal.Quotient.mk (temperleyLiebFiniteRadical (q := q) s n) x) =
      Ideal.Quotient.mk (temperleyLiebFiniteRadical (q := q) s (n + 1)) (strandIncl R q n x) :=
  Ideal.quotient_map_mkₐ _ _ _

/-- Every tower map `finiteQuotientStrandIncl` between finite Hecke trace-radical quotients at
`z = s⁻¹ - q⁻¹` is injective. -/
theorem finiteQuotientStrandIncl_injective (hs : (s : R) = (q : R) + ↑q⁻¹) (n : ℕ) :
    Function.Injective (finiteQuotientStrandIncl s hs n) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [finiteQuotientStrandIncl_mk, finiteQuotientStrandIncl_mk, Ideal.Quotient.eq] at hxy
  exact Ideal.Quotient.eq.mpr
    ((comap_finiteRadical_temperleyLieb_strandIncl hs n) ▸
      Ideal.mem_comap.mpr (by simpa only [map_sub] using hxy))

/-- `finiteQuotientStrandIncl` preserves the normalized finite quotient trace in every degree. -/
@[simp]
theorem finiteQuotientTrace_finiteQuotientStrandIncl (hs : (s : R) = (q : R) + ↑q⁻¹) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) :
    temperleyLiebFiniteQuotientTrace s (n + 1) (finiteQuotientStrandIncl s hs n x) =
      temperleyLiebFiniteQuotientTrace s n x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientStrandIncl_mk, temperleyLiebFiniteQuotientTrace,
    temperleyLiebFiniteQuotientTrace, finiteQuotientTrace_mk, finiteQuotientTrace_mk,
    toInfinite_strandIncl]

/-- **Algebra isomorphism between the finite Hecke trace-radical quotient at `z = s⁻¹ - q⁻¹` and
the Temperley–Lieb trace-radical quotient.** -/
noncomputable def finiteQuotientTemperleyLiebEquiv (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ) :
    (TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) ≃ₐ[R]
      TemperleyLieb R (s : R) n ⧸ (tr n).traceRadical (htr.map_mul_comm n) :=
  AlgEquiv.ofBijective
    (Ideal.quotientMapₐ ((tr n).traceRadical (htr.map_mul_comm n)) (toTemperleyLieb n hs)
      (finiteRadical_temperleyLieb_eq_comap hs htr n).le)
    ⟨by
      intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.quotient_map_mkₐ, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq] at hxy
      exact Ideal.Quotient.eq.mpr
        ((finiteRadical_temperleyLieb_eq_comap hs htr n).symm ▸
          Ideal.mem_comap.mpr (by simpa only [map_sub] using hxy)),
      fun y ↦ by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨a, rfl⟩ := toTemperleyLieb_surjective hs b
        exact ⟨Ideal.Quotient.mk _ a, Ideal.quotient_map_mkₐ _ _ _⟩⟩

/-- `finiteQuotientTemperleyLiebEquiv` acts on quotient representatives via `toTemperleyLieb`. -/
@[simp]
theorem finiteQuotientTemperleyLiebEquiv_mk (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    finiteQuotientTemperleyLiebEquiv hs htr n
        (Ideal.Quotient.mk (temperleyLiebFiniteRadical (q := q) s n) x) =
      Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) (toTemperleyLieb n hs x) :=
  Ideal.quotient_map_mkₐ ((tr n).traceRadical (htr.map_mul_comm n)) (toTemperleyLieb n hs)
    (finiteRadical_temperleyLieb_eq_comap hs htr n).le

/-- The Temperley–Lieb quotient trace under `finiteQuotientTemperleyLiebEquiv` is `s ^ n` times the
normalized Hecke quotient trace. -/
@[simp]
theorem quotientTrace_finiteQuotientTemperleyLiebEquiv (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) :
    (tr n).quotientTrace (htr.map_mul_comm n) (finiteQuotientTemperleyLiebEquiv hs htr n x) =
      (s : R) ^ n * temperleyLiebFiniteQuotientTrace s n x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientTemperleyLiebEquiv_mk, LinearMap.quotientTrace_mk,
    temperleyLiebFiniteQuotientTrace, finiteQuotientTrace_mk,
    temperleyLieb_trace_eq_mul_ocneanuTrace hs htr n x]

/-- Rescaling the Temperley–Lieb quotient trace by `(s⁻¹) ^ n` recovers the normalized Hecke
quotient trace along `finiteQuotientTemperleyLiebEquiv`. -/
theorem mul_quotientTrace_finiteQuotientTemperleyLiebEquiv (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ temperleyLiebFiniteRadical (q := q) s n) :
    (↑s⁻¹ : R) ^ n *
        (tr n).quotientTrace (htr.map_mul_comm n) (finiteQuotientTemperleyLiebEquiv hs htr n x) =
      temperleyLiebFiniteQuotientTrace s n x := by
  rw [quotientTrace_finiteQuotientTemperleyLiebEquiv, ← mul_assoc, ← mul_pow, s.inv_mul, one_pow,
    one_mul]

/-- The quotient isomorphisms `finiteQuotientTemperleyLiebEquiv` commute with the tower inclusions
from one strand upward. -/
@[simp]
theorem finiteQuotientTemperleyLiebEquiv_finiteQuotientStrandIncl
    (hs : (s : R) = (q : R) + ↑q⁻¹)
    {tr : ∀ n : ℕ, TemperleyLieb R (s : R) n →ₗ[R] R}
    (htr : TemperleyLieb.IsMarkovTrace R (s : R) tr) (n : ℕ)
    (x : TypeAHeckeAlgebra R q (n + 1) ⧸ temperleyLiebFiniteRadical (q := q) s (n + 1)) :
    finiteQuotientTemperleyLiebEquiv hs htr (n + 2) (finiteQuotientStrandIncl s hs (n + 1) x) =
      htr.quotientStrandIncl n (finiteQuotientTemperleyLiebEquiv hs htr (n + 1) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [finiteQuotientStrandIncl_mk, finiteQuotientTemperleyLiebEquiv_mk,
    finiteQuotientTemperleyLiebEquiv_mk, htr.quotientStrandIncl_mk, toTemperleyLieb_strandIncl]

end OcneanuComparison

end TauCeti.TypeAHeckeAlgebra
