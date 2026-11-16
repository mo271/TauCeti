/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import TauCeti.Analysis.Normed.Unbundled.RootBound
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Irreducible

/-!
# Spectral norm on finite reduced algebras

Let `L` be a module-finite reduced commutative algebra over a field `F`. Being Artinian and
reduced, `L` decomposes via `IsArtinianRing.equivPi` as the finite product of its residue fields
`L ⧸ m.asIdeal` over `m : MaximalSpectrum L`, each of which is a finite field extension of `F`.

For `x : L`, the minimal polynomial `minpoly F x` is the product of the distinct minimal
polynomials `minpoly F (Ideal.Quotient.mk m.asIdeal x)` across the maximal ideals `m` of `L`.
When `F` carries an ultrametric field norm (not assumed complete or nontrivially normed),
`spectralValue (minpoly F x)` equals the supremum of the residue-field spectral norms
`spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x)`. Bundling `x ↦ spectralValue
(minpoly F x)` therefore produces a nonarchimedean power-multiplicative `F`-algebra norm
`TauCeti.reducedSpectralAlgNorm F L`.

When `F` is weakly stable (`TauCeti.IsWeaklyStable F`), every `F`-linear functional on `L` is
bounded with respect to `reducedSpectralAlgNorm F L`, and `reducedSpectralAlgNorm F L` is
equivalent to the coordinate norm of every finite nonempty `F`-basis of `L`.

## Main definitions

* `TauCeti.reducedSpectralAlgNorm`: `x ↦ spectralValue (minpoly F x)` bundled as an
  `AlgebraNorm F L` on a module-finite reduced commutative `F`-algebra `L`.

## Main results

* `TauCeti.minpoly_eq_prod_minimalPolynomials_maximalSpectrum`: `minpoly F x` is the product of
  the distinct minimal polynomials of the residues of `x` at `MaximalSpectrum L`.
* `TauCeti.spectralValue_minpoly_eq_iSup_maximalSpectrum`: `spectralValue (minpoly F x)` equals
  the supremum over `m : MaximalSpectrum L` of the spectral norm of `x mod m`.
* `TauCeti.isNonarchimedean_reducedSpectralAlgNorm` and
  `TauCeti.isPowMul_reducedSpectralAlgNorm`: `reducedSpectralAlgNorm F L` is nonarchimedean and
  power-multiplicative.
* `TauCeti.IsWeaklyStable.exists_bound_reducedSpectralAlgNorm`: over a weakly stable field `F`,
  every `F`-linear functional on `L` is bounded by `reducedSpectralAlgNorm F L`.
* `TauCeti.IsWeaklyStable.exists_basis_norm_comparison_of_isReduced`: over a weakly stable field
  `F`, `reducedSpectralAlgNorm F L` is equivalent to every finite-basis coordinate norm on `L`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.8.1 and §3.8.3.
-/

public section

open Polynomial

namespace TauCeti

section Minpoly

variable {F L : Type*} [Field F] [CommRing L] [Algebra F L]

/-- At any maximal ideal `m` of a commutative `F`-algebra `L`, the minimal polynomial over `F` of
the residue of `x : L` in `L ⧸ m.asIdeal` divides `minpoly F x`. -/
theorem minpoly_quotientMk_dvd_minpoly (m : MaximalSpectrum L) (x : L) :
    minpoly F (Ideal.Quotient.mk m.asIdeal x) ∣ minpoly F x := by
  apply minpoly.dvd
  rw [← Ideal.Quotient.mkₐ_eq_mk F m.asIdeal, aeval_algHom_apply, minpoly.aeval, map_zero]

private theorem eq_of_monic_of_irreducible_of_dvd {p q : F[X]}
    (hp : p.Monic) (hq : q.Monic) (hpi : Irreducible p) (hqi : Irreducible q) (hdvd : p ∣ q) :
    p = q :=
  eq_of_monic_of_associated hp hq (associated_of_dvd_dvd hdvd (hpi.dvd_symm hqi hdvd))

variable [Module.Finite F L] [IsReduced L]

/-- In a module-finite reduced commutative `F`-algebra `L`, the minimal polynomial of `x : L` over
`F` is the product of the distinct minimal polynomials of the residues of `x` across
`MaximalSpectrum L`. -/
theorem minpoly_eq_prod_minimalPolynomials_maximalSpectrum (x : L) :
    haveI : IsArtinianRing L := .of_finite F L
    minpoly F x =
      ∏ q ∈ (Set.finite_range fun m : MaximalSpectrum L ↦
        minpoly F (Ideal.Quotient.mk m.asIdeal x)).toFinset, q := by
  have : IsArtinianRing L := .of_finite F L
  set s := (Set.finite_range fun m : MaximalSpectrum L ↦
    minpoly F (Ideal.Quotient.mk m.asIdeal x)).toFinset
  have hs_mem (q : F[X]) :
      q ∈ s ↔ ∃ m : MaximalSpectrum L, minpoly F (Ideal.Quotient.mk m.asIdeal x) = q := by
    simp [s]
  have hs_monic_irred {q : F[X]} (hq : q ∈ s) : q.Monic ∧ Irreducible q := by
    obtain ⟨m, rfl⟩ := (hs_mem q).mp hq
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hint : IsIntegral F (Ideal.Quotient.mk m.asIdeal x) := Algebra.IsIntegral.isIntegral _
    exact ⟨minpoly.monic hint, minpoly.irreducible hint⟩
  have hcop : (s : Set F[X]).Pairwise IsCoprime := by
    intro p hp q hq hpq
    obtain ⟨hpm, hpi⟩ := hs_monic_irred hp
    obtain ⟨hqm, hqi⟩ := hs_monic_irred hq
    rw [hpi.coprime_iff_not_dvd]
    exact fun hdvd ↦ hpq (eq_of_monic_of_irreducible_of_dvd hpm hqm hpi hqi hdvd)
  have hprod_dvd : (∏ q ∈ s, q) ∣ minpoly F x := by
    refine Finset.prod_dvd_of_coprime hcop fun q hq ↦ ?_
    obtain ⟨m, rfl⟩ := (hs_mem q).mp hq
    exact minpoly_quotientMk_dvd_minpoly m x
  have hdvd_prod : minpoly F x ∣ ∏ q ∈ s, q := by
    refine minpoly.dvd F x ?_
    apply (IsArtinianRing.equivPi L).injective
    rw [map_zero]
    ext m
    rw [Pi.zero_apply, IsArtinianRing.equivPi_apply, ← Ideal.Quotient.mkₐ_eq_mk F m.asIdeal,
      ← aeval_algHom_apply, map_prod]
    refine Finset.prod_eq_zero ((hs_mem _).mpr ⟨m, rfl⟩) ?_
    simpa only [Ideal.Quotient.mkₐ_eq_mk] using minpoly.aeval F (Ideal.Quotient.mk m.asIdeal x)
  exact eq_of_monic_of_associated (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    (monic_prod_of_monic _ _ fun q hq ↦ (hs_monic_irred hq).1)
    (associated_of_dvd_dvd hdvd_prod hprod_dvd)

end Minpoly

section SpectralNorm

variable {F L : Type*} [NormedField F] [IsUltrametricDist F]
  [CommRing L] [Algebra F L] [Module.Finite F L] [IsReduced L]

private theorem spectralValue_prod_le_of_monic (s : Finset F[X]) {M : ℝ} (hM : 0 ≤ M)
    (hmon : ∀ q ∈ s, q.Monic) (hle : ∀ q ∈ s, spectralValue q ≤ M) :
    spectralValue (∏ q ∈ s, q) ≤ M := by
  have hcoeff {q : F[X]} (hq : q ∈ s) (i : ℕ) : ‖q.coeff i‖ ≤ M ^ (q.natDegree - i) :=
    ((hmon q hq).norm_coeff_le_spectralValue_pow i).trans
      (pow_le_pow_left₀ (spectralValue_nonneg _) (hle q hq) _)
  have hdeg : (∏ q ∈ s, q).natDegree = ∑ q ∈ s, q.natDegree :=
    natDegree_prod _ _ fun q hq ↦ (hmon q hq).ne_zero
  have hprod_coeff (k : ℕ) : ‖(∏ q ∈ s, q).coeff k‖ ≤ M ^ ((∏ q ∈ s, q).natDegree - k) := by
    rw [hdeg]
    exact Polynomial.apply_coeff_prod_le_pow (f := normRingSeminorm F) norm_one.le
      IsUltrametricDist.isNonarchimedean_norm s id (fun q hq i ↦ hcoeff hq i) k
  refine ciSup_le fun k ↦ ?_
  by_cases hk : k < (∏ q ∈ s, q).natDegree
  · rw [spectralValueTerms_of_lt_natDegree _ hk]
    have hsub : ((∏ q ∈ s, q).natDegree - k : ℝ) = (((∏ q ∈ s, q).natDegree - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk.le]
    rw [one_div, hsub, Real.rpow_inv_le_iff_of_pos (norm_nonneg _) hM
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hk)), Real.rpow_natCast]
    exact hprod_coeff k
  · rw [spectralValueTerms_of_natDegree_le _ (not_lt.mp hk)]
    exact hM

/-- In a module-finite reduced commutative algebra `L` over an ultrametric normed field `F`,
`spectralValue (minpoly F x)` equals the supremum over `m : MaximalSpectrum L` of the spectral norm
of the residue of `x` in `L ⧸ m.asIdeal`. -/
theorem spectralValue_minpoly_eq_iSup_maximalSpectrum (x : L) :
    spectralValue (minpoly F x) =
      ⨆ m : MaximalSpectrum L,
        (letI := Ideal.Quotient.field m.asIdeal
         spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x)) := by
  have : IsArtinianRing L := .of_finite F L
  set f : MaximalSpectrum L → ℝ := fun m ↦
    letI := Ideal.Quotient.field m.asIdeal
    spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x)
  set M := ⨆ m : MaximalSpectrum L, f m
  have hM_nonneg : 0 ≤ M := Real.iSup_nonneg fun m ↦ by
    let := Ideal.Quotient.field m.asIdeal
    exact spectralNorm_nonneg _
  refine le_antisymm ?_ (Real.iSup_le (fun m ↦ ?_) (spectralValue_nonneg _))
  · set s := (Set.finite_range fun m : MaximalSpectrum L ↦
      minpoly F (Ideal.Quotient.mk m.asIdeal x)).toFinset
    rw [minpoly_eq_prod_minimalPolynomials_maximalSpectrum x]
    refine spectralValue_prod_le_of_monic s hM_nonneg (fun q hq ↦ ?_) (fun q hq ↦ ?_)
    · simp only [Set.Finite.mem_toFinset, Set.mem_range, s] at hq
      obtain ⟨m, rfl⟩ := hq
      have : Module.Finite F (L ⧸ m.asIdeal) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
          Ideal.Quotient.mk_surjective
      exact minpoly.monic (Algebra.IsIntegral.isIntegral _)
    · simp only [Set.Finite.mem_toFinset, Set.mem_range, s] at hq
      obtain ⟨m, rfl⟩ := hq
      exact le_ciSup (Set.finite_range f).bddAbove m
  · let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have haeval : aeval (Ideal.Quotient.mk m.asIdeal x) (minpoly F x) = 0 := by
      rw [← Ideal.Quotient.mkₐ_eq_mk F m.asIdeal, aeval_algHom_apply, minpoly.aeval, map_zero]
    exact norm_root_le_spectralValue (f := spectralAlgNorm F (L ⧸ m.asIdeal))
      isPowMul_spectralNorm isNonarchimedean_spectralNorm
      (minpoly.monic (Algebra.IsIntegral.isIntegral x)) haeval

private theorem spectralValue_minpoly_le_iff (x : L) {c : ℝ} (hc : 0 ≤ c) :
    spectralValue (minpoly F x) ≤ c ↔
      ∀ m : MaximalSpectrum L,
        (letI := Ideal.Quotient.field m.asIdeal
         spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x)) ≤ c := by
  have : IsArtinianRing L := .of_finite F L
  rw [spectralValue_minpoly_eq_iSup_maximalSpectrum]
  exact ⟨fun h m ↦ (le_ciSup (Set.finite_range _).bddAbove m).trans h, fun h ↦ Real.iSup_le h hc⟩

variable (F L) in
/-- On a module-finite reduced commutative algebra `L` over an ultrametric normed field `F`,
`x ↦ spectralValue (minpoly F x)` is an `F`-algebra norm. -/
noncomputable def reducedSpectralAlgNorm : AlgebraNorm F L where
  toFun x := spectralValue (minpoly F x)
  map_zero' := by
    simp [spectralValue_minpoly_eq_iSup_maximalSpectrum, spectralNorm_zero]
  add_le' x y := by
    have : IsArtinianRing L := .of_finite F L
    refine ((spectralValue_minpoly_le_iff (x + y)
      (le_max_of_le_left (spectralValue_nonneg _))).mpr fun m ↦ ?_).trans
        (max_le_add_of_nonneg (spectralValue_nonneg _) (spectralValue_nonneg _))
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    rw [map_add]
    exact (isNonarchimedean_spectralNorm _ _).trans (max_le_max
      ((spectralValue_minpoly_le_iff x (spectralValue_nonneg _)).mp le_rfl m)
      ((spectralValue_minpoly_le_iff y (spectralValue_nonneg _)).mp le_rfl m))
  neg' x := by
    simp only [spectralValue_minpoly_eq_iSup_maximalSpectrum, map_neg]
    congr 1; ext m
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)
  mul_le' x y := by
    refine (spectralValue_minpoly_le_iff (x * y)
      (mul_nonneg (spectralValue_nonneg _) (spectralValue_nonneg _))).mpr fun m ↦ ?_
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    rw [map_mul]
    exact (spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic _)
      (Algebra.IsAlgebraic.isAlgebraic _)).trans (mul_le_mul
        ((spectralValue_minpoly_le_iff x (spectralValue_nonneg _)).mp le_rfl m)
        ((spectralValue_minpoly_le_iff y (spectralValue_nonneg _)).mp le_rfl m)
        (spectralNorm_nonneg _) (spectralValue_nonneg _))
  smul' c x := by
    rw [spectralValue_minpoly_eq_iSup_maximalSpectrum,
      spectralValue_minpoly_eq_iSup_maximalSpectrum, Real.mul_iSup_of_nonneg (norm_nonneg c)]
    congr 1; ext m
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hmk : Ideal.Quotient.mk m.asIdeal (c • x) = c • Ideal.Quotient.mk m.asIdeal x := by
      rw [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
    rw [hmk, spectralNorm_smul c (Algebra.IsAlgebraic.isAlgebraic _), coe_nnNorm]
  eq_zero_of_map_eq_zero' x hx := by
    have : IsArtinianRing L := .of_finite F L
    apply (IsArtinianRing.equivPi L).injective
    rw [map_zero]
    ext m
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hm : spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) = 0 :=
      le_antisymm ((spectralValue_minpoly_le_iff x le_rfl).mp hx.le m) (spectralNorm_nonneg _)
    exact eq_zero_of_map_spectralNorm_eq_zero hm (Algebra.IsAlgebraic.isAlgebraic _)

theorem reducedSpectralAlgNorm_apply (x : L) :
    reducedSpectralAlgNorm F L x = spectralValue (minpoly F x) :=
  (rfl)

theorem reducedSpectralAlgNorm_eq_iSup_maximalSpectrum (x : L) :
    reducedSpectralAlgNorm F L x =
      ⨆ m : MaximalSpectrum L,
        (letI := Ideal.Quotient.field m.asIdeal
         spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x)) :=
  spectralValue_minpoly_eq_iSup_maximalSpectrum x

theorem isNonarchimedean_reducedSpectralAlgNorm :
    IsNonarchimedean (reducedSpectralAlgNorm F L) := by
  intro x y
  refine (spectralValue_minpoly_le_iff (x + y)
    (le_max_of_le_left (apply_nonneg (reducedSpectralAlgNorm F L) x))).mpr fun m ↦ ?_
  let := Ideal.Quotient.field m.asIdeal
  have : Module.Finite F (L ⧸ m.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  rw [map_add]
  exact (isNonarchimedean_spectralNorm _ _).trans (max_le_max
    ((spectralValue_minpoly_le_iff x (spectralValue_nonneg _)).mp le_rfl m)
    ((spectralValue_minpoly_le_iff y (spectralValue_nonneg _)).mp le_rfl m))

theorem isPowMul_reducedSpectralAlgNorm : IsPowMul (reducedSpectralAlgNorm F L) := by
  have : IsArtinianRing L := .of_finite F L
  intro x n hn
  refine le_antisymm ?_ ?_
  · refine (spectralValue_minpoly_le_iff (x ^ n)
      (pow_nonneg (apply_nonneg (reducedSpectralAlgNorm F L) x) n)).mpr fun m ↦ ?_
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    rw [map_pow, isPowMul_spectralNorm _ hn]
    exact pow_le_pow_left₀ (spectralNorm_nonneg _)
      ((spectralValue_minpoly_le_iff x (spectralValue_nonneg _)).mp le_rfl m) n
  · rcases isEmpty_or_nonempty (MaximalSpectrum L) with hE | hNE
    · rw [reducedSpectralAlgNorm_eq_iSup_maximalSpectrum,
        reducedSpectralAlgNorm_eq_iSup_maximalSpectrum]
      simp [zero_pow (Nat.ne_of_gt hn)]
    · obtain ⟨m, hm⟩ := exists_eq_ciSup_of_finite
        (f := fun m : MaximalSpectrum L ↦
          letI := Ideal.Quotient.field m.asIdeal
          spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x))
      rw [reducedSpectralAlgNorm_eq_iSup_maximalSpectrum, ← hm]
      let := Ideal.Quotient.field m.asIdeal
      have : Module.Finite F (L ⧸ m.asIdeal) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
          Ideal.Quotient.mk_surjective
      rw [← isPowMul_spectralNorm _ hn, ← map_pow]
      exact (spectralValue_minpoly_le_iff (x ^ n) (spectralValue_nonneg _)).mp le_rfl m

theorem reducedSpectralAlgNorm_one_le : reducedSpectralAlgNorm F L 1 ≤ 1 :=
  (spectralValue_minpoly_le_iff 1 zero_le_one).mpr fun m ↦ by
    let := Ideal.Quotient.field m.asIdeal
    rw [map_one, spectralNorm_one]

@[simp]
theorem reducedSpectralAlgNorm_one [Nontrivial L] : reducedSpectralAlgNorm F L 1 = 1 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal L
  refine le_antisymm reducedSpectralAlgNorm_one_le ?_
  let m' : MaximalSpectrum L := ⟨m, hm⟩
  let := Ideal.Quotient.field m'.asIdeal
  have h1 : spectralNorm F (L ⧸ m'.asIdeal) (Ideal.Quotient.mk m'.asIdeal 1) = 1 := by
    rw [map_one, spectralNorm_one]
  exact h1 ▸ (spectralValue_minpoly_le_iff 1 (spectralValue_nonneg _)).mp le_rfl m'

@[simp]
theorem reducedSpectralAlgNorm_algebraMap [Nontrivial L] (c : F) :
    reducedSpectralAlgNorm F L (algebraMap F L c) = ‖c‖ :=
  (reducedSpectralAlgNorm F L).extends_norm reducedSpectralAlgNorm_one c

end SpectralNorm

end TauCeti

namespace AlgHom

/-- An injective `F`-algebra homomorphism between module-finite reduced `F`-algebras preserves
`TauCeti.reducedSpectralAlgNorm`. -/
theorem reducedSpectralAlgNorm_map {F L L' : Type*} [NormedField F] [IsUltrametricDist F]
    [CommRing L] [Algebra F L] [Module.Finite F L] [IsReduced L]
    [CommRing L'] [Algebra F L'] [Module.Finite F L'] [IsReduced L']
    (ψ : L →ₐ[F] L') (hψ : Function.Injective ψ) (x : L) :
    TauCeti.reducedSpectralAlgNorm F L' (ψ x) = TauCeti.reducedSpectralAlgNorm F L x := by
  rw [TauCeti.reducedSpectralAlgNorm_apply, TauCeti.reducedSpectralAlgNorm_apply,
    minpoly.algHom_eq ψ hψ]

end AlgHom

namespace AlgEquiv

/-- An `F`-algebra equivalence between module-finite reduced `F`-algebras preserves
`TauCeti.reducedSpectralAlgNorm`. -/
@[simp]
theorem reducedSpectralAlgNorm_map {F L L' : Type*} [NormedField F] [IsUltrametricDist F]
    [CommRing L] [Algebra F L] [Module.Finite F L] [IsReduced L]
    [CommRing L'] [Algebra F L'] [Module.Finite F L'] [IsReduced L']
    (e : L ≃ₐ[F] L') (x : L) :
    TauCeti.reducedSpectralAlgNorm F L' (e x) = TauCeti.reducedSpectralAlgNorm F L x :=
  e.toAlgHom.reducedSpectralAlgNorm_map e.injective x

end AlgEquiv

namespace Module.Basis

/-- On a module-finite reduced algebra `L` over an ultrametric normed field `F`,
`TauCeti.reducedSpectralAlgNorm F L` is bounded above by a constant times the coordinate norm of
any finite nonempty `F`-basis of `L`. -/
theorem reducedSpectralAlgNorm_le_sum_mul_norm {F L ι : Type*} [NormedField F]
    [IsUltrametricDist F] [CommRing L] [Algebra F L] [Module.Finite F L] [IsReduced L]
    [Fintype ι] [Nonempty ι] (b : Module.Basis ι F L) (x : L) :
    TauCeti.reducedSpectralAlgNorm F L x ≤
      (∑ i, TauCeti.reducedSpectralAlgNorm F L (b i)) * b.norm x := by
  calc
    TauCeti.reducedSpectralAlgNorm F L x
        = TauCeti.reducedSpectralAlgNorm F L (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
    _ ≤ ∑ i, TauCeti.reducedSpectralAlgNorm F L (b.repr x i • b i) :=
      Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
    _ = ∑ i, ‖b.repr x i‖ * TauCeti.reducedSpectralAlgNorm F L (b i) := by
      simp only [map_smul_eq_mul]
    _ ≤ ∑ i, b.norm x * TauCeti.reducedSpectralAlgNorm F L (b i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (b.norm_repr_le_norm i)
        (apply_nonneg _ _)
    _ = (∑ i, TauCeti.reducedSpectralAlgNorm F L (b i)) * b.norm x := by
      rw [← Finset.mul_sum, mul_comm]

end Module.Basis

namespace TauCeti.IsWeaklyStable

universe u v

/-- Over a weakly stable ultrametric normed field `F`, every `F`-linear functional on a
module-finite reduced commutative `F`-algebra `L` (in any universe) is bounded with respect to
`TauCeti.reducedSpectralAlgNorm F L`. -/
theorem exists_bound_reducedSpectralAlgNorm {F : Type u} [NormedField F] [IsUltrametricDist F]
    (hF : IsWeaklyStable F) {L : Type v} [CommRing L] [Algebra F L] [Module.Finite F L]
    [IsReduced L] (φ : Module.Dual F L) :
    ∃ C : ℝ, ∀ x : L, ‖φ x‖ ≤ C * reducedSpectralAlgNorm F L x := by
  classical
  have : IsArtinianRing L := .of_finite F L
  have : Fintype (MaximalSpectrum L) := Fintype.ofFinite (MaximalSpectrum L)
  let e : L ≃ₗ[F] ∀ m : MaximalSpectrum L, L ⧸ m.asIdeal :=
    ((IsArtinianRing.equivPi L).restrictScalars F).toLinearEquiv
  have hsingle (m : MaximalSpectrum L) :
      ∃ C : ℝ, ∀ y : L ⧸ m.asIdeal,
        ‖φ (e.symm (LinearMap.single F (fun i : MaximalSpectrum L ↦ L ⧸ i.asIdeal) m y))‖ ≤
          C * (letI := Ideal.Quotient.field m.asIdeal; spectralNorm F (L ⧸ m.asIdeal) y) := by
    let := Ideal.Quotient.field m.asIdeal
    have : Module.Finite F (L ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact hF.exists_bound_spectralNorm
      (φ.comp (e.symm.toLinearMap.comp
        (LinearMap.single F (fun i : MaximalSpectrum L ↦ L ⧸ i.asIdeal) m)))
  choose C hC using hsingle
  refine ⟨∑ m : MaximalSpectrum L, |C m|, fun x ↦ ?_⟩
  have hx : x = ∑ m : MaximalSpectrum L,
      e.symm (LinearMap.single F (fun i : MaximalSpectrum L ↦ L ⧸ i.asIdeal) m
        (Ideal.Quotient.mk m.asIdeal x)) := by
    apply e.injective
    rw [map_sum]
    ext m
    simp [e]
  calc
    ‖φ x‖ = ‖∑ m : MaximalSpectrum L,
        φ (e.symm (LinearMap.single F (fun i : MaximalSpectrum L ↦ L ⧸ i.asIdeal) m
          (Ideal.Quotient.mk m.asIdeal x)))‖ := by
      rw [← map_sum, ← hx]
    _ ≤ ∑ m : MaximalSpectrum L,
        ‖φ (e.symm (LinearMap.single F (fun i : MaximalSpectrum L ↦ L ⧸ i.asIdeal) m
          (Ideal.Quotient.mk m.asIdeal x)))‖ := norm_sum_le _ _
    _ ≤ ∑ m : MaximalSpectrum L, |C m| * reducedSpectralAlgNorm F L x := by
      refine Finset.sum_le_sum fun m _ ↦ ?_
      let := Ideal.Quotient.field m.asIdeal
      have hm_le : spectralNorm F (L ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) ≤
          reducedSpectralAlgNorm F L x :=
        (spectralValue_minpoly_le_iff x (apply_nonneg _ _)).mp le_rfl m
      exact (hC m _).trans (mul_le_mul (le_abs_self (C m)) hm_le
        (spectralNorm_nonneg _) (abs_nonneg _))
    _ = (∑ m : MaximalSpectrum L, |C m|) * reducedSpectralAlgNorm F L x := by
      rw [← Finset.sum_mul]

/-- Over a weakly stable ultrametric normed field `F`, `TauCeti.reducedSpectralAlgNorm F L` on any
module-finite reduced commutative `F`-algebra `L` is equivalent to the coordinate norm of every
finite nonempty `F`-basis of `L`. -/
theorem exists_basis_norm_comparison_of_isReduced {F : Type u} [NormedField F] [IsUltrametricDist F]
    (hF : IsWeaklyStable F) {L : Type v} [CommRing L] [Algebra F L] [Module.Finite F L]
    [IsReduced L] {ι : Type*} [Fintype ι] [Nonempty ι] (b : Module.Basis ι F L) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x : L,
      b.norm x ≤ C * reducedSpectralAlgNorm F L x ∧
        reducedSpectralAlgNorm F L x ≤ D * b.norm x := by
  choose C hC using fun i ↦ hF.exists_bound_reducedSpectralAlgNorm (b.coord i)
  let C₀ := 1 + ∑ i, |C i|
  let D₀ := 1 + ∑ i, reducedSpectralAlgNorm F L (b i)
  have hDsum : 0 ≤ ∑ i, reducedSpectralAlgNorm F L (b i) :=
    Finset.sum_nonneg fun i _ ↦ apply_nonneg _ _
  refine ⟨C₀, D₀, by positivity, by positivity, fun x ↦ ⟨?_, ?_⟩⟩
  · apply Finset.sup'_le
    intro i _
    have hi : C i ≤ C₀ := by
      have := Finset.single_le_sum (f := fun i ↦ |C i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      dsimp [C₀]
      linarith [le_abs_self (C i)]
    exact (hC i x).trans (mul_le_mul_of_nonneg_right hi (apply_nonneg _ _))
  · exact (b.reducedSpectralAlgNorm_le_sum_mul_norm x).trans
      (mul_le_mul_of_nonneg_right (by dsimp [D₀]; linarith [hDsum]) (b.norm_nonneg x))

end TauCeti.IsWeaklyStable
