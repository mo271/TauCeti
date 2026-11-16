/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.Algebra.CharP.Frobenius.Basic
import TauCeti.Algebra.CharP.Frobenius.Flat
import TauCeti.RingTheory.AdicCompletion.Flat.Frobenius
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.KrullDimension.PowerSeries
import TauCeti.RingTheory.LocalRing.CoefficientField
import TauCeti.RingTheory.Perfect.IsPRadical
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Descent
import TauCeti.RingTheory.RegularLocalRing.Frobenius
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Kunz's theorem: flatness of Frobenius characterizes regular rings

Let `R` be a Noetherian ring of prime characteristic `p` (or exponential characteristic `p > 1`).
Kunz's theorem states that `R` is regular if and only if its Frobenius endomorphism `x ↦ x ^ p` is
flat (`TauCeti.IsRegularRing.flat_frobenius_iff`). The implication from regularity to flatness is
`TauCeti.IsRegularRing.flat_frobenius`; this file proves the converse
(`TauCeti.IsRegularRing.of_flat_frobenius`), following the perfection argument of Bhatt and Scholze
(Corollary 11.35).

By localization at prime ideals and completion at the maximal ideal
(`TauCeti.AdicCompletion.flat_frobenius` and `TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom`),
the converse reduces to a complete Noetherian local ring `(R, 𝔪)` of prime characteristic `p` with
residue field `k` and embedding dimension `e = spanFinrank 𝔪`. By Cohen's structure theorem
(`TauCeti.exists_surjective_mvPowerSeries_spanFinrank`), `R` is a quotient of the regular power
series ring `K = k⟦X₁, …, X_e⟧` of Krull dimension `e`. Passing to colimit perfections yields a
surjection `K_perf →+* R_perf` (`PerfectRing.lift_surjective_of_surjective`), so every
`R_perf`-module has projective dimension at most `e + 1`
(`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`). Since `R` has
flat Frobenius, `R → R_perf` is faithfully flat (`RingHom.FaithfullyFlat.of_isPerfectClosure`), and
faithfully flat descent (`ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`) shows that `R ⧸ 𝔪`
has projective dimension at most `e + 1` over `R`. Serre's theorem
(`TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`) concludes that `R` is regular.

## Main results

* `TauCeti.IsRegularLocalRing.of_flat_frobenius`: a Noetherian local ring of exponential
  characteristic `p > 1` whose Frobenius endomorphism is flat is regular.
* `TauCeti.IsRegularLocalRing.flat_frobenius_iff`: a Noetherian local ring of exponential
  characteristic `p > 1` is regular if and only if its Frobenius endomorphism is flat.
* `TauCeti.IsRegularRing.of_flat_frobenius`: **Converse of Kunz's theorem**, a Noetherian ring of
  exponential characteristic `p > 1` whose Frobenius endomorphism is flat is regular.
* `TauCeti.IsRegularRing.flat_frobenius_iff`: **Kunz's characterization**, a Noetherian ring of
  exponential characteristic `p > 1` is regular if and only if its Frobenius endomorphism is flat.

## References

* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Corollary 11.35.
* [Stacks Project, Lemma 51.17.6](https://stacks.math.columbia.edu/tag/0EC0).
-/

public section

open CategoryTheory IsLocalRing TensorProduct

universe u

namespace TauCeti

/-- Complete local case of the converse of Kunz's theorem: Cohen's presentation `k⟦X₁, …, X_e⟧ → R`
lifts to a surjection on perfections, bounding the projective dimension of `R ⧸ 𝔪` over `R_perf` and
hence over `R` by faithful flatness of `R → R_perf`. -/
private theorem isRegularLocalRing_of_flat_frobenius_of_isAdicComplete
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (hF : (frobenius R p).Flat) : IsRegularLocalRing R := by
  let : Algebra (ZMod p) R := (ZMod.castHom dvd_rfl R).toAlgebra
  obtain ⟨_, _, φ, hφ, _, _⟩ :=
    exists_surjective_mvPowerSeries_spanFinrank (ZMod p) R (maximalIdeal R).fg_of_isNoetherianRing
  let e := (maximalIdeal R).spanFinrank
  let K := MvPowerSeries (Fin e) (ResidueField R)
  have : CharP (ResidueField R) p := (CharP.charP_iff_prime_eq_zero hp.out).2 <| by
    rw [← map_natCast (residue R), CharP.cast_eq_zero, map_zero]
  have : CharP K p := charP_of_injective_ringHom MvPowerSeries.C_injective p
  have : IsReduced R := isReduced_of_flat_frobenius p hp.out.one_lt hF
  have hd : ringKrullDim K ≤ (e : ℕ) := by
    rw [MvPowerSeries.ringKrullDim_eq_natCard_of_field, Nat.card_fin]
  have hψ : Function.Surjective
      (PerfectRing.lift (PerfectClosure.of K p) ((PerfectClosure.of R p).comp φ) p) :=
    PerfectRing.lift_surjective_of_surjective (PerfectClosure.of K p) (PerfectClosure.of R p) p hφ
  let _ := (PerfectClosure.of R p).toAlgebra
  have hFF : Module.FaithfullyFlat R (PerfectClosure R p) := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    exact RingHom.FaithfullyFlat.of_isPerfectClosure (PerfectClosure.of R p) p hF
  let κ := Shrink.{u} (R ⧸ maximalIdeal R)
  have : Module.Finite R (R ⧸ maximalIdeal R) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  have : Module.Finite R κ := Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm
  have hpdPerf : HasProjectiveDimensionLE
      (ModuleCat.of (PerfectClosure R p) (PerfectClosure R p ⊗[R] κ)) (e + 1) :=
    IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
      (PerfectClosure.of K p) p hd hψ _
  have : HasProjectiveDimensionLE (ModuleCat.of R κ) (e + 1) :=
    ModuleCat.hasProjectiveDimensionLT_of_tensorProduct (PerfectClosure R p) κ hpdPerf
  exact IsRegularLocalRing.of_hasProjectiveDimensionLE (e + 1)

/-- **Converse of Kunz's theorem, local case.** A Noetherian local ring of exponential
characteristic `p > 1` whose Frobenius endomorphism is flat is a regular local ring. -/
theorem IsRegularLocalRing.of_flat_frobenius {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [ExpChar R p] (hp : 1 < p) (hF : (frobenius R p).Flat) :
    IsRegularLocalRing R := by
  obtain _ | ⟨hp'⟩ := ‹ExpChar R p›
  · exact absurd hp (lt_irrefl 1)
  have : Fact p.Prime := ⟨hp'⟩
  have hF' := AdicCompletion.flat_frobenius p hF
  obtain _ | ⟨_⟩ := (inferInstance : ExpChar (AdicCompletion (maximalIdeal R) R) p)
  · exact absurd hp (lt_irrefl 1)
  have : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    isRegularLocalRing_of_flat_frobenius_of_isAdicComplete p hF'
  exact IsRegularLocalRing.of_flat_of_isLocalHom (S := AdicCompletion (maximalIdeal R) R)

/-- **Kunz's characterization of regular local rings.** A Noetherian local ring of exponential
characteristic `p > 1` is regular if and only if its Frobenius endomorphism is flat. -/
theorem IsRegularLocalRing.flat_frobenius_iff {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [ExpChar R p] (hp : 1 < p) :
    (frobenius R p).Flat ↔ IsRegularLocalRing R :=
  ⟨of_flat_frobenius p hp, fun _ ↦ flat_frobenius p⟩

/-- **Converse of Kunz's theorem.** A Noetherian ring of exponential characteristic `p > 1` whose
Frobenius endomorphism is flat is regular. -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularRing.of_flat_frobenius {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [ExpChar R p] (hp : 1 < p) (hF : (frobenius R p).Flat) : IsRegularRing R := by
  obtain _ | ⟨hp'⟩ := ‹ExpChar R p›
  · exact absurd hp (lt_irrefl 1)
  refine isRegularRing_iff.mpr fun J hJ ↦ ?_
  have hQ : J = J.comap (frobenius R p) := by
    ext a
    exact (hJ.pow_mem_iff_mem p hp'.pos).symm
  have : CharP (Localization.AtPrime J) p := (CharP.charP_iff_prime_eq_zero hp').2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  have : ExpChar (Localization.AtPrime J) p := .prime hp'
  have hloc : frobenius (Localization.AtPrime J) p =
      Localization.localRingHom J J (frobenius R p) hQ :=
    IsLocalization.ringHom_ext J.primeCompl <| RingHom.ext fun a ↦ by
      simp [Localization.localRingHom_to_map, frobenius_def]
  refine IsRegularLocalRing.of_flat_frobenius p hp ?_
  rw [hloc]
  exact hF.localRingHom J J hQ

/-- **Kunz's characterization of regular rings.** A Noetherian ring of exponential characteristic
`p > 1` is regular if and only if its Frobenius endomorphism is flat. -/
@[stacks 0EC0]
theorem IsRegularRing.flat_frobenius_iff {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [ExpChar R p] (hp : 1 < p) : (frobenius R p).Flat ↔ IsRegularRing R :=
  ⟨of_flat_frobenius p hp, fun _ ↦ flat_frobenius p⟩

end TauCeti
