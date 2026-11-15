/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.Trace.Etale
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale.Topology
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.FiniteExtension

/-!
# Differential traces and residues on formally étale extensions of `K⸨X⸩`

Let `K` be a field and `F = K⸨X⸩`. For a formally étale `F`-algebra `L`, every continuous one-form
`ω ∈ Ω¹_cont(L/K)` has a canonical normal form `x dt` with `x = equivSelf K L ω`, equivalently
comes from `L ⊗_F Ω¹_cont(F/K) ≃ₗ[L] Ω¹_cont(L/K)`.

This file constructs the differential trace `Tr_{L/F} : Ω¹_cont(L/K) →ₗ[F] Ω¹_cont(F/K)`, the
relative differential trace `Tr_{M/L} : Ω¹_cont(M/K) →ₗ[F] Ω¹_cont(L/K)` in towers `F → L → M`,
and the intrinsic `K`-linear residue `Res_L : Ω¹_cont(L/K) →ₗ[K] K`, proving:

* **Projection and base-change formulas**: `Tr_{L/F}(x • map ω) = Tr_{L/F}(x) • ω`, compatibility
  with `TauCeti.ContinuousKaehlerDifferential.traceBaseChange` under `tensorEquiv K L`, and
  invariance under `F`-algebra equivalences `L ≃ₐ[F] M`.
* **Agreement with Kunz's algebraic differential trace**: when `L` is finite over `F`, the quotient
  map `Ω[L⁄K] → Ω¹_cont(L/K)` intertwines `(KaehlerDifferential.D K F).traceLin` with `Tr_{L/F}`;
  in particular `Tr_{L/F}(d x) = d(Tr_{L/F} x)`.
* **Towers and relative trace**: in a tower `F → L → M` of formally étale `F`-algebras, `Tr_{M/L}`
  acts as `y ⊗ ω ↦ Tr_{M/L}(y) • ω` across `M ⊗_L Ω¹_cont(L/K) ≃ₗ[M] Ω¹_cont(M/K)`, commutes with
  Kunz's trace and `d` when `M` is finite free over `L`, and satisfies
  `Tr_{L/F} ∘ Tr_{M/L} = Tr_{M/F}`.
* **Intrinsic residue**: `Res_L(ω)` is the `X⁻¹`-coefficient of `Tr_{L/F}(ω)`, vanishes on exact
  one-forms `d x` when `L/F` is finite, is invariant under `F`-algebra equivalences, and satisfies
  Tate's trace-residue formula `Res_L(Tr_{M/L} ω) = Res_M(ω)` in finite free étale towers.

## Main definitions

* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.trace`: the differential trace
  `Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(K⸨X⸩/K)`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.relativeTrace`: the relative
  differential trace `Ω¹_cont(M/K) →ₗ[K⸨X⸩] Ω¹_cont(L/K)` in a tower `K⸨X⸩ → L → M`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.residue`: the `K`-linear residue
  `Ω¹_cont(L/K) →ₗ[K] K`.

## Main results

* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.trace_mk`: compatibility with
  Kunz's algebraic differential trace `(KaehlerDifferential.D K K⸨X⸩).traceLin`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.trace_D`: `Tr(d x) = d(Tr x)`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.trace_relativeTrace`:
  transitivity `Tr_{L/K⸨X⸩}(Tr_{M/L} ω) = Tr_{M/K⸨X⸩}(ω)`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.residue_D`: exact forms have
  residue zero.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.residue_relativeTrace`:
  `Res_L(Tr_{M/L} ω) = Res_M(ω)`.

## References

* E. Kunz, *Kähler Differentials*, Vieweg, 1986, §16.
* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), 149–159.
-/

public section

open HahnSeries TensorProduct
open scoped KaehlerDifferential LaurentSeries

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

section Trace

variable (K : Type*) [Field K]
  (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]

/-- **Differential trace `Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(K⸨X⸩/K)`.** On normal forms it sends
`x dt` to `Tr_{L/K⸨X⸩}(x) dX`; as with `Algebra.trace`, it vanishes when `L` is infinite-dimensional
over `K⸨X⸩`. -/
noncomputable def trace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K :=
  (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).symm.toLinearMap ∘ₗ
    Algebra.trace K⸨X⸩ L ∘ₗ (equivSelf K L).toLinearMap.restrictScalars K⸨X⸩

variable {K L}

@[simp]
theorem equivLaurentSeries_trace (ω : ContinuousKaehlerDifferential K L) :
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω) =
      Algebra.trace K⸨X⸩ L (equivSelf K L ω) := by
  simp [trace]

theorem trace_equivSelf_symm (x : L) :
    trace K L ((equivSelf K L).symm x) =
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).symm
        (Algebra.trace K⸨X⸩ L x) := by
  simp [trace]

/-- **Projection formula for the differential trace.** -/
@[simp]
theorem trace_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (x • map K L ω) = Algebra.trace K⸨X⸩ L x • ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, map_smul, equivSelf_map, smul_eq_mul, mul_comm,
    ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- Compatibility with `TauCeti.ContinuousKaehlerDifferential.traceBaseChange` on field
extensions. -/
theorem trace_tensorEquiv {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Algebra K L]
    [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
    (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.traceBaseChange L η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω => simp
  | add η₁ η₂ h₁ h₂ => simp [h₁, h₂]

/-- Tracing a pulled-back form multiplies it by the degree `[L : K⸨X⸩]`. -/
theorem trace_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (map K L ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [← one_smul L (map K L ω), trace_smul_map, ← map_one (algebraMap K⸨X⸩ L),
    Algebra.trace_algebraMap, smul_assoc, one_smul]

/-- Differential trace is invariant under `K⸨X⸩`-algebra equivalences. -/
@[simp]
theorem trace_congrAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : L ≃ₐ[K⸨X⸩] M) (ω : ContinuousKaehlerDifferential K L) :
    trace K M (congrAlgEquiv (K := K) e ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivLaurentSeries_trace, equivSelf_congrAlgEquiv,
    Algebra.trace_eq_of_algEquiv]

/-- Differential trace is continuous when `L` carries the `K⸨X⸩`-module topology. -/
@[fun_prop]
theorem continuous_trace [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] :
    Continuous (trace K L) := by
  have : ContinuousAdd (TauCeti.ContinuousKaehlerDifferential K) :=
    IsModuleTopology.toContinuousAdd K⸨X⸩ _
  exact IsModuleTopology.continuous_of_linearMap (trace K L)

section Finite

variable [Module.Finite K⸨X⸩ L]

/-- **Compatibility with Kunz's algebraic differential trace.** When `L` is finite over `K⸨X⸩`,
the quotient map `Ω[L⁄K] → Ω¹_cont(L/K)` intertwines `(KaehlerDifferential.D K K⸨X⸩).traceLin`
with `trace K L`. -/
theorem trace_mk (ω : Ω[L⁄K]) :
    trace K L (mk K L ω) =
      TauCeti.ContinuousKaehlerDifferential.mk K ((KaehlerDifferential.D K K⸨X⸩).traceLin ω) := by
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K⸨X⸩ L).apply_symm_apply ω]
  induction (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K⸨X⸩ L).symm ω
      using TensorProduct.inductionOn with
  | tmul x η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, map_smul, ← map_mk, trace_smul_map,
      Derivation.traceLin_D_smul_map, map_smul]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- On algebraic Kähler differentials, Kunz's trace `(laurentSeriesDerivation K).traceLin` gives
the `dX`-coefficient of `trace K L (mk K L ω)`. -/
theorem laurentSeriesDerivation_traceLin (ω : Ω[L⁄K]) :
    (laurentSeriesDerivation K).traceLin ω =
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L (mk K L ω)) := by
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K⸨X⸩ L).apply_symm_apply ω]
  induction (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K⸨X⸩ L).symm ω
      using TensorProduct.inductionOn with
  | tmul x η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, Derivation.traceLin_smul_map, map_smul,
      ← map_mk, trace_smul_map, map_smul,
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_mk]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **Differential trace commutes with `d`.** -/
@[simp]
theorem trace_D (x : L) :
    trace K L (D K L x) =
      TauCeti.ContinuousKaehlerDifferential.D K (Algebra.trace K⸨X⸩ L x) := by
  rw [D_apply, trace_mk, Derivation.traceLin_D_eq, ← TauCeti.ContinuousKaehlerDifferential.D_apply]

end Finite

end Trace

section RelativeTrace

variable (K : Type*) [Field K]
  (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]
  (M : Type*) [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
  [Algebra.FormallyEtale K⸨X⸩ M] [Algebra L M] [IsScalarTower K⸨X⸩ L M]

/-- **Relative differential trace `Ω¹_cont(M/K) →ₗ[K⸨X⸩] Ω¹_cont(L/K)`** in a tower `K⸨X⸩ → L → M`
of formally étale `K⸨X⸩`-algebras. On normal forms it sends `y dt` to `Tr_{M/L}(y) dt`, and across
`M ⊗_L Ω¹_cont(L/K) ≃ₗ[M] Ω¹_cont(M/K)` it sends `y ⊗ ω` to `Tr_{M/L}(y) • ω`. -/
noncomputable def relativeTrace :
    ContinuousKaehlerDifferential K M →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ
    (Algebra.trace L M).restrictScalars K⸨X⸩ ∘ₗ
    (equivSelf K M).toLinearMap.restrictScalars K⸨X⸩

variable {K L M}

@[simp]
theorem equivSelf_relativeTrace (ω : ContinuousKaehlerDifferential K M) :
    equivSelf K L (relativeTrace K L M ω) = Algebra.trace L M (equivSelf K M ω) := by
  simp [relativeTrace, -equivSelf_symm_apply]

/-- `relativeTrace K L M` is `L`-linear with respect to `algebraMap L M`-scalar multiplication on
the source. -/
@[simp]
theorem relativeTrace_algebraMap_smul (a : L) (ω : ContinuousKaehlerDifferential K M) :
    relativeTrace K L M (algebraMap L M a • ω) = a • relativeTrace K L M ω := by
  apply (equivSelf K L).injective
  rw [equivSelf_relativeTrace, (equivSelf K M).map_smul, (equivSelf K L).map_smul,
    equivSelf_relativeTrace, smul_eq_mul, ← Algebra.smul_def, (Algebra.trace L M).map_smul,
    smul_eq_mul]

/-- **Projection formula for the relative differential trace.** -/
@[simp]
theorem relativeTrace_smul_mapTower (y : M) (ω : ContinuousKaehlerDifferential K L) :
    relativeTrace K L M (y • mapTower K L M ω) = Algebra.trace L M y • ω := by
  apply (equivSelf K L).injective
  rw [equivSelf_relativeTrace, (equivSelf K M).map_smul, mapTower_apply, equivSelf_mapAlgHom,
    IsScalarTower.toAlgHom_apply, (equivSelf K L).map_smul, smul_eq_mul, mul_comm,
    ← Algebra.smul_def, (Algebra.trace L M).map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- Relative differential trace is continuous when `L` and `M` carry the `K⸨X⸩`-module topology. -/
@[fun_prop]
theorem continuous_relativeTrace [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    [TopologicalSpace M] [IsModuleTopology K⸨X⸩ M] :
    Continuous (relativeTrace K L M) := by
  have : ContinuousAdd (ContinuousKaehlerDifferential K L) :=
    IsModuleTopology.toContinuousAdd K⸨X⸩ _
  exact IsModuleTopology.continuous_of_linearMap (relativeTrace K L M)

section FiniteFreeTower

variable [Module.Free L M] [Module.Finite L M]

/-- Compatibility of `relativeTrace K L M` with Kunz's algebraic differential trace
`(KaehlerDifferential.D K L).traceLin` when `M` is finite free over `L`. -/
theorem relativeTrace_mk [IsScalarTower K L M] (ω : Ω[M⁄K]) :
    relativeTrace K L M (mk K M ω) = mk K L ((KaehlerDifferential.D K L).traceLin ω) := by
  have : Algebra.FormallyEtale L M := .of_restrictScalars (R := K⸨X⸩)
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K L M).apply_symm_apply ω]
  induction (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K L M).symm ω
      using TensorProduct.inductionOn with
  | tmul y η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, map_smul, ← mapTower_mk,
      relativeTrace_smul_mapTower, Derivation.traceLin_D_smul_map, map_smul]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **Relative differential trace commutes with `d`.** -/
@[simp]
theorem relativeTrace_D [IsScalarTower K L M] (y : M) :
    relativeTrace K L M (D K M y) = D K L (Algebra.trace L M y) := by
  rw [D_apply, relativeTrace_mk, Derivation.traceLin_D_eq, ← D_apply]

/-- **Transitivity of differential trace in finite free étale towers.** -/
@[simp]
theorem trace_relativeTrace [Module.Finite K⸨X⸩ L]
    (ω : ContinuousKaehlerDifferential K M) :
    trace K L (relativeTrace K L M ω) = trace K M ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_relativeTrace, equivLaurentSeries_trace,
    Algebra.trace_trace]

end FiniteFreeTower

end RelativeTrace

section Residue

variable (K : Type*) [Field K]
  (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]

/-- **The intrinsic `K`-linear residue `Ω¹_cont(L/K) →ₗ[K] K`** on a formally étale `K⸨X⸩`-algebra:
the `X⁻¹`-coefficient of the differential trace `trace K L ω`. -/
noncomputable def residue : ContinuousKaehlerDifferential K L →ₗ[K] K :=
  HahnSeries.coeff.linearMap (-1 : ℤ) ∘ₗ
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearMap.restrictScalars K ∘ₗ
    (trace K L).restrictScalars K

variable {K L}

theorem residue_apply (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω =
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1) :=
  (rfl)

/-- The residue of `ω` is the `X⁻¹`-coefficient of `Tr_{L/K⸨X⸩}(equivSelf K L ω)`. -/
theorem residue_eq_coeff_trace_equivSelf (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = (Algebra.trace K⸨X⸩ L (equivSelf K L ω)).coeff (-1) := by
  rw [residue_apply, equivLaurentSeries_trace]

@[simp]
theorem residue_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (x • map K L ω) =
      (Algebra.trace K⸨X⸩ L x *
        TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  simp [residue_apply]

/-- Pulling back a one-form from `K⸨X⸩` multiplies its residue by `[L : K⸨X⸩]`. -/
theorem residue_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (map K L ω) =
      Module.finrank K⸨X⸩ L •
        (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  rw [residue_apply, trace_map, map_nsmul, HahnSeries.coeff_nsmul, Pi.smul_apply]

/-- Compatibility with `TauCeti.ContinuousKaehlerDifferential.residueBaseChange` on field
extensions. -/
theorem residue_tensorEquiv {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Algebra K L]
    [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
    (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.residueBaseChange L η := by
  rw [residue_apply, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.residueBaseChange_apply]

/-- **Invariance of the residue under `K⸨X⸩`-algebra equivalences.** -/
@[simp]
theorem residue_congrAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : L ≃ₐ[K⸨X⸩] M) (ω : ContinuousKaehlerDifferential K L) :
    residue K M (congrAlgEquiv (K := K) e ω) = residue K L ω := by
  rw [residue_apply, trace_congrAlgEquiv, ← residue_apply]

/-- **Exact continuous differentials have residue zero** on finite formally étale extensions of
`K⸨X⸩`. -/
@[simp]
theorem residue_D [Module.Finite K⸨X⸩ L] (x : L) :
    residue K L (D K L x) = 0 := by
  rw [residue_apply, trace_D, TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D,
    _root_.LaurentSeries.coeff_neg_one_derivative]

/-- **Tate's trace-residue formula `Res_L(Tr_{M/L} ω) = Res_M(ω)`.** In any tower `K⸨X⸩ → L → M`
of formally étale `K⸨X⸩`-algebras with `L` finite over `K⸨X⸩` and `M` finite free over `L`,
relative differential trace preserves residues. -/
@[simp]
theorem residue_relativeTrace {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [Algebra L M] [IsScalarTower K⸨X⸩ L M]
    [Module.Finite K⸨X⸩ L] [Module.Free L M] [Module.Finite L M]
    (ω : ContinuousKaehlerDifferential K M) :
    residue K L (relativeTrace K L M ω) = residue K M ω := by
  rw [residue_apply, trace_relativeTrace, ← residue_apply]

end Residue

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential
