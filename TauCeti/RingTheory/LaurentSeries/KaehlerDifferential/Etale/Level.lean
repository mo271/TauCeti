/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.DifferentialTransition
public import TauCeti.RingTheory.LaurentSeries.Level.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.Level.Separable
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale.Trace

/-!
# Intrinsic continuous Kähler differentials of separable Laurent levels and level charts

Let `K` be a field and `d : ℕ+` with `((d : ℕ) : K) ≠ 0`. By
`TauCeti.LaurentSeries.Level.instFormallyEtale`, the ramified level `Level K d` (`t = u ^ d`) is
formally étale over `F = K⸨X⸩`, so it carries two constructions of continuous one-forms:

1. The intrinsic étale module `Extension.ContinuousKaehlerDifferential K (Level K d)` with its
   universal derivation `Extension.ContinuousKaehlerDifferential.D K (Level K d)`.
2. The explicit level module `Level.ContinuousKaehlerDifferential K d` of series `g(u) du` in the
   level parameter `u`.

This file identifies the two as topological `Level K d`-modules, relates them to level transitions
and Puiseux differentials, and transports this comparison along arbitrary level charts
`e : L ≃ₐ[K⸨X⸩] Level K d`:

* `TauCeti.LaurentSeries.Level.ringEquivLaurentSeries_derivation`: the étale derivation `d/dt` on
  `Level K d` acts in the coordinate `u` as `g(u) ↦ g'(u) / (d u ^ (d - 1))`.
* `TauCeti.LaurentSeries.Level.equivLevelDifferential`: the continuous `Level K d`-linear
  equivalence `Extension.ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
  Level.ContinuousKaehlerDifferential K d`, intertwining the scalar-extension equivalences
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, pullbacks from `F`, universal derivations `d`, differential
  traces, residues, and level transitions (`equivLevelDifferential_mapAlgHom_transition`).
* `TauCeti.LaurentSeries.Level.residue_mapAlgHom` and
  `TauCeti.LaurentSeries.Level.residue_eq_nsmul_puiseuxField_residue`: along embeddings of
  separable levels `Level K n →ₐ[F] Level K m` the intrinsic residue scales by `m / n`, and in
  characteristic zero `Res_{L_d}(ω) = Res_F(Tr_{L_d/F} ω)` equals `d` times the rational-exponent
  Puiseux residue `Res_t^ℚ(ω)`, compatibly with the Hahn/level transition inclusions.
* `AlgEquiv.laurentExtensionDifferentialEquiv` and
  `AlgEquiv.continuousLaurentExtensionDifferentialEquiv`: for any `e : L ≃ₐ[K⸨X⸩] Level K d`, the
  induced (continuous) `K⸨X⸩`-linear chart on `Ω¹_cont(L/K)`, proving that the `u⁻¹`-coefficient
  residue computed in any separable level chart equals the intrinsic residue
  `Extension.ContinuousKaehlerDifferential.residue K L ω` and is therefore independent of the
  chosen chart (`AlgEquiv.coeff_laurentExtensionDifferentialEquiv_eq`).
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

section LevelComparison

variable (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]

private theorem derivative_single_ne_zero' :
    _root_.LaurentSeries.derivative K (single (d : ℤ) (1 : K)) ≠ 0 := by
  simp [NeZero.ne ((d : ℕ) : K)]

variable {K d} in
/-- **Explicit formula for the étale derivation `d/dt` on `Level K d`.** Read in the level
parameter `u` (`u ^ d = t`), `Extension.derivation K (Level K d)` divides the formal `u`-derivative
by `d u ^ (d - 1)`. -/
theorem ringEquivLaurentSeries_derivation (x : Level K d) :
    ringEquivLaurentSeries K d (Extension.derivation K (Level K d) x) =
      _root_.LaurentSeries.derivative K (ringEquivLaurentSeries K d x) /
        _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
  have hexp (f : K⸨X⸩) :
      _root_.LaurentSeries.derivative K (_root_.LaurentSeries.expand K d f) =
        _root_.LaurentSeries.expand K d (_root_.LaurentSeries.derivative K f) *
          _root_.LaurentSeries.derivative K (single (d : ℤ) (1 : K)) := by
    have h1 := ContinuousKaehlerDifferential.ringEquivLaurentSeries_equivLevel
      (ContinuousKaehlerDifferential.map K d (TauCeti.ContinuousKaehlerDifferential.D K f))
    have h2 := congrArg (ringEquivLaurentSeries K d)
      (ContinuousKaehlerDifferential.equivLevel_map (d := d)
        (TauCeti.ContinuousKaehlerDifferential.D K f))
    simpa [algebraMap_apply] using h1.symm.trans h2
  let δ₀ : Derivation K (Level K d) (Level K d) :=
    { toFun y := (ringEquivLaurentSeries K d).symm
        (laurentSeriesDerivation K (ringEquivLaurentSeries K d y))
      map_add' y₁ y₂ := (ringEquivLaurentSeries K d).injective
        (by simp [-laurentSeriesDerivation_apply])
      map_smul' r y := (ringEquivLaurentSeries K d).injective (by simp)
      map_one_eq_zero' := (ringEquivLaurentSeries K d).injective
        (by simp [-laurentSeriesDerivation_apply])
      leibniz' a b := (ringEquivLaurentSeries K d).injective
        (by simp [-laurentSeriesDerivation_apply]) }
  have hδ₀ (y : Level K d) :
      ringEquivLaurentSeries K d (δ₀ y) =
        _root_.LaurentSeries.derivative K (ringEquivLaurentSeries K d y) :=
    ((ringEquivLaurentSeries K d).apply_symm_apply _).trans (laurentSeriesDerivation_apply K _)
  let c : Level K d :=
    (ringEquivLaurentSeries K d).symm (_root_.LaurentSeries.derivative K (single (d : ℤ) 1))
  have hc : ringEquivLaurentSeries K d c =
      _root_.LaurentSeries.derivative K (single (d : ℤ) 1) :=
    (ringEquivLaurentSeries K d).apply_symm_apply _
  have hδ : c⁻¹ • δ₀ = Extension.derivation K (Level K d) :=
    Extension.eq_derivation fun f ↦ (ringEquivLaurentSeries K d).injective <| by
      rw [smul_apply, smul_eq_mul, map_mul, map_inv₀, hc, hδ₀, algebraMap_apply,
        algebraMap_apply, hexp f, laurentSeriesDerivation_apply, mul_comm,
        mul_inv_cancel_right₀ (derivative_single_ne_zero' K d)]
  rw [← hδ, smul_apply, smul_eq_mul, map_mul, map_inv₀, hc, hδ₀, div_eq_inv_mul]

variable {K d} in
/-- On the level parameter `u`, `d/dt (u) = (d u ^ (d - 1))⁻¹`. -/
@[simp]
theorem derivation_parameter :
    Extension.derivation K (Level K d) (parameter K d) =
      ((ringEquivLaurentSeries K d).symm
        (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)))⁻¹ := by
  apply (ringEquivLaurentSeries K d).injective
  simp [ringEquivLaurentSeries_derivation]

/-- **Comparison between intrinsic étale differentials and explicit level differentials.** For `d`
nonzero in `K`, the scalar-extension equivalences `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` induce a
continuous `Level K d`-linear equivalence between
`Extension.ContinuousKaehlerDifferential K (Level K d)` and
`Level.ContinuousKaehlerDifferential K d`. -/
noncomputable def equivLevelDifferential :
    Extension.ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  ((Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).symm.trans
    (Level.ContinuousKaehlerDifferential.tensorEquiv K d)).toContinuousLinearEquivOfIsModuleTopology

variable {K d}

@[simp]
theorem equivLevelDifferential_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    equivLevelDifferential K d
        (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d) η) =
      Level.ContinuousKaehlerDifferential.tensorEquiv K d η := by
  simp [equivLevelDifferential]

@[simp]
theorem equivLevelDifferential_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivLevelDifferential K d (Extension.ContinuousKaehlerDifferential.map K (Level K d) ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  simpa using equivLevelDifferential_tensorEquiv (K := K) (d := d) (1 ⊗ₜ ω)

/-- In coordinates, `equivLevelDifferential` converts the `dt`-coordinate `equivSelf` to the
`du`-coordinate `equivLevel` by multiplying by `d u ^ (d - 1)`. -/
@[simp]
theorem equivLevel_equivLevelDifferential
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    ContinuousKaehlerDifferential.equivLevel K d (equivLevelDifferential K d ω) =
      Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d) ω *
        (ringEquivLaurentSeries K d).symm
          (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)) := by
  conv_lhs =>
    rw [← Extension.ContinuousKaehlerDifferential.equivSelf_smul_D_algebraMap_single_one ω,
      ← Extension.ContinuousKaehlerDifferential.map_D]
  rw [ContinuousLinearEquiv.map_smul, equivLevelDifferential_map, LinearEquiv.map_smul,
    ContinuousKaehlerDifferential.equivLevel_map,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D_single_one, map_one, one_mul,
    smul_eq_mul]

/-- **Compatibility with the universal derivation `d`.** Under `equivLevelDifferential`, the
intrinsic differential `D K (Level K d) x` of `x ∈ Level K d` is the formal `u`-differential
`d(x(u))`. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_equivLevelDifferential_D (x : Level K d) :
    ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K d
        (equivLevelDifferential K d
          (Extension.ContinuousKaehlerDifferential.D K (Level K d) x)) =
      TauCeti.ContinuousKaehlerDifferential.D K (ringEquivLaurentSeries K d x) := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [← ContinuousKaehlerDifferential.ringEquivLaurentSeries_equivLevel,
    equivLevel_equivLevelDifferential, Extension.ContinuousKaehlerDifferential.equivSelf_D,
    map_mul, RingEquiv.apply_symm_apply, ringEquivLaurentSeries_derivation,
    div_mul_cancel₀ _ (derivative_single_ne_zero' K d),
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D]

/-- The `du`-coordinate of `D K (Level K d) (parameter K d)` is `1`. -/
theorem equivLevel_equivLevelDifferential_D_parameter :
    ContinuousKaehlerDifferential.equivLevel K d
        (equivLevelDifferential K d
          (Extension.ContinuousKaehlerDifferential.D K (Level K d) (parameter K d))) = 1 := by
  apply (ringEquivLaurentSeries K d).injective
  simp [NeZero.ne ((d : ℕ) : K)]

/-- **Compatibility of differential traces.** `equivLevelDifferential` intertwines the intrinsic
étale differential trace with the explicit level trace. -/
@[simp]
theorem trace_equivLevelDifferential
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    ContinuousKaehlerDifferential.trace K d (equivLevelDifferential K d ω) =
      Extension.ContinuousKaehlerDifferential.trace K (Level K d) ω := by
  rw [← (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).apply_symm_apply ω]
  induction (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).symm ω
      using TensorProduct.inductionOn with
  | tmul x η => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **Compatibility of residues.** The `u⁻¹`-coefficient of a continuous one-form on `Level K d`
equals its intrinsic étale residue. -/
theorem coeff_neg_one_equivLevel_equivLevelDifferential
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    (ringEquivLaurentSeries K d
      (ContinuousKaehlerDifferential.equivLevel K d (equivLevelDifferential K d ω))).coeff (-1) =
      Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω := by
  rw [← ContinuousKaehlerDifferential.coeff_neg_one_equivLaurentSeries_trace,
    trace_equivLevelDifferential, Extension.ContinuousKaehlerDifferential.residue_apply]

/-- On `dt`-coordinates, `Level.residue K d` agrees with the intrinsic étale residue. -/
@[simp]
theorem level_residue_equivSelf
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Level.residue K d (Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d) ω) =
      Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω := by
  rw [← coeff_neg_one_equivLevel_equivLevelDifferential, equivLevel_equivLevelDifferential,
    map_mul, RingEquiv.apply_symm_apply, Level.residue_apply]

end LevelComparison

section TransitionAndPuiseux

variable {K : Type*} [Field K]

/-- **Compatibility with level transitions.** For `n ∣ m` with both `n` and `m` nonzero in `K`,
`equivLevelDifferential` intertwines `Extension.ContinuousKaehlerDifferential.mapAlgHom` along
`Level.transition K h` with `Level.ContinuousKaehlerDifferential.transition K h`. -/
theorem equivLevelDifferential_mapAlgHom_transition {n m : ℕ+}
    [NeZero ((n : ℕ) : K)] [NeZero ((m : ℕ) : K)] (h : n ∣ m)
    (ω : Extension.ContinuousKaehlerDifferential K (Level K n)) :
    equivLevelDifferential K m
        (Extension.ContinuousKaehlerDifferential.mapAlgHom (transition K h) ω) =
      ContinuousKaehlerDifferential.transition K h (equivLevelDifferential K n ω) := by
  conv_lhs =>
    rw [← Extension.ContinuousKaehlerDifferential.equivSelf_smul_D_algebraMap_single_one ω]
  conv_rhs =>
    rw [← Extension.ContinuousKaehlerDifferential.equivSelf_smul_D_algebraMap_single_one ω]
  rw [← Extension.ContinuousKaehlerDifferential.map_D, map_smulₛₗ,
    Extension.ContinuousKaehlerDifferential.mapAlgHom_map, ContinuousLinearEquiv.map_smul,
    ContinuousLinearEquiv.map_smul, equivLevelDifferential_map, equivLevelDifferential_map,
    map_smulₛₗ, ContinuousKaehlerDifferential.transition_map, RingHom.coe_coe]

/-- **Residues along embeddings of separable levels.** Any `K⸨X⸩`-algebra map
`φ : Level K n →ₐ[K⸨X⸩] Level K m` between separable levels multiplies the intrinsic residue of a
continuous differential by `m / n`; in particular `Res_{u_m} = (m / n) Res_{u_n}` along
`Level.transition K h` for `h : n ∣ m`. -/
@[simp]
theorem residue_mapAlgHom {n m : ℕ+} [NeZero ((n : ℕ) : K)] [NeZero ((m : ℕ) : K)]
    (φ : Level K n →ₐ[K⸨X⸩] Level K m)
    (ω : Extension.ContinuousKaehlerDifferential K (Level K n)) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K m)
        (Extension.ContinuousKaehlerDifferential.mapAlgHom φ ω) =
      ((m : ℕ) / n) • Extension.ContinuousKaehlerDifferential.residue K (Level K n) ω := by
  rw [← level_residue_equivSelf, ← level_residue_equivSelf,
    Extension.ContinuousKaehlerDifferential.equivSelf_mapAlgHom, residue_algHom_apply]

section CharZero

variable [CharZero K]

/-- In characteristic zero, embedding an intrinsic continuous one-form `ω` of `Level K d` into
`Ω¹_cont(puiseuxField K / K)` sends `x dt` to `(toPuiseux K d x) dt`. -/
theorem equivPuiseuxField_levelMap_equivLevelDifferential (d : ℕ+)
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField K
        (puiseuxField.ContinuousKaehlerDifferential.levelMap K d
          (ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K d
            (equivLevelDifferential K d ω))) =
      toPuiseux K d (Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d) ω) := by
  have hdt :
      puiseuxField.levelEmbedding K d (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)) *
        puiseuxField.derivation K (puiseuxField.levelEmbedding K d (single 1 1)) = 1 := by
    have h := puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField_levelMap d
      (TauCeti.ContinuousKaehlerDifferential.D K (single (d : ℤ) (1 : K)))
    rw [puiseuxField.ContinuousKaehlerDifferential.levelMap_D,
      puiseuxField.levelEmbedding_single_self,
      puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField_D,
      puiseuxField.derivation_single_one,
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D] at h
    exact h.symm
  rw [puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField_levelMap,
    ← ContinuousKaehlerDifferential.ringEquivLaurentSeries_equivLevel,
    equivLevel_equivLevelDifferential, map_mul, RingEquiv.apply_symm_apply, map_mul, mul_assoc,
    hdt, mul_one, ← toPuiseux_apply]

/-- In characteristic zero, the embeddings of intrinsic level one-forms into Puiseux one-forms
commute with the Hahn/level transition maps. -/
theorem levelMap_equivLevelDifferential_mapAlgHom_transition {n m : ℕ+} (h : n ∣ m)
    (ω : Extension.ContinuousKaehlerDifferential K (Level K n)) :
    puiseuxField.ContinuousKaehlerDifferential.levelMap K m
        (ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K m
          (equivLevelDifferential K m
            (Extension.ContinuousKaehlerDifferential.mapAlgHom (transition K h) ω))) =
      puiseuxField.ContinuousKaehlerDifferential.levelMap K n
        (ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K n
          (equivLevelDifferential K n ω)) := by
  rw [equivLevelDifferential_mapAlgHom_transition,
    ContinuousKaehlerDifferential.levelMap_transition]

/-- **Comparison with the rational-exponent Puiseux residue `Res_t^ℚ`.** In characteristic zero,
the intrinsic residue `Res_{L_d}(ω) = Res_F(Tr_{L_d/F} ω)` on level `d` is `d` times the Puiseux
residue of `ω` embedded into `Ω¹_cont(puiseuxField K / K)`. -/
theorem residue_eq_nsmul_puiseuxField_residue (d : ℕ+)
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω =
      (d : ℕ) • puiseuxField.residue K
        (puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField K
          (puiseuxField.ContinuousKaehlerDifferential.levelMap K d
            (ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K d
              (equivLevelDifferential K d ω)))) := by
  rw [equivPuiseuxField_levelMap_equivLevelDifferential, ← residue_eq_nsmul_residue_toPuiseux,
    level_residue_equivSelf]

end CharZero

end TransitionAndPuiseux

end TauCeti.LaurentSeries.Level

namespace AlgEquiv

open TauCeti.LaurentSeries
open TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

variable {K : Type*} [Field K]
  {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- **Level chart on intrinsic continuous differentials.** A `K⸨X⸩`-algebra isomorphism
`e : L ≃ₐ[K⸨X⸩] Level K d` with a separable ramified level identifies `Ω¹_cont(L/K)` with the
explicit continuous one-forms of `Level K d`. -/
noncomputable def laurentExtensionDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  (congrAlgEquiv (K := K) e).trans
    ((Level.equivLevelDifferential K d).toLinearEquiv.restrictScalars K⸨X⸩)

/-- Continuous upgrade of `AlgEquiv.laurentExtensionDifferentialEquiv` when `L` carries the
`K⸨X⸩`-module topology. -/
noncomputable def continuousLaurentExtensionDifferentialEquiv
    [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃L[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  e.laurentExtensionDifferentialEquiv.toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem coe_continuousLaurentExtensionDifferentialEquiv
    [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] (e : L ≃ₐ[K⸨X⸩] Level K d) :
    ⇑(e.continuousLaurentExtensionDifferentialEquiv (K := K)) =
      e.laurentExtensionDifferentialEquiv := by
  simp [continuousLaurentExtensionDifferentialEquiv]

theorem laurentExtensionDifferentialEquiv_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentExtensionDifferentialEquiv ω =
      Level.equivLevelDifferential K d (congrAlgEquiv (K := K) e ω) :=
  (rfl)

theorem laurentExtensionDifferentialEquiv_smul (e : L ≃ₐ[K⸨X⸩] Level K d)
    (x : L) (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentExtensionDifferentialEquiv (x • ω) =
      e x • e.laurentExtensionDifferentialEquiv ω := by
  simp [laurentExtensionDifferentialEquiv_apply, congrAlgEquiv_smul]

@[simp]
theorem laurentExtensionDifferentialEquiv_map (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentExtensionDifferentialEquiv (map K L ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  simp [laurentExtensionDifferentialEquiv_apply]

@[simp]
theorem addEquiv_laurentExtensionDifferentialEquiv_D (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    Level.ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K d
        (e.laurentExtensionDifferentialEquiv (D K L x)) =
      TauCeti.ContinuousKaehlerDifferential.D K
        (Level.ringEquivLaurentSeries K d (e x)) := by
  simp [laurentExtensionDifferentialEquiv_apply]

/-- Compatibility with `AlgEquiv.laurentDifferentialTensorEquiv` on field extensions. -/
theorem laurentExtensionDifferentialEquiv_tensorEquiv
    {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L] (e : L ≃ₐ[K⸨X⸩] Level K d)
    (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentExtensionDifferentialEquiv (tensorEquiv K L η) =
      e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    simp [laurentExtensionDifferentialEquiv_smul]
  | add η₁ η₂ h₁ h₂ => simp [h₁, h₂]

/-- **Differential trace commutes with every separable level chart.** -/
@[simp]
theorem trace_laurentExtensionDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Level.ContinuousKaehlerDifferential.trace K d (e.laurentExtensionDifferentialEquiv ω) =
      trace K L ω := by
  simp [laurentExtensionDifferentialEquiv_apply]

/-- **Residue in any separable level chart.** The intrinsic `K`-linear residue on `Ω¹_cont(L/K)`
agrees with the `u⁻¹`-coefficient residue in the level parameter of any chart
`e : L ≃ₐ[K⸨X⸩] Level K d`. -/
theorem residue_eq_coeff_laurentExtensionDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    residue K L ω =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentExtensionDifferentialEquiv ω))).coeff (-1) := by
  rw [laurentExtensionDifferentialEquiv_apply,
    Level.coeff_neg_one_equivLevel_equivLevelDifferential, residue_congrAlgEquiv]

/-- In `dt`-coordinates, the intrinsic residue equals `Level.residue K d` evaluated at
`e (equivSelf K L ω)`. -/
theorem residue_eq_level_residue (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    residue K L ω = Level.residue K d (e (equivSelf K L ω)) := by
  rw [← residue_congrAlgEquiv (K := K) e ω, ← Level.level_residue_equivSelf,
    equivSelf_congrAlgEquiv]

/-- **Independence of the chosen `K⸨X⸩`-algebra equivalence with `K⸨u⸩`.** Any two level charts
`e : L ≃ₐ[K⸨X⸩] Level K d` and `e' : L ≃ₐ[K⸨X⸩] Level K n` compute the same coefficient residue on
every continuous differential `ω ∈ Ω¹_cont(L/K)`. -/
theorem coeff_laurentExtensionDifferentialEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] Level K d) (e' : L ≃ₐ[K⸨X⸩] Level K n)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    (Level.ringEquivLaurentSeries K d
      (Level.ContinuousKaehlerDifferential.equivLevel K d
        (e.laurentExtensionDifferentialEquiv ω))).coeff (-1) =
    (Level.ringEquivLaurentSeries K n
      (Level.ContinuousKaehlerDifferential.equivLevel K n
        (e'.laurentExtensionDifferentialEquiv ω))).coeff (-1) := by
  rw [← residue_eq_coeff_laurentExtensionDifferentialEquiv e,
    ← residue_eq_coeff_laurentExtensionDifferentialEquiv e']

end AlgEquiv
