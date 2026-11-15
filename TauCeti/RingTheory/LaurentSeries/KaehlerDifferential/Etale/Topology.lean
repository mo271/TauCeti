/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale.Map
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Topology and automatic continuity of derivations on étale Laurent extensions

Let `K` be a field, `F = K⸨X⸩` with the valuation topology, and `L` a formally étale `F`-algebra
carrying a topology. Transporting the topology of `L` across the rank-one coordinate
`equivSelf K L : Ω¹_cont(L/K) ≃ₗ[L] L` (`x dt ↦ x`) upgrades `equivSelf K L` to a continuous
`L`-linear equivalence `continuousEquivSelf K L : Ω¹_cont(L/K) ≃L[L] L`. Whenever `L` carries its
`F`-module topology, so does `Ω¹_cont(L/K)`; whenever `L` is a topological semiring, `Ω¹_cont(L/K)`
also carries the `L`-module topology. Every `L`-linear map out of `Ω¹_cont(L/K)` into a module with
continuous `L`-scalar multiplication is continuous.

When `L` is finite over `F` and carries the `F`-module topology:

* **Automatic continuity of `d/dt` and `d`:** Expanding elements of `L` in a finite `F`-basis and
  applying the Leibniz rule expresses `Extension.derivation K L` in terms of continuous `F`-linear
  coordinates and the continuous formal derivative of `F`, so `Extension.derivation K L` and the
  universal derivation `D K L : L → Ω¹_cont(L/K)` are automatically continuous.
* **Topological universal property:** For every Hausdorff module `M` with continuous `L`-scalar
  multiplication, a `K`-derivation `δ : L → M` is continuous on `L` if and only if its restriction
  to `F` is continuous, and if and only if it factors (uniquely) through `D K L` by a continuous
  `L`-linear map `Ω¹_cont(L/K) →L[L] M`.
-/

public section

open HahnSeries Topology
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

section InducedTopology

namespace ContinuousKaehlerDifferential

variable {K : Type*} [Field K]
  {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L] [TopologicalSpace L]

/-- Continuous one-forms of `L` carry the topology of their `dt`-coefficient in `L`. -/
noncomputable instance : TopologicalSpace (ContinuousKaehlerDifferential K L) :=
  .induced (equivSelf K L) inferInstance

/-- The coordinate `x dt ↦ x` induces the topology on `Ω¹_cont(L/K)`. -/
theorem isInducing_equivSelf : IsInducing (equivSelf K L) :=
  .induced _

variable (K L) in
/-- The `dt`-coordinate `Ω¹_cont(L/K) ≃L[L] L` as a continuous `L`-linear equivalence. -/
noncomputable def continuousEquivSelf : ContinuousKaehlerDifferential K L ≃L[L] L where
  toLinearEquiv := equivSelf K L
  continuous_toFun := isInducing_equivSelf.continuous
  continuous_invFun :=
    ((equivSelf K L).toEquiv.toHomeomorphOfIsInducing isInducing_equivSelf).symm.continuous

@[simp]
theorem continuousEquivSelf_apply (ω : ContinuousKaehlerDifferential K L) :
    continuousEquivSelf K L ω = equivSelf K L ω :=
  (rfl)

@[simp]
theorem continuousEquivSelf_symm_apply (x : L) :
    (continuousEquivSelf K L).symm x = (equivSelf K L).symm x :=
  (rfl)

@[simp]
theorem toLinearEquiv_continuousEquivSelf :
    (continuousEquivSelf K L).toLinearEquiv = equivSelf K L :=
  (rfl)

instance [T2Space L] : T2Space (ContinuousKaehlerDifferential K L) :=
  (continuousEquivSelf K L).toHomeomorph.isEmbedding.t2Space

instance [IsTopologicalAddGroup L] :
    IsTopologicalAddGroup (ContinuousKaehlerDifferential K L) :=
  isInducing_equivSelf.isTopologicalAddGroup (equivSelf K L).toAddMonoidHom

instance [IsTopologicalSemiring L] :
    IsModuleTopology L (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.iso (continuousEquivSelf K L).symm

variable (K L) in
/-- The `dt`-coordinate `Ω¹_cont(L/K) ≃L[K⸨X⸩] L` over the base Laurent field. -/
noncomputable def continuousEquivSelfLaurentSeries :
    ContinuousKaehlerDifferential K L ≃L[K⸨X⸩] L where
  toLinearEquiv := (equivSelf K L).restrictScalars K⸨X⸩
  continuous_toFun := (continuousEquivSelf K L).continuous
  continuous_invFun := (continuousEquivSelf K L).symm.continuous

instance [IsModuleTopology K⸨X⸩ L] :
    IsModuleTopology K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.iso (continuousEquivSelfLaurentSeries K L).symm

/-- Every `L`-linear map out of `Ω¹_cont(L/K)` into a module with continuous `L`-scalar
multiplication is continuous, without assuming continuity of addition on the target. -/
@[fun_prop]
theorem continuous_of_linearMap {M : Type*} [AddCommMonoid M] [Module L M]
    [TopologicalSpace M] [ContinuousSMul L M]
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) : Continuous ℓ :=
  ((continuousEquivSelf K L).continuous.fun_smul continuous_const).congr fun ω ↦ by
    simpa only [map_smul, continuousEquivSelf_apply] using
      congrArg ℓ (equivSelf_smul_D_algebraMap_single_one ω)

/-- Pullback of one-forms from `K⸨X⸩` to `L` is continuous whenever `algebraMap K⸨X⸩ L` is
continuous. -/
theorem continuous_map_of_continuous_algebraMap (h : Continuous (algebraMap K⸨X⸩ L)) :
    Continuous (map K L) :=
  (continuousEquivSelf K L).toHomeomorph.comp_continuous_iff.mp <|
    (h.comp (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).continuous).congr
      fun ω ↦ (equivSelf_map ω).symm

/-- Pullback of one-forms from `K⸨X⸩` to `L` is continuous when `K⸨X⸩` acts continuously on `L`. -/
theorem continuous_map [ContinuousSMul K⸨X⸩ L] : Continuous (map K L) :=
  continuous_map_of_continuous_algebraMap <|
    (continuous_id.fun_smul (continuous_const (y := (1 : L)))).congr fun f ↦ by
      simp [Algebra.smul_def]

/-- Pullback of continuous one-forms along a continuous `K⸨X⸩`-algebra homomorphism is
continuous. -/
theorem continuous_mapAlgHom {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [TopologicalSpace M]
    (φ : L →ₐ[K⸨X⸩] M) (hφ : Continuous φ) :
    Continuous (mapAlgHom (K := K) φ) :=
  (continuousEquivSelf K M).toHomeomorph.comp_continuous_iff.mp <|
    (hφ.comp (continuousEquivSelf K L).continuous).congr fun ω ↦ (equivSelf_mapAlgHom φ ω).symm

/-- Between formally étale `K⸨X⸩`-algebras carrying the `K⸨X⸩`-module topology, pullback of
continuous one-forms along any `K⸨X⸩`-algebra homomorphism is continuous. -/
theorem continuous_mapAlgHom_of_isModuleTopology {M : Type*} [CommRing M] [Algebra K⸨X⸩ M]
    [Algebra K M] [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [TopologicalSpace M]
    [IsModuleTopology K⸨X⸩ L] [IsModuleTopology K⸨X⸩ M] (φ : L →ₐ[K⸨X⸩] M) :
    Continuous (mapAlgHom (K := K) φ) := by
  have : ContinuousAdd M := IsModuleTopology.toContinuousAdd K⸨X⸩ M
  exact continuous_mapAlgHom φ (IsModuleTopology.continuous_of_linearMap φ.toLinearMap)

/-- Functorial action of `e : L ≃ₐ[K⸨X⸩] M` as a continuous `K⸨X⸩`-linear equivalence when `L` and
`M` carry the `K⸨X⸩`-module topology. -/
noncomputable def continuousCongrAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [TopologicalSpace M]
    [IsModuleTopology K⸨X⸩ L] [IsModuleTopology K⸨X⸩ M] (e : L ≃ₐ[K⸨X⸩] M) :
    ContinuousKaehlerDifferential K L ≃L[K⸨X⸩] ContinuousKaehlerDifferential K M :=
  (congrAlgEquiv (K := K) e).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem coe_continuousCongrAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [TopologicalSpace M]
    [IsModuleTopology K⸨X⸩ L] [IsModuleTopology K⸨X⸩ M] (e : L ≃ₐ[K⸨X⸩] M) :
    ⇑(continuousCongrAlgEquiv (K := K) e) = congrAlgEquiv (K := K) e := by
  simp [continuousCongrAlgEquiv]

end ContinuousKaehlerDifferential

end InducedTopology

section FiniteModuleTopology

variable (K : Type*) [Field K]
  (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L] [Module.Finite K⸨X⸩ L]
  [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]

/-- **Automatic continuity of `d/dt`.** On a finite formally étale `K⸨X⸩`-algebra carrying the
`K⸨X⸩`-module topology, the canonical derivation `Extension.derivation K L` is continuous. -/
@[fun_prop]
theorem continuous_derivation : Continuous (derivation K L) := by
  have : IsTopologicalRing L := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  let b := Module.Free.chooseBasis K⸨X⸩ L
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex K⸨X⸩ L)
  have hsum (x : L) :
      derivation K L x =
        ∑ i, (b.repr x i • derivation K L (b i) +
          _root_.LaurentSeries.derivative K (b.repr x i) • b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, Derivation.leibniz, derivation_algebraMap, smul_eq_mul, smul_eq_mul,
      laurentSeriesDerivation_apply, ← Algebra.smul_def, mul_comm (b i), ← Algebra.smul_def]
  refine (continuous_finsetSum Finset.univ fun i _ ↦ ?_).congr fun x ↦ (hsum x).symm
  have hcoord : Continuous fun x : L ↦ b.repr x i :=
    IsModuleTopology.continuous_of_linearMap (b.coord i)
  exact (hcoord.smul continuous_const).add
    (((_root_.LaurentSeries.continuous_derivative (K := K)).comp hcoord).smul continuous_const)

namespace ContinuousKaehlerDifferential

/-- **Automatic continuity of the universal derivation `d`.** On a finite formally étale
`K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, `D K L : L → Ω¹_cont(L/K)` is continuous. -/
@[fun_prop]
theorem continuous_D : Continuous (D K L) :=
  (continuousEquivSelf K L).toHomeomorph.comp_continuous_iff.mp <| by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def,
      continuousEquivSelf_apply, equivSelf_D] using continuous_derivation K L

variable {K L}
variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
  [TopologicalSpace M] [ContinuousSMul L M]

/-- Every derivation factoring through `D K L` is continuous on `L`. -/
theorem continuous_compDer (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) :
    Continuous (ℓ.compDer (D K L)) :=
  (continuous_of_linearMap ℓ).comp (continuous_D K L)

section Hausdorff

variable [Module K⸨X⸩ M] [IsScalarTower K⸨X⸩ L M] [IsScalarTower K K⸨X⸩ M] [T2Space M]

/-- A `K`-derivation of `L` into a Hausdorff topological `L`-module is continuous on `L` if and only
if its restriction to `K⸨X⸩` is continuous. -/
theorem continuous_derivation_iff_continuous_compAlgebraMap (δ : Derivation K L M) :
    Continuous δ ↔ Continuous (δ.compAlgebraMap K⸨X⸩) := by
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd K⸨X⸩ L
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  have halg : Continuous (algebraMap K⸨X⸩ L) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K⸨X⸩ L)
  refine ⟨fun hδ ↦ hδ.comp halg, fun hδ ↦ ?_⟩
  exact ((continuous_derivation K L).fun_smul continuous_const).congr fun x ↦
    (apply_eq_derivation_smul δ hδ x).symm

/-- **The continuous linear factorization of a continuous derivation through `d`.** -/
noncomputable def liftContinuous (δ : Derivation K L M) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential K L →L[L] M :=
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  let hδ₀ : Continuous (δ.compAlgebraMap K⸨X⸩) :=
    (continuous_derivation_iff_continuous_compAlgebraMap δ).mp hδ
  { toLinearMap := lift δ hδ₀
    cont := continuous_of_linearMap (lift δ hδ₀) }

@[simp]
theorem toLinearMap_liftContinuous [ContinuousSMul K⸨X⸩ M] (δ : Derivation K L M)
    (hδ : Continuous δ) :
    (liftContinuous δ hδ).toLinearMap =
      lift δ ((continuous_derivation_iff_continuous_compAlgebraMap δ).mp hδ) :=
  (rfl)

@[simp]
theorem liftContinuous_mk (δ : Derivation K L M) (hδ : Continuous δ) (ω : Ω[L⁄K]) :
    liftContinuous δ hδ (mk K L ω) = δ.liftKaehlerDifferential ω := by
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  exact lift_mk δ ((continuous_derivation_iff_continuous_compAlgebraMap δ).mp hδ) ω

@[simp]
theorem liftContinuous_D (δ : Derivation K L M) (hδ : Continuous δ) (x : L) :
    liftContinuous δ hδ (D K L x) = δ x := by
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  exact lift_D δ ((continuous_derivation_iff_continuous_compAlgebraMap δ).mp hδ) x

theorem compDer_liftContinuous (δ : Derivation K L M) (hδ : Continuous δ) :
    (liftContinuous δ hδ).toLinearMap.compDer (D K L) = δ :=
  Derivation.ext (liftContinuous_D δ hδ)

theorem liftContinuous_unique (δ : Derivation K L M) (hδ : Continuous δ)
    (ℓ : ContinuousKaehlerDifferential K L →L[L] M)
    (h : ℓ.toLinearMap.compDer (D K L) = δ) :
    ℓ = liftContinuous δ hδ := by
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  have hℓ := lift_unique δ ((continuous_derivation_iff_continuous_compAlgebraMap δ).mp hδ)
    ℓ.toLinearMap h
  exact ContinuousLinearMap.ext fun ω ↦ DFunLike.congr_fun hℓ ω

/-- **Topological universal property of `Ω¹_cont(L/K)`.** Every continuous `K`-derivation of `L`
into a Hausdorff module with continuous `L`-scalar multiplication factors uniquely through `D K L`
by a continuous `L`-linear map. -/
theorem existsUnique_continuousLinearMap_compDer_eq (δ : Derivation K L M) (hδ : Continuous δ) :
    ∃! ℓ : ContinuousKaehlerDifferential K L →L[L] M, ℓ.toLinearMap.compDer (D K L) = δ :=
  ⟨liftContinuous δ hδ, compDer_liftContinuous δ hδ, fun ℓ h ↦ liftContinuous_unique δ hδ ℓ h⟩

/-- A `K`-derivation of `L` into a Hausdorff module with continuous `L`-scalar multiplication is
continuous if and only if it factors through `D K L` by a continuous `L`-linear map. -/
theorem exists_continuousLinearMap_compDer_eq_iff (δ : Derivation K L M) :
    (∃ ℓ : ContinuousKaehlerDifferential K L →L[L] M, ℓ.toLinearMap.compDer (D K L) = δ) ↔
      Continuous δ :=
  ⟨fun ⟨ℓ, h⟩ ↦ h ▸ continuous_compDer ℓ.toLinearMap,
    fun hδ ↦ ⟨liftContinuous δ hδ, compDer_liftContinuous δ hδ⟩⟩

end Hausdorff

end ContinuousKaehlerDifferential

end FiniteModuleTopology

end TauCeti.LaurentSeries.Extension
