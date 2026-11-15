/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale.Basic

/-!
# Functoriality and tower base change for continuous one-forms of étale Laurent extensions

Let `K` be a field and `F = K⸨X⸩`. Any `F`-algebra homomorphism `φ : L →ₐ[F] M` between formally
étale `F`-algebras intertwines the canonical derivations `D_L` and `D_M` extending `d/dt`, and
therefore induces a `φ`-semilinear pullback `mapAlgHom φ : Ω¹_cont(L/K) → Ω¹_cont(M/K)` commuting
with the universal derivations `d` and with pullback from `Ω¹_cont(F/K)`. An `F`-algebra
equivalence `e : L ≃ₐ[F] M` upgrades to an `F`-linear equivalence `congrAlgEquiv e` intertwining
scalar multiplication through `e`.

For a tower `F → L → M` of formally étale `F`-algebras, specialization to `algebraMap L M` gives a
pullback `mapTower K L M : Ω¹_cont(L/K) →ₛₗ[algebraMap L M] Ω¹_cont(M/K)` induced by
`KaehlerDifferential.map K K L M`, together with the relative scalar-extension equivalence
`relativeTensorEquiv K L M : M ⊗[L] Ω¹_cont(L/K) ≃ₗ[M] Ω¹_cont(M/K)`, `y ⊗ ω ↦ y • mapTower ω`.
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

section Functoriality

variable {K : Type*} [Field K]
  {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]
  {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
  [Algebra.FormallyEtale K⸨X⸩ M]
  {N : Type*} [CommRing N] [Algebra K⸨X⸩ N] [Algebra K N] [IsScalarTower K K⸨X⸩ N]
  [Algebra.FormallyEtale K⸨X⸩ N]

/-- Every `K⸨X⸩`-algebra homomorphism between formally étale `K⸨X⸩`-algebras intertwines their
canonical derivations `d/dt`. -/
@[simp]
theorem map_derivation (φ : L →ₐ[K⸨X⸩] M) (x : L) :
    φ (derivation K L x) = derivation K M (φ x) :=
  φ.map_derivation_of_formallyUnramified (fun f ↦ by simp) x

/-- In a tower `K⸨X⸩ → L → M` of formally étale `K⸨X⸩`-algebras, `D_M` extends `D_L`. -/
@[simp]
theorem derivation_tower_algebraMap [Algebra L M] [IsScalarTower K⸨X⸩ L M] (x : L) :
    derivation K M (algebraMap L M x) = algebraMap L M (derivation K L x) :=
  (map_derivation (IsScalarTower.toAlgHom K⸨X⸩ L M) x).symm

namespace ContinuousKaehlerDifferential

/-- Pullback of continuous one-forms along a `K⸨X⸩`-algebra homomorphism `φ : L →ₐ[K⸨X⸩] M`:
`x dt ↦ φ(x) dt`. -/
noncomputable def mapAlgHom (φ : L →ₐ[K⸨X⸩] M) :
    ContinuousKaehlerDifferential K L →ₛₗ[(φ : L →+* M)] ContinuousKaehlerDifferential K M :=
  (equivSelf K M).symm.toLinearMap.comp
    ((φ : L →+* M).toSemilinearMap.comp (equivSelf K L).toLinearMap)

/-- In the coordinate `dt`, `mapAlgHom φ` applies `φ` to the `dt`-coefficient. -/
@[simp]
theorem equivSelf_mapAlgHom (φ : L →ₐ[K⸨X⸩] M) (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (mapAlgHom φ ω) = φ (equivSelf K L ω) :=
  (equivSelf K M).apply_symm_apply _

/-- `mapAlgHom φ` commutes with the universal derivations `d`. -/
@[simp]
theorem mapAlgHom_D (φ : L →ₐ[K⸨X⸩] M) (x : L) :
    mapAlgHom φ (D K L x) = D K M (φ x) :=
  (equivSelf K M).injective <| by simp

/-- `mapAlgHom φ` commutes with pullback from the base Laurent field `K⸨X⸩`. -/
@[simp]
theorem mapAlgHom_map (φ : L →ₐ[K⸨X⸩] M) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapAlgHom φ (map K L ω) = map K M ω :=
  (equivSelf K M).injective <| by simp

/-- `mapAlgHom φ` is `K⸨X⸩`-linear. -/
@[simp]
theorem mapAlgHom_laurentSeries_smul (φ : L →ₐ[K⸨X⸩] M) (f : K⸨X⸩)
    (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom φ (f • ω) = f • mapAlgHom φ ω := by
  rw [← IsScalarTower.algebraMap_smul L f, map_smulₛₗ, RingHom.coe_coe, φ.commutes,
    IsScalarTower.algebraMap_smul]

/-- `mapAlgHom φ` is the unique `φ`-semilinear map sending `dt` to `dt`. -/
theorem eq_mapAlgHom_of_apply_D_single_one (φ : L →ₐ[K⸨X⸩] M)
    (ℓ : ContinuousKaehlerDifferential K L →ₛₗ[(φ : L →+* M)] ContinuousKaehlerDifferential K M)
    (h : ℓ (D K L (algebraMap K⸨X⸩ L (single 1 1))) =
      D K M (algebraMap K⸨X⸩ M (single 1 1))) :
    ℓ = mapAlgHom φ :=
  hom_ext <| by rw [h, ← φ.commutes (single 1 1), mapAlgHom_D]

/-- Pullback of continuous one-forms along an injective `K⸨X⸩`-algebra map is injective. -/
theorem mapAlgHom_injective (φ : L →ₐ[K⸨X⸩] M) (hφ : Function.Injective φ) :
    Function.Injective (mapAlgHom φ) := fun ω η h ↦
  (equivSelf K L).injective <| hφ <| by
    simpa only [equivSelf_mapAlgHom] using congrArg (equivSelf K M) h

@[simp]
theorem mapAlgHom_id (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom (AlgHom.id K⸨X⸩ L) ω = ω :=
  (equivSelf K L).injective <| by rw [equivSelf_mapAlgHom, AlgHom.id_apply]

theorem mapAlgHom_comp (ψ : M →ₐ[K⸨X⸩] N) (φ : L →ₐ[K⸨X⸩] M)
    (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom (ψ.comp φ) ω = mapAlgHom ψ (mapAlgHom φ ω) :=
  (equivSelf K N).injective <| by simp

/-- Functorial action of a `K⸨X⸩`-algebra equivalence `e : L ≃ₐ[K⸨X⸩] M` on continuous one-forms,
bundled as a `K⸨X⸩`-linear equivalence `Ω¹_cont(L/K) ≃ₗ[K⸨X⸩] Ω¹_cont(M/K)` that intertwines
scalar multiplication by `L` and `M` through `e`
(`ContinuousKaehlerDifferential.congrAlgEquiv_smul`). -/
noncomputable def congrAlgEquiv (e : L ≃ₐ[K⸨X⸩] M) :
    ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩] ContinuousKaehlerDifferential K M where
  toFun := mapAlgHom e.toAlgHom
  invFun := mapAlgHom e.symm.toAlgHom
  map_add' := map_add _
  map_smul' := mapAlgHom_laurentSeries_smul e.toAlgHom
  left_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.symm_comp, mapAlgHom_id]
  right_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.comp_symm, mapAlgHom_id]

theorem congrAlgEquiv_apply (e : L ≃ₐ[K⸨X⸩] M) (ω : ContinuousKaehlerDifferential K L) :
    congrAlgEquiv e ω = mapAlgHom e.toAlgHom ω :=
  (rfl)

@[simp]
theorem congrAlgEquiv_symm (e : L ≃ₐ[K⸨X⸩] M) :
    (congrAlgEquiv e).symm = congrAlgEquiv (K := K) e.symm :=
  (rfl)

theorem congrAlgEquiv_smul (e : L ≃ₐ[K⸨X⸩] M) (x : L) (ω : ContinuousKaehlerDifferential K L) :
    congrAlgEquiv e (x • ω) = e x • congrAlgEquiv e ω :=
  map_smulₛₗ (mapAlgHom e.toAlgHom) x ω

@[simp]
theorem equivSelf_congrAlgEquiv (e : L ≃ₐ[K⸨X⸩] M) (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (congrAlgEquiv e ω) = e (equivSelf K L ω) :=
  equivSelf_mapAlgHom e.toAlgHom ω

@[simp]
theorem congrAlgEquiv_D (e : L ≃ₐ[K⸨X⸩] M) (x : L) :
    congrAlgEquiv e (D K L x) = D K M (e x) :=
  mapAlgHom_D e.toAlgHom x

@[simp]
theorem congrAlgEquiv_map (e : L ≃ₐ[K⸨X⸩] M) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    congrAlgEquiv e (map K L ω) = map K M ω :=
  mapAlgHom_map e.toAlgHom ω

@[simp]
theorem congrAlgEquiv_refl (ω : ContinuousKaehlerDifferential K L) :
    congrAlgEquiv (AlgEquiv.refl : L ≃ₐ[K⸨X⸩] L) ω = ω :=
  mapAlgHom_id ω

theorem congrAlgEquiv_trans (e : L ≃ₐ[K⸨X⸩] M) (e' : M ≃ₐ[K⸨X⸩] N)
    (ω : ContinuousKaehlerDifferential K L) :
    congrAlgEquiv (e.trans e') ω = congrAlgEquiv e' (congrAlgEquiv e ω) :=
  mapAlgHom_comp e'.toAlgHom e.toAlgHom ω

end ContinuousKaehlerDifferential

end Functoriality

section Tower

namespace ContinuousKaehlerDifferential

variable (K : Type*) [Field K]
  (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]
  (M : Type*) [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
  [Algebra L M] [Algebra.FormallyEtale K⸨X⸩ M]

/-- For an `L`-algebra `M` between formally étale `K⸨X⸩`-algebras, the `algebraMap L M`-semilinear
pullback of continuous one-forms `Ω¹_cont(L/K) →ₛₗ[algebraMap L M] Ω¹_cont(M/K)`. -/
noncomputable def mapTower :
    ContinuousKaehlerDifferential K L →ₛₗ[algebraMap L M] ContinuousKaehlerDifferential K M :=
  (equivSelf K M).symm.toLinearMap.comp
    ((algebraMap L M).toSemilinearMap.comp (equivSelf K L).toLinearMap)

variable {K L M}

@[simp]
theorem equivSelf_mapTower (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (mapTower K L M ω) = algebraMap L M (equivSelf K L ω) :=
  (equivSelf K M).apply_symm_apply _

variable (K L M) in
/-- **Relative scalar extension of continuous one-forms in étale towers.** For formally étale
`K⸨X⸩`-algebras `L` and `M` with `M` an `L`-algebra,
`M ⊗[L] Ω¹_cont(L/K) ≃ₗ[M] Ω¹_cont(M/K)` sends `y ⊗ ω` to `y • mapTower K L M ω`. -/
noncomputable def relativeTensorEquiv :
    M ⊗[L] ContinuousKaehlerDifferential K L ≃ₗ[M] ContinuousKaehlerDifferential K M :=
  LinearEquiv.baseChange L M _ _ (equivSelf K L) ≪≫ₗ
    AlgebraTensorModule.rid L M M ≪≫ₗ (equivSelf K M).symm

@[simp]
theorem relativeTensorEquiv_tmul (y : M) (ω : ContinuousKaehlerDifferential K L) :
    relativeTensorEquiv K L M (y ⊗ₜ ω) = y • mapTower K L M ω := by
  apply (equivSelf K M).injective
  simp [relativeTensorEquiv, LinearEquiv.baseChange, Algebra.smul_def, mul_comm]

variable [IsScalarTower K⸨X⸩ L M]

theorem mapTower_apply (ω : ContinuousKaehlerDifferential K L) :
    mapTower K L M ω = mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ L M) ω :=
  (rfl)

@[simp]
theorem mapTower_D (x : L) :
    mapTower K L M (D K L x) = D K M (algebraMap L M x) :=
  mapAlgHom_D (IsScalarTower.toAlgHom K⸨X⸩ L M) x

@[simp]
theorem mapTower_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapTower K L M (map K L ω) = map K M ω :=
  mapAlgHom_map (IsScalarTower.toAlgHom K⸨X⸩ L M) ω

/-- `mapTower K L M` is induced by the algebraic Kähler differential pullback
`Ω[L⁄K] →ₗ[L] Ω[M⁄K]`. -/
theorem mapTower_mk [IsScalarTower K L M] (ω : Ω[L⁄K]) :
    mapTower K L M (mk K L ω) = mk K M (KaehlerDifferential.map K K L M ω) := by
  apply (equivSelf K M).injective
  rw [equivSelf_mapTower, equivSelf_mk, equivSelf_mk]
  have hω : ω ∈ Submodule.span L (Set.range (KaehlerDifferential.D K L)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ hx =>
    rcases hx with ⟨x, rfl⟩
    simp
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul a x _ hx =>
    rw [map_smul, smul_eq_mul, map_mul, hx, LinearMap.map_smul, ← algebraMap_smul M a, map_smul,
      smul_eq_mul]

theorem mapTower_injective [FaithfulSMul L M] : Function.Injective (mapTower K L M) :=
  mapAlgHom_injective (IsScalarTower.toAlgHom K⸨X⸩ L M) (FaithfulSMul.algebraMap_injective L M)

end ContinuousKaehlerDifferential

end Tower

end TauCeti.LaurentSeries.Extension
