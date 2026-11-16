/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Highest
public import TauCeti.RepresentationTheory.LSPath.Crystal.Basic
public import TauCeti.RepresentationTheory.LSPath.Highest
public import TauCeti.RepresentationTheory.LSPath.Realization
public import TauCeti.RepresentationTheory.LSPath.Word

import Mathlib.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.LSPath.LinearMap
import TauCeti.RepresentationTheory.LSPath.Lower
import TauCeti.RepresentationTheory.LSPath.Raise
import TauCeti.RepresentationTheory.LSPath.Weight

/-!
# The normal crystal of Lakshmibai–Seshadri paths and the straight-path component

Let `P : RootDatum ι X Y` be a finite reduced root datum with base `b : P.Base`, and let `λ ∈ X` be
a dominant weight (`λ ∈ dominantChamber P b`), allowing `λ = 0`, weights on chamber walls, pure
central weights, and empty root systems.

Combining lattice-valued endpoints (`TauCeti.LSPath.exists_mem_rootSpan_endpoint_eq_add`),
integrality of minimum simple-coroot heights (`TauCeti.LSPath.exists_minHeight_eq_intCast`), and
stability of Lakshmibai–Seshadri paths under Littelmann's raising and lowering operators
(`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`,
`TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`), the realized LS paths of shape `λ` in any
compatible realization `(f, F)` form a crystal-admissible path set
(`TauCeti.LSPath.isCrystalSet_range_toPLPath`).

Applying this to the canonical injection `X →+ (ℚ ⊗[ℤ] X)`
(`RootPairing.tensorProduct_mk_injective`, requiring no freeness assumption on `X` or `Y`) endows
`LSPath P b λ` with an intrinsic normal crystal structure `TauCeti.LSPath.normalCrystal`.
Semilinear pushforward along `ℚ →+* 𝕜` (`TauCeti.PLPath.mapₛₗ`) shows that `normalCrystal` agrees
with Littelmann's path operators, endpoints, and string-length formulas in every ordered-field
realization `(𝕜, V, f, F)`, even when `f` is not injective.

Because `LSPath P b λ` is finite (`TauCeti.LSPath.finite`) and `straight λ` is its unique element
annihilated by all raising operators (`TauCeti.LSPath.forall_raise_eq_none_iff`), every LS path is
obtained from `straight λ` by a lowering word (`TauCeti.LSPath.exists_fWord_straight_eq_some`).
Consequently, in every compatible realization `(f, F)` the realized LS paths of shape `λ` coincide
with the paths reachable from `PLPath.straight 𝕜 (f λ)` by root steps or pure lowering words
(`TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen_rootStep`,
`TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord`), and when `f` is injective `toPLPath`
induces a strict crystal isomorphism onto the connected path component of `straight 𝕜 (f λ)`
(`TauCeti.LSPath.toNormalCrystalComponentIso`).

## Main definitions

* `TauCeti.LSPath.normalCrystal`: the intrinsic normal crystal structure on `LSPath P b λ` for
  dominant `λ`.
* `TauCeti.LSPath.toNormalCrystalOnIso`: strict crystal isomorphism from `normalCrystal` onto the
  realized LS path crystal `PLPath.normalCrystalOn`.
* `TauCeti.LSPath.toNormalCrystalComponentIso`: strict crystal isomorphism from `normalCrystal` onto
  the connected path component `PLPath.normalCrystalComponent` of `straight 𝕜 (f λ)`.

## Main results

* `TauCeti.LSPath.isCrystalSet_range_toPLPath`: the realized LS paths of dominant shape `λ` form a
  `PLPath.IsCrystalSet`.
* `TauCeti.LSPath.forall_normalCrystal_e_eq_none_iff`: `straight λ` is the unique highest element of
  `normalCrystal`.
* `TauCeti.LSPath.exists_fWord_straight_eq_some`: every LS path of dominant shape `λ` is generated
  from `straight λ` by a word of lowering operators.
* `TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen_rootStep`,
  `TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord`: equivalence of the LS chain condition
  with generation from the straight path by root operators.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent. Math.
  116 (1994), §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§2, 4–5.
-/

public section

namespace TauCeti.LSPath

open Module Relation RootPairing Set
open scoped TensorProduct

section CrystalSet

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **Realized Lakshmibai–Seshadri paths form a crystal-admissible path set.** No injectivity
assumption on `f` is needed. -/
theorem isCrystalSet_range_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsCrystalSet b f F (range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) where
  endpoint_mem_range := by
    rintro _ ⟨π, rfl⟩
    obtain ⟨m, -, hm⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := 𝕜) hlam f
    exact ⟨_, hm.symm⟩
  exists_minHeight_eq_intCast := by
    rintro _ ⟨π, rfl⟩ i
    exact π.exists_minHeight_eq_intCast hlam f i (F i) (hF i)
  mem_of_raise_eq_some := by
    rintro i _ _ hr ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_raise_eq_some hlam f i (F i) (hF i) hr
  mem_of_lower_eq_some := by
    rintro i _ _ hl ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_lower_eq_some hlam f i (F i) (hF i) hl

/-- Every realized LS path of dominant shape is an integral path in Littelmann's sense. -/
theorem isIntegralPath_toPLPath (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsIntegralPath b f F (π.toPLPath 𝕜 f) :=
  (isCrystalSet_range_toPLPath hlam hF).subset_isIntegralPath ⟨π, rfl⟩

/-- For dominant `λ`, the straight path `PLPath.straight 𝕜 (f λ)` is an integral path. -/
theorem isIntegralPath_straight (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsIntegralPath b f F (PLPath.straight 𝕜 (f lam)) := by
  simpa using isIntegralPath_toPLPath (straight lam) hlam hF

end CrystalSet

section NormalCrystal

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

private def ratEmbed (X : Type*) [AddCommGroup X] : X →+ (ℚ ⊗[ℤ] X) :=
  (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

private noncomputable def ratCoroot (P : RootDatum ι X Y) (b : P.Base) (i : b.support) :
    Dual ℚ (ℚ ⊗[ℤ] X) :=
  LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ).comp (P.coroot' i.1))

omit [Finite ι] [P.IsReduced] in
private theorem ratEmbed_injective (P : RootDatum ι X Y) : Function.Injective (ratEmbed X) :=
  P.tensorProduct_mk_injective ℚ

omit [Finite ι] [P.IsReduced] in
private theorem ratCoroot_ratEmbed (i : b.support) (x : X) :
    ratCoroot P b i (ratEmbed X x) = (P.coroot' i x : ℚ) := by
  simp [ratEmbed, ratCoroot]

private noncomputable def ratEquiv (hlam : lam ∈ dominantChamber P b) :
    LSPath P b lam ≃ range (fun π : LSPath P b lam ↦ π.toPLPath ℚ (ratEmbed X)) :=
  Equiv.ofInjective _
    (toPLPath_injective_of_coroot' hlam (ratEmbed_injective P).injOn ratCoroot_ratEmbed)

@[simp]
private theorem ratEquiv_apply_coe (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (ratEquiv hlam π : PLPath ℚ (ℚ ⊗[ℤ] X)) = π.toPLPath ℚ (ratEmbed X) :=
  (rfl)

/-- **The normal crystal of Lakshmibai–Seshadri paths of dominant shape `λ`.** Its weight map
assigns to each LS path its lattice endpoint, its raising and lowering operators are Littelmann's
path root operators, and its string lengths are `ε_i(π) = -min H_i(π)` and
`φ_i(π) = H_i(π)(1) - min H_i(π)`. No auxiliary realization parameters or freeness assumptions on
`X` or `Y` are required. -/
noncomputable def normalCrystal (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) :=
  (PLPath.normalCrystalOn (ratEmbed_injective P) ratCoroot_ratEmbed
    (isCrystalSet_range_toPLPath hlam ratCoroot_ratEmbed)).transport (ratEquiv hlam).symm

section Realization

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Canonical `(Rat.castHom 𝕜)`-semilinear realization map `(ℚ ⊗[ℤ] X) →ₛₗ[Rat.castHom 𝕜] V`
extending an additive realization `f : X →+ V`. -/
private noncomputable def ratLiftₛₗ (f : X →+ V) : (ℚ ⊗[ℤ] X) →ₛₗ[Rat.castHom 𝕜] V :=
  let B : ℚ →ₗ[ℤ] X →ₗ[ℤ] V :=
    { toFun q :=
        { toFun x := (q : 𝕜) • f x
          map_add' x₁ x₂ := by rw [map_add, smul_add]
          map_smul' n x := by rw [map_zsmul, RingHom.id_apply, smul_comm] }
      map_add' q₁ q₂ := by ext x; simp [Rat.cast_add, add_smul]
      map_smul' n q := by
        ext x
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
          zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, mul_smul, Int.cast_smul_eq_zsmul] }
  { toFun := TensorProduct.lift B
    map_add' := map_add _
    map_smul' r u :=
      u.inductionOn
        (fun q x ↦ by simp [B, TensorProduct.smul_tmul', Rat.cast_mul, mul_smul])
        (fun u₁ u₂ ih₁ ih₂ ↦ by simp [smul_add, ih₁, ih₂]) }

@[simp]
private theorem ratLiftₛₗ_ratEmbed (f : X →+ V) (x : X) :
    ratLiftₛₗ (𝕜 := 𝕜) f (ratEmbed X x) = f x := by
  simp [ratLiftₛₗ, ratEmbed]

private theorem mapₛₗ_ratLiftₛₗ_toPLPath (f : X →+ V) (π : LSPath P b lam) :
    (π.toPLPath ℚ (ratEmbed X)).mapₛₗ (ratLiftₛₗ (𝕜 := 𝕜) f) = π.toPLPath 𝕜 f := by
  rw [toPLPath_def, toPLPath_def, PLPath.mapₛₗ_ofSegments Rat.cast_strictMono]
  congr 1
  simp [timed_def, Function.comp_def, map_smulₛₗ]

omit [Finite ι] [P.IsReduced] in
private theorem apply_ratLiftₛₗ_eq {f : X →+ V} {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (u : ℚ ⊗[ℤ] X) :
    F i (ratLiftₛₗ (𝕜 := 𝕜) f u) = Rat.castHom 𝕜 (ratCoroot P b i u) :=
  u.inductionOn
    (fun q x ↦ by
      have htmul : ratLiftₛₗ (𝕜 := 𝕜) f (q ⊗ₜ[ℤ] x) = (q : 𝕜) • f x := rfl
      simp [htmul, ratCoroot, hF])
    (fun u₁ u₂ ih₁ ih₂ ↦ by simp [ih₁, ih₂])

/-- The endpoint of a realized LS path in any additive realization `f : X →+ V` is the image of its
crystal weight. -/
theorem endpoint_toPLPath_eq_apply_normalCrystal_wt (hlam : lam ∈ dominantChamber P b)
    (f : X →+ V) (π : LSPath P b lam) :
    (π.toPLPath 𝕜 f).endpoint = f ((normalCrystal hlam).wt π) := by
  rw [← mapₛₗ_ratLiftₛₗ_toPLPath f π, PLPath.endpoint_mapₛₗ, normalCrystal,
    NormalCrystal.transport_wt, Equiv.symm_symm, ← ratLiftₛₗ_ratEmbed (𝕜 := 𝕜) f,
    PLPath.apply_normalCrystalOn_wt, ratEquiv_apply_coe]

theorem normalCrystal_wt_eq_iff (hlam : lam ∈ dominantChamber P b)
    {f : X →+ V} (hf : Function.Injective f) {π : LSPath P b lam} {μ : X} :
    (normalCrystal hlam).wt π = μ ↔ (π.toPLPath 𝕜 f).endpoint = f μ := by
  rw [endpoint_toPLPath_eq_apply_normalCrystal_wt, hf.eq_iff]

/-- **Raising string-length formula** in any compatible realization `(f, F)`:
`ε_i(π) = -min H_i(π)`. -/
theorem cast_normalCrystal_ε (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).ε i π : 𝕜) = -(π.toPLPath 𝕜 f).minHeight (F i) := by
  rw [← mapₛₗ_ratLiftₛₗ_toPLPath f π,
    PLPath.minHeight_mapₛₗ Rat.cast_strictMono (apply_ratLiftₛₗ_eq hF i),
    normalCrystal, NormalCrystal.transport_ε, Equiv.symm_symm,
    ← Rat.cast_natCast (α := 𝕜), PLPath.cast_normalCrystalOn_ε, ratEquiv_apply_coe,
    Rat.coe_castHom, Rat.cast_neg]

/-- **Lowering string-length formula** in any compatible realization `(f, F)`:
`φ_i(π) = H_i(π)(1) - min H_i(π)`. -/
theorem cast_normalCrystal_φ (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).φ i π : 𝕜) =
      F i (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight (F i) := by
  rw [← mapₛₗ_ratLiftₛₗ_toPLPath f π, PLPath.endpoint_mapₛₗ, apply_ratLiftₛₗ_eq hF i,
    PLPath.minHeight_mapₛₗ Rat.cast_strictMono (apply_ratLiftₛₗ_eq hF i),
    normalCrystal, NormalCrystal.transport_φ, Equiv.symm_symm,
    ← Rat.cast_natCast (α := 𝕜), PLPath.cast_normalCrystalOn_φ, ratEquiv_apply_coe,
    Rat.coe_castHom, Rat.cast_sub]

theorem normalCrystal_ε_eq_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} {n : ℕ} :
    (normalCrystal hlam).ε i π = n ↔ -(π.toPLPath 𝕜 f).minHeight (F i) = n := by
  rw [← Nat.cast_inj (R := 𝕜), cast_normalCrystal_ε hlam hF]

theorem normalCrystal_φ_eq_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} {n : ℕ} :
    (normalCrystal hlam).φ i π = n ↔
      F i (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight (F i) = n := by
  rw [← Nat.cast_inj (R := 𝕜), cast_normalCrystal_φ hlam hF]

/-- Realizing an LS path intertwines `(normalCrystal hlam).e i` with Littelmann's path raising
operator `PLPath.raise (F i) (f (P.root i))` in any compatible realization `(f, F)`. -/
theorem map_toPLPath_normalCrystal_e (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).e i π).map (·.toPLPath 𝕜 f) =
      PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) := by
  rw [← mapₛₗ_ratLiftₛₗ_toPLPath f π, ← ratLiftₛₗ_ratEmbed (𝕜 := 𝕜) f (P.root i),
    PLPath.raise_mapₛₗ Rat.cast_strictMono (apply_ratLiftₛₗ_eq hF i),
    normalCrystal, NormalCrystal.transport_e, Equiv.symm_symm, ← ratEquiv_apply_coe hlam π,
    ← PLPath.unattach_normalCrystalOn_e
      (hf := ratEmbed_injective P) (hF := ratCoroot_ratEmbed)
      (hS := isCrystalSet_range_toPLPath hlam ratCoroot_ratEmbed),
    Option.unattach, Option.map_map, Option.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply, ← mapₛₗ_ratLiftₛₗ_toPLPath (𝕜 := 𝕜) f,
    ← ratEquiv_apply_coe hlam, Equiv.apply_symm_apply]

/-- Realizing an LS path intertwines `(normalCrystal hlam).f i` with Littelmann's path lowering
operator `PLPath.lower (F i) (f (P.root i))` in any compatible realization `(f, F)`. -/
theorem map_toPLPath_normalCrystal_f (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).f i π).map (·.toPLPath 𝕜 f) =
      PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) := by
  rw [← mapₛₗ_ratLiftₛₗ_toPLPath f π, ← ratLiftₛₗ_ratEmbed (𝕜 := 𝕜) f (P.root i),
    PLPath.lower_mapₛₗ Rat.cast_strictMono (apply_ratLiftₛₗ_eq hF i),
    normalCrystal, NormalCrystal.transport_f, Equiv.symm_symm, ← ratEquiv_apply_coe hlam π,
    ← PLPath.unattach_normalCrystalOn_f
      (hf := ratEmbed_injective P) (hF := ratCoroot_ratEmbed)
      (hS := isCrystalSet_range_toPLPath hlam ratCoroot_ratEmbed),
    Option.unattach, Option.map_map, Option.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply, ← mapₛₗ_ratLiftₛₗ_toPLPath (𝕜 := 𝕜) f,
    ← ratEquiv_apply_coe hlam, Equiv.apply_symm_apply]

theorem normalCrystal_e_eq_none_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).e i π = none ↔
      PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = none := by
  rw [← map_toPLPath_normalCrystal_e hlam hF, Option.map_eq_none_iff]

theorem normalCrystal_f_eq_none_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).f i π = none ↔
      PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = none := by
  rw [← map_toPLPath_normalCrystal_f hlam hF, Option.map_eq_none_iff]

theorem normalCrystal_e_eq_some_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    (hf : Set.InjOn f (range fun w : P.weylGroup ↦ w • lam))
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).e i π = some π' ↔
      PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  rw [← map_toPLPath_normalCrystal_e hlam hF, Option.map_eq_some_iff]
  simp [toPLPath_inj_of_coroot' hlam hf hF]

theorem normalCrystal_f_eq_some_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    (hf : Set.InjOn f (range fun w : P.weylGroup ↦ w • lam))
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).f i π = some π' ↔
      PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  rw [← map_toPLPath_normalCrystal_f hlam hF, Option.map_eq_some_iff]
  simp [toPLPath_inj_of_coroot' hlam hf hF]

/-- Realizing an LS path intertwines `(normalCrystal hlam).eWord` with `PLPath.raiseWord`. -/
theorem map_toPLPath_normalCrystal_eWord (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).eWord w π).map (·.toPLPath 𝕜 f) =
      PLPath.raiseWord (fun i : b.support ↦ F i) (fun i : b.support ↦ f (P.root i)) w
        (π.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [NormalCrystal.eWord_cons, PLPath.raiseWord_cons, ← map_toPLPath_normalCrystal_e hlam hF]
    cases (normalCrystal hlam).e i π <;> simp [ih]

/-- Realizing an LS path intertwines `(normalCrystal hlam).fWord` with `PLPath.lowerWord`. -/
theorem map_toPLPath_normalCrystal_fWord (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).fWord w π).map (·.toPLPath 𝕜 f) =
      PLPath.lowerWord (fun i : b.support ↦ F i) (fun i : b.support ↦ f (P.root i)) w
        (π.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [NormalCrystal.fWord_cons, PLPath.lowerWord_cons, ← map_toPLPath_normalCrystal_f hlam hF]
    cases (normalCrystal hlam).f i π <;> simp [ih]

end Realization

/-! ### Highest path, generation by lowering words, and connectedness -/

/-- The weight of `straight λ` in `normalCrystal` is `λ`. -/
@[simp]
theorem normalCrystal_wt_straight (hlam : lam ∈ dominantChamber P b) :
    (normalCrystal hlam).wt (straight lam) = lam := by
  rw [normalCrystal_wt_eq_iff (𝕜 := ℚ) hlam (ratEmbed_injective P), toPLPath_straight,
    PLPath.endpoint_straight]

/-- **Uniqueness of the highest LS path in `normalCrystal`.** An LS path of dominant shape `λ` is
annihilated by all crystal raising operators if and only if it is `straight λ`. -/
theorem forall_normalCrystal_e_eq_none_iff (hlam : lam ∈ dominantChamber P b)
    {π : LSPath P b lam} :
    (∀ i, (normalCrystal hlam).e i π = none) ↔ π = straight lam := by
  have := P.flip_isReduced
  simp_rw [normalCrystal_e_eq_none_iff hlam ratCoroot_ratEmbed]
  exact π.forall_raise_eq_none_iff hlam (ratEmbed X) (ratCoroot P b) ratCoroot_ratEmbed

@[simp]
theorem normalCrystal_e_straight (hlam : lam ∈ dominantChamber P b) (i : b.support) :
    (normalCrystal hlam).e i (straight lam) = none :=
  (forall_normalCrystal_e_eq_none_iff hlam).mpr rfl i

@[simp]
theorem normalCrystal_ε_straight (hlam : lam ∈ dominantChamber P b) (i : b.support) :
    (normalCrystal hlam).ε i (straight lam) = 0 :=
  (normalCrystal hlam).ε_eq_zero_iff.mpr (normalCrystal_e_straight hlam i)

/-- **Every Lakshmibai–Seshadri path of dominant shape `λ` is generated from `straight λ` by a word
of crystal lowering operators.** -/
theorem exists_fWord_straight_eq_some (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    ∃ w : List b.support, (normalCrystal hlam).fWord w (straight lam) = some π := by
  have := finite hlam
  exact (normalCrystal hlam).exists_fWord_eq_some_of_unique_highest
    (fun _ hx ↦ (forall_normalCrystal_e_eq_none_iff hlam).mp hx) π

/-- Every Lakshmibai–Seshadri path of dominant shape `λ` can be raised to `straight λ`. -/
theorem exists_eWord_eq_some_straight (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    ∃ w : List b.support, (normalCrystal hlam).eWord w π = some (straight lam) := by
  obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
  exact ⟨w.reverse, (normalCrystal hlam).fWord_eq_some_iff.mp hw⟩

/-- **The crystal graph of `normalCrystal` is connected.** -/
theorem connected_normalCrystal_graph (hlam : lam ∈ dominantChamber P b) :
    (normalCrystal hlam).graph.Connected := by
  have hreach {π π' : LSPath P b lam} {w : List b.support}
      (hw : (normalCrystal hlam).fWord w π = some π') :
      (normalCrystal hlam).graph.Reachable π π' := by
    induction w generalizing π with
    | nil =>
      rw [NormalCrystal.fWord_nil, Option.some.injEq] at hw
      subst hw
      exact .refl _
    | cons i w ih =>
      obtain ⟨ρ, hρ, hw'⟩ := Option.bind_eq_some_iff.mp
        ((normalCrystal hlam).fWord_cons i w π ▸ hw)
      exact (((normalCrystal hlam).graph_adj_of_f_eq_some hρ).reachable).trans (ih hw')
  exact (normalCrystal hlam).graph.connected_iff_exists_forall_reachable.mpr
    ⟨straight lam, fun π ↦
      let ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
      hreach hw⟩

/-! ### Equivalence with the straight-path component in path models -/

section ComponentEquivalence

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}

omit [Finite ι] [P.IsReduced] in
private theorem reflTransGen_rootStep_of_lowerWord_eq_some {w : List b.support}
    {p q : PLPath 𝕜 V}
    (hw : PLPath.lowerWord (fun i : b.support ↦ F i) (fun i : b.support ↦ f (P.root i)) w p =
      some q) :
    ReflTransGen (PLPath.RootStep b f F) p q := by
  induction w generalizing p with
  | nil =>
    rw [PLPath.lowerWord_nil, Option.some.injEq] at hw
    subst hw
    exact .refl
  | cons i w ih =>
    obtain ⟨ρ, hρ, hw'⟩ := Option.bind_eq_some_iff.mp (PLPath.lowerWord_cons i w p ▸ hw)
    exact .head (.of_lower_eq_some hρ) (ih hw')

/-- **Equivalence of Lakshmibai–Seshadri paths with lowering-word generation.** In any compatible
realization `(f, F)`, a piecewise-linear path is the realization of an LS path of dominant shape `λ`
if and only if it is obtained from `PLPath.straight 𝕜 (f λ)` by a word of lowering operators. -/
theorem mem_range_toPLPath_iff_exists_lowerWord (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) {q : PLPath 𝕜 V} :
    q ∈ range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      ∃ w : List b.support,
        PLPath.lowerWord (fun i : b.support ↦ F i) (fun i : b.support ↦ f (P.root i)) w
          (PLPath.straight 𝕜 (f lam)) = some q := by
  constructor
  · rintro ⟨π, rfl⟩
    obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
    refine ⟨w, ?_⟩
    have hmap := congrArg (Option.map (·.toPLPath 𝕜 f)) hw
    rwa [map_toPLPath_normalCrystal_fWord hlam hF, toPLPath_straight, Option.map_some] at hmap
  · rintro ⟨w, hw⟩
    exact (isCrystalSet_range_toPLPath hlam hF).mem_of_reflTransGen_rootStep
      (reflTransGen_rootStep_of_lowerWord_eq_some hw) ⟨straight lam, toPLPath_straight 𝕜 f⟩

/-- **Equivalence of Lakshmibai–Seshadri paths with the root-operator component of `straight λ`.**
In any compatible realization `(f, F)`, a piecewise-linear path is the realization of an LS path of
dominant shape `λ` if and only if it is reachable from `PLPath.straight 𝕜 (f λ)` by a finite
sequence of simple-root raising and lowering steps. -/
theorem mem_range_toPLPath_iff_reflTransGen_rootStep (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) {q : PLPath 𝕜 V} :
    q ∈ range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      ReflTransGen (PLPath.RootStep b f F) (PLPath.straight 𝕜 (f lam)) q := by
  constructor
  · intro hq
    obtain ⟨w, hw⟩ := (mem_range_toPLPath_iff_exists_lowerWord hlam hF).mp hq
    exact reflTransGen_rootStep_of_lowerWord_eq_some hw
  · intro hwalk
    exact (isCrystalSet_range_toPLPath hlam hF).mem_of_reflTransGen_rootStep hwalk
      ⟨straight lam, toPLPath_straight 𝕜 f⟩

/-- **Strict crystal isomorphism onto the realized LS path crystal.** When `f` is injective,
`π ↦ π.toPLPath 𝕜 f` is a strict isomorphism of normal crystals from `normalCrystal hlam` onto
`PLPath.normalCrystalOn`. -/
noncomputable def toNormalCrystalOnIso (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalOn hf hF (isCrystalSet_range_toPLPath hlam hF)) where
  toEquiv := Equiv.ofInjective _ (toPLPath_injective_of_coroot' hlam hf.injOn hF)
  wt_toFun π := hf (by
    rw [PLPath.apply_normalCrystalOn_wt]
    exact endpoint_toPLPath_eq_apply_normalCrystal_wt (𝕜 := 𝕜) hlam f π)
  e_toFun i π := by
    rw [PLPath.normalCrystalOn_e_eq_map_iff]
    exact (map_toPLPath_normalCrystal_e hlam hF i π).symm

@[simp]
theorem toNormalCrystalOnIso_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (toNormalCrystalOnIso hf hF hlam π).1 = π.toPLPath 𝕜 f :=
  (rfl)

/-- **Strict crystal isomorphism onto the connected path component `B(λ)`.** When `f` is injective,
`π ↦ π.toPLPath 𝕜 f` identifies `LSPath.normalCrystal hlam` strictly with Littelmann's connected
path component `PLPath.normalCrystalComponent` generated by `PLPath.straight 𝕜 (f λ)`. -/
noncomputable def toNormalCrystalComponentIso (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalComponent hf hF
        ⟨PLPath.straight 𝕜 (f lam), isIntegralPath_straight hlam hF⟩) where
  toEquiv := Equiv.ofBijective
    (fun π ↦ ⟨⟨π.toPLPath 𝕜 f, isIntegralPath_toPLPath π hlam hF⟩,
      (PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff _ _).mpr
        ((mem_range_toPLPath_iff_reflTransGen_rootStep hlam hF).mp ⟨π, rfl⟩)⟩)
    ⟨fun π₁ π₂ h ↦ toPLPath_injective_of_coroot' hlam hf.injOn hF (congrArg (·.1.1) h),
     fun y ↦
       let ⟨π, hπ⟩ := (mem_range_toPLPath_iff_reflTransGen_rootStep hlam hF).mpr
         ((PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff _ y.1).mp y.2)
       ⟨π, Subtype.ext (Subtype.ext hπ)⟩⟩
  wt_toFun π := hf (by
    rw [PLPath.normalCrystalComponent, NormalCrystal.component_eq_restrict,
      NormalCrystal.restrict_wt, PLPath.apply_normalCrystalOn_wt]
    exact endpoint_toPLPath_eq_apply_normalCrystal_wt (𝕜 := 𝕜) hlam f π)
  e_toFun i π := by
    apply Option.map_injective Subtype.val_injective
    apply Option.map_injective Subtype.val_injective
    -- Unwrap the two subtype layers (`component` and `IsIntegralPath`) via `Option.unattach`.
    change (((PLPath.normalCrystal hf hF).component _).e i _).unattach.unattach = _
    rw [NormalCrystal.component_eq_restrict, NormalCrystal.unattach_restrict_e,
      PLPath.unattach_normalCrystalOn_e, Option.map_map, Option.map_map]
    exact (map_toPLPath_normalCrystal_e hlam hF i π).symm

@[simp]
theorem toNormalCrystalComponentIso_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (toNormalCrystalComponentIso hf hF hlam π).1.1 = π.toPLPath 𝕜 f :=
  (rfl)

end ComponentEquivalence

end NormalCrystal

end TauCeti.LSPath
