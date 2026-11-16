/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import TauCeti.FieldTheory.Galois.Restriction
import Mathlib.GroupTheory.Index
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.GroupTheory.GroupAction.Orbit.ENNReal

/-!
# Automorphisms and isomorphism classes over a normal intermediate field

Let `Ω / F` be a field extension and `U` a normal intermediate field of `Ω / F`. Every intermediate
field `L` of `Ω / F` containing `U` (`h : U ≤ L`) may be viewed over `U` as
`IntermediateField.extendScalars h : IntermediateField U Ω`, and conversely every intermediate field
`E` of `Ω / U` restricts to `E.restrictScalars F` over `F`. This file relates `F`-automorphisms and
`F`-isomorphism classes of such intermediate fields to their `U`-automorphisms and `U`-isomorphism
classes.

First, for any `h : U ≤ L` (with neither `Ω / F` assumed normal nor `L / F` assumed finite),
restriction `(IntermediateField.inclusion h).restrictNormalHom : (L ≃ₐ[F] L) →* (U ≃ₐ[F] U)` has
kernel isomorphic to `extendScalars h ≃ₐ[U] extendScalars h` and image consisting of those
automorphisms of `U / F` that extend to `L`. Consequently, `#Aut_F(L)` factors as `#Aut_U(L)` times
the cardinality of that image (`IntermediateField.natCard_algEquiv_eq_mul_of_le`).

Second, every `F`-algebra endomorphism `σ : Ω →ₐ[F] Ω` maps `U` onto itself, so pushing `E` forward
along `σ` yields another intermediate field `mapNormalBase σ E : IntermediateField U Ω` over `U`.
When `σ` is an automorphism of `Ω / F`, `mapNormalBase` preserves `U`-isomorphism and depends up to
`U`-isomorphism only on `AlgEquiv.restrictNormalHom U σ`. When `Ω / F` is also normal, two
intermediate fields of `Ω / U` become `F`-isomorphic upon restricting scalars to `F` if and only if
some automorphism of `Ω / F` carries one onto a field `U`-isomorphic to the other, and an
automorphism `σ` of `Ω / F` stabilizes `extendScalars h` up to `U`-isomorphism if and only if its
restriction to `U` extends to `L`.

Third, when `U / F` has finite automorphism group and `Ω / F` is normal, `Gal(U / F)` acts on any
set of `U`-isomorphism class representatives of an invariant family of intermediate fields of
`Ω / U`. Its orbits correspond to the `F`-isomorphism classes of the restricted fields, and its
point stabilizers are the subgroups of automorphisms of `U / F` extending to `L`. Orbit-stabilizer
counting then rewrites any `F`-isomorphism-invariant sum weighted by `1 / #Aut_F(L)` as
`(1 / #Aut_F(U))` times the sum over `U`-isomorphism classes weighted by `1 / #Aut_U(E)`
(`IntermediateField.tsum_div_natCard_algEquiv_eq_inv_natCard_mul_tsum`, and
`IntermediateField.tsum_div_natCard_algEquiv_eq_inv_finrank_mul_tsum` when `U / F` is finite
Galois).

## Main definitions

* `IntermediateField.extendScalarsAlgEquivMulEquivKer`: the group isomorphism between
  `extendScalars h ≃ₐ[U] extendScalars h` and the kernel of
  `(inclusion h).restrictNormalHom : (L ≃ₐ[F] L) →* (U ≃ₐ[F] U)`.
* `IntermediateField.mapNormalBase`: transport of an intermediate field of `Ω / U` along
  `σ : Ω →ₐ[F] Ω`, using `[Normal F U]` to land back over `U`.
* `IntermediateField.mapNormalBaseAlgEquiv`: a `U`-isomorphism `E₁ ≃ₐ[U] E₂` induces a
  `U`-isomorphism `mapNormalBase σ E₁ ≃ₐ[U] mapNormalBase σ E₂` for any `σ : Ω ≃ₐ[F] Ω`.
* `IntermediateField.mapNormalBaseAlgEquivOfRestrictNormalEq`: automorphisms of `Ω / F` with the
  same restriction to `U` give `U`-isomorphic images under `mapNormalBase`.

## Main results

* `IntermediateField.map_eq_self_of_normal`: `U.map σ = U` for normal `U / F` and any
  `σ : Ω →ₐ[F] Ω`, without assuming `Ω / F` normal.
* `IntermediateField.natCard_algEquiv_eq_mul_of_le`: `#Aut_F(L)` equals `#Aut_U(extendScalars h)`
  times the number of automorphisms of `U / F` extending to `L`.
* `IntermediateField.nonempty_restrictScalars_algEquiv_iff`: for normal `Ω / F`, `F`-isomorphism of
  `E₁.restrictScalars F` and `E₂.restrictScalars F` is equivalent to `U`-isomorphism after applying
  `mapNormalBase σ` for some `σ : Ω ≃ₐ[F] Ω`.
* `IntermediateField.nonempty_mapNormalBase_algEquiv_iff_mem_range`: for normal `Ω / F`, `σ`
  stabilizes `extendScalars h` up to `U`-isomorphism if and only if `σ|_U` extends to `L`.
* `IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard`: the `Gal(U / F)`-orbit count on
  `U`-isomorphism class representatives.
* `IntermediateField.tsum_div_natCard_algEquiv_eq_inv_natCard_mul_tsum` and
  `IntermediateField.tsum_div_natCard_algEquiv_eq_inv_finrank_mul_tsum`: weighted `1 / #Aut`
  class-sum reduction from `F`-isomorphism classes to `U`-isomorphism classes.

## References

* S. Lang, *Algebra*, revised 3rd ed., Graduate Texts in Mathematics 211, Springer, 2002,
  Chapter VI, §1.
* N. Bourbaki, *Algebra II*, Chapters 4–7, Springer, 1990, Chapter V, §10.
-/

public section
noncomputable section

open scoped ENNReal

namespace IntermediateField

section NormalSubextension

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- Every `F`-algebra endomorphism of `Ω` maps a normal intermediate field `U` of `Ω / F` onto
itself; unlike `IntermediateField.normal_iff_forall_map_eq`, no normality assumption on `Ω / F` is
needed. -/
@[simp]
theorem map_eq_self_of_normal (U : IntermediateField F Ω) [Normal F U] (σ : Ω →ₐ[F] Ω) :
    U.map σ = U :=
  (U.fieldRange_val ▸ AlgHom.map_fieldRange U.val σ).trans (AlgHom.fieldRange_of_normal _)

/-- If `U` is normal over `F` and contained in `L`, then `U` is also contained in `L.map σ` for
every `σ : Ω →ₐ[F] Ω`. -/
theorem le_map_of_normal {U L : IntermediateField F Ω} [Normal F U] (h : U ≤ L) (σ : Ω →ₐ[F] Ω) :
    U ≤ L.map σ :=
  (U.map_eq_self_of_normal σ).symm.trans_le (map_mono σ h)

/-- Restricting scalars of an intermediate field `E` of `Ω / U` down to `F` produces an
intermediate field containing `U`. -/
theorem le_restrictScalars {U : IntermediateField F Ω} (E : IntermediateField U Ω) :
    U ≤ E.restrictScalars F :=
  fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩

/-- Extending scalars back to `U` along any proof `U ≤ E.restrictScalars F` recovers `E`. -/
@[simp]
theorem extendScalars_of_restrictScalars {U : IntermediateField F Ω} (E : IntermediateField U Ω)
    {h : U ≤ E.restrictScalars F} :
    extendScalars h = E :=
  restrictScalars_injective F (extendScalars_restrictScalars h)

end NormalSubextension

/-! ### Restriction of automorphisms to a normal intermediate field -/

section AutomorphismRestriction

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
  {U L : IntermediateField F Ω} [Normal F U]

/-- Restriction along `inclusion h : U →ₐ[F] L` agrees with `σ` on elements of `U` viewed in `Ω`. -/
theorem restrictNormalHom_inclusion_commutes (h : U ≤ L) (σ : L ≃ₐ[F] L) (x : U) :
    (σ ⟨x.1, h x.2⟩ : Ω) = (inclusion h).restrictNormalHom σ x :=
  congrArg Subtype.val ((inclusion h).restrictNormalHom_commutes σ x).symm

/-- `τ` is the restriction of `σ : L ≃ₐ[F] L` along `inclusion h` precisely when `σ` and `τ` agree
on every element of `U` inside `Ω`. -/
theorem restrictNormalHom_inclusion_eq_iff (h : U ≤ L) {σ : L ≃ₐ[F] L} {τ : U ≃ₐ[F] U} :
    (inclusion h).restrictNormalHom σ = τ ↔ ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = τ x := by
  rw [(inclusion h).restrictNormalHom_eq_iff]
  exact forall_congr' fun _ ↦ Subtype.ext_iff

/-- An `F`-automorphism of `L` lies in the kernel of restriction to `U` if and only if it fixes
every element of `U` pointwise. -/
theorem mem_ker_restrictNormalHom_inclusion_iff (h : U ≤ L) {σ : L ≃ₐ[F] L} :
    σ ∈ (inclusion h).restrictNormalHom.ker ↔ ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = x := by
  rw [MonoidHom.mem_ker, restrictNormalHom_inclusion_eq_iff]
  rfl

/-- An `F`-automorphism `τ` of `U` lies in the range of restriction from `L` if and only if some
`F`-automorphism of `L` agrees with `τ` on `U`. -/
theorem mem_range_restrictNormalHom_inclusion_iff (h : U ≤ L) {τ : U ≃ₐ[F] U} :
    τ ∈ (inclusion h).restrictNormalHom.range ↔
      ∃ σ : L ≃ₐ[F] L, ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = τ x := by
  rw [MonoidHom.mem_range]
  exact exists_congr fun _ ↦ restrictNormalHom_inclusion_eq_iff h

/-- The `U`-automorphisms of `extendScalars h` correspond as a group to the `F`-automorphisms of
`L` that restrict to the identity on `U`. -/
def extendScalarsAlgEquivMulEquivKer (h : U ≤ L) :
    (extendScalars h ≃ₐ[U] extendScalars h) ≃* (inclusion h).restrictNormalHom.ker where
  toFun ρ :=
    ⟨{ toFun x := ⟨(ρ ⟨x.1, x.2⟩ : Ω), (ρ ⟨x.1, x.2⟩).2⟩
       invFun x := ⟨(ρ.symm ⟨x.1, x.2⟩ : Ω), (ρ.symm ⟨x.1, x.2⟩).2⟩
       left_inv x := Subtype.ext (congrArg Subtype.val (ρ.symm_apply_apply ⟨x.1, x.2⟩))
       right_inv x := Subtype.ext (congrArg Subtype.val (ρ.apply_symm_apply ⟨x.1, x.2⟩))
       map_mul' x y := Subtype.ext (congrArg Subtype.val (map_mul ρ ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
       map_add' x y := Subtype.ext (congrArg Subtype.val (map_add ρ ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
       commutes' a := Subtype.ext (congrArg Subtype.val (ρ.commutes (algebraMap F U a))) },
      (mem_ker_restrictNormalHom_inclusion_iff h).2 fun x ↦
        congrArg Subtype.val (ρ.commutes x)⟩
  invFun σ :=
    { toFun x := ⟨(σ.1 ⟨x.1, x.2⟩ : Ω), (σ.1 ⟨x.1, x.2⟩).2⟩
      invFun x := ⟨(σ.1.symm ⟨x.1, x.2⟩ : Ω), (σ.1.symm ⟨x.1, x.2⟩).2⟩
      left_inv x := Subtype.ext (congrArg Subtype.val (σ.1.symm_apply_apply ⟨x.1, x.2⟩))
      right_inv x := Subtype.ext (congrArg Subtype.val (σ.1.apply_symm_apply ⟨x.1, x.2⟩))
      map_mul' x y := Subtype.ext (congrArg Subtype.val (map_mul σ.1 ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
      map_add' x y := Subtype.ext (congrArg Subtype.val (map_add σ.1 ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
      commutes' x := Subtype.ext ((mem_ker_restrictNormalHom_inclusion_iff h).1 σ.2 x) }
  left_inv _ := AlgEquiv.ext fun _ ↦ rfl
  right_inv _ := Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)

@[simp]
theorem coe_extendScalarsAlgEquivMulEquivKer_apply (h : U ≤ L)
    (ρ : extendScalars h ≃ₐ[U] extendScalars h) (x : L) :
    (((extendScalarsAlgEquivMulEquivKer h ρ : (inclusion h).restrictNormalHom.ker) : L ≃ₐ[F] L) x :
      Ω) = ρ ⟨x.1, x.2⟩ :=
  (rfl)

@[simp]
theorem coe_extendScalarsAlgEquivMulEquivKer_symm_apply (h : U ≤ L)
    (σ : (inclusion h).restrictNormalHom.ker) (x : extendScalars h) :
    ((extendScalarsAlgEquivMulEquivKer h).symm σ x : Ω) = (σ : L ≃ₐ[F] L) ⟨x.1, x.2⟩ :=
  (rfl)

/-- **Automorphism count over a normal subextension**: for any normal intermediate field `U ≤ L`,
the cardinality of `L ≃ₐ[F] L` is the cardinality of `extendScalars h ≃ₐ[U] extendScalars h` times
the cardinality of the automorphisms of `U / F` that extend to `L`. Neither normality of `Ω / F`
nor finiteness of `L / F` is required. -/
theorem natCard_algEquiv_eq_mul_of_le (h : U ≤ L) :
    Nat.card (L ≃ₐ[F] L) =
      Nat.card (extendScalars h ≃ₐ[U] extendScalars h) *
        Nat.card {τ : U ≃ₐ[F] U // ∃ σ : L ≃ₐ[F] L, ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = τ x} := by
  rw [← Subgroup.card_ker_mul_card_range (inclusion h).restrictNormalHom,
    Nat.card_congr (extendScalarsAlgEquivMulEquivKer h).toEquiv,
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_range_restrictNormalHom_inclusion_iff h)]

/-- The order of the `U`-automorphism group of `extendScalars h` divides the order of
`L ≃ₐ[F] L`. -/
theorem natCard_extendScalars_algEquiv_dvd (h : U ≤ L) :
    Nat.card (extendScalars h ≃ₐ[U] extendScalars h) ∣ Nat.card (L ≃ₐ[F] L) :=
  ⟨_, natCard_algEquiv_eq_mul_of_le h⟩

/-- The number of `F`-automorphisms of `U` extending to `L` divides `#Aut_F(U)`. -/
theorem natCard_subtype_extend_dvd_natCard_algEquiv (h : U ≤ L) :
    Nat.card {τ : U ≃ₐ[F] U // ∃ σ : L ≃ₐ[F] L, ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = τ x} ∣
      Nat.card (U ≃ₐ[F] U) := by
  rw [← Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦
    mem_range_restrictNormalHom_inclusion_iff h)]
  exact Subgroup.card_subgroup_dvd_card _

end AutomorphismRestriction

/-! ### Transporting intermediate fields over a normal base -/

section MapNormalBase

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
  {U : IntermediateField F Ω} [Normal F U]

/-- Push an intermediate field `E` of `Ω / U` forward along an `F`-algebra endomorphism
`σ : Ω →ₐ[F] Ω`. Since `U` is normal over `F`, the image `(E.restrictScalars F).map σ` still
contains `U`, so extending scalars returns an intermediate field over `U`. -/
def mapNormalBase (σ : Ω →ₐ[F] Ω) (E : IntermediateField U Ω) : IntermediateField U Ω :=
  extendScalars (le_map_of_normal (le_restrictScalars E) σ)

/-- `mapNormalBase σ E` is `extendScalars` of `(E.restrictScalars F).map σ`. -/
theorem mapNormalBase_def (σ : Ω →ₐ[F] Ω) (E : IntermediateField U Ω) :
    mapNormalBase σ E = extendScalars (le_map_of_normal (le_restrictScalars E) σ) :=
  (rfl)

/-- Restricting scalars of `mapNormalBase σ E` to `F` gives `(E.restrictScalars F).map σ`. -/
@[simp]
theorem mapNormalBase_restrictScalars (σ : Ω →ₐ[F] Ω) (E : IntermediateField U Ω) :
    (mapNormalBase σ E).restrictScalars F = (E.restrictScalars F).map σ :=
  extendScalars_restrictScalars _

@[simp]
theorem mem_mapNormalBase {σ : Ω →ₐ[F] Ω} {E : IntermediateField U Ω} {x : Ω} :
    x ∈ mapNormalBase σ E ↔ ∃ y ∈ E, σ y = x := by
  rw [← mem_restrictScalars F, mapNormalBase_restrictScalars, mem_map]
  rfl

@[simp]
theorem mapNormalBase_id (E : IntermediateField U Ω) :
    mapNormalBase (AlgHom.id F Ω) E = E :=
  restrictScalars_injective F (by rw [mapNormalBase_restrictScalars, map_id])

@[simp]
theorem mapNormalBase_comp (σ₁ σ₂ : Ω →ₐ[F] Ω) (E : IntermediateField U Ω) :
    mapNormalBase (σ₁.comp σ₂) E = mapNormalBase σ₁ (mapNormalBase σ₂ E) :=
  restrictScalars_injective F (by simp [map_map])

@[simp]
theorem mapNormalBase_extendScalars {L : IntermediateField F Ω} (h : U ≤ L) (σ : Ω →ₐ[F] Ω) :
    mapNormalBase σ (extendScalars h) = extendScalars (le_map_of_normal h σ) :=
  restrictScalars_injective F (by simp)

/-- For an automorphism `σ : Ω ≃ₐ[F] Ω`, an element `x` lies in `mapNormalBase σ E` if and only if
`σ.symm x` lies in `E`. -/
theorem mem_mapNormalBase_iff_symm_mem (σ : Ω ≃ₐ[F] Ω) {E : IntermediateField U Ω} {x : Ω} :
    x ∈ mapNormalBase (σ : Ω →ₐ[F] Ω) E ↔ σ.symm x ∈ E := by
  rw [mem_mapNormalBase]
  exact ⟨fun ⟨y, hy, hxy⟩ ↦ hxy ▸ (σ.symm_apply_apply y).symm ▸ hy,
    fun hx ↦ ⟨σ.symm x, hx, σ.apply_symm_apply x⟩⟩

/-- A `U`-algebra isomorphism `e : E₁ ≃ₐ[U] E₂` transports along any `σ : Ω ≃ₐ[F] Ω` to a
`U`-algebra isomorphism `mapNormalBase σ E₁ ≃ₐ[U] mapNormalBase σ E₂`, sending `x` to
`σ (e (σ.symm x))`. Although `σ` permutes `U`, conjugation by `σ` fixes every element of `U` once
`e` fixes `σ.symm u ∈ U`. -/
def mapNormalBaseAlgEquiv (σ : Ω ≃ₐ[F] Ω) {E₁ E₂ : IntermediateField U Ω} (e : E₁ ≃ₐ[U] E₂) :
    mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ≃ₐ[U] mapNormalBase (σ : Ω →ₐ[F] Ω) E₂ where
  toFun x := ⟨σ (e ⟨σ.symm x.1, (mem_mapNormalBase_iff_symm_mem σ).1 x.2⟩),
    (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩
  invFun x := ⟨σ (e.symm ⟨σ.symm x.1, (mem_mapNormalBase_iff_symm_mem σ).1 x.2⟩),
    (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext <| by
    have hmul : (⟨σ.symm (x * y).1,
        (mem_mapNormalBase_iff_symm_mem σ).1 (x * y).2⟩ : E₁) =
      ⟨σ.symm x.1, (mem_mapNormalBase_iff_symm_mem σ).1 x.2⟩ *
        ⟨σ.symm y.1, (mem_mapNormalBase_iff_symm_mem σ).1 y.2⟩ :=
      Subtype.ext (map_mul σ.symm x.1 y.1)
    exact (congrArg (fun z : E₁ ↦ σ (e z : Ω)) hmul).trans
      ((congrArg (fun w : E₂ ↦ σ (w : Ω)) (map_mul e _ _)).trans (map_mul σ _ _))
  map_add' x y := Subtype.ext <| by
    have hadd : (⟨σ.symm (x + y).1,
        (mem_mapNormalBase_iff_symm_mem σ).1 (x + y).2⟩ : E₁) =
      ⟨σ.symm x.1, (mem_mapNormalBase_iff_symm_mem σ).1 x.2⟩ +
        ⟨σ.symm y.1, (mem_mapNormalBase_iff_symm_mem σ).1 y.2⟩ :=
      Subtype.ext (map_add σ.symm x.1 y.1)
    exact (congrArg (fun z : E₁ ↦ σ (e z : Ω)) hadd).trans
      ((congrArg (fun w : E₂ ↦ σ (w : Ω)) (map_add e _ _)).trans (map_add σ _ _))
  commutes' u := Subtype.ext (by
    let u' : U := AlgEquiv.restrictNormalHom U σ.symm u
    have hu' : (⟨σ.symm (u : Ω),
        (mem_mapNormalBase_iff_symm_mem σ).1 ((mapNormalBase _ E₁).algebraMap_mem u)⟩ : E₁) =
        algebraMap U E₁ u' :=
      Subtype.ext (AlgEquiv.restrictNormalHom_apply U σ.symm u).symm
    have he : (e ⟨σ.symm (u : Ω),
        (mem_mapNormalBase_iff_symm_mem σ).1 ((mapNormalBase _ E₁).algebraMap_mem u)⟩ : Ω) =
        σ.symm (u : Ω) := by
      rw [hu', e.commutes]
      exact AlgEquiv.restrictNormalHom_apply U σ.symm u
    exact (congrArg σ he).trans (σ.apply_symm_apply u))

@[simp]
theorem coe_mapNormalBaseAlgEquiv_apply (σ : Ω ≃ₐ[F] Ω) {E₁ E₂ : IntermediateField U Ω}
    (e : E₁ ≃ₐ[U] E₂) (x : mapNormalBase (σ : Ω →ₐ[F] Ω) E₁) :
    (mapNormalBaseAlgEquiv σ e x : Ω) =
      σ (e ⟨σ.symm x.1, (mem_mapNormalBase_iff_symm_mem σ).1 x.2⟩) :=
  (rfl)

/-- Inverse transport of a `U`-algebra isomorphism
`mapNormalBase σ E₁ ≃ₐ[U] mapNormalBase σ E₂` back to `E₁ ≃ₐ[U] E₂`, sending `x` to
`σ.symm (e' (σ x))`. -/
def ofMapNormalBaseAlgEquiv (σ : Ω ≃ₐ[F] Ω) {E₁ E₂ : IntermediateField U Ω}
    (e' : mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ≃ₐ[U] mapNormalBase (σ : Ω →ₐ[F] Ω) E₂) :
    E₁ ≃ₐ[U] E₂ where
  toFun x := ⟨σ.symm (e' ⟨σ x.1, (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩),
    (mem_mapNormalBase_iff_symm_mem σ).1 (e' _).2⟩
  invFun x := ⟨σ.symm (e'.symm ⟨σ x.1, (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩),
    (mem_mapNormalBase_iff_symm_mem σ).1 (e'.symm _).2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext <| by
    have hmul : (⟨σ (x * y).1,
        (mem_mapNormalBase_iff_symm_mem σ).2 (by simp [mul_mem])⟩ :
        mapNormalBase (σ : Ω →ₐ[F] Ω) E₁) =
      ⟨σ x.1, (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩ *
        ⟨σ y.1, (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩ :=
      Subtype.ext (map_mul σ x.1 y.1)
    exact (congrArg (fun z : mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ↦ σ.symm (e' z : Ω)) hmul).trans
      ((congrArg (fun w : mapNormalBase (σ : Ω →ₐ[F] Ω) E₂ ↦ σ.symm (w : Ω))
        (map_mul e' _ _)).trans (map_mul σ.symm _ _))
  map_add' x y := Subtype.ext <| by
    have hadd : (⟨σ (x + y).1,
        (mem_mapNormalBase_iff_symm_mem σ).2 (by simp [add_mem])⟩ :
        mapNormalBase (σ : Ω →ₐ[F] Ω) E₁) =
      ⟨σ x.1, (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩ +
        ⟨σ y.1, (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩ :=
      Subtype.ext (map_add σ x.1 y.1)
    exact (congrArg (fun z : mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ↦ σ.symm (e' z : Ω)) hadd).trans
      ((congrArg (fun w : mapNormalBase (σ : Ω →ₐ[F] Ω) E₂ ↦ σ.symm (w : Ω))
        (map_add e' _ _)).trans (map_add σ.symm _ _))
  commutes' u := Subtype.ext (by
    let u' : U := AlgEquiv.restrictNormalHom U σ u
    have hu' : (⟨σ (u : Ω),
        (mem_mapNormalBase_iff_symm_mem σ).2 (by simpa using E₁.algebraMap_mem u)⟩ :
        mapNormalBase (σ : Ω →ₐ[F] Ω) E₁) = algebraMap U _ u' :=
      Subtype.ext (AlgEquiv.restrictNormalHom_apply U σ u).symm
    have he' : (e' ⟨σ (u : Ω),
        (mem_mapNormalBase_iff_symm_mem σ).2 (by simpa using E₁.algebraMap_mem u)⟩ : Ω) =
        σ (u : Ω) := by
      rw [hu', e'.commutes]
      exact AlgEquiv.restrictNormalHom_apply U σ u
    exact (congrArg σ.symm he').trans (σ.symm_apply_apply u))

@[simp]
theorem coe_ofMapNormalBaseAlgEquiv_apply (σ : Ω ≃ₐ[F] Ω) {E₁ E₂ : IntermediateField U Ω}
    (e' : mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ≃ₐ[U] mapNormalBase (σ : Ω →ₐ[F] Ω) E₂) (x : E₁) :
    (ofMapNormalBaseAlgEquiv σ e' x : Ω) =
      σ.symm (e' ⟨σ x.1, (mem_mapNormalBase_iff_symm_mem σ).2 (by simp)⟩) :=
  (rfl)

/-- Conjugation by `σ : Ω ≃ₐ[F] Ω` gives a group isomorphism between the `U`-automorphism groups of
`E` and of `mapNormalBase σ E`. -/
def mapNormalBaseAutMulEquiv (σ : Ω ≃ₐ[F] Ω) (E : IntermediateField U Ω) :
    (E ≃ₐ[U] E) ≃*
      (mapNormalBase (σ : Ω →ₐ[F] Ω) E ≃ₐ[U] mapNormalBase (σ : Ω →ₐ[F] Ω) E) where
  toFun e := mapNormalBaseAlgEquiv σ e
  invFun e' := ofMapNormalBaseAlgEquiv σ e'
  left_inv e := AlgEquiv.ext fun x ↦ Subtype.ext <| by
    simp only [coe_ofMapNormalBaseAlgEquiv_apply, coe_mapNormalBaseAlgEquiv_apply,
      σ.symm_apply_apply]
  right_inv e' := AlgEquiv.ext fun x ↦ Subtype.ext <| by
    simp only [coe_mapNormalBaseAlgEquiv_apply, coe_ofMapNormalBaseAlgEquiv_apply,
      σ.apply_symm_apply]
  map_mul' e₁ e₂ := AlgEquiv.ext fun x ↦ Subtype.ext <| by
    simp only [AlgEquiv.mul_apply, coe_mapNormalBaseAlgEquiv_apply]
    exact congrArg (fun z : E ↦ σ (e₁ z : Ω)) (Subtype.ext (σ.symm_apply_apply _).symm)

/-- Transporting an intermediate field of `Ω / U` along `σ : Ω ≃ₐ[F] Ω` preserves the cardinality of
its `U`-automorphism group. -/
@[simp]
theorem natCard_mapNormalBase_algEquiv (σ : Ω ≃ₐ[F] Ω) (E : IntermediateField U Ω) :
    Nat.card (mapNormalBase (σ : Ω →ₐ[F] Ω) E ≃ₐ[U] mapNormalBase (σ : Ω →ₐ[F] Ω) E) =
      Nat.card (E ≃ₐ[U] E) :=
  Nat.card_congr (mapNormalBaseAutMulEquiv σ E).symm.toEquiv

/-- Two automorphisms `σ₁, σ₂ : Ω ≃ₐ[F] Ω` with the same restriction to `U` transport `E` to
`U`-isomorphic intermediate fields: `σ₂ * σ₁⁻¹` fixes `U` pointwise and carries `σ₁(E)` onto
`σ₂(E)`. -/
def mapNormalBaseAlgEquivOfRestrictNormalEq {σ₁ σ₂ : Ω ≃ₐ[F] Ω}
    (hσ : AlgEquiv.restrictNormalHom U σ₁ = AlgEquiv.restrictNormalHom U σ₂)
    (E : IntermediateField U Ω) :
    mapNormalBase (σ₁ : Ω →ₐ[F] Ω) E ≃ₐ[U] mapNormalBase (σ₂ : Ω →ₐ[F] Ω) E where
  toFun x := ⟨σ₂ (σ₁.symm x.1),
    (mem_mapNormalBase_iff_symm_mem σ₂).2 (by
      simpa using (mem_mapNormalBase_iff_symm_mem σ₁).1 x.2)⟩
  invFun x := ⟨σ₁ (σ₂.symm x.1),
    (mem_mapNormalBase_iff_symm_mem σ₁).2 (by
      simpa using (mem_mapNormalBase_iff_symm_mem σ₂).1 x.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
  commutes' u := Subtype.ext (by
    have hker : σ₂ * σ₁⁻¹ ∈ (AlgEquiv.restrictNormalHom (K₁ := Ω) U).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    have hfix : (σ₂ * σ₁⁻¹) (algebraMap U Ω u) = algebraMap U Ω u :=
      (AlgEquiv.restrictNormal_eq_one_iff_algebraMap F U Ω (σ₂ * σ₁⁻¹)).1 hker u
    exact hfix)

@[simp]
theorem coe_mapNormalBaseAlgEquivOfRestrictNormalEq_apply {σ₁ σ₂ : Ω ≃ₐ[F] Ω}
    (hσ : AlgEquiv.restrictNormalHom U σ₁ = AlgEquiv.restrictNormalHom U σ₂)
    (E : IntermediateField U Ω) (x : mapNormalBase (σ₁ : Ω →ₐ[F] Ω) E) :
    (mapNormalBaseAlgEquivOfRestrictNormalEq hσ E x : Ω) = σ₂ (σ₁.symm x.1) :=
  (rfl)

/-- A `U`-isomorphism `mapNormalBase σ E₁ ≃ₐ[U] E₂` induces an `F`-isomorphism
`E₁.restrictScalars F ≃ₐ[F] E₂.restrictScalars F`. -/
def restrictScalarsAlgEquivOfMapNormalBase (σ : Ω ≃ₐ[F] Ω) {E₁ E₂ : IntermediateField U Ω}
    (e : mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ≃ₐ[U] E₂) :
    E₁.restrictScalars F ≃ₐ[F] E₂.restrictScalars F :=
  (intermediateFieldMap σ (E₁.restrictScalars F)).trans
    ((equivOfEq (mapNormalBase_restrictScalars (σ : Ω →ₐ[F] Ω) E₁).symm).trans
      ((restrictScalarsAlgEquiv F _).trans
        ((e.restrictScalars F).trans (restrictScalarsAlgEquiv F E₂).symm)))

@[simp]
theorem coe_restrictScalarsAlgEquivOfMapNormalBase_apply (σ : Ω ≃ₐ[F] Ω)
    {E₁ E₂ : IntermediateField U Ω} (e : mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ≃ₐ[U] E₂)
    (x : E₁.restrictScalars F) :
    (restrictScalarsAlgEquivOfMapNormalBase σ e x : Ω) =
      e ⟨σ x.1, mem_mapNormalBase.2 ⟨x.1, x.2, rfl⟩⟩ := by
  simp only [restrictScalarsAlgEquivOfMapNormalBase, AlgEquiv.trans_apply,
    coe_restrictScalarsAlgEquiv_symm_apply, AlgEquiv.restrictScalars_apply]
  congr 2
  apply Subtype.ext
  simp [equivOfEq_apply, intermediateFieldMap_apply_coe]

section NormalAmbient

variable [Normal F Ω]

/-- When `Ω / F` is normal, any `F`-isomorphism between `E₁.restrictScalars F` and
`E₂.restrictScalars F` lifts to an automorphism `σ : Ω ≃ₐ[F] Ω` carrying `E₁` onto `E₂` via
`mapNormalBase`. -/
theorem exists_mapNormalBase_eq_of_algEquiv {E₁ E₂ : IntermediateField U Ω}
    (e : E₁.restrictScalars F ≃ₐ[F] E₂.restrictScalars F) :
    ∃ σ : Ω ≃ₐ[F] Ω, mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ = E₂ := by
  refine ⟨e.liftNormal Ω, restrictScalars_injective F ?_⟩
  rw [mapNormalBase_restrictScalars]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hcomm := e.liftNormal_commutes Ω ⟨x, hx⟩
    exact hcomm.symm ▸ (e ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(e.symm ⟨y, hy⟩ : Ω), (e.symm ⟨y, hy⟩).2, ?_⟩
    exact (e.liftNormal_commutes Ω (e.symm ⟨y, hy⟩)).trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))

/-- **Classification of `F`-isomorphism over a normal base**: when `Ω / F` is normal, two
intermediate fields of `Ω / U` become `F`-isomorphic upon restricting scalars if and only if some
`σ : Ω ≃ₐ[F] Ω` maps one to an intermediate field `U`-isomorphic to the other. -/
theorem nonempty_restrictScalars_algEquiv_iff {E₁ E₂ : IntermediateField U Ω} :
    Nonempty (E₁.restrictScalars F ≃ₐ[F] E₂.restrictScalars F) ↔
      ∃ σ : Ω ≃ₐ[F] Ω, Nonempty (mapNormalBase (σ : Ω →ₐ[F] Ω) E₁ ≃ₐ[U] E₂) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨σ, ⟨e⟩⟩ ↦ ⟨restrictScalarsAlgEquivOfMapNormalBase σ e⟩⟩
  obtain ⟨σ, rfl⟩ := exists_mapNormalBase_eq_of_algEquiv e
  exact ⟨σ, ⟨AlgEquiv.refl⟩⟩

/-- **Stabilizer characterization**: when `Ω / F` is normal and `h : U ≤ L`, an automorphism
`σ : Ω ≃ₐ[F] Ω` stabilizes `extendScalars h` up to `U`-isomorphism if and only if its restriction
to `U` lies in the range of `(inclusion h).restrictNormalHom`. -/
theorem nonempty_mapNormalBase_algEquiv_iff_mem_range {L : IntermediateField F Ω} (h : U ≤ L)
    (σ : Ω ≃ₐ[F] Ω) :
    Nonempty (mapNormalBase (σ : Ω →ₐ[F] Ω) (extendScalars h) ≃ₐ[U] extendScalars h) ↔
      AlgEquiv.restrictNormalHom U σ ∈ (inclusion h).restrictNormalHom.range := by
  rw [mem_range_restrictNormalHom_inclusion_iff]
  constructor
  · rintro ⟨e⟩
    let γ₀ := restrictScalarsAlgEquivOfMapNormalBase σ e
    let γ : L ≃ₐ[F] L :=
      (equivOfEq (extendScalars_restrictScalars h).symm).trans
        (γ₀.trans (equivOfEq (extendScalars_restrictScalars h)))
    have hcoe_eq {S T : IntermediateField F Ω} (hST : S = T) (z : S) :
        (equivOfEq hST z : Ω) = z.1 := by
      cases hST; rfl
    refine ⟨γ, fun u ↦ ?_⟩
    have hγu : (γ ⟨u.1, h u.2⟩ : Ω) =
        e ⟨σ u.1, mem_mapNormalBase.2 ⟨u.1, h u.2, rfl⟩⟩ := by
      dsimp only [γ, γ₀]
      rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, hcoe_eq,
        coe_restrictScalarsAlgEquivOfMapNormalBase_apply]
      exact congrArg (fun z : mapNormalBase (σ : Ω →ₐ[F] Ω) (extendScalars h) ↦ (e z : Ω))
        (Subtype.ext (congrArg σ (hcoe_eq _ _)))
    have hu : (⟨σ u.1, mem_mapNormalBase.2 ⟨u.1, h u.2, rfl⟩⟩ :
        mapNormalBase (σ : Ω →ₐ[F] Ω) (extendScalars h)) =
        algebraMap U _ (AlgEquiv.restrictNormalHom U σ u) :=
      Subtype.ext (AlgEquiv.restrictNormalHom_apply U σ u).symm
    rw [hγu, hu, e.commutes]
    rfl
  · rintro ⟨γ, hγ⟩
    let γ' : (extendScalars h).restrictScalars F ≃ₐ[F] (extendScalars h).restrictScalars F :=
      (equivOfEq (extendScalars_restrictScalars h)).trans
        (γ.trans (equivOfEq (extendScalars_restrictScalars h).symm))
    let σ' : Ω ≃ₐ[F] Ω := γ'.liftNormal Ω
    have hmap : mapNormalBase (σ' : Ω →ₐ[F] Ω) (extendScalars h) = extendScalars h := by
      apply restrictScalars_injective F
      rw [mapNormalBase_restrictScalars]
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (γ'.liftNormal_commutes Ω ⟨x, hx⟩).symm ▸ (γ' ⟨x, hx⟩).2
      · intro y hy
        refine ⟨(γ'.symm ⟨y, hy⟩ : Ω), (γ'.symm ⟨y, hy⟩).2, ?_⟩
        exact (γ'.liftNormal_commutes Ω (γ'.symm ⟨y, hy⟩)).trans
          (congrArg Subtype.val (γ'.apply_symm_apply ⟨y, hy⟩))
    have hrest : AlgEquiv.restrictNormalHom U σ = AlgEquiv.restrictNormalHom U σ' := by
      ext u
      rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
      have hcomm : σ' u.1 = (γ ⟨u.1, h u.2⟩ : Ω) := γ'.liftNormal_commutes Ω ⟨u.1, h u.2⟩
      exact (AlgEquiv.restrictNormalHom_apply U σ u).symm.trans ((hγ u).symm.trans hcomm.symm)
    exact ⟨(mapNormalBaseAlgEquivOfRestrictNormalEq hrest (extendScalars h)).trans
      (equivOfEq hmap)⟩

end NormalAmbient

end MapNormalBase

/-! ### Sets of isomorphism-class representatives and `Gal(U / F)` orbit sums -/

section ClassSums

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- Every set `S` of intermediate fields of `Ω / F` admits a subset `R ⊆ S` containing a unique
representative of each `F`-isomorphism class present in `S`. -/
theorem exists_subset_forall_existsUnique_nonempty_algEquiv (S : Set (IntermediateField F Ω)) :
    ∃ R ⊆ S, ∀ L ∈ S, ∃! M, M ∈ R ∧ Nonempty (L ≃ₐ[F] M) := by
  let s : Setoid S :=
    { r := fun L M ↦ Nonempty (L.1 ≃ₐ[F] M.1)
      iseqv := ⟨fun _ ↦ ⟨.refl⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩ }
  refine ⟨Set.range fun c : Quotient s ↦ (c.out : IntermediateField F Ω), ?_,
    fun L hL ↦ ⟨(Quotient.mk s ⟨L, hL⟩).out,
      ⟨⟨_, rfl⟩, Setoid.symm' s (Quotient.mk_out (s := s) ⟨L, hL⟩)⟩, ?_⟩⟩
  · rintro _ ⟨c, rfl⟩
    exact c.out.2
  · rintro _ ⟨⟨c, rfl⟩, he⟩
    have hc : c = Quotient.mk s ⟨L, hL⟩ := by
      rw [← Quotient.out_eq c]
      exact Quotient.sound (Setoid.symm' s he)
    rw [hc]

variable {U : IntermediateField F Ω} [Normal F U]

/-- If `S : Set (IntermediateField U Ω)` has restriction image `T` closed under `map σ`, then `S`
is closed under `mapNormalBase σ`. -/
theorem mapNormalBase_mem_of_image_restrictScalars {S : Set (IntermediateField U Ω)}
    {T : Set (IntermediateField F Ω)} (hST : IntermediateField.restrictScalars F '' S = T)
    (hT : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ L ∈ T, L.map (σ : Ω →ₐ[F] Ω) ∈ T)
    (σ : Ω ≃ₐ[F] Ω) {E : IntermediateField U Ω} (hE : E ∈ S) :
    mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S := by
  have hmem : (mapNormalBase (σ : Ω →ₐ[F] Ω) E).restrictScalars F ∈
      IntermediateField.restrictScalars F '' S := by
    rw [hST, mapNormalBase_restrictScalars]
    exact hT σ (E.restrictScalars F) (hST ▸ ⟨E, hE, rfl⟩)
  obtain ⟨E', hE', hEq⟩ := hmem
  exact restrictScalars_injective F hEq ▸ hE'

variable [Normal F Ω]

/-- The action of `U ≃ₐ[F] U` on a set `R` of `U`-isomorphism class representatives of a
`mapNormalBase`-invariant family `S : Set (IntermediateField U Ω)`. For `τ : U ≃ₐ[F] U` and
`M : R`, choose a lift `σ : Ω ≃ₐ[F] Ω` of `τ` and take the unique representative in `R`
`U`-isomorphic to `mapNormalBase σ M.1`. -/
@[instance_reducible]
private def representativeSetMulAction {S R : Set (IntermediateField U Ω)}
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M)) :
    MulAction (U ≃ₐ[F] U) R where
  smul τ M :=
    let σ := (AlgEquiv.restrictNormalHom_surjective Ω τ).choose
    ⟨(hR (mapNormalBase (σ : Ω →ₐ[F] Ω) M.1) (hS σ M.1 (hRS M.2))).choose,
      (hR (mapNormalBase (σ : Ω →ₐ[F] Ω) M.1) (hS σ M.1 (hRS M.2))).choose_spec.1.1⟩
  one_smul M := by
    let σ := (AlgEquiv.restrictNormalHom_surjective Ω (1 : U ≃ₐ[F] U)).choose
    have hσ : AlgEquiv.restrictNormalHom U σ = AlgEquiv.restrictNormalHom U (1 : Ω ≃ₐ[F] Ω) := by
      rw [(AlgEquiv.restrictNormalHom_surjective Ω (1 : U ≃ₐ[F] U)).choose_spec, map_one]
    have he : Nonempty (mapNormalBase (σ : Ω →ₐ[F] Ω) M.1 ≃ₐ[U] M.1) :=
      ⟨(mapNormalBaseAlgEquivOfRestrictNormalEq hσ M.1).trans (equivOfEq (mapNormalBase_id M.1))⟩
    have huniq := (hR (mapNormalBase (σ : Ω →ₐ[F] Ω) M.1) (hS σ M.1 (hRS M.2))).choose_spec
    exact Subtype.ext (huniq.2 M.1 ⟨M.2, he⟩).symm
  mul_smul τ₁ τ₂ M := by
    let σ₁₂ := (AlgEquiv.restrictNormalHom_surjective Ω (τ₁ * τ₂)).choose
    let σ₁ := (AlgEquiv.restrictNormalHom_surjective Ω τ₁).choose
    let σ₂ := (AlgEquiv.restrictNormalHom_surjective Ω τ₂).choose
    let h₂ := hR (mapNormalBase (σ₂ : Ω →ₐ[F] Ω) M.1) (hS σ₂ M.1 (hRS M.2))
    let M₂ : R := ⟨h₂.choose, h₂.choose_spec.1.1⟩
    let h₁ := hR (mapNormalBase (σ₁ : Ω →ₐ[F] Ω) M₂.1) (hS σ₁ M₂.1 (hRS M₂.2))
    let M₁ : R := ⟨h₁.choose, h₁.choose_spec.1.1⟩
    have hσ : AlgEquiv.restrictNormalHom U σ₁₂ = AlgEquiv.restrictNormalHom U (σ₁ * σ₂) := by
      rw [(AlgEquiv.restrictNormalHom_surjective Ω (τ₁ * τ₂)).choose_spec, map_mul,
        (AlgEquiv.restrictNormalHom_surjective Ω τ₁).choose_spec,
        (AlgEquiv.restrictNormalHom_surjective Ω τ₂).choose_spec]
    obtain ⟨e₂⟩ := h₂.choose_spec.1.2
    obtain ⟨e₁⟩ := h₁.choose_spec.1.2
    have he₁₂ : Nonempty (mapNormalBase (σ₁₂ : Ω →ₐ[F] Ω) M.1 ≃ₐ[U] M₁.1) :=
      ⟨(mapNormalBaseAlgEquivOfRestrictNormalEq hσ M.1).trans
        ((equivOfEq (mapNormalBase_comp (σ₁ : Ω →ₐ[F] Ω) (σ₂ : Ω →ₐ[F] Ω) M.1)).trans
          ((mapNormalBaseAlgEquiv σ₁ e₂).trans e₁))⟩
    have huniq := (hR (mapNormalBase (σ₁₂ : Ω →ₐ[F] Ω) M.1) (hS σ₁₂ M.1 (hRS M.2))).choose_spec
    exact Subtype.ext (huniq.2 M₁.1 ⟨M₁.2, he₁₂⟩).symm

/-- Characterization of `τ • M = M'` in `representativeSetMulAction`: for any lift `σ : Ω ≃ₐ[F] Ω`
of `τ`, `τ • M = M'` holds if and only if `mapNormalBase σ M.1` is `U`-isomorphic to `M'.1`. -/
private theorem representativeSetMulAction_smul_eq_iff {S R : Set (IntermediateField U Ω)}
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M))
    {τ : U ≃ₐ[F] U} {σ : Ω ≃ₐ[F] Ω} (hσ : AlgEquiv.restrictNormalHom U σ = τ)
    (M M' : R) :
    (letI := representativeSetMulAction hS hRS hR; τ • M = M') ↔
      Nonempty (mapNormalBase (σ : Ω →ₐ[F] Ω) M.1 ≃ₐ[U] M'.1) := by
  let _ := representativeSetMulAction hS hRS hR
  let σ₀ := (AlgEquiv.restrictNormalHom_surjective Ω τ).choose
  have hσ₀ : AlgEquiv.restrictNormalHom U σ₀ = AlgEquiv.restrictNormalHom U σ :=
    (AlgEquiv.restrictNormalHom_surjective Ω τ).choose_spec.trans hσ.symm
  let hex := hR (mapNormalBase (σ₀ : Ω →ₐ[F] Ω) M.1) (hS σ₀ M.1 (hRS M.2))
  constructor
  · intro hEq
    obtain ⟨e₀⟩ := hex.choose_spec.1.2
    have hval : hex.choose = M'.1 := congrArg Subtype.val hEq
    exact ⟨(mapNormalBaseAlgEquivOfRestrictNormalEq hσ₀ M.1).symm.trans
      (e₀.trans (equivOfEq hval))⟩
  · rintro ⟨e⟩
    have he₀ : Nonempty (mapNormalBase (σ₀ : Ω →ₐ[F] Ω) M.1 ≃ₐ[U] M'.1) :=
      ⟨(mapNormalBaseAlgEquivOfRestrictNormalEq hσ₀ M.1).trans e⟩
    exact Subtype.ext (hex.choose_spec.2 M'.1 ⟨M'.2, he₀⟩).symm

/-- Two representatives in `R` lie in the same `Gal(U / F)`-orbit if and only if their scalar
restrictions to `F` are `F`-isomorphic. -/
private theorem representativeSetMulAction_mem_orbit_iff {S R : Set (IntermediateField U Ω)}
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M))
    (M M' : R) :
    (letI := representativeSetMulAction hS hRS hR; M' ∈ MulAction.orbit (U ≃ₐ[F] U) M) ↔
      Nonempty (M.1.restrictScalars F ≃ₐ[F] M'.1.restrictScalars F) := by
  let _ := representativeSetMulAction hS hRS hR
  rw [MulAction.mem_orbit_iff, nonempty_restrictScalars_algEquiv_iff]
  constructor
  · rintro ⟨τ, hτ⟩
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
    exact ⟨σ, (representativeSetMulAction_smul_eq_iff hS hRS hR hσ M M').1 hτ⟩
  · rintro ⟨σ, he⟩
    exact ⟨AlgEquiv.restrictNormalHom U σ,
      (representativeSetMulAction_smul_eq_iff hS hRS hR rfl M M').2 he⟩

/-- The stabilizer of `M : R` in `U ≃ₐ[F] U` is the range of restriction from
`M.1.restrictScalars F`. -/
private theorem representativeSetMulAction_stabilizer_eq {S R : Set (IntermediateField U Ω)}
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M))
    (M : R) :
    (letI := representativeSetMulAction hS hRS hR; MulAction.stabilizer (U ≃ₐ[F] U) M) =
      (inclusion (le_restrictScalars M.1)).restrictNormalHom.range := by
  let _ := representativeSetMulAction hS hRS hR
  ext τ
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
  rw [MulAction.mem_stabilizer_iff, representativeSetMulAction_smul_eq_iff hS hRS hR hσ M M, ← hσ]
  have hExt : extendScalars (le_restrictScalars M.1) = M.1 :=
    extendScalars_of_restrictScalars M.1
  rw [← nonempty_mapNormalBase_algEquiv_iff_mem_range (le_restrictScalars M.1) σ, hExt]

/-- **Orbit count on `U`-isomorphism classes**: for a `mapNormalBase`-invariant family
`S : Set (IntermediateField U Ω)` with representative set `R`, the number of `U`-classes in `R`
whose scalar restriction to `F` is `F`-isomorphic to `M.restrictScalars F`, multiplied by the
number of automorphisms of `U / F` extending to `M.restrictScalars F`, equals `#Aut_F(U)`. -/
theorem ncard_isomorphic_restrictScalars_mul_natCard {S R : Set (IntermediateField U Ω)}
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M))
    {M : IntermediateField U Ω} (hM : M ∈ R) :
    {M' ∈ R | Nonempty (M.restrictScalars F ≃ₐ[F] M'.restrictScalars F)}.ncard *
      Nat.card {τ : U ≃ₐ[F] U // ∃ σ : M.restrictScalars F ≃ₐ[F] M.restrictScalars F,
        ∀ x : U, (σ ⟨x.1, le_restrictScalars M x.2⟩ : Ω) = τ x} =
      Nat.card (U ≃ₐ[F] U) := by
  let _ := representativeSetMulAction hS hRS hR
  let m : R := ⟨M, hM⟩
  have horb : Nat.card (MulAction.orbit (U ≃ₐ[F] U) m) =
      {M' ∈ R | Nonempty (M.restrictScalars F ≃ₐ[F] M'.restrictScalars F)}.ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun x := ⟨x.1.1, x.1.2,
          (representativeSetMulAction_mem_orbit_iff hS hRS hR m x.1).1 x.2⟩
        invFun y := ⟨⟨y.1, y.2.1⟩,
          (representativeSetMulAction_mem_orbit_iff hS hRS hR m ⟨y.1, y.2.1⟩).2 y.2.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
  have hstab : Nat.card (MulAction.stabilizer (U ≃ₐ[F] U) m) =
      Nat.card {τ : U ≃ₐ[F] U // ∃ σ : M.restrictScalars F ≃ₐ[F] M.restrictScalars F,
        ∀ x : U, (σ ⟨x.1, le_restrictScalars M x.2⟩ : Ω) = τ x} := by
    rw [representativeSetMulAction_stabilizer_eq hS hRS hR m]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦
      mem_range_restrictNormalHom_inclusion_iff (le_restrictScalars M))
  rw [← horb, ← hstab, ← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (U ≃ₐ[F] U) m)

/-- **Orbit count on `U`-isomorphism classes for finite Galois `U / F`**: the number of
`U`-classes in `R` that become `F`-isomorphic to `M.restrictScalars F`, multiplied by the size of
the extending subgroup in `Gal(U / F)`, equals `[U : F]`. -/
theorem ncard_isomorphic_restrictScalars_mul_natCard_eq_finrank {S R : Set (IntermediateField U Ω)}
    [FiniteDimensional F U] [IsGalois F U]
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M))
    {M : IntermediateField U Ω} (hM : M ∈ R) :
    {M' ∈ R | Nonempty (M.restrictScalars F ≃ₐ[F] M'.restrictScalars F)}.ncard *
      Nat.card {τ : U ≃ₐ[F] U // ∃ σ : M.restrictScalars F ≃ₐ[F] M.restrictScalars F,
        ∀ x : U, (σ ⟨x.1, le_restrictScalars M x.2⟩ : Ω) = τ x} =
      Module.finrank F U :=
  (ncard_isomorphic_restrictScalars_mul_natCard hS hRS hR hM).trans
    (IsGalois.card_aut_eq_finrank F U)

/-- **Weighted `1 / #Aut` class-sum reduction over a normal base**: let `S` be a
`mapNormalBase`-invariant family of intermediate fields of `Ω / U` with `U`-isomorphism
representative set `R`, and let `R_F` be an `F`-isomorphism representative set for the scalar
restrictions `T = restrictScalars F '' S`. For any weight `w : IntermediateField F Ω → ℝ≥0∞`
constant on `F`-isomorphism classes, summing `w(N) / #Aut_F(N)` over `N ∈ R_F` equals
`(#Aut_F(U))⁻¹` times the sum of `w(M.restrictScalars F) / #Aut_U(M)` over `M ∈ R`. -/
theorem tsum_div_natCard_algEquiv_eq_inv_natCard_mul_tsum
    {S R : Set (IntermediateField U Ω)} {T R_F : Set (IntermediateField F Ω)}
    [Finite (U ≃ₐ[F] U)]
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M))
    (hST : IntermediateField.restrictScalars F '' S = T)
    (hR_FT : R_F ⊆ T) (hR_F : ∀ L ∈ T, ∃! N, N ∈ R_F ∧ Nonempty (L ≃ₐ[F] N))
    (w : IntermediateField F Ω → ℝ≥0∞)
    (hw : ∀ {L₁ L₂ : IntermediateField F Ω}, (L₁ ≃ₐ[F] L₂) → w L₁ = w L₂) :
    ∑' N : R_F, w N.1 / (Nat.card (N.1 ≃ₐ[F] N.1) : ℝ≥0∞) =
      (Nat.card (U ≃ₐ[F] U) : ℝ≥0∞)⁻¹ *
        ∑' M : R, w (M.1.restrictScalars F) / (Nat.card (M.1 ≃ₐ[U] M.1) : ℝ≥0∞) := by
  let _ := representativeSetMulAction hS hRS hR
  let f : R → ℝ≥0∞ := fun M ↦ w (M.1.restrictScalars F) / (Nat.card (M.1 ≃ₐ[U] M.1) : ℝ≥0∞)
  have hf : ∀ (τ : U ≃ₐ[F] U) (M : R), f (τ • M) = f M := by
    intro τ M
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
    obtain ⟨e⟩ := (representativeSetMulAction_smul_eq_iff hS hRS hR hσ M (τ • M)).1 rfl
    have heF : M.1.restrictScalars F ≃ₐ[F] (τ • M).1.restrictScalars F :=
      restrictScalarsAlgEquivOfMapNormalBase σ e
    have hcard : Nat.card ((τ • M).1 ≃ₐ[U] (τ • M).1) = Nat.card (M.1 ≃ₐ[U] M.1) :=
      (Nat.card_congr (e.equivCongr e).symm).trans (natCard_mapNormalBase_algEquiv σ M.1)
    simp only [f, hw heF.symm, hcard]
  rw [MulAction.inv_natCard_mul_tsum_eq_tsum_div_natCard_stabilizer f hf]
  -- Identify the `Gal(U / F)`-orbits on `R` with the `F`-isomorphism representatives in `R_F`.
  have hmemT (M : R) : M.1.restrictScalars F ∈ T := hST ▸ ⟨M.1, hRS M.2, rfl⟩
  let toRF (ω : MulAction.orbitRel.Quotient (U ≃ₐ[F] U) R) : R_F :=
    ⟨(hR_F (ω.out.1.restrictScalars F) (hmemT ω.out)).choose,
      (hR_F (ω.out.1.restrictScalars F) (hmemT ω.out)).choose_spec.1.1⟩
  have hbij : Function.Bijective toRF := by
    refine ⟨fun ω₁ ω₂ hEq ↦ ?_, fun N ↦ ?_⟩
    · have hspec₁ := (hR_F (ω₁.out.1.restrictScalars F) (hmemT ω₁.out)).choose_spec.1.2
      have hspec₂ := (hR_F (ω₂.out.1.restrictScalars F) (hmemT ω₂.out)).choose_spec.1.2
      obtain ⟨e₁⟩ := hspec₁
      obtain ⟨e₂⟩ := hspec₂
      have he₁₂ : Nonempty (ω₁.out.1.restrictScalars F ≃ₐ[F] ω₂.out.1.restrictScalars F) :=
        ⟨e₁.trans ((equivOfEq (congrArg Subtype.val hEq)).trans e₂.symm)⟩
      have horb : ω₂.out ∈ MulAction.orbit (U ≃ₐ[F] U) ω₁.out :=
        (representativeSetMulAction_mem_orbit_iff hS hRS hR ω₁.out ω₂.out).2 he₁₂
      rw [← Quotient.out_eq ω₁, ← Quotient.out_eq ω₂]
      exact (Quotient.sound horb).symm
    · obtain ⟨E, hES, hEN⟩ := hST ▸ hR_FT N.2
      obtain ⟨M, ⟨hMR, ⟨eEM⟩⟩, -⟩ := hR E hES
      let ω : MulAction.orbitRel.Quotient (U ≃ₐ[F] U) R := Quotient.mk'' ⟨M, hMR⟩
      refine ⟨ω, Subtype.ext ?_⟩
      have horb : (⟨M, hMR⟩ : R) ∈ MulAction.orbit (U ≃ₐ[F] U) ω.out :=
        MulAction.orbitRel.Quotient.mem_orbit.2 (Quotient.out_eq ω).symm
      obtain ⟨eωM⟩ :=
        (representativeSetMulAction_mem_orbit_iff hS hRS hR ω.out ⟨M, hMR⟩).1 horb
      have heMF : M.restrictScalars F ≃ₐ[F] N.1 :=
        (restrictScalarsAlgEquiv F M).trans
          ((eEM.symm.restrictScalars F).trans
            ((restrictScalarsAlgEquiv F E).symm.trans (equivOfEq hEN)))
      have hspec := (hR_F (ω.out.1.restrictScalars F) (hmemT ω.out)).choose_spec
      exact (hspec.2 N.1 ⟨N.2, ⟨eωM.trans heMF⟩⟩).symm
  let ε := Equiv.ofBijective toRF hbij
  rw [← ε.tsum_eq]
  refine tsum_congr fun ω ↦ ?_
  obtain ⟨eN₀⟩ : Nonempty (ω.out.1.restrictScalars F ≃ₐ[F] (toRF ω).1) :=
    (hR_F (ω.out.1.restrictScalars F) (hmemT ω.out)).choose_spec.1.2
  have heps : (toRF ω).1 = (ε ω).1 := by simp [ε]
  let eN : ω.out.1.restrictScalars F ≃ₐ[F] (ε ω).1 := eN₀.trans (equivOfEq heps)
  have hcardF : Nat.card ((ε ω).1 ≃ₐ[F] (ε ω).1) =
      Nat.card (ω.out.1 ≃ₐ[U] ω.out.1) *
        Nat.card (MulAction.stabilizer (U ≃ₐ[F] U) ω.out) := by
    rw [Nat.card_congr (eN.equivCongr eN).symm,
      natCard_algEquiv_eq_mul_of_le (le_restrictScalars ω.out.1),
      extendScalars_of_restrictScalars,
      representativeSetMulAction_stabilizer_eq hS hRS hR ω.out,
      Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦
        mem_range_restrictNormalHom_inclusion_iff (le_restrictScalars ω.out.1))]
  rw [hw eN.symm, hcardF, Nat.cast_mul]
  simp only [f, div_eq_mul_inv,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)), mul_assoc]

/-- **Weighted `1 / #Aut` class-sum reduction over a finite Galois base `U / F`**: specialization
of `tsum_div_natCard_algEquiv_eq_inv_natCard_mul_tsum` replacing `#Aut_F(U)` with `[U : F]`. -/
theorem tsum_div_natCard_algEquiv_eq_inv_finrank_mul_tsum
    {S R : Set (IntermediateField U Ω)} {T R_F : Set (IntermediateField F Ω)}
    [FiniteDimensional F U] [IsGalois F U]
    (hS : ∀ (σ : Ω ≃ₐ[F] Ω), ∀ E ∈ S, mapNormalBase (σ : Ω →ₐ[F] Ω) E ∈ S)
    (hRS : R ⊆ S) (hR : ∀ E ∈ S, ∃! M, M ∈ R ∧ Nonempty (E ≃ₐ[U] M))
    (hST : IntermediateField.restrictScalars F '' S = T)
    (hR_FT : R_F ⊆ T) (hR_F : ∀ L ∈ T, ∃! N, N ∈ R_F ∧ Nonempty (L ≃ₐ[F] N))
    (w : IntermediateField F Ω → ℝ≥0∞)
    (hw : ∀ {L₁ L₂ : IntermediateField F Ω}, (L₁ ≃ₐ[F] L₂) → w L₁ = w L₂) :
    ∑' N : R_F, w N.1 / (Nat.card (N.1 ≃ₐ[F] N.1) : ℝ≥0∞) =
      (Module.finrank F U : ℝ≥0∞)⁻¹ *
        ∑' M : R, w (M.1.restrictScalars F) / (Nat.card (M.1 ≃ₐ[U] M.1) : ℝ≥0∞) := by
  rw [← IsGalois.card_aut_eq_finrank F U]
  exact tsum_div_natCard_algEquiv_eq_inv_natCard_mul_tsum hS hRS hR hST hR_FT hR_F w hw

end ClassSums

end IntermediateField
