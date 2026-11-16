/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.HilbertTower
import TauCeti.NumberTheory.NumberField.Global.Ideles.IdealExtension
import TauCeti.NumberTheory.NumberField.InfinitePlace.NormalClosure
import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import TauCeti.RingTheory.ClassGroup.Extension

/-!
# The Principal Ideal Theorem

Every ideal of a number field `K` becomes principal in the ring of integers of its Hilbert class
field `H = hilbertClassField K` (`isPrincipal_map_hilbertClassField`), equivalently the class-group
extension homomorphism `ClassGroup.extendedHom (𝓞 K) (𝓞 H)` is trivial
(`extendedHom_hilbertClassField_eq_one`).

## Proof outline

The Hilbert class field `H'` of `H` need not be Galois over `K`, so idelic transfer cannot be
applied directly to `H' / K`. Instead we embed `H'` over `H` into `SeparableClosure K` with image
`E`, and form its Galois closure `N = normalClosure K E (SeparableClosure K)`:

1. Both `H / K` and `H' / H` are unramified at every finite and infinite place
   (`formallyUnramified_hilbertClassField`, `isUnramifiedAtInfinitePlaces_hilbertClassField`),
   hence `E / K` is formally unramified on rings of integers and unramified at infinite places.
2. Passing to `N` preserves formal unramifiedness
   (`Algebra.FormallyUnramified.ringOfIntegers_normalClosure`) and unramifiedness at infinite
   places (`IsUnramifiedAtInfinitePlaces.normalClosure`), while producing a finite Galois
   subextension of `SeparableClosure K`, i.e. a class field `classField K V` containing `H`.
3. By `ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`, every idele class of `K`
   extended to `H` is a norm from `classField K V`. Since `H'` embeds into `classField K V` over
   `H`, monotonicity of idele-class norm groups (`range_ideleClassNormMap_le_of_algHom`) places
   that extended idele class inside `N_{H'/H}(C_{H'}) = raySubgroup (Modulus.one H)`
   (`ideleClassExtension_mem_raySubgroup_one_hilbertClassField`).
4. The idelic principalization criterion
   `extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup` and
   `ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal` then conclude that every ideal of `𝓞 K`
   becomes principal in `𝓞 H`, and hence in the ring of integers of any field extension receiving
   `H` over `K` (`isPrincipal_map_of_algHom_hilbertClassField`), including every ray class field
   (`isPrincipal_map_rayClassField`) and the narrow Hilbert class field
   (`isPrincipal_map_narrowHilbertClassField`).

## Main results

* `TauCeti.ClassFieldTheory.formallyUnramified_hilbertClassField`,
  `TauCeti.ClassFieldTheory.formallyUnramified_narrowHilbertClassField`: the rings of integers of
  the Hilbert and narrow Hilbert class fields are formally unramified over `𝓞 K`.
* `TauCeti.ClassFieldTheory.ideleClassExtension_mem_raySubgroup_one_hilbertClassField`: every
  idele class of `K` maps into the trivial-modulus ray subgroup of `hilbertClassField K`.
* `TauCeti.ClassFieldTheory.extendedHom_hilbertClassField_eq_one`,
  `TauCeti.ClassFieldTheory.extendedHom_rayClassField_eq_one`: extension of ideal classes to the
  Hilbert class field (and any ray class field) is trivial.
* `TauCeti.ClassFieldTheory.isPrincipal_map_hilbertClassField`: **The Principal Ideal Theorem** —
  every ideal of `𝓞 K` becomes principal in `𝓞 (hilbertClassField K)`.
* `TauCeti.ClassFieldTheory.isPrincipal_map_of_algHom_hilbertClassField`,
  `TauCeti.ClassFieldTheory.extendedHom_eq_one_of_algHom_hilbertClassField`: principalization in
  any field extension into which `hilbertClassField K` embeds over `K`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7, Theorem 7.6.
-/

public noncomputable section

open IntermediateField IsDedekindDomain NumberField TauCeti.GlobalNumberFields

namespace TauCeti.ClassFieldTheory

section Unramified

variable (K : Type) [Field K] [NumberField K]

/-- The ring of integers of the Hilbert class field of `K` is formally unramified over `𝓞 K`. -/
instance formallyUnramified_hilbertClassField :
    Algebra.FormallyUnramified (𝓞 K) (𝓞 (hilbertClassField K)) := by
  refine Algebra.formallyUnramified_iff_forall.mpr fun ⟨P, hP⟩ ↦ ?_
  rcases eq_or_ne P ⊥ with rfl | hP0
  · exact Algebra.isUnramifiedAt_bot
  · exact isUnramifiedAt_hilbertClassField K ⟨P, hP, hP0⟩

/-- The ring of integers of the narrow Hilbert class field of `K` is formally unramified over
`𝓞 K`. -/
instance formallyUnramified_narrowHilbertClassField :
    Algebra.FormallyUnramified (𝓞 K) (𝓞 (narrowHilbertClassField K)) := by
  refine Algebra.formallyUnramified_iff_forall.mpr fun ⟨P, hP⟩ ↦ ?_
  rcases eq_or_ne P ⊥ with rfl | hP0
  · exact Algebra.isUnramifiedAt_bot
  · exact isUnramifiedAt_narrowHilbertClassField K ⟨P, hP, hP0⟩

end Unramified

section PrincipalIdeal

variable (K : Type) [Field K] [NumberField K]

/-- For any finite unramified extension `E` of `hilbertClassField K` inside `SeparableClosure K`,
its normal closure over `K` is an everywhere-unramified class field `classField K V`. -/
private theorem exists_unramified_classField_eq_normalClosure
    (E : IntermediateField (hilbertClassField K) (SeparableClosure K))
    [FiniteDimensional (hilbertClassField K) E]
    [IsUnramifiedAtInfinitePlaces (hilbertClassField K) E]
    [Algebra.FormallyUnramified (𝓞 (hilbertClassField K)) (𝓞 E)] :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      classField K V = IntermediateField.normalClosure K E (SeparableClosure K) ∧
        IsUnramifiedAtInfinitePlaces K (classField K V) ∧
        Algebra.FormallyUnramified (𝓞 K) (𝓞 (classField K V)) := by
  let H := hilbertClassField K
  have : IsScalarTower K H E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional K E := Module.Finite.trans H E
  have : IsUnramifiedAtInfinitePlaces K E :=
    IsUnramifiedAtInfinitePlaces.trans (k := K) (K := H) (F := E)
  have : Algebra.FormallyUnramified (𝓞 K) (𝓞 E) :=
    Algebra.FormallyUnramified.comp (𝓞 K) (𝓞 H) (𝓞 E)
  let N : IntermediateField K (SeparableClosure K) :=
    IntermediateField.normalClosure K E (SeparableClosure K)
  have : IsGalois K N := {}
  have : Algebra.FormallyUnramified (𝓞 K) (𝓞 N) :=
    Algebra.FormallyUnramified.ringOfIntegers_normalClosure E (SeparableClosure K)
  obtain ⟨V, hV⟩ := (exists_classField_eq_iff N).2 ⟨inferInstance, inferInstance⟩
  exact ⟨V, hV, hV.symm ▸ (inferInstance : IsUnramifiedAtInfinitePlaces K N),
    Algebra.FormallyUnramified.of_equiv
      (RingOfIntegers.mapAlgEquiv (IntermediateField.equivOfEq hV.symm))⟩

/-- **Idelic Principal Ideal Theorem.** Every idele class of `K`, extended to its Hilbert class
field `H`, lies in the trivial-modulus ray subgroup `raySubgroup (Modulus.one H)` — equivalently,
its finite part generates a principal fractional ideal of `𝓞 H`. -/
theorem ideleClassExtension_mem_raySubgroup_one_hilbertClassField
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      raySubgroup (Modulus.one (hilbertClassField K)) := by
  let H := hilbertClassField K
  -- Supply the canonical `H`-algebra structures on `SeparableClosure H` and `hilbertClassField H`
  -- directly so `IntermediateField` shortcut instances do not search for an action of
  -- `SeparableClosure K` on `SeparableClosure H`.
  let _ : Algebra H (SeparableClosure H) :=
    (separableClosure H (AlgebraicClosure H)).toSubalgebra.algebra
  let H' := hilbertClassField H
  let _ : Algebra H H' := H'.toSubalgebra.algebra
  let _ : Module H H' := Algebra.toModule
  let j : H' →ₐ[H] SeparableClosure K := IsSepClosed.lift
  let E : IntermediateField H (SeparableClosure K) := j.fieldRange
  have : FiniteDimensional H E := j.toLinearMap.finiteDimensional_range
  have : IsUnramifiedAtInfinitePlaces H E := j.isUnramifiedAtInfinitePlaces_fieldRange
  have : Algebra.FormallyUnramified (𝓞 H) (𝓞 E) :=
    Algebra.FormallyUnramified.of_equiv (RingOfIntegers.mapAlgEquiv j.equivFieldRange)
  obtain ⟨V, hV, hinf, hfu⟩ := exists_unramified_classField_eq_normalClosure K E
  have hEN : ∀ z : E, (z : SeparableClosure K) ∈ classField K V := fun z ↦
    hV.symm ▸ (IsScalarTower.toAlgHom K E (SeparableClosure K)).fieldRange_le_normalClosure
      ⟨z, rfl⟩
  have hHV : H ≤ classField K V := fun x hx ↦ hEN (algebraMap H E ⟨x, hx⟩)
  let _ : Algebra H (classField K V) := (IntermediateField.inclusion hHV).toAlgebra
  have : IsScalarTower H (classField K V) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hc := ideleClassExtension_mem_range_ideleClassNormMap_of_unramified V
    (fun w ↦ Algebra.formallyUnramified_iff_forall.mp hfu ⟨w.asIdeal, w.isPrime⟩) c
  let g : H' →ₐ[H] classField K V :=
    { toFun z := ⟨j z, hEN ⟨j z, ⟨z, rfl⟩⟩⟩
      map_one' := Subtype.ext j.map_one
      map_mul' x y := Subtype.ext (j.map_mul x y)
      map_zero' := Subtype.ext j.map_zero
      map_add' x y := Subtype.ext (j.map_add x y)
      commutes' x := Subtype.ext (j.commutes x) }
  rw [← range_ideleClassNormMap_rayClassField (Modulus.one H)]
  exact range_ideleClassNormMap_le_of_algHom g hc

/-- **Class-group form of the Principal Ideal Theorem.** Extending ideal classes from a number
field `K` to its Hilbert class field produces the trivial homomorphism on class groups. Notice
that `@[simp]` is placed on `extendedHom_rayClassField_eq_one`, which simplifies this left-hand
side as well since `hilbertClassField K` is an abbreviation for `rayClassField (Modulus.one K)`. -/
theorem extendedHom_hilbertClassField_eq_one :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (hilbertClassField K)) = 1 :=
  extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup.mpr
    (ideleClassExtension_mem_raySubgroup_one_hilbertClassField K)

/-- **The Principal Ideal Theorem.** Every ideal of the ring of integers of a number field `K`
becomes principal when extended to the ring of integers of `hilbertClassField K`. -/
theorem isPrincipal_map_hilbertClassField (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (hilbertClassField K)))).IsPrincipal :=
  (ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal
    (𝓞 K) (𝓞 (hilbertClassField K))).mp (extendedHom_hilbertClassField_eq_one K) I

variable {K}

/-- Every ideal of `𝓞 K` becomes principal in the ring of integers of any field extension `L / K`
into which `hilbertClassField K` embeds over `K`; `L` need not be finite over `K`. -/
theorem isPrincipal_map_of_algHom_hilbertClassField {L : Type*} [Field L] [Algebra K L]
    (f : hilbertClassField K →ₐ[K] L) (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  rw [← (RingOfIntegers.mapAlgHom f).comp_algebraMap, ← Ideal.map_map]
  exact (isPrincipal_map_hilbertClassField K I).map_ringHom (RingOfIntegers.mapAlgHom f).toRingHom

/-- Extending ideal classes from `K` to any field extension `L / K` into which `hilbertClassField K`
embeds over `K` gives the trivial homomorphism `ClassGroup (𝓞 K) →* ClassGroup (𝓞 L)`. -/
theorem extendedHom_eq_one_of_algHom_hilbertClassField {L : Type*} [Field L] [Algebra K L]
    (f : hilbertClassField K →ₐ[K] L) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 L) = 1 :=
  (ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal (𝓞 K) (𝓞 L)).mpr
    (isPrincipal_map_of_algHom_hilbertClassField f)

/-- Every ideal of `𝓞 K` becomes principal in `𝓞 F` for any intermediate field `F` of
`SeparableClosure K / K` containing `hilbertClassField K`. -/
theorem isPrincipal_map_of_hilbertClassField_le {F : IntermediateField K (SeparableClosure K)}
    (hF : hilbertClassField K ≤ F) (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 F))).IsPrincipal :=
  isPrincipal_map_of_algHom_hilbertClassField (IntermediateField.inclusion hF) I

/-- Extending ideal classes from `K` to any intermediate field `F` of `SeparableClosure K / K`
containing `hilbertClassField K` is trivial on class groups. -/
theorem extendedHom_eq_one_of_hilbertClassField_le {F : IntermediateField K (SeparableClosure K)}
    (hF : hilbertClassField K ≤ F) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 F) = 1 :=
  extendedHom_eq_one_of_algHom_hilbertClassField (IntermediateField.inclusion hF)

/-- Extending ideal classes from `K` to any ray class field `rayClassField 𝔪` (including
`hilbertClassField K` and `narrowHilbertClassField K`) gives the trivial homomorphism. -/
@[simp]
theorem extendedHom_rayClassField_eq_one (𝔪 : Modulus K) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (rayClassField 𝔪)) = 1 :=
  extendedHom_eq_one_of_hilbertClassField_le (hilbertClassField_le_rayClassField 𝔪)

/-- Every ideal of `𝓞 K` becomes principal in the ring of integers of any ray class field
`rayClassField 𝔪` of `K`. -/
theorem isPrincipal_map_rayClassField (𝔪 : Modulus K) (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (rayClassField 𝔪)))).IsPrincipal :=
  isPrincipal_map_of_hilbertClassField_le (hilbertClassField_le_rayClassField 𝔪) I

variable (K) in
/-- Every ideal of `𝓞 K` becomes principal in the ring of integers of the narrow Hilbert class
field `narrowHilbertClassField K`. -/
theorem isPrincipal_map_narrowHilbertClassField (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (narrowHilbertClassField K)))).IsPrincipal :=
  isPrincipal_map_rayClassField (narrowModulus K) I

end PrincipalIdeal

end TauCeti.ClassFieldTheory
