/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import TauCeti.Algebra.Category.FGModuleCat.Mat
public import TauCeti.CategoryTheory.Semisimple.Multiplicity

/-!
# Finite semisimplicity of the matrix category over a division ring

Over a division ring `K`, the singleton object `CategoryTheory.Mat.unit K` is simple, an object
`M : Mat K` is simple if and only if `Nat.card M = 1` (equivalently `Nonempty (M ≅ unit K)`), and
every object decomposes via `CategoryTheory.Mat.isoFinBiproductUnit` as a finite biproduct of
copies of `unit K`. Hence `Mat K` is a finite semisimple abelian category with a unique simple
isomorphism class `SimpleClasses.classOf (Mat.unit K)`, and the simple multiplicity of `M` at that
class is `Nat.card M`.

## Main results

* `CategoryTheory.Mat.instSimpleUnit`: `Mat.unit K` is simple over a division ring `K`.
* `CategoryTheory.Mat.simple_iff_nonempty_iso_unit`, `CategoryTheory.Mat.simple_iff_natCard_eq_one`:
  characterizations of simple objects in `Mat K`.
* `TauCeti.instIsFiniteSemisimpleCategoryMat`: `Mat K` is a finite semisimple category.
* `TauCeti.SimpleClasses.instUniqueMat`: `SimpleClasses (Mat K)` has `classOf (Mat.unit K)` as its
  unique element.
* `TauCeti.simpleMultiplicities_mat`, `TauCeti.simpleMultiplicities_mat_apply`: the simple
  multiplicity of `M : Mat K` is `Nat.card M`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Mat

variable {K : Type u} [DivisionRing K]

/-- Over a division ring `K`, the singleton object `unit K` is simple. -/
instance instSimpleUnit : Simple (unit K) := by
  let F := forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)
  let _ : Simple (F.obj (FGModuleCat.of K K)) := simple_of_isSimpleModule (R := K) (M := K)
  have _ : Simple (FGModuleCat.of K K) := F.simple_of_simple_obj (FGModuleCat.of K K)
  have _ : Simple ((toFGModuleCat K).obj (unit K)) := Simple.of_iso (toFGModuleCatUnitIso K)
  exact (toFGModuleCat K).simple_of_simple_obj (unit K)

/-- An object of `Mat K` over a division ring `K` is simple if and only if it is isomorphic to
`unit K`. -/
theorem simple_iff_nonempty_iso_unit (M : Mat K) :
    Simple M ↔ Nonempty (M ≅ unit K) := by
  refine ⟨fun _ ↦ ?_, fun ⟨e⟩ ↦ Simple.of_iso e⟩
  let _ : Fintype M := @FintypeCat.fintype M
  have hne : Nonempty M :=
    not_isEmpty_iff.mp fun h ↦ Simple.not_isZero M (isZero_iff_isEmpty.mpr h)
  obtain ⟨i₀⟩ := hne
  let ι : unit K ⟶ M := biproduct.ι (fun _ : M ↦ unit K) i₀ ≫ (isoBiproductUnit M).inv
  let π : M ⟶ unit K := (isoBiproductUnit M).hom ≫ biproduct.π (fun _ : M ↦ unit K) i₀
  have hιπ : ι ≫ π = 𝟙 (unit K) := by simp [ι, π]
  have _ : IsSplitMono ι := IsSplitMono.mk' ⟨π, hιπ⟩
  have hnz : ι ≠ 0 := fun h0 ↦
    CategoryTheory.id_ne_zero (unit K) (by rw [← hιπ, h0, zero_comp])
  have _ : IsIso ι := isIso_of_mono_of_ne_zero hnz
  exact ⟨(asIso ι).symm⟩

/-- An object of `Mat K` over a division ring `K` is simple if and only if its cardinality is `1`.
-/
theorem simple_iff_natCard_eq_one (M : Mat K) :
    Simple M ↔ Nat.card M = 1 := by
  have h1 : Nat.card (unit K) = 1 := Nat.card_unique
  rw [simple_iff_nonempty_iso_unit, nonempty_iso_iff_natCard_eq, h1]

end CategoryTheory.Mat

namespace TauCeti

variable (K : Type u) [DivisionRing K]

/-- Over a division ring `K`, `Mat K` is a finite semisimple abelian category: every object `M` is
isomorphic via `Mat.isoFinBiproductUnit M` to the biproduct of `Nat.card M` copies of the simple
object `Mat.unit K`. -/
noncomputable instance instIsFiniteSemisimpleCategoryMat :
    IsFiniteSemisimpleCategory (Mat K) where
  exists_biproduct_simples M :=
    ⟨Fin (Nat.card M), inferInstance, fun _ ↦ Mat.unit K, fun _ ↦ inferInstance,
      inferInstance, ⟨Mat.isoFinBiproductUnit M⟩⟩

/-- `Mat K` over a division ring `K` has a unique simple isomorphism class, represented by
`Mat.unit K`. -/
noncomputable instance SimpleClasses.instUniqueMat : Unique (SimpleClasses (Mat K)) where
  default := SimpleClasses.classOf (Mat.unit K)
  uniq S := by
    rw [← SimpleClasses.classOf_repr S, SimpleClasses.classOf_eq_iff_nonempty_iso]
    exact (Mat.simple_iff_nonempty_iso_unit S.repr).mp S.2

@[simp]
theorem SimpleClasses.default_mat :
    (default : SimpleClasses (Mat K)) = SimpleClasses.classOf (Mat.unit K) :=
  (rfl)

variable {K}

/-- The simple multiplicity function of `M : Mat K` is supported on `classOf (Mat.unit K)` with
value `Nat.card M`. -/
@[simp]
theorem simpleMultiplicities_mat (M : Mat K) :
    simpleMultiplicities M = Finsupp.single (SimpleClasses.classOf (Mat.unit K)) (Nat.card M) := by
  rw [simpleMultiplicities_eq_of_iso_biproduct (fun _ : Fin (Nat.card M) ↦ Mat.unit K)
    (Mat.isoFinBiproductUnit M)]
  simp

/-- Every simple isomorphism class of `Mat K` occurs with multiplicity `Nat.card M` in `M`. -/
theorem simpleMultiplicities_mat_apply (M : Mat K) (S : SimpleClasses (Mat K)) :
    simpleMultiplicities M S = Nat.card M := by
  rw [Subsingleton.elim S (SimpleClasses.classOf (Mat.unit K)), simpleMultiplicities_mat,
    Finsupp.single_eq_same]

end TauCeti
