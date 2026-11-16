/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms
public import TauCeti.NumberTheory.NumberField.FinitePlace.Basic

import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Counting distinct linear forms across places

In the quantitative Subspace Theorem (Evertse–Schlickewei) and in Schmidt's qualitative proof
(Bombieri–Gubler, Theorem 7.5.13), the auxiliary multihomogeneous polynomial has to vanish to high
order along the linear forms occurring at the infinite places and at the selected finite places
`S₀`. Crucially, the number of vanishing systems in Siegel's lemma depends only on the number of
*distinct* linear forms across all relevant places, not on the number of places itself:

1. When `TauCeti.NumberField.exists_forall_approxProd_le_imp` enlarges `(Sinf, Sfin)` to all
   infinite places and a principal-ideal-ring set `S₀ ⊇ Sfin` by placing the coordinate forms
   `LinearMap.proj i` at every newly added place, all newly added places share the same `card ι`
   coordinate forms (`TauCeti.NumberField.formCount_le_of_eq_proj`), so the distinct-form count is
   at most `card ι * (#Sinf + #Sfin + 1)`, independent of `#S₀` and `[K : ℚ]`.
2. When passing from vectors in `Kⁱ` to `p`-vectors in `⋀^p Kⁱ` (Bombieri–Gubler, Theorem 7.5.13
   to Theorem 7.5.18), every `p`-wedge `wedgeForms (L v) p T` is `wedgeForm` of an ordered `p`-tuple
   of forms from `distinctFormSet S₀ L`, so the wedge system has at most `formCount S₀ L ^ p`
   distinct forms (`TauCeti.NumberField.formCount_wedgeForms_le`). Note that `formCount S₀ L ^ p`
   cannot be tightened to `(formCount S₀ L).choose p`: swapping the order of two forms between two
   places negates their exterior product, producing two distinct linear forms from a two-element
   pool (see the final example below).

## Main definitions

* `TauCeti.NumberField.distinctFormSet S₀ L`: the set of linear forms `L v i` occurring at the
  infinite places of `K` or at the finite places in `S₀`.
* `TauCeti.NumberField.formCount S₀ L`: its cardinality `(distinctFormSet S₀ L).ncard`.

## Main results

* `TauCeti.NumberField.finite_distinctFormSet`: `distinctFormSet S₀ L` is finite when the per-place
  index type `κ` is finite.
* `TauCeti.NumberField.formCount_le`: `formCount S₀ L ≤ card κ * (card (InfinitePlace K) + #S₀)`.
* `TauCeti.NumberField.formCount_proj`: the coordinate system has `formCount = card ι` for any `S₀`.
* `TauCeti.NumberField.formCount_le_of_eq_proj`: for an enlarged system equal to `LinearMap.proj`
  outside `(Sinf, Sfin)`, `formCount S₀ L ≤ card ι * (#Sinf + #Sfin + 1)`.
* `TauCeti.NumberField.exists_finset_toMatrix'_pi_mem`: packages the coefficient rows of
  `LinearMap.toMatrix' (LinearMap.pi (L v))` into a `Finset (ι → K)` of exact size `formCount S₀ L`.
* `TauCeti.NumberField.formCount_wedgeForms_le`:
  `formCount S₀ (fun v ↦ wedgeForms (L v) p) ≤ formCount S₀ L ^ p`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Theorems 7.5.13 and 7.5.18.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  Ann. of Math. (2) 156 (2002), 867–901.
-/

public section

open Finset Module Set Set.powersetCard

namespace TauCeti.NumberField

open _root_.NumberField

variable {K κ ι : Type*} [Field K] [NumberField K]

/-- **The set of distinct linear forms** occurring in `L` at the infinite places of `K` or at the
finite places in `S₀`. Using `Set` avoids baking a classical `DecidableEq` instance on
`Dual K (ι → K)` into the public type signature. -/
def distinctFormSet (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) : Set (Dual K (ι → K)) :=
  (⋃ (v : InfinitePlace K) (i : κ), {L v.1 i}) ∪ ⋃ (v ∈ S₀) (i : κ), {L v.1 i}

/-- Explicit union formula for `distinctFormSet`. -/
theorem distinctFormSet_def (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    distinctFormSet S₀ L =
      (⋃ (v : InfinitePlace K) (i : κ), {L v.1 i}) ∪ ⋃ (v ∈ S₀) (i : κ), {L v.1 i} :=
  (rfl)

/-- Membership in `distinctFormSet S₀ L`, unfolded. -/
@[simp]
theorem mem_distinctFormSet {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → κ → Dual K (ι → K)} {f : Dual K (ι → K)} :
    f ∈ distinctFormSet S₀ L ↔
      (∃ (v : InfinitePlace K) (i : κ), L v.1 i = f) ∨ ∃ v ∈ S₀, ∃ i : κ, L v.1 i = f := by
  simp [distinctFormSet, eq_comm]

theorem apply_mem_distinctFormSet_infinite {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → κ → Dual K (ι → K)} (v : InfinitePlace K) (i : κ) :
    L v.1 i ∈ distinctFormSet S₀ L :=
  mem_distinctFormSet.mpr (Or.inl ⟨v, i, rfl⟩)

theorem apply_mem_distinctFormSet_finite {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → κ → Dual K (ι → K)} {v : FinitePlace K} (hv : v ∈ S₀) (i : κ) :
    L v.1 i ∈ distinctFormSet S₀ L :=
  mem_distinctFormSet.mpr (Or.inr ⟨v, hv, i, rfl⟩)

/-- `distinctFormSet S₀ L` depends on `L` only at the infinite places and the places of `S₀`. -/
theorem distinctFormSet_congr {S₀ : Finset (FinitePlace K)}
    {L₁ L₂ : AbsoluteValue K ℝ → κ → Dual K (ι → K)}
    (hInf : ∀ (v : InfinitePlace K) (i : κ), L₁ v.1 i = L₂ v.1 i)
    (hFin : ∀ v ∈ S₀, ∀ i : κ, L₁ v.1 i = L₂ v.1 i) :
    distinctFormSet S₀ L₁ = distinctFormSet S₀ L₂ := by
  ext f
  simp only [mem_distinctFormSet]
  constructor <;> rintro (⟨v, i, rfl⟩ | ⟨v, hv, i, rfl⟩)
  · exact Or.inl ⟨v, i, (hInf v i).symm⟩
  · exact Or.inr ⟨v, hv, i, (hFin v hv i).symm⟩
  · exact Or.inl ⟨v, i, hInf v i⟩
  · exact Or.inr ⟨v, hv, i, hFin v hv i⟩

theorem distinctFormSet_mono {S₀ S₁ : Finset (FinitePlace K)} (hS : S₀ ⊆ S₁)
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    distinctFormSet S₀ L ⊆ distinctFormSet S₁ L := by
  intro f hf
  rcases mem_distinctFormSet.mp hf with ⟨v, i, rfl⟩ | ⟨v, hv, i, rfl⟩
  · exact apply_mem_distinctFormSet_infinite v i
  · exact apply_mem_distinctFormSet_finite (hS hv) i

@[simp]
theorem distinctFormSet_isEmpty [IsEmpty κ] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    distinctFormSet S₀ L = ∅ := by
  ext f
  simp

/-- When the per-place index type `κ` is finite, `distinctFormSet S₀ L` is a finite set. -/
theorem finite_distinctFormSet [Finite κ] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    (distinctFormSet S₀ L).Finite :=
  (finite_iUnion fun _ ↦ finite_iUnion fun _ ↦ finite_singleton _).union
    (S₀.finite_toSet.biUnion fun _ _ ↦ finite_iUnion fun _ ↦ finite_singleton _)

/-- **The number of distinct linear forms** occurring in `L` at the infinite places of `K` or at
the finite places in `S₀`. -/
noncomputable def formCount (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) : ℕ :=
  (distinctFormSet S₀ L).ncard

/-- Explicit `Set.ncard` formula for `formCount`. -/
theorem formCount_def (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    formCount S₀ L = (distinctFormSet S₀ L).ncard :=
  (rfl)

/-- `formCount S₀ L` depends on `L` only at the infinite places and the places of `S₀`. -/
theorem formCount_congr {S₀ : Finset (FinitePlace K)}
    {L₁ L₂ : AbsoluteValue K ℝ → κ → Dual K (ι → K)}
    (hInf : ∀ (v : InfinitePlace K) (i : κ), L₁ v.1 i = L₂ v.1 i)
    (hFin : ∀ v ∈ S₀, ∀ i : κ, L₁ v.1 i = L₂ v.1 i) :
    formCount S₀ L₁ = formCount S₀ L₂ := by
  rw [formCount_def, formCount_def, distinctFormSet_congr hInf hFin]

theorem formCount_mono [Finite κ] {S₀ S₁ : Finset (FinitePlace K)} (hS : S₀ ⊆ S₁)
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    formCount S₀ L ≤ formCount S₁ L :=
  ncard_le_ncard (distinctFormSet_mono hS L) (finite_distinctFormSet S₁ L)

@[simp]
theorem formCount_isEmpty [IsEmpty κ] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    formCount S₀ L = 0 := by
  simp [formCount_def]

/-- **Crude place-by-place upper bound**: `L` contributes at most `card κ` forms at each of the
`card (InfinitePlace K) + #S₀` places. -/
theorem formCount_le [Fintype κ] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    formCount S₀ L ≤ Fintype.card κ * (Fintype.card (InfinitePlace K) + #S₀) := by
  classical
  let F : Finset (Dual K (ι → K)) :=
    ((univ : Finset (InfinitePlace K)).biUnion fun v ↦ univ.image (L v.1)) ∪
      S₀.biUnion fun v ↦ univ.image (L v.1)
  have hsub : distinctFormSet S₀ L ⊆ (F : Set (Dual K (ι → K))) := by
    intro f hf
    rw [mem_coe]
    rcases mem_distinctFormSet.mp hf with ⟨v, i, rfl⟩ | ⟨v, hv, i, rfl⟩
    · exact Finset.mem_union_left _
        (mem_biUnion.mpr ⟨v, mem_univ v, mem_image_of_mem _ (mem_univ i)⟩)
    · exact Finset.mem_union_right _
        (mem_biUnion.mpr ⟨v, hv, mem_image_of_mem _ (mem_univ i)⟩)
  calc formCount S₀ L
      ≤ #F := (ncard_le_ncard hsub F.finite_toSet).trans_eq (ncard_coe_finset F)
    _ ≤ #((univ : Finset (InfinitePlace K)).biUnion fun v ↦ univ.image (L v.1)) +
          #(S₀.biUnion fun v ↦ univ.image (L v.1)) := Finset.card_union_le _ _
    _ ≤ (∑ _v : InfinitePlace K, Fintype.card κ) + ∑ _v ∈ S₀, Fintype.card κ := by
        gcongr
        · exact card_biUnion_le.trans (sum_le_sum fun v _ ↦ card_image_le.trans_eq card_univ)
        · exact card_biUnion_le.trans (sum_le_sum fun v _ ↦ card_image_le.trans_eq card_univ)
    _ = Fintype.card κ * (Fintype.card (InfinitePlace K) + #S₀) := by
        simp [Nat.mul_add, Nat.mul_comm]

/-- Placing the coordinate forms `LinearMap.proj i` at every place yields `Set.range LinearMap.proj`
as the distinct form set, since every number field has at least one infinite place. -/
@[simp]
theorem distinctFormSet_proj (S₀ : Finset (FinitePlace K)) :
    distinctFormSet S₀ (fun _ (i : ι) ↦ LinearMap.proj (R := K) (φ := fun _ : ι ↦ K) i) =
      Set.range (LinearMap.proj (R := K) (φ := fun _ : ι ↦ K)) := by
  have hne : (univ : Finset (InfinitePlace K)).Nonempty :=
    nonempty_of_sum_ne_zero
      (InfinitePlace.sum_mult_eq.trans_ne (Module.finrank_pos (R := ℚ) (M := K)).ne')
  obtain ⟨v₀, -⟩ := hne
  ext f
  simp only [mem_distinctFormSet, Set.mem_range]
  exact ⟨by rintro (⟨_, i, rfl⟩ | ⟨_, _, i, rfl⟩) <;> exact ⟨i, rfl⟩,
    fun ⟨i, hi⟩ ↦ Or.inl ⟨v₀, i, hi⟩⟩

/-- **Coordinate forms contribute only `card ι` distinct forms**, regardless of `#S₀` or
`[K : ℚ]`. -/
@[simp]
theorem formCount_proj [Fintype ι] (S₀ : Finset (FinitePlace K)) :
    formCount S₀ (fun _ (i : ι) ↦ LinearMap.proj (R := K) (φ := fun _ : ι ↦ K) i) =
      Fintype.card ι := by
  classical
  have hinj : Function.Injective (LinearMap.proj (R := K) (φ := fun _ : ι ↦ K)) := by
    intro i j h
    by_contra hij
    have hval := LinearMap.congr_fun h (Pi.single i (1 : K))
    simp [Pi.single_eq_of_ne' hij] at hval
  rw [formCount_def, distinctFormSet_proj, ncard_range_of_injective hinj, Nat.card_eq_fintype_card]

/-- **Distinct-form bound after enlarging the place set** (as in
`TauCeti.NumberField.exists_forall_approxProd_le_imp`). If `L` equals the coordinate forms
`LinearMap.proj` at every infinite place outside `Sinf` and every place of `S₀` outside `Sfin`, then
`formCount S₀ L ≤ card ι * (#Sinf + #Sfin + 1)`, independent of `#S₀` and `[K : ℚ]`. -/
theorem formCount_le_of_eq_proj [Fintype ι] (Sinf : Finset (InfinitePlace K))
    (Sfin S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hInf : ∀ v : InfinitePlace K, v ∉ Sinf → ∀ i, L v.1 i = LinearMap.proj i)
    (hFin : ∀ v ∈ S₀, v ∉ Sfin → ∀ i, L v.1 i = LinearMap.proj i) :
    formCount S₀ L ≤ Fintype.card ι * (#Sinf + #Sfin + 1) := by
  classical
  let F : Finset (Dual K (ι → K)) :=
    (Sinf.biUnion fun v ↦ univ.image (L v.1)) ∪
      (Sfin.biUnion fun v ↦ univ.image (L v.1)) ∪
      univ.image (LinearMap.proj (R := K) (φ := fun _ : ι ↦ K))
  have hsub : distinctFormSet S₀ L ⊆ (F : Set (Dual K (ι → K))) := by
    intro f hf
    rw [mem_coe]
    rcases mem_distinctFormSet.mp hf with ⟨v, i, rfl⟩ | ⟨v, hv, i, rfl⟩
    · by_cases hvS : v ∈ Sinf
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (mem_biUnion.mpr ⟨v, hvS, mem_image_of_mem _ (mem_univ i)⟩))
      · rw [hInf v hvS i]
        exact Finset.mem_union_right _ (mem_image_of_mem _ (mem_univ i))
    · by_cases hvS : v ∈ Sfin
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_biUnion.mpr ⟨v, hvS, mem_image_of_mem _ (mem_univ i)⟩))
      · rw [hFin v hv hvS i]
        exact Finset.mem_union_right _ (mem_image_of_mem _ (mem_univ i))
  calc formCount S₀ L
      ≤ #F := (ncard_le_ncard hsub F.finite_toSet).trans_eq (ncard_coe_finset F)
    _ ≤ #(Sinf.biUnion fun v ↦ univ.image (L v.1)) +
          #(Sfin.biUnion fun v ↦ univ.image (L v.1)) +
          #(univ.image (LinearMap.proj (R := K) (φ := fun _ : ι ↦ K))) :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (∑ _v ∈ Sinf, Fintype.card ι) + (∑ _v ∈ Sfin, Fintype.card ι) + Fintype.card ι := by
        gcongr
        · exact card_biUnion_le.trans (sum_le_sum fun v _ ↦ card_image_le.trans_eq card_univ)
        · exact card_biUnion_le.trans (sum_le_sum fun v _ ↦ card_image_le.trans_eq card_univ)
        · exact card_image_le.trans_eq card_univ
    _ = Fintype.card ι * (#Sinf + #Sfin + 1) := by
        simp [Nat.mul_add, Nat.mul_comm]

/-- **Packaging distinct forms as coefficient rows.** There is a finite set `F : Finset (ι → K)` of
exact cardinality `formCount S₀ L` containing every row of
`LinearMap.toMatrix' (LinearMap.pi (L v))` at every infinite place `v` and every `v ∈ S₀`. -/
theorem exists_finset_toMatrix'_pi_mem [Finite κ] [Fintype ι] [DecidableEq ι]
    (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) :
    ∃ F : Finset (ι → K), #F = formCount S₀ L ∧
      (∀ (v : InfinitePlace K) (i : κ), LinearMap.toMatrix' (LinearMap.pi (L v.1)) i ∈ F) ∧
      ∀ v ∈ S₀, ∀ i : κ, LinearMap.toMatrix' (LinearMap.pi (L v.1)) i ∈ F := by
  classical
  let row : Dual K (ι → K) → (ι → K) := fun f j ↦ f (Pi.single j 1)
  have hrow_inj : Function.Injective row := fun f g h ↦ by
    ext j
    exact congrFun h j
  let F₀ := (finite_distinctFormSet S₀ L).toFinset
  refine ⟨F₀.image row, ?_, fun v i ↦ ?_, fun v hv i ↦ ?_⟩
  · rw [Finset.card_image_of_injective F₀ hrow_inj, formCount_def,
      ncard_eq_toFinset_card _ (finite_distinctFormSet S₀ L)]
  · refine mem_image.mpr ⟨L v.1 i, (finite_distinctFormSet S₀ L).mem_toFinset.mpr
      (apply_mem_distinctFormSet_infinite v i), ?_⟩
    ext j
    simp [row, LinearMap.toMatrix'_apply]
  · refine mem_image.mpr ⟨L v.1 i, (finite_distinctFormSet S₀ L).mem_toFinset.mpr
      (apply_mem_distinctFormSet_finite hv i), ?_⟩
    ext j
    simp [row, LinearMap.toMatrix'_apply]

/-- **Exterior-power distinct-form bound** (for the reduction from `⋀^p Kⁱ` to `Kⁱ` in
Bombieri–Gubler, Theorem 7.5.18): passing from `L v` to its `p`-wedges `wedgeForms (L v) p` raises
the number of distinct forms to at most the `p`-th power `formCount S₀ L ^ p`. -/
theorem formCount_wedgeForms_le [LinearOrder κ] [Finite κ] [LinearOrder ι] [Fintype ι]
    (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → κ → Dual K (ι → K)) (p : ℕ) :
    formCount S₀ (fun v ↦ wedgeForms (L v) p) ≤ formCount S₀ L ^ p := by
  classical
  have _ : Fintype κ := Fintype.ofFinite κ
  let F₀ : Finset (Dual K (ι → K)) := (finite_distinctFormSet S₀ L).toFinset
  let W : Finset (Dual K (powersetCard ι p → K)) :=
    (Fintype.piFinset fun _ : Fin p ↦ F₀).image wedgeForm
  have hsub : distinctFormSet S₀ (fun v ↦ wedgeForms (L v) p) ⊆ (W : Set _) := by
    intro wf hwf
    rw [mem_coe]
    rcases mem_distinctFormSet.mp hwf with ⟨v, T, rfl⟩ | ⟨v, hv, T, rfl⟩
    · refine mem_image.mpr ⟨L v.1 ∘ ofFinEmbEquiv.symm T, Fintype.mem_piFinset.mpr fun a ↦ ?_,
        (wedgeForms_apply (L v.1) p T).symm⟩
      exact (finite_distinctFormSet S₀ L).mem_toFinset.mpr
        (apply_mem_distinctFormSet_infinite v _)
    · refine mem_image.mpr ⟨L v.1 ∘ ofFinEmbEquiv.symm T, Fintype.mem_piFinset.mpr fun a ↦ ?_,
        (wedgeForms_apply (L v.1) p T).symm⟩
      exact (finite_distinctFormSet S₀ L).mem_toFinset.mpr
        (apply_mem_distinctFormSet_finite hv _)
  calc formCount S₀ (fun v ↦ wedgeForms (L v) p)
      ≤ #W := (ncard_le_ncard hsub W.finite_toSet).trans_eq (ncard_coe_finset W)
    _ ≤ #(Fintype.piFinset fun _ : Fin p ↦ F₀) := card_image_le
    _ = #F₀ ^ p := by simp [Fintype.card_piFinset]
    _ = formCount S₀ L ^ p := by
        rw [formCount_def, ncard_eq_toFinset_card _ (finite_distinctFormSet S₀ L)]

/-! ### Examples -/

/-- Over `ℚ`, the coordinate forms on `ℚ³` contribute exactly `3` distinct forms for any `S₀`. -/
example (S₀ : Finset (FinitePlace ℚ)) :
    formCount S₀ (fun _ (i : Fin 3) ↦ LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 ↦ ℚ) i) = 3 := by
  simp

open scoped Classical in
/-- `formCount S₀ L ^ p` in `TauCeti.NumberField.formCount_wedgeForms_le` cannot be tightened to
`(formCount S₀ L).choose p`: if an infinite place uses `(e₀, e₁)` and a finite place `v₀` uses the
swapped pair `(e₁, e₀)`, then `formCount {v₀} L = 2` (so `Nat.choose 2 2 = 1`), yet `e₀ ∧ e₁` and
`e₁ ∧ e₀ = -(e₀ ∧ e₁)` are two distinct `2`-wedges. -/
example (v₀ : FinitePlace K) :
    let e₀ : Dual K (Fin 2 → K) := LinearMap.proj 0
    let e₁ : Dual K (Fin 2 → K) := LinearMap.proj 1
    let L : AbsoluteValue K ℝ → Fin 2 → Dual K (Fin 2 → K) := fun v ↦
      if v = v₀.1 then ![e₁, e₀] else ![e₀, e₁]
    formCount {v₀} L = 2 ∧
      ¬ formCount {v₀} (fun v ↦ wedgeForms (L v) 2) ≤ (formCount {v₀} L).choose 2 := by
  intro e₀ e₁ L
  have he_ne : e₀ ≠ e₁ := fun h ↦ by simpa [e₀, e₁] using LinearMap.congr_fun h ![1, 0]
  have hv_ne (v : InfinitePlace K) : v.1 ≠ v₀.1 := fun h ↦
    v.not_isNonarchimedean (h ▸ fun x y ↦ v₀.add_le x y)
  obtain ⟨v_inf, -⟩ : (univ : Finset (InfinitePlace K)).Nonempty :=
    nonempty_of_sum_ne_zero
      (InfinitePlace.sum_mult_eq.trans_ne (Module.finrank_pos (R := ℚ) (M := K)).ne')
  have hset : distinctFormSet {v₀} L = ({e₀, e₁} : Finset (Dual K (Fin 2 → K))) := by
    ext f
    simp only [mem_distinctFormSet, Finset.mem_singleton, coe_insert, coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro (⟨v, i, rfl⟩ | ⟨v, rfl, i, rfl⟩) <;> fin_cases i <;> simp [L, hv_ne]
    · rintro (rfl | rfl)
      · exact Or.inl ⟨v_inf, 0, by simp [L, hv_ne v_inf]⟩
      · exact Or.inl ⟨v_inf, 1, by simp [L, hv_ne v_inf]⟩
  have hcount : formCount {v₀} L = 2 := by
    rw [formCount_def, hset, ncard_coe_finset, card_pair he_ne]
  refine ⟨hcount, ?_⟩
  rw [hcount, Nat.choose_self]
  let T₀ : powersetCard (Fin 2) 2 := ⟨univ, by simp⟩
  let w_inf := wedgeForms (L v_inf.1) 2 T₀
  let w_fin := wedgeForms (L v₀.1) 2 T₀
  have hw_ne : w_inf ≠ w_fin := by
    intro h
    have hval := LinearMap.congr_fun h (plucker ![![(1 : K), 0], ![0, 1]])
    have hlt : ofFinEmbEquiv.symm T₀ 0 < ofFinEmbEquiv.symm T₀ 1 :=
      (ofFinEmbEquiv.symm T₀).strictMono (by decide)
    have h01 : ofFinEmbEquiv.symm T₀ 0 = 0 ∧ ofFinEmbEquiv.symm T₀ 1 = 1 := by omega
    simp only [w_inf, w_fin, wedgeForms_plucker, L, hv_ne v_inf, ↓reduceIte,
      Matrix.det_fin_two, Matrix.of_apply, h01.1, h01.2,
      Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁, LinearMap.proj_apply] at hval
    norm_num at hval
  have hpair : ({w_inf, w_fin} : Set _) ⊆ distinctFormSet {v₀} (fun v ↦ wedgeForms (L v) 2) := by
    rintro f (rfl | rfl)
    · exact apply_mem_distinctFormSet_infinite v_inf T₀
    · exact apply_mem_distinctFormSet_finite (Finset.mem_singleton_self v₀) T₀
  have h2le : 2 ≤ formCount {v₀} (fun v ↦ wedgeForms (L v) 2) :=
    (ncard_pair hw_ne).symm.trans_le (ncard_le_ncard hpair (finite_distinctFormSet {v₀} _))
  omega

end TauCeti.NumberField
