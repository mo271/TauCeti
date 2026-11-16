/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Properness on finite covers of the source

A continuous map whose restriction to each piece of a finite cover of its domain is proper is
itself proper. Neither the pieces of the cover nor the spaces need satisfy any closedness,
compactness, or separation condition: every ultrafilter on the domain contains at least one piece
of a finite cover, so a limit of the restricted ultrafilter in that piece pushes forward to a
limit in the ambient space.

Both hypotheses are sharp:
* **Finiteness** cannot be weakened even to a locally finite closed cover: the constant map
  `ℝ → Unit` restricts to a proper map on every interval `[n, n + 1]` (`n : ℤ`), yet `ℝ` is not
  compact.
* **Continuity** cannot be dropped when the pieces are not closed: the map `[0, 1] → ℝ` sending
  `0` to `0` and `x > 0` to `1 / x` restricts to proper maps on `{0}` and on `(0, 1]`, yet is
  not continuous (nor closed).

When the pieces of the finite cover are closed, continuity on the whole domain follows from
continuity on each piece and restriction preserves properness (`IsProperMap.restrict`), giving
an equivalence (`isProperMap_iff_domRestrict_of_isClosed_biUnion`,
`isProperMap_iff_domRestrict_of_isClosed_iUnion`,
`isProperMap_iff_domRestrict_of_isClosed_union`). This is used in homotopy theory to verify
properness of concatenated homotopies and piecewise glued maps on cylinders.

## Main declarations

* `Continuous.isProperMap_of_biUnion_eq_univ`, `Continuous.isProperMap_of_iUnion_eq_univ`,
  `Continuous.isProperMap_of_union_eq_univ`: a continuous map proper on each piece of a finite
  cover of its source is proper.
* `isProperMap_iff_domRestrict_of_isClosed_biUnion`,
  `isProperMap_iff_domRestrict_of_isClosed_iUnion`,
  `isProperMap_iff_domRestrict_of_isClosed_union`: for a finite closed cover of the source, a map
  is proper if and only if its restriction to every piece is proper.

## References

* N. Bourbaki, *General Topology*, Chapter I, §10, no. 3, Proposition 8.
-/

public section

open Filter Set Topology

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- A continuous map whose restriction to each member of a finite family covering its domain is
proper is itself proper. No closedness or separation hypothesis is needed. -/
theorem Continuous.isProperMap_of_biUnion_eq_univ {t : Set ι} {s : ι → Set X}
    (hf : Continuous f) (ht : t.Finite) (hcover : ⋃ i ∈ t, s i = univ)
    (h : ∀ i ∈ t, IsProperMap ((s i).domRestrict f)) : IsProperMap f := by
  refine isProperMap_iff_ultrafilter.2 ⟨hf, fun 𝒰 y hy ↦ ?_⟩
  -- Every ultrafilter on `X` contains at least one member `s i` of the finite cover.
  have hmem : (⋃ i ∈ t, s i) ∈ 𝒰 := hcover ▸ univ_mem
  obtain ⟨i, hit, hsi⟩ := (Ultrafilter.finite_biUnion_mem_iff ht).1 hmem
  -- Pull `𝒰` back to `s i`, find a limit there by properness of `(s i).domRestrict f`, and push
  -- that limit back to `X`.
  let 𝒱 : Ultrafilter (s i) := 𝒰.comap Subtype.val_injective (by rwa [Subtype.range_coe])
  have h𝒱 : Tendsto ((s i).domRestrict f) 𝒱 (𝓝 y) := hy.comp tendsto_comap
  obtain ⟨x, hfx, hx⟩ := (h i hit).ultrafilter_le_nhds_of_tendsto h𝒱
  refine ⟨x, hfx, ?_⟩
  calc (𝒰 : Filter X)
      = Filter.map Subtype.val (𝒱 : Filter (s i)) :=
        (map_comap_of_mem (by rwa [Subtype.range_coe])).symm
    _ ≤ Filter.map Subtype.val (𝓝 x) := map_mono hx
    _ ≤ 𝓝 (x : X) := continuous_subtype_val.tendsto x

/-- A continuous map whose restriction to each piece of a finite indexed cover of its domain is
proper is itself proper. -/
theorem Continuous.isProperMap_of_iUnion_eq_univ [Finite ι] {s : ι → Set X}
    (hf : Continuous f) (hcover : ⋃ i, s i = univ)
    (h : ∀ i, IsProperMap ((s i).domRestrict f)) : IsProperMap f :=
  hf.isProperMap_of_biUnion_eq_univ finite_univ (by simpa using hcover) fun i _ ↦ h i

/-- A continuous map whose restrictions to two sets covering its domain are proper is proper. -/
theorem Continuous.isProperMap_of_union_eq_univ {s₁ s₂ : Set X} (hf : Continuous f)
    (hcover : s₁ ∪ s₂ = univ) (h₁ : IsProperMap (s₁.domRestrict f))
    (h₂ : IsProperMap (s₂.domRestrict f)) : IsProperMap f := by
  refine hf.isProperMap_of_iUnion_eq_univ (ι := Bool) (s := fun b ↦ cond b s₁ s₂) ?_ ?_
  · ext x
    simpa [Bool.exists_bool, or_comm] using eq_univ_iff_forall.1 hcover x
  · rintro (_ | _) <;> assumption

/-- Over a finite closed cover of the domain, a map is proper if and only if its restriction to
each piece is proper. Continuity of `f` on `X` need not be assumed separately. -/
theorem isProperMap_iff_domRestrict_of_isClosed_biUnion {t : Set ι} {s : ι → Set X}
    (ht : t.Finite) (hcl : ∀ i ∈ t, IsClosed (s i)) (hcover : ⋃ i ∈ t, s i = univ) :
    IsProperMap f ↔ ∀ i ∈ t, IsProperMap ((s i).domRestrict f) := by
  refine ⟨fun hf i hi ↦ hf.restrict (hcl i hi), fun h ↦ ?_⟩
  have := ht.to_subtype
  have hcont : Continuous f :=
    (locallyFinite_of_finite (f := fun i : t ↦ s i)).continuous (by simpa using hcover)
      (fun i ↦ hcl i i.2) fun i ↦ continuousOn_iff_continuous_domRestrict.2 (h i i.2).continuous
  exact hcont.isProperMap_of_biUnion_eq_univ ht hcover h

/-- Over a finite indexed closed cover of the domain, a map is proper if and only if its
restriction to each piece is proper. -/
theorem isProperMap_iff_domRestrict_of_isClosed_iUnion [Finite ι] {s : ι → Set X}
    (hcl : ∀ i, IsClosed (s i)) (hcover : ⋃ i, s i = univ) :
    IsProperMap f ↔ ∀ i, IsProperMap ((s i).domRestrict f) := by
  simpa using isProperMap_iff_domRestrict_of_isClosed_biUnion (f := f) finite_univ
    (fun i _ ↦ hcl i) (by simpa using hcover)

/-- Over a binary closed cover `s₁ ∪ s₂ = univ` of the domain, a map is proper if and only if its
restrictions to `s₁` and `s₂` are proper. -/
theorem isProperMap_iff_domRestrict_of_isClosed_union {s₁ s₂ : Set X}
    (hs₁ : IsClosed s₁) (hs₂ : IsClosed s₂) (hcover : s₁ ∪ s₂ = univ) :
    IsProperMap f ↔ IsProperMap (s₁.domRestrict f) ∧ IsProperMap (s₂.domRestrict f) := by
  simpa [Bool.forall_bool, Bool.cond_true, Bool.cond_false, and_comm] using
    isProperMap_iff_domRestrict_of_isClosed_iUnion (f := f) (ι := Bool) (s := fun b ↦ cond b s₁ s₂)
      (fun b ↦ by cases b <;> assumption)
      (by ext x; simpa [Bool.exists_bool, or_comm] using eq_univ_iff_forall.1 hcover x)
