/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root operators under linear maps

The linear-image construction `TauCeti.PLPath.map` is defined in
`TauCeti.RepresentationTheory.LSPath.PLPath`, including for noninjective maps and collapsed
segments. This file proves naturality of root operators.

The operators `lower` and `raise` commute with a linear map `g` when the target coroot form
pulls back to the source form and the target root is the image of the source root. More generally,
`TauCeti.PLPath.mapₛₗ` pushes paths forward along a semilinear map over a strictly monotone ring
homomorphism `σ : 𝕜 →+* 𝕜'` between ordered fields (for instance `ℚ →+* 𝕜`), commuting with
`endpoint`, `minHeight`, `lower`, and `raise`. The equality of forms up to `σ` preserves all
running heights, so the record cuts, not just the endpoints, agree. This permits both changes of
weight space and scalar extensions of path realizations.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1 (paths, reparametrizations and root operators).
-/

public section

namespace TauCeti.PLPath

open Module

variable {𝕜 V W : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

section Heights

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {g : V →ₗ[𝕜] W} {f : Dual 𝕜 V} {f' : Dual 𝕜 W}

omit [IsStrictOrderedRing 𝕜] in
/-- Capped record reflection commutes with a linear map preserving the height form.
No normalization or injectivity assumption is needed. -/
theorem reflectRecords_map (hf : f'.comp g = f) (x : V) (c : 𝕜) (l : List V) :
    reflectRecords f' (g x) c (l.map g) = (reflectRecords f x c l).map g := by
  have he (v : V) : f' (g v) = f v := LinearMap.congr_fun hf v
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hm : listMinHeight f' (l.map g) = listMinHeight f l := by
      rw [listMinHeight_map, hf]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · rw [List.map_cons, reflectRecords_cons_of_pos (f := f') (by
        simpa only [he, hm] using h), reflectRecords_cons_of_pos h]
      simp [he, hm, ih, preReflection_apply, map_sub, map_smul]
    · rw [List.map_cons, reflectRecords_cons_of_nonpos (f := f') (by
        simpa only [he, hm] using le_of_not_gt h),
        reflectRecords_cons_of_nonpos (le_of_not_gt h)]
      simp [he, ih]

omit [IsStrictOrderedRing 𝕜] in
/-- Lowering on lists is natural for maps preserving the root and coroot form. -/
theorem listLower_map (hf : f'.comp g = f) (x : V) (l : List V) :
    listLower f' (g x) (l.map g) = (listLower f x l).map (List.map g) := by
  have he : f' (l.map g).sum = f l.sum := by
    rw [← map_list_sum, ← LinearMap.comp_apply, hf]
  simp only [listLower_def, listMinHeight_map, hf, he]
  split_ifs <;> simp [reflectRecords_map hf]

/-- Lowering commutes with a linear image preserving the root and the coroot form. -/
theorem lower_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    lower f' (g x) (p.map g) = (lower f x p).map (fun q ↦ q.map g) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [map_ofSegments, lower_ofSegments, listLower_map hf, Option.map_map]
  congr 1
  funext l
  exact (map_ofSegments l g).symm

/-- Raising commutes with a linear image preserving the root and the coroot form. -/
theorem raise_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    raise f' (g x) (p.map g) = (raise f x p).map (fun q ↦ q.map g) := by
  simp only [raise_def, ← map_reverse, lower_map _ hf, Option.map_map]
  congr 1
  funext q
  exact (map_reverse q g).symm

end Heights

section Semilinear

open Relation

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {𝕜' U : Type*} [Field 𝕜'] [LinearOrder 𝕜']
  [IsStrictOrderedRing 𝕜'] [AddCommGroup U] [Module 𝕜' U] {σ : 𝕜 →+* 𝕜'}

private theorem sameRay_mapₛₗ (hσ : StrictMono σ) (g : V →ₛₗ[σ] U) {v w : V}
    (h : SameRay 𝕜 v w) : SameRay 𝕜' (g v) (g w) := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨r₁, r₂, hr₁, hr₂, heq⟩ := h.exists_pos hv hw
  have hr₁' : 0 < σ r₁ := by simpa only [map_zero] using hσ hr₁
  have hr₂' : 0 < σ r₂ := by simpa only [map_zero] using hσ hr₂
  have hg : g v = ((σ r₁)⁻¹ * σ r₂) • g w := by
    have hge := congrArg (fun z ↦ (σ r₁)⁻¹ • g z) heq
    simpa only [map_smulₛₗ, mul_smul, inv_smul_smul₀ hr₁'.ne'] using hge
  rw [hg]
  exact SameRay.rfl.nonneg_smul_left (mul_nonneg (inv_nonneg.mpr hr₁'.le) hr₂'.le)

/-- Taking a semilinear image along a strictly monotone scalar homomorphism preserves elementary
path moves. -/
theorem Move.mapₛₗ (hσ : StrictMono σ) {l m : List V} (h : Move 𝕜 l m) (g : V →ₛₗ[σ] U) :
    Move 𝕜' (l.map g) (m.map g) := by
  cases h with
  | merge l m hvw => simpa using Move.merge (l.map g) (m.map g) (sameRay_mapₛₗ hσ g hvw)
  | erase_zero l m => simpa using Move.erase_zero (l.map g) (m.map g)

/-- Normalizing a presentation before taking a semilinear image along a strictly monotone scalar
homomorphism does not change the path. -/
theorem ofSegments_mapₛₗ_normalize (hσ : StrictMono σ) (g : V →ₛₗ[σ] U) (l : List V) :
    ofSegments 𝕜' ((normalize 𝕜 l).map g) = ofSegments 𝕜' (l.map g) := by
  apply ofSegments_eq_ofSegments_iff.mpr
  exact (EqvGen.reflTransGen_le_eqvGen _ _ _
    ((reflTransGen_move_normalize l).lift _ fun _ _ h ↦ h.mapₛₗ hσ g)).symm _ _

/-- The semilinear image of a piecewise-linear path along `g : V →ₛₗ[σ] U`, with any collapsed
segments removed. -/
noncomputable def mapₛₗ (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] U) : PLPath 𝕜' U :=
  ofSegments 𝕜' (p.segments.map g)

theorem mapₛₗ_def (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] U) :
    p.mapₛₗ g = ofSegments 𝕜' (p.segments.map g) :=
  (rfl)

@[simp]
theorem mapₛₗ_ofSegments (hσ : StrictMono σ) (l : List V) (g : V →ₛₗ[σ] U) :
    (ofSegments 𝕜 l).mapₛₗ g = ofSegments 𝕜' (l.map g) := by
  simp only [mapₛₗ, segments_ofSegments, ofSegments_mapₛₗ_normalize hσ]

@[simp]
theorem mapₛₗ_one (g : V →ₛₗ[σ] U) : (1 : PLPath 𝕜 V).mapₛₗ g = 1 := by
  simp [mapₛₗ]

@[simp]
theorem mapₛₗ_mul (hσ : StrictMono σ) (p q : PLPath 𝕜 V) (g : V →ₛₗ[σ] U) :
    (p * q).mapₛₗ g = p.mapₛₗ g * q.mapₛₗ g := by
  simp [mapₛₗ, ofSegments_mapₛₗ_normalize hσ, List.map_append]

@[simp]
theorem mapₛₗ_straight (hσ : StrictMono σ) (v : V) (g : V →ₛₗ[σ] U) :
    (straight 𝕜 v).mapₛₗ g = straight 𝕜' (g v) := by
  simp [straight_def, mapₛₗ_ofSegments hσ]

@[simp]
theorem endpoint_mapₛₗ (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] U) :
    (p.mapₛₗ g).endpoint = g p.endpoint := by
  simp [mapₛₗ, endpoint_def, map_list_sum]

@[simp]
theorem mapₛₗ_reverse (hσ : StrictMono σ) (p : PLPath 𝕜 V) (g : V →ₛₗ[σ] U) :
    p.reverse.mapₛₗ g = (p.mapₛₗ g).reverse := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp [reverse_ofSegments, mapₛₗ_ofSegments hσ, List.map_reverse, Function.comp_def]

omit [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜'] in
theorem listMinHeight_mapₛₗ (hσ : StrictMono σ) {g : V →ₛₗ[σ] U} {f : Dual 𝕜 V} {f' : Dual 𝕜' U}
    (hf : ∀ v, f' (g v) = σ (f v)) (l : List V) :
    listMinHeight f' (l.map g) = σ (listMinHeight f l) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, listMinHeight_cons, hf, ih, ← σ.map_add]
    rw [← σ.map_zero, hσ.monotone.map_min]

theorem minHeight_mapₛₗ (hσ : StrictMono σ) {g : V →ₛₗ[σ] U} {f : Dual 𝕜 V} {f' : Dual 𝕜' U}
    (hf : ∀ v, f' (g v) = σ (f v)) (p : PLPath 𝕜 V) :
    (p.mapₛₗ g).minHeight f' = σ (p.minHeight f) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp [mapₛₗ_ofSegments hσ, minHeight_ofSegments, listMinHeight_mapₛₗ hσ hf]

omit [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜'] in
theorem reflectRecords_mapₛₗ (hσ : StrictMono σ) {g : V →ₛₗ[σ] U} {f : Dual 𝕜 V} {f' : Dual 𝕜' U}
    (hf : ∀ v, f' (g v) = σ (f v)) (x : V) (c : 𝕜) (l : List V) :
    reflectRecords f' (g x) (σ c) (l.map g) = (reflectRecords f x c l).map g := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hm := listMinHeight_mapₛₗ hσ hf l
    have hmin_eq : min (f' (g v) + listMinHeight f' (l.map g)) (σ c) =
        σ (min (f v + listMinHeight f l) c) := by
      rw [hf, hm, ← σ.map_add, hσ.monotone.map_min]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · have h' : 0 < min (f' (g v) + listMinHeight f' (l.map g)) (σ c) := by
        rw [hmin_eq]
        simpa only [map_zero] using hσ h
      rw [List.map_cons, reflectRecords_cons_of_pos (f := f') h', reflectRecords_cons_of_pos h,
        hmin_eq, hf v, ← map_div₀ σ, ← σ.map_sub, ih]
      simp [hf, preReflection_apply, map_sub, map_smulₛₗ]
    · have h' : min (f' (g v) + listMinHeight f' (l.map g)) (σ c) ≤ 0 := by
        rw [hmin_eq]
        simpa only [map_zero] using hσ.monotone (le_of_not_gt h)
      rw [List.map_cons, reflectRecords_cons_of_nonpos (f := f') h',
        reflectRecords_cons_of_nonpos (le_of_not_gt h), hf v, ← σ.map_sub, ih, List.map_cons]

omit [IsStrictOrderedRing 𝕜] [IsStrictOrderedRing 𝕜'] in
theorem listLower_mapₛₗ (hσ : StrictMono σ) {g : V →ₛₗ[σ] U} {f : Dual 𝕜 V} {f' : Dual 𝕜' U}
    (hf : ∀ v, f' (g v) = σ (f v)) (x : V) (l : List V) :
    listLower f' (g x) (l.map g) = (listLower f x l).map (List.map g) := by
  have he : f' (l.map g).sum = σ (f l.sum) := by
    rw [← map_list_sum, hf]
  have hguard : 1 ≤ f' (l.map g).sum - listMinHeight f' (l.map g) ↔
      1 ≤ f l.sum - listMinHeight f l := by
    rw [he, listMinHeight_mapₛₗ hσ hf, ← σ.map_sub, ← σ.map_one, hσ.le_iff_le]
  rw [listLower_def, listLower_def]
  by_cases h : 1 ≤ f l.sum - listMinHeight f l
  · rw [ite_eq_left (hguard.mpr h), ite_eq_left h, listMinHeight_mapₛₗ hσ hf, ← σ.map_one,
      ← σ.map_add, reflectRecords_mapₛₗ hσ hf, Option.map_some]
  · rw [ite_eq_right (mt hguard.mp h), ite_eq_right h, Option.map_none]

/-- Lowering commutes with a semilinear image along a strictly monotone scalar homomorphism
preserving the root and the coroot form. -/
theorem lower_mapₛₗ (hσ : StrictMono σ) {g : V →ₛₗ[σ] U} {f : Dual 𝕜 V} {f' : Dual 𝕜' U}
    (hf : ∀ v, f' (g v) = σ (f v)) (p : PLPath 𝕜 V) (x : V) :
    lower f' (g x) (p.mapₛₗ g) = (lower f x p).map (fun q ↦ q.mapₛₗ g) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [mapₛₗ_ofSegments hσ, lower_ofSegments, listLower_mapₛₗ hσ hf, Option.map_map]
  congr 1
  funext l
  exact (mapₛₗ_ofSegments hσ l g).symm

/-- Raising commutes with a semilinear image along a strictly monotone scalar homomorphism
preserving the root and the coroot form. -/
theorem raise_mapₛₗ (hσ : StrictMono σ) {g : V →ₛₗ[σ] U} {f : Dual 𝕜 V} {f' : Dual 𝕜' U}
    (hf : ∀ v, f' (g v) = σ (f v)) (p : PLPath 𝕜 V) (x : V) :
    raise f' (g x) (p.mapₛₗ g) = (raise f x p).map (fun q ↦ q.mapₛₗ g) := by
  simp only [raise_def, ← mapₛₗ_reverse hσ, lower_mapₛₗ hσ hf, Option.map_map]
  congr 1
  funext q
  exact (mapₛₗ_reverse hσ q g).symm

end Semilinear

end TauCeti.PLPath
