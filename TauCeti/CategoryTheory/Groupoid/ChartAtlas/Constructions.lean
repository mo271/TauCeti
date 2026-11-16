/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import TauCeti.Algebra.Group.Action.Sum
public import TauCeti.Algebra.GroupAction.Prod
public import TauCeti.CategoryTheory.Groupoid.ChartAtlas.Basic

/-!
# Constructions on retained-arrow chart atlases and induced chart atlases

This file develops standard constructions on `TauCeti.ChartAtlas` and the two-way correspondence
with families of fully faithful action-groupoid charts:

1. **Restriction and reindexing (`restrict`, `reindex`).** Restricting `𝓐` to `G i`-invariant
   subsets `S i : SubMulAction (G i) (U i)` yields `𝓐.restrict S` with full and faithful inclusion
   `𝓐.restrictHom S` and universal lift `𝓐.restrictLift S`. Pulling chart indices back along
   `σ : ν → ι` yields `𝓐.reindex σ` and a full and faithful morphism `𝓐.reindexHom σ`.
2. **Binary products (`prod`).** The componentwise product `𝓐.prod 𝓑` (via
   `TauCeti.IndependentProd`) has projections `fstHom`, `sndHom`, universal pairing `Hom.prod`, and
   presenting-groupoid equivalence `prodObjEquivalence : (𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj`.
3. **Induced atlas and round-trip (`ofCharts`, `toOfCharts`, `fromOfCharts`, `sumCharts`).** Fully
   faithful charts `F i : ActionCategory (G i) (U i) ⥤ C` into a groupoid `C` induce `ofCharts F`
   and fully faithful `ofChartsFunctor F : (ofCharts F).Obj ⥤ C` (essentially surjective iff the
   charts cover `C` up to isomorphism); `toOfCharts` and `fromOfCharts` strictly recover `𝓐` from
   `ofCharts 𝓐.chartFunctor`, and `sumCharts` combines chart families over `ι ⊕ κ`.

## Main declarations

* `TauCeti.ChartAtlas.restrict`, `TauCeti.ChartAtlas.restrictHom`,
  `TauCeti.ChartAtlas.restrictLift`: invariant-subaction restriction and its universal lift.
* `TauCeti.ChartAtlas.reindex`, `TauCeti.ChartAtlas.reindexHom`: chart-index pullback.
* `TauCeti.ChartAtlas.prod`, `TauCeti.ChartAtlas.Hom.prod`, `TauCeti.ChartAtlas.prodObjEquivalence`:
  binary products, universal pairing, and presenting-groupoid equivalence.
* `TauCeti.ChartAtlas.ChartOverlap`, `TauCeti.ChartAtlas.ofCharts`,
  `TauCeti.ChartAtlas.ofChartsFunctor`: induced chart atlas and comparison functor to `C`.
* `TauCeti.ChartAtlas.toOfCharts`, `TauCeti.ChartAtlas.fromOfCharts`,
  `TauCeti.ChartAtlas.ofChartsReindexHom`, `TauCeti.ChartAtlas.sumCharts`,
  `TauCeti.ChartAtlas.sumInlHom`, `TauCeti.ChartAtlas.sumInrHom`: round-trip and sum comparisons.
-/

public section

open CategoryTheory MulAction

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace TauCeti.ChartAtlas

section Restrict

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R) (S : ∀ i, SubMulAction (G i) (U i))

/-- Overlap arrows of `𝓐` whose source lies in `S i` and whose target lies in `S j`. -/
abbrev RestrictArrow (i j : ι) : Type u₄ := { α : R i j // 𝓐.src α ∈ S i ∧ 𝓐.tgt α ∈ S j }

/-- Because `S j` is `G j`-invariant, `G j` acts on `RestrictArrow 𝓐 S i j`. -/
instance instMulActionRestrictArrow (i j : ι) : MulAction (G j) (𝓐.RestrictArrow S i j) where
  smul g α := ⟨g • α.1, (𝓐.src_smul g α.1).symm ▸ α.2.1,
    (𝓐.tgt_smul g α.1).symm ▸ (S j).smul_mem g α.2.2⟩
  one_smul α := Subtype.ext (one_smul _ α.1)
  mul_smul g₁ g₂ α := Subtype.ext (mul_smul g₁ g₂ α.1)

/-- Coercion from `RestrictArrow` commutes with the `G j`-action. -/
@[simp] theorem val_smul_restrictArrow {i j : ι} (g : G j) (α : 𝓐.RestrictArrow S i j) :
    (g • α).1 = g • α.1 := (rfl)

/-- The restriction of a chart atlas `𝓐` to a family of `G i`-invariant subsets `S i ⊆ U i`. -/
def restrict : ChartAtlas G (fun i ↦ S i) (𝓐.RestrictArrow S) where
  src α := ⟨𝓐.src α.1, α.2.1⟩
  tgt α := ⟨𝓐.tgt α.1, α.2.2⟩
  unit i x := ⟨𝓐.unit i x.1, by simp [x.2]⟩
  inv α := ⟨𝓐.inv α.1, by simp [α.2.2, α.2.1]⟩
  comp α β h := ⟨𝓐.comp α.1 β.1 (congrArg Subtype.val h), by simp [α.2.1, β.2.2]⟩
  src_unit _ _ := Subtype.ext (𝓐.src_unit _ _)
  tgt_unit _ _ := Subtype.ext (𝓐.tgt_unit _ _)
  src_inv _ := Subtype.ext (𝓐.src_inv _)
  tgt_inv _ := Subtype.ext (𝓐.tgt_inv _)
  src_comp _ _ _ := Subtype.ext (𝓐.src_comp _ _ _)
  tgt_comp _ _ _ := Subtype.ext (𝓐.tgt_comp _ _ _)
  unit_comp _ _ _ := Subtype.ext (𝓐.unit_comp _ _ _)
  comp_unit _ _ _ := Subtype.ext (𝓐.comp_unit _ _ _)
  comp_assoc _ _ _ _ _ := Subtype.ext (𝓐.comp_assoc _ _ _ _ _)
  comp_inv _ := Subtype.ext (𝓐.comp_inv _)
  inv_comp _ := Subtype.ext (𝓐.inv_comp _)
  src_smul _ _ := Subtype.ext (𝓐.src_smul _ _)
  tgt_smul _ _ := Subtype.ext (𝓐.tgt_smul _ _)
  comp_smul _ _ _ _ := Subtype.ext (𝓐.comp_smul _ _ _ _)
  existsUnique_smul_eq α β h :=
    let ⟨g, hg, hu⟩ := 𝓐.existsUnique_smul_eq α.1 β.1 (congrArg Subtype.val h)
    ⟨g, Subtype.ext hg, fun g' hg' ↦ hu g' (congrArg Subtype.val hg')⟩

/-- Source of a restricted overlap arrow in `𝓐.restrict S`. -/
@[simp] theorem restrict_src {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrict S).src α = ⟨𝓐.src α.1, α.2.1⟩ := (rfl)

/-- Target of a restricted overlap arrow in `𝓐.restrict S`. -/
@[simp] theorem restrict_tgt {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrict S).tgt α = ⟨𝓐.tgt α.1, α.2.2⟩ := (rfl)

/-- Unit overlap arrow in `𝓐.restrict S`. -/
@[simp] theorem restrict_unit (i : ι) (x : S i) :
    (𝓐.restrict S).unit i x = ⟨𝓐.unit i x.1, by simp [x.2]⟩ := (rfl)

/-- Inverse overlap arrow in `𝓐.restrict S`. -/
@[simp] theorem restrict_inv {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrict S).inv α = ⟨𝓐.inv α.1, by simp [α.2.2, α.2.1]⟩ := (rfl)

/-- Composition of overlap arrows in `𝓐.restrict S`. -/
@[simp] theorem restrict_comp {i j k : ι} (α : 𝓐.RestrictArrow S i j) (β : 𝓐.RestrictArrow S j k)
    (h : (𝓐.restrict S).tgt α = (𝓐.restrict S).src β) :
    (𝓐.restrict S).comp α β h = ⟨𝓐.comp α.1 β.1
      (congrArg Subtype.val ((𝓐.restrict_tgt S α).symm.trans (h.trans (𝓐.restrict_src S β)))),
      by simp [α.2.1, β.2.2]⟩ := (rfl)

/-- The canonical inclusion morphism `(𝓐.restrict S).Hom 𝓐`, keeping all group labels. -/
-- `expose, implicit_reducible`: unification in `groupHom`, `obj`, and `map` must see `index i = i`.
@[expose, implicit_reducible] def restrictHom : (𝓐.restrict S).Hom 𝓐 :=
  ⟨id, fun i ↦ MonoidHom.id (G i), fun _ ↦ Subtype.val, Subtype.val,
    fun _ ↦ by simp, fun _ ↦ by simp, fun _ _ ↦ by simp, fun _ _ _ ↦ by simp, fun _ _ ↦ by simp⟩

/-- The index map of `restrictHom` is the identity. -/
@[simp] theorem restrictHom_index : (𝓐.restrictHom S).index = id := (rfl)

/-- The group homomorphism of `restrictHom` on chart `i` is `MonoidHom.id (G i)`. -/
@[simp] theorem restrictHom_groupHom (i : ι) :
    (𝓐.restrictHom S).groupHom i = MonoidHom.id (G i) := (rfl)

/-- `restrictHom` sends a point in `S i` to its underlying point in `U i`. -/
@[simp] theorem restrictHom_obj (i : ι) (x : S i) : (𝓐.restrictHom S).obj i x = x.1 := (rfl)

/-- `restrictHom` sends a restricted overlap arrow to its underlying arrow in `R i j`. -/
@[simp] theorem restrictHom_map {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrictHom S).map α = α.1 := (rfl)

/-- The inclusion functor `(𝓐.restrict S).Obj ⥤ 𝓐.Obj` is faithful. -/
instance instFaithfulRestrictHom : (𝓐.restrictHom S).toFunctor.Faithful :=
  (Hom.faithful_toFunctor_iff _).mpr fun _ _ _ _ hm ↦ Subtype.ext hm

/-- The inclusion functor `(𝓐.restrict S).Obj ⥤ 𝓐.Obj` is full. -/
instance instFullRestrictHom : (𝓐.restrictHom S).toFunctor.Full :=
  (Hom.full_toFunctor_iff _).mpr fun x y β hs ht ↦
    ⟨⟨β, hs.symm ▸ x.2, ht.symm ▸ y.2⟩, Subtype.ext hs, Subtype.ext ht, rfl⟩

variable {κ : Type v₁} {G' : κ → Type v₂} [∀ k, Group (G' k)]
  {U' : κ → Type v₃} [∀ k, MulAction (G' k) (U' k)]
  {R' : κ → κ → Type v₄} [∀ k l, MulAction (G' l) (R' k l)] {𝓑 : ChartAtlas G' U' R'}

/-- Postcomposition with `𝓐.restrictHom S` is injective on atlas morphisms. -/
theorem restrictHom_comp_injective :
    Function.Injective ((𝓐.restrictHom S).comp : 𝓑.Hom (𝓐.restrict S) → 𝓑.Hom 𝓐) := by
  intro Ψ₁ Ψ₂ h
  have hidx : Ψ₁.index = Ψ₂.index := by simpa using congrArg Hom.index h
  have hsub : ∀ {i₁ i₂ j₁ j₂} (_ : i₁ = i₂) (_ : j₁ = j₂) (a : 𝓐.RestrictArrow S i₁ j₁)
      (b : 𝓐.RestrictArrow S i₂ j₂), a.1 ≍ b.1 → a ≍ b := by
    rintro _ _ _ _ rfl rfl _ _ hab; exact heq_of_eq (Subtype.ext (eq_of_heq hab))
  refine Hom.ext hidx (fun k ↦ ?_) fun {k l} α ↦ hsub (congrFun hidx k) (congrFun hidx l) _ _ ?_
  · have hg : ((𝓐.restrictHom S).comp Ψ₁).groupHom k ≍ ((𝓐.restrictHom S).comp Ψ₂).groupHom k := by
      rw [h]
    exact (heq_of_eq (MonoidHom.id_comp _)).symm.trans (hg.trans (heq_of_eq (MonoidHom.id_comp _)))
  · change ((𝓐.restrictHom S).comp Ψ₁).map α ≍ ((𝓐.restrictHom S).comp Ψ₂).map α; rw [h]

/-- Lift an atlas morphism `Φ : 𝓑.Hom 𝓐` whose chart maps land in `S` to `𝓑.Hom (𝓐.restrict S)`. -/
-- `expose, implicit_reducible`: `(𝓐.restrictLift S Φ hΦ).index` must reduce to `Φ.index`.
@[expose, implicit_reducible] def restrictLift (Φ : 𝓑.Hom 𝓐)
    (hΦ : ∀ k x, Φ.obj k x ∈ S (Φ.index k)) : 𝓑.Hom (𝓐.restrict S) :=
  ⟨Φ.index, Φ.groupHom, fun k x ↦ ⟨Φ.obj k x, hΦ k x⟩,
    fun α ↦ ⟨Φ.map α, (Φ.src_map α).symm ▸ hΦ _ _, (Φ.tgt_map α).symm ▸ hΦ _ _⟩,
    fun _ ↦ by ext; simp, fun _ ↦ by ext; simp, fun _ _ ↦ by ext; simp,
    fun α β h ↦ by ext; simp [Φ.map_comp α β (by simpa [Subtype.ext_iff] using h)],
    fun _ _ ↦ by ext; simp⟩

/-- Index map of `restrictLift`. -/
@[simp] theorem restrictLift_index (Φ : 𝓑.Hom 𝓐) (hΦ : ∀ k x, Φ.obj k x ∈ S (Φ.index k)) :
    (𝓐.restrictLift S Φ hΦ).index = Φ.index := (rfl)

/-- Group homomorphism of `restrictLift` at chart `k`. -/
@[simp] theorem restrictLift_groupHom (Φ : 𝓑.Hom 𝓐) (hΦ : ∀ k x, Φ.obj k x ∈ S (Φ.index k))
    (k : κ) : (𝓐.restrictLift S Φ hΦ).groupHom k = Φ.groupHom k := (rfl)

/-- Point map of `restrictLift` at chart `k`. -/
@[simp] theorem restrictLift_obj (Φ : 𝓑.Hom 𝓐) (hΦ : ∀ k x, Φ.obj k x ∈ S (Φ.index k))
    (k : κ) (x : U' k) : (𝓐.restrictLift S Φ hΦ).obj k x = ⟨Φ.obj k x, hΦ k x⟩ := (rfl)

/-- Overlap-arrow map of `restrictLift`. -/
@[simp] theorem restrictLift_map (Φ : 𝓑.Hom 𝓐) (hΦ : ∀ k x, Φ.obj k x ∈ S (Φ.index k))
    {k l : κ} (α : R' k l) : (𝓐.restrictLift S Φ hΦ).map α =
      ⟨Φ.map α, (Φ.src_map α).symm ▸ hΦ _ _, (Φ.tgt_map α).symm ▸ hΦ _ _⟩ := (rfl)

/-- Postcomposing `restrictLift` with `restrictHom` recovers `Φ`. -/
@[simp] theorem restrictHom_comp_restrictLift (Φ : 𝓑.Hom 𝓐)
    (hΦ : ∀ k x, Φ.obj k x ∈ S (Φ.index k)) :
    (𝓐.restrictHom S).comp (𝓐.restrictLift S Φ hΦ) = Φ :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.id_comp _)) (fun _ ↦ HEq.rfl)

/-- Universal property of `ChartAtlas.restrict`: a morphism into `𝓐.restrict S` equals
`𝓐.restrictLift S Φ hΦ` iff postcomposing with `𝓐.restrictHom S` gives `Φ`. -/
theorem eq_restrictLift_iff {Ψ : 𝓑.Hom (𝓐.restrict S)} {Φ : 𝓑.Hom 𝓐}
    (hΦ : ∀ k x, Φ.obj k x ∈ S (Φ.index k)) :
    Ψ = 𝓐.restrictLift S Φ hΦ ↔ (𝓐.restrictHom S).comp Ψ = Φ :=
  ⟨by rintro rfl; exact 𝓐.restrictHom_comp_restrictLift S Φ hΦ,
    fun h ↦ 𝓐.restrictHom_comp_injective S (h.trans (𝓐.restrictHom_comp_restrictLift S Φ hΦ).symm)⟩

end Restrict

section Reindex

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R) {ν : Type v₁} (σ : ν → ι)

/-- Pull back the chart index set of a chart atlas `𝓐` along an arbitrary map `σ : ν → ι`. -/
-- `expose, implicit_reducible`: `(ofCharts F).reindex σ` unifies with `ofCharts (F ∘ σ)`.
@[expose, implicit_reducible] def reindex :
    ChartAtlas (fun n ↦ G (σ n)) (fun n ↦ U (σ n)) (fun m n ↦ R (σ m) (σ n)) :=
  ⟨𝓐.src, 𝓐.tgt, fun n ↦ 𝓐.unit (σ n), 𝓐.inv, 𝓐.comp, fun n ↦ 𝓐.src_unit (σ n),
    fun n ↦ 𝓐.tgt_unit (σ n), 𝓐.src_inv, 𝓐.tgt_inv, 𝓐.src_comp, 𝓐.tgt_comp, 𝓐.unit_comp,
    𝓐.comp_unit, 𝓐.comp_assoc, 𝓐.comp_inv, 𝓐.inv_comp, 𝓐.src_smul, 𝓐.tgt_smul, 𝓐.comp_smul,
    𝓐.existsUnique_smul_eq⟩

/-- Source of an overlap arrow in `𝓐.reindex σ`. -/
@[simp] theorem reindex_src {m n : ν} (α : R (σ m) (σ n)) : (𝓐.reindex σ).src α = 𝓐.src α := (rfl)

/-- Target of an overlap arrow in `𝓐.reindex σ`. -/
@[simp] theorem reindex_tgt {m n : ν} (α : R (σ m) (σ n)) : (𝓐.reindex σ).tgt α = 𝓐.tgt α := (rfl)

/-- Unit overlap arrow in `𝓐.reindex σ`. -/
@[simp] theorem reindex_unit (n : ν) (x : U (σ n)) :
    (𝓐.reindex σ).unit n x = 𝓐.unit (σ n) x := (rfl)

/-- Inverse overlap arrow in `𝓐.reindex σ`. -/
@[simp] theorem reindex_inv {m n : ν} (α : R (σ m) (σ n)) : (𝓐.reindex σ).inv α = 𝓐.inv α := (rfl)

/-- Composition of overlap arrows in `𝓐.reindex σ`. -/
@[simp] theorem reindex_comp {l m n : ν} (α : R (σ l) (σ m)) (β : R (σ m) (σ n))
    (h : (𝓐.reindex σ).tgt α = (𝓐.reindex σ).src β) :
    (𝓐.reindex σ).comp α β h = 𝓐.comp α β h := (rfl)

/-- Canonical atlas morphism `(𝓐.reindex σ).Hom 𝓐` induced by reindexing charts along `σ`. -/
-- `expose, implicit_reducible`: dependent chart types must see `(𝓐.reindexHom σ).index n = σ n`.
@[expose, implicit_reducible] def reindexHom : (𝓐.reindex σ).Hom 𝓐 :=
  ⟨σ, fun n ↦ MonoidHom.id (G (σ n)), fun _ ↦ id, id,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Index map of `reindexHom`. -/
@[simp] theorem reindexHom_index : (𝓐.reindexHom σ).index = σ := (rfl)

/-- Group homomorphism of `reindexHom` at chart `n`. -/
@[simp] theorem reindexHom_groupHom (n : ν) :
    (𝓐.reindexHom σ).groupHom n = MonoidHom.id (G (σ n)) := (rfl)

/-- Point map of `reindexHom` at chart `n`. -/
@[simp] theorem reindexHom_obj (n : ν) (x : U (σ n)) : (𝓐.reindexHom σ).obj n x = x := (rfl)

/-- Overlap-arrow map of `reindexHom`. -/
@[simp] theorem reindexHom_map {m n : ν} (α : R (σ m) (σ n)) : (𝓐.reindexHom σ).map α = α := (rfl)

/-- Every chart-reindexing morphism is faithful on presenting groupoids. -/
instance instFaithfulReindexHom : (𝓐.reindexHom σ).toFunctor.Faithful :=
  (Hom.faithful_toFunctor_iff _).mpr fun _ _ _ _ hm ↦ hm

/-- Every chart-reindexing morphism is full on presenting groupoids. -/
instance instFullReindexHom : (𝓐.reindexHom σ).toFunctor.Full :=
  (Hom.full_toFunctor_iff _).mpr fun _ _ β hs ht ↦ ⟨β, hs, ht, rfl⟩

end Reindex

section Prod

open scoped TauCeti.IndependentProd

variable {ι : Type u₁} {G₁ : ι → Type u₂} [∀ i, Group (G₁ i)]
  {U₁ : ι → Type u₃} [∀ i, MulAction (G₁ i) (U₁ i)]
  {R₁ : ι → ι → Type u₄} [∀ i j, MulAction (G₁ j) (R₁ i j)]
  {κ : Type v₁} {G₂ : κ → Type v₂} [∀ k, Group (G₂ k)]
  {U₂ : κ → Type v₃} [∀ k, MulAction (G₂ k) (U₂ k)]
  {R₂ : κ → κ → Type v₄} [∀ k l, MulAction (G₂ l) (R₂ k l)]
  (𝓐 : ChartAtlas G₁ U₁ R₁) (𝓑 : ChartAtlas G₂ U₂ R₂)

/-- The binary product `𝓐.prod 𝓑` of two retained-arrow chart atlases. -/
def prod : ChartAtlas (fun p : ι × κ ↦ G₁ p.1 × G₂ p.2)
    (fun p ↦ U₁ p.1 × U₂ p.2) (fun p q ↦ R₁ p.1 q.1 × R₂ p.2 q.2) where
  src α := (𝓐.src α.1, 𝓑.src α.2)
  tgt α := (𝓐.tgt α.1, 𝓑.tgt α.2)
  unit p x := (𝓐.unit p.1 x.1, 𝓑.unit p.2 x.2)
  inv α := (𝓐.inv α.1, 𝓑.inv α.2)
  comp α β h := (𝓐.comp α.1 β.1 (congrArg Prod.fst h), 𝓑.comp α.2 β.2 (congrArg Prod.snd h))
  src_unit p x := Prod.ext (𝓐.src_unit p.1 x.1) (𝓑.src_unit p.2 x.2)
  tgt_unit p x := Prod.ext (𝓐.tgt_unit p.1 x.1) (𝓑.tgt_unit p.2 x.2)
  src_inv α := Prod.ext (𝓐.src_inv α.1) (𝓑.src_inv α.2)
  tgt_inv α := Prod.ext (𝓐.tgt_inv α.1) (𝓑.tgt_inv α.2)
  src_comp _ _ _ := Prod.ext (𝓐.src_comp _ _ _) (𝓑.src_comp _ _ _)
  tgt_comp _ _ _ := Prod.ext (𝓐.tgt_comp _ _ _) (𝓑.tgt_comp _ _ _)
  unit_comp _ _ _ := Prod.ext (𝓐.unit_comp _ _ _) (𝓑.unit_comp _ _ _)
  comp_unit _ _ _ := Prod.ext (𝓐.comp_unit _ _ _) (𝓑.comp_unit _ _ _)
  comp_assoc _ _ _ _ _ := Prod.ext (𝓐.comp_assoc _ _ _ _ _) (𝓑.comp_assoc _ _ _ _ _)
  comp_inv α := Prod.ext (𝓐.comp_inv α.1) (𝓑.comp_inv α.2)
  inv_comp α := Prod.ext (𝓐.inv_comp α.1) (𝓑.inv_comp α.2)
  src_smul g α := Prod.ext (𝓐.src_smul g.1 α.1) (𝓑.src_smul g.2 α.2)
  tgt_smul g α := Prod.ext (𝓐.tgt_smul g.1 α.1) (𝓑.tgt_smul g.2 α.2)
  comp_smul α g β _ := Prod.ext (𝓐.comp_smul α.1 g.1 β.1 _) (𝓑.comp_smul α.2 g.2 β.2 _)
  existsUnique_smul_eq α β h :=
    let ⟨g₁, hg₁, hu₁⟩ := 𝓐.existsUnique_smul_eq α.1 β.1 (congrArg Prod.fst h)
    let ⟨g₂, hg₂, hu₂⟩ := 𝓑.existsUnique_smul_eq α.2 β.2 (congrArg Prod.snd h)
    ⟨(g₁, g₂), Prod.ext hg₁ hg₂, fun g hg ↦
      Prod.ext (hu₁ g.1 (congrArg Prod.fst hg)) (hu₂ g.2 (congrArg Prod.snd hg))⟩

/-- Source of an overlap arrow in `𝓐.prod 𝓑`. -/
@[simp] theorem prod_src {p q : ι × κ} (α : R₁ p.1 q.1 × R₂ p.2 q.2) :
    (𝓐.prod 𝓑).src α = (𝓐.src α.1, 𝓑.src α.2) := (rfl)

/-- Target of an overlap arrow in `𝓐.prod 𝓑`. -/
@[simp] theorem prod_tgt {p q : ι × κ} (α : R₁ p.1 q.1 × R₂ p.2 q.2) :
    (𝓐.prod 𝓑).tgt α = (𝓐.tgt α.1, 𝓑.tgt α.2) := (rfl)

/-- Unit overlap arrow in `𝓐.prod 𝓑`. -/
@[simp] theorem prod_unit (p : ι × κ) (x : U₁ p.1 × U₂ p.2) :
    (𝓐.prod 𝓑).unit p x = (𝓐.unit p.1 x.1, 𝓑.unit p.2 x.2) := (rfl)

/-- Inverse overlap arrow in `𝓐.prod 𝓑`. -/
@[simp] theorem prod_inv {p q : ι × κ} (α : R₁ p.1 q.1 × R₂ p.2 q.2) :
    (𝓐.prod 𝓑).inv α = (𝓐.inv α.1, 𝓑.inv α.2) := (rfl)

/-- Composition of overlap arrows in `𝓐.prod 𝓑`. -/
@[simp] theorem prod_comp {p q r : ι × κ}
    (α : R₁ p.1 q.1 × R₂ p.2 q.2) (β : R₁ q.1 r.1 × R₂ q.2 r.2)
    (h : (𝓐.prod 𝓑).tgt α = (𝓐.prod 𝓑).src β) :
    (𝓐.prod 𝓑).comp α β h =
      (𝓐.comp α.1 β.1 (congrArg Prod.fst ((𝓐.prod_tgt 𝓑 α).symm.trans (h.trans (𝓐.prod_src 𝓑 β)))),
        𝓑.comp α.2 β.2
          (congrArg Prod.snd ((𝓐.prod_tgt 𝓑 α).symm.trans (h.trans (𝓐.prod_src 𝓑 β))))) := (rfl)

/-- First projection morphism `(𝓐.prod 𝓑).Hom 𝓐`. -/
-- `expose, implicit_reducible`: dependent chart types must see `(𝓐.fstHom 𝓑).index p` as `p.1`.
@[expose, implicit_reducible] def fstHom : (𝓐.prod 𝓑).Hom 𝓐 :=
  ⟨Prod.fst, fun _ ↦ MonoidHom.fst _ _, fun _ ↦ Prod.fst, Prod.fst,
    fun _ ↦ by simp, fun _ ↦ by simp, fun _ _ ↦ by simp, fun _ _ _ ↦ by simp, fun _ _ ↦ by simp⟩

/-- Index map of `fstHom`. -/
@[simp] theorem fstHom_index : (𝓐.fstHom 𝓑).index = Prod.fst := (rfl)

/-- Group homomorphism of `fstHom` at chart `p`. -/
@[simp] theorem fstHom_groupHom (p : ι × κ) :
    (𝓐.fstHom 𝓑).groupHom p = MonoidHom.fst (G₁ p.1) (G₂ p.2) := (rfl)

/-- Point map of `fstHom` at chart `p`. -/
@[simp] theorem fstHom_obj (p : ι × κ) (x : U₁ p.1 × U₂ p.2) : (𝓐.fstHom 𝓑).obj p x = x.1 := (rfl)

/-- Overlap-arrow map of `fstHom`. -/
@[simp] theorem fstHom_map {p q : ι × κ} (α : R₁ p.1 q.1 × R₂ p.2 q.2) :
    (𝓐.fstHom 𝓑).map α = α.1 := (rfl)

/-- Second projection morphism `(𝓐.prod 𝓑).Hom 𝓑`. -/
-- `expose, implicit_reducible`: dependent chart types must see `(𝓐.sndHom 𝓑).index p` as `p.2`.
@[expose, implicit_reducible] def sndHom : (𝓐.prod 𝓑).Hom 𝓑 :=
  ⟨Prod.snd, fun _ ↦ MonoidHom.snd _ _, fun _ ↦ Prod.snd, Prod.snd,
    fun _ ↦ by simp, fun _ ↦ by simp, fun _ _ ↦ by simp, fun _ _ _ ↦ by simp, fun _ _ ↦ by simp⟩

/-- Index map of `sndHom`. -/
@[simp] theorem sndHom_index : (𝓐.sndHom 𝓑).index = Prod.snd := (rfl)

/-- Group homomorphism of `sndHom` at chart `p`. -/
@[simp] theorem sndHom_groupHom (p : ι × κ) :
    (𝓐.sndHom 𝓑).groupHom p = MonoidHom.snd (G₁ p.1) (G₂ p.2) := (rfl)

/-- Point map of `sndHom` at chart `p`. -/
@[simp] theorem sndHom_obj (p : ι × κ) (x : U₁ p.1 × U₂ p.2) : (𝓐.sndHom 𝓑).obj p x = x.2 := (rfl)

/-- Overlap-arrow map of `sndHom`. -/
@[simp] theorem sndHom_map {p q : ι × κ} (α : R₁ p.1 q.1 × R₂ p.2 q.2) :
    (𝓐.sndHom 𝓑).map α = α.2 := (rfl)

section ProdPairing

variable {𝓐 𝓑} {μ : Type*} {G₃ : μ → Type*} [∀ m, Group (G₃ m)]
  {U₃ : μ → Type*} [∀ m, MulAction (G₃ m) (U₃ m)]
  {R₃ : μ → μ → Type*} [∀ m n, MulAction (G₃ n) (R₃ m n)] {𝓒 : ChartAtlas G₃ U₃ R₃}

/-- Product pairing morphism `𝓒.Hom (𝓐.prod 𝓑)` assembled from morphisms into each factor. -/
-- `expose, implicit_reducible`: dependent chart types must see `(Φ₁.prod Φ₂).index m`.
@[expose, implicit_reducible] def Hom.prod (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) : 𝓒.Hom (𝓐.prod 𝓑) :=
  ⟨fun m ↦ (Φ₁.index m, Φ₂.index m), fun m ↦ (Φ₁.groupHom m).prod (Φ₂.groupHom m),
    fun m x ↦ (Φ₁.obj m x, Φ₂.obj m x), fun α ↦ (Φ₁.map α, Φ₂.map α),
    fun _ ↦ by ext <;> simp, fun _ ↦ by ext <;> simp, fun _ _ ↦ by ext <;> simp,
    fun _ _ _ ↦ by ext <;> simp [Φ₁.map_comp, Φ₂.map_comp], fun _ _ ↦ by ext <;> simp⟩

/-- Index map of `Hom.prod`. -/
@[simp] theorem Hom.prod_index (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) (m : μ) :
    (Φ₁.prod Φ₂).index m = (Φ₁.index m, Φ₂.index m) := (rfl)

/-- Group homomorphism of `Hom.prod` at chart `m`. -/
@[simp] theorem Hom.prod_groupHom (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) (m : μ) :
    (Φ₁.prod Φ₂).groupHom m = (Φ₁.groupHom m).prod (Φ₂.groupHom m) := (rfl)

/-- Point map of `Hom.prod` at chart `m`. -/
@[simp] theorem Hom.prod_obj (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) (m : μ) (x : U₃ m) :
    (Φ₁.prod Φ₂).obj m x = (Φ₁.obj m x, Φ₂.obj m x) := (rfl)

/-- Overlap-arrow map of `Hom.prod`. -/
@[simp] theorem Hom.prod_map (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) {m n : μ} (α : R₃ m n) :
    (Φ₁.prod Φ₂).map α = (Φ₁.map α, Φ₂.map α) := (rfl)

/-- Projecting `Φ₁.prod Φ₂` onto the first factor recovers `Φ₁`. -/
@[simp] theorem fstHom_comp_prod (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) :
    (𝓐.fstHom 𝓑).comp (Φ₁.prod Φ₂) = Φ₁ :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.fst_comp_prod _ _)) (fun _ ↦ HEq.rfl)

/-- Projecting `Φ₁.prod Φ₂` onto the second factor recovers `Φ₂`. -/
@[simp] theorem sndHom_comp_prod (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) :
    (𝓐.sndHom 𝓑).comp (Φ₁.prod Φ₂) = Φ₂ :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.snd_comp_prod _ _)) (fun _ ↦ HEq.rfl)

/-- Pairing the two projections of `𝓐.prod 𝓑` gives the identity morphism. -/
@[simp] theorem fstHom_prod_sndHom : (𝓐.fstHom 𝓑).prod (𝓐.sndHom 𝓑) = Hom.id (𝓐.prod 𝓑) :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.ext fun _ ↦ rfl)) (fun _ ↦ HEq.rfl)

/-- Universal property of `ChartAtlas.prod`: a morphism into `𝓐.prod 𝓑` equals `Φ₁.prod Φ₂` if and
only if its projections equal `Φ₁` and `Φ₂`. -/
theorem Hom.eq_prod_iff {Θ : 𝓒.Hom (𝓐.prod 𝓑)} {Φ₁ : 𝓒.Hom 𝓐} {Φ₂ : 𝓒.Hom 𝓑} :
    Θ = Φ₁.prod Φ₂ ↔ (𝓐.fstHom 𝓑).comp Θ = Φ₁ ∧ (𝓐.sndHom 𝓑).comp Θ = Φ₂ :=
  ⟨by rintro rfl; exact ⟨fstHom_comp_prod Φ₁ Φ₂, sndHom_comp_prod Φ₁ Φ₂⟩,
    by rintro ⟨rfl, rfl⟩; exact
      Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.ext fun _ ↦ rfl)) (fun _ ↦ HEq.rfl)⟩

end ProdPairing

/-- Categorical equivalence `(𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj` identifying the presenting groupoid
of a product atlas with the product of the presenting groupoids. -/
-- `expose, implicit_reducible`: `functor` and `inverse` object maps must reduce on chart indices.
@[expose, implicit_reducible] def prodObjEquivalence : (𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj where
  functor := (𝓐.fstHom 𝓑).toFunctor.prod' (𝓐.sndHom 𝓑).toFunctor
  inverse := ⟨fun p ↦ ⟨(p.1.chart, p.2.chart), (p.1.point, p.2.point)⟩,
    fun f ↦ ⟨(f.1.arrow, f.2.arrow), by simp, by simp⟩, fun _ ↦ by ext <;> simp,
    fun _ _ ↦ by ext <;> simp⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by ext <;> simp

/-- Forward functor of `prodObjEquivalence`. -/
@[simp] theorem prodObjEquivalence_functor :
    (𝓐.prodObjEquivalence 𝓑).functor = (𝓐.fstHom 𝓑).toFunctor.prod' (𝓐.sndHom 𝓑).toFunctor := (rfl)

/-- Object action of the inverse functor of `prodObjEquivalence`. -/
@[simp] theorem prodObjEquivalence_inverse_obj (p : 𝓐.Obj × 𝓑.Obj) :
    (𝓐.prodObjEquivalence 𝓑).inverse.obj p = ⟨(p.1.chart, p.2.chart), (p.1.point, p.2.point)⟩ :=
  (rfl)

/-- Arrow action of the inverse functor of `prodObjEquivalence`. -/
@[simp] theorem prodObjEquivalence_inverse_map_arrow {p q : 𝓐.Obj × 𝓑.Obj} (f : p ⟶ q) :
    ((𝓐.prodObjEquivalence 𝓑).inverse.map f).arrow = (f.1.arrow, f.2.arrow) := (rfl)

/-- Unit isomorphism of `prodObjEquivalence`. -/
@[simp] theorem prodObjEquivalence_unitIso :
    (𝓐.prodObjEquivalence 𝓑).unitIso = Iso.refl (𝟭 (𝓐.prod 𝓑).Obj) := (rfl)

/-- Counit isomorphism of `prodObjEquivalence`. -/
@[simp] theorem prodObjEquivalence_counitIso :
    (𝓐.prodObjEquivalence 𝓑).counitIso = Iso.refl (𝟭 (𝓐.Obj × 𝓑.Obj)) := (rfl)

end Prod

section MonoidCharts

variable {C : Type*} [Category* C] {M₁ : Type u₁} {M₂ : Type u₂} [Monoid M₁] [Monoid M₂]
  {U₁ : Type u₃} {U₂ : Type u₄} [MulAction M₁ U₁] [MulAction M₂ U₂]

/-- An overlap arrow between two action-category charts `F₁ : ActionCategory M₁ U₁ ⥤ C` and
`F₂ : ActionCategory M₂ U₂ ⥤ C`: a source point `src : U₁`, a target point `tgt : U₂`, and a
morphism in `C` between their chart images. -/
@[ext] structure ChartOverlap (F₁ : ActionCategory M₁ U₁ ⥤ C) (F₂ : ActionCategory M₂ U₂ ⥤ C) where
  /-- Source point in the first chart. -/
  src : U₁
  /-- Target point in the second chart. -/
  tgt : U₂
  /-- Morphism in `C` from the image of `src` to the image of `tgt`. -/
  hom : F₁.obj (ActionCategory.objEquiv M₁ U₁ src) ⟶ F₂.obj (ActionCategory.objEquiv M₂ U₂ tgt)

/-- `M₂` acts on `ChartOverlap F₁ F₂` by translating `tgt` and postcomposing `hom` with the
image under `F₂` of the action-category arrow labelled by `m`. -/
instance instSMulChartOverlap (F₁ : ActionCategory M₁ U₁ ⥤ C) (F₂ : ActionCategory M₂ U₂ ⥤ C) :
    SMul M₂ (ChartOverlap F₁ F₂) where
  smul m α := ⟨α.src, m • α.tgt,
    α.hom ≫ F₂.map (Functor.Elements.homMk m rfl :
      ActionCategory.objEquiv M₂ U₂ α.tgt ⟶ ActionCategory.objEquiv M₂ U₂ (m • α.tgt))⟩

/-- `smul` on `ChartOverlap` preserves `src`. -/
@[simp] theorem chartOverlap_smul_src {F₁ : ActionCategory M₁ U₁ ⥤ C}
    {F₂ : ActionCategory M₂ U₂ ⥤ C} (m : M₂) (α : ChartOverlap F₁ F₂) : (m • α).src = α.src := (rfl)

/-- `smul` on `ChartOverlap` translates `tgt` by `m`. -/
@[simp] theorem chartOverlap_smul_tgt {F₁ : ActionCategory M₁ U₁ ⥤ C}
    {F₂ : ActionCategory M₂ U₂ ⥤ C} (m : M₂) (α : ChartOverlap F₁ F₂) :
    (m • α).tgt = m • α.tgt := (rfl)

/-- `smul` on `ChartOverlap` postcomposes `hom` with `F₂.map` of the arrow labelled by `m`. -/
@[simp] theorem chartOverlap_smul_hom {F₁ : ActionCategory M₁ U₁ ⥤ C}
    {F₂ : ActionCategory M₂ U₂ ⥤ C} (m : M₂) (α : ChartOverlap F₁ F₂) :
    (m • α).hom = α.hom ≫ F₂.map (Functor.Elements.homMk m rfl :
      ActionCategory.objEquiv M₂ U₂ α.tgt ⟶ ActionCategory.objEquiv M₂ U₂ (m • α.tgt)) := (rfl)

/-- `MulAction` of `M₂` on `ChartOverlap F₁ F₂`. -/
instance instMulActionChartOverlap (F₁ : ActionCategory M₁ U₁ ⥤ C)
    (F₂ : ActionCategory M₂ U₂ ⥤ C) : MulAction M₂ (ChartOverlap F₁ F₂) where
  one_smul α := by
    have h1 : (1 : M₂) • α.tgt = α.tgt := one_smul M₂ α.tgt
    have heq : (Functor.Elements.homMk (1 : M₂) rfl :
        ActionCategory.objEquiv M₂ U₂ α.tgt ⟶ ActionCategory.objEquiv M₂ U₂ ((1 : M₂) • α.tgt)) =
        eqToHom (congrArg (ActionCategory.objEquiv M₂ U₂) h1.symm) :=
      Functor.Elements.hom_ext (ActionCategory.eqToHom_hom _).symm
    exact ChartOverlap.ext rfl h1 (by simp [heq, eqToHom_map])
  mul_smul m₁ m₂ α := by
    have hm : (m₁ * m₂) • α.tgt = m₁ • m₂ • α.tgt := mul_smul m₁ m₂ α.tgt
    have hcomp :
        (Functor.Elements.homMk m₂ rfl :
            ActionCategory.objEquiv M₂ U₂ α.tgt ⟶ ActionCategory.objEquiv M₂ U₂ (m₂ • α.tgt)) ≫
          Functor.Elements.homMk m₁ rfl =
        Functor.Elements.homMk (m₁ * m₂) rfl ≫
          eqToHom (congrArg (ActionCategory.objEquiv M₂ U₂) hm) :=
      Functor.Elements.hom_ext <| by
        rw [ActionCategory.comp_hom, ActionCategory.comp_hom, ActionCategory.eqToHom_hom]; simp
    have hhom : (m₁ • m₂ • α).hom = ((m₁ * m₂) • α).hom ≫
          eqToHom (congrArg (fun u ↦ F₂.obj (ActionCategory.objEquiv M₂ U₂ u)) hm) := by
      simp [← F₂.map_comp, hcomp, eqToHom_map]
    exact ChartOverlap.ext rfl hm
      ((CategoryTheory.comp_eqToHom_heq ((m₁ * m₂) • α).hom _).symm.trans (heq_of_eq hhom.symm))

end MonoidCharts

section GroupoidCharts

variable {C : Type*} [Category* C] [IsGroupoid C]
  {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  (F : ∀ i, ActionCategory (G i) (U i) ⥤ C) [∀ i, (F i).Full] [∀ i, (F i).Faithful]

/-- **Induced retained-arrow chart atlas.** Any family of fully faithful action-groupoid charts
`F i : ActionCategory (G i) (U i) ⥤ C` into a groupoid `C` induces a `ChartAtlas` on
`fun i j ↦ ChartOverlap (F i) (F j)`, retaining all ineffective isotropy labels. -/
-- `expose, implicit_reducible`: `(ofCharts F).reindex σ` unifies with `ofCharts (F ∘ σ)`.
@[expose, implicit_reducible] noncomputable def ofCharts :
    ChartAtlas G U (fun i j ↦ ChartOverlap (F i) (F j)) where
  src α := α.src
  tgt α := α.tgt
  unit _ x := ⟨x, x, 𝟙 _⟩
  inv α := ⟨α.tgt, α.src, CategoryTheory.inv α.hom⟩
  comp {_ j _} α β h := ⟨α.src, β.tgt,
    α.hom ≫ eqToHom (congrArg (fun u ↦ (F j).obj (ActionCategory.objEquiv (G j) (U j) u)) h) ≫
      β.hom⟩
  src_unit _ _ := rfl
  tgt_unit _ _ := rfl
  src_inv _ := rfl
  tgt_inv _ := rfl
  src_comp _ _ _ := rfl
  tgt_comp _ _ _ := rfl
  unit_comp _ α h := by obtain ⟨_, _, _⟩ := α; cases h; exact ChartOverlap.ext rfl rfl (by simp)
  comp_unit α _ h := by obtain ⟨_, _, _⟩ := α; cases h; exact ChartOverlap.ext rfl rfl (by simp)
  comp_assoc α β γ h₁ h₂ := by
    obtain ⟨_, _, _⟩ := α; obtain ⟨_, _, _⟩ := β; obtain ⟨_, _, _⟩ := γ
    cases h₁; cases h₂; exact ChartOverlap.ext rfl rfl (by simp)
  comp_inv _ := ChartOverlap.ext rfl rfl (by simp)
  inv_comp _ := ChartOverlap.ext rfl rfl (by simp)
  src_smul _ _ := rfl
  tgt_smul _ _ := rfl
  comp_smul α g β h := by
    obtain ⟨_, _, _⟩ := α; obtain ⟨_, _, _⟩ := β; cases h; exact ChartOverlap.ext rfl rfl (by simp)
  existsUnique_smul_eq {i j} α β h := by
    obtain ⟨x₁, y₁, f₁⟩ := α; obtain ⟨_, y₂, f₂⟩ := β; cases h
    obtain ⟨e, he⟩ := (F j).map_surjective (CategoryTheory.inv f₁ ≫ f₂)
    let g₀ : G j := e.hom
    have hey : g₀ • y₁ = y₂ := ActionCategory.hom_smul e
    refine ⟨g₀, ?_, fun g hg ↦ ?_⟩
    · have he' : (Functor.Elements.homMk g₀ rfl :
          ActionCategory.objEquiv (G j) (U j) y₁ ⟶ ActionCategory.objEquiv (G j) (U j) (g₀ • y₁)) =
          e ≫ eqToHom (congrArg (ActionCategory.objEquiv (G j) (U j)) hey.symm) :=
        Functor.Elements.hom_ext (by simp [g₀])
      have hhom : (g₀ • (⟨x₁, y₁, f₁⟩ : ChartOverlap (F i) (F j))).hom =
          f₂ ≫ eqToHom
            (congrArg (fun u ↦ (F j).obj (ActionCategory.objEquiv (G j) (U j) u)) hey.symm) := by
        simp [he', eqToHom_map, he]
      exact ChartOverlap.ext rfl hey ((heq_of_eq hhom).trans (CategoryTheory.comp_eqToHom_heq f₂ _))
    · have hg_tgt : g • y₁ = y₂ := congrArg ChartOverlap.tgt hg
      subst hg_tgt
      have hg_hom : f₁ ≫ (F j).map (Functor.Elements.homMk g rfl :
          ActionCategory.objEquiv (G j) (U j) y₁ ⟶ ActionCategory.objEquiv (G j) (U j) (g • y₁)) =
          f₂ := eq_of_heq (ChartOverlap.ext_iff.mp hg).2.2
      have hmap : (F j).map (Functor.Elements.homMk g rfl :
          ActionCategory.objEquiv (G j) (U j) y₁ ⟶ ActionCategory.objEquiv (G j) (U j) (g • y₁)) =
          (F j).map e := by rw [he, ← hg_hom, IsIso.inv_hom_id_assoc]
      exact congrArg Functor.Elements.Hom.hom ((F j).map_injective hmap)

/-- Source of an overlap arrow in `ofCharts F`. -/
@[simp] theorem ofCharts_src {i j : ι} (α : ChartOverlap (F i) (F j)) :
    (ofCharts F).src α = α.src := (rfl)

/-- Target of an overlap arrow in `ofCharts F`. -/
@[simp] theorem ofCharts_tgt {i j : ι} (α : ChartOverlap (F i) (F j)) :
    (ofCharts F).tgt α = α.tgt := (rfl)

/-- Unit overlap arrow in `ofCharts F`. -/
@[simp] theorem ofCharts_unit (i : ι) (x : U i) : (ofCharts F).unit i x = ⟨x, x, 𝟙 _⟩ := (rfl)

/-- Inverse overlap arrow in `ofCharts F`. -/
@[simp] theorem ofCharts_inv {i j : ι} (α : ChartOverlap (F i) (F j)) :
    (ofCharts F).inv α = ⟨α.tgt, α.src, CategoryTheory.inv α.hom⟩ := (rfl)

/-- Composition of overlap arrows in `ofCharts F`. -/
@[simp] theorem ofCharts_comp {i j k : ι}
    (α : ChartOverlap (F i) (F j)) (β : ChartOverlap (F j) (F k))
    (h : (ofCharts F).tgt α = (ofCharts F).src β) :
    (ofCharts F).comp α β h = ⟨α.src, β.tgt,
      α.hom ≫ eqToHom (congrArg (fun u ↦ (F j).obj (ActionCategory.objEquiv (G j) (U j) u))
        ((ofCharts_tgt F α).symm.trans (h.trans (ofCharts_src F β)))) ≫ β.hom⟩ := (rfl)

/-- The canonical comparison functor `(ofCharts F).Obj ⥤ C` from the presenting groupoid of the
induced chart atlas back to `C`. -/
-- `expose, implicit_reducible`: `(ofChartsFunctor F).obj x` must reduce in morphism types.
@[expose, implicit_reducible] noncomputable def ofChartsFunctor : (ofCharts F).Obj ⥤ C where
  obj x := (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) x.point)
  map {x y} f :=
    eqToHom (congrArg (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u))
      ((ofCharts_src F f.arrow).symm.trans f.src_arrow).symm) ≫ f.arrow.hom ≫
      eqToHom (congrArg
        (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u))
        ((ofCharts_tgt F f.arrow).symm.trans f.tgt_arrow))
  map_id x := by
    have h : (𝟙 x : x ⟶ x).arrow = ⟨x.point, x.point, 𝟙 _⟩ :=
      ((ofCharts F).id_arrow x).trans (ofCharts_unit F x.chart x.point)
    generalize (𝟙 x : x ⟶ x) = e at h ⊢; rcases e with ⟨_, _, _⟩; subst h; simp
  map_comp {x y z} f g := by
    rcases f with ⟨⟨sx₁, sy₁, m₁⟩, hs₁, ht₁⟩; rcases g with ⟨⟨sx₂, sy₂, m₂⟩, hs₂, ht₂⟩
    obtain rfl : sx₁ = x.point := (ofCharts_src F _).symm.trans hs₁
    obtain rfl : sy₁ = y.point := (ofCharts_tgt F _).symm.trans ht₁
    obtain rfl : sx₂ = y.point := (ofCharts_src F _).symm.trans hs₂
    obtain rfl : sy₂ = z.point := (ofCharts_tgt F _).symm.trans ht₂
    have h : (⟨⟨x.point, y.point, m₁⟩, hs₁, ht₁⟩ ≫ ⟨⟨y.point, z.point, m₂⟩, hs₂, ht₂⟩ :
        x ⟶ z).arrow = ⟨x.point, z.point, m₁ ≫ eqToHom rfl ≫ m₂⟩ :=
      ((ofCharts F).comp_arrow _ _).trans (ofCharts_comp F _ _ _)
    generalize (⟨⟨x.point, y.point, m₁⟩, hs₁, ht₁⟩ ≫ ⟨⟨y.point, z.point, m₂⟩, hs₂, ht₂⟩ :
      x ⟶ z) = e at h ⊢
    rcases e with ⟨_, _, _⟩; subst h; simp

/-- `ofChartsFunctor F` evaluates on `⟨i, x⟩` as `(F i).obj (objEquiv (G i) (U i) x)`. -/
@[simp] theorem ofChartsFunctor_obj (x : (ofCharts F).Obj) :
    (ofChartsFunctor F).obj x =
      (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) x.point) := (rfl)

/-- Action of `ofChartsFunctor F` on morphisms. -/
theorem ofChartsFunctor_map {x y : (ofCharts F).Obj} (f : x ⟶ y) :
    (ofChartsFunctor F).map f =
      eqToHom (congrArg
        (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u))
        ((ofCharts_src F f.arrow).symm.trans f.src_arrow).symm) ≫ f.arrow.hom ≫
        eqToHom (congrArg
          (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u))
          ((ofCharts_tgt F f.arrow).symm.trans f.tgt_arrow)) := (rfl)

private theorem ofChartsFunctor_map_of_arrow_eq {x y : (ofCharts F).Obj} (f : x ⟶ y)
    {α : ChartOverlap (F x.chart) (F y.chart)} (hf : f.arrow = α)
    (hs : α.src = x.point) (ht : α.tgt = y.point) :
    (ofChartsFunctor F).map f =
      eqToHom (congrArg
        (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u)) hs.symm) ≫
        α.hom ≫ eqToHom (congrArg
          (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u)) ht) := by
  rcases f with ⟨_, _, _⟩; subst hf; rfl

/-- Action of `ofChartsFunctor F` on a morphism constructed directly from chart points and `m`. -/
@[simp] theorem ofChartsFunctor_map_mk {i j : ι} (x : U i) (y : U j)
    (m : (F i).obj (ActionCategory.objEquiv (G i) (U i) x) ⟶
      (F j).obj (ActionCategory.objEquiv (G j) (U j) y))
    (hs : (ofCharts F).src ⟨x, y, m⟩ = x) (ht : (ofCharts F).tgt ⟨x, y, m⟩ = y) :
    (ofChartsFunctor F).map (⟨⟨x, y, m⟩, hs, ht⟩ : (⟨i, x⟩ : (ofCharts F).Obj) ⟶ ⟨j, y⟩) = m := by
  simp [ofChartsFunctor_map]

/-- `ofChartsFunctor F` is faithful. -/
instance instFaithfulOfChartsFunctor : (ofChartsFunctor F).Faithful where
  map_injective {x y} f₁ f₂ h := by
    obtain ⟨⟨sx₁, sy₁, m₁⟩, hs₁, ht₁⟩ := f₁; obtain ⟨⟨sx₂, sy₂, m₂⟩, hs₂, ht₂⟩ := f₂
    obtain rfl : sx₁ = x.point := (ofCharts_src F _).symm.trans hs₁
    obtain rfl : sy₁ = y.point := (ofCharts_tgt F _).symm.trans ht₁
    obtain rfl : sx₂ = x.point := (ofCharts_src F _).symm.trans hs₂
    obtain rfl : sy₂ = y.point := (ofCharts_tgt F _).symm.trans ht₂
    exact Obj.Hom.ext <| ChartOverlap.ext rfl rfl <| heq_of_eq <| by
      simpa [ofChartsFunctor_map] using h

/-- `ofChartsFunctor F` is full. -/
instance instFullOfChartsFunctor : (ofChartsFunctor F).Full where
  map_surjective {x y} m :=
    ⟨⟨⟨x.point, y.point, m⟩, ofCharts_src F _, ofCharts_tgt F _⟩,
      ofChartsFunctor_map_mk F x.point y.point m _ _⟩

/-- `ofChartsFunctor F` is essentially surjective iff the charts `F i` cover `C` up to iso. -/
theorem essSurj_ofChartsFunctor_iff :
    (ofChartsFunctor F).EssSurj ↔ ∀ c : C, ∃ (i : ι) (x : U i),
      Nonempty ((F i).obj (ActionCategory.objEquiv (G i) (U i) x) ≅ c) :=
  ⟨fun h c ↦ let ⟨y, ⟨e⟩⟩ := h.mem_essImage c; ⟨y.chart, y.point, ⟨e⟩⟩,
    fun h ↦ ⟨fun c ↦ let ⟨i, x, ⟨e⟩⟩ := h c; ⟨⟨i, x⟩, ⟨e⟩⟩⟩⟩

/-- Restricting `ofChartsFunctor F` along the `i`-th chart inclusion recovers `F i`. -/
@[simp] theorem chartFunctor_comp_ofChartsFunctor (i : ι) :
    (ofCharts F).chartFunctor i ⋙ ofChartsFunctor F = F i := by
  refine CategoryTheory.Functor.hext (fun a ↦ congrArg (F i).obj (ActionCategory.back_coe a))
    fun {a b} f ↦ ?_
  let g₀ : G i := f.hom
  let obj := ActionCategory.objEquiv (G i) (U i)
  have ea : obj a.back = a := ActionCategory.back_coe a
  have eb : obj (g₀ • a.back) = b :=
    (congrArg obj (ActionCategory.hom_smul f)).trans (ActionCategory.back_coe b)
  have hact : (Functor.Elements.homMk g₀ rfl : obj a.back ⟶ obj (g₀ • a.back)) =
      eqToHom ea ≫ f ≫ eqToHom eb.symm := Functor.Elements.hom_ext (by simp [g₀])
  have hf : (((ofCharts F).chartFunctor i).map f).arrow =
      ⟨a.back, g₀ • a.back,
        𝟙 _ ≫ (F i).map (Functor.Elements.homMk g₀ rfl : obj a.back ⟶ obj (g₀ • a.back))⟩ :=
    ((ofCharts F).chartFunctor_map_arrow i f).trans (congrArg (g₀ • ·) (ofCharts_unit F i a.back))
  rw [Functor.comp_map, ofChartsFunctor_map_of_arrow_eq F _ hf rfl (ActionCategory.hom_smul f)]
  simp [hact, eqToHom_map]

/-- Reindexing a family of fully faithful action charts along `σ : ν → ι` induces a canonical
morphism of chart atlases `(ofCharts (fun n ↦ F (σ n))).Hom (ofCharts F)`. -/
noncomputable abbrev ofChartsReindexHom {ν : Type*} (σ : ν → ι) :
    (ofCharts (fun n ↦ F (σ n))).Hom (ofCharts F) :=
  (ofCharts F).reindexHom σ

/-- `ofChartsReindexHom` commutes strictly with `ofChartsFunctor`. -/
@[simp] theorem ofChartsReindexHom_toFunctor_comp_ofChartsFunctor {ν : Type*} (σ : ν → ι) :
    (ofChartsReindexHom F σ).toFunctor ⋙ ofChartsFunctor F =
      ofChartsFunctor (fun n ↦ F (σ n)) := (rfl)

/-- `ofChartsReindexHom` induces a faithful functor on presenting groupoids. -/
instance instFaithfulOfChartsReindexHom {ν : Type*} (σ : ν → ι) :
    (ofChartsReindexHom F σ).toFunctor.Faithful :=
  inferInstanceAs ((ofCharts F).reindexHom σ).toFunctor.Faithful

/-- `ofChartsReindexHom` induces a full functor on presenting groupoids. -/
instance instFullOfChartsReindexHom {ν : Type*} (σ : ν → ι) :
    (ofChartsReindexHom F σ).toFunctor.Full :=
  inferInstanceAs ((ofCharts F).reindexHom σ).toFunctor.Full

end GroupoidCharts

section RoundTrip

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R)

/-- Two overlap arrows between `chartFunctor`s are equal when their underlying `R`-arrows agree. -/
theorem chartOverlap_chartFunctor_ext {i j : ι}
    {α β : ChartOverlap (𝓐.chartFunctor i) (𝓐.chartFunctor j)} (h : α.hom.arrow = β.hom.arrow) :
    α = β := by
  have hs : α.src = β.src := (ActionCategory.coe_back (M := G i) α.src).symm.trans <|
    α.hom.src_arrow.symm.trans
      ((congrArg 𝓐.src h).trans (β.hom.src_arrow.trans (ActionCategory.coe_back (M := G i) β.src)))
  have ht : α.tgt = β.tgt := (ActionCategory.coe_back (M := G j) α.tgt).symm.trans <|
    α.hom.tgt_arrow.symm.trans
      ((congrArg 𝓐.tgt h).trans (β.hom.tgt_arrow.trans (ActionCategory.coe_back (M := G j) β.tgt)))
  exact ChartOverlap.ext hs ht <| Obj.Hom.hext
    (congrArg (fun u ↦ (𝓐.chartFunctor i).obj (ActionCategory.objEquiv (G i) (U i) u)) hs)
    (congrArg (fun u ↦ (𝓐.chartFunctor j).obj (ActionCategory.objEquiv (G j) (U j) u)) ht)
    (heq_of_eq h)

/-- Inverse atlas morphism from `ofCharts 𝓐.chartFunctor` back to `𝓐`, extracting the underlying
overlap arrow of each morphism in `𝓐.Obj`. -/
-- `expose, implicit_reducible`: dependent chart types must see `𝓐.fromOfCharts.index i` as `i`.
@[expose, implicit_reducible] noncomputable def fromOfCharts :
    (ofCharts 𝓐.chartFunctor).Hom 𝓐 where
  index i := i
  groupHom i := MonoidHom.id (G i)
  obj _ x := x
  map α := α.hom.arrow
  src_map {i _} α := by simpa using α.hom.src_arrow.trans (ActionCategory.coe_back (M := G i) α.src)
  tgt_map {_ j} α := by simpa using α.hom.tgt_arrow.trans (ActionCategory.coe_back (M := G j) α.tgt)
  map_unit i x := by
    rw [ofCharts_unit, id_arrow]; exact congrArg (𝓐.unit i) (ActionCategory.coe_back (M := G i) x)
  map_comp {_ j _} α β h := by
    have h' : α.tgt = β.src := (ofCharts_tgt _ α).symm.trans (h.trans (ofCharts_src _ β))
    have hsrc : 𝓐.tgt (𝓐.unit j (ActionCategory.objEquiv (G j) (U j) α.tgt).back) =
        𝓐.src β.hom.arrow :=
      (𝓐.tgt_unit j _).trans
        ((congrArg (fun s ↦ (ActionCategory.objEquiv (G j) (U j) s).back) h').trans
          β.hom.src_arrow.symm)
    rw [ofCharts_comp, comp_arrow]
    exact 𝓐.comp_congr rfl
      ((𝓐.comp_congr (𝓐.eqToHom_mk_arrow _) rfl _ hsrc).trans (𝓐.unit_comp _ β.hom.arrow hsrc)) _ _
  map_smul {_ j} g α := by
    have htgt : 𝓐.tgt α.hom.arrow = 𝓐.src (g • 𝓐.unit j (𝓐.tgt α.hom.arrow)) :=
      (𝓐.src_unit j _).symm.trans (𝓐.src_smul g _).symm
    rw [chartOverlap_smul_hom, comp_arrow]
    exact (𝓐.comp_congr rfl
      ((𝓐.chartFunctor_map_arrow j _).trans (congrArg (g • 𝓐.unit j ·) α.hom.tgt_arrow.symm))
      _ htgt).trans (𝓐.comp_smul_unit_tgt α.hom.arrow g htgt)

/-- Index map of `fromOfCharts`. -/
@[simp] theorem fromOfCharts_index (i : ι) : 𝓐.fromOfCharts.index i = i := (rfl)

/-- Group homomorphism of `fromOfCharts` at chart `i`. -/
@[simp] theorem fromOfCharts_groupHom (i : ι) : 𝓐.fromOfCharts.groupHom i = MonoidHom.id (G i) :=
  (rfl)

/-- Point map of `fromOfCharts` at chart `i`. -/
@[simp] theorem fromOfCharts_obj (i : ι) (x : U i) : 𝓐.fromOfCharts.obj i x = x := (rfl)

/-- Overlap-arrow map of `fromOfCharts`. -/
@[simp] theorem fromOfCharts_map {i j : ι}
    (α : ChartOverlap (𝓐.chartFunctor i) (𝓐.chartFunctor j)) :
    𝓐.fromOfCharts.map α = α.hom.arrow := (rfl)

/-- Forward atlas morphism from `𝓐` to `ofCharts 𝓐.chartFunctor`, sending each overlap arrow to the
morphism it defines in `𝓐.Obj`. -/
-- `expose, implicit_reducible`: dependent chart types must see `𝓐.toOfCharts.index i` as `i`.
@[expose, implicit_reducible] noncomputable def toOfCharts : 𝓐.Hom (ofCharts 𝓐.chartFunctor) where
  index i := i
  groupHom i := MonoidHom.id (G i)
  obj _ x := x
  map {i j} α := ⟨𝓐.src α, 𝓐.tgt α, ⟨α, (ActionCategory.coe_back (M := G i) (𝓐.src α)).symm,
    (ActionCategory.coe_back (M := G j) (𝓐.tgt α)).symm⟩⟩
  src_map _ := by simp
  tgt_map _ := by simp
  map_unit i x := 𝓐.chartOverlap_chartFunctor_ext (𝓐.fromOfCharts.map_unit i x).symm
  map_comp {i j k} α β h := by
    let mk {a b : ι} (γ : R a b) : ChartOverlap (𝓐.chartFunctor a) (𝓐.chartFunctor b) :=
      ⟨𝓐.src γ, 𝓐.tgt γ, ⟨γ, (ActionCategory.coe_back (M := G a) (𝓐.src γ)).symm,
        (ActionCategory.coe_back (M := G b) (𝓐.tgt γ)).symm⟩⟩
    exact 𝓐.chartOverlap_chartFunctor_ext (𝓐.fromOfCharts.map_comp (mk α) (mk β)
      ((ofCharts_tgt _ (mk α)).trans (h.trans (ofCharts_src _ (mk β)).symm))).symm
  map_smul {i j} g α := 𝓐.chartOverlap_chartFunctor_ext (𝓐.fromOfCharts.map_smul g ⟨𝓐.src α,
    𝓐.tgt α, ⟨α, (ActionCategory.coe_back (M := G i) (𝓐.src α)).symm,
      (ActionCategory.coe_back (M := G j) (𝓐.tgt α)).symm⟩⟩).symm

/-- Index map of `toOfCharts`. -/
@[simp] theorem toOfCharts_index (i : ι) : 𝓐.toOfCharts.index i = i := (rfl)

/-- Group homomorphism of `toOfCharts` at chart `i`. -/
@[simp] theorem toOfCharts_groupHom (i : ι) : 𝓐.toOfCharts.groupHom i = MonoidHom.id (G i) := (rfl)

/-- Point map of `toOfCharts` at chart `i`. -/
@[simp] theorem toOfCharts_obj (i : ι) (x : U i) : 𝓐.toOfCharts.obj i x = x := (rfl)

/-- Source point of `toOfCharts.map α`. -/
@[simp] theorem toOfCharts_map_src {i j : ι} (α : R i j) :
    (𝓐.toOfCharts.map α).src = 𝓐.src α := (rfl)

/-- Target point of `toOfCharts.map α`. -/
@[simp] theorem toOfCharts_map_tgt {i j : ι} (α : R i j) :
    (𝓐.toOfCharts.map α).tgt = 𝓐.tgt α := (rfl)

/-- Underlying arrow of `toOfCharts.map α`. -/
@[simp] theorem toOfCharts_map_hom_arrow {i j : ι} (α : R i j) :
    (𝓐.toOfCharts.map α).hom.arrow = α := (rfl)

/-- The functor induced by `fromOfCharts` on presenting groupoids coincides with
`ofChartsFunctor 𝓐.chartFunctor`. -/
@[simp] theorem fromOfCharts_toFunctor :
    𝓐.fromOfCharts.toFunctor = ofChartsFunctor 𝓐.chartFunctor := by
  have hobj (x : (ofCharts 𝓐.chartFunctor).Obj) :
      𝓐.fromOfCharts.toFunctor.obj x = (ofChartsFunctor 𝓐.chartFunctor).obj x :=
    congrArg (Obj.mk x.chart) (ActionCategory.coe_back (M := G x.chart) x.point).symm
  refine CategoryTheory.Functor.hext hobj fun {x y} f ↦
    Obj.Hom.hext (hobj x) (hobj y) (heq_of_eq ?_)
  obtain ⟨⟨sx, sy, m⟩, hs, ht⟩ := f
  obtain rfl : sx = x.point := (ofCharts_src _ _).symm.trans hs
  obtain rfl : sy = y.point := (ofCharts_tgt _ _).symm.trans ht
  simp [ofChartsFunctor_map]

/-- `fromOfCharts` is a strict left inverse to `toOfCharts`. -/
@[simp] theorem fromOfCharts_comp_toOfCharts : 𝓐.fromOfCharts.comp 𝓐.toOfCharts = Hom.id 𝓐 :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.id_comp _)) (fun _ ↦ HEq.rfl)

/-- `fromOfCharts` is a strict right inverse to `toOfCharts`. -/
@[simp] theorem toOfCharts_comp_fromOfCharts :
    𝓐.toOfCharts.comp 𝓐.fromOfCharts = Hom.id (ofCharts 𝓐.chartFunctor) :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.id_comp _)) fun _ ↦
    heq_of_eq (𝓐.chartOverlap_chartFunctor_ext rfl)

end RoundTrip

section SumElim

variable {C : Type*} [Category* C]
  {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {κ : Type v₁} {G' : κ → Type u₂} [∀ k, Group (G' k)]
  {U' : κ → Type u₃} [∀ k, MulAction (G' k) (U' k)]
  (F₁ : ∀ i, ActionCategory (G i) (U i) ⥤ C) (F₂ : ∀ k, ActionCategory (G' k) (U' k) ⥤ C)

/-- Combining two families of action charts into `C` over `ι ⊕ κ`. -/
-- `expose, implicit_reducible`: `sumCharts` must reduce on `.inl` and `.inr` in implicit args.
@[expose, implicit_reducible] def sumCharts :
    ∀ s : ι ⊕ κ, ActionCategory (Sum.elim G G' s) (Sum.elim U U' s) ⥤ C
  | .inl i => F₁ i
  | .inr k => F₂ k

/-- `sumCharts` evaluates on `Sum.inl i` as `F₁ i`. -/
@[simp] theorem sumCharts_inl (i : ι) : sumCharts F₁ F₂ (.inl i) = F₁ i := (rfl)

/-- `sumCharts` evaluates on `Sum.inr k` as `F₂ k`. -/
@[simp] theorem sumCharts_inr (k : κ) : sumCharts F₁ F₂ (.inr k) = F₂ k := (rfl)

variable [∀ i, (F₁ i).Full] [∀ i, (F₁ i).Faithful] [∀ k, (F₂ k).Full] [∀ k, (F₂ k).Faithful]

/-- Each chart of `sumCharts F₁ F₂` is full. -/
instance instFullSumCharts : ∀ s : ι ⊕ κ, (sumCharts F₁ F₂ s).Full
  | .inl i => inferInstanceAs (F₁ i).Full
  | .inr k => inferInstanceAs (F₂ k).Full

/-- Each chart of `sumCharts F₁ F₂` is faithful. -/
instance instFaithfulSumCharts : ∀ s : ι ⊕ κ, (sumCharts F₁ F₂ s).Faithful
  | .inl i => inferInstanceAs (F₁ i).Faithful
  | .inr k => inferInstanceAs (F₂ k).Faithful

variable [IsGroupoid C]

/-- Left inclusion of `ofCharts F₁` into the combined chart atlas `ofCharts (sumCharts F₁ F₂)`. -/
noncomputable abbrev sumInlHom : (ofCharts F₁).Hom (ofCharts (sumCharts F₁ F₂)) :=
  ofChartsReindexHom (sumCharts F₁ F₂) Sum.inl

/-- `sumInlHom` commutes strictly with `ofChartsFunctor`. -/
@[simp] theorem sumInlHom_toFunctor_comp_ofChartsFunctor :
    (sumInlHom F₁ F₂).toFunctor ⋙ ofChartsFunctor (sumCharts F₁ F₂) = ofChartsFunctor F₁ :=
  ofChartsReindexHom_toFunctor_comp_ofChartsFunctor (sumCharts F₁ F₂) Sum.inl

/-- Right inclusion of `ofCharts F₂` into the combined chart atlas `ofCharts (sumCharts F₁ F₂)`. -/
noncomputable abbrev sumInrHom : (ofCharts F₂).Hom (ofCharts (sumCharts F₁ F₂)) :=
  ofChartsReindexHom (sumCharts F₁ F₂) Sum.inr

/-- `sumInrHom` commutes strictly with `ofChartsFunctor`. -/
@[simp] theorem sumInrHom_toFunctor_comp_ofChartsFunctor :
    (sumInrHom F₁ F₂).toFunctor ⋙ ofChartsFunctor (sumCharts F₁ F₂) = ofChartsFunctor F₂ :=
  ofChartsReindexHom_toFunctor_comp_ofChartsFunctor (sumCharts F₁ F₂) Sum.inr

end SumElim

end TauCeti.ChartAtlas
