/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Whiskering
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map

/-!
# Retained-arrow chart atlases and their presenting groupoids

An orbifold chart `[U_i / G_i]` is presented by the action groupoid `G_i ⋉ U_i`, keeping all
elements of `G_i` as distinct arrow labels even when they act trivially on `U_i`. Gluing such charts
without erasing ineffective isotropy requires actual overlap arrows `R i j` with source in `U i`,
target in `U j`, associative composition with units and inverses, and a postcomposition action of
`G j` making every nonempty source fiber into a `G j`-torsor.

`TauCeti.ChartAtlas` axiomatizes this structure for an indexed family of actions `G i ↷ U i`.
Postcomposing the unit section identifies `G i × U i` with `R i i` (`TauCeti.ChartAtlas.diagEquiv`),
retaining every ineffective label. Assembling the charts on `Σ i, U i` and overlap arrows on
`Σ p : ι × ι, R p.1 p.2` yields the presenting groupoid `𝓐.Obj`, into which each
`ActionCategory (G i) (U i)` embeds fully and faithfully (`TauCeti.ChartAtlas.chartFunctor`), giving
`Aut ⟨i, x⟩ ≃* stabilizer (G i) x` (`TauCeti.ChartAtlas.stabilizerMulEquivAutObj`) and stabilizer
conjugation `TauCeti.ChartAtlas.stabilizerConj`. Morphisms (`TauCeti.ChartAtlas.Hom`) and natural
transformations (`TauCeti.ChartAtlas.NatTrans`) induce functors and natural isomorphisms on `Obj`.

## Main declarations

* `TauCeti.ChartAtlas`, `TauCeti.ChartAtlas.instTorsorSourceFiber`, `TauCeti.ChartAtlas.diagEquiv`:
  chart atlases, overlap-arrow torsors, and diagonal identification `G i × U i ≃ R i i`.
* `TauCeti.ChartAtlas.Obj`, `TauCeti.ChartAtlas.chartFunctor`: presenting groupoid and charts.
* `TauCeti.ChartAtlas.stabilizerMulEquivAutObj`, `TauCeti.ChartAtlas.stabilizerConj`: isotropy
  identification and stabilizer conjugation along overlap arrows.
* `TauCeti.ChartAtlas.Hom`, `TauCeti.ChartAtlas.NatTrans`: morphisms and natural transformations.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2.2–2.4.
* I. Moerdijk and D. A. Pronk, *Orbifolds, sheaves and groupoids*, K-Theory 12 (1997), 3–21.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory MulAction

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace TauCeti

/-- A **retained-arrow chart atlas** for a family of groups `G i` acting on chart domains `U i`,
with overlap-arrow types `R i j` carrying postcomposition actions of `G j`.

Composition is written in categorical order (`comp α β h` traverses `α` followed by `β`). On each
overlap `R i j`, the group `G j` acts freely and transitively by postcomposition on arrows sharing a
common source (`existsUnique_smul_eq`), retaining all stabilizer labels on `R i i`. -/
structure ChartAtlas {ι : Type u₁} (G : ι → Type u₂) [∀ i, Group (G i)]
    (U : ι → Type u₃) [∀ i, MulAction (G i) (U i)]
    (R : ι → ι → Type u₄) [∀ i j, MulAction (G j) (R i j)] where
  /-- The source point of an overlap arrow in the `i`-th chart. -/
  src : ∀ {i j}, R i j → U i
  /-- The target point of an overlap arrow in the `j`-th chart. -/
  tgt : ∀ {i j}, R i j → U j
  /-- The identity overlap arrow at a point of the `i`-th chart. -/
  unit : ∀ i, U i → R i i
  /-- The inverse of an overlap arrow. -/
  inv : ∀ {i j}, R i j → R j i
  /-- Categorical composition of composable overlap arrows: `α` followed by `β`. -/
  comp : ∀ {i j k} (α : R i j) (β : R j k), tgt α = src β → R i k
  /-- The source of a unit arrow is its base point. -/
  src_unit : ∀ (i : ι) (x : U i), src (unit i x) = x
  /-- The target of a unit arrow is its base point. -/
  tgt_unit : ∀ (i : ι) (x : U i), tgt (unit i x) = x
  /-- Inversion swaps target to source. -/
  src_inv : ∀ {i j} (α : R i j), src (inv α) = tgt α
  /-- Inversion swaps source to target. -/
  tgt_inv : ∀ {i j} (α : R i j), tgt (inv α) = src α
  /-- Composition takes its source from the first arrow. -/
  src_comp : ∀ {i j k} (α : R i j) (β : R j k) (h : tgt α = src β), src (comp α β h) = src α
  /-- Composition takes its target from the second arrow. -/
  tgt_comp : ∀ {i j k} (α : R i j) (β : R j k) (h : tgt α = src β), tgt (comp α β h) = tgt β
  /-- Left unit law for overlap-arrow composition. -/
  unit_comp : ∀ {i j} (x : U i) (α : R i j) (h : tgt (unit i x) = src α), comp (unit i x) α h = α
  /-- Right unit law for overlap-arrow composition. -/
  comp_unit : ∀ {i j} (α : R i j) (y : U j) (h : tgt α = src (unit j y)), comp α (unit j y) h = α
  /-- Associativity of overlap-arrow composition. -/
  comp_assoc : ∀ {i j k l} (α : R i j) (β : R j k) (γ : R k l) (h₁ : tgt α = src β)
    (h₂ : tgt β = src γ), comp (comp α β h₁) γ ((tgt_comp α β h₁).trans h₂) =
      comp α (comp β γ h₂) (h₁.trans (src_comp β γ h₂).symm)
  /-- Right inverse law for overlap arrows. -/
  comp_inv : ∀ {i j} (α : R i j), comp α (inv α) (src_inv α).symm = unit i (src α)
  /-- Left inverse law for overlap arrows. -/
  inv_comp : ∀ {i j} (α : R i j), comp (inv α) α (tgt_inv α) = unit j (tgt α)
  /-- Postcomposition by `G j` preserves the source in `U i`. -/
  src_smul : ∀ {i j} (g : G j) (α : R i j), src (g • α) = src α
  /-- Postcomposition by `G j` translates the target in `U j`. -/
  tgt_smul : ∀ {i j} (g : G j) (α : R i j), tgt (g • α) = g • tgt α
  /-- Postcomposition by `G k` commutes with composition on the left. -/
  comp_smul : ∀ {i j k} (α : R i j) (g : G k) (β : R j k) (h : tgt α = src β),
    comp α (g • β) (h.trans (src_smul g β).symm) = g • comp α β h
  /-- Two overlap arrows in `R i j` with the same source differ by a unique element of `G j`. -/
  existsUnique_smul_eq : ∀ {i j} (α β : R i j), src α = src β → ∃! g : G j, g • α = β

namespace ChartAtlas

section SingleAtlas

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)] (𝓐 : ChartAtlas G U R)

attribute [simp] src_unit tgt_unit src_inv tgt_inv src_comp tgt_comp
  unit_comp comp_unit comp_inv inv_comp src_smul tgt_smul

/-- Composition of overlap arrows is independent of the composability proof. -/
theorem comp_congr {i j k : ι} {α α' : R i j} {β β' : R j k}
    (hα : α = α') (hβ : β = β') (h : 𝓐.tgt α = 𝓐.src β) (h' : 𝓐.tgt α' = 𝓐.src β') :
    𝓐.comp α β h = 𝓐.comp α' β' h' := by subst hα hβ; rfl

/-- Uniqueness of right inverses: if `comp α β h = unit i (src α)`, then `inv α = β`. -/
theorem inv_eq_of_comp_eq_unit {i j : ι} {α : R i j} {β : R j i}
    (h : 𝓐.tgt α = 𝓐.src β) (hcomp : 𝓐.comp α β h = 𝓐.unit i (𝓐.src α)) : 𝓐.inv α = β := by
  calc 𝓐.inv α = 𝓐.comp (𝓐.inv α) (𝓐.unit i (𝓐.src α)) (by simp) := by simp
    _ = 𝓐.comp (𝓐.inv α) (𝓐.comp α β h) (by simp) := 𝓐.comp_congr rfl hcomp.symm _ _
    _ = 𝓐.comp (𝓐.comp (𝓐.inv α) α (𝓐.tgt_inv α)) β _ := (𝓐.comp_assoc _ _ _ _ _).symm
    _ = β := by simp

/-- Atlas extensionality; units and inverses are determined by `src`, `tgt`, and `comp`. -/
@[ext] theorem ext {𝓐 𝓑 : ChartAtlas G U R} (hsrc : ∀ {i j} (α : R i j), 𝓐.src α = 𝓑.src α)
    (htgt : ∀ {i j} (α : R i j), 𝓐.tgt α = 𝓑.tgt α)
    (hcomp : ∀ {i j k} (α : R i j) (β : R j k)
      (h₁ : 𝓐.tgt α = 𝓐.src β) (h₂ : 𝓑.tgt α = 𝓑.src β), 𝓐.comp α β h₁ = 𝓑.comp α β h₂) :
    𝓐 = 𝓑 := by
  have hunit : 𝓐.unit = 𝓑.unit := funext fun i ↦ funext fun x ↦ by
    have h₁ : 𝓐.tgt (𝓐.unit i x) = 𝓐.src (𝓑.unit i x) := by rw [hsrc]; simp
    have h₂ : 𝓑.tgt (𝓐.unit i x) = 𝓑.src (𝓑.unit i x) := by rw [← htgt]; simp
    exact (𝓑.comp_unit (𝓐.unit i x) x h₂).symm.trans
      ((hcomp _ _ h₁ h₂).symm.trans (𝓐.unit_comp x (𝓑.unit i x) h₁))
  have hinv : @𝓐.inv = @𝓑.inv := funext fun i ↦ funext fun j ↦ funext fun α ↦ by
    have h₂ : 𝓐.tgt α = 𝓐.src (𝓑.inv α) := by rw [htgt, hsrc]; simp
    exact 𝓐.inv_eq_of_comp_eq_unit h₂
      (by rw [hcomp α (𝓑.inv α) h₂ (𝓑.src_inv α).symm, 𝓑.comp_inv, ← hsrc, hunit])
  cases 𝓐; cases 𝓑
  have hs : _ = _ := funext fun i ↦ funext fun j ↦ funext (@hsrc i j)
  have ht : _ = _ := funext fun i ↦ funext fun j ↦ funext (@htgt i j)
  subst hs ht hunit hinv; congr; funext _ _ _ α β h; exact hcomp α β h h

/-- The inverse of a unit overlap arrow is itself. -/
@[simp] theorem inv_unit (i : ι) (x : U i) : 𝓐.inv (𝓐.unit i x) = 𝓐.unit i x :=
  𝓐.inv_eq_of_comp_eq_unit (by simp) (by simp)

/-- Inversion on overlap arrows is an involution. -/
@[simp] theorem inv_inv {i j : ι} (α : R i j) : 𝓐.inv (𝓐.inv α) = α :=
  𝓐.inv_eq_of_comp_eq_unit (𝓐.tgt_inv α)
    ((𝓐.inv_comp α).trans (congrArg (𝓐.unit j) (𝓐.src_inv α).symm))

/-- The inverse of a composite overlap arrow is the reverse composite of the inverses. -/
@[simp] theorem inv_comp_rev {i j k : ι} (α : R i j) (β : R j k) (h : 𝓐.tgt α = 𝓐.src β) :
    𝓐.inv (𝓐.comp α β h) =
      𝓐.comp (𝓐.inv β) (𝓐.inv α) ((𝓐.tgt_inv β).trans (h.symm.trans (𝓐.src_inv α).symm)) := by
  refine 𝓐.inv_eq_of_comp_eq_unit (by simp) ?_
  calc 𝓐.comp (𝓐.comp α β h) (𝓐.comp (𝓐.inv β) (𝓐.inv α) _) _
      = 𝓐.comp α (𝓐.comp (𝓐.comp β (𝓐.inv β) (by simp)) (𝓐.inv α) (by simp [h])) (by simp) := by
          rw [𝓐.comp_assoc]; exact 𝓐.comp_congr rfl (𝓐.comp_assoc _ _ _ _ _).symm _ _
    _ = 𝓐.unit i (𝓐.src (𝓐.comp α β h)) := by simp [← h]

/-- Composing `g₂ • unit i x` with `g₁ • unit i (g₂ • x)` gives `(g₁ * g₂) • unit i x`. -/
@[simp] theorem smul_unit_comp_smul_unit {i : ι} (g₁ g₂ : G i) (x : U i) (h) :
    𝓐.comp (g₂ • 𝓐.unit i x) (g₁ • 𝓐.unit i (g₂ • x)) h = (g₁ * g₂) • 𝓐.unit i x :=
  (𝓐.comp_smul _ _ _ (by simp)).trans (by simp [mul_smul])

/-- Postcomposing an arrow `α` by `g` is composing `α` with the `g`-translated unit at `tgt α`. -/
theorem comp_smul_unit_tgt {i j : ι} (α : R i j) (g : G j) (h) :
    𝓐.comp α (g • 𝓐.unit j (𝓐.tgt α)) h = g • α :=
  (𝓐.comp_smul α g (𝓐.unit j (𝓐.tgt α)) (by simp)).trans (by simp)

/-- Inverting a `g`-translated unit arrow gives the `g⁻¹`-translated unit at `g • x`. -/
@[simp] theorem inv_smul_unit {i : ι} (g : G i) (x : U i) :
    𝓐.inv (g • 𝓐.unit i x) = g⁻¹ • 𝓐.unit i (g • x) :=
  𝓐.inv_eq_of_comp_eq_unit (by simp) (by simp)

/-- The fiber of overlap arrows in `R i j` over a fixed source point `x : U i`. -/
abbrev SourceFiber {i : ι} (j : ι) (x : U i) : Type u₄ := { α : R i j // 𝓐.src α = x }

/-- `G j` acts by postcomposition on each source fiber of `R i j`. -/
instance instMulActionSourceFiber {i : ι} (j : ι) (x : U i) :
    MulAction (G j) (𝓐.SourceFiber j x) where
  smul g α := ⟨g • α.1, (𝓐.src_smul g α.1).trans α.2⟩
  one_smul α := Subtype.ext (one_smul _ α.1)
  mul_smul g₁ g₂ α := Subtype.ext (mul_smul g₁ g₂ α.1)

/-- Coercion from a source fiber commutes with the `G j`-action. -/
@[simp] theorem val_smul_sourceFiber {i j : ι} {x : U i} (g : G j) (α : 𝓐.SourceFiber j x) :
    (g • α).1 = g • α.1 := (rfl)

/-- The unique element of `G j` carrying `β` to `α` in a common source fiber. -/
noncomputable instance instSDivSourceFiber {i : ι} (j : ι) (x : U i) :
    SDiv (G j) (𝓐.SourceFiber j x) :=
  ⟨fun α β ↦ (𝓐.existsUnique_smul_eq β.1 α.1 (β.2.trans α.2.symm)).choose⟩

/-- Applying `α /ₛ β` to `β` in a source fiber recovers `α`. -/
@[simp] theorem sdiv_smul_sourceFiber {i j : ι} {x : U i} (α β : 𝓐.SourceFiber j x) :
    (α /ₛ β) • β = α :=
  Subtype.ext (𝓐.existsUnique_smul_eq β.1 α.1 (β.2.trans α.2.symm)).choose_spec.1

/-- **Overlap-arrow torsor.** Every nonempty source fiber of `R i j` is a `G j`-torsor. -/
noncomputable instance instTorsorSourceFiber {i : ι} (j : ι) (x : U i)
    [Nonempty (𝓐.SourceFiber j x)] : Torsor (G j) (𝓐.SourceFiber j x) where
  sdiv_smul' := 𝓐.sdiv_smul_sourceFiber
  smul_sdiv' g α :=
    let h := 𝓐.existsUnique_smul_eq α.1 (g • α.1) (𝓐.src_smul g α.1).symm
    h.unique h.choose_spec.1 rfl

/-- Postcomposing `unit i` identifies `G i × U i` with `R i i`, retaining all group labels. -/
noncomputable def diagEquiv (i : ι) : G i × U i ≃ R i i where
  toFun p := p.1 • 𝓐.unit i p.2
  invFun α := ((𝓐.existsUnique_smul_eq (𝓐.unit i (𝓐.src α)) α (𝓐.src_unit i _)).choose, 𝓐.src α)
  left_inv p := by
    have h := 𝓐.existsUnique_smul_eq _ (p.1 • 𝓐.unit i p.2) (𝓐.src_unit i _)
    exact Prod.ext (h.unique h.choose_spec.1 (by simp)) (by simp)
  right_inv α := (𝓐.existsUnique_smul_eq (𝓐.unit i (𝓐.src α)) α (𝓐.src_unit i _)).choose_spec.1

/-- `diagEquiv i` translates the unit at `p.2` by `p.1`. -/
@[simp] theorem diagEquiv_apply (i : ι) (p : G i × U i) :
    𝓐.diagEquiv i p = p.1 • 𝓐.unit i p.2 := (rfl)

/-- `(diagEquiv i).symm` recovers `(g, x)` from `g • unit i x`. -/
@[simp] theorem diagEquiv_symm_smul_unit (i : ι) (g : G i) (x : U i) :
    (𝓐.diagEquiv i).symm (g • 𝓐.unit i x) = (g, x) := (𝓐.diagEquiv i).symm_apply_eq.mpr rfl

/-- `(diagEquiv i).symm` sends `unit i x` to `(1, x)`. -/
@[simp] theorem diagEquiv_symm_unit (i : ι) (x : U i) :
    (𝓐.diagEquiv i).symm (𝓐.unit i x) = (1, x) := by simpa using 𝓐.diagEquiv_symm_smul_unit i 1 x

/-- The second coordinate of `(diagEquiv i).symm α` is `src α`. -/
@[simp] theorem snd_diagEquiv_symm (i : ι) (α : R i i) :
    ((𝓐.diagEquiv i).symm α).2 = 𝓐.src α := (rfl)

/-- Translating `unit i (src α)` by the first coordinate of `(diagEquiv i).symm α` recovers `α`. -/
@[simp] theorem fst_diagEquiv_symm_smul_unit (i : ι) (α : R i i) :
    ((𝓐.diagEquiv i).symm α).1 • 𝓐.unit i (𝓐.src α) = α := by
  have h := (𝓐.diagEquiv i).apply_symm_apply α; rwa [diagEquiv_apply] at h

/-- An object of the presenting groupoid of `𝓐`: a chart `chart : ι` and `point : U chart`. -/
@[ext] structure Obj (𝓐 : ChartAtlas G U R) where
  /-- The chart index of the object. -/
  chart : ι
  /-- The point in `U chart` underlying the object. -/
  point : U chart

/-- Equivalence between objects of `𝓐.Obj` and the disjoint union `Σ i, U i` of chart domains. -/
def objEquiv : 𝓐.Obj ≃ Σ i, U i :=
  ⟨fun x ↦ ⟨x.chart, x.point⟩, fun p ↦ ⟨p.1, p.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- `objEquiv` records the chart index and point of an object. -/
@[simp] theorem objEquiv_apply (x : 𝓐.Obj) : 𝓐.objEquiv x = ⟨x.chart, x.point⟩ := (rfl)

/-- `objEquiv.symm` constructs an object from a chart index and point. -/
@[simp] theorem objEquiv_symm_apply (p : Σ i, U i) : 𝓐.objEquiv.symm p = ⟨p.1, p.2⟩ := (rfl)

/-- A morphism in `𝓐.Obj`: an arrow in `R x.chart y.chart` from `x.point` to `y.point`. -/
@[ext] structure Obj.Hom {𝓐 : ChartAtlas G U R} (x y : 𝓐.Obj) where
  /-- The underlying overlap arrow. -/
  arrow : R x.chart y.chart
  /-- Source compatibility of the overlap arrow. -/
  src_arrow : 𝓐.src arrow = x.point
  /-- Target compatibility of the overlap arrow. -/
  tgt_arrow : 𝓐.tgt arrow = y.point

attribute [simp] Obj.Hom.src_arrow Obj.Hom.tgt_arrow

/-- The presenting groupoid structure on `𝓐.Obj`. -/
instance instGroupoidObj : Groupoid 𝓐.Obj where
  Hom := Obj.Hom
  id x := ⟨𝓐.unit x.chart x.point, 𝓐.src_unit _ _, 𝓐.tgt_unit _ _⟩
  comp f g := ⟨𝓐.comp f.arrow g.arrow (f.tgt_arrow.trans g.src_arrow.symm),
    (𝓐.src_comp _ _ _).trans f.src_arrow, (𝓐.tgt_comp _ _ _).trans g.tgt_arrow⟩
  inv f := ⟨𝓐.inv f.arrow, (𝓐.src_inv _).trans f.tgt_arrow, (𝓐.tgt_inv _).trans f.src_arrow⟩
  id_comp _ := Obj.Hom.ext (𝓐.unit_comp _ _ _)
  comp_id _ := Obj.Hom.ext (𝓐.comp_unit _ _ _)
  assoc _ _ _ := Obj.Hom.ext (𝓐.comp_assoc _ _ _ _ _)
  inv_comp f := Obj.Hom.ext ((𝓐.inv_comp _).trans (congrArg (𝓐.unit _) f.tgt_arrow))
  comp_inv f := Obj.Hom.ext ((𝓐.comp_inv _).trans (congrArg (𝓐.unit _) f.src_arrow))

/-- Extensionality for morphisms in the presenting groupoid `𝓐.Obj`. -/
@[ext] theorem Obj.hom_ext {𝓐 : ChartAtlas G U R} {x y : 𝓐.Obj} {f g : x ⟶ y}
    (h : f.arrow = g.arrow) : f = g := Obj.Hom.ext h

/-- Heterogeneous extensionality for morphisms in `𝓐.Obj`. -/
theorem Obj.Hom.hext {𝓐 : ChartAtlas G U R} {x₁ x₂ y₁ y₂ : 𝓐.Obj} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {f₁ : x₁ ⟶ y₁} {f₂ : x₂ ⟶ y₂} (h : f₁.arrow ≍ f₂.arrow) : f₁ ≍ f₂ := by
  cases hx; cases hy; exact heq_of_eq (Obj.hom_ext (eq_of_heq h))

/-- The underlying overlap arrow of the identity morphism at `x`. -/
@[simp] theorem id_arrow (x : 𝓐.Obj) : (𝟙 x : x ⟶ x).arrow = 𝓐.unit x.chart x.point := (rfl)

/-- The underlying overlap arrow of a composite morphism in `𝓐.Obj`. -/
@[simp] theorem comp_arrow {x y z : 𝓐.Obj} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).arrow = 𝓐.comp f.arrow g.arrow (f.tgt_arrow.trans g.src_arrow.symm) := (rfl)

/-- The underlying overlap arrow of a categorical inverse in `𝓐.Obj`. -/
@[simp] theorem inv_arrow {x y : 𝓐.Obj} (f : x ⟶ y) :
    (CategoryTheory.inv f).arrow = 𝓐.inv f.arrow := by rw [← Groupoid.inv_eq_inv]; rfl

/-- `eqToHom h` in `𝓐.Obj` has the unit overlap arrow at its source transported along `h`. -/
theorem eqToHom_arrow {x y : 𝓐.Obj} (h : x = y) :
    (eqToHom h).arrow = h ▸ 𝓐.unit x.chart x.point := by subst h; rfl

/-- An `eqToHom` morphism within the same chart `i` has underlying arrow `unit i x`. -/
@[simp] theorem eqToHom_mk_arrow {i : ι} {x y : U i} (h : (⟨i, x⟩ : 𝓐.Obj) = ⟨i, y⟩) :
    (eqToHom h).arrow = 𝓐.unit i x := by cases h; rfl

/-- Equivalence between the total arrows of `𝓐.Obj` and `Σ p : ι × ι, R p.1 p.2`. -/
-- `expose, implicit_reducible`: `(𝓐.totalEquiv.symm p).left.chart` and `.right.chart` must reduce.
@[expose, implicit_reducible] def totalEquiv : Quiver.Total 𝓐.Obj ≃ Σ p : ι × ι, R p.1 p.2 where
  toFun a := ⟨(a.left.chart, a.right.chart), a.hom.arrow⟩
  invFun q := ⟨⟨q.1.1, 𝓐.src q.2⟩, ⟨q.1.2, 𝓐.tgt q.2⟩, ⟨q.2, rfl, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨i, x⟩, ⟨j, y⟩, ⟨α, hs, ht⟩⟩
    have key : ∀ (x' : U i) (y' : U j) (f' : (⟨i, x'⟩ : 𝓐.Obj) ⟶ ⟨j, y'⟩),
        x' = x → y' = y → f'.arrow = α →
        (⟨⟨i, x'⟩, ⟨j, y'⟩, f'⟩ : Quiver.Total 𝓐.Obj) = ⟨⟨i, x⟩, ⟨j, y⟩, ⟨α, hs, ht⟩⟩ := by
      rintro _ _ f' rfl rfl h; exact congrArg _ (Obj.Hom.ext h)
    exact key _ _ _ hs ht rfl
  right_inv _ := rfl

/-- `totalEquiv` sends a total arrow to its pair of chart indices and underlying overlap arrow. -/
@[simp] theorem totalEquiv_apply (a : Quiver.Total 𝓐.Obj) :
    𝓐.totalEquiv a = ⟨(a.left.chart, a.right.chart), a.hom.arrow⟩ := (rfl)

/-- The source of `totalEquiv.symm ⟨(i, j), α⟩` is `⟨i, src α⟩`. -/
@[simp] theorem totalEquiv_symm_apply_left (p : Σ q : ι × ι, R q.1 q.2) :
    (𝓐.totalEquiv.symm p).left = ⟨p.1.1, 𝓐.src p.2⟩ := (rfl)

/-- The target of `totalEquiv.symm ⟨(i, j), α⟩` is `⟨j, tgt α⟩`. -/
@[simp] theorem totalEquiv_symm_apply_right (p : Σ q : ι × ι, R q.1 q.2) :
    (𝓐.totalEquiv.symm p).right = ⟨p.1.2, 𝓐.tgt p.2⟩ := (rfl)

/-- The underlying overlap arrow of `totalEquiv.symm ⟨(i, j), α⟩` is `α`. -/
@[simp] theorem totalEquiv_symm_apply_hom_arrow (p : Σ q : ι × ι, R q.1 q.2) :
    (𝓐.totalEquiv.symm p).hom.arrow = p.2 := (rfl)

/-- Canonical inclusion `ActionCategory (G i) (U i) ⥤ 𝓐.Obj` of chart `i`, retaining labels. -/
-- `expose, implicit_reducible`: `((𝓐.chartFunctor i).obj a).chart` must reduce to `i`.
@[expose, implicit_reducible] def chartFunctor (i : ι) : ActionCategory (G i) (U i) ⥤ 𝓐.Obj where
  obj a := ⟨i, a.back⟩
  map {a _} f := ⟨(f.hom : G i) • 𝓐.unit i a.back, (𝓐.src_smul _ _).trans (𝓐.src_unit _ _),
    (𝓐.tgt_smul _ _).trans ((congrArg ((f.hom : G i) • ·) (𝓐.tgt_unit _ _)).trans f.map_val)⟩
  map_id a := Obj.Hom.ext (one_smul (G i) (𝓐.unit i a.back))
  map_comp {a b _} f g := Obj.Hom.ext <| by
    have hf : (f.hom : G i) • a.back = b.back := ActionCategory.hom_smul f
    exact (congrArg (· • 𝓐.unit i a.back) (ActionCategory.comp_hom f g)).trans <|
      (𝓐.smul_unit_comp_smul_unit g.hom f.hom a.back (by simp)).symm.trans
        (𝓐.comp_congr rfl (congrArg ((g.hom : G i) • 𝓐.unit i ·) hf) _ _)

/-- `chartFunctor i` sends an object `a` of the action category to `⟨i, a.back⟩`. -/
@[simp] theorem chartFunctor_obj (i : ι) (a : ActionCategory (G i) (U i)) :
    (𝓐.chartFunctor i).obj a = ⟨i, a.back⟩ := (rfl)

/-- `chartFunctor i` maps an arrow labelled `g` at `a` to `g • unit i a.back`. -/
@[simp] theorem chartFunctor_map_arrow (i : ι) {a b : ActionCategory (G i) (U i)} (f : a ⟶ b) :
    ((𝓐.chartFunctor i).map f).arrow = (f.hom : G i) • 𝓐.unit i a.back := (rfl)

/-- Each chart inclusion `chartFunctor i` is faithful, keeping every group label distinct. -/
instance instFaithfulChartFunctor (i : ι) : (𝓐.chartFunctor i).Faithful where
  map_injective {a _} _ f₂ h := Functor.Elements.hom_ext <|
    (𝓐.existsUnique_smul_eq (𝓐.unit i a.back) ((f₂.hom : G i) • 𝓐.unit i a.back)
      (𝓐.src_smul _ _).symm).unique (congrArg Obj.Hom.arrow h) rfl

/-- Each chart inclusion `chartFunctor i` is full: every arrow in `R i i` comes from `G i`. -/
instance instFullChartFunctor (i : ι) : (𝓐.chartFunctor i).Full where
  map_surjective {a b} m := by
    obtain ⟨g, hg, -⟩ :=
      𝓐.existsUnique_smul_eq (𝓐.unit i a.back) m.arrow ((𝓐.src_unit i _).trans m.src_arrow.symm)
    have hgx : g • a.back = b.back := by
      calc g • a.back = 𝓐.tgt (g • 𝓐.unit i a.back) := by simp
        _ = b.back := by rw [hg, m.tgt_arrow]; rfl
    exact ⟨Functor.Elements.homMk g hgx, Obj.Hom.ext hg⟩

/-- On total arrows, `chartFunctor i` acts as `diagEquiv i` followed by `(i, i)`-inclusion. -/
theorem totalEquiv_mapTotal_chartFunctor (i : ι) (p : G i × U i) :
    𝓐.totalEquiv ((𝓐.chartFunctor i).toPrefunctor.mapTotal
      ((ActionCategory.totalEquiv (G i) (U i)).symm p)) = ⟨(i, i), 𝓐.diagEquiv i p⟩ := by
  dsimp [Prefunctor.mapTotal, chartFunctor]; simp [ActionCategory.objEquiv]

/-- Translating the unit at `x` by `h : stabilizer (G i) x` gives a loop at `x`. -/
theorem tgt_smul_unit_of_stabilizer {i : ι} {x : U i} (h : stabilizer (G i) x) :
    𝓐.tgt ((h : G i) • 𝓐.unit i x) = x :=
  (𝓐.tgt_smul _ _).trans ((congrArg _ (𝓐.tgt_unit _ _)).trans h.2)

/-- The stabilizer `stabilizer (G i) x` is canonically isomorphic to `Aut ⟨i, x⟩` in `𝓐.Obj`. -/
noncomputable def stabilizerMulEquivAutObj (i : ι) (x : U i) :
    stabilizer (G i) x ≃* Aut (⟨i, x⟩ : 𝓐.Obj) :=
  ActionCategory.stabilizerMulEquivAutOfFullyFaithful (𝓐.chartFunctor i)
    ((𝓐.chartFunctor_obj i _).trans (congrArg (Obj.mk i) (ActionCategory.coe_back (M := G i) x)))

/-- Forward arrow of `stabilizerMulEquivAutObj i x h` in `R i i`. -/
@[simp] theorem stabilizerMulEquivAutObj_hom_arrow (i : ι) (x : U i) (h : stabilizer (G i) x) :
    (𝓐.stabilizerMulEquivAutObj i x h).asIso.hom.arrow = (h : G i) • 𝓐.unit i x := by
  have hback : (ActionCategory.objEquiv (G i) (U i) x).back = x := ActionCategory.coe_back x
  have hcu (hc) : 𝓐.comp ((h : G i) • 𝓐.unit i x) (𝓐.unit i x) hc = _ := 𝓐.comp_unit _ _ hc
  simp [stabilizerMulEquivAutObj, hback, hcu]

/-- Inverse arrow of `stabilizerMulEquivAutObj i x h` in `R i i`. -/
@[simp] theorem stabilizerMulEquivAutObj_inv_arrow (i : ι) (x : U i) (h : stabilizer (G i) x) :
    (𝓐.stabilizerMulEquivAutObj i x h).asIso.inv.arrow = (h : G i)⁻¹ • 𝓐.unit i x := by
  have hback : (ActionCategory.objEquiv (G i) (U i) x).back = x := ActionCategory.coe_back x
  have hcu (hc) : 𝓐.comp ((h : G i)⁻¹ • 𝓐.unit i x) (𝓐.unit i x) hc = _ := 𝓐.comp_unit _ _ hc
  simp [stabilizerMulEquivAutObj, hback, hcu]

/-- `(stabilizerMulEquivAutObj i x).symm` extracts the `G i`-coordinate via `diagEquiv i`. -/
@[simp] theorem coe_stabilizerMulEquivAutObj_symm_apply (i : ι) (x : U i)
    (e : Aut (⟨i, x⟩ : 𝓐.Obj)) : ((𝓐.stabilizerMulEquivAutObj i x).symm e : G i) =
      ((𝓐.diagEquiv i).symm e.asIso.hom.arrow).1 := by
  have hg := congrArg (fun a : Aut (⟨i, x⟩ : 𝓐.Obj) ↦ a.asIso.hom.arrow)
    ((𝓐.stabilizerMulEquivAutObj i x).apply_symm_apply e)
  rw [stabilizerMulEquivAutObj_hom_arrow] at hg; simp [← hg]

/-- **Stabilizer conjugation** along `α : R i j`, retaining all ineffective elements. -/
noncomputable def stabilizerConj {i j : ι} (α : R i j) :
    stabilizer (G i) (𝓐.src α) ≃* stabilizer (G j) (𝓐.tgt α) :=
  (𝓐.stabilizerMulEquivAutObj i (𝓐.src α)).trans <| (Aut.autMulEquivOfIso
    ((Groupoid.isoEquivHom (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟨j, 𝓐.tgt α⟩).symm ⟨α, rfl, rfl⟩)).trans
    (𝓐.stabilizerMulEquivAutObj j (𝓐.tgt α)).symm

/-- Defining intertwining equation of `stabilizerConj`. -/
theorem stabilizerConj_smul {i j : ι} (α : R i j) (h : stabilizer (G i) (𝓐.src α)) :
    (𝓐.stabilizerConj α h : G j) • α =
      𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h) := by
  set g := 𝓐.stabilizerConj α h
  let f : (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟶ ⟨j, 𝓐.tgt α⟩ := ⟨α, rfl, rfl⟩
  have haut : 𝓐.stabilizerMulEquivAutObj j (𝓐.tgt α) g =
      Aut.autMulEquivOfIso ((Groupoid.isoEquivHom _ _).symm f)
        (𝓐.stabilizerMulEquivAutObj i (𝓐.src α) h) := by simp [g, f, stabilizerConj]
  have hmor : f ≫ (𝓐.stabilizerMulEquivAutObj j (𝓐.tgt α) g).asIso.hom =
      (𝓐.stabilizerMulEquivAutObj i (𝓐.src α) h).asIso.hom ≫ f := by
    simp [haut, f, Aut.autMulEquivOfIso]
  simpa [f, comp_smul_unit_tgt] using congrArg Obj.Hom.arrow hmor

/-- Characterization of `stabilizerConj α h` by its postcomposition action on `α`. -/
theorem stabilizerConj_eq_iff {i j : ι} (α : R i j) (h : stabilizer (G i) (𝓐.src α))
    (g : stabilizer (G j) (𝓐.tgt α)) : 𝓐.stabilizerConj α h = g ↔ (g : G j) • α =
      𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h) :=
  ⟨by rintro rfl; exact 𝓐.stabilizerConj_smul α h, fun hg ↦
    Subtype.ext ((𝓐.existsUnique_smul_eq α _ (by simp)).unique (𝓐.stabilizerConj_smul α h) hg)⟩

/-- Stabilizer conjugation along a unit arrow is the identity on stabilizers. -/
@[simp] theorem coe_stabilizerConj_unit (i : ι) (x : U i)
    (h : stabilizer (G i) (𝓐.src (𝓐.unit i x))) : (𝓐.stabilizerConj (𝓐.unit i x) h : G i) = h :=
  congrArg Subtype.val ((𝓐.stabilizerConj_eq_iff _ h ⟨h, by simpa using h.2⟩).mpr (by simp))

/-- Stabilizer conjugation along a composite arrow is the composite of the conjugations. -/
theorem coe_stabilizerConj_comp {i j k : ι} (α : R i j) (β : R j k) (hab : 𝓐.tgt α = 𝓐.src β)
    (h : stabilizer (G i) (𝓐.src (𝓐.comp α β hab))) :
    (𝓐.stabilizerConj (𝓐.comp α β hab) h : G k) =
      𝓐.stabilizerConj β ⟨𝓐.stabilizerConj α ⟨h, by simpa using h.2⟩,
        by rw [mem_stabilizer_iff, ← hab]; exact (𝓐.stabilizerConj α _).2⟩ := by
  set h' : stabilizer (G i) (𝓐.src α) := ⟨h, by simpa using h.2⟩
  set u := 𝓐.stabilizerConj α h'; set u' : stabilizer (G j) (𝓐.src β) := ⟨u, hab ▸ u.2⟩
  set v := 𝓐.stabilizerConj β u'
  have hu_tgt : 𝓐.tgt ((u : G j) • α) = 𝓐.src β :=
    (𝓐.tgt_smul _ _).trans ((mem_stabilizer_iff.mp u.2).trans hab)
  refine congrArg Subtype.val ((𝓐.stabilizerConj_eq_iff _ h ⟨(v : G k), by simp⟩).mpr ?_)
  calc (v : G k) • 𝓐.comp α β hab
      = 𝓐.comp α ((v : G k) • β) (hab.trans (𝓐.src_smul _ β).symm) := (𝓐.comp_smul _ _ _ _).symm
    _ = 𝓐.comp α (𝓐.comp ((u : G j) • 𝓐.unit j (𝓐.src β)) β (𝓐.tgt_smul_unit_of_stabilizer u'))
          (by simpa using hab) := 𝓐.comp_congr rfl (𝓐.stabilizerConj_smul β u') _ _
    _ = 𝓐.comp (𝓐.comp α ((u : G j) • 𝓐.unit j (𝓐.tgt α)) (by simp)) β (by simpa using hu_tgt) :=
        (𝓐.comp_assoc _ _ _ (by simpa using hab) _).symm.trans
          (𝓐.comp_congr (𝓐.comp_congr rfl (congrArg ((u : G j) • 𝓐.unit j ·) hab.symm) _ _) rfl _ _)
    _ = 𝓐.comp ((u : G j) • α) β hu_tgt := 𝓐.comp_congr (𝓐.comp_smul_unit_tgt α u _) rfl _ _
    _ = 𝓐.comp (𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h')) β
          (by simpa using hab) := 𝓐.comp_congr (𝓐.stabilizerConj_smul α h') rfl _ _
    _ = 𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src (𝓐.comp α β hab))) (𝓐.comp α β hab)
          (𝓐.tgt_smul_unit_of_stabilizer h) :=
        (𝓐.comp_assoc _ _ _ _ hab).trans (𝓐.comp_congr (by simp) rfl _ _)

/-- Stabilizer conjugation along an inverse arrow is the inverse isomorphism on stabilizers. -/
@[simp] theorem coe_stabilizerConj_inv {i j : ι} (α : R i j)
    (h : stabilizer (G j) (𝓐.src (𝓐.inv α))) : (𝓐.stabilizerConj (𝓐.inv α) h : G i) =
      (𝓐.stabilizerConj α).symm ⟨h, by simpa using h.2⟩ := by
  set u := (𝓐.stabilizerConj α).symm ⟨h, by simpa using h.2⟩
  have hu : (𝓐.stabilizerConj α u : G j) = h :=
    congrArg Subtype.val ((𝓐.stabilizerConj α).apply_symm_apply _)
  have hunit : ∀ (γ : R i i), γ = 𝓐.unit i (𝓐.src α) →
      ∀ z : stabilizer (G i) (𝓐.src γ), (𝓐.stabilizerConj γ z : G i) = z := by
    rintro _ rfl z; exact 𝓐.coe_stabilizerConj_unit i (𝓐.src α) z
  have hc := 𝓐.coe_stabilizerConj_comp α (𝓐.inv α) (𝓐.src_inv α).symm ⟨u, by simp⟩
  exact (congrArg (fun z ↦ (𝓐.stabilizerConj (𝓐.inv α) z : G i)) (Subtype.ext hu.symm)).trans
    (hc.symm.trans (hunit _ (𝓐.comp_inv α) _))

/-- Translating an overlap arrow `α` by `g : G j` conjugates `stabilizerConj α` by `g`. -/
theorem coe_stabilizerConj_smul {i j : ι} (g : G j) (α : R i j)
    (h : stabilizer (G i) (𝓐.src (g • α))) : (𝓐.stabilizerConj (g • α) h : G j) =
      stabilizerEquivStabilizer (𝓐.tgt_smul g α) (𝓐.stabilizerConj α ⟨h, by simpa using h.2⟩) := by
  set h' : stabilizer (G i) (𝓐.src α) := ⟨h, by simpa using h.2⟩
  set u := 𝓐.stabilizerConj α h'; set w := stabilizerEquivStabilizer (𝓐.tgt_smul g α) u
  refine congrArg Subtype.val ((𝓐.stabilizerConj_eq_iff (g • α) h w).mpr ?_)
  have hconj : (w : G j) = g * (u : G j) * g⁻¹ := by
    simp [w, stabilizerEquivStabilizer_apply, MulAut.conj_apply]
  calc (w : G j) • (g • α)
      = g • ((u : G j) • α) := by rw [hconj, smul_smul, inv_mul_cancel_right, mul_smul]
    _ = g • 𝓐.comp ((h' : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h') := by
        rw [𝓐.stabilizerConj_smul α h']
    _ = 𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src (g • α))) (g • α)
          (𝓐.tgt_smul_unit_of_stabilizer h) := by
        rw [← 𝓐.comp_smul]; exact 𝓐.comp_congr (by simp [h']) rfl _ _

end SingleAtlas

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  {κ : Type v₁} {G' : κ → Type v₂} [∀ k, Group (G' k)]
  {U' : κ → Type v₃} [∀ k, MulAction (G' k) (U' k)]
  {R' : κ → κ → Type v₄} [∀ k l, MulAction (G' l) (R' k l)]

/-- A morphism between retained-arrow chart atlases `𝓐` and `𝓑`: chart reindexing `index`, group
homomorphisms `groupHom i : G i →* G' (index i)`, point maps `obj i : U i → U' (index i)`, and
overlap-arrow maps `map : R i j → R' (index i) (index j)` preserving the atlas structure. -/
structure Hom (𝓐 : ChartAtlas G U R) (𝓑 : ChartAtlas G' U' R') where
  /-- Reindexing map on charts. -/
  index : ι → κ
  /-- Group homomorphisms on chart groups. -/
  groupHom : ∀ i, G i →* G' (index i)
  /-- Point maps on chart domains. -/
  obj : ∀ i, U i → U' (index i)
  /-- Maps on overlap-arrow types. -/
  map : ∀ {i j}, R i j → R' (index i) (index j)
  /-- Source compatibility of `map`. -/
  src_map : ∀ {i j} (α : R i j), 𝓑.src (map α) = obj i (𝓐.src α)
  /-- Target compatibility of `map`. -/
  tgt_map : ∀ {i j} (α : R i j), 𝓑.tgt (map α) = obj j (𝓐.tgt α)
  /-- Preservation of unit overlap arrows. -/
  map_unit : ∀ i (x : U i), map (𝓐.unit i x) = 𝓑.unit (index i) (obj i x)
  /-- Preservation of overlap-arrow composition. -/
  map_comp : ∀ {i j k} (α : R i j) (β : R j k) (h : 𝓐.tgt α = 𝓐.src β),
    map (𝓐.comp α β h) = 𝓑.comp (map α) (map β)
      ((tgt_map α).trans ((congrArg (obj j) h).trans (src_map β).symm))
  /-- Equivariance of `map` with respect to `groupHom`. -/
  map_smul : ∀ {i j} (g : G j) (α : R i j), map (g • α) = groupHom j g • map α

namespace Hom

variable {𝓐 : ChartAtlas G U R} {𝓑 : ChartAtlas G' U' R'}

attribute [simp] src_map tgt_map map_unit map_smul

/-- Extensionality for atlas morphisms; `obj` is determined by `index` and `map` on units. -/
@[ext] theorem ext {Φ Ψ : 𝓐.Hom 𝓑} (hindex : Φ.index = Ψ.index)
    (hgroup : ∀ i, HEq (Φ.groupHom i) (Ψ.groupHom i))
    (hmap : ∀ {i j} (α : R i j), HEq (Φ.map α) (Ψ.map α)) : Φ = Ψ := by
  obtain ⟨idx₁, grp₁, obj₁, map₁, hsrc₁, _, _, _, _⟩ := Φ
  obtain ⟨idx₂, grp₂, obj₂, map₂, hsrc₂, _, _, _, _⟩ := Ψ
  dsimp only at hindex hgroup hmap; subst hindex
  obtain rfl : grp₁ = grp₂ := funext fun i ↦ eq_of_heq (hgroup i)
  obtain rfl : @map₁ = @map₂ := funext fun _ ↦ funext fun _ ↦ funext fun α ↦ eq_of_heq (hmap α)
  obtain rfl : obj₁ = obj₂ := funext fun i ↦ funext fun x ↦ by
    simpa using (hsrc₁ (𝓐.unit i x)).symm.trans (hsrc₂ (𝓐.unit i x))
  rfl

/-- Each chart map `Φ.obj i` is automatically `Φ.groupHom i`-equivariant. -/
@[simp] theorem obj_smul (Φ : 𝓐.Hom 𝓑) (i : ι) (g : G i) (x : U i) :
    Φ.obj i (g • x) = Φ.groupHom i g • Φ.obj i x := by
  calc Φ.obj i (g • x) = Φ.obj i (𝓐.tgt (g • 𝓐.unit i x)) := by simp
    _ = 𝓑.tgt (Φ.map (g • 𝓐.unit i x)) := (Φ.tgt_map _).symm
    _ = Φ.groupHom i g • Φ.obj i x := by simp

/-- The identity morphism on a chart atlas `𝓐`. -/
-- `expose, implicit_reducible`: `(Hom.id 𝓐).index` must reduce in dependent chart types.
@[expose, implicit_reducible] def id (𝓐 : ChartAtlas G U R) : 𝓐.Hom 𝓐 :=
  ⟨_root_.id, fun i ↦ MonoidHom.id (G i), fun _ ↦ _root_.id, fun α ↦ α, fun _ ↦ rfl, fun _ ↦ rfl,
    fun _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- The index map of `Hom.id 𝓐` is the identity. -/
@[simp] theorem id_index (𝓐 : ChartAtlas G U R) : (Hom.id 𝓐).index = _root_.id := (rfl)

/-- The group homomorphism of `Hom.id 𝓐` on chart `i` is `MonoidHom.id (G i)`. -/
@[simp] theorem id_groupHom (𝓐 : ChartAtlas G U R) (i : ι) :
    (Hom.id 𝓐).groupHom i = MonoidHom.id (G i) := (rfl)

/-- `Hom.id 𝓐` acts as the identity on chart points. -/
@[simp] theorem id_obj (𝓐 : ChartAtlas G U R) (i : ι) (x : U i) : (Hom.id 𝓐).obj i x = x := (rfl)

/-- `Hom.id 𝓐` acts as the identity on overlap arrows. -/
@[simp] theorem id_map (𝓐 : ChartAtlas G U R) {i j : ι} (α : R i j) : (Hom.id 𝓐).map α = α := (rfl)

/-- The functor `𝓐.Obj ⥤ 𝓑.Obj` between presenting groupoids induced by an atlas morphism `Φ`. -/
-- `expose, implicit_reducible`: `(Φ.toFunctor.obj x).chart` must reduce to `Φ.index x.chart`.
@[expose, implicit_reducible] def toFunctor (Φ : 𝓐.Hom 𝓑) : 𝓐.Obj ⥤ 𝓑.Obj where
  obj x := ⟨Φ.index x.chart, Φ.obj x.chart x.point⟩
  map f := ⟨Φ.map f.arrow, (Φ.src_map _).trans (congrArg _ f.src_arrow),
    (Φ.tgt_map _).trans (congrArg _ f.tgt_arrow)⟩
  map_id x := Obj.Hom.ext (Φ.map_unit x.chart x.point)
  map_comp f g := Obj.Hom.ext (Φ.map_comp f.arrow g.arrow _)

/-- `Φ.toFunctor` sends `⟨i, x⟩` to `⟨Φ.index i, Φ.obj i x⟩`. -/
@[simp] theorem toFunctor_obj (Φ : 𝓐.Hom 𝓑) (x : 𝓐.Obj) :
    Φ.toFunctor.obj x = ⟨Φ.index x.chart, Φ.obj x.chart x.point⟩ := (rfl)

/-- `Φ.toFunctor` applies `Φ.map` to the underlying overlap arrow. -/
@[simp] theorem toFunctor_map_arrow (Φ : 𝓐.Hom 𝓑) {x y : 𝓐.Obj} (f : x ⟶ y) :
    (Φ.toFunctor.map f).arrow = Φ.map f.arrow := (rfl)

/-- An atlas morphism preserves inverses of overlap arrows. -/
@[simp] theorem map_inv (Φ : 𝓐.Hom 𝓑) {i j : ι} (α : R i j) :
    Φ.map (𝓐.inv α) = 𝓑.inv (Φ.map α) := by
  have h := congrArg Obj.Hom.arrow
    (Φ.toFunctor.map_inv (⟨α, rfl, rfl⟩ : (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟶ ⟨j, 𝓐.tgt α⟩))
  rwa [toFunctor_map_arrow, inv_arrow, inv_arrow, toFunctor_map_arrow] at h

/-- The identity atlas morphism induces the identity functor on `𝓐.Obj`. -/
@[simp] theorem toFunctor_id (𝓐 : ChartAtlas G U R) : (Hom.id 𝓐).toFunctor = 𝟭 𝓐.Obj := (rfl)

variable {μ : Type*} {G'' : μ → Type*} [∀ m, Group (G'' m)]
  {U'' : μ → Type*} [∀ m, MulAction (G'' m) (U'' m)]
  {R'' : μ → μ → Type*} [∀ m n, MulAction (G'' n) (R'' m n)]
  {𝓒 : ChartAtlas G'' U'' R''}

/-- Composition of morphisms of chart atlases. -/
-- `expose, implicit_reducible`: `(Ψ.comp Φ).index` must reduce in dependent chart types.
@[expose, implicit_reducible] def comp (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) : 𝓐.Hom 𝓒 :=
  ⟨Ψ.index ∘ Φ.index, fun i ↦ (Ψ.groupHom (Φ.index i)).comp (Φ.groupHom i),
    fun i ↦ Ψ.obj (Φ.index i) ∘ Φ.obj i, fun α ↦ Ψ.map (Φ.map α),
    fun α ↦ (Ψ.src_map _).trans (congrArg (Ψ.obj _) (Φ.src_map α)),
    fun α ↦ (Ψ.tgt_map _).trans (congrArg (Ψ.obj _) (Φ.tgt_map α)),
    fun i x ↦ (congrArg Ψ.map (Φ.map_unit i x)).trans (Ψ.map_unit _ _),
    fun α β h ↦ (congrArg Ψ.map (Φ.map_comp α β h)).trans (Ψ.map_comp _ _ _),
    fun g α ↦ (congrArg Ψ.map (Φ.map_smul g α)).trans (Ψ.map_smul _ _)⟩

/-- The index map of a composite atlas morphism is the composite of the index maps. -/
@[simp] theorem comp_index (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) :
    (Ψ.comp Φ).index = Ψ.index ∘ Φ.index := (rfl)

/-- The group homomorphism of a composite atlas morphism is the composite group homomorphism. -/
@[simp] theorem comp_groupHom (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) (i : ι) :
    (Ψ.comp Φ).groupHom i = (Ψ.groupHom (Φ.index i)).comp (Φ.groupHom i) := (rfl)

/-- Evaluation of a composite atlas morphism on chart points. -/
@[simp] theorem comp_obj (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) (i : ι) (x : U i) :
    (Ψ.comp Φ).obj i x = Ψ.obj (Φ.index i) (Φ.obj i x) := (rfl)

/-- Evaluation of a composite atlas morphism on overlap arrows. -/
@[simp] theorem comp_map (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) {i j : ι} (α : R i j) :
    (Ψ.comp Φ).map α = Ψ.map (Φ.map α) := (rfl)

/-- Left identity law for composition of chart-atlas morphisms. -/
@[simp] theorem id_comp (Φ : 𝓐.Hom 𝓑) : (Hom.id 𝓑).comp Φ = Φ :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.id_comp _)) (fun _ ↦ HEq.rfl)

/-- Right identity law for composition of chart-atlas morphisms. -/
@[simp] theorem comp_id (Φ : 𝓐.Hom 𝓑) : Φ.comp (Hom.id 𝓐) = Φ :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.comp_id _)) (fun _ ↦ HEq.rfl)

/-- Associativity of composition of chart-atlas morphisms. -/
theorem comp_assoc {ν : Type*} {G''' : ν → Type*} [∀ n, Group (G''' n)]
    {U''' : ν → Type*} [∀ n, MulAction (G''' n) (U''' n)]
    {R''' : ν → ν → Type*} [∀ m n, MulAction (G''' n) (R''' m n)]
    {𝓓 : ChartAtlas G''' U''' R'''} (Θ : 𝓒.Hom 𝓓) (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) :
    (Θ.comp Ψ).comp Φ = Θ.comp (Ψ.comp Φ) :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.comp_assoc _ _ _)) (fun _ ↦ HEq.rfl)

/-- Composition of atlas morphisms induces composition of presenting-groupoid functors. -/
@[simp] theorem toFunctor_comp (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) :
    (Ψ.comp Φ).toFunctor = Φ.toFunctor ⋙ Ψ.toFunctor := (rfl)

/-- An atlas morphism intertwines the chart inclusion functors via `ActionCategory.map`. -/
theorem chartFunctor_comp_toFunctor (Φ : 𝓐.Hom 𝓑) (i : ι) :
    𝓐.chartFunctor i ⋙ Φ.toFunctor =
      ActionCategory.map (Φ.groupHom i) ⟨Φ.obj i, Φ.obj_smul i⟩ ⋙ 𝓑.chartFunctor (Φ.index i) := by
  let f : U i →ₑ[Φ.groupHom i] U' (Φ.index i) := ⟨Φ.obj i, Φ.obj_smul i⟩
  have hobj (a : ActionCategory (G i) (U i)) :
      (𝓐.chartFunctor i ⋙ Φ.toFunctor).obj a =
        (ActionCategory.map (Φ.groupHom i) f ⋙ 𝓑.chartFunctor (Φ.index i)).obj a :=
    congrArg (Obj.mk (Φ.index i)) (ActionCategory.back_map_obj (Φ.groupHom i) f a).symm
  refine CategoryTheory.Functor.hext hobj fun a b m ↦
    Obj.Hom.hext (hobj a) (hobj b) (heq_of_eq ?_)
  have hcoe (x : U i) : f x = Φ.obj i x := rfl
  dsimp [chartFunctor, toFunctor]; simp [f, hcoe]

/-- `Φ.toFunctor` is faithful iff `Φ.map` is injective on arrows sharing endpoints. -/
theorem faithful_toFunctor_iff (Φ : 𝓐.Hom 𝓑) : Φ.toFunctor.Faithful ↔
    ∀ {i j : ι} (α β : R i j), 𝓐.src α = 𝓐.src β → 𝓐.tgt α = 𝓐.tgt β →
      Φ.map α = Φ.map β → α = β :=
  ⟨fun h _ _ α β hs ht hmap ↦ by
    have : Φ.toFunctor.Faithful := h
    exact congrArg Obj.Hom.arrow (Φ.toFunctor.map_injective
      (a₁ := (⟨α, rfl, rfl⟩ : (⟨_, 𝓐.src α⟩ : 𝓐.Obj) ⟶ ⟨_, 𝓐.tgt α⟩))
      (a₂ := ⟨β, hs.symm, ht.symm⟩) (Obj.Hom.ext hmap)),
    fun h ↦ ⟨fun {_ _} f₁ f₂ hm ↦ Obj.Hom.ext <| h f₁.arrow f₂.arrow
      (f₁.src_arrow.trans f₂.src_arrow.symm) (f₁.tgt_arrow.trans f₂.tgt_arrow.symm)
      (congrArg Obj.Hom.arrow hm)⟩⟩

/-- `Φ.toFunctor` is full iff every overlap arrow between image points lifts to `𝓐`. -/
theorem full_toFunctor_iff (Φ : 𝓐.Hom 𝓑) : Φ.toFunctor.Full ↔
    ∀ {i j : ι} (x : U i) (y : U j) (β : R' (Φ.index i) (Φ.index j)),
      𝓑.src β = Φ.obj i x → 𝓑.tgt β = Φ.obj j y →
        ∃ α : R i j, 𝓐.src α = x ∧ 𝓐.tgt α = y ∧ Φ.map α = β :=
  ⟨fun h _ _ x y β hs ht ↦ by
    have : Φ.toFunctor.Full := h
    obtain ⟨f, hf⟩ := Φ.toFunctor.map_surjective
      (⟨β, hs, ht⟩ : Φ.toFunctor.obj ⟨_, x⟩ ⟶ Φ.toFunctor.obj ⟨_, y⟩)
    exact ⟨f.arrow, f.src_arrow, f.tgt_arrow, congrArg Obj.Hom.arrow hf⟩,
    fun h ↦ ⟨fun {x y} g ↦
      let ⟨α, hs, ht, hm⟩ := h x.point y.point g.arrow g.src_arrow g.tgt_arrow
      ⟨⟨α, hs, ht⟩, Obj.Hom.ext hm⟩⟩⟩

/-- `Φ.toFunctor` is essentially surjective iff every point in `𝓑` receives an arrow from `Φ`. -/
theorem essSurj_toFunctor_iff (Φ : 𝓐.Hom 𝓑) : Φ.toFunctor.EssSurj ↔
    ∀ (k : κ) (y : U' k), ∃ (i : ι) (x : U i) (β : R' (Φ.index i) k),
      𝓑.src β = Φ.obj i x ∧ 𝓑.tgt β = y :=
  ⟨fun h k y ↦ let ⟨z, ⟨e⟩⟩ := h.mem_essImage ⟨k, y⟩
    ⟨z.chart, z.point, e.hom.arrow, e.hom.src_arrow, e.hom.tgt_arrow⟩,
    fun h ↦ ⟨fun y ↦ let ⟨i, x, β, hs, ht⟩ := h y.chart y.point
      ⟨⟨i, x⟩, ⟨(Groupoid.isoEquivHom _ _).symm ⟨β, hs, ht⟩⟩⟩⟩⟩

end Hom

/-- A natural transformation between `Φ Ψ : 𝓐.Hom 𝓑`: overlap arrows `app i x` from `Φ.obj i x` to
`Ψ.obj i x` in `𝓑` commuting with all overlap arrows of `𝓐`. -/
@[ext] structure NatTrans {𝓐 : ChartAtlas G U R} {𝓑 : ChartAtlas G' U' R'} (Φ Ψ : 𝓐.Hom 𝓑) where
  /-- Component overlap arrow at `x : U i`. -/
  app : ∀ (i : ι), U i → R' (Φ.index i) (Ψ.index i)
  /-- Source of `app i x` is `Φ.obj i x`. -/
  src_app : ∀ (i : ι) (x : U i), 𝓑.src (app i x) = Φ.obj i x
  /-- Target of `app i x` is `Ψ.obj i x`. -/
  tgt_app : ∀ (i : ι) (x : U i), 𝓑.tgt (app i x) = Ψ.obj i x
  /-- Naturality square in `𝓑` for every overlap arrow `α : R i j` in `𝓐`. -/
  naturality : ∀ {i j : ι} (α : R i j),
    𝓑.comp (Φ.map α) (app j (𝓐.tgt α)) ((Φ.tgt_map α).trans (src_app j _).symm) =
      𝓑.comp (app i (𝓐.src α)) (Ψ.map α) ((tgt_app i _).trans (Ψ.src_map α).symm)

namespace NatTrans

variable {𝓐 : ChartAtlas G U R} {𝓑 : ChartAtlas G' U' R'}

attribute [simp] src_app tgt_app

/-- The categorical natural transformation `Φ.toFunctor ⟶ Ψ.toFunctor` induced by `η`. -/
def toNatTrans {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : Φ.toFunctor ⟶ Ψ.toFunctor where
  app x := ⟨η.app x.chart x.point, η.src_app _ _, η.tgt_app _ _⟩
  naturality {x y} f := Obj.Hom.ext <|
    (𝓑.comp_congr rfl (congrArg (η.app y.chart) f.tgt_arrow.symm) _ _).trans
      ((η.naturality f.arrow).trans (𝓑.comp_congr (congrArg (η.app x.chart) f.src_arrow) rfl _ _))

/-- Component arrow of `η.toNatTrans` at `x`. -/
@[simp] theorem toNatTrans_app_arrow {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) (x : 𝓐.Obj) :
    (η.toNatTrans.app x).arrow = η.app x.chart x.point := (rfl)

/-- Reconstruct an atlas natural transformation from `τ : Φ.toFunctor ⟶ Ψ.toFunctor`. -/
def ofNatTrans {Φ Ψ : 𝓐.Hom 𝓑} (τ : Φ.toFunctor ⟶ Ψ.toFunctor) : NatTrans Φ Ψ :=
  ⟨fun i x ↦ (τ.app ⟨i, x⟩).arrow, fun i x ↦ (τ.app ⟨i, x⟩).src_arrow,
    fun i x ↦ (τ.app ⟨i, x⟩).tgt_arrow, fun {i j} α ↦ by
      have h := congrArg Obj.Hom.arrow
        (τ.naturality (⟨α, rfl, rfl⟩ : (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟶ ⟨j, 𝓐.tgt α⟩))
      simpa only [comp_arrow, Hom.toFunctor_map_arrow] using h⟩

/-- Component overlap arrow of `ofNatTrans τ`. -/
@[simp] theorem ofNatTrans_app {Φ Ψ : 𝓐.Hom 𝓑} (τ : Φ.toFunctor ⟶ Ψ.toFunctor) (i : ι) (x : U i) :
    (ofNatTrans τ).app i x = (τ.app ⟨i, x⟩).arrow := (rfl)

/-- `ofNatTrans` is a left inverse to `toNatTrans`. -/
@[simp] theorem ofNatTrans_toNatTrans {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) :
    ofNatTrans η.toNatTrans = η := by ext; simp

/-- `ofNatTrans` is a right inverse to `toNatTrans`. -/
@[simp] theorem toNatTrans_ofNatTrans {Φ Ψ : 𝓐.Hom 𝓑} (τ : Φ.toFunctor ⟶ Ψ.toFunctor) :
    (ofNatTrans τ).toNatTrans = τ := by ext x; simp

/-- Equivalence between `NatTrans Φ Ψ` and `Φ.toFunctor ⟶ Ψ.toFunctor`. -/
def toNatTransEquiv (Φ Ψ : 𝓐.Hom 𝓑) : NatTrans Φ Ψ ≃ (Φ.toFunctor ⟶ Ψ.toFunctor) :=
  ⟨toNatTrans, ofNatTrans, ofNatTrans_toNatTrans, toNatTrans_ofNatTrans⟩

/-- `toNatTransEquiv` evaluates as `toNatTrans`. -/
@[simp] theorem toNatTransEquiv_apply {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) :
    toNatTransEquiv Φ Ψ η = η.toNatTrans := (rfl)

/-- `toNatTransEquiv.symm` evaluates as `ofNatTrans`. -/
@[simp] theorem toNatTransEquiv_symm_apply {Φ Ψ : 𝓐.Hom 𝓑} (τ : Φ.toFunctor ⟶ Ψ.toFunctor) :
    (toNatTransEquiv Φ Ψ).symm τ = ofNatTrans τ := (rfl)

/-- Because `𝓑.Obj` is a groupoid, `η` induces a natural isomorphism `Φ.toFunctor ≅ Ψ.toFunctor`. -/
def toNatIso {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : Φ.toFunctor ≅ Ψ.toFunctor :=
  NatIso.ofComponents (fun x ↦ (Groupoid.isoEquivHom _ _).symm (η.toNatTrans.app x))
    fun f ↦ η.toNatTrans.naturality f

/-- The forward natural transformation of `η.toNatIso` is `η.toNatTrans`. -/
@[simp] theorem toNatIso_hom {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) :
    η.toNatIso.hom = η.toNatTrans := by ext x; simp [toNatIso]

/-- The identity natural transformation on an atlas morphism `Φ`. -/
def refl (Φ : 𝓐.Hom 𝓑) : NatTrans Φ Φ :=
  ⟨fun i x ↦ 𝓑.unit (Φ.index i) (Φ.obj i x), fun _ _ ↦ 𝓑.src_unit _ _,
    fun _ _ ↦ 𝓑.tgt_unit _ _, fun _ ↦ by simp⟩

/-- Component overlap arrow of `NatTrans.refl Φ`. -/
@[simp] theorem refl_app (Φ : 𝓐.Hom 𝓑) (i : ι) (x : U i) :
    (refl Φ).app i x = 𝓑.unit (Φ.index i) (Φ.obj i x) := (rfl)

/-- `NatTrans.refl Φ` induces the identity natural transformation on `Φ.toFunctor`. -/
@[simp] theorem toNatTrans_refl (Φ : 𝓐.Hom 𝓑) : (refl Φ).toNatTrans = 𝟙 Φ.toFunctor := by
  ext x; simp [Hom.toFunctor]

/-- The inverse natural transformation of `η : NatTrans Φ Ψ`, formed using `𝓑.inv`. -/
def symm {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : NatTrans Ψ Φ :=
  ⟨fun i x ↦ 𝓑.inv (η.app i x), fun i x ↦ (𝓑.src_inv _).trans (η.tgt_app i x),
    fun i x ↦ (𝓑.tgt_inv _).trans (η.src_app i x),
    fun α ↦ by simpa [toNatIso] using (ofNatTrans η.toNatIso.inv).naturality α⟩

/-- Component overlap arrow of `η.symm`. -/
@[simp] theorem symm_app {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) (i : ι) (x : U i) :
    η.symm.app i x = 𝓑.inv (η.app i x) := (rfl)

/-- The inverse natural transformation of `η.toNatIso` is `η.symm.toNatTrans`. -/
@[simp] theorem toNatIso_inv {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) :
    η.toNatIso.inv = η.symm.toNatTrans := by ext x; simp [toNatIso]

/-- Vertical composition of natural transformations between atlas morphisms. -/
def trans {Φ Ψ Θ : 𝓐.Hom 𝓑} (η₁ : NatTrans Φ Ψ) (η₂ : NatTrans Ψ Θ) : NatTrans Φ Θ :=
  ⟨fun i x ↦ 𝓑.comp (η₁.app i x) (η₂.app i x) ((η₁.tgt_app i x).trans (η₂.src_app i x).symm),
    fun i x ↦ (𝓑.src_comp _ _ _).trans (η₁.src_app i x),
    fun i x ↦ (𝓑.tgt_comp _ _ _).trans (η₂.tgt_app i x),
    fun α ↦ by simpa using (ofNatTrans (η₁.toNatTrans ≫ η₂.toNatTrans)).naturality α⟩

/-- Component overlap arrow of `η₁.trans η₂`. -/
@[simp] theorem trans_app {Φ Ψ Θ : 𝓐.Hom 𝓑} (η₁ : NatTrans Φ Ψ) (η₂ : NatTrans Ψ Θ) (i : ι)
    (x : U i) : (η₁.trans η₂).app i x =
      𝓑.comp (η₁.app i x) (η₂.app i x) ((η₁.tgt_app i x).trans (η₂.src_app i x).symm) := (rfl)

/-- Vertical composition of atlas natural transformations induces `≫` on `toNatTrans`. -/
@[simp] theorem toNatTrans_trans {Φ Ψ Θ : 𝓐.Hom 𝓑} (η₁ : NatTrans Φ Ψ) (η₂ : NatTrans Ψ Θ) :
    (η₁.trans η₂).toNatTrans = η₁.toNatTrans ≫ η₂.toNatTrans := by ext x; simp

/-- Left unit law for vertical composition of atlas natural transformations. -/
@[simp] theorem refl_trans {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : (refl Φ).trans η = η := by ext; simp

/-- Right unit law for vertical composition of atlas natural transformations. -/
@[simp] theorem trans_refl {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : η.trans (refl Ψ) = η := by ext; simp

/-- Right inverse law for vertical composition of atlas natural transformations. -/
@[simp] theorem trans_symm {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : η.trans η.symm = refl Φ := by
  ext; simp

/-- Left inverse law for vertical composition of atlas natural transformations. -/
@[simp] theorem symm_trans {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : η.symm.trans η = refl Ψ := by
  ext; simp

/-- Symmetry of atlas natural transformations is an involution. -/
@[simp] theorem symm_symm {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : η.symm.symm = η := by ext; simp

/-- The inverse of `NatTrans.refl Φ` is itself. -/
@[simp] theorem symm_refl (Φ : 𝓐.Hom 𝓑) : (refl Φ).symm = refl Φ := by ext; simp

/-- Associativity of vertical composition of atlas natural transformations. -/
theorem trans_assoc {Φ Ψ Θ Ξ : 𝓐.Hom 𝓑}
    (η₁ : NatTrans Φ Ψ) (η₂ : NatTrans Ψ Θ) (η₃ : NatTrans Θ Ξ) :
    (η₁.trans η₂).trans η₃ = η₁.trans (η₂.trans η₃) := by ext; simp [ChartAtlas.comp_assoc]

/-- `NatTrans.refl` induces `Iso.refl` on `Φ.toFunctor`. -/
@[simp] theorem toNatIso_refl (Φ : 𝓐.Hom 𝓑) :
    (refl Φ).toNatIso = Iso.refl Φ.toFunctor := by ext1; simp

/-- `NatTrans.symm` induces `Iso.symm` on presenting-groupoid functors. -/
@[simp] theorem toNatIso_symm {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) :
    η.symm.toNatIso = η.toNatIso.symm := by ext1; simp

/-- `NatTrans.trans` induces `Iso.trans` on presenting-groupoid functors. -/
@[simp] theorem toNatIso_trans {Φ Ψ Θ : 𝓐.Hom 𝓑} (η₁ : NatTrans Φ Ψ) (η₂ : NatTrans Ψ Θ) :
    (η₁.trans η₂).toNatIso = η₁.toNatIso ≪≫ η₂.toNatIso := by ext1; simp

variable {μ : Type*} {G'' : μ → Type*} [∀ m, Group (G'' m)]
  {U'' : μ → Type*} [∀ m, MulAction (G'' m) (U'' m)]
  {R'' : μ → μ → Type*} [∀ m n, MulAction (G'' n) (R'' m n)]
  {𝓒 : ChartAtlas G'' U'' R''}

/-- Precompose `η : NatTrans Ψ₁ Ψ₂` along `Φ : 𝓐.Hom 𝓑` (`Functor.whiskerLeft Φ.toFunctor`). -/
def whiskerLeft (Φ : 𝓐.Hom 𝓑) {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒} (η : NatTrans Ψ₁ Ψ₂) :
    NatTrans (Ψ₁.comp Φ) (Ψ₂.comp Φ) :=
  ⟨fun i x ↦ η.app (Φ.index i) (Φ.obj i x), fun i x ↦ η.src_app (Φ.index i) (Φ.obj i x),
    fun i x ↦ η.tgt_app (Φ.index i) (Φ.obj i x), fun α ↦
      (𝓒.comp_congr rfl (congrArg (η.app _) (Φ.tgt_map α).symm) _ _).trans
        ((η.naturality (Φ.map α)).trans (𝓒.comp_congr (congrArg (η.app _) (Φ.src_map α)) rfl _ _))⟩

/-- Component overlap arrow of `NatTrans.whiskerLeft Φ η`. -/
@[simp] theorem whiskerLeft_app (Φ : 𝓐.Hom 𝓑) {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒} (η : NatTrans Ψ₁ Ψ₂)
    (i : ι) (x : U i) : (whiskerLeft Φ η).app i x = η.app (Φ.index i) (Φ.obj i x) := (rfl)

/-- `NatTrans.whiskerLeft` induces `Functor.whiskerLeft` on presenting-groupoid functors. -/
@[simp] theorem toNatTrans_whiskerLeft (Φ : 𝓐.Hom 𝓑) {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒} (η : NatTrans Ψ₁ Ψ₂) :
    (whiskerLeft Φ η).toNatTrans = Functor.whiskerLeft Φ.toFunctor η.toNatTrans := by
  ext x; simp [Hom.toFunctor]

/-- `NatTrans.whiskerLeft` induces `Functor.isoWhiskerLeft` on presenting-groupoid functors. -/
@[simp] theorem toNatIso_whiskerLeft (Φ : 𝓐.Hom 𝓑) {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒} (η : NatTrans Ψ₁ Ψ₂) :
    (whiskerLeft Φ η).toNatIso = Functor.isoWhiskerLeft Φ.toFunctor η.toNatIso := by ext1; simp

/-- Postcompose `η : NatTrans Φ₁ Φ₂` with `Ψ : 𝓑.Hom 𝓒` (`Functor.whiskerRight · Ψ.toFunctor`). -/
def whiskerRight {Φ₁ Φ₂ : 𝓐.Hom 𝓑} (η : NatTrans Φ₁ Φ₂) (Ψ : 𝓑.Hom 𝓒) :
    NatTrans (Ψ.comp Φ₁) (Ψ.comp Φ₂) :=
  ⟨fun i x ↦ Ψ.map (η.app i x), fun i x ↦ (Ψ.src_map _).trans (congrArg (Ψ.obj _) (η.src_app i x)),
    fun i x ↦ (Ψ.tgt_map _).trans (congrArg (Ψ.obj _) (η.tgt_app i x)), fun α ↦
      (Ψ.map_comp _ _ _).symm.trans ((congrArg Ψ.map (η.naturality α)).trans (Ψ.map_comp _ _ _))⟩

/-- Component overlap arrow of `η.whiskerRight Ψ`. -/
@[simp] theorem whiskerRight_app {Φ₁ Φ₂ : 𝓐.Hom 𝓑} (η : NatTrans Φ₁ Φ₂) (Ψ : 𝓑.Hom 𝓒)
    (i : ι) (x : U i) : (η.whiskerRight Ψ).app i x = Ψ.map (η.app i x) := (rfl)

/-- `NatTrans.whiskerRight` induces `Functor.whiskerRight` on presenting-groupoid functors. -/
@[simp] theorem toNatTrans_whiskerRight {Φ₁ Φ₂ : 𝓐.Hom 𝓑} (η : NatTrans Φ₁ Φ₂) (Ψ : 𝓑.Hom 𝓒) :
    (η.whiskerRight Ψ).toNatTrans = Functor.whiskerRight η.toNatTrans Ψ.toFunctor := by ext x; simp

/-- `NatTrans.whiskerRight` induces `Functor.isoWhiskerRight` on presenting-groupoid functors. -/
@[simp] theorem toNatIso_whiskerRight {Φ₁ Φ₂ : 𝓐.Hom 𝓑} (η : NatTrans Φ₁ Φ₂) (Ψ : 𝓑.Hom 𝓒) :
    (η.whiskerRight Ψ).toNatIso = Functor.isoWhiskerRight η.toNatIso Ψ.toFunctor := by ext1; simp

/-- Horizontal composition of atlas natural transformations along `Hom.comp`. -/
def hcomp {Φ₁ Φ₂ : 𝓐.Hom 𝓑} {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒}
    (η₁ : NatTrans Φ₁ Φ₂) (η₂ : NatTrans Ψ₁ Ψ₂) : NatTrans (Ψ₁.comp Φ₁) (Ψ₂.comp Φ₂) :=
  (whiskerLeft Φ₁ η₂).trans (η₁.whiskerRight Ψ₂)

/-- Component overlap arrow of `η₁.hcomp η₂`. -/
@[simp] theorem hcomp_app {Φ₁ Φ₂ : 𝓐.Hom 𝓑} {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒}
    (η₁ : NatTrans Φ₁ Φ₂) (η₂ : NatTrans Ψ₁ Ψ₂) (i : ι) (x : U i) :
    (η₁.hcomp η₂).app i x = 𝓒.comp (η₂.app (Φ₁.index i) (Φ₁.obj i x)) (Ψ₂.map (η₁.app i x))
      ((η₂.tgt_app _ _).trans
        ((Ψ₂.src_map _).trans (congrArg (Ψ₂.obj _) (η₁.src_app i x))).symm) := (rfl)

/-- `NatTrans.hcomp` induces horizontal composition `◫` on presenting-groupoid functors. -/
@[simp] theorem toNatTrans_hcomp {Φ₁ Φ₂ : 𝓐.Hom 𝓑} {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒}
    (η₁ : NatTrans Φ₁ Φ₂) (η₂ : NatTrans Ψ₁ Ψ₂) :
    (η₁.hcomp η₂).toNatTrans = η₁.toNatTrans ◫ η₂.toNatTrans := by ext x; simp [Hom.toFunctor]

/-- `NatTrans.hcomp` induces `NatIso.hcomp` on presenting-groupoid functors. -/
@[simp] theorem toNatIso_hcomp {Φ₁ Φ₂ : 𝓐.Hom 𝓑} {Ψ₁ Ψ₂ : 𝓑.Hom 𝓒}
    (η₁ : NatTrans Φ₁ Φ₂) (η₂ : NatTrans Ψ₁ Ψ₂) :
    (η₁.hcomp η₂).toNatIso = NatIso.hcomp η₁.toNatIso η₂.toNatIso := by ext1; simp

end NatTrans

end ChartAtlas

end TauCeti
