/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Cone
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.Algebra.Order.Group.OrderIdeal.Basic
import Mathlib.Tactic.Abel

/-!
# Quotients of partially ordered abelian groups by order ideals

Given an order ideal `I` of a partially ordered abelian group `G`, the image of the positive cone
`G⁺ = AddSubmonoid.nonneg G` in the quotient group `G ⧸ I.toAddSubgroup` is pointed because `I` is
hereditary in `G⁺`. This equips `G ⧸ I.toAddSubgroup` with a canonical translation-invariant
partial order for which `0 → I → G → G ⧸ I.toAddSubgroup → 0` is exact on positive cones.

## Main definitions

* `TauCeti.OrderIdeal.quotientPartialOrder`: the canonical `PartialOrder (G ⧸ I.toAddSubgroup)`
  (sealed with `@[no_expose]`; consumers rewrite through `quotient_nonneg_iff` and
  `quotient_le_iff`).
* `TauCeti.OrderIdeal.quotientMk`: the canonical monotone quotient map
  `G →+o G ⧸ I.toAddSubgroup`.
* `TauCeti.OrderIdeal.quotientLift`: universal property of `G ⧸ I.toAddSubgroup` for monotone
  additive homomorphisms vanishing on `I`.
* `TauCeti.OrderIdeal.quotientBotOrderAddMonoidIso`: `(G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) ≃+o G`.
* `TauCeti.OrderIdeal.quotientOrderIdealIso`: `OrderIdeal (G ⧸ I.toAddSubgroup) ≃o Set.Ici I`.

## Main results

* `TauCeti.OrderIdeal.map_nonneg_quotientMk`: `(G ⧸ I.toAddSubgroup)⁺` is the image of `G⁺`.
* `TauCeti.OrderIdeal.isSimpleOrder_quotient_iff_isCoatom`: in a directed group, the quotient by
  `I` has a simple order-ideal lattice if and only if `I` is a maximal proper order ideal.
* `TauCeti.OrderIdeal.hasRieszInterpolation_quotient`, `isUnperforated_quotient`,
  `isDimensionGroup_quotient`: Riesz interpolation, unperforation, and the dimension group
  property descend to quotients by order ideals.

## References

* K. R. Goodearl, *Partially ordered abelian groups with interpolation*, Mathematical Surveys
  and Monographs 20, AMS, 1986, Chapter 1, Proposition 2.4, and Corollary 3.2.
* M. Rørdam, *Classification of nuclear C⋆-algebras*, Encyclopaedia of Mathematical Sciences
  126, Springer, 2002, §§1.4–1.5.
-/

public section

namespace TauCeti

namespace OrderIdeal

section Quotient

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] (I : OrderIdeal G)

/-- The image of the positive cone `G⁺` in `G ⧸ I.toAddSubgroup` is pointed because `I` is
hereditary in `G⁺`. -/
private theorem isPointed_map_nonneg :
    ((AddSubmonoid.nonneg G).map (QuotientAddGroup.mk' I.toAddSubgroup)).IsPointed := by
  rintro q ⟨a, ha0, rfl⟩ ⟨b, hb0, hb⟩
  have hab : a + b ∈ I := by
    rw [← mem_toAddSubgroup, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_add,
      ← QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk'_apply, hb, add_neg_cancel]
  exact (QuotientAddGroup.eq_zero_iff a).2
    (I.mem_of_nonneg_of_le ha0 (le_add_of_nonneg_right hb0) hab)

/-- The quotient of a partially ordered abelian group `G` by an order ideal `I` is partially
ordered by the image of `G⁺`. Its body is sealed with `@[no_expose]`; use `quotient_nonneg_iff`
and `quotient_le_iff` rather than unfolding the cone construction. -/
@[no_expose]
instance quotientPartialOrder : PartialOrder (G ⧸ I.toAddSubgroup) :=
  PartialOrder.ofAddSubmonoid (isPointed_map_nonneg I)

/-- The quotient partial order on `G ⧸ I.toAddSubgroup` is translation-invariant. -/
instance quotientIsOrderedAddMonoid : IsOrderedAddMonoid (G ⧸ I.toAddSubgroup) :=
  IsOrderedAddMonoid.ofAddSubmonoid (isPointed_map_nonneg I)

/-- A class in `G ⧸ I.toAddSubgroup` is non-negative if and only if it lifts to a non-negative
element of `G`. -/
theorem quotient_nonneg_iff {q : G ⧸ I.toAddSubgroup} :
    0 ≤ q ↔ ∃ a : G, 0 ≤ a ∧ (a : G ⧸ I.toAddSubgroup) = q := by
  -- Unfold the `@[no_expose]` instance `quotientPartialOrder` to reach `ofAddSubmonoid_le_iff`.
  change (PartialOrder.ofAddSubmonoid (isPointed_map_nonneg I)).le 0 q ↔ _
  simp [PartialOrder.ofAddSubmonoid_le_iff]

/-- Characterization of `≤` on `G ⧸ I.toAddSubgroup`: `[a] ≤ [b]` if and only if `a ≤ b + c` for
some `c ∈ I`. -/
theorem quotient_le_iff {a b : G} :
    (a : G ⧸ I.toAddSubgroup) ≤ (b : G ⧸ I.toAddSubgroup) ↔ ∃ c ∈ I, a ≤ b + c := by
  -- Unfold the `@[no_expose]` instance `quotientPartialOrder` to reach `ofAddSubmonoid_le_iff`.
  change (PartialOrder.ofAddSubmonoid (isPointed_map_nonneg I)).le (a : G ⧸ I.toAddSubgroup) b ↔ _
  rw [PartialOrder.ofAddSubmonoid_le_iff]
  simp only [AddSubmonoid.mem_map, AddSubmonoid.mem_nonneg, QuotientAddGroup.mk'_apply]
  refine ⟨fun ⟨u, hu0, hu⟩ ↦ ?_, fun ⟨c, hcI, habc⟩ ↦ ?_⟩
  · have hcI : u - (b - a) ∈ I := by
      rw [← mem_toAddSubgroup, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, hu,
        QuotientAddGroup.mk_sub, sub_self]
    refine ⟨u - (b - a), hcI, ?_⟩
    have eq : b + (u - (b - a)) = a + u := by abel
    rw [eq]
    exact le_add_of_nonneg_right hu0
  · refine ⟨b + c - a, sub_nonneg.2 habc, ?_⟩
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff c).2 hcI,
      add_zero]

/-- Strengthened characterization of `≤` on `G ⧸ I.toAddSubgroup` with a non-negative witness in
`I`: `[a] ≤ [b]` if and only if `a ≤ b + c` for some `c ∈ I` with `0 ≤ c`. -/
theorem quotient_le_iff_exists_nonneg {a b : G} :
    (a : G ⧸ I.toAddSubgroup) ≤ (b : G ⧸ I.toAddSubgroup) ↔ ∃ c ∈ I, 0 ≤ c ∧ a ≤ b + c := by
  rw [quotient_le_iff]
  refine ⟨fun ⟨c, hcI, habc⟩ ↦ ?_, fun ⟨c, hcI, _, habc⟩ ↦ ⟨c, hcI, habc⟩⟩
  obtain ⟨c', hc'I, hc'0, hcc'⟩ := I.exists_nonneg_le hcI
  exact ⟨c', hc'I, hc'0, habc.trans (add_le_add_right hcc' b)⟩

/-- The canonical monotone additive homomorphism `G →+o G ⧸ I.toAddSubgroup`. -/
def quotientMk : G →+o G ⧸ I.toAddSubgroup where
  toAddMonoidHom := QuotientAddGroup.mk' I.toAddSubgroup
  monotone' _ _ hab := (I.quotient_le_iff).2 ⟨0, zero_mem I, by simpa using hab⟩

/-- `quotientMk` sends `a : G` to its coset `(a : G ⧸ I.toAddSubgroup)`. -/
@[simp]
theorem quotientMk_apply (a : G) : I.quotientMk a = (a : G ⧸ I.toAddSubgroup) :=
  (rfl)

/-- The canonical map `I.quotientMk` is surjective. -/
theorem quotientMk_surjective : Function.Surjective I.quotientMk :=
  QuotientAddGroup.mk'_surjective I.toAddSubgroup

/-- An element maps to `0` under `I.quotientMk` if and only if it belongs to `I`. -/
theorem quotientMk_eq_zero_iff {x : G} : I.quotientMk x = 0 ↔ x ∈ I :=
  QuotientAddGroup.eq_zero_iff x

/-- The additive kernel of `I.quotientMk` is `I.toAddSubgroup`. -/
@[simp]
theorem ker_quotientMk : (I.quotientMk : G →+ G ⧸ I.toAddSubgroup).ker = I.toAddSubgroup :=
  QuotientAddGroup.ker_mk' I.toAddSubgroup

/-- **Ordered exactness on positive cones**: the positive cone of `G ⧸ I.toAddSubgroup` is the
image of `G⁺` under `I.quotientMk`. -/
@[simp]
theorem map_nonneg_quotientMk :
    (AddSubmonoid.nonneg G).map I.quotientMk =
      AddSubmonoid.nonneg (G ⧸ I.toAddSubgroup) := by
  ext q
  exact AddSubmonoid.mem_map.trans I.quotient_nonneg_iff.symm

/-- If `G` is upward directed, so is `G ⧸ I.toAddSubgroup`. -/
instance quotientIsDirectedOrder [IsDirectedOrder G] : IsDirectedOrder (G ⧸ I.toAddSubgroup) where
  directed q₁ q₂ := by
    obtain ⟨a, rfl⟩ := I.quotientMk_surjective q₁
    obtain ⟨b, rfl⟩ := I.quotientMk_surjective q₂
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
    exact ⟨I.quotientMk c, OrderHomClass.mono I.quotientMk hac,
      OrderHomClass.mono I.quotientMk hbc⟩

omit [IsOrderedAddMonoid G] in
/-- In a directed group, `G ⧸ I.toAddSubgroup` is nontrivial if and only if `I ≠ ⊤`. -/
theorem nontrivial_quotient_iff [IsDirectedOrder G] :
    Nontrivial (G ⧸ I.toAddSubgroup) ↔ I ≠ ⊤ := by
  rw [QuotientAddGroup.nontrivial_iff, ne_eq, ← top_toAddSubgroup, toAddSubgroup_inj]

/-- Universal property of `G ⧸ I.toAddSubgroup`: a monotone additive homomorphism `G →+o H`
vanishing on `I` descends to a monotone additive homomorphism `(G ⧸ I.toAddSubgroup) →+o H`. -/
def quotientLift {H : Type*} [AddCommGroup H] [Preorder H]
    (f : G →+o H) (hI : ∀ x ∈ I, f x = 0) : (G ⧸ I.toAddSubgroup) →+o H where
  toAddMonoidHom := QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom hI
  monotone' q₁ q₂ hle := by
    induction q₁ using QuotientAddGroup.induction_on with | _ a =>
    induction q₂ using QuotientAddGroup.induction_on with | _ b =>
    obtain ⟨c, hcI, habc⟩ := (I.quotient_le_iff).1 hle
    calc
      f a ≤ f (b + c) := OrderHomClass.mono f habc
      _ = f b + f c := map_add f b c
      _ = f b := by rw [hI c hcI, add_zero]

/-- `I.quotientLift f hI` evaluates on `[a]` as `f a`. -/
@[simp]
theorem quotientLift_mk {H : Type*} [AddCommGroup H] [Preorder H]
    (f : G →+o H) (hI : ∀ x ∈ I, f x = 0) (a : G) :
    I.quotientLift f hI (a : G ⧸ I.toAddSubgroup) = f a :=
  (rfl)

/-- Composing `I.quotientLift f hI` with `I.quotientMk` recovers `f`. -/
@[simp]
theorem quotientLift_comp_quotientMk {H : Type*} [AddCommGroup H] [Preorder H]
    (f : G →+o H) (hI : ∀ x ∈ I, f x = 0) :
    (I.quotientLift f hI).comp I.quotientMk = f := by
  ext a
  exact I.quotientLift_mk f hI a

/-- Uniqueness in the universal property of `G ⧸ I.toAddSubgroup`. -/
theorem quotientLift_unique {H : Type*} [AddCommGroup H] [Preorder H]
    {f : G →+o H} {hI : ∀ x ∈ I, f x = 0} {g : (G ⧸ I.toAddSubgroup) →+o H}
    (hg : g.comp I.quotientMk = f) : g = I.quotientLift f hI := by
  ext q
  obtain ⟨a, rfl⟩ := I.quotientMk_surjective q
  simpa using DFunLike.congr_fun hg a

/-- The image of an order unit of `G` in `G ⧸ I.toAddSubgroup` is an order unit. -/
theorem _root_.TauCeti.IsOrderUnit.quotientMk {u : G} (hu : IsOrderUnit u) :
    IsOrderUnit (I.quotientMk u) :=
  hu.map_of_surjective I.quotientMk I.quotientMk_surjective

/-! ### The quotient by `⊥` -/

private def quotientBotAddEquiv : (G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) ≃+ G :=
  (QuotientAddGroup.quotientAddEquivOfEq (bot_toAddSubgroup (G := G))).trans
    QuotientAddGroup.quotientBot

omit [IsOrderedAddMonoid G] in
private theorem quotientBotAddEquiv_mk (a : G) :
    quotientBotAddEquiv (a : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) = a :=
  rfl

private theorem quotientBotAddEquiv_le_iff {q₁ q₂ : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup} :
    quotientBotAddEquiv q₁ ≤ quotientBotAddEquiv q₂ ↔ q₁ ≤ q₂ := by
  induction q₁ using QuotientAddGroup.induction_on with | _ a =>
  induction q₂ using QuotientAddGroup.induction_on with | _ b =>
  rw [quotientBotAddEquiv_mk, quotientBotAddEquiv_mk, (⊥ : OrderIdeal G).quotient_le_iff]
  simp

/-- The quotient of `G` by the bottom order ideal `⊥` is canonically order-isomorphic to `G`
(modeled on `TauCeti.ConvexSubgroup.quotientBotOrderIso`). -/
def quotientBotOrderAddMonoidIso : (G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) ≃+o G :=
  { quotientBotAddEquiv with
    map_le_map_iff' := quotientBotAddEquiv_le_iff }

private theorem quotientBotOrderAddMonoidIso_mk_aux (a : G) :
    quotientBotOrderAddMonoidIso (a : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) = a :=
  rfl

/-- `quotientBotOrderAddMonoidIso` sends `(a : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup)` to `a`.
Not `@[simp]` because `bot_toAddSubgroup` rewrites `(⊥ : OrderIdeal G).toAddSubgroup` inside the
coercion's type argument. -/
theorem quotientBotOrderAddMonoidIso_mk (a : G) :
    quotientBotOrderAddMonoidIso (a : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) = a :=
  quotientBotOrderAddMonoidIso_mk_aux a

private theorem quotientBotOrderAddMonoidIso_symm_apply_aux (a : G) :
    quotientBotOrderAddMonoidIso.symm a = (a : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) :=
  rfl

/-- `quotientBotOrderAddMonoidIso.symm` sends `a` to `(a : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup)`.
Not `@[simp]` for the same reason as `quotientBotOrderAddMonoidIso_mk`. -/
theorem quotientBotOrderAddMonoidIso_symm_apply (a : G) :
    quotientBotOrderAddMonoidIso.symm a = (a : G ⧸ (⊥ : OrderIdeal G).toAddSubgroup) :=
  quotientBotOrderAddMonoidIso_symm_apply_aux a

/-! ### Correspondence of order ideals in the quotient -/

/-- Preimage of an order ideal `K` of `G ⧸ I.toAddSubgroup` along `I.quotientMk`. -/
def comapQuotientMk (K : OrderIdeal (G ⧸ I.toAddSubgroup)) : OrderIdeal G :=
  ofPosGenHereditary (K.toAddSubgroup.comap I.quotientMk.toAddMonoidHom)
    (fun x hx ↦ by
      obtain ⟨w, hwK, hw0, hxw⟩ := K.exists_nonneg_le hx
      obtain ⟨a, ha0, rfl⟩ := (I.quotient_nonneg_iff).1 hw0
      obtain ⟨c, hcI, hc0, hxac⟩ := (I.quotient_le_iff_exists_nonneg).1 hxw
      refine ⟨a + c, ?_, add_nonneg ha0 hc0, hxac⟩
      rw [AddSubgroup.mem_comap, mem_toAddSubgroup]
      have hmk : I.quotientMk.toAddMonoidHom (a + c) = (a : G ⧸ I.toAddSubgroup) := by
        simpa [(I.quotientMk_eq_zero_iff).2 hcI] using map_add I.quotientMk a c
      rwa [hmk])
    (fun x y hx0 hxy hy ↦
      K.mem_of_nonneg_of_le (map_nonneg I.quotientMk hx0)
        (OrderHomClass.mono I.quotientMk hxy) hy)

/-- Membership in `I.comapQuotientMk K`. -/
@[simp]
theorem mem_comapQuotientMk {K : OrderIdeal (G ⧸ I.toAddSubgroup)} {x : G} :
    x ∈ I.comapQuotientMk K ↔ (x : G ⧸ I.toAddSubgroup) ∈ K := by
  simp [comapQuotientMk]

/-- Every preimage order ideal `I.comapQuotientMk K` contains `I`. -/
theorem le_comapQuotientMk (K : OrderIdeal (G ⧸ I.toAddSubgroup)) :
    I ≤ I.comapQuotientMk K := fun x hx ↦ by
  rw [mem_comapQuotientMk, (QuotientAddGroup.eq_zero_iff x).2 hx]
  exact zero_mem K

/-- Image in `G ⧸ I.toAddSubgroup` of an order ideal `J` of `G` containing `I`. -/
def mapQuotientMk (J : OrderIdeal G) (hIJ : I ≤ J) : OrderIdeal (G ⧸ I.toAddSubgroup) :=
  ofPosGenHereditary (J.toAddSubgroup.map I.quotientMk.toAddMonoidHom)
    (fun q ⟨z, hzJ, hzq⟩ ↦ by
      obtain ⟨w, hwJ, hw0, hzw⟩ := J.exists_nonneg_le hzJ
      exact ⟨I.quotientMk w, ⟨w, hwJ, rfl⟩, map_nonneg I.quotientMk hw0,
        hzq ▸ OrderHomClass.mono I.quotientMk hzw⟩)
    (fun q₁ q₂ hq₁0 hq₁₂ ⟨y, hyJ, hyq₂⟩ ↦ by
      obtain ⟨x, hx0, rfl⟩ := (I.quotient_nonneg_iff).1 hq₁0
      subst hyq₂
      obtain ⟨c, hcI, hxyc⟩ := (I.quotient_le_iff).1 hq₁₂
      exact ⟨x, J.mem_of_nonneg_of_le hx0 hxyc (add_mem hyJ (hIJ hcI)), rfl⟩)

/-- A coset `[x]` belongs to `I.mapQuotientMk J hIJ` if and only if `x ∈ J`. -/
@[simp]
theorem mk_mem_mapQuotientMk {J : OrderIdeal G} (hIJ : I ≤ J) {x : G} :
    (x : G ⧸ I.toAddSubgroup) ∈ I.mapQuotientMk J hIJ ↔ x ∈ J := by
  rw [mapQuotientMk, mem_ofPosGenHereditary, AddSubgroup.mem_map]
  refine ⟨fun ⟨z, hzJ, hzx⟩ ↦ ?_, fun hxJ ↦ ⟨x, hxJ, rfl⟩⟩
  have hxz : x - z ∈ I := by
    rw [← I.quotientMk_eq_zero_iff, map_sub, sub_eq_zero]
    exact hzx.symm
  simpa using add_mem (hIJ hxz) hzJ

/-- Order isomorphism between order ideals of `G ⧸ I.toAddSubgroup` and order ideals of `G`
containing `I`. -/
def quotientOrderIdealIso : OrderIdeal (G ⧸ I.toAddSubgroup) ≃o Set.Ici I where
  toFun K := ⟨I.comapQuotientMk K, I.le_comapQuotientMk K⟩
  invFun J := I.mapQuotientMk J.1 J.2
  left_inv K := ext fun q ↦ by
    obtain ⟨x, rfl⟩ := I.quotientMk_surjective q
    rw [quotientMk_apply, I.mk_mem_mapQuotientMk (I.le_comapQuotientMk K), mem_comapQuotientMk]
  right_inv J := Subtype.ext <| ext fun x ↦ by
    rw [mem_comapQuotientMk, I.mk_mem_mapQuotientMk J.2]
  map_rel_iff' {K₁ K₂} := by
    simp only [Equiv.coe_fn_mk]
    refine ⟨fun h q hq ↦ ?_,
      fun h _ hx ↦ (I.mem_comapQuotientMk).2 (h ((I.mem_comapQuotientMk).1 hx))⟩
    obtain ⟨x, rfl⟩ := I.quotientMk_surjective q
    exact (I.mem_comapQuotientMk).1 (h ((I.mem_comapQuotientMk).2 hq))

/-- Evaluating `I.quotientOrderIdealIso` takes the preimage `I.comapQuotientMk`. -/
@[simp]
theorem coe_quotientOrderIdealIso_apply (K : OrderIdeal (G ⧸ I.toAddSubgroup)) :
    (I.quotientOrderIdealIso K : OrderIdeal G) = I.comapQuotientMk K :=
  (rfl)

/-- Evaluating `I.quotientOrderIdealIso.symm` takes the image `I.mapQuotientMk`. -/
@[simp]
theorem quotientOrderIdealIso_symm_apply (J : Set.Ici I) :
    I.quotientOrderIdealIso.symm J = I.mapQuotientMk J.1 J.2 :=
  (rfl)

/-- In a directed partially ordered abelian group, `OrderIdeal (G ⧸ I.toAddSubgroup)` is a simple
lattice if and only if `I` is a maximal proper order ideal (`IsCoatom I`). -/
theorem isSimpleOrder_quotient_iff_isCoatom [IsDirectedOrder G] :
    IsSimpleOrder (OrderIdeal (G ⧸ I.toAddSubgroup)) ↔ IsCoatom I :=
  I.quotientOrderIdealIso.isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom

/-! ### Permanence of Riesz interpolation, unperforation, and dimension groups -/

/-- **Order-interval lifting** (Goodearl, Proposition 2.4): under Riesz interpolation, if
`0 ≤ s` in `G` and `0 ≤ q ≤ [s]` in `G ⧸ I.toAddSubgroup`, then `q = [x]` for some `x ∈ [0, s]`. -/
theorem exists_nonneg_le_and_quotientMk_eq (hG : HasRieszInterpolation G) {s : G}
    {q : G ⧸ I.toAddSubgroup} (hs : 0 ≤ s) (hq0 : 0 ≤ q) (hqs : q ≤ I.quotientMk s) :
    ∃ x : G, 0 ≤ x ∧ x ≤ s ∧ I.quotientMk x = q := by
  obtain ⟨a, ha0, rfl⟩ := (I.quotient_nonneg_iff).1 hq0
  obtain ⟨c, hcI, hc0, hasc⟩ := (I.quotient_le_iff_exists_nonneg).1 hqs
  obtain ⟨x, y, hx0, hxs, hy0, hyc, rfl⟩ := hG.exists_decomposition hs hc0 ha0 hasc
  have hyI : y ∈ I := I.mem_of_nonneg_of_le hy0 hyc hcI
  refine ⟨x, hx0, hxs, ?_⟩
  rw [quotientMk_apply, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff y).2 hyI, add_zero]

/-- Quotients by order ideals preserve Riesz interpolation (Goodearl, Proposition 2.4). -/
theorem hasRieszInterpolation_quotient (hG : HasRieszInterpolation G) :
    HasRieszInterpolation (G ⧸ I.toAddSubgroup) := by
  rw [hasRieszInterpolation_iff_decomposition]
  intro qa qb qg hqa0 hqb0 hqg0 hqgab
  obtain ⟨a, ha0, rfl⟩ := (I.quotient_nonneg_iff).1 hqa0
  obtain ⟨b, hb0, rfl⟩ := (I.quotient_nonneg_iff).1 hqb0
  have hqgab' : qg ≤ I.quotientMk (a + b) := by simpa using hqgab
  obtain ⟨g, hg0, hgab, rfl⟩ :=
    I.exists_nonneg_le_and_quotientMk_eq hG (add_nonneg ha0 hb0) hqg0 hqgab'
  obtain ⟨g₁, g₂, hg₁0, hg₁a, hg₂0, hg₂b, rfl⟩ := hG.exists_decomposition ha0 hb0 hg0 hgab
  exact ⟨I.quotientMk g₁, I.quotientMk g₂, map_nonneg I.quotientMk hg₁0,
    OrderHomClass.mono I.quotientMk hg₁a, map_nonneg I.quotientMk hg₂0,
    OrderHomClass.mono I.quotientMk hg₂b, map_add I.quotientMk g₁ g₂⟩

/-- Quotients by order ideals preserve unperforation (Goodearl, Corollary 3.2). -/
theorem isUnperforated_quotient (hG : IsUnperforated G) :
    IsUnperforated (G ⧸ I.toAddSubgroup) := by
  rw [isUnperforated_iff]
  intro n hn q hq
  obtain ⟨g, rfl⟩ := I.quotientMk_surjective q
  have hq' : (0 : G ⧸ I.toAddSubgroup) ≤ ((n • g : G) : G ⧸ I.toAddSubgroup) := by
    simpa [← map_nsmul] using hq
  obtain ⟨c, hcI, hc0, hngc⟩ :=
    (I.quotient_le_iff_exists_nonneg (a := 0) (b := n • g)).1 (by simpa using hq')
  have hcn : c ≤ n • c := by
    simpa [one_nsmul] using nsmul_le_nsmul_left hc0 (Nat.one_le_iff_ne_zero.2 hn)
  have hngnc : 0 ≤ n • (g + c) := by
    rw [nsmul_add]
    exact hngc.trans (add_le_add_right hcn (n • g))
  have hgc : 0 ≤ g + c := hG.nonneg_of_nsmul_nonneg hn hngnc
  have hqgc : 0 ≤ I.quotientMk (g + c) := map_nonneg I.quotientMk hgc
  rwa [map_add, (I.quotientMk_eq_zero_iff).2 hcI, add_zero] at hqgc

/-- A quotient of a dimension group by an order ideal is a dimension group
(Goodearl, Corollary 3.2). -/
theorem isDimensionGroup_quotient (hG : IsDimensionGroup G) :
    IsDimensionGroup (G ⧸ I.toAddSubgroup) where
  isDirectedOrder := by
    have := hG.isDirectedOrder
    infer_instance
  isUnperforated := I.isUnperforated_quotient hG.isUnperforated
  hasRieszInterpolation := I.hasRieszInterpolation_quotient hG.hasRieszInterpolation

end Quotient

end OrderIdeal

end TauCeti
