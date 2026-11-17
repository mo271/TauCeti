/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Exact monotone-composition lifting

Given an inner map `g : X → Y` mapping a domain `D : Set X` into a preordered height domain
`E : Set Y`, and an outer function `h : Y → β` that is monotone on `E`, the sublevel set
`originalSet D g h b = {x ∈ D | h (g x) ≤ b}` is the exact first-coordinate projection of the
lifted set `liftedSet D E g h b = {(x, y) | x ∈ D ∧ y ∈ E ∧ g x ≤ y ∧ h y ≤ b}`. No convexity,
differentiability, or topological assumptions are required: graph insertion `x ↦ (x, g x)` and
first-coordinate projection `Prod.fst` witness the identity directly.

For any objective `f : X → α` lifted without height dependence as `f ∘ Prod.fst`, the same two
maps preserve the set of feasible objective values, lower bounds, feasible minima at every
specified pair, and existence of an attained feasible minimum, without asserting that attainment
holds. Specializing the budget to a parameter `t` recovers the epigraph lifting criterion for
monotone compositions `h ∘ g`.

## Main definitions

* `TauCeti.ConvexLifting.originalSet`: the sublevel set `{x | x ∈ D ∧ h (g x) ≤ b}` of a
  composed map on `D`.
* `TauCeti.ConvexLifting.liftedSet`: the lifted set
  `{p | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b}` introducing an auxiliary upper height in `E`.

## Main statements

* `TauCeti.ConvexLifting.image_fst_liftedSet`: under `MapsTo g D E` and `MonotoneOn h E`,
  `Prod.fst '' liftedSet D E g h b = originalSet D g h b`.
* `TauCeti.ConvexLifting.mem_epigraph_comp_iff`: the epigraph lifting equivalence
  `(x ∈ D ∧ h (g x) ≤ t) ↔ ∃ y ∈ E, g x ≤ y ∧ h y ≤ t ∧ x ∈ D`.
* `TauCeti.ConvexLifting.isMinOn_comp_fst_liftedSet_iff` and
  `TauCeti.ConvexLifting.mem_liftedSet_and_isMinOn_iff`: equivalence of minima (and feasible minima
  at a specified pair) between `f ∘ Prod.fst` on `liftedSet` and `f` on `originalSet`.
* `TauCeti.ConvexLifting.exists_mem_liftedSet_isMinOn_iff`: existence of an attained feasible
  minimum transfers in both directions.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global optimization*,
  Mathematical Programming 103 (2005), 225–249, §2, Proposition 1, pp. 226–227.
* M. Lubin, E. Yamangil, R. Bent and J. P. Vielma, *Extended Formulations in Mixed-integer Convex
  Programming*, IPCO 2016, pp. 102–113 (arXiv:1511.06710v3, §4, p. 9).
-/

public section

open Set

namespace TauCeti.ConvexLifting

section Definitions

variable {X Y β : Type*}

/-- Points in `D` satisfying the composed inequality `h (g x) ≤ b`. -/
def originalSet [LE β] (D : Set X) (g : X → Y) (h : Y → β) (b : β) : Set X :=
  {x | x ∈ D ∧ h (g x) ≤ b}

/-- Lifted pairs `(x, y)` in `D × E` with auxiliary upper height `g x ≤ y` satisfying `h y ≤ b`. -/
def liftedSet [LE Y] [LE β] (D : Set X) (E : Set Y) (g : X → Y) (h : Y → β) (b : β) :
    Set (X × Y) :=
  {p | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b}

/-- Membership characterization of `originalSet`. -/
@[simp]
theorem mem_originalSet_iff [LE β] {D : Set X} {g : X → Y} {h : Y → β} {b : β} {x : X} :
    x ∈ originalSet D g h b ↔ x ∈ D ∧ h (g x) ≤ b :=
  Iff.rfl

/-- Membership characterization of `liftedSet`. -/
@[simp]
theorem mem_liftedSet_iff [LE Y] [LE β] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}
    {p : X × Y} :
    p ∈ liftedSet D E g h b ↔ p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b :=
  Iff.rfl

/-- The original sublevel set is contained in the domain `D`. -/
theorem originalSet_subset [LE β] (D : Set X) (g : X → Y) (h : Y → β) (b : β) :
    originalSet D g h b ⊆ D :=
  fun _ hx => hx.1

/-- The lifted set is contained in the product domain `D ×ˢ E`. -/
theorem liftedSet_subset_prod [LE Y] [LE β] (D : Set X) (E : Set Y) (g : X → Y) (h : Y → β)
    (b : β) :
    liftedSet D E g h b ⊆ D ×ˢ E :=
  fun _ hp => ⟨hp.1, hp.2.1⟩

/-- With an empty domain, `originalSet` is empty. -/
@[simp]
theorem originalSet_empty [LE β] (g : X → Y) (h : Y → β) (b : β) :
    originalSet (∅ : Set X) g h b = ∅ := by
  ext x
  simp

/-- With an empty original domain, `liftedSet` is empty. -/
@[simp]
theorem liftedSet_empty_left [LE Y] [LE β] (E : Set Y) (g : X → Y) (h : Y → β) (b : β) :
    liftedSet (∅ : Set X) E g h b = ∅ := by
  ext p
  simp

/-- With an empty height domain, `liftedSet` is empty. -/
@[simp]
theorem liftedSet_empty_right [LE Y] [LE β] (D : Set X) (g : X → Y) (h : Y → β) (b : β) :
    liftedSet D (∅ : Set Y) g h b = ∅ := by
  ext p
  simp

/-- `originalSet` is monotone in the domain and budget. -/
@[gcongr]
theorem originalSet_mono [Preorder β] {D₁ D₂ : Set X} {g : X → Y} {h : Y → β} {b₁ b₂ : β}
    (hD : D₁ ⊆ D₂) (hb : b₁ ≤ b₂) :
    originalSet D₁ g h b₁ ⊆ originalSet D₂ g h b₂ :=
  fun _ hx => ⟨hD hx.1, hx.2.trans hb⟩

/-- `liftedSet` is monotone in both domains and the budget. -/
@[gcongr]
theorem liftedSet_mono [LE Y] [Preorder β] {D₁ D₂ : Set X} {E₁ E₂ : Set Y} {g : X → Y}
    {h : Y → β} {b₁ b₂ : β} (hD : D₁ ⊆ D₂) (hE : E₁ ⊆ E₂) (hb : b₁ ≤ b₂) :
    liftedSet D₁ E₁ g h b₁ ⊆ liftedSet D₂ E₂ g h b₂ :=
  fun _ hp => ⟨hD hp.1, hE hp.2.1, hp.2.2.1, hp.2.2.2.trans hb⟩

end Definitions

section ExactProjection

variable {X Y β : Type*} [Preorder Y] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}

/-- Graph insertion maps a feasible point of `originalSet` into `liftedSet` whenever its image lies
in `E`. -/
theorem graph_mem_liftedSet [LE β] {x : X} (hgx : g x ∈ E) (hx : x ∈ originalSet D g h b) :
    (x, g x) ∈ liftedSet D E g h b :=
  ⟨hx.1, hgx, le_rfl, hx.2⟩

/-- Graph insertion as a `MapsTo` witness from `originalSet` into `liftedSet`. -/
theorem mapsTo_graph_liftedSet [LE β] (hg : MapsTo g (originalSet D g h b) E) :
    MapsTo (fun x => (x, g x)) (originalSet D g h b) (liftedSet D E g h b) :=
  fun _ hx => graph_mem_liftedSet (hg hx) hx

variable [Preorder β]

/-- Under `MonotoneOn h E`, if `p ∈ liftedSet D E g h b` and `g p.1 ∈ E`, then `p.1` lies in
`originalSet D g h b`. -/
theorem fst_mem_originalSet (hm : MonotoneOn h E) {p : X × Y} (hgp : g p.1 ∈ E)
    (hp : p ∈ liftedSet D E g h b) :
    p.1 ∈ originalSet D g h b :=
  ⟨hp.1, (hm hgp hp.2.1 hp.2.2.1).trans hp.2.2.2⟩

/-- First-coordinate projection as a `MapsTo` witness from `liftedSet` into `originalSet`. -/
theorem mapsTo_fst_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    MapsTo Prod.fst (liftedSet D E g h b) (originalSet D g h b) :=
  fun _ hp => fst_mem_originalSet hm (hg hp.1) hp

/-- Pointwise existential characterization of membership in `originalSet` via `liftedSet`. -/
theorem exists_mem_liftedSet_iff {x : X} (hg : x ∈ D → g x ∈ E) (hm : MonotoneOn h E) :
    (∃ y, (x, y) ∈ liftedSet D E g h b) ↔ x ∈ originalSet D g h b :=
  ⟨fun ⟨_, hy⟩ => fst_mem_originalSet hm (hg hy.1) hy,
   fun hx => ⟨g x, graph_mem_liftedSet (hg hx.1) hx⟩⟩

/-- **Exact monotone-composition projection.** Under `MapsTo g D E` and `MonotoneOn h E`, the
first-coordinate projection of `liftedSet D E g h b` equals `originalSet D g h b`. -/
theorem image_fst_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    Prod.fst '' liftedSet D E g h b = originalSet D g h b := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact fst_mem_originalSet hm (hg hp.1) hp
  · intro hx
    exact ⟨(x, g x), graph_mem_liftedSet (hg hx.1) hx, rfl⟩

/-- Nonemptiness of the lifted set is equivalent to nonemptiness of the original set. -/
theorem liftedSet_nonempty_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    (liftedSet D E g h b).Nonempty ↔ (originalSet D g h b).Nonempty := by
  rw [← image_fst_liftedSet (b := b) hg hm, image_nonempty]

/-- Emptiness of the lifted set is equivalent to emptiness of the original set. -/
theorem liftedSet_eq_empty_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    liftedSet D E g h b = ∅ ↔ originalSet D g h b = ∅ := by
  rw [← image_fst_liftedSet (b := b) hg hm, image_eq_empty]

omit b in
/-- **Epigraph lifting criterion for monotone compositions.** A pair `(x, t)` lies in the epigraph
of `h ∘ g` on `D` if and only if there is an admissible upper height `y ∈ E` with `g x ≤ y` and
`h y ≤ t`. -/
theorem mem_epigraph_comp_iff {x : X} {t : β} (hg : x ∈ D → g x ∈ E) (hm : MonotoneOn h E) :
    (x ∈ D ∧ h (g x) ≤ t) ↔ ∃ y ∈ E, g x ≤ y ∧ h y ≤ t ∧ x ∈ D := by
  simpa only [mem_originalSet_iff, mem_liftedSet_iff, and_comm, and_left_comm, and_assoc] using
    (exists_mem_liftedSet_iff (b := t) hg hm).symm

end ExactProjection

section FeasibleMinima

variable {X Y β α : Type*} [Preorder Y] [Preorder β] {D : Set X} {E : Set Y}
  {g : X → Y} {h : Y → β} {b : β}

/-- Lifted objectives `f ∘ Prod.fst` attain the exact same set of feasible objective values as `f`
on `originalSet`. -/
theorem image_comp_fst_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) (f : X → α) :
    (f ∘ Prod.fst) '' liftedSet D E g h b = f '' originalSet D g h b := by
  rw [Set.image_comp, image_fst_liftedSet hg hm]

/-- Lower bounds on the objective transfer identically between `liftedSet` and `originalSet`. -/
theorem forall_mem_liftedSet_le_iff [LE α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) {c : α} :
    (∀ p ∈ liftedSet D E g h b, c ≤ f p.1) ↔ ∀ x ∈ originalSet D g h b, c ≤ f x := by
  rw [← image_fst_liftedSet (b := b) hg hm, forall_mem_image]

/-- An arbitrary point `p` minimizes `f ∘ Prod.fst` on `liftedSet` if and only if `p.1` minimizes
`f` on `originalSet`. -/
theorem isMinOn_comp_fst_liftedSet_iff [Preorder α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) (p : X × Y) :
    IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p ↔ IsMinOn f (originalSet D g h b) p.1 :=
  ⟨fun hp _ hx => hp (graph_mem_liftedSet (hg hx.1) hx),
   fun hp => hp.comp_of_mapsTo (mapsTo_fst_liftedSet hg hm) rfl⟩

/-- **Feasible minimum equivalence at a specified pair.** A pair `p` is a feasible minimizer of
`f ∘ Prod.fst` on `liftedSet` if and only if `p` is feasible in `liftedSet` and `p.1` is a
feasible minimizer of `f` on `originalSet`. -/
theorem mem_liftedSet_and_isMinOn_iff [Preorder α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) (p : X × Y) :
    (p ∈ liftedSet D E g h b ∧ IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) ↔
      p ∈ liftedSet D E g h b ∧ p.1 ∈ originalSet D g h b ∧
        IsMinOn f (originalSet D g h b) p.1 := by
  constructor
  · rintro ⟨hp, hmin⟩
    exact ⟨hp, fst_mem_originalSet hm (hg hp.1) hp,
      (isMinOn_comp_fst_liftedSet_iff hg hm f p).1 hmin⟩
  · rintro ⟨hp, _, hmin⟩
    exact ⟨hp, (isMinOn_comp_fst_liftedSet_iff hg hm f p).2 hmin⟩

/-- **Attainment equivalence.** An attained feasible minimum exists on `liftedSet` if and only if
one exists on `originalSet`, without asserting that either feasible set attains its infimum. -/
theorem exists_mem_liftedSet_isMinOn_iff [Preorder α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) :
    (∃ p ∈ liftedSet D E g h b, IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) ↔
      ∃ x ∈ originalSet D g h b, IsMinOn f (originalSet D g h b) x := by
  constructor
  · rintro ⟨p, hp, hmin⟩
    exact ⟨p.1, fst_mem_originalSet hm (hg hp.1) hp,
      (isMinOn_comp_fst_liftedSet_iff hg hm f p).1 hmin⟩
  · rintro ⟨x, hx, hmin⟩
    exact ⟨(x, g x), graph_mem_liftedSet (hg hx.1) hx,
      hmin.comp_of_mapsTo (mapsTo_fst_liftedSet hg hm) rfl⟩

end FeasibleMinima

/-! ### Examples -/

/-- For `g(x) = x.natAbs` and `h = id` on `ℤ` with budget `0`, exact projection gives `{0}` and
`(0, 0)` minimizes `id ∘ Prod.fst` on `liftedSet`, exercising the lifting without differentiability.
Meanwhile, for `g(x) = x * x` and decreasing `h(y) = 1 - y` at budget `0`, `(0, 1)` lies in
`liftedSet` even though `0` does not lie in `originalSet`, showing that `MonotoneOn` cannot be
dropped. -/
example :
    (Prod.fst '' liftedSet (Set.univ : Set ℤ) Set.univ Int.natAbs id 0 =
      originalSet Set.univ Int.natAbs id 0) ∧
    ((0, 0) ∈ liftedSet (Set.univ : Set ℤ) Set.univ Int.natAbs id 0 ∧
      IsMinOn (id ∘ Prod.fst)
        (liftedSet (Set.univ : Set ℤ) Set.univ Int.natAbs id 0) (0, 0)) ∧
    ((0, 1) ∈ liftedSet (Set.univ : Set ℤ) Set.univ (fun x : ℤ => x * x) (fun y => 1 - y) 0 ∧
      0 ∉ originalSet (Set.univ : Set ℤ) (fun x : ℤ => x * x) (fun y => 1 - y) 0) := by
  refine ⟨image_fst_liftedSet (mapsTo_univ _ _) monotoneOn_id, ?_, ?_⟩
  · rw [mem_liftedSet_and_isMinOn_iff (mapsTo_univ _ _) monotoneOn_id]
    refine ⟨by simp, by simp, fun x hx => ?_⟩
    simp only [mem_originalSet_iff, mem_univ, true_and, id_eq, Nat.le_zero,
      Int.natAbs_eq_zero] at hx
    simp [hx]
  · simp

end TauCeti.ConvexLifting
