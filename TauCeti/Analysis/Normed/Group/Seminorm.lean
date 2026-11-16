/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Kernels and quotient descent of group seminorms

For a group seminorm `p` on a group `E`, the elements on which `p` vanishes form a subgroup
`p.ker` (`GroupSeminorm.ker`, `AddGroupSeminorm.ker`). Multiplying on either side by an element of
`p.ker` leaves `p` unchanged, and conversely a subgroup `S` lies in `p.ker` precisely when `p` is
right-invariant (or left-invariant) along `S`. On a seminormed commutative group, the kernel of
`normGroupSeminorm E` is Mathlib's `nullSubgroup E`.

When `S` is a normal subgroup of `E`, `p` induces a seminorm on the quotient group `E ⧸ S` in two
ways:

* If `S ≤ p.ker`, `p` is constant on the cosets of `S` and descends directly to
  `p.liftQ S hS : GroupSeminorm (E ⧸ S)`, characterized by `(p.liftQ S hS) ↑x = p x`. For
  `S = p.ker` (when normal), the descended seminorm is separated and defines a group norm
  `p.kerLiftNorm : GroupNorm (E ⧸ p.ker)`.
* For an arbitrary normal subgroup `S`, taking the infimum of `p` over each coset defines the
  quotient seminorm `p.quotient S : GroupSeminorm (E ⧸ S)`. It agrees with `p.liftQ S hS` whenever
  `S ≤ p.ker`, and for `normGroupSeminorm E` it recovers `QuotientGroup.groupSeminorm`.

Whenever `p x ≤ M * ‖x‖` holds on a seminormed commutative group `E`, passing to coset
representatives yields `(p.quotient S) z ≤ M * ‖z‖` (and hence `(p.liftQ S hS) z ≤ M * ‖z‖` when
`S ≤ p.ker`) without assuming `0 ≤ M`: if `‖z‖ > 0` then any representative `x` of `z` has
`‖x‖ > 0`, forcing `0 ≤ M` from `0 ≤ p x ≤ M * ‖x‖`, whereas if `‖z‖ = 0` and `M < 0` then every
element of `E` has norm `0` and both sides vanish.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966], Chapter I, §2 and Chapter II, §4.
-/

public section

open Set

namespace GroupSeminorm

section Ker

variable {E F : Type*} [Group E] [Group F]

/-- The subgroup of elements on which a group seminorm vanishes. -/
@[to_additive /-- The additive subgroup of elements on which an additive group seminorm
vanishes. -/]
def ker (p : GroupSeminorm E) : Subgroup E where
  carrier := {x : E | p x = 0}
  one_mem' := map_one_eq_zero p
  mul_mem' {x y} (hx : p x = 0) (hy : p y = 0) :=
    le_antisymm ((map_mul_le_add p x y).trans_eq (by rw [hx, hy, add_zero])) (apply_nonneg p _)
  inv_mem' {x} (hx : p x = 0) := by simpa only [mem_ofPred_eq, map_inv_eq_map] using hx

@[to_additive (attr := simp)]
theorem mem_ker {p : GroupSeminorm E} {x : E} : x ∈ p.ker ↔ p x = 0 :=
  (Iff.rfl)

@[to_additive (attr := simp)]
theorem coe_ker (p : GroupSeminorm E) : (p.ker : Set E) = {x : E | p x = 0} :=
  (rfl)

@[to_additive (attr := simp)]
theorem ker_zero : (0 : GroupSeminorm E).ker = ⊤ := by
  ext x
  simp

@[to_additive (attr := simp)]
theorem ker_add (p q : GroupSeminorm E) : (p + q).ker = p.ker ⊓ q.ker := by
  ext x
  simp only [mem_ker, add_apply, Subgroup.mem_inf]
  exact add_eq_zero_iff_of_nonneg (apply_nonneg p x) (apply_nonneg q x)

@[to_additive (attr := simp)]
theorem ker_sup (p q : GroupSeminorm E) : (p ⊔ q).ker = p.ker ⊓ q.ker := by
  ext x
  simp only [mem_ker, sup_apply, Subgroup.mem_inf]
  exact ⟨fun h ↦ ⟨le_antisymm ((le_max_left _ _).trans_eq h) (apply_nonneg p x),
    le_antisymm ((le_max_right _ _).trans_eq h) (apply_nonneg q x)⟩,
    fun ⟨hp, hq⟩ ↦ by rw [hp, hq, max_self]⟩

@[to_additive (attr := simp)]
theorem ker_comp (p : GroupSeminorm E) (f : F →* E) : (p.comp f).ker = p.ker.comap f :=
  (rfl)

@[to_additive]
theorem antitone_ker : Antitone (ker : GroupSeminorm E → Subgroup E) :=
  fun p _ hpq _ hx ↦
    mem_ker.mpr <| le_antisymm ((hpq _).trans_eq (mem_ker.mp hx)) (apply_nonneg p _)

/-- Right-multiplying by an element of the kernel leaves a group seminorm unchanged. -/
@[to_additive /-- Adding an element of the kernel on the right leaves an additive group seminorm
unchanged. -/]
theorem map_mul_eq_left_of_mem_ker {p : GroupSeminorm E} (x : E) {k : E} (hk : k ∈ p.ker) :
    p (x * k) = p x := by
  refine le_antisymm ((map_mul_le_add p x k).trans_eq (by rw [mem_ker.mp hk, add_zero])) ?_
  simpa only [mul_inv_cancel_right, map_inv_eq_map, mem_ker.mp hk, add_zero] using
    map_mul_le_add p (x * k) k⁻¹

/-- Left-multiplying by an element of the kernel leaves a group seminorm unchanged. -/
@[to_additive /-- Adding an element of the kernel on the left leaves an additive group seminorm
unchanged. -/]
theorem map_mul_eq_right_of_mem_ker {p : GroupSeminorm E} {k : E} (hk : k ∈ p.ker) (x : E) :
    p (k * x) = p x := by
  refine le_antisymm ((map_mul_le_add p k x).trans_eq (by rw [mem_ker.mp hk, zero_add])) ?_
  simpa only [inv_mul_cancel_left, map_inv_eq_map, mem_ker.mp hk, zero_add] using
    map_mul_le_add p k⁻¹ (k * x)

/-- Dividing on the right by an element of the kernel leaves a group seminorm unchanged. -/
@[to_additive /-- Subtracting an element of the kernel leaves an additive group seminorm
unchanged. -/]
theorem map_div_eq_left_of_mem_ker {p : GroupSeminorm E} (x : E) {k : E} (hk : k ∈ p.ker) :
    p (x / k) = p x := by
  rw [div_eq_mul_inv]
  exact map_mul_eq_left_of_mem_ker x (p.ker.inv_mem hk)

/-- A subgroup lies in the kernel of `p` if and only if `p` is right-invariant under `S`. -/
@[to_additive /-- An additive subgroup lies in the kernel of `p` if and only if `p` is invariant
under adding elements of `S`. -/]
theorem le_ker_iff_forall_map_mul_eq {p : GroupSeminorm E} {S : Subgroup E} :
    S ≤ p.ker ↔ ∀ x : E, ∀ s ∈ S, p (x * s) = p x := by
  refine ⟨fun hS x s hs ↦ map_mul_eq_left_of_mem_ker x (hS hs), fun h s hs ↦ ?_⟩
  rw [mem_ker, ← one_mul s, h 1 s hs, map_one_eq_zero]

/-- A subgroup lies in the kernel of `p` if and only if `p` is invariant under right-division by
elements of `S`. -/
@[to_additive /-- An additive subgroup lies in the kernel of `p` if and only if `p` is invariant
under subtracting elements of `S`. -/]
theorem le_ker_iff_forall_map_div_eq {p : GroupSeminorm E} {S : Subgroup E} :
    S ≤ p.ker ↔ ∀ x : E, ∀ s ∈ S, p (x / s) = p x := by
  rw [le_ker_iff_forall_map_mul_eq]
  exact ⟨fun h x s hs ↦ by simpa only [div_eq_mul_inv] using h x s⁻¹ (S.inv_mem hs),
    fun h x s hs ↦ by simpa only [div_inv_eq_mul] using h x s⁻¹ (S.inv_mem hs)⟩

/-- On a seminormed commutative group, the kernel of `normGroupSeminorm` is `nullSubgroup`. -/
@[to_additive (attr := simp)
  /-- On a seminormed additive commutative group, the kernel of `normAddGroupSeminorm` is
  `nullAddSubgroup`. -/]
theorem ker_normGroupSeminorm {M : Type*} [SeminormedCommGroup M] :
    (normGroupSeminorm M).ker = nullSubgroup M :=
  (rfl)

end Ker

section LiftQ

variable {E : Type*} [Group E]

/-- Descend a group seminorm across a normal subgroup contained in its kernel. -/
@[to_additive /-- Descend an additive group seminorm across a normal additive subgroup contained
in its kernel. -/]
def liftQ (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (hS : S ≤ p.ker) :
    GroupSeminorm (E ⧸ S) where
  toFun z := Quotient.liftOn' z p fun x y hxy ↦ by
    have hmem : x⁻¹ * y ∈ p.ker := hS (QuotientGroup.leftRel_apply.mp hxy)
    simpa only [mul_inv_cancel_left] using (map_mul_eq_left_of_mem_ker x hmem).symm
  map_one' := map_one_eq_zero p
  mul_le' x y := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact map_mul_le_add p a b
  inv' x := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    exact map_inv_eq_map p a

@[to_additive (attr := simp)]
theorem liftQ_mk (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (hS : S ≤ p.ker) (x : E) :
    p.liftQ S hS (x : E ⧸ S) = p x :=
  (rfl)

@[to_additive (attr := simp)]
theorem comp_mk'_liftQ (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (hS : S ≤ p.ker) :
    (p.liftQ S hS).comp (QuotientGroup.mk' S) = p :=
  ext fun _ ↦ rfl

@[to_additive (attr := simp)]
theorem liftQ_comp_mk' (S : Subgroup E) [S.Normal] (q : GroupSeminorm (E ⧸ S))
    (hS : S ≤ (q.comp (QuotientGroup.mk' S)).ker := fun x hx ↦ by
      simp [(QuotientGroup.eq_one_iff x).mpr hx]) :
    (q.comp (QuotientGroup.mk' S)).liftQ S hS = q := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  exact liftQ_mk _ S hS x

@[to_additive]
theorem eq_liftQ_iff {p : GroupSeminorm E} {S : Subgroup E} [S.Normal] {hS : S ≤ p.ker}
    {q : GroupSeminorm (E ⧸ S)} :
    q = p.liftQ S hS ↔ q.comp (QuotientGroup.mk' S) = p := by
  refine ⟨fun h ↦ h ▸ comp_mk'_liftQ p S hS, fun h ↦ ?_⟩
  subst h
  exact (liftQ_comp_mk' S q hS).symm

@[to_additive]
theorem liftQ_mono {p q : GroupSeminorm E} {S : Subgroup E} [S.Normal] {hp : S ≤ p.ker}
    {hq : S ≤ q.ker} (hpq : p ≤ q) :
    p.liftQ S hp ≤ q.liftQ S hq := by
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  exact hpq x

@[to_additive (attr := simp)]
theorem liftQ_zero (S : Subgroup E) [S.Normal] (hS : S ≤ (0 : GroupSeminorm E).ker := by simp) :
    (0 : GroupSeminorm E).liftQ S hS = 0 := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp

@[to_additive]
theorem liftQ_add (p q : GroupSeminorm E) (S : Subgroup E) [S.Normal]
    (hp : S ≤ p.ker) (hq : S ≤ q.ker) :
    (p + q).liftQ S (ker_add p q ▸ le_inf hp hq) = p.liftQ S hp + q.liftQ S hq := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp

@[to_additive]
theorem liftQ_sup (p q : GroupSeminorm E) (S : Subgroup E) [S.Normal]
    (hp : S ≤ p.ker) (hq : S ≤ q.ker) :
    (p ⊔ q).liftQ S (ker_sup p q ▸ le_inf hp hq) = p.liftQ S hp ⊔ q.liftQ S hq := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp

@[to_additive]
theorem ker_liftQ (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (hS : S ≤ p.ker) :
    (p.liftQ S hS).ker = p.ker.map (QuotientGroup.mk' S) := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp only [mem_ker, liftQ_mk, Subgroup.mem_map, QuotientGroup.mk'_apply]
  refine ⟨fun hx ↦ ⟨x, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, hyx⟩
  have hxy : y⁻¹ * x ∈ p.ker := hS (QuotientGroup.eq.mp hyx)
  simpa only [mul_inv_cancel_left, hy] using map_mul_eq_left_of_mem_ker y hxy

@[to_additive (attr := simp)]
theorem ker_liftQ_self (p : GroupSeminorm E) [p.ker.Normal] :
    (p.liftQ p.ker le_rfl).ker = ⊥ := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp [Subgroup.mem_bot, QuotientGroup.eq_one_iff]

/-- Descending a group seminorm across its full normal kernel produces a separated group norm on
`E ⧸ p.ker`. -/
@[to_additive /-- Descending an additive group seminorm across its full normal kernel produces a
separated additive group norm on `E ⧸ p.ker`. -/]
def kerLiftNorm (p : GroupSeminorm E) [p.ker.Normal] : GroupNorm (E ⧸ p.ker) where
  __ := p.liftQ p.ker le_rfl
  eq_one_of_map_eq_zero' z hz := by
    have hmem : z ∈ (p.liftQ p.ker le_rfl).ker := hz
    rwa [ker_liftQ_self, Subgroup.mem_bot] at hmem

@[to_additive (attr := simp)]
theorem kerLiftNorm_mk (p : GroupSeminorm E) [p.ker.Normal] (x : E) :
    p.kerLiftNorm (x : E ⧸ p.ker) = p x :=
  (rfl)

end LiftQ

section Quotient

variable {E : Type*} [Group E]

@[to_additive]
private theorem coset_bddBelow (p : GroupSeminorm E) (S : Subgroup E) (x : E ⧸ S) :
    BddBelow (range fun m : {m : E | (m : E ⧸ S) = x} ↦ p m) :=
  ⟨0, forall_mem_range.2 fun m ↦ apply_nonneg p m.1⟩

/-- The infimal quotient group seminorm on `E ⧸ S` induced by `p` and an arbitrary normal subgroup
`S`, defined on each class as the infimum of `p` over its representatives in `E`. -/
@[to_additive /-- The infimal quotient additive group seminorm on `E ⧸ S` induced by `p` and an
arbitrary normal additive subgroup `S`, defined on each class as the infimum of `p` over its
representatives in `E`. -/]
noncomputable def quotient (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] :
    GroupSeminorm (E ⧸ S) where
  toFun x := ⨅ m : {m : E | (m : E ⧸ S) = x}, p m
  map_one' := by
    have : Nonempty {m : E | (m : E ⧸ S) = 1} := ⟨⟨1, rfl⟩⟩
    refine le_antisymm ?_ (le_ciInf fun m ↦ apply_nonneg p m.1)
    exact (ciInf_le (coset_bddBelow p S 1) ⟨1, rfl⟩).trans_eq (map_one_eq_zero p)
  mul_le' x y := by
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
    have : Nonempty {m : E | (m : E ⧸ S) = x₀} := ⟨⟨x₀, rfl⟩⟩
    have : Nonempty {m : E | (m : E ⧸ S) = y₀} := ⟨⟨y₀, rfl⟩⟩
    refine le_ciInf_add_ciInf fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ?_
    refine ciInf_le_of_le (coset_bddBelow p S _)
      ⟨a * b, by rw [mem_ofPred_eq, QuotientGroup.mk_mul, ha, hb]⟩ (map_mul_le_add p a b)
  inv' x := by
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
    have : Nonempty {m : E | (m : E ⧸ S) = (x₀ : E ⧸ S)⁻¹} := ⟨⟨x₀⁻¹, rfl⟩⟩
    have : Nonempty {m : E | (m : E ⧸ S) = x₀} := ⟨⟨x₀, rfl⟩⟩
    refine le_antisymm (le_ciInf fun ⟨m, hm⟩ ↦ ?_) (le_ciInf fun ⟨m, hm⟩ ↦ ?_)
    · refine (ciInf_le (coset_bddBelow p S _) ⟨m⁻¹, ?_⟩).trans_eq (map_inv_eq_map p m)
      simp [mem_ofPred_eq.mp hm]
    · refine (ciInf_le (coset_bddBelow p S _) ⟨m⁻¹, ?_⟩).trans_eq (map_inv_eq_map p m)
      simp [mem_ofPred_eq.mp hm]

@[to_additive]
theorem le_quotient_iff {p : GroupSeminorm E} {S : Subgroup E} [S.Normal] {x : E ⧸ S} {r : ℝ} :
    r ≤ p.quotient S x ↔ ∀ m : E, (m : E ⧸ S) = x → r ≤ p m := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  have : Nonempty {m : E | (m : E ⧸ S) = x₀} := ⟨⟨x₀, rfl⟩⟩
  exact (le_ciInf_iff (coset_bddBelow p S _)).trans Subtype.forall

@[to_additive]
theorem quotient_lt_iff {p : GroupSeminorm E} {S : Subgroup E} [S.Normal] {x : E ⧸ S} {r : ℝ} :
    p.quotient S x < r ↔ ∃ m : E, (m : E ⧸ S) = x ∧ p m < r := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  have : Nonempty {m : E | (m : E ⧸ S) = x₀} := ⟨⟨x₀, rfl⟩⟩
  refine (ciInf_lt_iff (coset_bddBelow p S _)).trans ?_
  exact ⟨fun ⟨⟨m, hm⟩, hlt⟩ ↦ ⟨m, hm, hlt⟩, fun ⟨m, hm, hlt⟩ ↦ ⟨⟨m, hm⟩, hlt⟩⟩

@[to_additive]
theorem quotient_mk_le (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (x : E) :
    p.quotient S (x : E ⧸ S) ≤ p x :=
  ciInf_le (coset_bddBelow p S _) ⟨x, rfl⟩

@[to_additive]
theorem exists_mk_eq_and_lt (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (x : E ⧸ S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : E, (m : E ⧸ S) = x ∧ p m < p.quotient S x + ε :=
  quotient_lt_iff.mp (lt_add_of_pos_right _ hε)

@[to_additive]
theorem quotient_mk_eq_iInf_mul (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (x : E) :
    p.quotient S (x : E ⧸ S) = ⨅ s : S, p (x * s) := by
  have hbdd : BddBelow (range fun s : S ↦ p (x * s)) :=
    ⟨0, forall_mem_range.2 fun s ↦ apply_nonneg p _⟩
  refine le_antisymm (le_ciInf fun s ↦ ?_) (le_quotient_iff.mpr fun m hm ↦ ?_)
  · have hmk : ((x * s : E) : E ⧸ S) = x := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr s.2, mul_one]
    exact hmk ▸ p.quotient_mk_le S (x * s)
  · have hmem : x⁻¹ * m ∈ S := QuotientGroup.eq.mp hm.symm
    simpa only [mul_inv_cancel_left] using ciInf_le hbdd ⟨x⁻¹ * m, hmem⟩

@[to_additive]
theorem quotient_mk_eq_iInf_div (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (x : E) :
    p.quotient S (x : E ⧸ S) = ⨅ s : S, p (x / s) := by
  rw [quotient_mk_eq_iInf_mul]
  exact Equiv.inv S |>.iInf_congr fun s ↦ by simp [div_eq_mul_inv]

@[to_additive]
theorem quotient_mono {p q : GroupSeminorm E} (S : Subgroup E) [S.Normal] (hpq : p ≤ q) :
    p.quotient S ≤ q.quotient S :=
  fun _ ↦ le_quotient_iff.mpr fun m hm ↦ (hm ▸ p.quotient_mk_le S m).trans (hpq m)

@[to_additive]
theorem quotient_anti (p : GroupSeminorm E) {S₁ S₂ : Subgroup E} [S₁.Normal] [S₂.Normal]
    (hS : S₁ ≤ S₂) (x : E) :
    p.quotient S₂ (x : E ⧸ S₂) ≤ p.quotient S₁ (x : E ⧸ S₁) :=
  le_quotient_iff.mpr fun m hm ↦ by
    have hmk : (m : E ⧸ S₂) = (x : E ⧸ S₂) :=
      QuotientGroup.eq.mpr (hS (QuotientGroup.eq.mp hm))
    exact hmk ▸ p.quotient_mk_le S₂ m

/-- When `S ≤ p.ker`, the infimal quotient seminorm coincides with the direct coset lift
`p.liftQ S hS`. -/
@[to_additive /-- When `S ≤ p.ker`, the infimal quotient seminorm coincides with the direct coset
lift `p.liftQ S hS`. -/]
theorem quotient_eq_liftQ (p : GroupSeminorm E) (S : Subgroup E) [S.Normal] (hS : S ≤ p.ker) :
    p.quotient S = p.liftQ S hS := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [liftQ_mk]
  refine le_antisymm (p.quotient_mk_le S x) (le_quotient_iff.mpr fun m hm ↦ ?_)
  have hmem : x⁻¹ * m ∈ p.ker := hS (QuotientGroup.eq.mp hm.symm)
  have h := map_mul_eq_left_of_mem_ker x hmem
  rw [mul_inv_cancel_left] at h
  exact h.ge

/-- On a seminormed commutative group, the quotient seminorm of `normGroupSeminorm` is
`QuotientGroup.groupSeminorm`. -/
@[to_additive (attr := simp)
  /-- On a seminormed additive commutative group, the quotient seminorm of
  `normAddGroupSeminorm` is `QuotientAddGroup.addGroupSeminorm`. -/]
theorem quotient_normGroupSeminorm {M : Type*} [SeminormedCommGroup M] (S : Subgroup M) :
    (normGroupSeminorm M).quotient S = QuotientGroup.groupSeminorm := by
  ext z
  refine le_antisymm ?_ ?_
  · rw [← QuotientGroup.norm_eq_groupSeminorm, QuotientGroup.le_norm_iff]
    intro m hm
    exact hm ▸ (normGroupSeminorm M).quotient_mk_le S m
  · rw [le_quotient_iff]
    intro m hm
    simpa only [coe_normGroupSeminorm, ← hm, QuotientGroup.norm_eq_groupSeminorm] using
      (QuotientGroup.norm_mk_le_norm (S := S) (m := m))

/-- A norm bound `p x ≤ M * ‖x‖` on a seminormed commutative group passes to the quotient seminorm
on `G ⧸ S`, without requiring `0 ≤ M`. -/
@[to_additive quotient_le_mul_norm
  /-- A norm bound `p x ≤ M * ‖x‖` on a seminormed additive commutative group passes to the
  quotient seminorm on `G ⧸ S`, without requiring `0 ≤ M`. -/]
theorem quotient_le_mul_norm {G : Type*} [SeminormedCommGroup G] (p : GroupSeminorm G)
    (S : Subgroup G) {M : ℝ} (hM : ∀ x : G, p x ≤ M * ‖x‖) (z : G ⧸ S) :
    p.quotient S z ≤ M * ‖z‖ := by
  rcases le_or_gt 0 M with hM0 | hMneg
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    rcases eq_or_lt_of_le hM0 with rfl | hMpos
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
      have hx0 : p x ≤ 0 := by simpa using hM x
      linarith [p.quotient_mk_le S x, hε]
    · obtain ⟨m, rfl, hm⟩ := QuotientGroup.exists_norm_mk_lt z (div_pos hε hMpos)
      calc p.quotient S (m : G ⧸ S) ≤ p m := p.quotient_mk_le S m
        _ ≤ M * ‖m‖ := hM m
        _ ≤ M * (‖(m : G ⧸ S)‖ + ε / M) := mul_le_mul_of_nonneg_left hm.le hM0
        _ = M * ‖(m : G ⧸ S)‖ + ε := by rw [mul_add, mul_div_cancel₀ _ hMpos.ne']
  · -- When `M < 0`, `0 ≤ p x ≤ M * ‖x‖` forces `‖x‖ = 0` and `p x = 0` for every `x`.
    have hnorm0 (x : G) : ‖x‖ = 0 := by
      by_contra hx
      have hxpos : 0 < ‖x‖ := (norm_nonneg' x).lt_of_ne' hx
      linarith [apply_nonneg p x, hM x, mul_neg_of_neg_of_pos hMneg hxpos]
    have hp0 (x : G) : p x = 0 :=
      le_antisymm ((hM x).trans_eq (by rw [hnorm0 x, mul_zero])) (apply_nonneg p x)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have hz0 : ‖(x : G ⧸ S)‖ = 0 :=
      le_antisymm ((QuotientGroup.norm_mk_le_norm (S := S) (m := x)).trans_eq (hnorm0 x))
        (norm_nonneg' _)
    have hq0 : p.quotient S (x : G ⧸ S) = 0 :=
      le_antisymm ((p.quotient_mk_le S x).trans_eq (hp0 x)) (apply_nonneg _ _)
    rw [hq0, hz0, mul_zero]

/-- When `S ≤ p.ker`, a norm bound `p x ≤ M * ‖x‖` descends to `(p.liftQ S hS) z ≤ M * ‖z‖`
without requiring `0 ≤ M`. -/
@[to_additive liftQ_le_mul_norm
  /-- When `S ≤ p.ker`, a norm bound `p x ≤ M * ‖x‖` descends to `(p.liftQ S hS) z ≤ M * ‖z‖`
  without requiring `0 ≤ M`. -/]
theorem liftQ_le_mul_norm {G : Type*} [SeminormedCommGroup G] (p : GroupSeminorm G)
    (S : Subgroup G) (hS : S ≤ p.ker) {M : ℝ} (hM : ∀ x : G, p x ≤ M * ‖x‖) (z : G ⧸ S) :
    p.liftQ S hS z ≤ M * ‖z‖ := by
  rw [← quotient_eq_liftQ]
  exact p.quotient_le_mul_norm S hM z

end Quotient

end GroupSeminorm
