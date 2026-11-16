/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finset.NoncommProd
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Exchange
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# Commuting products of orthogonal root reflections and their inversions

Reflections in orthogonal roots commute (`RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal`),
so any finite set `s` of pairwise orthogonal root indices determines a canonical unordered product
`s.noncommProd (RootPairing.weylGroup.ofIdx P) _` in the Weyl group. Because the individual
reflections are involutions that fix one another's roots, their commuting product is again an
involution and acts on weights by subtracting the orthogonal reflection terms simultaneously,
`x ↦ x - ∑ i ∈ s, ⟨x, αᵢ^∨⟩ • αᵢ`.

When `s` consists of pairwise orthogonal simple roots of a base `b`, each reflection `sᵢ` fixes
every other root of `s`, so right multiplication by the product toggles all `#s` simple roots of
`s` independently in the inversion set:
* if every root of `s` is already an inversion of `w`, right multiplication by the product lowers
  the number of inversions of `w` by `#s`;
* if no root of `s` is an inversion of `w`, right multiplication raises the number of inversions
  by `#s`; in particular, the inversion set of the product itself is `s`.

These simultaneous wall-crossing formulas underlie block-reflection descent for diagram
automorphisms whose simple-root orbits are pairwise orthogonal.

## Main results

* `RootPairing.weylGroup.pairwise_commute_ofIdx_of_isOrthogonal`: reflections in pairwise
  orthogonal roots pairwise commute in the Weyl group.
* `RootPairing.weylGroup.noncommProd_ofIdx_mul_self` and
  `RootPairing.weylGroup.noncommProd_ofIdx_inv`: any commuting product of root reflections is an
  involution.
* `RootPairing.Equiv.weylGroupEquiv_noncommProd_ofIdx`: an equivalence of root pairings transports
  a commuting product of root reflections by mapping its index finset along `indexEquiv`.
* `RootPairing.weylGroup.noncommProd_ofIdx_smul`: a product of pairwise orthogonal root reflections
  sends `x` to `x - ∑ i ∈ s, P.coroot' i x • P.root i`, negating each root in `s` and their sum.
* `TauCeti.mem_inversions_mul_ofIdx_iff_of_pairing_eq_zero`: right multiplication by `sᵢ` preserves
  whether a root `αⱼ` with `⟨αⱼ, αᵢ^∨⟩ = 0` is an inversion.
* `TauCeti.ncard_inversions_mul_noncommProd_ofIdx_of_subset` and
  `TauCeti.ncard_inversions_mul_noncommProd_ofIdx_of_disjoint`: right multiplication by a product
  of pairwise orthogonal simple reflections changes the inversion count by `#s`.
* `TauCeti.inversions_noncommProd_ofIdx`: the inversion set of a product of pairwise orthogonal
  simple reflections is that set of simple roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, Claim 3.
-/

public section

namespace RootPairing

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- Reflections in pairwise orthogonal roots pairwise commute in the Weyl group. -/
theorem weylGroup.pairwise_commute_ofIdx_of_isOrthogonal {s : Set ι}
    (hs : s.Pairwise P.IsOrthogonal) :
    s.Pairwise (Function.onFun Commute (weylGroup.ofIdx P)) :=
  fun _ hi _ hj hij ↦ weylGroup.commute_ofIdx_of_isOrthogonal P (hs hi hj hij)

/-- Any unordered product of commuting root reflections in the Weyl group is an involution. -/
@[simp]
theorem weylGroup.noncommProd_ofIdx_mul_self (s : Finset ι)
    (comm : (s : Set ι).Pairwise (Function.onFun Commute (weylGroup.ofIdx P))) :
    s.noncommProd (weylGroup.ofIdx P) comm * s.noncommProd (weylGroup.ofIdx P) comm = 1 := by
  rw [← Finset.noncommProd_mul_distrib (comm_gf := comm),
    Finset.noncommProd_eq_pow_card s (weylGroup.ofIdx P * weylGroup.ofIdx P) _ 1
      (fun i _ ↦ weylGroup.ofIdx_mul_self P i),
    one_pow]

/-- Any unordered product of commuting root reflections in the Weyl group is its own inverse. -/
@[simp]
theorem weylGroup.noncommProd_ofIdx_inv (s : Finset ι)
    (comm : (s : Set ι).Pairwise (Function.onFun Commute (weylGroup.ofIdx P))) :
    (s.noncommProd (weylGroup.ofIdx P) comm)⁻¹ = s.noncommProd (weylGroup.ofIdx P) comm :=
  inv_eq_of_mul_eq_one_right (weylGroup.noncommProd_ofIdx_mul_self P s comm)

section Transport

variable {P} {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {Q : RootPairing ι₂ R M₂ N₂}

/-- **An equivalence of root pairings transports a commuting product of root reflections** by
mapping its index finset along `e.indexEquiv`. -/
theorem Equiv.weylGroupEquiv_noncommProd_ofIdx (e : P.Equiv Q) (s : Finset ι)
    (comm : (s : Set ι).Pairwise (Function.onFun Commute (weylGroup.ofIdx P))) :
    e.weylGroupEquiv (s.noncommProd (weylGroup.ofIdx P) comm) =
      (s.map e.indexEquiv.toEmbedding).noncommProd (weylGroup.ofIdx Q) (by
        intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
        rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
        simpa only [Function.onFun, Equiv.coe_toEmbedding, ← e.weylGroupEquiv_ofIdx] using
          (comm ha hb (ne_of_apply_ne _ hxy)).map e.weylGroupEquiv) := by
  rw [Finset.noncommProd_map, Finset.map_noncommProd]
  exact Finset.noncommProd_congr rfl (fun i _ ↦ e.weylGroupEquiv_ofIdx i) _

end Transport

/-- A commuting product of root reflections fixes any root index whose pairing with every root of
the product vanishes. -/
theorem weylGroupToPerm_noncommProd_ofIdx_of_forall_pairing_eq_zero (s : Finset ι)
    (comm : (s : Set ι).Pairwise (Function.onFun Commute (weylGroup.ofIdx P))) {j : ι}
    (hj : ∀ i ∈ s, P.pairing j i = 0) :
    P.weylGroupToPerm (s.noncommProd (weylGroup.ofIdx P) comm) j = j := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.noncommProd_cons, map_mul, Equiv.Perm.mul_apply,
      ih (comm.mono fun _ ↦ Finset.mem_cons_of_mem)
        (fun i hi ↦ hj i (Finset.mem_cons_of_mem hi)),
      weylGroupToPerm_ofIdx_apply,
      P.reflectionPerm_eq_of_pairing_eq_zero (hj a (Finset.mem_cons_self a t))]

/-- **Weight-space action of a product of pairwise orthogonal root reflections**: each reflection
subtracts its independent component `⟨x, αᵢ^∨⟩ • αᵢ`. -/
theorem weylGroup.noncommProd_ofIdx_smul {s : Finset ι} (hs : (s : Set ι).Pairwise P.IsOrthogonal)
    (x : M) :
    s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs) • x =
      x - ∑ i ∈ s, P.coroot' i x • P.root i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    have ht : (t : Set ι).Pairwise P.IsOrthogonal := hs.mono fun _ ↦ Finset.mem_cons_of_mem
    rw [Finset.noncommProd_cons, mul_smul, ih ht, weylGroup.ofIdx_smul, Equiv.reflection_smul,
      map_sub, map_sum, P.reflection_apply, Finset.sum_cons]
    have hfix : ∑ i ∈ t, P.reflection a (P.coroot' i x • P.root i) =
        ∑ i ∈ t, P.coroot' i x • P.root i :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [map_smul, (hs (Finset.mem_cons_self a t) (Finset.mem_cons_of_mem hi)
          (ne_of_mem_of_not_mem hi ha).symm).reflection_apply_right]
    rw [hfix, sub_sub]

/-- A product of pairwise orthogonal root reflections negates every root in the product. -/
theorem weylGroup.noncommProd_ofIdx_smul_root_of_mem {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {i : ι} (hi : i ∈ s) :
    s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs) • P.root i = -P.root i := by
  classical
  rw [weylGroup.noncommProd_ofIdx_smul P hs, ← Finset.add_sum_erase _ _ hi,
    root_coroot'_eq_pairing, pairing_same]
  have hzero : ∑ j ∈ s.erase i, P.coroot' j (P.root i) • P.root j = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [root_coroot'_eq_pairing,
        (hs hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm).1, zero_smul]
  rw [hzero, add_zero, two_smul, sub_add_cancel_left]

/-- A product of pairwise orthogonal root reflections negates the sum of the roots in the
product. -/
theorem weylGroup.noncommProd_ofIdx_smul_sum_root {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs) • ∑ i ∈ s, P.root i =
      -∑ i ∈ s, P.root i := by
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi ↦ weylGroup.noncommProd_ofIdx_smul_root_of_mem P hs hi

/-- On root indices, a product of pairwise orthogonal root reflections negates every root index in
the product. -/
theorem weylGroupToPerm_noncommProd_ofIdx_of_mem {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {i : ι} (hi : i ∈ s) :
    P.weylGroupToPerm (s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs)) i = P.reflectionPerm i i := by
  refine P.root.injective ?_
  rw [← P.weylGroup_apply_root, weylGroup.noncommProd_ofIdx_smul_root_of_mem P hs hi,
    root_reflectionPerm, reflection_apply_self]

end RootPairing

namespace TauCeti

open Finset RootPairing

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [CharZero R] (w : P.weylGroup) (b : P.Base)

/-- Right multiplication by `sᵢ` leaves unchanged whether a root `αⱼ` with `⟨αⱼ, αᵢ^∨⟩ = 0` belongs
to the inversion set. -/
theorem mem_inversions_mul_ofIdx_iff_of_pairing_eq_zero {i j : ι} (hij : P.pairing j i = 0) :
    j ∈ inversions P b (w * weylGroup.ofIdx P i) ↔ j ∈ inversions P b w := by
  simp only [mem_inversions, weylGroupToPerm_mul_ofIdx_apply,
    P.reflectionPerm_eq_of_pairing_eq_zero hij]

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **Simultaneous inversion drop for orthogonal simple roots.** If `s` is a finset of pairwise
orthogonal simple roots all belonging to the inversion set of `w`, right multiplication by their
commuting reflection product lowers the number of inversions by `#s`. -/
theorem ncard_inversions_mul_noncommProd_ofIdx_of_subset {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsupp : (s : Set ι) ⊆ b.support)
    (hinv : (s : Set ι) ⊆ inversions P b w) :
    (inversions P b (w * s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs))).ncard + #s =
      (inversions P b w).ncard := by
  induction s using Finset.cons_induction generalizing w with
  | empty => simp
  | cons a t ha ih =>
    have ht : (t : Set ι).Pairwise P.IsOrthogonal := hs.mono fun _ ↦ Finset.mem_cons_of_mem
    have ha_mem : a ∈ (Finset.cons a t ha : Set ι) := Finset.mem_cons_self a t
    have ht_supp : (t : Set ι) ⊆ b.support :=
      (Set.Subset.trans fun _ ↦ Finset.mem_cons_of_mem) hsupp
    have ht_inv : (t : Set ι) ⊆ inversions P b (w * weylGroup.ofIdx P a) := fun j hj ↦ by
      have hja : P.pairing j a = 0 :=
        (hs (Finset.mem_cons_of_mem hj) ha_mem (ne_of_mem_of_not_mem hj ha)).1
      exact (mem_inversions_mul_ofIdx_iff_of_pairing_eq_zero P w b hja).mpr
        (hinv (Finset.mem_cons_of_mem hj))
    have hstep := ih (w * weylGroup.ofIdx P a) ht ht_supp ht_inv
    have hdrop := ncard_inversions_mul_ofIdx_of_mem P w b (hsupp ha_mem) (hinv ha_mem)
    rw [Finset.noncommProd_cons, ← mul_assoc, Finset.card_cons]
    omega

/-- **Simultaneous inversion rise for orthogonal simple roots.** If `s` is a finset of pairwise
orthogonal simple roots none of which belongs to the inversion set of `w`, right multiplication by
their commuting reflection product raises the number of inversions by `#s`. -/
theorem ncard_inversions_mul_noncommProd_ofIdx_of_disjoint {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsupp : (s : Set ι) ⊆ b.support)
    (hdisj : Disjoint (s : Set ι) (inversions P b w)) :
    (inversions P b (w * s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs))).ncard =
      (inversions P b w).ncard + #s := by
  induction s using Finset.cons_induction generalizing w with
  | empty => simp
  | cons a t ha ih =>
    have ht : (t : Set ι).Pairwise P.IsOrthogonal := hs.mono fun _ ↦ Finset.mem_cons_of_mem
    have ha_mem : a ∈ (Finset.cons a t ha : Set ι) := Finset.mem_cons_self a t
    have ht_supp : (t : Set ι) ⊆ b.support :=
      (Set.Subset.trans fun _ ↦ Finset.mem_cons_of_mem) hsupp
    have ht_disj : Disjoint (t : Set ι) (inversions P b (w * weylGroup.ofIdx P a)) :=
      Set.disjoint_left.mpr fun j hj hjw ↦ by
        have hja : P.pairing j a = 0 :=
          (hs (Finset.mem_cons_of_mem hj) ha_mem (ne_of_mem_of_not_mem hj ha)).1
        exact Set.disjoint_left.mp hdisj (Finset.mem_cons_of_mem hj)
          ((mem_inversions_mul_ofIdx_iff_of_pairing_eq_zero P w b hja).mp hjw)
    have hstep := ih (w * weylGroup.ofIdx P a) ht ht_supp ht_disj
    have hrise := ncard_inversions_mul_ofIdx_of_notMem P w b (hsupp ha_mem)
      (Set.disjoint_left.mp hdisj ha_mem)
    rw [Finset.noncommProd_cons, ← mul_assoc, Finset.card_cons]
    omega

/-- **The inversion set of a product of pairwise orthogonal simple reflections is that set of
simple roots.** -/
theorem inversions_noncommProd_ofIdx {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsupp : (s : Set ι) ⊆ b.support) :
    inversions P b (s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs)) = (s : Set ι) := by
  refine (Set.eq_of_subset_of_ncard_le (fun i hi ↦ ?_) ?_ (Set.toFinite _)).symm
  · refine (mem_inversions P b _ i).mpr ⟨b.isPos_of_mem_support (hsupp hi), ?_⟩
    rw [weylGroupToPerm_noncommProd_ofIdx_of_mem P hs hi, ← mem_negRoots,
      reflectionPerm_self_mem_negRoots_iff_mem_posRoots, mem_posRoots]
    exact b.isPos_of_mem_support (hsupp hi)
  · have hcard := ncard_inversions_mul_noncommProd_ofIdx_of_disjoint P 1 b hs hsupp (by simp)
    rw [one_mul, ncard_inversions_one, zero_add, ← Set.ncard_coe_finset] at hcard
    exact hcard.le

/-- The inversion finset of a product of pairwise orthogonal simple reflections is that finset of
simple roots. -/
theorem inversionsFinset_noncommProd_ofIdx {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsupp : (s : Set ι) ⊆ b.support) :
    inversionsFinset P b (s.noncommProd (weylGroup.ofIdx P)
      (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P hs)) = s := by
  rw [← Finset.coe_inj, coe_inversionsFinset, inversions_noncommProd_ofIdx P b hs hsupp]

end TauCeti
