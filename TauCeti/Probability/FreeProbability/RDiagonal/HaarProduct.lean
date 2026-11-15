/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Kreweras
public import TauCeti.Probability.FreeProbability.HaarUnitary.Basic
public import TauCeti.Probability.FreeProbability.RDiagonal.Tracial
public import TauCeti.Probability.FreeProbability.StarIndependence

/-!
# Products of Haar unitaries and R-diagonal elements

This file establishes stability of Haar unitaries and R-diagonal elements under star-free
multiplication.

## Main results

* **Haar unitary absorption** (`TauCeti.IsHaarUnitary.mul_right`,
  `TauCeti.IsHaarUnitary.mul_left`): if `u` is a Haar unitary, `v` is unitary, and `![u, v]` is
  star-free, then `u * v` and `v * u` are Haar unitaries.
* **Stability of R-diagonality under star-free products** (`TauCeti.IsRDiagonal.mul_right`,
  `TauCeti.IsRDiagonal.mul_left`): if `u` is R-diagonal and `![u, b]` is star-free, then `u * b`
  and `b * u` are R-diagonal, without assuming positivity or traciality (Nica–Speicher,
  Proposition 15.8).
* **Haar-unitary product corollaries** (`TauCeti.IsHaarUnitary.isRDiagonal_mul_right`,
  `TauCeti.IsHaarUnitary.isRDiagonal_mul_left`,
  `TauCeti.IsHaarUnitary.isRDiagonal_of_starDistribution_mul_right_eq`,
  `TauCeti.IsHaarUnitary.isRDiagonal_of_starDistribution_mul_left_eq`): multiplying any element
  by a star-free Haar unitary produces an R-diagonal element, so invariance of the star
  distribution under multiplication by a star-free Haar unitary implies R-diagonality.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Proposition 15.8 and
  Theorem 15.10.
-/

public section

open Finset

namespace TauCeti

section HaarAbsorption

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A]

/-- If `x ∈ B i` and `y ∈ B j` lie in distinct members of a free family and at least one of `x`, `y`
has vanishing constant free cumulants of all positive orders, then `φ ((x * y) ^ n) = 0` for all
`n ≠ 0`. -/
private theorem apply_pow_mul_eq_zero_of_isFreelyIndependent {φ : A →ₗ[R] R}
    {B : ι → Subalgebra R A} (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    {x y : A} (hx : x ∈ B i) (hy : y ∈ B j)
    (hzero : (∀ m, m ≠ 0 → freeCumulant φ (fun _ : Fin m => x) univ = 0) ∨
      (∀ m, m ≠ 0 → freeCumulant φ (fun _ : Fin m => y) univ = 0))
    {n : ℕ} (hn : n ≠ 0) :
    φ ((x * y) ^ n) = 0 := by
  have hpart_zero {z : A} (hz : ∀ m, m ≠ 0 → freeCumulant φ (fun _ : Fin m => z) univ = 0)
      {C : Finset (Fin n)} (hC : C.Nonempty) (π : NoncrossingPartition C) :
      partitionCumulant φ (fun _ : Fin n => z) π = 0 := by
    obtain ⟨D, hD⟩ := π.1.parts_nonempty hC.ne_empty
    rw [partitionCumulant_eq_prod_freeCumulant]
    refine prod_eq_zero hD ?_
    rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin]
    exact hz #D (π.1.nonempty_of_mem_parts hD).card_pos.ne'
  have hcum : ∀ {C : Finset (Fin n)}, C.Nonempty →
      freeCumulant φ (fun _ : Fin n => x * y) C = 0 := by
    intro C hC
    rw [h.freeCumulant_mul_eq_sum_partitionCumulant_mul_partitionCumulant hφ hij
      (fun _ _ => hx) (fun _ _ => hy)]
    refine sum_eq_zero fun π _ => ?_
    rcases hzero with hx0 | hy0
    · rw [hpart_zero hx0 hC π, zero_mul]
    · rw [hpart_zero hy0 hC (NoncrossingPartition.kreweras π), mul_zero]
  have hpow : (x * y) ^ n = (List.ofFn fun _ : Fin n => x * y).prod := by
    simp [List.ofFn_const]
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [hpow, apply_prod_ofFn_eq_sum_prod_freeCumulant φ hn]
  refine sum_eq_zero fun σ _ => ?_
  obtain ⟨C, hC⟩ := σ.1.parts_nonempty univ_nonempty.ne_empty
  exact prod_eq_zero hC (hcum (σ.1.nonempty_of_mem_parts hC))

namespace IsHaarUnitary

variable [StarRing R] [StarRing A] [StarModule R A] {φ : A →ₗ[R] R} {u v : A}

/-- Right-multiplying a Haar unitary `u` by any star-free unitary `v` yields a Haar unitary. -/
theorem mul_right (hu : IsHaarUnitary φ u) (hv : v ∈ unitary A)
    (hfree : IsStarFreelyIndependentElements φ ![u, v]) :
    IsHaarUnitary φ (u * v) where
  mem_unitary := Submonoid.mul_mem _ hu.mem_unitary hv
  apply_one := hu.apply_one
  apply_pow_eq_zero {n} hn := by
    have hu_mem : u ∈ (StarAlgebra.adjoin R {![u, v] 0}).toSubalgebra :=
      StarAlgebra.subset_adjoin R _ rfl
    have hv_mem : v ∈ (StarAlgebra.adjoin R {![u, v] 1}).toSubalgebra :=
      StarAlgebra.subset_adjoin R _ rfl
    exact apply_pow_mul_eq_zero_of_isFreelyIndependent
      (isStarFreelyIndependentElements_iff.1 hfree) hu.apply_one
      (by decide : (0 : Fin 2) ≠ 1) hu_mem hv_mem
      (Or.inl fun _ hm => hu.freeCumulant_const_eq_zero hm) hn
  apply_star_pow_eq_zero {n} hn := by
    have hu_mem : Star.star u ∈ (StarAlgebra.adjoin R {![u, v] 0}).toSubalgebra :=
      StarSubalgebra.mem_toSubalgebra.2 (star_mem (StarAlgebra.subset_adjoin R _ rfl))
    have hv_mem : Star.star v ∈ (StarAlgebra.adjoin R {![u, v] 1}).toSubalgebra :=
      StarSubalgebra.mem_toSubalgebra.2 (star_mem (StarAlgebra.subset_adjoin R _ rfl))
    rw [star_mul]
    exact apply_pow_mul_eq_zero_of_isFreelyIndependent
      (isStarFreelyIndependentElements_iff.1 hfree) hu.apply_one
      (by decide : (1 : Fin 2) ≠ 0) hv_mem hu_mem
      (Or.inr fun _ hm => hu.star.freeCumulant_const_eq_zero hm) hn

/-- Left-multiplying a Haar unitary `u` by any star-free unitary `v` yields a Haar unitary. -/
theorem mul_left (hu : IsHaarUnitary φ u) (hv : v ∈ unitary A)
    (hfree : IsStarFreelyIndependentElements φ ![u, v]) :
    IsHaarUnitary φ (v * u) := by
  have hstar : Star.star (![u, v] : Fin 2 → A) = ![Star.star u, Star.star v] := by
    funext i; fin_cases i <;> rfl
  have hfree' : IsStarFreelyIndependentElements φ ![Star.star u, Star.star v] := by
    rw [← hstar, isStarFreelyIndependentElements_star_iff]
    exact hfree
  simpa only [star_mul, star_star] using
    (hu.star.mul_right (Unitary.star_mem hv) hfree').star

end IsHaarUnitary

end HaarAbsorption

section RDiagonalProduct

/-- If a nonempty convex subset of `(univ : Finset (Fin m)).interlace` determined by a predicate `P`
on the first coordinate is `σ`-saturated for some `σ` with `σ ⊔ interlacePairs univ = ⊤`, then `P`
holds on all of `Fin m`. -/
private theorem interlace_forall_of_saturated {m : ℕ}
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hsup : σ ⊔ NoncrossingPartition.interlacePairs univ = ⊤)
    {P : Fin m → Prop} [DecidablePred P] {x₀ : Fin m} (hx₀ : P x₀)
    (hconv : ∀ p ∈ {q ∈ (univ : Finset (Fin m)).interlace | P (ofLex q).1},
      ∀ r ∈ {q ∈ (univ : Finset (Fin m)).interlace | P (ofLex q).1},
      ∀ q ∈ (univ : Finset (Fin m)).interlace, p < q → q < r →
        q ∈ {q ∈ (univ : Finset (Fin m)).interlace | P (ofLex q).1})
    (hsat : ∀ p ∈ (univ : Finset (Fin m)).interlace, ∀ q ∈ σ.1.part p,
      P (ofLex p).1 → P (ofLex q).1)
    (x : Fin m) : P x := by
  let s : Finset (Fin m) := univ
  set T : Finset (Fin m ×ₗ Bool) := {q ∈ s.interlace | P (ofLex q).1}
  have hT (y : Fin m) (β : Bool) : toLex (y, β) ∈ T ↔ P y := by simp [T, s]
  have hp₀ : toLex (x₀, false) ∈ T := (hT x₀ false).2 hx₀
  have hTne : T.Nonempty := ⟨toLex (x₀, false), hp₀⟩
  let ρ : NoncrossingPartition s.interlace :=
    ⟨Finpartition.splitPartition s.interlace T hTne (filter_subset _ _),
      Finpartition.isNoncrossing_splitPartition hconv⟩
  have hiff : ∀ {p q}, p ∈ s.interlace → q ∈ s.interlace →
      (P (ofLex p).1 ↔ P (ofLex q).1) →
      q ∈ (Finpartition.splitPartition s.interlace T hTne (filter_subset _ _)).part p := by
    intro p q hp hq hpq
    by_cases hpP : P (ofLex p).1
    · rw [Finpartition.part_splitPartition_of_mem (mem_filter.2 ⟨hp, hpP⟩)]
      exact mem_filter.2 ⟨hq, hpq.1 hpP⟩
    · have hp_notT : p ∉ T := fun h => hpP (mem_filter.1 h).2
      rw [Finpartition.part_splitPartition_of_notMem hp hp_notT, mem_sdiff]
      exact ⟨hq, fun h => hpP (hpq.2 (mem_filter.1 h).2)⟩
  have hle₁ : σ ≤ ρ := by
    rw [← Subtype.coe_le_coe]
    refine Finpartition.le_iff_forall_part_subset.2 fun p q hq => ?_
    have hp : p ∈ s.interlace := σ.1.part_nonempty.1 ⟨q, hq⟩
    have hq_mem : q ∈ s.interlace := σ.1.part_subset p hq
    have hsymm := (σ.1.mem_part_iff_part_eq_part hq_mem hp).1 hq
    have hp' : p ∈ σ.1.part q := hsymm ▸ σ.1.mem_part_self.2 hp
    exact hiff hp hq_mem ⟨hsat p hp q hq, hsat q hq_mem p hp'⟩
  have hle₂ : NoncrossingPartition.interlacePairs s ≤ ρ := by
    rw [← Subtype.coe_le_coe]
    refine Finpartition.le_iff_forall_part_subset.2 fun p q hq => ?_
    have hp : p ∈ s.interlace := (NoncrossingPartition.interlacePairs s).1.part_nonempty.1 ⟨q, hq⟩
    obtain ⟨⟨y, β⟩, rfl⟩ := toLex.surjective p
    rw [NoncrossingPartition.part_interlacePairs (mem_univ y)] at hq
    rcases mem_insert.1 hq with rfl | hq'
    · exact hiff hp (toLex_mem_interlace.2 (mem_univ y)) Iff.rfl
    · rw [mem_singleton.1 hq']
      exact hiff hp (toLex_mem_interlace.2 (mem_univ y)) Iff.rfl
  have htop : (⊤ : NoncrossingPartition s.interlace) ≤ ρ := hsup ▸ sup_le hle₁ hle₂
  have htop_mem : toLex (x, false) ∈ (⊤ : Finpartition s.interlace).part (toLex (x₀, false)) := by
    rw [Finpartition.part_top (toLex_mem_interlace.2 (mem_univ x₀))]
    exact toLex_mem_interlace.2 (mem_univ x)
  have hmem := Finpartition.part_mono (Subtype.coe_le_coe.2 htop) (toLex (x₀, false)) htop_mem
  change toLex (x, false) ∈
    (Finpartition.splitPartition s.interlace T hTne (filter_subset _ _)).part
      (toLex (x₀, false)) at hmem
  rw [Finpartition.part_splitPartition_of_mem hp₀] at hmem
  exact (hT x false).1 hmem

/-- If a part `C` of `σ` (`σ ⊔ interlacePairs univ = ⊤`) has minimum `(c, false)` and maximum
`(d, true)`, then `[c, d]` covers all of `Fin m`. -/
private theorem interlace_closed_interval_eq_univ {m : ℕ}
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hsup : σ ⊔ NoncrossingPartition.interlacePairs univ = ⊤)
    {C : Finset (Fin m ×ₗ Bool)} (hC : C ∈ σ.1.parts) {c d : Fin m} (hcd : c ≤ d)
    (hcC : toLex (c, false) ∈ C) (hdC : toLex (d, true) ∈ C)
    (hmin : ∀ r ∈ C, toLex (c, false) ≤ r) (hmax : ∀ r ∈ C, r ≤ toLex (d, true))
    (x : Fin m) : c ≤ x ∧ x ≤ d := by
  have hord (p : Fin m ×ₗ Bool) :
      (c ≤ (ofLex p).1 ∧ (ofLex p).1 ≤ d) ↔ toLex (c, false) ≤ p ∧ p ≤ toLex (d, true) := by
    obtain ⟨⟨y, β⟩, rfl⟩ := toLex.surjective p
    rw [ofLex_toLex, Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_le_toLex]
    cases β <;> simp [le_iff_lt_or_eq, eq_comm]
  refine interlace_forall_of_saturated hsup (P := fun y => c ≤ y ∧ y ≤ d) ⟨le_rfl, hcd⟩
    (fun p hp r hr q hq hpq hqr => ?_) (fun p hp q hq hpP => ?_) x
  · simp only [mem_filter, hord] at hp hr ⊢
    exact ⟨hq, hp.2.1.trans hpq.le, hqr.le.trans hr.2.2⟩
  · rw [hord] at hpP ⊢
    by_cases hpC : σ.1.part p = C
    · have hqC : q ∈ C := hpC ▸ hq
      exact ⟨hmin q hqC, hmax q hqC⟩
    · have hp_notC : p ∉ C := fun h => hpC (σ.1.part_eq_of_mem hC h)
      have hplt₁ : toLex (c, false) < p := hpP.1.lt_of_ne fun h => hp_notC (h ▸ hcC)
      have hplt₂ : p < toLex (d, true) := hpP.2.lt_of_ne fun h => hp_notC (h ▸ hdC)
      by_contra hq_not
      rcases not_and_or.1 hq_not with hq₁ | hq₂
      · exact hpC (Finpartition.isNoncrossing_iff.1 σ.2 (σ.1.part p) (σ.1.part_mem.2 hp) C hC
          q hq (toLex (c, false)) hcC p (σ.1.mem_part_self.2 hp) (toLex (d, true)) hdC
          (lt_of_not_ge hq₁) hplt₁ hplt₂)
      · exact hpC (Finpartition.isNoncrossing_iff.1 σ.2 C hC (σ.1.part p) (σ.1.part_mem.2 hp)
          (toLex (c, false)) hcC p (σ.1.mem_part_self.2 hp) (toLex (d, true)) hdC q hq
          hplt₁ hplt₂ (lt_of_not_ge hq₂)).symm

/-- If `(c, true)` and `(d, false)` (`c < d`) are consecutive elements of a part `C` of `σ`
(`σ ⊔ interlacePairs univ = ⊤`), then `c` and `d` are adjacent in `Fin m`. -/
private theorem interlace_open_interval_adj {m : ℕ}
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hsup : σ ⊔ NoncrossingPartition.interlacePairs univ = ⊤)
    {C : Finset (Fin m ×ₗ Bool)} (hC : C ∈ σ.1.parts) {c d : Fin m} (hcd : c < d)
    (hcC : toLex (c, true) ∈ C) (hdC : toLex (d, false) ∈ C)
    (hadj : ∀ r ∈ C, r ≤ toLex (c, true) ∨ toLex (d, false) ≤ r) :
    (d : ℕ) = (c : ℕ) + 1 := by
  by_contra hne
  have hlt : (c : ℕ) + 1 < (d : ℕ) := Nat.lt_of_le_of_ne hcd (Ne.symm hne)
  let x₀ : Fin m := ⟨(c : ℕ) + 1, hlt.trans d.isLt⟩
  have hx₀ : c < x₀ ∧ x₀ < d := ⟨Nat.lt_succ_self _, hlt⟩
  have hord (p : Fin m ×ₗ Bool) :
      (c < (ofLex p).1 ∧ (ofLex p).1 < d) ↔ toLex (c, true) < p ∧ p < toLex (d, false) := by
    obtain ⟨⟨y, β⟩, rfl⟩ := toLex.surjective p
    simp only [ofLex_toLex, Prod.Lex.toLex_lt_toLex]
    cases β <;> simp
  have hall := interlace_forall_of_saturated hsup (P := fun y => c < y ∧ y < d) hx₀
    (fun p hp r hr q hq hpq hqr => ?_) (fun p hp q hq hpP => ?_) c
  · exact lt_irrefl c hall.1
  · simp only [mem_filter, hord] at hp hr ⊢
    exact ⟨hq, hp.2.1.trans_le hpq.le, hqr.le.trans_lt hr.2.2⟩
  · rw [hord] at hpP ⊢
    have hp_notC : p ∉ C := fun h => by
      rcases hadj p h with h₁ | h₂
      exacts [not_lt_of_ge h₁ hpP.1, not_lt_of_ge h₂ hpP.2]
    have hpC : σ.1.part p ≠ C := fun h => hp_notC (h ▸ σ.1.mem_part_self.2 hp)
    have hsymm := (σ.1.mem_part_iff_part_eq_part (σ.1.part_subset p hq) hp).1 hq
    have hq_notC : q ∉ C := fun h => hpC (hsymm.symm.trans (σ.1.part_eq_of_mem hC h))
    by_contra hq_not
    rcases not_and_or.1 hq_not with hq₁ | hq₂
    · have hqle : q ≤ toLex (c, true) := le_of_not_gt hq₁
      have hqlt : q < toLex (c, true) := hqle.lt_of_ne fun h => hq_notC (h ▸ hcC)
      exact hpC (Finpartition.isNoncrossing_iff.1 σ.2 (σ.1.part p) (σ.1.part_mem.2 hp) C hC
        q hq (toLex (c, true)) hcC p (σ.1.mem_part_self.2 hp) (toLex (d, false)) hdC
        hqlt hpP.1 hpP.2)
    · have hqge : toLex (d, false) ≤ q := le_of_not_gt hq₂
      have hqgt : toLex (d, false) < q := hqge.lt_of_ne fun h => hq_notC (h.symm ▸ hdC)
      exact hpC (Finpartition.isNoncrossing_iff.1 σ.2 C hC (σ.1.part p) (σ.1.part_mem.2 hp)
        (toLex (c, true)) hcC p (σ.1.mem_part_self.2 hp) (toLex (d, false)) hdC q hq
        hpP.1 hpP.2 hqgt).symm

/-- A Boolean word of length `2 * (n + 1)` with `n + 1` `true` entries in which no cyclic step keeps
`true` fixed must be the alternating word `rDiagonalWord (w 0) (2 * (n + 1))`. -/
private theorem eq_rDiagonalWord_of_card_true {n : ℕ} (w : Fin (2 * (n + 1)) → Bool)
    (hcard : #{k : Fin (2 * (n + 1)) | w k = true} = n + 1)
    (hstep : ∀ (k : Fin (2 * (n + 1))) (hk : (k : ℕ) + 1 < 2 * (n + 1)),
      w k = true → w ⟨(k : ℕ) + 1, hk⟩ = false)
    (hwrap : w 0 = true → w ⟨2 * n + 1, by omega⟩ = false)
    (i : Fin (2 * (n + 1))) :
    w i = rDiagonalWord (w 0) (2 * (n + 1)) i := by
  let f (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
    if hk : (k : ℕ) + 1 < 2 * (n + 1) then ⟨(k : ℕ) + 1, hk⟩ else 0
  let next : Fin (2 * (n + 1)) ↪ Fin (2 * (n + 1)) := ⟨f, fun a b hab => by
    have := a.isLt; have := b.isLt; dsimp only [f] at hab
    split_ifs at hab <;> apply Fin.ext <;> simp only [Fin.ext_iff, Fin.val_zero] at hab <;> omega⟩
  let S : Finset (Fin (2 * (n + 1))) := {k ∈ univ | w k = true}
  let R : Finset (Fin (2 * (n + 1))) := S.map next
  have hcyc (k : Fin (2 * (n + 1))) (hk : w k = true) : w (next k) = false := by
    change w (f k) = false; dsimp only [f]
    split_ifs with hlt
    · exact hstep k hlt hk
    · have hkeq : k = ⟨2 * n + 1, by omega⟩ := Fin.ext (by dsimp only; have := k.isLt; omega)
      by_contra h0
      have h0' : w 0 = true := by revert h0; cases w 0 <;> simp
      exact absurd (hkeq ▸ hk) (by rw [hwrap h0']; decide)
  have hdisj : Disjoint S R := disjoint_left.2 fun x hxS hxR => by
    obtain ⟨k, hkS, rfl⟩ := mem_map.1 hxR
    exact absurd (hcyc k (mem_filter.1 hkS).2) (by rw [(mem_filter.1 hxS).2]; decide)
  have huniv : S ∪ R = univ := eq_univ_of_card _ (by
    rw [card_union_of_disjoint hdisj, show #R = #S from card_map _, hcard, Fintype.card_fin]
    omega)
  have hadj (j : ℕ) (hj : j + 1 < 2 * (n + 1)) :
      w ⟨j + 1, hj⟩ = !w ⟨j, Nat.lt_of_succ_lt hj⟩ := by
    let k : Fin (2 * (n + 1)) := ⟨j, Nat.lt_of_succ_lt hj⟩
    have hnext : next k = ⟨j + 1, hj⟩ := by
      change f k = _; dsimp only [f, k]; exact dite_eq_left_of_eq_true (eq_true hj)
    rw [← hnext]
    by_cases hk : w k = true
    · rw [hcyc k hk, hk]; rfl
    · have hkS : k ∉ S := fun h => hk (mem_filter.1 h).2
      have hfkS : next k ∈ S :=
        (mem_union.1 (huniv ▸ mem_univ _)).resolve_right (mt (mem_map' next).1 hkS)
      rw [(mem_filter.1 hfkS).2, Bool.eq_false_iff.2 hk]; rfl
  obtain ⟨m, hm'⟩ := i
  induction m with
  | zero => simp [rDiagonalWord_apply]
  | succ m ih =>
    rw [hadj m hm', ih (Nat.lt_of_succ_lt hm')]
    simp only [rDiagonalWord_apply, Nat.even_add_one]
    by_cases he : Even m <;> simp [he]

/-- Each Boolean value appears exactly `k + 1` times in `rDiagonalWord c (2 * (k + 1))`. -/
private theorem card_filter_rDiagonalWord (c : Bool) (k : ℕ) (β : Bool) :
    #{i : Fin (2 * (k + 1)) | rDiagonalWord c (2 * (k + 1)) i = β} = k + 1 := by
  induction k with
  | zero =>
    simp only [rDiagonalWord_apply]
    cases c <;> cases β <;> decide
  | succ k ih =>
    have h2 : 2 * (k + 1 + 1) = 2 * (k + 1) + 1 + 1 := by omega
    rw [h2, Fin.card_filter_univ_succ', Fin.card_filter_univ_succ']
    have hcast : ∀ i : Fin (2 * (k + 1)),
        (rDiagonalWord c (2 * (k + 1) + 1 + 1) i.succ.succ = β) ↔
          (rDiagonalWord c (2 * (k + 1)) i = β) := fun i => by
      simp only [rDiagonalWord_apply, Fin.val_succ, Nat.even_add_one, not_not]
    rw [filter_congr fun i _ => hcast i, ih]
    have he₀ : Even (0 : ℕ) := ⟨0, rfl⟩
    have he₁ : ¬ Even (1 : ℕ) := by decide
    simp only [Fin.val_zero, Fin.val_succ, zero_add, rDiagonalWord_apply, he₀, he₁]
    cases c <;> cases β <;> simp <;> omega

private theorem step_of_lt_card_part {m : ℕ} {w : Fin m → Bool}
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hsup : σ ⊔ NoncrossingPartition.interlacePairs univ = ⊤)
    {C : Finset (Fin m ×ₗ Bool)} (hC : C ∈ σ.1.parts)
    (hCU : ∀ p ∈ C, (ofLex p).2 = w (ofLex p).1)
    {c₀ : Bool} (halt : ∀ i : Fin #C, (ofLex (C.orderEmbOfFin rfl i)).2 = rDiagonalWord c₀ #C i)
    {k : Fin m} {i : Fin #C} (hi : C.orderEmbOfFin rfl i = toLex (k, true))
    (hilast : (i : ℕ) + 1 < #C) :
    ∃ hk : (k : ℕ) + 1 < m, w ⟨(k : ℕ) + 1, hk⟩ = false := by
  let e := C.orderEmbOfFin rfl
  let i' : Fin #C := ⟨(i : ℕ) + 1, hilast⟩
  have hi_true : rDiagonalWord c₀ #C i = true := by rw [← halt i, hi]; rfl
  have hi'_false : (ofLex (e i')).2 = false := by
    rw [halt i']
    rw [rDiagonalWord_apply] at hi_true
    simp only [rDiagonalWord_apply, show (i' : ℕ) = (i : ℕ) + 1 from rfl, Nat.even_add_one]
    by_cases he : Even (i : ℕ) <;> simp_all
  obtain ⟨⟨d, β⟩, hd⟩ := toLex.surjective (e i')
  have hβ : β = false := by rw [← hi'_false, ← hd]; rfl
  subst hβ
  have hlt_e : toLex (k, true) < toLex (d, false) := by
    rw [← hi, hd]; exact e.strictMono (Nat.lt_succ_self _)
  have hkd : k < d := (Prod.Lex.toLex_lt_toLex.1 hlt_e).elim id fun ⟨_, h⟩ =>
    absurd h (by dsimp only; decide)
  have hadjC : ∀ r ∈ C, r ≤ toLex (k, true) ∨ toLex (d, false) ≤ r := fun r hr => by
    obtain ⟨j, rfl⟩ : r ∈ Set.range e := by rwa [range_orderEmbOfFin]
    by_cases hj : (j : ℕ) ≤ (i : ℕ)
    · exact Or.inl (hi ▸ e.monotone hj)
    · exact Or.inr (hd.symm ▸ e.monotone (show (i' : ℕ) ≤ (j : ℕ) by dsimp [i']; omega))
  have hdeq := interlace_open_interval_adj hsup hC hkd (hi ▸ orderEmbOfFin_mem C rfl i)
    (hd.symm ▸ orderEmbOfFin_mem C rfl i') hadjC
  have hklt : (k : ℕ) + 1 < m := hdeq ▸ d.isLt
  have hd_eq : d = ⟨(k : ℕ) + 1, hklt⟩ := Fin.ext hdeq
  exact ⟨hklt, hd_eq ▸ (hCU (toLex (d, false)) (hd.symm ▸ orderEmbOfFin_mem C rfl i')).symm⟩

private theorem last_of_not_lt_card_part {m k₀ : ℕ} {w : Fin m → Bool}
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hsup : σ ⊔ NoncrossingPartition.interlacePairs univ = ⊤)
    {C : Finset (Fin m ×ₗ Bool)} (hC : C ∈ σ.1.parts)
    (hCU : ∀ p ∈ C, (ofLex p).2 = w (ofLex p).1)
    {c₀ : Bool} (hcardC : #C = 2 * (k₀ + 1))
    (halt : ∀ i : Fin #C, (ofLex (C.orderEmbOfFin rfl i)).2 = rDiagonalWord c₀ #C i)
    {k : Fin m} {i : Fin #C} (hi : C.orderEmbOfFin rfl i = toLex (k, true))
    (hilast : ¬ ((i : ℕ) + 1 < #C)) :
    w ⟨0, k.pos⟩ = false ∧ ∀ x : Fin m, x ≤ k := by
  let e := C.orderEmbOfFin rfl
  have hi_true : rDiagonalWord c₀ #C i = true := by rw [← halt i, hi]; rfl
  have := i.isLt
  have hi_eq : (i : ℕ) = 2 * k₀ + 1 := by omega
  have hnot_even : ¬ Even (2 * k₀ + 1) := by rintro ⟨t, ht⟩; omega
  have hc₀ : c₀ = false := by
    simpa only [rDiagonalWord_apply, hi_eq, hnot_even, ite_false, Bool.not_eq_true'] using hi_true
  subst hc₀
  let i₀ : Fin #C := ⟨0, by omega⟩
  have h0_false : (ofLex (e i₀)).2 = false := by rw [halt i₀, rDiagonalWord_apply]; simp [i₀]
  obtain ⟨⟨c, β⟩, hc⟩ := toLex.surjective (e i₀)
  have hβ : β = false := by rw [← h0_false, ← hc]; rfl
  subst hβ
  have hle_e : toLex (c, false) ≤ toLex (k, true) := by
    rw [hc, ← hi]; exact e.monotone (Nat.zero_le _)
  have hck : c ≤ k := Prod.Lex.monotone_fst_ofLex hle_e
  have hminC : ∀ r ∈ C, toLex (c, false) ≤ r := fun r hr => by
    obtain ⟨j, rfl⟩ : r ∈ Set.range e := by rwa [range_orderEmbOfFin]
    exact hc.symm ▸ e.monotone (Nat.zero_le _)
  have hmaxC : ∀ r ∈ C, r ≤ toLex (k, true) := fun r hr => by
    obtain ⟨j, rfl⟩ : r ∈ Set.range e := by rwa [range_orderEmbOfFin]
    exact hi ▸ e.monotone (Fin.le_def.2 (by have := j.isLt; omega))
  have hall := interlace_closed_interval_eq_univ hsup hC hck
    (hc.symm ▸ orderEmbOfFin_mem C rfl i₀) (hi ▸ orderEmbOfFin_mem C rfl i) hminC hmaxC
  have hc0 : c = ⟨0, k.pos⟩ := le_antisymm (hall ⟨0, k.pos⟩).1 (Nat.zero_le _)
  exact ⟨hc0 ▸ (hCU (toLex (c, false)) (hc.symm ▸ orderEmbOfFin_mem C rfl i₀)).symm,
    fun x => (hall x).2⟩

/-- For any `k` with `w k = true`, either `k` is the maximum of `Fin m` and `w 0 = false`, or
`w (k + 1) = false`. -/
private theorem step_or_last_of_true {m : ℕ} {w : Fin m → Bool}
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hsup : σ ⊔ NoncrossingPartition.interlacePairs univ = ⊤)
    (hmono : ∀ C ∈ σ.1.parts, ∀ p ∈ C, ∀ q ∈ C,
      ((ofLex p).2 == w (ofLex p).1) = ((ofLex q).2 == w (ofLex q).1))
    (hU_alt : ∀ C ∈ σ.1.parts, (∀ p ∈ C, (ofLex p).2 = w (ofLex p).1) →
      ∃ k₀ c₀, #C = 2 * (k₀ + 1) ∧
        ∀ i : Fin #C, (ofLex (C.orderEmbOfFin rfl i)).2 = rDiagonalWord c₀ #C i)
    {k : Fin m} (hwk : w k = true) :
    (w ⟨0, k.pos⟩ = false ∧ ∀ x : Fin m, x ≤ k) ∨
      ∃ hk : (k : ℕ) + 1 < m, w ⟨(k : ℕ) + 1, hk⟩ = false := by
  have hp : toLex (k, true) ∈ (univ : Finset (Fin m)).interlace :=
    toLex_mem_interlace.2 (mem_univ k)
  let C := σ.1.part (toLex (k, true))
  have hC : C ∈ σ.1.parts := σ.1.part_mem.2 hp
  have hkC : toLex (k, true) ∈ C := σ.1.mem_part_self.2 hp
  have hCU : ∀ q ∈ C, (ofLex q).2 = w (ofLex q).1 := fun q hq => by
    simpa [hwk] using hmono C hC q hq (toLex (k, true)) hkC
  obtain ⟨k₀, c₀, hcardC, halt⟩ := hU_alt C hC hCU
  obtain ⟨i, hi⟩ : toLex (k, true) ∈ Set.range (C.orderEmbOfFin rfl) := by
    rwa [range_orderEmbOfFin]
  by_cases hilast : (i : ℕ) + 1 < #C
  · exact Or.inr (step_of_lt_card_part hsup hC hCU halt hi hilast)
  · exact Or.inl (last_of_not_lt_card_part hsup hC hCU hcardC halt hi hilast)

variable {R A : Type*} [CommRing R] [StarRing R]
  [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
  {φ : A →ₗ[R] R} {u b : A}

/-- The interlaced word for `u * b` and `star (u * b) = star b * star u` along `w : Fin m → Bool`:
positions with `(ofLex p).2 = w (ofLex p).1` carry `u` or `star u`, and the complementary positions
carry `b` or `star b`. -/
private def rDiagonalProdWord (u b : A) {m : ℕ} (w : Fin m → Bool) (p : Fin m ×ₗ Bool) : A :=
  if (ofLex p).2 = w (ofLex p).1 then
    if (ofLex p).2 then star u else u
  else
    if (ofLex p).2 then b else star b

private theorem fiberProd_rDiagonalProdWord {m : ℕ} (w : Fin m → Bool) (x : Fin m) :
    fiberProd (rDiagonalProdWord u b w) (univ : Finset (Fin m)).interlace
      (fun p => (ofLex p).1) x =
      if w x then star (u * b) else u * b := by
  rw [fiberProd_def, filter_interlace_fst_eq (mem_univ x), sort_pair _
    (show toLex (x, false) ≤ toLex (x, true) from
      Prod.Lex.toLex_le_toLex.2 (Or.inr ⟨rfl, Bool.false_le _⟩))
    (fun h => Bool.noConfusion (Prod.mk.inj (toLex.injective h)).2)]
  cases hwx : w x <;> simp [rDiagonalProdWord, hwx, star_mul]

private theorem card_filter_snd_eq_of_rDiagonalWord {m k₀ : ℕ} {c₀ : Bool}
    {C : Finset (Fin m ×ₗ Bool)} (hcardC : #C = 2 * (k₀ + 1))
    (halt : ∀ i : Fin #C, (ofLex (C.orderEmbOfFin rfl i)).2 = rDiagonalWord c₀ #C i) :
    #{p ∈ C | (ofLex p).2 = false} = #{p ∈ C | (ofLex p).2 = true} := by
  have hbij (β : Bool) : #{p ∈ C | (ofLex p).2 = β} =
      #{i : Fin #C | rDiagonalWord c₀ #C i = β} := by
    refine card_bij (fun p hp => (Equiv.ofInjective _ (C.orderEmbOfFin rfl).injective).symm
        ⟨p, (range_orderEmbOfFin C rfl).symm ▸ (mem_filter.1 hp).1⟩)
      (fun p hp => ?_) (fun p₁ hp₁ p₂ hp₂ heq => ?_) (fun i hi => ?_)
    · simp only [mem_filter, mem_univ, true_and] at hp ⊢
      rw [← halt]
      have hval := Equiv.apply_ofInjective_symm (C.orderEmbOfFin rfl).injective
        ⟨p, (range_orderEmbOfFin C rfl).symm ▸ hp.1⟩
      exact (congrArg (fun z : Fin m ×ₗ Bool => (ofLex z).2) hval).trans hp.2
    · have h₁ := Equiv.apply_ofInjective_symm (C.orderEmbOfFin rfl).injective
        ⟨p₁, (range_orderEmbOfFin C rfl).symm ▸ (mem_filter.1 hp₁).1⟩
      have h₂ := Equiv.apply_ofInjective_symm (C.orderEmbOfFin rfl).injective
        ⟨p₂, (range_orderEmbOfFin C rfl).symm ▸ (mem_filter.1 hp₂).1⟩
      exact h₁.symm.trans ((congrArg _ heq).trans h₂)
    · refine ⟨C.orderEmbOfFin rfl i, mem_filter.2 ⟨orderEmbOfFin_mem C rfl i,
        (halt i).trans (mem_filter.1 hi).2⟩,
        Equiv.ofInjective_symm_apply (C.orderEmbOfFin rfl).injective i⟩
  rw [hbij false, hbij true, hcardC, card_filter_rDiagonalWord, card_filter_rDiagonalWord]

/-- If every `U`-part of a monochromatic partition `σ` has even alternating `.2` entries, then `w`
has the same number of `false` and `true` entries. -/
private theorem card_filter_false_eq_true_of_parts {m : ℕ} {w : Fin m → Bool}
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hmono : ∀ C ∈ σ.1.parts, ∀ p ∈ C, ∀ q ∈ C,
      ((ofLex p).2 == w (ofLex p).1) = ((ofLex q).2 == w (ofLex q).1))
    (hU_alt : ∀ C ∈ σ.1.parts, (∀ p ∈ C, (ofLex p).2 = w (ofLex p).1) →
      ∃ k₀ c₀, #C = 2 * (k₀ + 1) ∧
        ∀ i : Fin #C, (ofLex (C.orderEmbOfFin rfl i)).2 = rDiagonalWord c₀ #C i) :
    #{k : Fin m | w k = false} = #{k : Fin m | w k = true} := by
  let P_U := {C ∈ σ.1.parts | ∀ p ∈ C, (ofLex p).2 = w (ofLex p).1}
  have hbiUnion_U : P_U.biUnion id =
      {p ∈ (univ : Finset (Fin m)).interlace | (ofLex p).2 = w (ofLex p).1} := by
    ext p
    simp only [P_U, mem_biUnion, id_eq, mem_filter]
    refine ⟨fun ⟨C, ⟨hC, hCU⟩, hpC⟩ => ⟨σ.1.le hC hpC, hCU p hpC⟩, fun ⟨hp, hpU⟩ => ?_⟩
    refine ⟨σ.1.part p, ⟨σ.1.part_mem.2 hp, fun q hq => ?_⟩, σ.1.mem_part_self.2 hp⟩
    simpa [hpU] using hmono (σ.1.part p) (σ.1.part_mem.2 hp) q hq p (σ.1.mem_part_self.2 hp)
  have hdisj_PU : (P_U : Set (Finset (Fin m ×ₗ Bool))).PairwiseDisjoint id :=
    σ.1.disjoint.subset (coe_subset.2 (filter_subset _ _))
  have hcount (β : Bool) :
      #{k : Fin m | w k = β} = ∑ C ∈ P_U, #{p ∈ C | (ofLex p).2 = β} := by
    rw [← card_biUnion (fun C hC D hD hCD => disjoint_of_subset_left (filter_subset _ C)
      (disjoint_of_subset_right (filter_subset _ D) (hdisj_PU hC hD hCD)))]
    have hfilt : P_U.biUnion (fun C => {p ∈ C | (ofLex p).2 = β}) =
        {p ∈ P_U.biUnion id | (ofLex p).2 = β} := by
      ext p; simp only [mem_biUnion, mem_filter, id_eq]
      exact ⟨fun ⟨C, hC, hpC, hβ⟩ => ⟨⟨C, hC, hpC⟩, hβ⟩,
        fun ⟨⟨C, hC, hpC⟩, hβ⟩ => ⟨C, hC, hpC, hβ⟩⟩
    rw [hfilt, hbiUnion_U]
    refine card_bij (fun k _ => toLex (k, β))
      (fun k hk => by simp [(mem_filter.1 hk).2])
      (fun k₁ _ k₂ _ h => (Prod.mk.inj (toLex.injective h)).1)
      (fun p hp => ?_)
    obtain ⟨⟨k, γ⟩, rfl⟩ := toLex.surjective p
    simp only [mem_filter, ofLex_toLex] at hp
    exact ⟨k, mem_filter.2 ⟨mem_univ k, hp.1.2.symm.trans hp.2⟩, by rw [hp.2]⟩
  rw [hcount false, hcount true]
  refine sum_congr rfl fun C hCPU => ?_
  obtain ⟨k₀, c₀, hcardC, halt⟩ := hU_alt C (mem_filter.1 hCPU).1 (mem_filter.1 hCPU).2
  exact card_filter_snd_eq_of_rDiagonalWord hcardC halt

/-- If a noncrossing partition `σ` of `univ.interlace` with `σ ⊔ interlacePairs univ = ⊤` has
nonzero cumulant product for `rDiagonalProdWord u b w`, then `w` must be an even alternating
word. -/
private theorem exists_rDiagonalWord_of_prod_ne_zero (hu : IsRDiagonal φ u)
    (hfree : IsStarFreelyIndependentElements φ ![u, b]) {m : ℕ} (hm : m ≠ 0) (w : Fin m → Bool)
    {σ : NoncrossingPartition (univ : Finset (Fin m)).interlace}
    (hsup : σ ⊔ NoncrossingPartition.interlacePairs univ = ⊤)
    (hσ : ∏ C ∈ σ.1.parts, freeCumulant φ (rDiagonalProdWord u b w) C ≠ 0) :
    ∃ n c, m = 2 * (n + 1) ∧ ∀ i, w i = rDiagonalWord c m i := by
  have hmono : ∀ C ∈ σ.1.parts, ∀ p ∈ C, ∀ q ∈ C,
      ((ofLex p).2 == w (ofLex p).1) = ((ofLex q).2 == w (ofLex q).1) := fun C hC p hp q hq => by
    by_contra hne
    refine hσ (prod_eq_zero hC ?_)
    refine (isStarFreelyIndependentElements_iff.1 hfree).freeCumulant_eq_zero
      (ℓ := fun r => if (ofLex r).2 = w (ofLex r).1 then (0 : Fin 2) else 1) hu.apply_one
      (fun r _ => ?_) hp hq ?_
    · have hu_mem : u ∈ (StarAlgebra.adjoin R {![u, b] 0}).toSubalgebra :=
        StarAlgebra.subset_adjoin R _ rfl
      have hb_mem : b ∈ (StarAlgebra.adjoin R {![u, b] 1}).toSubalgebra :=
        StarAlgebra.subset_adjoin R _ rfl
      have hsu_mem : Star.star u ∈ (StarAlgebra.adjoin R {![u, b] 0}).toSubalgebra :=
        StarSubalgebra.mem_toSubalgebra.2 (star_mem (StarAlgebra.subset_adjoin R _ rfl))
      have hsb_mem : Star.star b ∈ (StarAlgebra.adjoin R {![u, b] 1}).toSubalgebra :=
        StarSubalgebra.mem_toSubalgebra.2 (star_mem (StarAlgebra.subset_adjoin R _ rfl))
      dsimp only [rDiagonalProdWord]; split_ifs <;> assumption
    · revert hne
      by_cases h1 : (ofLex p).2 = w (ofLex p).1 <;>
        by_cases h2 : (ofLex q).2 = w (ofLex q).1 <;> simp [h1, h2]
  have hU_alt : ∀ C ∈ σ.1.parts, (∀ p ∈ C, (ofLex p).2 = w (ofLex p).1) →
      ∃ k₀ c₀, #C = 2 * (k₀ + 1) ∧
        ∀ i : Fin #C, (ofLex (C.orderEmbOfFin rfl i)).2 = rDiagonalWord c₀ #C i := by
    intro C hC hCU
    have hC_nz : freeCumulant φ (rDiagonalProdWord u b w) C ≠ 0 :=
      fun hz => hσ (prod_eq_zero hC hz)
    rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin,
      show (rDiagonalProdWord u b w ∘ C.orderEmbOfFin rfl) =
          fun i : Fin #C => if (ofLex (C.orderEmbOfFin rfl i)).2 then star u else u from
        funext fun i => by
          simp [Function.comp_apply, rDiagonalProdWord, hCU _ (orderEmbOfFin_mem C rfl i)]] at hC_nz
    by_contra hnot
    exact hC_nz (hu.freeCumulant_eq_zero (σ.1.nonempty_of_mem_parts hC).card_pos.ne' _ hnot)
  have hbal := card_filter_false_eq_true_of_parts hmono hU_alt
  have hsum_m : #{k : Fin m | w k = false} + #{k : Fin m | w k = true} = m := by
    simpa only [Bool.not_eq_false, card_univ, Fintype.card_fin] using
      card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun k => w k = false)
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 * (n + 1) := ⟨#{k : Fin m | w k = true} - 1, by omega⟩
  refine ⟨n, w 0, rfl, eq_rDiagonalWord_of_card_true w (by omega)
    (fun k hk hwk => ?_) (fun hw0 => ?_)⟩
  · rcases step_or_last_of_true hsup hmono hU_alt hwk with ⟨_, hall⟩ | ⟨_, hnext⟩
    · exact absurd (hall ⟨(k : ℕ) + 1, hk⟩) (Nat.not_le_of_gt (Nat.lt_succ_self _))
    · exact hnext
  · by_contra hlast_ne
    have hlast : w ⟨2 * n + 1, by omega⟩ = true := by
      revert hlast_ne; cases w ⟨2 * n + 1, by omega⟩ <;> simp
    rcases step_or_last_of_true hsup hmono hU_alt hlast with ⟨hw0', _⟩ | ⟨hk, _⟩
    · exact absurd hw0 (by rw [show (⟨0, _⟩ : Fin (2 * (n + 1))) = 0 from rfl] at hw0'; simp [hw0'])
    · dsimp only at hk; omega

namespace IsRDiagonal

/-- *Nica–Speicher, Proposition 15.8* (right product): the product `u * b` of an R-diagonal element
`u` with any star-free element `b` is R-diagonal. -/
theorem mul_right (hu : IsRDiagonal φ u) (hfree : IsStarFreelyIndependentElements φ ![u, b]) :
    IsRDiagonal φ (u * b) where
  apply_one := hu.apply_one
  freeCumulant_eq_zero {m} hm w hw := by
    have hf : MonotoneOn (fun p : Fin m ×ₗ Bool => (ofLex p).1)
        (univ : Finset (Fin m)).interlace :=
      Prod.Lex.monotone_fst_ofLex.monotoneOn _
    have hgroup : freeCumulant φ (fun i => if w i then Star.star (u * b) else u * b) univ =
        freeCumulant φ (fiberProd (rDiagonalProdWord u b w)
          (univ : Finset (Fin m)).interlace fun p => (ofLex p).1)
          ((univ : Finset (Fin m)).interlace.image fun p => (ofLex p).1) := by
      rw [image_interlace_fst]
      exact freeCumulant_congr φ fun x _ => (fiberProd_rDiagonalProdWord w x).symm
    rw [hgroup, freeCumulant_fiberProd_eq_sum_prod φ _ hf,
      NoncrossingPartition.comap_fst_bot_eq_interlacePairs]
    refine sum_eq_zero fun σ hσ => ?_
    by_contra hne
    exact hw (exists_rDiagonalWord_of_prod_ne_zero hu hfree hm w (mem_filter.1 hσ).2 hne)

/-- *Nica–Speicher, Proposition 15.8* (left product): the product `b * u` of any element `b` with a
star-free R-diagonal element `u` is R-diagonal. -/
theorem mul_left (hu : IsRDiagonal φ u) (hfree : IsStarFreelyIndependentElements φ ![u, b]) :
    IsRDiagonal φ (b * u) := by
  have hstar : Star.star (![u, b] : Fin 2 → A) = ![Star.star u, Star.star b] := by
    funext i; fin_cases i <;> rfl
  have hfree' : IsStarFreelyIndependentElements φ ![Star.star u, Star.star b] := by
    rw [← hstar, isStarFreelyIndependentElements_star_iff]
    exact hfree
  simpa only [star_mul, star_star] using (hu.star.mul_right hfree').star

end IsRDiagonal

namespace IsHaarUnitary

/-- Right-multiplying a Haar unitary `u` by any star-free element `b` produces an R-diagonal
element. -/
theorem isRDiagonal_mul_right (hu : IsHaarUnitary φ u)
    (hfree : IsStarFreelyIndependentElements φ ![u, b]) :
    IsRDiagonal φ (u * b) :=
  hu.isRDiagonal.mul_right hfree

/-- Left-multiplying a Haar unitary `u` by any star-free element `b` produces an R-diagonal
element. -/
theorem isRDiagonal_mul_left (hu : IsHaarUnitary φ u)
    (hfree : IsStarFreelyIndependentElements φ ![u, b]) :
    IsRDiagonal φ (b * u) :=
  hu.isRDiagonal.mul_left hfree

/-- If `u` is a Haar unitary star-free from `b` and `u * b` has the same star distribution as `b`,
then `b` is R-diagonal (one direction of Nica–Speicher, Theorem 15.10). -/
theorem isRDiagonal_of_starDistribution_mul_right_eq (hu : IsHaarUnitary φ u)
    (hfree : IsStarFreelyIndependentElements φ ![u, b])
    (hdist : starDistribution φ (fun _ : Unit => u * b) =
      starDistribution φ (fun _ : Unit => b)) :
    IsRDiagonal φ b :=
  (isRDiagonal_iff_of_starDistribution_eq hdist).1 (hu.isRDiagonal_mul_right hfree)

/-- If `u` is a Haar unitary star-free from `b` and `b * u` has the same star distribution as `b`,
then `b` is R-diagonal. -/
theorem isRDiagonal_of_starDistribution_mul_left_eq (hu : IsHaarUnitary φ u)
    (hfree : IsStarFreelyIndependentElements φ ![u, b])
    (hdist : starDistribution φ (fun _ : Unit => b * u) =
      starDistribution φ (fun _ : Unit => b)) :
    IsRDiagonal φ b :=
  (isRDiagonal_iff_of_starDistribution_eq hdist).1 (hu.isRDiagonal_mul_left hfree)

end IsHaarUnitary

end RDiagonalProduct

end TauCeti
