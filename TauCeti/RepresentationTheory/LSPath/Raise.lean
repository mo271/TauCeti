/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
public import TauCeti.RepresentationTheory.LSPath.Linked
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root, and write
`H(t) = ⟨π(t), αᵢ^∨⟩` for its running height, with minimum `h`. When `-h ≥ 1`, Littelmann's raising
operator `e_αᵢ` reflects by `sᵢ` the single piece of the path between the last time `t₀` before the
first minimum `t₁` at which `H = h + 1`, and `t₁` itself, and keeps the rest
(`TauCeti.LSPath.exists_raise_toPLPath_eq`). This file proves Littelmann's theorem that the result
is again the path of an LS path of shape `λ` (`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`).

In terms of the directions `τ₀ > ⋯ > τ_l` and durations of `π`, with `t₀` inside the segment `j₀`
and `t₁` at the break `k₁`, the raised path runs along the list of directions
`τ₀, …, τ_{j₀}, sᵢ τ_{j₀}, …, sᵢ τ_{k₁ - 1}, τ_{k₁}, …, τ_l`, the segment `j₀` being cut at `t₀`.
This list is linked (`TauCeti.LSPath.Linked`), so it defines an LS path by
`TauCeti.LSPath.ofLinked`, which drops a zero-duration piece when `t₀` is already a break (`θ = 0`)
and merges repeated directions. The chain conditions at its breaks follow from
`TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain`:

* at `t₀` the height `h + 1` is an integer and `⟨τ_{j₀} λ, αᵢ^∨⟩ < 0`, so `sᵢ τ_{j₀} ⋖ τ_{j₀}` is
  a `t₀`-chain;
* at a break `a` strictly inside the reflected piece the height lies strictly between the integers
  `h` and `h + 1`, so `a ⟨τ λ, αᵢ^∨⟩` is not an integer, and the `a`-chain stays on the negative
  side of the wall of `αᵢ`, where `sᵢ` carries it to an `a`-chain;
* at `t₁` (when `t₁ < 1`) the height attains its minimum, so
  `⟨τ_{k₁ - 1} λ, αᵢ^∨⟩ < 0 ≤ ⟨τ_{k₁} λ, αᵢ^∨⟩`, and an `a`-chain from `τ_{k₁ - 1}` down to
  `τ_{k₁}` gives one from `sᵢ τ_{k₁ - 1}` down to `τ_{k₁}`.

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`: **Littelmann's raising operator
  preserves Lakshmibai–Seshadri paths**.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Sections 1 and 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- **Reflecting a falling window of a linked list.** Let `[w₀, w₁]` (`0 < w₀`) be a window of
entries of a linked list along which the heights `⟨τ λ, αᵢ^∨⟩` of the directions are negative, with
`a ⟨τ λ, αᵢ^∨⟩` nonintegral at the internal breaks `a`, preceded by an entry with the same
direction as its first one at a break `a` with `a ⟨τ λ, αᵢ^∨⟩` integral, and followed (if not at
the end of the list) by a direction of nonnegative height. Replacing the directions `τ` in the
window by `sᵢ τ` keeps the list linked. -/
private theorem Linked.mapIdx_simple_mul_neg (hlam : lam ∈ dominantChamber P b) {t : ℚ}
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l)
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {w₀ w₁ : ℕ} (hw₀ : 0 < w₀) (hw₀₁ : w₀ ≤ w₁) (hw₁ : w₁ < l.length)
    (hneg : ∀ k (hk : k < l.length), w₀ ≤ k → k ≤ w₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), w₀ < k → k ≤ w₁ →
      ¬∃ z : ℤ, (t + ((l.take k).map Prod.snd).sum) * P.coroot' i (l[k].1 • lam) = z)
    (hcut : l[w₀ - 1].1 = l[w₀].1)
    (hcutint : ∃ z : ℤ,
      (t + ((l.take w₀).map Prod.snd).sum) * P.coroot' i (l[w₀].1 • lam) = z)
    (hright : ∀ k (hk : k < l.length), w₁ + 1 = k → 0 ≤ P.coroot' i (l[k].1 • lam)) :
    Linked P b lam t (l.mapIdx fun k p ↦
      if w₀ ≤ k ∧ k ≤ w₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p) := by
  set g : ℕ → P.weylGroup × ℚ → P.weylGroup × ℚ := fun k p ↦
    if w₀ ≤ k ∧ k ≤ w₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p
  have hsnd : (l.mapIdx g).map Prod.snd = l.map Prod.snd := by
    refine List.ext_getElem (by simp) fun k _ _ ↦ ?_
    simp only [g, List.getElem_map, List.getElem_mapIdx]
    split_ifs <;> rfl
  rw [linked_iff_getElem] at hl ⊢
  intro k hk
  rw [List.length_mapIdx] at hk
  rw [List.map_take, hsnd, ← List.map_take]
  obtain ⟨C, hhead, hlast, hC⟩ := hl k hk
  simp only [List.getElem_mapIdx, g]
  by_cases hk₁ : w₀ ≤ k ∧ k ≤ w₁ <;> by_cases hk₂ : w₀ ≤ k + 1 ∧ k + 1 ≤ w₁ <;>
    simp only [hk₁, hk₂, and_self, ↓reduceIte]
  · -- Both ends in the window: the chain stays on the negative side and reflects.
    have hint_head :
        ¬∃ z : ℤ, (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (C.head.1 • lam) = z := by
      rintro ⟨z₁, hz₁⟩
      obtain ⟨z₂, hz₂⟩ := hC.exists_mul_sub_eq_intCast hlam (P.coroot' i)
      refine hint (k + 1) hk (by omega) hk₂.2 ⟨z₁ - z₂, ?_⟩
      rw [← hlast]
      push_cast at hz₁ hz₂ ⊢
      linear_combination hz₁ - hz₂
    have hall := hC.coroot'_smul_neg hlam i
      (by rw [hhead]; exact hneg k (by omega) hk₁.1 hk₁.2) hint_head
    refine ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inr hall), ?_, ?_,
      _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr hC⟩
    · simp [hhead]
    · simp [hlast]
  · -- Leaving the window at `w₁`: Littelmann's chain at the end of a reflected piece.
    obtain rfl : k = w₁ := by omega
    obtain ⟨D, hDhead, hDlast, hD⟩ := hC.exists_isAChain_simple_mul_head hlam i
      (by rw [hhead]; exact hneg k (by omega) hk₁.1 le_rfl)
      (by rw [hlast]; exact hright (k + 1) (by simpa using hk) rfl)
    exact ⟨D, by rw [hDhead, hhead], by rw [hDlast, hlast], hD⟩
  · -- Entering the window at `w₀`: the cover `sᵢ τ ⋖ τ`.
    have hkw₀ : k + 1 = w₀ := by omega
    have hk_eq : k = w₀ - 1 := by omega
    set sᵢ := (weylCoxeterSystem P b).simple i
    set τ := l[w₀].1
    have hτneg : P.coroot' i (τ • lam) < 0 := hneg w₀ (by omega) le_rfl hw₀₁
    have hτmin : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (sᵢ * τ) :=
      isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hmin _ (List.getElem_mem (by omega)))
        hτneg.ne
    have hsτ_smul : P.coroot' i ((sᵢ * τ) • lam) = -P.coroot' i (τ • lam) := by
      rw [simple_mul_smul_eq_reflection, P.coroot'_reflection_self]
    obtain ⟨z, hz⟩ := hcutint
    obtain ⟨D, hDhead, hDlast, hD⟩ := exists_isAChain_simple_mul_of_coroot'_pos hlam hτmin
      (a := t + ((l.take (k + 1)).map Prod.snd).sum)
      (by rw [hsτ_smul]; omega)
      ⟨-z, by rw [hkw₀, hsτ_smul]; push_cast at hz ⊢; linear_combination -hz⟩
    refine ⟨D, ?_, ?_, hD⟩
    · rw [hDhead, (weylCoxeterSystem P b).simple_mul_simple_cancel_left]
      simpa only [hk_eq] using hcut.symm
    · simpa only [hkw₀] using hDlast
  · exact ⟨C, hhead, hlast, hC⟩

variable (b) in
/-- The directions and durations produced from `l` by Littelmann's raising operator along the
simple root `αᵢ`: the first part `(τ, θ d)` of `l[j₀] = (τ, d)` is kept, the second part
`(τ, (1 - θ) d)` and the entries `j₀ + 1, …, k₁ - 1` are reflected by `sᵢ`, and the entries from
`k₁` on are kept. -/
private noncomputable def raiseList (i : b.support) (l : List (P.weylGroup × ℚ)) (j₀ k₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) : List (P.weylGroup × ℚ) :=
  (l.take j₀ ++ [(τ, θ * d)]) ++
    ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).map
      (fun p ↦ ((weylCoxeterSystem P b).simple i * p.1, p.2)) ++
    l.drop k₁

private theorem nonneg_of_mem_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)}
    (hl : ∀ p ∈ l, 0 ≤ p.2) {j₀ k₁ : ℕ} {τ : P.weylGroup} {d θ : ℚ} (hd : 0 ≤ d) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) {p : P.weylGroup × ℚ} (hp : p ∈ raiseList b i l j₀ k₁ τ d θ) : 0 ≤ p.2 := by
  simp only [raiseList, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with ((hp | rfl) | ⟨q, rfl | hq, rfl⟩) | hp
  · exact hl p (List.mem_of_mem_take hp)
  · exact mul_nonneg hθ₀ hd
  · exact mul_nonneg (by linarith) hd
  · exact hl q (List.mem_of_mem_take (List.mem_of_mem_drop hq))
  · exact hl p (List.mem_of_mem_drop hp)

private theorem sum_map_snd_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)} {j₀ k₁ : ℕ}
    (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ) :
    ((raiseList b i l j₀ k₁ l[j₀].1 l[j₀].2 θ).map Prod.snd).sum = (l.map Prod.snd).sum := by
  conv_rhs => rw [← List.take_append_drop k₁ l, ← List.take_append_drop j₀ (l.take k₁),
    List.take_take, min_eq_left (by omega), List.drop_eq_getElem_cons (by simp; omega),
    List.getElem_take]
  simp only [raiseList, List.map_append, List.map_cons, List.map_map, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
  ring

/-- **The raised list is linked.** Let `l` be a linked list of minimal coset representatives, let
`[j₀, k₁)` be a window along which the height `⟨-, αᵢ^∨⟩` of the directions is negative, with
`a ⟨τ λ, αᵢ^∨⟩` nonintegral at its internal breaks `a`, followed (if `k₁ < l.length`) by a
direction of nonnegative height, and let `θ` cut the entry `l[j₀] = (τ, d)` at an `a`-integral
time. Then `TauCeti.LSPath.raiseList` is linked, and its directions are minimal coset
representatives. -/
private theorem linked_raiseList (hlam : lam ∈ dominantChamber P b)
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ)
    (hneg : ∀ k (hk : k < l.length), j₀ ≤ k → k < k₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), j₀ < k → k < k₁ →
      ¬∃ m : ℤ, ((l.take k).map Prod.snd).sum * P.coroot' i (l[k].1 • lam) = m)
    (hcut : ∃ m : ℤ,
      (((l.take j₀).map Prod.snd).sum + θ * l[j₀].2) * P.coroot' i (l[j₀].1 • lam) = m)
    (hright : ∀ k (hk : k < l.length), k = k₁ → 0 ≤ P.coroot' i (l[k].1 • lam)) :
    Linked P b lam 0 (raiseList b i l j₀ k₁ l[j₀].1 l[j₀].2 θ) ∧
      ∀ p ∈ raiseList b i l j₀ k₁ l[j₀].1 l[j₀].2 θ,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hj₀ : j₀ < l.length := by omega
  set τ := l[j₀].1 with hτ
  set d := l[j₀].2 with hd
  set s := (weylCoxeterSystem P b).simple i
  have hτmin : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) τ :=
    hlmin _ (List.getElem_mem hj₀)
  -- Subdivide the entry `j₀` at the fraction `θ`; the list stays linked.
  set Dp : List (P.weylGroup × ℚ) :=
    l.take j₀ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₀ + 1) with hDp
  have hDp_linked : Linked P b lam 0 Dp := by
    have hsplit : l = l.take j₀ ++ (τ, θ * d + (1 - θ) * d) :: l.drop (j₀ + 1) := by
      rw [show θ * d + (1 - θ) * d = d by ring, ← List.drop_eq_getElem_cons hj₀,
        List.take_append_drop]
    rw [hsplit] at hl
    exact Linked.split hτmin hl
  have hDpmin : ∀ p ∈ Dp, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
    intro p hp
    simp only [Dp, List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | rfl | hp
    · exact hlmin p (List.mem_of_mem_take hp)
    · exact hτmin
    · exact hτmin
    · exact hlmin p (List.mem_of_mem_drop hp)
  have hlen_take : (l.take j₀).length = j₀ := by simp; omega
  have hDp_len : Dp.length = l.length + 1 := by simp [Dp]; omega
  have hDp_j₀ : Dp[j₀]'(by omega) = (τ, θ * d) := by
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  have hDp_j₀1 : Dp[j₀ + 1]'(by omega) = (τ, (1 - θ) * d) := by
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  have hDp_gt : ∀ k (hk : k < Dp.length), j₀ + 2 ≤ k → Dp[k] = l[k - 1]'(by omega) := by
    intro k hk hkj
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, k = j₀ + 2 + m := ⟨k - (j₀ + 2), by omega⟩
    simp only [hlen_take, show j₀ + 2 + m - j₀ = m + 2 by omega, List.getElem_cons_succ,
      List.getElem_drop]
    congr 1
    omega
  have hDp_fst_win : ∀ k (hk : k < Dp.length), j₀ + 1 ≤ k → Dp[k].1 = (l[k - 1]'(by omega)).1 := by
    intro k hk hkj
    rcases hkj.eq_or_lt with rfl | hkj'
    · rw [hDp_j₀1]
      exact hτ
    · rw [hDp_gt k hk (by omega)]
  have hcum_j₀1 : ((Dp.take (j₀ + 1)).map Prod.snd).sum =
      ((l.take j₀).map Prod.snd).sum + θ * d := by
    simp only [Dp]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₀ + 1 - j₀ = 1 by omega]
    simp
  have hcum_gt : ∀ k, j₀ + 2 ≤ k → ((Dp.take k).map Prod.snd).sum =
      ((l.take (k - 1)).map Prod.snd).sum := by
    intro k hkj
    obtain ⟨m, rfl⟩ : ∃ m, k = j₀ + 2 + m := ⟨k - (j₀ + 2), by omega⟩
    simp only [Dp]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₀ + 2 + m - j₀ = m + 2 by omega, List.take_succ_cons, List.take_succ_cons]
    have hl_split : l.take (j₀ + 1 + m) = l.take j₀ ++ l[j₀] :: (l.drop (j₀ + 1)).take m := by
      have h1 : l.take (j₀ + 1 + m) = l.take (j₀ + 1) ++ (l.drop (j₀ + 1)).take m := by
        rw [List.take_add]
      rw [h1, List.take_add_one, getElem?_pos l j₀ hj₀, Option.toList_some, List.append_assoc,
        List.singleton_append]
    rw [show j₀ + 2 + m - 1 = j₀ + 1 + m by omega, hl_split]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, ← hd]
    ring
  -- Reflect the window `[j₀ + 1, k₁]` of the subdivided list in `sᵢ`.
  have hW := Linked.mapIdx_simple_mul_neg hlam hDp_linked hDpmin i
    (w₀ := j₀ + 1) (w₁ := k₁) (Nat.succ_pos _) (by omega) (by omega)
    (fun k hk hk₀ hkk₁ ↦ by
      rw [hDp_fst_win k hk hk₀]
      exact hneg (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hk₀ hkk₁ ↦ by
      rw [zero_add, hcum_gt k (by omega), hDp_fst_win k hk (by omega)]
      exact hint (k - 1) (by omega) (by omega) (by omega))
    ((congrArg Prod.fst hDp_j₀).trans (congrArg Prod.fst hDp_j₀1).symm)
    (by
      rw [zero_add, hcum_j₀1, hDp_j₀1]
      exact hcut)
    (fun k hk hkk ↦ by
      rw [hDp_gt k hk (by omega)]
      exact hright (k - 1) (by omega) (by omega))
  -- The reflected subdivided list is the raised list.
  have hraise : raiseList b i l j₀ k₁ τ d θ =
      Dp.mapIdx fun k p ↦ if j₀ + 1 ≤ k ∧ k ≤ k₁ then (s * p.1, p.2) else p := by
    have hDp' : Dp = (l.take j₀ ++ [(τ, θ * d)]) ++
        ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)) ++ l.drop k₁ := by
      rw [hDp]
      have hdrop : l.drop (j₀ + 1) = (l.take k₁).drop (j₀ + 1) ++ l.drop k₁ := by
        conv_lhs => rw [← List.take_append_drop k₁ l]
        rw [List.drop_append_of_le_length (by simp; omega)]
      rw [hdrop]
      simp [List.append_assoc]
    have hA : (l.take j₀ ++ [(τ, θ * d)]).length = j₀ + 1 := by simp; omega
    have hB : ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).length = k₁ - j₀ := by simp; omega
    rw [hDp']
    refine List.ext_getElem (by simp [raiseList]) fun k hk₁ hk₂ ↦ ?_
    simp only [raiseList, List.getElem_mapIdx, List.getElem_append, List.getElem_map,
      List.length_append, List.length_map, hA, hB]
    split_ifs <;> first | rfl | omega
  rw [hraise]
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < Dp.length := by simpa using hk
  rw [List.getElem_mapIdx]
  split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [hDp_fst_win k hk' hw.1]
    exact (hneg (k - 1) (by omega) (by omega) (by omega)).ne
  · exact hDpmin _ (List.getElem_mem hk')

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem preReflection_smul_apply (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (d : 𝕜) (w : P.weylGroup) :
    Module.preReflection (f (P.root i)) F (d • f (w • lam)) =
      d • f (((weylCoxeterSystem P b).simple i * w) • lam) := by
  rw [map_smul, ← P.map_reflection_eq_preReflection i hF, simple_mul_smul_eq_reflection]

/-- **The rational data of a raising step.** If Littelmann's raising operator `e_αᵢ` is defined on
the path of an LS path `π` of dominant shape, it is presented by `TauCeti.LSPath.raiseList` on the
directions and durations of `π`, for a window `[j₀, k₁)` and a cut `θ` satisfying the hypotheses of
`TauCeti.LSPath.linked_raiseList`. -/
private theorem exists_raise_toPLPath_eq_ofSegments_raiseList (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    (h1 : 1 ≤ -(π.toPLPath 𝕜 f).minHeight F) :
    ∃ (j₀ k₁ : ℕ) (hj₀ : j₀ < π.dirDurations.length) (θ : ℚ),
      j₀ < k₁ ∧ k₁ ≤ π.dirDurations.length ∧ 0 ≤ θ ∧ θ ≤ 1 ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ ≤ k → k < k₁ →
        P.coroot' i (π.dirDurations[k].1 • lam) < 0) ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ < k → k < k₁ →
        ¬∃ m : ℤ, ((π.dirDurations.take k).map Prod.snd).sum *
          P.coroot' i (π.dirDurations[k].1 • lam) = m) ∧
      (∃ m : ℤ, (((π.dirDurations.take j₀).map Prod.snd).sum + θ * π.dirDurations[j₀].2) *
        P.coroot' i (π.dirDurations[j₀].1 • lam) = m) ∧
      (∀ k (hk : k < π.dirDurations.length), k = k₁ →
        0 ≤ P.coroot' i (π.dirDurations[k].1 • lam)) ∧
      PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
        ((raiseList b i π.dirDurations j₀ k₁ π.dirDurations[j₀].1 π.dirDurations[j₀].2 θ).map
          fun p ↦ (p.2 : 𝕜) • f (p.1 • lam))) := by
  obtain ⟨j₀', k₁, θ', hj₀k₁, hk₁s, hθnonneg', hθlt', hmin, hfall, hbetween, hcross, -, hraise⟩ :=
    π.exists_raise_toPLPath_eq hlam f i F hF (f (P.root i)) h1
  obtain ⟨z, hz⟩ := π.exists_minHeight_eq_intCast hlam f i F hF
  have hminH : (π.toPLPath 𝕜 f).minHeight F =
      PLPath.listMinHeight F (π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) := by
    rw [toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed]
  rw [map_snd_timed] at hmin hfall hbetween hcross hraise
  set D := π.dirDurations
  set seg : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam) with hseg
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum with hhgt
  set cum : ℕ → ℚ := fun k ↦ ((D.take k).map Prod.snd).sum
  have hHdef : ∀ w, H w = (P.coroot' i (w • lam) : ℚ) := fun _ ↦ rfl
  set j₀ : ℕ := (j₀' : ℕ)
  have hlen : D.length = π.length + 1 := length_dirDurations π
  have hj₀lt : j₀ < D.length := by rw [hlen]; exact j₀'.2
  have hk₁len : k₁ ≤ D.length := by rw [hlen]; exact hk₁s
  set τ := (π.dir j₀').1
  set d := π.duration j₀' with hd
  have hDj₀ : D[j₀] = (τ, d) := by rw [getElem_dirDurations]
  have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k hk ↦ by
    rw [getElem_dirDurations]; exact π.duration_pos _
  have hHF : ∀ k, F ((D.map seg).take k).sum = (hgt k : 𝕜) := by
    intro k
    simp only [hgt, ← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
    congr 1
    refine List.map_congr_left fun p _ ↦ ?_
    simp [seg, H, hF]
  have hgt_succ : ∀ k (hk : k < D.length), hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := by
    intro k hk
    simp only [hgt, List.map_take]
    rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
  have hFseg : F ((d : 𝕜) • f (τ • lam)) = ((d * H τ : ℚ) : 𝕜) := by simp [H, hF]
  have hgtk₁ : hgt k₁ = z := by
    rw [hHF, hz] at hmin
    exact_mod_cast hmin
  have hfall' : ∀ k, j₀ ≤ k → k < k₁ → hgt (k + 1) < hgt k := fun k hj₀k hkk₁ ↦ by
    have := hfall k hj₀k hkk₁
    rwa [hHF, hHF, Rat.cast_lt] at this
  have hnegH : ∀ k (hk : k < D.length), j₀ ≤ k → k < k₁ → H D[k].1 < 0 := fun k hk hj₀k hkk₁ ↦ by
    have := hfall' k hj₀k hkk₁
    rw [hgt_succ k hk] at this
    exact neg_of_mul_neg_right (by linarith) (hdpos k hk).le
  have hdH : d * H τ < 0 := by
    have := hnegH j₀ hj₀lt le_rfl hj₀k₁
    rw [hDj₀] at this
    exact mul_neg_of_pos_of_neg (by rw [hd]; exact π.duration_pos _) this
  set θ : ℚ := (z + 1 - hgt j₀) / (d * H τ) with hθ
  have hθd : θ * (d * H τ) = z + 1 - hgt j₀ := div_mul_cancel₀ _ hdH.ne
  have hθ' : θ' = θ := by
    have hc := hcross
    rw [hHF, hz, hFseg] at hc
    have hc' : θ' * ((d * H τ : ℚ) : 𝕜) = ((z + 1 - hgt j₀ : ℚ) : 𝕜) := by
      push_cast at hc ⊢
      linear_combination hc
    rw [hθ, Rat.cast_div, eq_div_iff (by exact_mod_cast hdH.ne), hc']
  rw [hθ'] at hθnonneg' hθlt' hraise
  have hθnonneg : 0 ≤ θ := by exact_mod_cast hθnonneg'
  have hθle : θ ≤ 1 := (by exact_mod_cast hθlt' : θ < 1).le
  have hbetween' : ∀ k, j₀ < k → k < k₁ → (z : ℚ) < hgt k ∧ hgt k < z + 1 := by
    intro k hj₀k hkk₁
    obtain ⟨h₁, h₂⟩ := hbetween k hj₀k hkk₁
    rw [hz, hHF] at h₁ h₂
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
  have hrightH : ∀ k (hk : k < D.length), k = k₁ → 0 ≤ H D[k].1 := by
    rintro k hk rfl
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F) (D.map seg) (k + 1)
    rw [← hminH, hz, hHF] at hle
    have hle' : (z : ℚ) ≤ hgt (k + 1) := by exact_mod_cast hle
    have := hgt_succ k hk
    rw [hgtk₁] at this
    exact nonneg_of_mul_nonneg_right (by linarith) (hdpos k hk)
  have hcong : ∀ k (hk : k < D.length), ∃ m : ℤ, hgt k - cum k * H D[k].1 = m := fun k hk ↦
    π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk
  refine ⟨j₀, k₁, hj₀lt, θ, hj₀k₁, hk₁len, hθnonneg, hθle,
    fun k hk hj₀k hkk₁ ↦ ?_, fun k hk hj₀k hkk₁ ↦ ?_, ?_, fun k hk hkk ↦ ?_, ?_⟩
  · have := hnegH k hk hj₀k hkk₁
    rw [hHdef] at this
    exact_mod_cast this
  · rintro ⟨m, hm⟩
    obtain ⟨m', hm'⟩ := hcong k hk
    obtain ⟨h₁, h₂⟩ := hbetween' k hj₀k hkk₁
    have hk' : hgt k = ((m' + m : ℤ) : ℚ) := by
      simp only [H] at hm'
      push_cast
      linarith
    rw [hk'] at h₁ h₂
    have h₁' : z < m' + m := by exact_mod_cast h₁
    have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
    omega
  · obtain ⟨m, hm⟩ := hcong j₀ hj₀lt
    refine ⟨z + 1 - m, ?_⟩
    rw [hDj₀] at hm ⊢
    simp only [H] at hm hθd
    push_cast
    linear_combination hθd - hm
  · have := hrightH k hk hkk
    rw [hHdef] at this
    exact_mod_cast this
  · rw [hraise, hDj₀]
    congr 2
    have hσ : ∀ p : P.weylGroup × ℚ,
        (p.2 : 𝕜) • f (((weylCoxeterSystem P b).simple i * p.1) • lam) =
          Module.preReflection (f (P.root i)) F ((p.2 : 𝕜) • f (p.1 • lam)) := fun p ↦
      (preReflection_smul_apply f i F hF _ _).symm
    simp only [raiseList, hseg, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.map_take, List.map_drop, Function.comp_def, hσ, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_one]
    rw [preReflection_smul_apply f i F hF]

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the raising operator `e_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_raise_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  have h1 : 1 ≤ -(π.toPLPath 𝕜 f).minHeight F := by
    by_contra! h
    have := (PLPath.raise_eq_none_iff (f := F) (x := f (P.root i)) (p := π.toPLPath 𝕜 f)).mpr
      (by linarith)
    rw [hq] at this
    exact Option.some_ne_none _ this
  obtain ⟨j₀, k₁, hj₀, θ, hj₀k₁, hk₁, hθ₀, hθ₁, hneg, hint, hcut, hright, hraise⟩ :=
    exists_raise_toPLPath_eq_ofSegments_raiseList π hlam f i F hF h1
  obtain ⟨hL, hLmin⟩ := linked_raiseList hlam π.linked_dirDurations
    (fun _ hp ↦ π.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁ θ hneg hint hcut hright
  refine ⟨ofLinked _ hLmin
    (fun _ hp ↦ nonneg_of_mem_raiseList i (fun _ hp ↦ (π.pos_of_mem_dirDurations hp).le)
      (π.pos_of_mem_dirDurations (List.getElem_mem hj₀)).le hθ₀ hθ₁ hp)
    (by rw [sum_map_snd_raiseList i hj₀k₁ hk₁, sum_map_snd_dirDurations]) hL, ?_⟩
  rw [toPLPath_ofLinked]
  exact Option.some.inj (hraise.symm.trans hq)

end TauCeti.LSPath
