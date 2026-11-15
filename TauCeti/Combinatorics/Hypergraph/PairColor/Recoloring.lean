/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
import TauCeti.Combinatorics.Enumerative.CoupledColoring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Regular recolorings of a pair of disjoint sets

Let `S` be a pair-color system with a finite palette `κ`, let `s` and `t` be disjoint vertex
sets, and let `p` be a probability distribution on `κ`. If `s` and `t` are large enough in terms
of `ε` and the palette size, the pairs between `s` and `t` can be recolored so that every color
`c` has density within `ε` of `p c` on every rectangle `s' ×ˢ t'` with `s' ⊆ s`, `t' ⊆ t`,
`ε * #s ≤ #s'` and `ε * #t ≤ #t'`. The new system (`PairColorSystem.recolorProduct`) has the same
palette reversal and the same colors on all pairs that do not join `s` and `t`; the pairs from `t`
to `s` receive the reversed colors. In particular `(s, t)` becomes a `2ε`-regular pair whose color
densities are within `ε` of `p`.

This file provides both an uncoupled and a coupled version of this step:

* **Independent regular recoloring** (`PairColorSystem.exists_recoloring_isRegularPair`): samples a
  coloring of `s ×ˢ t` with distribution `p`
  (`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`) under the size condition
  `card κ + 1 ≤ ε ^ 6 * #s` and `card κ + 1 ≤ ε ^ 6 * #t`, replacing an arbitrary or irregular
  block by a quasi-random one.
* **Coupled regular recoloring** (`PairColorSystem.exists_coupled_recoloring_isRegularPair`): when
  `(s, t)` is already `η`-regular for `S` with `card κ * η ≤ δ ^ 3 / 2`, pushes `S` on `s ×ˢ t`
  through the optimal Markov transition coupling
  (`TauCeti.exists_coupled_coloring_abs_card_filter_sub_mul_card_le`) under
  `8 (card κ + 1)³ ≤ δ ^ 6 * #s` and `8 (card κ + 1)³ ≤ δ ^ 6 * #t`, achieving `(2 * δ)`-regularity
  and density accuracy `δ` while editing at most
  `((∑ c, |d_c(s, t) - p c|) / 2 + δ / 2) * (#s * #t)` pairs of `s ×ˢ t`.

Both union bounds over the `2 ^ (#s + #t)` subrectangles and the palette follow from
`PairColorSystem.two_mul_two_pow_mul_two_pow_add_mul_exp_lt`.

## Main definitions

* `TauCeti.PairColorSystem.recolorProduct`: recolor `s ×ˢ t` by `x`, `t ×ˢ s` by `S.rev ∘ x ∘ swap`,
  and preserve `S` elsewhere.

## Main results

* `TauCeti.PairColorSystem.two_mul_two_pow_mul_two_pow_add_mul_exp_lt`: exponential union bound over
  subrectangles of `s ×ˢ t` plus `r` extra events.
* `TauCeti.PairColorSystem.exists_recoloring_abs_pairColorDensity_sub_le` and
  `TauCeti.PairColorSystem.exists_recoloring_isRegularPair`: uncoupled quasi-random recoloring of
  `(s, t)` with prescribed densities `p`.
* `TauCeti.PairColorSystem.exists_coupled_recoloring_abs_pairColorDensity_sub_le` and
  `TauCeti.PairColorSystem.exists_coupled_recoloring_isRegularPair`: coupled quasi-random recoloring
  of an already `η`-regular pair `(s, t)` with edit distance controlled by the `ℓ¹` density gap.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2 (the regular approximation lemma).
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), §9.3
  (quasi-random graphs).
-/

public section

open Finset Real

namespace TauCeti

namespace PairColorSystem

variable {κ V : Type*}

open Classical in
/-- Recolor the pairs from `s` to `t` by `x`, the pairs from `t` to `s` by the reversed colors,
and keep all other colors of `S`. -/
noncomputable def recolorProduct (S : PairColorSystem κ V) {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) : PairColorSystem κ V where
  color q :=
    if q.1 ∈ s ×ˢ t then x q.1 else if q.1.swap ∈ s ×ˢ t then S.rev (x q.1.swap) else S.color q
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev q := by
    obtain ⟨⟨u, v⟩, huv⟩ := q
    have hboth : ¬((u, v) ∈ s ×ˢ t ∧ (v, u) ∈ s ×ˢ t) := fun ⟨h₁, h₂⟩ ↦
      disjoint_left.1 hst (mem_product.1 h₂).1 (mem_product.1 h₁).2
    simp only [Prod.swap_prod_mk]
    by_cases h₁ : (u, v) ∈ s ×ˢ t <;> by_cases h₂ : (v, u) ∈ s ×ˢ t
    · exact absurd ⟨h₁, h₂⟩ hboth
    · simp [h₁, h₂]
    · simp [h₁, h₂]
    · simpa [h₁, h₂] using S.color_rev ⟨(u, v), huv⟩

section RecolorProduct

variable {S : PairColorSystem κ V} {s t : Finset V} (hst : Disjoint s t) (x : V × V → κ)

/-- On `s ×ˢ t`, `PairColorSystem.recolorProduct` assigns `some (x (u, v))`. -/
theorem colorOfPair_recolorProduct_of_mem {u v : V} (h : (u, v) ∈ s ×ˢ t) :
    (S.recolorProduct hst x).colorOfPair u v = some (x (u, v)) := by
  have huv : u ≠ v := hst.forall_ne_finset (mem_product.1 h).1 (mem_product.1 h).2
  rw [colorOfPair_of_ne _ huv]
  simp [recolorProduct, h]

/-- Outside `(s ×ˢ t) ∪ (t ×ˢ s)`, `PairColorSystem.recolorProduct` preserves `S.colorOfPair`. -/
theorem colorOfPair_recolorProduct_of_not_mem {u v : V} (hs : u ∈ s → v ∉ t)
    (ht : u ∈ t → v ∉ s) : (S.recolorProduct hst x).colorOfPair u v = S.colorOfPair u v := by
  by_cases huv : u = v
  · simp [huv]
  have h₁ : (u, v) ∉ s ×ˢ t := fun h ↦ hs (mem_product.1 h).1 (mem_product.1 h).2
  have h₂ : (v, u) ∉ s ×ˢ t := fun h ↦ ht (mem_product.1 h).2 (mem_product.1 h).1
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  simp [recolorProduct, h₁, h₂]

end RecolorProduct

private theorem nonempty_of_sum_eq_one [Fintype κ] {p : κ → ℝ} (hp1 : ∑ c, p c = 1) :
    Nonempty κ :=
  let ⟨c, _, _⟩ := exists_ne_zero_of_sum_ne_zero (hp1.trans_ne one_ne_zero)
  ⟨c⟩

/-- A size bound `0 < b ≤ c ^ 2 * #u` forces `u` to have positive cardinality. -/
private theorem cast_card_pos_of_pos_le {b c : ℝ} {u : Finset V} (hb : 0 < b)
    (h : b ≤ c ^ 2 * #u) : (0 : ℝ) < #u :=
  pos_of_mul_pos_right (hb.trans_le h) (sq_nonneg c)

/-- Exponential union bound over all `2 ^ #s * 2 ^ #t` subrectangles of `s ×ˢ t` plus `r` extra
events across a finite palette `κ`: when `card κ + r + 1 ≤ c ^ 2 * #s` and
`card κ + r + 1 ≤ c ^ 2 * #t`,
`2 * (2 ^ #s * 2 ^ #t + r) * card κ * exp (-2 * (c * #s * #t)² / (#s * #t)) < 1`. -/
theorem two_mul_two_pow_mul_two_pow_add_mul_exp_lt [Fintype κ] [Nonempty κ] {r : ℕ} {c : ℝ}
    {s t : Finset V}
    (hs : Fintype.card κ + r + 1 ≤ c ^ 2 * #s) (ht : Fintype.card κ + r + 1 ≤ c ^ 2 * #t) :
    2 * (2 ^ #s * 2 ^ #t + r : ℕ) * Fintype.card κ *
      exp (-2 * (c * #s * #t) ^ 2 / (#s * #t : ℕ)) < 1 := by
  have hK : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
  have hbpos : (0 : ℝ) < Fintype.card κ + r + 1 := by positivity
  have hm := cast_card_pos_of_pos_le hbpos hs
  have hn := cast_card_pos_of_pos_le hbpos ht
  -- Bound each factor by an exponential, using `x + 1 ≤ exp x`.
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ exp k :=
    calc (2 : ℝ) ^ k ≤ exp 1 ^ k := pow_le_pow_left₀ (by norm_num) h2 k
      _ = exp k := by rw [← exp_nat_mul, mul_one]
  have h2st : (1 : ℝ) ≤ (2 : ℝ) ^ #s * (2 : ℝ) ^ #t :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hr_add : ((2 ^ #s * 2 ^ #t + r : ℕ) : ℝ) ≤
      ((r : ℝ) + 1) * ((2 : ℝ) ^ #s * (2 : ℝ) ^ #t) := by
    push_cast
    linarith [le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) r) h2st]
  have hrexp : (r : ℝ) + 1 ≤ exp r := add_one_le_exp (r : ℝ)
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ - 1) := by
    linarith [add_one_le_exp ((Fintype.card κ : ℝ) - 1)]
  have hpre : 2 * ((2 ^ #s * 2 ^ #t + r : ℕ) : ℝ) * Fintype.card κ ≤
      exp (#s + #t + Fintype.card κ + r) :=
    calc 2 * ((2 ^ #s * 2 ^ #t + r : ℕ) : ℝ) * Fintype.card κ
        ≤ 2 * (((r : ℝ) + 1) * ((2 : ℝ) ^ #s * (2 : ℝ) ^ #t)) * Fintype.card κ := by gcongr
      _ ≤ exp 1 * (exp r * (exp #s * exp #t)) * exp (Fintype.card κ - 1) := by
          gcongr
          exacts [hpow #s, hpow #t]
      _ = exp (#s + #t + Fintype.card κ + r) := by
          simp only [← exp_add]
          ring_nf
  have hexp : -2 * (c * #s * #t) ^ 2 / ((#s * #t : ℕ) : ℝ) = -2 * (c ^ 2 * #s) * #t := by
    rw [Nat.cast_mul, div_eq_iff (mul_pos hm hn).ne']
    ring
  calc 2 * ((2 ^ #s * 2 ^ #t + r : ℕ) : ℝ) * Fintype.card κ *
        exp (-2 * (c * #s * #t) ^ 2 / (#s * #t : ℕ))
      ≤ exp (#s + #t + Fintype.card κ + r) * exp (-2 * (c ^ 2 * #s) * #t) := by
        rw [hexp]
        gcongr
    _ = exp (#s + #t + Fintype.card κ + r - 2 * (c ^ 2 * #s) * #t) := by
        rw [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        -- `2 c² #s #t ≥ (card κ + r + 1) (#s + #t) > #s + #t + card κ + r`.
        have hm1 : (1 : ℝ) ≤ #s := Nat.one_le_cast.2 (Nat.cast_pos.1 hm)
        have hn1 : (1 : ℝ) ≤ #t := Nat.one_le_cast.2 (Nat.cast_pos.1 hn)
        have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        linarith [mul_le_mul_of_nonneg_right hs hn.le, mul_le_mul_of_nonneg_right ht hm.le,
          mul_nonneg (by linarith [hK, hr0] : (0 : ℝ) ≤ Fintype.card κ + r - 1)
            (by linarith [hm1, hn1] : (0 : ℝ) ≤ #s + #t - 1)]

variable {s t : Finset V}

/-- **Regular recoloring with prescribed densities.** Let `S` be a pair-color system with a
finite palette `κ`, let `s` and `t` be disjoint vertex sets with `card κ + 1 ≤ ε ^ 6 * #s` and
`card κ + 1 ≤ ε ^ 6 * #t`, and let `p` be a probability distribution on `κ`. Then there is a
pair-color system `S'` with the palette reversal of `S` that agrees with `S` on all pairs not
joining `s` and `t`, such that on every rectangle `s' ×ˢ t'` with `s' ⊆ s`, `t' ⊆ t`,
`ε * #s ≤ #s'` and `ε * #t ≤ #t'` the density of every color `c` is within `ε` of `p c`. -/
theorem exists_recoloring_abs_pairColorDensity_sub_le [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ}
    (hε : 0 < ε) (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, ε * #s ≤ #s' → ε * #t ≤ #t' →
        |(pairColorDensity S' c s' t' : ℝ) - p c| ≤ ε := by
  classical
  have := nonempty_of_sum_eq_one hp1
  have hs' : Fintype.card κ + (0 : ℕ) + 1 ≤ (ε ^ 3) ^ 2 * #s := by
    simpa [show (ε ^ 3) ^ 2 = ε ^ 6 by ring] using hs
  have ht' : Fintype.card κ + (0 : ℕ) + 1 ≤ (ε ^ 3) ^ 2 * #t := by
    simpa [show (ε ^ 3) ^ 2 = ε ^ 6 by ring] using ht
  have hs0 := cast_card_pos_of_pos_le (by positivity) hs'
  have ht0 := cast_card_pos_of_pos_le (by positivity) ht'
  -- A coloring of `s ×ˢ t` with small deviations on all rectangles `s' ×ˢ t'`.
  obtain ⟨x, hx⟩ := exists_forall_abs_card_filter_sub_mul_card_lt hp hp1
    (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2) (N := #s * #t)
    (fun i ↦ by
      obtain ⟨hs₁, ht₁⟩ := mem_product.1 i.2
      rw [card_product]
      exact Nat.mul_le_mul (card_le_card (mem_powerset.1 hs₁)) (card_le_card (mem_powerset.1 ht₁)))
    (a := ε ^ 3 * #s * #t)
    (mul_pos (mul_pos (pow_pos hε 3) hs0) ht0)
    (by simpa using two_mul_two_pow_mul_two_pow_add_mul_exp_lt hs' ht')
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_not_mem hst x, ?_⟩
  intro c s' hs' t' ht' hs's ht't
  have hpos : (0 : ℝ) < #s' * #t' :=
    mul_pos ((mul_pos hε hs0).trans_le hs's) ((mul_pos hε ht0).trans_le ht't)
  have hdev := hx ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
  -- On `s' ×ˢ t' ⊆ s ×ˢ t` the recolored system has the colors of `x`, and the color count is the
  -- density times `#s' * #t'`, since `s'` and `t'` are disjoint.
  have hcount : (#{q ∈ s' ×ˢ t' | x q = c} : ℝ) =
      pairColorDensity (S.recolorProduct hst x) c s' t' * (#s' * #t') := by
    have hfilter : {q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
        {q ∈ s' ×ˢ t' | x q = c} := filter_congr fun q hq ↦ by
      rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
        Option.some_inj]
    rw [← hfilter]
    exact mod_cast (pairColorDensity_mul_card_of_disjoint _ c (hst.mono hs' ht')).symm
  rw [hcount, card_product, Nat.cast_mul, ← sub_mul, abs_mul, abs_of_pos hpos] at hdev
  refine le_of_mul_le_mul_right ?_ hpos
  calc _ ≤ ε ^ 3 * #s * #t := hdev.le
    _ = ε * ((ε * #s) * (ε * #t)) := by ring
    _ ≤ ε * (#s' * #t') := by gcongr

/-- **Regular recoloring.** Under the hypotheses of
`TauCeti.PairColorSystem.exists_recoloring_abs_pairColorDensity_sub_le`, the pairs between `s`
and `t` can be recolored so that `(s, t)` becomes a `2ε`-regular pair whose color densities are
within `ε` of `p`, keeping the palette reversal and all colors on pairs not joining `s` and
`t`. -/
theorem exists_recoloring_isRegularPair [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ}
    (hε : 0 < ε) (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      S'.IsRegularPair (2 * ε) s t ∧ ∀ c, |(pairColorDensity S' c s t : ℝ) - p c| ≤ ε := by
  obtain ⟨S', hrev, hagree, hdens⟩ :=
    S.exists_recoloring_abs_pairColorDensity_sub_le hst hp hp1 hε hs ht
  have hthr {ε' : ℝ} (hε' : ε' ≤ 1) (u : Finset V) : ε' * #u ≤ #u :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) hε'
  -- For `ε ≤ 1` the pair `(s, t)` itself passes the size thresholds; otherwise densities in
  -- `[0, 1]` are trivially within `ε` of each other.
  have hfull (c : κ) : |(pairColorDensity S' c s t : ℝ) - p c| ≤ ε := by
    obtain hε1 | hε1 := le_or_gt ε 1
    · exact hdens c s subset_rfl t subset_rfl (hthr hε1 s) (hthr hε1 t)
    have h₀ : (0 : ℝ) ≤ pairColorDensity S' c s t := mod_cast pairColorDensity_nonneg S' c s t
    have h₁ : (pairColorDensity S' c s t : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S' c s t
    have hpc : p c ≤ 1 := hp1 ▸ single_le_sum (fun c _ ↦ hp c) (mem_univ c)
    exact (abs_sub_le_iff.2 ⟨by linarith [hp c], by linarith [hp c]⟩).trans hε1.le
  refine ⟨S', hrev, hagree, ?_, hfull⟩
  obtain hε2 | _ := le_or_gt 1 (2 * ε)
  · exact isRegularPair_of_one_le hε2
  rw [isRegularPair_iff]
  intro c s' hs' t' ht' hs's ht't
  have hmono (u u' : Finset V) (hu : 2 * ε * #u ≤ #u') : ε * #u ≤ #u' :=
    le_trans (by nlinarith [(Nat.cast_nonneg #u : (0 : ℝ) ≤ _)]) hu
  have h₁ := hdens c s' hs' t' ht' (hmono s s' hs's) (hmono t t' ht't)
  have h₂ := hfull c
  calc _ ≤ |(pairColorDensity S' c s' t' : ℝ) - p c| + |p c - pairColorDensity S' c s t| :=
        abs_sub_le _ _ _
    _ ≤ 2 * ε := by rw [abs_sub_comm (p c)]; linarith

/-! ### Coupled regular recoloring -/

private theorem coupled_size_le [Fintype κ] [Nonempty κ] {δ : ℝ} {u : Finset V}
    (hu : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #u) :
    Fintype.card κ + (1 : ℕ) + 1 ≤ (δ ^ 3 / (2 * Fintype.card κ)) ^ 2 * #u := by
  let K : ℝ := Fintype.card κ
  have hKpos : 0 < K := Nat.cast_pos.2 Fintype.card_pos
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc ((Fintype.card κ : ℝ) + (1 : ℕ) + 1) * (2 * K) ^ 2
      = 4 * K ^ 2 * (K + 2) := by push_cast; ring
    _ ≤ 8 * (K + 1) ^ 3 := by linarith [pow_nonneg hKpos.le 3, sq_nonneg K, hKpos]
    _ ≤ δ ^ 6 * #u := hu
    _ = (δ ^ 3) ^ 2 * #u := by ring

private theorem card_filter_getD_eq_pairColorDensity_mul [DecidableEq κ]
    (S : PairColorSystem κ V) {u v : Finset V} (huv : Disjoint u v) (c_def c : κ) :
    (#{q ∈ u ×ˢ v | (S.colorOfPair q.1 q.2).getD c_def = c} : ℝ) =
      pairColorDensity S c u v * (#u * #v) := by
  classical
  have hf : {q ∈ u ×ˢ v | (S.colorOfPair q.1 q.2).getD c_def = c} =
      {q ∈ u ×ˢ v | S.colorOfPair q.1 q.2 = some c} := filter_congr fun q hq ↦ by
    simp [colorOfPair_of_ne S (huv.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2)]
  rw [hf]
  exact mod_cast (pairColorDensity_mul_card_of_disjoint S c huv).symm

/-- Translate `S.IsRegularPair η s t` into the count-discrepancy hypothesis expected by
`exists_coupled_coloring_abs_card_filter_sub_mul_card_le`. -/
private theorem abs_card_filter_getD_sub_le [DecidableEq κ] {S : PairColorSystem κ V}
    {s' t' : Finset V} (hst : Disjoint s t) (hs0 : (0 : ℝ) < #s) (ht0 : (0 : ℝ) < #t)
    {η : ℝ} (hreg : S.IsRegularPair η s t) (hs' : s' ⊆ s) (ht' : t' ⊆ t) (c_def c₀ : κ) :
    |(#{q ∈ s' ×ˢ t' | (S.colorOfPair q.1 q.2).getD c_def = c₀} : ℝ) -
      ((#{q ∈ s ×ˢ t | (S.colorOfPair q.1 q.2).getD c_def = c₀} : ℝ) / #(s ×ˢ t)) *
        #(s' ×ˢ t')| ≤ η * #s * #t := by
  classical
  have hiff : {q ∈ s' ×ˢ t' | (S.colorOfPair q.1 q.2).getD c_def = c₀} =
      {q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c₀} := filter_congr fun q hq ↦ by
    simp [colorOfPair_of_ne S ((hst.mono hs' ht').forall_ne_finset (mem_product.1 hq).1
      (mem_product.1 hq).2)]
  have h1 := hreg.abs_card_filter_colorOfPair_sub_le (c := c₀) hst hs' ht'
  rw [← hiff] at h1
  have h2 : ((#{q ∈ s ×ˢ t | (S.colorOfPair q.1 q.2).getD c_def = c₀} : ℝ) / #(s ×ˢ t)) *
      #(s' ×ˢ t') = pairColorDensity S c₀ s t * #s' * #t' := by
    rw [card_filter_getD_eq_pairColorDensity_mul S hst, card_product, card_product, Nat.cast_mul,
      Nat.cast_mul, mul_div_cancel_right₀ _ (mul_pos hs0 ht0).ne', mul_assoc]
  rwa [h2]

open Classical in
/-- **Coupled regular recoloring with subrectangle density bounds.** If `(s, t)` is disjoint and
`η`-regular for `S` with `card κ * η ≤ δ ^ 3 / 2`, `8 (card κ + 1)³ ≤ δ⁶ #s`, and
`8 (card κ + 1)³ ≤ δ⁶ #t`, then for any probability distribution `p` on `κ` there is a pair-color
system `S'` with the same palette reversal and the same colors outside `(s ×ˢ t) ∪ (t ×ˢ s)` that
edits at most `((∑ c, |d_c(s, t) - p c|) / 2 + δ³ / 2) * (#s * #t)` pairs of `s ×ˢ t` and achieves
density within `δ` of `p c` on every rectangle `s' ×ˢ t'` with `δ * #s ≤ #s'` and `δ * #t ≤ #t'`. -/
theorem exists_coupled_recoloring_abs_pairColorDensity_sub_le [Fintype κ]
    (S : PairColorSystem κ V) (hst : Disjoint s t) {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {η δ : ℝ} (hreg : S.IsRegularPair η s t)
    (hδ : 0 < δ) (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hs : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #s)
    (ht : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c s t : ℝ) - p c|) / 2 + δ ^ 3 / 2) * (#s * #t) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, δ * #s ≤ #s' → δ * #t ≤ #t' →
        |(pairColorDensity S' c s' t' : ℝ) - p c| ≤ δ := by
  classical
  have := nonempty_of_sum_eq_one hp1
  have hs_ub := coupled_size_le hs
  have ht_ub := coupled_size_le ht
  have hs0 : (0 : ℝ) < #s := cast_card_pos_of_pos_le (by positivity) hs_ub
  have ht0 : (0 : ℝ) < #t := cast_card_pos_of_pos_le (by positivity) ht_ub
  let c_def := Classical.arbitrary κ
  let x₀ (q : V × V) : κ := (S.colorOfPair q.1 q.2).getD c_def
  have hub : 2 * (Fintype.card ↥(s.powerset ×ˢ t.powerset) + 1 : ℕ) * Fintype.card κ *
      exp (-2 * ((δ ^ 3 / 2 * #s * #t) / Fintype.card κ) ^ 2 / #(s ×ˢ t)) < 1 := by
    have heq : (δ ^ 3 / 2 * #s * #t) / (Fintype.card κ : ℝ) =
        (δ ^ 3 / (2 * Fintype.card κ)) * #s * #t := by ring
    simpa [card_product, heq] using two_mul_two_pow_mul_two_pow_add_mul_exp_lt hs_ub ht_ub
  obtain ⟨x, -, hedit, htest⟩ := exists_coupled_coloring_abs_card_filter_sub_mul_card_le hp hp1
    (s ×ˢ t) x₀ (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2)
    (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
      (mem_powerset.1 (mem_product.1 i.2).2))
    (a := δ ^ 3 / 2 * #s * #t) (by positivity) hub
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_not_mem hst x,
    ?_, ?_⟩
  · have hne_eq :
        {q ∈ s ×ˢ t | (S.recolorProduct hst x).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ s ×ˢ t | x q ≠ x₀ q} := filter_congr fun q hq ↦ by
      simp [x₀, colorOfPair_recolorProduct_of_mem hst x hq,
        colorOfPair_of_ne S (hst.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2)]
    have hsum_eq : ∑ c : κ, |(#{q ∈ s ×ˢ t | x₀ q = c} : ℝ) - p c * #(s ×ˢ t)| =
        (∑ c : κ, |(pairColorDensity S c s t : ℝ) - p c|) * (#s * #t) := by
      rw [sum_mul]
      refine sum_congr rfl fun c _ ↦ ?_
      rw [card_filter_getD_eq_pairColorDensity_mul S hst c_def c, card_product, Nat.cast_mul,
        ← sub_mul, abs_mul, abs_of_pos (mul_pos hs0 ht0)]
    rw [hne_eq]
    linarith [hedit]
  · intro c s' hs' t' ht' hs's ht't
    have hpos : (0 : ℝ) < #s' * #t' :=
      mul_pos ((mul_pos hδ hs0).trans_le hs's) ((mul_pos hδ ht0).trans_le ht't)
    have hdev := htest ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩
      (fun c₀ ↦ abs_card_filter_getD_sub_le hst hs0 ht0 hreg hs' ht' c_def c₀) c
    have hx_card : (#{q ∈ s' ×ˢ t' | x q = c} : ℝ) =
        pairColorDensity (S.recolorProduct hst x) c s' t' * (#s' * #t') := by
      have hf : {q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
          {q ∈ s' ×ˢ t' | x q = c} := filter_congr fun q hq ↦ by
        rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
          Option.some_inj]
      rw [← hf]
      exact mod_cast (pairColorDensity_mul_card_of_disjoint _ c (hst.mono hs' ht')).symm
    rw [hx_card, card_product, Nat.cast_mul, ← sub_mul, abs_mul, abs_of_pos hpos] at hdev
    refine le_of_mul_le_mul_right ?_ hpos
    have hrect : δ ^ 3 * (#s * #t) ≤ δ * (#s' * #t') :=
      (by ring : δ ^ 3 * (#s * #t) = δ * ((δ * #s) * (δ * #t))).trans_le
        (mul_le_mul_of_nonneg_left (mul_le_mul hs's ht't (by positivity) (by positivity)) hδ.le)
    nlinarith [mul_le_mul_of_nonneg_right hηδ (mul_pos hs0 ht0).le]

open Classical in
/-- **Coupled regular recoloring of a disjoint pair.** If `(s, t)` is disjoint and `η`-regular for
`S` with `card κ * η ≤ δ ^ 3 / 2`, `8 (card κ + 1)³ ≤ δ⁶ #s`, and `8 (card κ + 1)³ ≤ δ⁶ #t`, then
for any target probability distribution `p` on `κ` there is a pair-color system `S'` with the same
palette reversal and the same colors outside `(s ×ˢ t) ∪ (t ×ˢ s)` such that `(s, t)` is
`(2 * δ)`-regular for `S'`, its color densities lie within `δ` of `p`, and at most
`((∑ c, |d_c(s, t) - p c|) / 2 + δ / 2) * (#s * #t)` pairs of `s ×ˢ t` are edited. -/
theorem exists_coupled_recoloring_isRegularPair [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    {η δ : ℝ} (hreg : S.IsRegularPair η s t) (hδ : 0 < δ)
    (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hs : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #s)
    (ht : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      S'.IsRegularPair (2 * δ) s t ∧
      (∀ c, |(pairColorDensity S' c s t : ℝ) - p c| ≤ δ) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c s t : ℝ) - p c|) / 2 + δ / 2) * (#s * #t) := by
  classical
  obtain hδ1 | hδ1 := le_or_gt 1 δ
  · refine ⟨S, rfl, fun _ _ _ _ ↦ rfl, isRegularPair_of_one_le (by linarith), fun c ↦ ?_, ?_⟩
    · have h₀ : (0 : ℝ) ≤ pairColorDensity S c s t := mod_cast pairColorDensity_nonneg S c s t
      have h₁ : (pairColorDensity S c s t : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S c s t
      have hpc : p c ≤ 1 := hp1 ▸ single_le_sum (fun c _ ↦ hp c) (mem_univ c)
      exact (abs_sub_le_iff.2 ⟨by linarith [hp c], by linarith [hp c]⟩).trans hδ1
    · have : 0 ≤ ∑ c, |(pairColorDensity S c s t : ℝ) - p c| :=
        sum_nonneg fun _ _ ↦ abs_nonneg _
      simp only [ne_eq, not_true_eq_false, filter_false, card_empty, Nat.cast_zero]
      positivity
  · obtain ⟨S', hrev, hagree, hedit, hdens⟩ :=
      S.exists_coupled_recoloring_abs_pairColorDensity_sub_le hst hp hp1 hreg hδ hηδ hs ht
    have hthr (u : Finset V) : δ * #u ≤ #u := mul_le_of_le_one_left (Nat.cast_nonneg _) hδ1.le
    have hfull (c : κ) : |(pairColorDensity S' c s t : ℝ) - p c| ≤ δ :=
      hdens c s subset_rfl t subset_rfl (hthr s) (hthr t)
    refine ⟨S', hrev, hagree, ?_, hfull, hedit.trans ?_⟩
    · obtain h2δ | _ := le_or_gt 1 (2 * δ)
      · exact isRegularPair_of_one_le h2δ
      rw [isRegularPair_iff]
      intro c s' hs' t' ht' hs's ht't
      have h1 := hdens c s' hs' t' ht'
        ((by nlinarith [Nat.cast_nonneg (α := ℝ) #s] : δ * #s ≤ 2 * δ * #s).trans hs's)
        ((by nlinarith [Nat.cast_nonneg (α := ℝ) #t] : δ * #t ≤ 2 * δ * #t).trans ht't)
      exact (abs_sub_le _ (p c) _).trans (by rw [abs_sub_comm (p c)]; linarith [hfull c])
    · have hpow : δ ^ 3 ≤ δ := pow_le_of_le_one hδ.le hδ1.le (by norm_num)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end PairColorSystem

end TauCeti
