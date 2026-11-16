/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Generator

/-!
# Every Brauer diagram is built from cap-cup diagrams and a permutation diagram

A Brauer diagram `D` with a cap has a cup as well, since it has as many caps as cups. Take a cap
of `D`, joining the bottom points `a` and `b`, and a cup, joining the top points `c` and `d`.
Reconnecting these two arcs into the through strands `a`–`c` and `b`–`d` gives a diagram `X` with
one cap fewer, `X = D.reconnect (Sum.inr c) (Sum.inl a)`. Stacking the cap-cup diagram
`TauCeti.capCup c d` above `X` undoes the reconnection: its cup restores the cup `c`–`d`, and its
cap joins the middle points `c` and `d`, where the strands of `X` from `a` and from `b` arrive, so
it restores the cap `a`–`b`. Every other strand of `X` passes straight through the cap-cup
diagram. No closed loop is formed in the middle, because every middle point lies on a through
strand of one of the two diagrams. So

`D = capCup c d ∘ X` with no middle loop (`TauCeti.composeDiagram_capCup_reconnect` and
`TauCeti.middleLoopCount_capCup_reconnect`).

Repeating this until no cap is left reaches a diagram without caps, which is a permutation
diagram. This gives an induction principle for Brauer diagrams
(`TauCeti.BrauerDiagram.capCup_induction_on`): a property of diagrams that holds for the
permutation diagrams, and passes from `X` to `capCup a b ∘ X` whenever no loop closes up in the
middle, holds for every diagram. In the Brauer algebra, where a loop-free stack is the product,
this says that the permutation diagrams and the cap-cup diagrams generate the algebra
(`TauCeti/Algebra/BrauerAlgebra/Generation.lean`).

## Main results

* `TauCeti.composeDiagram_capCup_reconnect`: stacking `capCup c d` above the reconnected diagram
  gives back `D`.
* `TauCeti.middleLoopCount_capCup_reconnect`: that stack closes up no loop.
* `TauCeti.BrauerDiagram.bottomCap_reconnect`: the reconnected diagram caps the bottom points of
  `D` other than `a` and `b`, so it has one cap fewer
  (`TauCeti.BrauerDiagram.card_bottomCap_reconnect`).
* `TauCeti.BrauerDiagram.capCup_induction_on`: **induction on Brauer diagrams** from the
  permutation diagrams by stacking cap-cup diagrams on top.
* `TauCeti.composeDiagram_capCup_left` and `TauCeti.middleLoopCount_capCup_left`: stacking
  `capCup a b` above any diagram `D` reconnects its top points `a` and `b`, closing a single loop
  when `D` already cups them and none otherwise; `TauCeti.composeDiagram_capCup_right` and
  `TauCeti.middleLoopCount_capCup_right` are the mirrors for stacking `capCup a b` below `D`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

namespace TauCeti

variable {k : ℕ} {a b c d : Fin k} {D : BrauerDiagram k}

/-! ### The arcs of the reconnected diagram -/

namespace BrauerDiagram

section Reconnect

variable (hcap : D.val (Sum.inl a) = Sum.inl b) (hcup : D.val (Sum.inr c) = Sum.inr d)
include hcap hcup

/-- **The reconnected diagram has one cap fewer**: it caps exactly the bottom points capped by `D`
other than `a` and `b`. -/
theorem bottomCap_reconnect :
    bottomCap (D.reconnect (Sum.inr c) (Sum.inl a)) = (D.bottomCap.erase a).erase b := by
  ext i
  simp only [mem_bottomCap, Finset.mem_erase, isCap_def, Sum.isLeft_inl, true_and]
  by_cases hia : i = a
  · subst i
    simp [PerfectMatching.reconnect_val_right Sum.inl_ne_inr]
  by_cases hib : i = b
  · subst i
    simp [hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_right (D := D) Sum.inl_ne_inr]
  rw [PerfectMatching.reconnect_val_of_ne Sum.inl_ne_inr (by simpa using hia)
    (hcup ▸ Sum.inl_ne_inr) (hcap ▸ by simpa using hib)]
  simp [hia, hib]

/-- The reconnected diagram has two capped bottom points fewer than `D`. -/
theorem card_bottomCap_reconnect :
    (bottomCap (D.reconnect (Sum.inr c) (Sum.inl a))).card + 2 = D.bottomCap.card := by
  have hab : b ≠ a := fun h => D.apply_ne (Sum.inl a) (by rw [hcap, h])
  have ha : a ∈ D.bottomCap := by simp [isCap_def, hcap]
  have hb : b ∈ D.bottomCap.erase a := by
    simp [hab, isCap_def, D.apply_eq_of_apply_eq hcap]
  have h : 0 < (D.bottomCap.erase a).card := Finset.card_pos.mpr ⟨b, hb⟩
  rw [Finset.card_erase_of_mem ha] at h
  rw [bottomCap_reconnect hcap hcup, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
  omega

end Reconnect

end BrauerDiagram

/-! ### Undoing the reconnection by a cap-cup diagram -/

section Reconnect

variable (hcap : D.val (Sum.inl a) = Sum.inl b) (hcup : D.val (Sum.inr c) = Sum.inr d)
include hcap hcup

open BrauerDiagram

/-- **A cap-cup diagram undoes the reconnection of a cap and a cup.** If `D` caps the bottom
points `a` and `b` and cups the top points `c` and `d`, then stacking `capCup c d` above the
diagram `D.reconnect (Sum.inr c) (Sum.inl a)`, in which these two arcs have become the through
strands `a`–`c` and `b`–`d`, gives back `D`. -/
theorem composeDiagram_capCup_reconnect :
    composeDiagram (capCup c d) (D.reconnect (Sum.inr c) (Sum.inl a)) = D := by
  set X := D.reconnect (Sum.inr c) (Sum.inl a)
  have hcd : c ≠ d := fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h])
  have hba : D.val (Sum.inl b) = Sum.inl a := D.apply_eq_of_apply_eq hcap
  have hdc : D.val (Sum.inr d) = Sum.inr c := D.apply_eq_of_apply_eq hcup
  have hXa : X.val (Sum.inl a) = Sum.inr c := PerfectMatching.reconnect_val_right Sum.inl_ne_inr
  have hXb : X.val (Sum.inl b) = Sum.inr d :=
    hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_right Sum.inl_ne_inr
  have hXc : X.val (Sum.inr c) = Sum.inl a := PerfectMatching.reconnect_val_self Sum.inl_ne_inr
  have hXd : X.val (Sum.inr d) = Sum.inl b :=
    hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_self Sum.inl_ne_inr
  refine Subtype.ext (Equiv.ext fun x => ?_)
  -- The four points `a`, `b`, `c`, `d` are treated by hand; every other point keeps its arc.
  by_cases hxa : x = Sum.inl a
  · subst x
    rw [hcap]
    exact composeDiagram_val_inl_eq_inl_of_cap_upper _ _ hXa
      (capCup_val_inl_left hcd) hXd
  by_cases hxb : x = Sum.inl b
  · subst x
    rw [hba]
    exact composeDiagram_val_inl_eq_inl_of_cap_upper _ _ hXb
      (capCup_val_inl_right hcd) hXc
  by_cases hxc : x = Sum.inr c
  · subst x
    rw [hcup]
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hcd)
  by_cases hxd : x = Sum.inr d
  · subst x
    rw [hdc]
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hcd)
  have hX : X.val x = D.val x :=
    PerfectMatching.reconnect_val_of_ne hxc hxa (hcup ▸ hxd) (hcap ▸ hxb)
  obtain ⟨hyc, hyd⟩ := (D.apply_ne_and_ne_iff hcup x).mpr ⟨hxc, hxd⟩
  rcases x with i | j <;> rcases hy : D.val _ with i' | j'
  · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ _ (hX.trans hy)
  · rw [hy] at hyc hyd
    exact composeDiagram_val_inl_eq_inr_of_through _ _ (hX.trans hy)
      (capCup_val_inl_of_ne (by simpa using hyc) (by simpa using hyd))
  · exact composeDiagram_val_inr_eq_inl_of_through _ _
      (capCup_val_inr_of_ne (by simpa using hxc) (by simpa using hxd)) (hX.trans hy)
  · rw [hy] at hyc hyd
    exact composeDiagram_val_inr_eq_inr_of_cup_lower _ _
      (capCup_val_inr_of_ne (by simpa using hxc) (by simpa using hxd)) (hX.trans hy)
      (capCup_val_inl_of_ne (by simpa using hyc) (by simpa using hyd))

/-- **Undoing the reconnection closes up no loop**: every middle point lies on a through strand,
of the reconnected diagram at the two middle points `c` and `d` of the cap, and of the cap-cup
diagram at every other middle point. -/
theorem middleLoopCount_capCup_reconnect :
    middleLoopCount (capCup c d) (D.reconnect (Sum.inr c) (Sum.inl a)) = 0 := by
  refine middleLoopCount_eq_zero_iff.mpr fun m => ?_
  by_cases hmc : m = c
  · subst m
    exact not_onMiddleLoop_of_isThrough_right <| by
      simp [isThrough_def]
  by_cases hmd : m = d
  · subst m
    exact not_onMiddleLoop_of_isThrough_right <| by
      simp [isThrough_def,
        hcap ▸ hcup ▸ PerfectMatching.reconnect_val_val_self (D := D) Sum.inl_ne_inr]
  exact not_onMiddleLoop_of_isThrough_left <| by
    simp [isThrough_def, capCup_val_inl_of_ne hmc hmd]

end Reconnect

/-! ### Induction on Brauer diagrams -/

namespace BrauerDiagram

/-- **A diagram with a cap is a loop-free stack of a cap-cup diagram on a diagram with one cap
fewer.** -/
theorem exists_composeDiagram_capCup_eq (ha : a ∈ D.bottomCap) :
    ∃ c d : Fin k, ∃ X : BrauerDiagram k, c ≠ d ∧ middleLoopCount (capCup c d) X = 0 ∧
      X.bottomCap.card + 2 = D.bottomCap.card ∧ composeDiagram (capCup c d) X = D := by
  obtain ⟨b, hcap⟩ : ∃ b, D.val (Sum.inl a) = Sum.inl b :=
    Sum.isLeft_iff.mp ((isCap_def D _).mp ((mem_bottomCap D).mp ha)).2
  obtain ⟨c, hc⟩ : D.topCup.Nonempty := by
    rw [← Finset.card_pos, ← card_bottomCap_eq_card_topCup]
    exact Finset.card_pos.mpr ⟨a, ha⟩
  obtain ⟨d, hcup⟩ : ∃ d, D.val (Sum.inr c) = Sum.inr d :=
    Sum.isRight_iff.mp ((isCup_def D _).mp ((mem_topCup D).mp hc)).2
  exact ⟨c, d, _, fun h => D.apply_ne (Sum.inr c) (by rw [hcup, h]),
    middleLoopCount_capCup_reconnect hcap hcup, card_bottomCap_reconnect hcap hcup,
    composeDiagram_capCup_reconnect hcap hcup⟩

/-- **Induction on Brauer diagrams.** A property of Brauer diagrams that holds for every
permutation diagram, and passes from a diagram `X` to the stack `capCup a b ∘ X` of a cap-cup
diagram on two distinct strands above it whenever that stack closes up no loop, holds for every
Brauer diagram. -/
@[elab_as_elim]
theorem capCup_induction_on {motive : BrauerDiagram k → Prop} (D : BrauerDiagram k)
    (permToBrauer : ∀ σ : Equiv.Perm (Fin k), motive (permToBrauer σ))
    (capCup_compose : ∀ (a b : Fin k) (X : BrauerDiagram k), a ≠ b →
      middleLoopCount (capCup a b) X = 0 → motive X → motive (composeDiagram (capCup a b) X)) :
    motive D := by
  induction hD : D.bottomCap.card using Nat.strong_induction_on generalizing D with
  | _ m ih =>
    obtain hempty | ⟨a, ha⟩ := D.bottomCap.eq_empty_or_nonempty
    · obtain ⟨σ, rfl⟩ := (exists_eq_permToBrauer_iff_bottomCap_eq_empty (D := D)).mpr hempty
      exact permToBrauer σ
    obtain ⟨c, d, X, hcd, hloop, hcard, rfl⟩ := exists_composeDiagram_capCup_eq ha
    exact capCup_compose c d X hcd hloop (ih _ (by omega) X rfl)

end BrauerDiagram

/-! ### Stacking a cap-cup diagram against any diagram -/

/-- When `D` does not already cup `a` to `b`, the strand of `capCup a b ∘ D` starting at the
partner of `Sum.inr a` in `D` runs across the cap `a`–`b` of `capCup a b` and emerges at the
partner of `Sum.inr b` in `D`. -/
private theorem composeDiagram_capCup_left_val_partner (hab : a ≠ b) (D : BrauerDiagram k)
    (hcup : D.val (Sum.inr a) ≠ Sum.inr b) :
    (composeDiagram (capCup a b) D).val (D.val (Sum.inr a)) = D.val (Sum.inr b) := by
  set p := D.val (Sum.inr a)
  set q := D.val (Sum.inr b)
  have hpa : p ≠ Sum.inr a := D.apply_ne (Sum.inr a)
  have hqa : q ≠ Sum.inr a := fun h => hcup (D.apply_eq_of_apply_eq h)
  have hqb : q ≠ Sum.inr b := D.apply_ne (Sum.inr b)
  have hDp : D.val p = Sum.inr a := D.apply_apply (Sum.inr a)
  -- First leg: from the outer point `p` up to `a` and across the cap of `capCup a b` to `b`.
  have hleg₁ : ∃ s, stackStart (capCup a b) D p = Sum.inr s ∧
      Relation.ReflTransGen (fun u v => stackStep (capCup a b) D u = Sum.inr v) s (Sum.inr b) := by
    rcases hp : p with i | j
    · rw [hp] at hDp
      exact ⟨Sum.inl a, by rw [stackStart_inl, hDp, Sum.elim_inr],
        .single (by rw [stackStep_inl, capCup_val_inl_left hab, Sum.elim_inl])⟩
    · rw [hp] at hpa hDp
      have hja : j ≠ a := by simpa using hpa
      have hjb : j ≠ b := fun h => hcup (hp.trans (congrArg Sum.inr h))
      exact ⟨Sum.inr j,
        by rw [stackStart_inr, capCup_val_inr_of_ne hja hjb, Sum.elim_inl],
        (Relation.ReflTransGen.single (by rw [stackStep_inr, hDp, Sum.elim_inr])).tail
          (by rw [stackStep_inl, capCup_val_inl_left hab, Sum.elim_inl])⟩
  -- Second leg: from `b` down along the arc of `D` at `Sum.inr b` and out at `q`.
  have hleg₂ : ∃ t,
      Relation.ReflTransGen (fun u v => stackStep (capCup a b) D u = Sum.inr v) (Sum.inr b) t ∧
      stackStep (capCup a b) D t = Sum.inl q := by
    rcases hq : q with i' | j'
    · have hDb : D.val (Sum.inr b) = Sum.inl i' := hq
      exact ⟨Sum.inr b, .refl, by rw [stackStep_inr, hDb, Sum.elim_inl]⟩
    · have hDb : D.val (Sum.inr b) = Sum.inr j' := hq
      rw [hq] at hqa hqb
      have hj'a : j' ≠ a := by simpa using hqa
      have hj'b : j' ≠ b := by simpa using hqb
      exact ⟨Sum.inl j', .single (by rw [stackStep_inr, hDb, Sum.elim_inr]),
        by rw [stackStep_inl, capCup_val_inl_of_ne hj'a hj'b, Sum.elim_inr]⟩
  obtain ⟨s, hstart, hpath₁⟩ := hleg₁
  obtain ⟨t, hpath₂, hexit⟩ := hleg₂
  exact (composeDiagram_val_eq_iff _ _).mpr (Or.inr ⟨s, t, hstart, hpath₁.trans hpath₂, hexit⟩)

/-- Strands of `D` disjoint from `Sum.inr a` and `Sum.inr b` pass unchanged through stacking
`capCup a b` on top. -/
private theorem composeDiagram_capCup_left_val_of_ne {a b : Fin k} {D : BrauerDiagram k}
    {x : Fin k ⊕ Fin k} (hxa : x ≠ Sum.inr a) (hxb : x ≠ Sum.inr b)
    (hya : D.val x ≠ Sum.inr a) (hyb : D.val x ≠ Sum.inr b) :
    (composeDiagram (capCup a b) D).val x = D.val x := by
  rcases x with i | j <;> rcases hy : D.val _ with i' | j'
  · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ _ hy
  · rw [hy] at hya hyb
    exact composeDiagram_val_inl_eq_inr_of_through _ _ hy
      (capCup_val_inl_of_ne (by simpa using hya) (by simpa using hyb))
  · exact composeDiagram_val_inr_eq_inl_of_through _ _
      (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
  · rw [hy] at hya hyb
    exact composeDiagram_val_inr_eq_inr_of_cup_lower _ _
      (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
      (capCup_val_inl_of_ne (by simpa using hya) (by simpa using hyb))

/-- **Stacking a cap-cup diagram above any diagram reconnects its two top points.** On distinct
strands `a ≠ b`, stacking `capCup a b` above `D` replaces the arcs of `D` at the top points `a`
and `b` by the cup `a`–`b` and the arc joining their old partners; when `D` already cups `a` to
`b`, `PerfectMatching.reconnect_partner` says that reconnection leaves `D` unchanged. -/
theorem composeDiagram_capCup_left (hab : a ≠ b) (D : BrauerDiagram k) :
    composeDiagram (capCup a b) D = D.reconnect (Sum.inr a) (Sum.inr b) := by
  have hab' : (Sum.inr b : Fin k ⊕ Fin k) ≠ Sum.inr a := by simpa using hab.symm
  by_cases hcup : D.val (Sum.inr a) = Sum.inr b
  · rw [← hcup, PerfectMatching.reconnect_partner]
    refine Subtype.ext (Equiv.ext fun x => ?_)
    by_cases hxa : x = Sum.inr a
    · subst x; rw [hcup]
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab)
    by_cases hxb : x = Sum.inr b
    · subst x; rw [D.apply_eq_of_apply_eq hcup]
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab)
    obtain ⟨hya, hyb⟩ := (D.apply_ne_and_ne_iff hcup x).mpr ⟨hxa, hxb⟩
    exact composeDiagram_capCup_left_val_of_ne hxa hxb hya hyb
  · have hpq := composeDiagram_capCup_left_val_partner hab D hcup
    refine Subtype.ext (Equiv.ext fun x => ?_)
    by_cases hxa : x = Sum.inr a
    · subst x
      rw [PerfectMatching.reconnect_val_self hab']
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab)
    by_cases hxb : x = Sum.inr b
    · subst x
      rw [PerfectMatching.reconnect_val_right hab']
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab)
    by_cases hxp : x = D.val (Sum.inr a)
    · subst x; rwa [PerfectMatching.reconnect_val_val_self hab']
    by_cases hxq : x = D.val (Sum.inr b)
    · subst x; rw [PerfectMatching.reconnect_val_val_right hab']
      exact (composeDiagram (capCup a b) D).apply_eq_of_apply_eq hpq
    rw [PerfectMatching.reconnect_val_of_ne hxa hxb hxp hxq]
    exact composeDiagram_capCup_left_val_of_ne hxa hxb
      (fun h => hxp (D.apply_eq_of_apply_eq h).symm)
      (fun h => hxq (D.apply_eq_of_apply_eq h).symm)

/-- **The middle-loop count when stacking a cap-cup diagram on top.** On distinct strands `a ≠ b`,
stacking `capCup a b` above `D` closes up one loop when `D` already cups `a` to `b` — the two-point
loop formed by that cup and the cap of `capCup a b` — and closes up no loop otherwise. -/
theorem middleLoopCount_capCup_left (hab : a ≠ b) (D : BrauerDiagram k) :
    middleLoopCount (capCup a b) D = if D.val (Sum.inr a) = Sum.inr b then 1 else 0 := by
  split_ifs with hcup
  · have hpos := middleLoopCount_pos_of_val_eq (capCup_val_inl_left hab) hcup
    have hsub : {x : Fin k | IsMiddleLoopMin (capCup a b) D x}.Subsingleton := by
      intro p hp q hq
      have hp' := (BrauerDiagram.isCap_capCup_inl_iff hab).mp
        (((isMiddleVertex_def _ _ p).mp ((isMiddleLoopMin_def _ _ p).mp hp).1.isMiddleVertex).1)
      have hq' := (BrauerDiagram.isCap_capCup_inl_iff hab).mp
        (((isMiddleVertex_def _ _ q).mp ((isMiddleLoopMin_def _ _ q).mp hq).1.isMiddleVertex).1)
      have hadj : Relation.ReflTransGen (MiddleAdj (capCup a b) D) p q := by
        rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
        · exact .refl
        · exact .single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_left hab)))
        · exact .single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_right hab)))
        · exact .refl
      exact hp.eq_of_reflTransGen hq hadj
    have hle : middleLoopCount (capCup a b) D ≤ 1 := by
      rw [middleLoopCount_def]
      rcases hsub.eq_empty_or_singleton with h | ⟨x, h⟩ <;> simp [h]
    omega
  · refine middleLoopCount_eq_zero_iff.mpr fun x hx => ?_
    have hcap_x := ((isMiddleVertex_def _ _ x).mp hx.isMiddleVertex).1
    have ha : OnMiddleLoop (capCup a b) D a := by
      rcases (BrauerDiagram.isCap_capCup_inl_iff hab).mp hcap_x with rfl | rfl
      · exact hx
      · exact hx.reflTransGen
          (.single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_right hab))))
    have hcup_a := ((isMiddleVertex_def _ _ a).mp ha.isMiddleVertex).2
    obtain ⟨m, hm⟩ := Sum.isRight_iff.mp ((BrauerDiagram.isCup_def D (Sum.inr a)).mp hcup_a).2
    have hm_loop : OnMiddleLoop (capCup a b) D m :=
      ha.reflTransGen (.single ((middleAdj_def _ _ _ _).mpr (Or.inr hm)))
    have hcap_m := ((isMiddleVertex_def _ _ m).mp hm_loop.isMiddleVertex).1
    rcases (BrauerDiagram.isCap_capCup_inl_iff hab).mp hcap_m with hma | hmb
    · subst m; exact D.apply_ne (Sum.inr a) hm
    · subst m; exact hcup hm

/-- **Stacking a cap-cup diagram below any diagram reconnects its two bottom points**, the
reflection of `TauCeti.composeDiagram_capCup_left`. -/
theorem composeDiagram_capCup_right (hab : a ≠ b) (D : BrauerDiagram k) :
    composeDiagram D (capCup a b) = D.reconnect (Sum.inl a) (Sum.inl b) := by
  apply BrauerDiagram.flip_injective
  rw [flip_composeDiagram, BrauerDiagram.flip_capCup, composeDiagram_capCup_left hab]
  refine PerfectMatching.ext fun z => ?_
  rw [BrauerDiagram.flip_val (D.reconnect (Sum.inl a) (Sum.inl b)) z, PerfectMatching.reconnect_val,
    PerfectMatching.reconnect_val]
  simp only [Equiv.permCongr_apply, Equiv.symm_swap, BrauerDiagram.flip_val_inr]
  have hswap (w : Fin k ⊕ Fin k) :
      (Equiv.swap (D.val (Sum.inl a)) (Sum.inl b) w).swap =
        Equiv.swap (D.val (Sum.inl a)).swap (Sum.inr b) w.swap := by
    have h := Equiv.swap_apply_apply (Equiv.sumComm (Fin k) (Fin k)) (D.val (Sum.inl a)) (Sum.inl b)
    simpa [Equiv.Perm.mul_apply] using Equiv.congr_fun h.symm w.swap
  set u := Equiv.swap (D.val (Sum.inl a)).swap (Sum.inr b) z
  have hu : u.swap = Equiv.swap (D.val (Sum.inl a)) (Sum.inl b) z.swap := by
    simpa [u] using congrArg Sum.swap (hswap z.swap).symm
  rw [D.flip_val u, hu, ← hswap]

/-- **The middle-loop count when stacking a cap-cup diagram underneath**, the reflection of
`TauCeti.middleLoopCount_capCup_left`. -/
theorem middleLoopCount_capCup_right (hab : a ≠ b) (D : BrauerDiagram k) :
    middleLoopCount D (capCup a b) = if D.val (Sum.inl a) = Sum.inl b then 1 else 0 := by
  rw [← middleLoopCount_flip, BrauerDiagram.flip_capCup, middleLoopCount_capCup_left hab,
    BrauerDiagram.flip_val_inr]
  exact if_congr ⟨fun h => by simpa using congrArg Sum.swap h,
    fun h => by rw [h]; rfl⟩ rfl rfl

end TauCeti
