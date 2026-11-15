/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Disjoint sums of graphs

Five gaps in Mathlib's `SimpleGraph.sum` API.

`SimpleGraph.sum` has no `DecidableRel` instance in Mathlib. Consequently, even when adjacency in
both summands is decidable, `(G ⊕g H).edgeFinset` is not expressible without supplying an
instance. `TauCeti.instDecidableRelSumAdj` supplies it by the four-way case split in the definition
of `SimpleGraph.sum`.

Nor does it describe the graphs containing a disjoint sum: `SimpleGraph.sum_le_iff` says a graph on
`V ⊕ W` contains `G ⊕g H` exactly when its two sides contain `G` and `H`, which is how containing a
disjoint union of patterns splits into two independent containment events.

`SimpleGraph.sum` has no `bot` law in Mathlib either: `TauCeti.SimpleGraph.sum_bot_bot` says a
disjoint sum of edgeless graphs is edgeless, the form in which a graph parameter that is
multiplicative over disjoint sums is evaluated on an edgeless graph.

Mathlib's `SimpleGraph.edgeSetSumEquiv`, implemented by `Sym2.fromRelNdrec`, comes with no
evaluation lemmas. `SimpleGraph.coe_edgeSetSumEquiv_symm_inl` and
`SimpleGraph.coe_edgeSetSumEquiv_symm_inr` say that its inverse sends an edge of either summand to
its image under the corresponding inclusion, which is how a product over the edges of `G ⊕g H`
splits into products over the edges of `G` and of `H`.

Finally, `SimpleGraph.reachable_sum_inl_iff`, `SimpleGraph.reachable_sum_inr_iff`, and
`SimpleGraph.connectedComponentSumEquiv` identify reachability within each summand and split the
connected components of `G ⊕g H` as `G.ConnectedComponent ⊕ H.ConnectedComponent`.

## Main results

* `TauCeti.instDecidableRelSumAdj` — adjacency in a disjoint sum is decidable;
* `SimpleGraph.sum_le_iff` — a graph contains a disjoint sum exactly when its two sides contain the
  summands;
* `TauCeti.SimpleGraph.sum_bot_bot` — a disjoint sum of edgeless graphs is edgeless;
* `SimpleGraph.coe_edgeSetSumEquiv_symm_inl`, `SimpleGraph.coe_edgeSetSumEquiv_symm_inr` — the
  edges of the two summands sit in the disjoint sum through the two inclusions;
* `SimpleGraph.reachable_sum_inl_iff`, `SimpleGraph.reachable_sum_inr_iff`,
  `SimpleGraph.connectedComponentSumEquiv` — reachability and connected components of `G ⊕g H`
  split across the two summands.
-/

public section

namespace TauCeti

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Adjacency in a disjoint sum of graphs is decidable: `SimpleGraph.sum` splits on which sides its
two arguments lie, and vertices on opposite sides are never adjacent. -/
instance instDecidableRelSumAdj (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | .inl u, .inl v => ‹DecidableRel G.Adj› u v
  | .inr u, .inr v => ‹DecidableRel H.Adj› u v
  | .inl _, .inr _ => isFalse (by simp)
  | .inr _, .inl _ => isFalse (by simp)

/-- A graph on `V ⊕ W` contains the disjoint sum `G ⊕g H` exactly when its restrictions to the two
sides contain `G` and `H`: the sum has no edges across the sides. -/
@[simp]
theorem _root_.SimpleGraph.sum_le_iff {K : SimpleGraph (V ⊕ W)} :
    G ⊕g H ≤ K ↔ G ≤ K.comap Sum.inl ∧ H ≤ K.comap Sum.inr := by
  refine ⟨fun h => ⟨fun a b hab => h (sum_adj_inl.2 hab), fun a b hab => h (sum_adj_inr.2 hab)⟩,
    ?_⟩
  rintro ⟨hG, hH⟩ (a | a) (b | b) hab
  · exact hG (sum_adj_inl.1 hab)
  · simp at hab
  · simp at hab
  · exact hH (sum_adj_inr.1 hab)

-- Both evaluation lemmas reduce the `Sym2.fromRelNdrec` implementation of `edgeSetSumEquiv` on an
-- edge `s(a, b)`, which holds by `rfl` once the edge is split into its endpoints.

/-- The inverse of `SimpleGraph.edgeSetSumEquiv` sends an edge of `G` to its image under the left
inclusion `Sum.inl`. -/
@[simp]
theorem _root_.SimpleGraph.coe_edgeSetSumEquiv_symm_inl (e : G.edgeSet) :
    ((edgeSetSumEquiv.symm (.inl e) : (G ⊕g H).edgeSet) : Sym2 (V ⊕ W)) =
      Sym2.map Sum.inl (e : Sym2 V) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with | _ a b => rfl

/-- The inverse of `SimpleGraph.edgeSetSumEquiv` sends an edge of `H` to its image under the right
inclusion `Sum.inr`. -/
@[simp]
theorem _root_.SimpleGraph.coe_edgeSetSumEquiv_symm_inr (e : H.edgeSet) :
    ((edgeSetSumEquiv.symm (.inr e) : (G ⊕g H).edgeSet) : Sym2 (V ⊕ W)) =
      Sym2.map Sum.inr (e : Sym2 W) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with | _ a b => rfl

namespace SimpleGraph

/-- A disjoint sum of edgeless graphs is edgeless: no edge is contributed by either summand, and
none across the two sides. -/
theorem sum_bot_bot : ((⊥ : SimpleGraph V) ⊕g (⊥ : SimpleGraph W)) = ⊥ := by
  ext u v
  cases u <;> cases v <;> simp

end SimpleGraph

private theorem reachable_of_walk_sum_inl {x y : V ⊕ W} {v : V}
    (p : (G ⊕g H).Walk x y) (hy : y = .inl v) : ∃ u : V, x = .inl u ∧ G.Reachable u v := by
  induction p with
  | nil => exact ⟨v, hy, .rfl⟩
  | @cons x _ _ hadj _ ih =>
    obtain ⟨u', rfl, hreach⟩ := ih hy
    rcases x with u | w
    · exact ⟨u, rfl, (Adj.reachable (sum_adj_inl.mp hadj)).trans hreach⟩
    · simp at hadj

/-- Two left-summand vertices are reachable in `G ⊕g H` iff they are reachable in `G`. -/
@[simp]
theorem _root_.SimpleGraph.reachable_sum_inl_iff {u v : V} :
    (G ⊕g H).Reachable (.inl u) (.inl v) ↔ G.Reachable u v := by
  refine ⟨fun ⟨p⟩ => ?_, fun h => h.map Embedding.sumInl.toHom⟩
  obtain ⟨u', hu', hreach⟩ := reachable_of_walk_sum_inl p rfl
  exact Sum.inl.inj hu' ▸ hreach

/-- Two right-summand vertices are reachable in `G ⊕g H` iff they are reachable in `H`. -/
@[simp]
theorem _root_.SimpleGraph.reachable_sum_inr_iff {u v : W} :
    (G ⊕g H).Reachable (.inr u) (.inr v) ↔ H.Reachable u v :=
  ⟨fun h => reachable_sum_inl_iff.mp (h.map Iso.sumComm.toHom),
    fun h => h.map Embedding.sumInr.toHom⟩

/-- Connected components of a disjoint sum `G ⊕g H` decompose as the sum of the connected
components of `G` and of `H`. -/
def _root_.SimpleGraph.connectedComponentSumEquiv (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).ConnectedComponent ≃ G.ConnectedComponent ⊕ H.ConnectedComponent where
  toFun := ConnectedComponent.lift
    (Sum.elim (Sum.inl ∘ G.connectedComponentMk) (Sum.inr ∘ H.connectedComponentMk))
    fun x y p _ => by
      rcases x with u₁ | w₁ <;> rcases y with u₂ | w₂
      · simp [ConnectedComponent.eq, reachable_sum_inl_iff.mp p.reachable]
      · exact (not_reachable_sum_inl_inr u₁ w₂ p.reachable).elim
      · exact (not_reachable_sum_inl_inr u₂ w₁ p.reachable.symm).elim
      · simp [ConnectedComponent.eq, reachable_sum_inr_iff.mp p.reachable]
  invFun := Sum.elim (ConnectedComponent.map Embedding.sumInl.toHom)
    (ConnectedComponent.map Embedding.sumInr.toHom)
  left_inv c := c.ind fun x => by cases x <;> rfl
  right_inv x := by rcases x with c | c <;> exact c.ind fun _ => rfl

/-- `SimpleGraph.connectedComponentSumEquiv` sends a left-summand component to `Sum.inl`. -/
@[simp]
theorem _root_.SimpleGraph.connectedComponentSumEquiv_mk_inl (v : V) :
    G.connectedComponentSumEquiv H ((G ⊕g H).connectedComponentMk (.inl v)) =
      .inl (G.connectedComponentMk v) := (rfl)

/-- `SimpleGraph.connectedComponentSumEquiv` sends a right-summand component to `Sum.inr`. -/
@[simp]
theorem _root_.SimpleGraph.connectedComponentSumEquiv_mk_inr (w : W) :
    G.connectedComponentSumEquiv H ((G ⊕g H).connectedComponentMk (.inr w)) =
      .inr (H.connectedComponentMk w) := (rfl)

/-- The inverse of `SimpleGraph.connectedComponentSumEquiv` maps `Sum.inl` along `sumInl`. -/
@[simp]
theorem _root_.SimpleGraph.connectedComponentSumEquiv_symm_inl (c : G.ConnectedComponent) :
    (G.connectedComponentSumEquiv H).symm (.inl c) =
      ConnectedComponent.map Embedding.sumInl.toHom c := (rfl)

/-- The inverse of `SimpleGraph.connectedComponentSumEquiv` maps `Sum.inr` along `sumInr`. -/
@[simp]
theorem _root_.SimpleGraph.connectedComponentSumEquiv_symm_inr (c : H.ConnectedComponent) :
    (G.connectedComponentSumEquiv H).symm (.inr c) =
      ConnectedComponent.map Embedding.sumInr.toHom c := (rfl)

end TauCeti
