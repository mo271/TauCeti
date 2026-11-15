/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# The Bass–Serre tree of a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ` with base vertex `v₀`. The Bass–Serre covering
tree `GraphOfGroups.bassSerreTree 𝔸 v₀` is a `GTree` for the fundamental group `π₁(𝔸, v₀)`:

* Its vertices are the classes `p A_v` (`bassSerreVertex p`) of `𝔸`-paths `p` from `v₀` to `v`,
  where `p ≈ q` when `p` is homotopic to `q a` for some `a ∈ A_v`, with base vertex
  `bassSerreBase 𝔸 v₀ = 1 A_{v₀}`.
* Its darts over a dart `e` of `Γ` are the classes `p α_e(A_e)` (`bassSerreDart e p`) of `𝔸`-paths
  `p` from `v₀` to `src e`, where `p ≈ q` when `p` is homotopic to `q α_e(c)` for some `c ∈ A_e`.
  The source of `p α_e(A_e)` is `p A_{src e}` and its reverse is `(p e) α_{rev e}(A_e)`, whose
  source is `(p e) A_{tgt e}` because `α_{rev e} = ω_e` and `p α_e(c) e` is homotopic to
  `p e ω_e(c)`.
* The group `π₁(𝔸, v₀)` acts on vertices and darts by left concatenation of closed `𝔸`-paths at
  `v₀`, without inversions because `Γ.rev e ≠ e`.

Connectedness holds by induction on `𝔸`-paths from `v₀`, and acyclicity follows from the normal
form theorem (`GraphOfGroups.AlternatingPath.IsReduced.toPath_homotopic_ofVertex_iff`): any
reduced path in the Bass–Serre graph lifts to a reduced alternating `𝔸`-path of the same length, so
a reduced closed path has length zero.

The stabilizer of the vertex `p A_v` is the image of `A_v` under `π₁.vertexHom p` (`p A_v p⁻¹`),
isomorphic to `A_v` by injectivity of `π₁.vertexHom p`, and the stabilizer of the dart
`p α_e(A_e)` is `((π₁.vertexHom p).comp (𝔸.α e)).range` (`p α_e(A_e) p⁻¹`), isomorphic to `A_e`.
The darts and the adjacent vertices issuing from `p A_v` are in bijection with
`Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range`.

Quotient graphs, edgeless and disconnected graphs of groups, and the comparison with homotopy
classes of `𝔸`-paths without the right `A_v`-quotient are developed in
`TauCeti.GroupTheory.GraphOfGroups.BassSerre.Quotient`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTree`: the Bass–Serre `GTree` of `(𝔸, v₀)` for `π₁(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreVertex`, `TauCeti.GraphOfGroups.bassSerreBase`,
  `TauCeti.GraphOfGroups.bassSerreDart`, `TauCeti.GraphOfGroups.bassSerreArrowDart`,
  `TauCeti.GraphOfGroups.bassSerreArrow`: constructors for vertices, darts, and arrows of
  `bassSerreTree 𝔸 v₀`.
* `TauCeti.GraphOfGroups.stabilizerBassSerreVertexEquiv`,
  `TauCeti.GraphOfGroups.stabilizerBassSerreDartEquiv`: isomorphisms from `A_v` and `A_e` onto the
  vertex and dart stabilizers.
* `TauCeti.GraphOfGroups.bassSerreStarEquiv`, `TauCeti.GraphOfGroups.bassSerreNeighborEquiv`: the
  star and the neighbors of `p A_v` as disjoint unions of left coset spaces `A_v ⧸ α_e(A_e)`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `bassSerreTree 𝔸 v₀` is a tree.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreVertex`: the stabilizer of `p A_v` is
  `(π₁.vertexHom p).range`.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreDart`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreDart_cons_vertex`: dart stabilizers are the conjugates
  `p α_e(A_e) p⁻¹` and `p a α_e(A_e) a⁻¹ p⁻¹`.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreTree_vertex_eq_bot`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreTree_dart_eq_bot`: when all vertex groups are trivial,
  `π₁(𝔸, v₀)` acts freely on `bassSerreTree 𝔸 v₀`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

open SerreGraph _root_.MulAction

/-! ### Path coset quotients -/

section PathCoset

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Two `𝔸`-paths `p` and `q` from `v₀` to `v` represent the same right `H`-class `p H` when `p` is
homotopic to `q h` for some `h ∈ H`. -/
def pathCosetRel {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v))
    (p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : Prop :=
  ∃ h ∈ H, p.Homotopic (q.cons (.vertex h))

/-- The right `H`-coset relation on `𝔸`-paths is an equivalence relation. -/
theorem pathCosetRel_equivalence {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v)) :
    Equivalence (pathCosetRel 𝔸 v₀ H) where
  refl p := ⟨1, H.one_mem, (Path.Homotopic.one p).symm⟩
  symm := by
    rintro p q ⟨h, hh, hpq⟩
    refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
    have h₁ := (hpq.cons (.vertex h⁻¹)).symm
    exact (((Path.Homotopic.mul q h h⁻¹).trans
      (by rw [mul_inv_cancel]; exact .one q)).symm).trans h₁
  trans := by
    rintro p q r ⟨h₁, hh₁, hpq⟩ ⟨h₂, hh₂, hqr⟩
    exact ⟨h₂ * h₁, H.mul_mem hh₂ hh₁,
      (hpq.trans (hqr.cons (.vertex h₁))).trans (Path.Homotopic.mul r h₂ h₁)⟩

/-- The setoid on `𝔸`-paths from `v₀` to `v` identifying `p` with `q h` for `h ∈ H` up to
homotopy. -/
def pathCosetSetoid {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v)) :
    Setoid (𝔸.Path ⟨v₀⟩ ⟨v⟩) :=
  ⟨pathCosetRel 𝔸 v₀ H, pathCosetRel_equivalence 𝔸 v₀ H⟩

/-- Left concatenation of closed `𝔸`-paths at `v₀` on right `H`-classes of `𝔸`-paths. -/
def pathCosetSmul {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v)) :
    π₁ 𝔸 v₀ → Quotient (pathCosetSetoid 𝔸 v₀ H) → Quotient (pathCosetSetoid 𝔸 v₀ H) :=
  π₁.lift
    (fun s => Quotient.lift (fun p => Quotient.mk _ (s.comp p)) fun _ _ ⟨h, hh, hpq⟩ =>
      Quotient.sound ⟨h, hh, by simpa only [Quiver.Path.comp_cons] using hpq.comp_left s⟩)
    fun _ s₂ hs => funext fun q => Quotient.inductionOn q fun p =>
      Quotient.sound ⟨1, H.one_mem,
        (hs.comp_right p).trans (Path.Homotopic.one (s₂.comp p)).symm⟩

private theorem pathCosetSmul_mk {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v))
    (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    pathCosetSmul 𝔸 v₀ H (π₁.mk s) (Quotient.mk _ p) = Quotient.mk _ (s.comp p) := by
  rw [pathCosetSmul, π₁.lift_mk]
  rfl

private theorem pathCosetSmul_one {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v))
    (q : Quotient (pathCosetSetoid 𝔸 v₀ H)) : pathCosetSmul 𝔸 v₀ H 1 q = q :=
  Quotient.inductionOn q fun p => by
    rw [← π₁.mk_nil, pathCosetSmul_mk, Quiver.Path.nil_comp]

private theorem pathCosetSmul_mul {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v))
    (g₁ g₂ : π₁ 𝔸 v₀) (q : Quotient (pathCosetSetoid 𝔸 v₀ H)) :
    pathCosetSmul 𝔸 v₀ H (g₁ * g₂) q = pathCosetSmul 𝔸 v₀ H g₁ (pathCosetSmul 𝔸 v₀ H g₂ q) :=
  π₁.induction_on g₁ fun s₁ => π₁.induction_on g₂ fun s₂ => Quotient.inductionOn q fun p => by
    rw [← π₁.mk_comp, pathCosetSmul_mk, pathCosetSmul_mk, pathCosetSmul_mk, Quiver.Path.comp_assoc]

/-- Left concatenation of `s` fixes `[p]_H` if and only if `[s]` belongs to `p H p⁻¹`. -/
private theorem pathCosetSmul_eq_self_iff {v : Γ.V} (H : Subgroup (𝔸.vertexGroup v))
    (g : π₁ 𝔸 v₀) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    pathCosetSmul 𝔸 v₀ H g (Quotient.mk _ p) = Quotient.mk _ p ↔
      g ∈ H.map (π₁.vertexHom p) := by
  induction g using π₁.induction_on with | _ s =>
  rw [pathCosetSmul_mk, Quotient.eq (r := pathCosetSetoid 𝔸 v₀ H), Subgroup.mem_map]
  refine ⟨fun ⟨h, hh, hs⟩ => ⟨h, hh, ?_⟩, fun ⟨h, hh, hs⟩ => ⟨h, hh, ?_⟩⟩
  · rw [π₁.vertexHom_apply, eq_comm, π₁.mk_eq_mk_iff]
    have h₁ := hs.comp_right p.reverse
    rw [← Path.comp_ofVertex] at h₁
    exact (Path.Homotopic.comp_comp_reverse s p).symm.trans h₁
  · rw [π₁.vertexHom_apply, eq_comm, π₁.mk_eq_mk_iff] at hs
    have h₂ := hs.comp_right p
    rw [Quiver.Path.comp_assoc, Path.comp_ofVertex] at h₂
    exact h₂.trans (by
      simpa only [Quiver.Path.comp_nil] using
        (Path.Homotopic.reverse_comp p).comp_left (p.cons (.vertex h)))

end PathCoset

/-! ### Construction of the Bass–Serre graph and its tree property -/

section Graph

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- The equivalence relation `p ≈ q` (`p ~ q a` for `a ∈ A_v`) defining vertices of
`bassSerreTree 𝔸 v₀` over `v`. -/
abbrev bassSerreVertexSetoid (v : Γ.V) : Setoid (𝔸.Path ⟨v₀⟩ ⟨v⟩) :=
  pathCosetSetoid 𝔸 v₀ (⊤ : Subgroup (𝔸.vertexGroup v))

/-- The equivalence relation `p ≈ q` (`p ~ q α_e(c)` for `c ∈ A_e`) defining darts of
`bassSerreTree 𝔸 v₀` over `e`. -/
abbrev bassSerreDartSetoid (e : Γ.E) : Setoid (𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :=
  pathCosetSetoid 𝔸 v₀ (𝔸.α e).range

/-- Forgetful map from dart coset classes over `e` to vertex coset classes over `Γ.src e`. -/
def bassSerreDartSrc (e : Γ.E) :
    Quotient (bassSerreDartSetoid 𝔸 v₀ e) → Quotient (bassSerreVertexSetoid 𝔸 v₀ (Γ.src e)) :=
  Quotient.lift (fun p => Quotient.mk _ p)
    fun _ _ ⟨h, _, hpq⟩ => Quotient.sound ⟨h, Subgroup.mem_top h, hpq⟩

/-- Reversal of dart coset classes over `e`, sending `[p]` to `[p e]`. -/
def bassSerreDartRev (e : Γ.E) :
    Quotient (bassSerreDartSetoid 𝔸 v₀ e) → Quotient (bassSerreDartSetoid 𝔸 v₀ (Γ.rev e)) :=
  Quotient.lift (fun p => Quotient.mk _ (p.cons (.dart (Γ.dart e))))
    fun _ q ⟨_, ⟨c, rfl⟩, hpq⟩ => Quotient.sound
      ⟨𝔸.ω e c, ⟨(MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c, by
          rw [α_rev_apply, MulEquiv.apply_symm_apply]⟩,
        (hpq.cons (.dart (Γ.dart e))).trans (Path.Homotopic.dart_ω e c q).symm⟩

/-- Reversing a dart coset class twice returns the original dart coset class. -/
theorem bassSerreGraph_rev_rev :
    ∀ d : Σ e : Γ.E, Quotient (bassSerreDartSetoid 𝔸 v₀ e),
      (⟨Γ.rev (Γ.rev d.1), bassSerreDartRev 𝔸 v₀ (Γ.rev d.1) (bassSerreDartRev 𝔸 v₀ d.1 d.2)⟩ :
        Σ e : Γ.E, Quotient (bassSerreDartSetoid 𝔸 v₀ e)) = d
  | ⟨e, q⟩ => Quotient.inductionOn q fun p => by
    have key : ∀ (f : Γ.E) (_ : f = e) (e₁ : Γ.tgt e ⟶ Γ.src f) (e₂ : Γ.tgt e ⟶ Γ.src e),
        e₁.1 = e₂.1 →
        (⟨f, Quotient.mk _ ((p.cons (.dart (Γ.dart e))).cons (.dart e₁))⟩ :
          Σ d : Γ.E, Quotient (bassSerreDartSetoid 𝔸 v₀ d)) =
        ⟨e, Quotient.mk _ ((p.cons (.dart (Γ.dart e))).cons (.dart e₂))⟩ := by
      rintro f rfl e₁ e₂ h
      obtain rfl : e₁ = e₂ := Subtype.ext h
      rfl
    refine (key (Γ.rev (Γ.rev e)) (Γ.rev_rev e) (Γ.dart (Γ.rev e)) (Quiver.reverse (Γ.dart e))
      (by simp)).trans (congrArg (Sigma.mk e) (Quotient.sound ⟨1, (𝔸.α e).range.one_mem, ?_⟩))
    exact (Path.Homotopic.dart_reverse p (Γ.dart e)).trans (Path.Homotopic.one p).symm

-- The carrier graph is exposed so that the Lean `module` code generator sees the same vertex and
-- dart representation for computable constructors and projections across module boundaries.
/-- The Serre graph underlying the Bass–Serre tree of `(𝔸, v₀)`. -/
@[expose] def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := Σ v : Γ.V, Quotient (bassSerreVertexSetoid 𝔸 v₀ v)
  E := Σ e : Γ.E, Quotient (bassSerreDartSetoid 𝔸 v₀ e)
  src d := ⟨Γ.src d.1, bassSerreDartSrc 𝔸 v₀ d.1 d.2⟩
  rev d := ⟨Γ.rev d.1, bassSerreDartRev 𝔸 v₀ d.1 d.2⟩
  rev_rev := bassSerreGraph_rev_rev 𝔸 v₀
  rev_ne d h := Γ.rev_ne d.1 (congrArg Sigma.fst h)

private def graphVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (bassSerreGraph 𝔸 v₀).V :=
  ⟨v, Quotient.mk _ p⟩

private def graphArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreGraph 𝔸 v₀).E :=
  ⟨e.1, Quotient.mk _ (p.cast rfl (congrArg LetterVertex.mk e.2.1.symm))⟩

private theorem graphVertex_eq_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    graphVertex 𝔸 v₀ p = graphVertex 𝔸 v₀ q ↔
      ∃ a : 𝔸.vertexGroup v, p.Homotopic (q.cons (.vertex a)) := by
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ =>
    congrArg (Sigma.mk v) (Quotient.sound ⟨a, Subgroup.mem_top a, ha⟩)⟩
  obtain ⟨a, -, ha⟩ :=
    (Quotient.eq (r := bassSerreVertexSetoid 𝔸 v₀ v)).mp (eq_of_heq (Sigma.mk.inj h).2)
  exact ⟨a, ha⟩

private theorem graphVertex_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    graphVertex 𝔸 v₀ p = graphVertex 𝔸 v₀ q :=
  (graphVertex_eq_iff 𝔸 v₀).mpr ⟨1, h.trans (Path.Homotopic.one q).symm⟩

private theorem src_graphArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreGraph 𝔸 v₀).src (graphArrowDart 𝔸 v₀ p e) = graphVertex 𝔸 v₀ p := by
  obtain ⟨e, rfl, rfl⟩ := e
  rfl

private theorem rev_graphArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreGraph 𝔸 v₀).rev (graphArrowDart 𝔸 v₀ p e) =
      graphArrowDart 𝔸 v₀ (p.cons (.dart e)) (Quiver.reverse e) := by
  let r : b ⟶ a := Quiver.reverse e
  have hr : r.1 = Γ.rev e.1 := Γ.reverse_val e
  obtain ⟨e, rfl, rfl⟩ := e
  have key : ∀ (f : Γ.E) (_ : f = Γ.rev e) (h₁ : Γ.src f = Γ.tgt e),
      (⟨f, Quotient.mk _ ((p.cons (.dart ⟨e, rfl, rfl⟩)).cast rfl
        (congrArg LetterVertex.mk h₁.symm))⟩ : (bassSerreGraph 𝔸 v₀).E) =
        ⟨Γ.rev e, Quotient.mk _ (p.cons (.dart (Γ.dart e)))⟩ := by
    rintro _ rfl h₁
    have hh : congrArg (LetterVertex.mk : Γ.V → 𝔸.LetterVertex) h₁.symm = rfl :=
      Subsingleton.elim _ _
    rw [hh, Γ.dart_def]
    rfl
  exact (key r.1 hr r.2.1).symm

private theorem tgt_graphArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreGraph 𝔸 v₀).tgt (graphArrowDart 𝔸 v₀ p e) =
      graphVertex 𝔸 v₀ (p.cons (.dart e)) := by
  rw [tgt_def, rev_graphArrowDart, src_graphArrowDart]

private theorem graphArrowDart_eq_iff {a b : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} {e : a ⟶ b} :
    graphArrowDart 𝔸 v₀ p e = graphArrowDart 𝔸 v₀ q e ↔
      ∃ h ∈ (𝔸.αArrow e).range, p.Homotopic (q.cons (.vertex h)) := by
  obtain ⟨e, rfl, rfl⟩ := e
  refine ⟨fun h => ?_, fun ⟨a, ha, hpq⟩ =>
    congrArg (Sigma.mk e) (Quotient.sound ⟨a, by simpa using ha, hpq⟩)⟩
  obtain ⟨a, ha, hpq⟩ :=
    (Quotient.eq (r := bassSerreDartSetoid 𝔸 v₀ e)).mp (eq_of_heq (Sigma.mk.inj h).2)
  exact ⟨a, by simpa using ha, hpq⟩

private theorem graphArrowDart_congr {a b : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} (h : p.Homotopic q)
    (e : a ⟶ b) : graphArrowDart 𝔸 v₀ p e = graphArrowDart 𝔸 v₀ q e :=
  (graphArrowDart_eq_iff 𝔸 v₀).mpr
    ⟨1, (𝔸.αArrow e).range.one_mem, h.trans (Path.Homotopic.one q).symm⟩

private theorem exists_graphArrowDart_of_hom {z y : (bassSerreGraph 𝔸 v₀).V}
    (D : z ⟶ y) :
    ∃ (e : z.1 ⟶ y.1) (q : 𝔸.Path ⟨v₀⟩ ⟨z.1⟩),
      e.1 = D.1.1 ∧ graphVertex 𝔸 v₀ q = z ∧ D.1 = graphArrowDart 𝔸 v₀ q e ∧
        graphVertex 𝔸 v₀ (q.cons (.dart e)) = y := by
  obtain ⟨zv, zq⟩ := z
  obtain ⟨yv, yq⟩ := y
  obtain ⟨⟨e₀, dq⟩, hs, ht⟩ := D
  have hs₁ : Γ.src e₀ = zv := congrArg Sigma.fst hs
  have ht₁ : Γ.tgt e₀ = yv := congrArg Sigma.fst ht
  subst hs₁ ht₁
  revert hs ht
  refine Quotient.inductionOn dq fun q hs ht => ⟨⟨e₀, rfl, rfl⟩, q, rfl, hs, rfl, ?_⟩
  exact (tgt_graphArrowDart 𝔸 v₀ q ⟨e₀, rfl, rfl⟩).symm.trans ht

private theorem bassSerreGraph_reachable :
    ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩),
      Nonempty ((bassSerreGraph 𝔸 v₀).Path
        (graphVertex 𝔸 v₀ Quiver.Path.nil) (graphVertex 𝔸 v₀ p))
  | _, .nil => ⟨.nil⟩
  | _, .cons p (.vertex g) => by
    have h : graphVertex 𝔸 v₀ (p.cons (.vertex g)) = graphVertex 𝔸 v₀ p :=
      (graphVertex_eq_iff 𝔸 v₀).mpr ⟨g, .refl _⟩
    exact h ▸ bassSerreGraph_reachable p
  | _, .cons p (.dart e) =>
    (bassSerreGraph_reachable p).map fun P =>
      P.cons ⟨graphArrowDart 𝔸 v₀ p e, src_graphArrowDart 𝔸 v₀ p e,
        tgt_graphArrowDart 𝔸 v₀ p e⟩

/-- The Bass–Serre graph `bassSerreGraph 𝔸 v₀` is connected. -/
theorem bassSerreGraph_connected : (bassSerreGraph 𝔸 v₀).Connected := by
  refine ((bassSerreGraph 𝔸 v₀).connected_iff).mpr
    ⟨⟨graphVertex 𝔸 v₀ Quiver.Path.nil⟩,
      preconnected_of_forall_nonempty_path _ (graphVertex 𝔸 v₀ Quiver.Path.nil) ?_⟩
  rintro ⟨v, q⟩
  exact Quotient.inductionOn q fun p => bassSerreGraph_reachable 𝔸 v₀ p

private theorem lift_reduced_path_not_cancels {a b c : Γ.V} (p₀ : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (w'' : 𝔸.AlternatingPath a b) (e' : b ⟶ c) (g : 𝔸.vertexGroup c) {yv : Γ.V} (e : c ⟶ yv)
    {Dprev D : (bassSerreGraph 𝔸 v₀).E} (hD₁ : D = graphArrowDart 𝔸 v₀
      (p₀.comp (AlternatingPath.cons w'' e' g).toPath) e)
    (hrev_prev : (bassSerreGraph 𝔸 v₀).rev Dprev =
      graphArrowDart 𝔸 v₀ (p₀.comp (AlternatingPath.cons w'' e' 1).toPath) (Quiver.reverse e'))
    (hne : D ≠ (bassSerreGraph 𝔸 v₀).rev Dprev) :
    ¬(AlternatingPath.cons w'' e' g).Cancels e := by
  intro hc
  have hc' : e.1 = Γ.rev e'.1 ∧ g ∈ (𝔸.ωArrow e').range :=
    (AlternatingPath.cancels_cons_iff_ωArrow w'' e' g e).mp hc
  have hy_eq : yv = b := Γ.tgt_eq_src_of_val_eq_rev hc'.1
  subst hy_eq
  obtain rfl : e = Quiver.reverse e' := Γ.eq_reverse_of_val_eq_rev hc'.1
  have hg_range : g ∈ (𝔸.αArrow (Quiver.reverse e')).range := by
    simpa only [𝔸.range_αArrow_reverse] using hc'.2
  have hsame : graphArrowDart 𝔸 v₀ (p₀.comp (AlternatingPath.cons w'' e' g).toPath)
        (Quiver.reverse e') =
      graphArrowDart 𝔸 v₀ (p₀.comp (AlternatingPath.cons w'' e' 1).toPath)
        (Quiver.reverse e') := by
    refine (graphArrowDart_eq_iff 𝔸 v₀).mpr ⟨g, hg_range, ?_⟩
    simpa [Quiver.Path.comp_cons] using
      (AlternatingPath.toPath_setLast_mul_homotopic (AlternatingPath.cons w'' e' 1) g).comp_left p₀
  exact hne (hD₁.trans (hsame.trans hrev_prev.symm))

private theorem lift_reduced_path {x : (bassSerreGraph 𝔸 v₀).V} (p₀ : 𝔸.Path ⟨v₀⟩ ⟨x.1⟩)
    (hp₀ : graphVertex 𝔸 v₀ p₀ = x) :
    ∀ {y : (bassSerreGraph 𝔸 v₀).V} (P : (bassSerreGraph 𝔸 v₀).Path x y),
      SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) P →
      ∃ w : 𝔸.AlternatingPath x.1 y.1,
        w.IsReduced ∧ w.length = P.length ∧
          graphVertex 𝔸 v₀ (p₀.comp w.toPath) = y ∧
          ∀ {z : (bassSerreGraph 𝔸 v₀).V} (P' : (bassSerreGraph 𝔸 v₀).Path x z) (D : z ⟶ y),
            P = P'.cons D →
            ∃ (w'' : 𝔸.AlternatingPath x.1 z.1) (e' : z.1 ⟶ y.1),
              w = .cons w'' e' 1 ∧
                (bassSerreGraph 𝔸 v₀).rev D.1 =
                  graphArrowDart 𝔸 v₀ (p₀.comp w.toPath) (Quiver.reverse e')
  | _, .nil, _ =>
    ⟨.single 1, AlternatingPath.isReduced_single 1, AlternatingPath.length_single 1,
      (graphVertex_congr 𝔸 v₀
        (by simpa [Path.comp_ofVertex] using Path.Homotopic.one p₀)).trans hp₀,
      by rintro _ _ _ h; cases h⟩
  | ⟨yv, yq⟩, .cons P' D, hP => by
    obtain ⟨w', hw', hlen, hz, hlast⟩ := lift_reduced_path p₀ hp₀ P' (hP.of_cons _)
    obtain ⟨e, q, -, hqz, hD, hqy⟩ := exists_graphArrowDart_of_hom 𝔸 v₀ D
    obtain ⟨g, hg⟩ := (graphVertex_eq_iff 𝔸 v₀).mp (hqz.trans hz.symm)
    let w₁ := w'.setLast (w'.last * g)
    have hw₁_hom : Path.Homotopic q (p₀.comp w₁.toPath) :=
      hg.trans (((AlternatingPath.toPath_setLast_mul_homotopic w' g).symm).comp_left p₀)
    have hD₁ : D.1 = graphArrowDart 𝔸 v₀ (p₀.comp w₁.toPath) e :=
      hD.trans (graphArrowDart_congr 𝔸 v₀ hw₁_hom e)
    have hnc : ¬w₁.Cancels e := by
      cases P' with
      | nil =>
        cases w' with
        | single _ =>
          simpa only [w₁, AlternatingPath.setLast_single] using
            AlternatingPath.not_cancels_single _ e
        | cons _ _ _ => simp at hlen
      | @cons b _ P'' Dprev =>
        obtain ⟨bv, bq⟩ := b
        obtain ⟨w'', e', rfl, hrev_prev⟩ := hlast P'' Dprev rfl
        have hw₁_eq : w₁ = .cons w'' e' g := by simp [w₁]
        rw [hw₁_eq] at hD₁ ⊢
        exact lift_reduced_path_not_cancels 𝔸 v₀ p₀ w'' e' g e hD₁ hrev_prev
          ((SerreGraph.Path.isReduced_cons_cons _ P'' Dprev D).mp hP).2
    have hrev_curr : (bassSerreGraph 𝔸 v₀).rev D.1 =
        graphArrowDart 𝔸 v₀ (p₀.comp (AlternatingPath.cons w₁ e 1).toPath) (Quiver.reverse e) := by
      rw [hD₁, rev_graphArrowDart]
      exact graphArrowDart_congr 𝔸 v₀
        (by simpa [AlternatingPath.toPath_cons, Quiver.Path.comp_cons] using
          (Path.Homotopic.one ((p₀.comp w₁.toPath).cons (.dart e))).symm)
        (Quiver.reverse e)
    refine ⟨.cons w₁ e 1,
      (AlternatingPath.isReduced_cons_iff w₁ e 1).mpr
        ⟨(AlternatingPath.isReduced_setLast w' _).mpr hw', hnc⟩,
      (AlternatingPath.length_cons w₁ e 1).trans
        (congrArg (· + 1) ((AlternatingPath.length_setLast w' _).trans hlen)),
      ?_, ?_⟩
    · have hwy :
          Path.Homotopic (p₀.comp (AlternatingPath.cons w₁ e 1).toPath) (q.cons (.dart e)) := by
        simpa [AlternatingPath.toPath_cons, Quiver.Path.comp_cons] using
          (Path.Homotopic.one ((p₀.comp w₁.toPath).cons (.dart e))).trans
            (hw₁_hom.symm.cons (.dart e))
      exact (graphVertex_congr 𝔸 v₀ hwy).trans hqy
    · rintro _ P₁ D₁ hEq
      cases hEq
      exact ⟨w₁, e, rfl, hrev_curr⟩

/-- The Bass–Serre graph `bassSerreGraph 𝔸 v₀` is acyclic. -/
theorem bassSerreGraph_isAcyclic : (bassSerreGraph 𝔸 v₀).IsAcyclic :=
  ((bassSerreGraph 𝔸 v₀).isAcyclic_iff).mpr fun x P hP => by
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : 𝔸.Path ⟨v₀⟩ ⟨x.1⟩, graphVertex 𝔸 v₀ p₀ = x := by
      obtain ⟨v, q⟩ := x
      exact Quotient.inductionOn q fun p₀ => ⟨p₀, rfl⟩
    obtain ⟨w, hw, hlen, hvy, -⟩ := lift_reduced_path 𝔸 v₀ p₀ hp₀ P hP
    obtain ⟨h, hh⟩ := (graphVertex_eq_iff 𝔸 v₀).mp (hvy.trans hp₀.symm)
    have hw_hom : Path.Homotopic w.toPath (Path.ofVertex h) :=
      Path.Homotopic.comp_left_iff.mp (by simpa [Path.comp_ofVertex] using hh)
    have hw_eq : w = .single h := hw.toPath_homotopic_ofVertex_iff.mp hw_hom
    have hlen₀ : P.length = 0 := by simpa [hw_eq] using hlen.symm
    cases P with
    | nil => rfl
    | cons _ _ => simp at hlen₀

/-- The graph automorphism of `bassSerreGraph 𝔸 v₀` given by left concatenation of
`g ∈ π₁(𝔸, v₀)`. -/
def bassSerreGraphAut (g : π₁ 𝔸 v₀) : (bassSerreGraph 𝔸 v₀).Aut where
  equivV :=
    { toFun := fun x => ⟨x.1, pathCosetSmul 𝔸 v₀ ⊤ g x.2⟩
      invFun := fun x => ⟨x.1, pathCosetSmul 𝔸 v₀ ⊤ g⁻¹ x.2⟩
      left_inv := fun ⟨v, q⟩ =>
        congrArg (Sigma.mk (β := fun v => Quotient (bassSerreVertexSetoid 𝔸 v₀ v)) v)
          (by rw [← pathCosetSmul_mul, inv_mul_cancel, pathCosetSmul_one])
      right_inv := fun ⟨v, q⟩ =>
        congrArg (Sigma.mk (β := fun v => Quotient (bassSerreVertexSetoid 𝔸 v₀ v)) v)
          (by rw [← pathCosetSmul_mul, mul_inv_cancel, pathCosetSmul_one]) }
  equivE :=
    { toFun := fun d => ⟨d.1, pathCosetSmul 𝔸 v₀ (𝔸.α d.1).range g d.2⟩
      invFun := fun d => ⟨d.1, pathCosetSmul 𝔸 v₀ (𝔸.α d.1).range g⁻¹ d.2⟩
      left_inv := fun ⟨e, q⟩ =>
        congrArg (Sigma.mk (β := fun e => Quotient (bassSerreDartSetoid 𝔸 v₀ e)) e)
          (by rw [← pathCosetSmul_mul, inv_mul_cancel, pathCosetSmul_one])
      right_inv := fun ⟨e, q⟩ =>
        congrArg (Sigma.mk (β := fun e => Quotient (bassSerreDartSetoid 𝔸 v₀ e)) e)
          (by rw [← pathCosetSmul_mul, mul_inv_cancel, pathCosetSmul_one]) }
  map_src := by
    rintro ⟨e, q⟩
    refine π₁.induction_on g fun s => Quotient.inductionOn q fun p =>
      congrArg (Sigma.mk (β := fun v => Quotient (bassSerreVertexSetoid 𝔸 v₀ v)) (Γ.src e)) ?_
    change bassSerreDartSrc 𝔸 v₀ e
      (pathCosetSmul 𝔸 v₀ (𝔸.α e).range (π₁.mk s) (Quotient.mk _ p)) =
      pathCosetSmul 𝔸 v₀ ⊤ (π₁.mk s) (Quotient.mk _ p)
    rw [pathCosetSmul_mk, pathCosetSmul_mk]
    rfl
  map_rev := by
    rintro ⟨e, q⟩
    refine π₁.induction_on g fun s => Quotient.inductionOn q fun p =>
      congrArg (Sigma.mk (β := fun e => Quotient (bassSerreDartSetoid 𝔸 v₀ e)) (Γ.rev e)) ?_
    change pathCosetSmul 𝔸 v₀ (𝔸.α (Γ.rev e)).range (π₁.mk s)
      (bassSerreDartRev 𝔸 v₀ e (Quotient.mk _ p)) =
      bassSerreDartRev 𝔸 v₀ e (pathCosetSmul 𝔸 v₀ (𝔸.α e).range (π₁.mk s) (Quotient.mk _ p))
    rw [pathCosetSmul_mk]
    let p' : 𝔸.Path ⟨v₀⟩ ⟨Γ.src (Γ.rev e)⟩ := p.cons (.dart (Γ.dart e))
    exact (pathCosetSmul_mk 𝔸 v₀ (𝔸.α (Γ.rev e)).range s p').trans
      (congrArg (Quotient.mk (bassSerreDartSetoid 𝔸 v₀ (Γ.rev e)))
        (Quiver.Path.comp_cons s p (.dart (Γ.dart e))).symm)

/-- The action homomorphism `π₁(𝔸, v₀) →* (bassSerreGraph 𝔸 v₀).Aut`. -/
def bassSerreGraphAction : π₁ 𝔸 v₀ →* (bassSerreGraph 𝔸 v₀).Aut where
  toFun := bassSerreGraphAut 𝔸 v₀
  map_one' := Iso.ext
    (fun ⟨v, q⟩ => congrArg (Sigma.mk (β := fun v => Quotient (bassSerreVertexSetoid 𝔸 v₀ v)) v)
      (pathCosetSmul_one 𝔸 v₀ ⊤ q))
    (fun ⟨e, q⟩ => congrArg (Sigma.mk (β := fun e => Quotient (bassSerreDartSetoid 𝔸 v₀ e)) e)
      (pathCosetSmul_one 𝔸 v₀ _ q))
  map_mul' g₁ g₂ := Iso.ext
    (fun ⟨v, q⟩ => congrArg (Sigma.mk (β := fun v => Quotient (bassSerreVertexSetoid 𝔸 v₀ v)) v)
      (pathCosetSmul_mul 𝔸 v₀ ⊤ g₁ g₂ q))
    (fun ⟨e, q⟩ => congrArg (Sigma.mk (β := fun e => Quotient (bassSerreDartSetoid 𝔸 v₀ e)) e)
      (pathCosetSmul_mul 𝔸 v₀ _ g₁ g₂ q))

/-- Left concatenation by `π₁(𝔸, v₀)` acts without inversions on `bassSerreGraph 𝔸 v₀`. -/
theorem bassSerreGraphAction_equivE_ne_rev (g : π₁ 𝔸 v₀) (d : (bassSerreGraph 𝔸 v₀).E) :
    (bassSerreGraphAction 𝔸 v₀ g).equivE d ≠ (bassSerreGraph 𝔸 v₀).rev d :=
  fun h => Γ.rev_ne d.1 (congrArg Sigma.fst h).symm

end Graph

/-! ### The Bass–Serre `GTree` and its characteristic API -/

section BassSerreTree

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

-- The body is exposed because the Lean `module` compiler requires the vertex and dart types of
-- `bassSerreTree` to agree across module boundaries for computable projections and constructors.
/-- The Bass–Serre covering tree `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`:
vertices are the classes `p A_v` of `𝔸`-paths `p` from `v₀` to `v`, darts over `e` are the classes
`p α_e(A_e)`, and `π₁(𝔸, v₀)` acts without inversions by left concatenation. -/
@[expose] def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := bassSerreGraph 𝔸 v₀
  isTree := ((bassSerreGraph 𝔸 v₀).isTree_iff).mpr
    ⟨bassSerreGraph_connected 𝔸 v₀, bassSerreGraph_isAcyclic 𝔸 v₀⟩
  action := bassSerreGraphAction 𝔸 v₀
  action_smul_ne_rev := bassSerreGraphAction_equivE_ne_rev 𝔸 v₀

/-- The Bass–Serre covering graph `bassSerreTree 𝔸 v₀` is a tree. -/
theorem bassSerreTree_isTree : (bassSerreTree 𝔸 v₀).IsTree :=
  (bassSerreTree 𝔸 v₀).isTree

variable {𝔸 v₀}

/-- The vertex `p A_v` of the Bass–Serre tree represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (bassSerreTree 𝔸 v₀).V :=
  ⟨v, Quotient.mk _ p⟩

variable (𝔸 v₀) in
/-- The base vertex `1 A_{v₀}` of the Bass–Serre tree `bassSerreTree 𝔸 v₀`. -/
@[expose] def bassSerreBase : (bassSerreTree 𝔸 v₀).V :=
  bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)

/-- The dart `p α_e(A_e)` of the Bass–Serre tree over `e : Γ.E`, represented by an `𝔸`-path `p`
from `v₀` to `Γ.src e`. -/
def bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (bassSerreTree 𝔸 v₀).E :=
  ⟨e, Quotient.mk _ p⟩

/-- The dart of the Bass–Serre tree over a quiver arrow `e : a ⟶ b` of `Γ`, represented by an
`𝔸`-path `p` from `v₀` to `a`. -/
def bassSerreArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreTree 𝔸 v₀).E :=
  ⟨e.1, Quotient.mk _ (p.cast rfl (congrArg LetterVertex.mk e.2.1.symm))⟩

/-- Every vertex of `bassSerreTree 𝔸 v₀` is represented by an `𝔸`-path from `v₀`. -/
theorem exists_eq_bassSerreVertex (x : (bassSerreTree 𝔸 v₀).V) :
    ∃ (v : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), bassSerreVertex p = x :=
  let ⟨v, q⟩ := x
  Quotient.inductionOn q fun p => ⟨v, p, rfl⟩

/-- Induction principle for vertices of `bassSerreTree 𝔸 v₀`. -/
@[elab_as_elim] theorem bassSerreVertex_induction_on
    {motive : (bassSerreTree 𝔸 v₀).V → Prop} (x : (bassSerreTree 𝔸 v₀).V)
    (mk : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), motive (bassSerreVertex p)) : motive x := by
  obtain ⟨_, p, rfl⟩ := exists_eq_bassSerreVertex x
  exact mk p

/-- Every dart of `bassSerreTree 𝔸 v₀` is represented by a dart `e` of `Γ` and an `𝔸`-path from
`v₀` to `Γ.src e`. -/
theorem exists_eq_bassSerreDart (d : (bassSerreTree 𝔸 v₀).E) :
    ∃ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), bassSerreDart e p = d :=
  let ⟨e, q⟩ := d
  Quotient.inductionOn q fun p => ⟨e, p, rfl⟩

/-- Induction principle for darts of `bassSerreTree 𝔸 v₀`. -/
@[elab_as_elim] theorem bassSerreDart_induction_on
    {motive : (bassSerreTree 𝔸 v₀).E → Prop} (d : (bassSerreTree 𝔸 v₀).E)
    (mk : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), motive (bassSerreDart e p)) : motive d := by
  obtain ⟨e, p, rfl⟩ := exists_eq_bassSerreDart d
  exact mk e p

@[simp] theorem bassSerreVertex_nil :
    bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) = bassSerreBase 𝔸 v₀ :=
  (rfl)

@[simp] theorem bassSerreVertex_fst {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreVertex p).1 = v :=
  (rfl)

@[simp] theorem bassSerreDart_fst (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreDart e p).1 = e :=
  (rfl)

@[simp] theorem bassSerreArrowDart_fst {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreArrowDart p e).1 = e.1 :=
  (rfl)

/-- Two `𝔸`-paths to `v` represent the same vertex of `bassSerreTree 𝔸 v₀` if and only if they
differ on the right by an element of `A_v` up to homotopy. -/
theorem bassSerreVertex_eq_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    bassSerreVertex p = bassSerreVertex q ↔
      ∃ a : 𝔸.vertexGroup v, p.Homotopic (q.cons (.vertex a)) :=
  graphVertex_eq_iff 𝔸 v₀

/-- Two `𝔸`-paths representing the same vertex of `bassSerreTree 𝔸 v₀` end at the same vertex of
`Γ`. -/
theorem eq_of_bassSerreVertex_eq {v w : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨v⟩} {q : 𝔸.Path ⟨v₀⟩ ⟨w⟩}
    (h : bassSerreVertex p = bassSerreVertex q) : v = w :=
  congrArg Sigma.fst h

/-- Homotopic `𝔸`-paths represent the same vertex of `bassSerreTree 𝔸 v₀`. -/
theorem bassSerreVertex_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    bassSerreVertex p = bassSerreVertex q :=
  graphVertex_congr 𝔸 v₀ h

/-- Appending an element of `A_v` on the right does not change the vertex `p A_v`. -/
@[simp] theorem bassSerreVertex_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) : bassSerreVertex (p.cons (.vertex a)) = bassSerreVertex p :=
  bassSerreVertex_eq_iff.mpr ⟨a, .refl _⟩

@[simp] theorem bassSerreVertex_ofVertex (a : 𝔸.vertexGroup v₀) :
    bassSerreVertex (Path.ofVertex a) = bassSerreBase 𝔸 v₀ := by
  rw [Path.ofVertex_eq_nil_cons, bassSerreVertex_cons_vertex, bassSerreVertex_nil]

/-- Two `𝔸`-paths to `Γ.src e` represent the same dart over `e` if and only if they differ on the
right by `α_e(c)` for some `c ∈ A_e` up to homotopy. -/
theorem bassSerreDart_eq_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    bassSerreDart e p = bassSerreDart e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), p.Homotopic (q.cons (.vertex (𝔸.α e c))) := by
  refine ⟨fun h => ?_, fun ⟨c, hpq⟩ =>
    congrArg (Sigma.mk e) (Quotient.sound ⟨𝔸.α e c, ⟨c, rfl⟩, hpq⟩)⟩
  obtain ⟨_, ⟨c, rfl⟩, hpq⟩ :=
    (Quotient.eq (r := bassSerreDartSetoid 𝔸 v₀ e)).mp (eq_of_heq (Sigma.mk.inj h).2)
  exact ⟨c, hpq⟩

/-- Two representations of the same dart of `bassSerreTree 𝔸 v₀` lie over the same dart of `Γ`. -/
theorem eq_of_bassSerreDart_eq {e f : Γ.E} {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src f⟩} (h : bassSerreDart e p = bassSerreDart f q) : e = f :=
  congrArg Sigma.fst h

/-- Homotopic `𝔸`-paths represent the same dart over `e`. -/
theorem bassSerreDart_congr {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    bassSerreDart e p = bassSerreDart e q :=
  bassSerreDart_eq_iff.mpr ⟨1, by simpa only [map_one] using h.trans (Path.Homotopic.one q).symm⟩

/-- Appending `α_e(c)` on the right does not change the dart `p α_e(A_e)`. -/
@[simp] theorem bassSerreDart_cons_vertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    bassSerreDart e (p.cons (.vertex (𝔸.α e c))) = bassSerreDart e p :=
  bassSerreDart_eq_iff.mpr ⟨c, .refl _⟩

@[simp] theorem bassSerreArrowDart_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    bassSerreArrowDart p ⟨e, rfl, rfl⟩ = bassSerreDart e p :=
  (rfl)

@[simp] theorem bassSerreArrowDart_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    bassSerreArrowDart p (Γ.dart e) = bassSerreDart e p := by
  rw [Γ.dart_def]
  rfl

theorem bassSerreArrowDart_eq_iff {a b : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} {e : a ⟶ b} :
    bassSerreArrowDart p e = bassSerreArrowDart q e ↔
      ∃ h ∈ (𝔸.αArrow e).range, p.Homotopic (q.cons (.vertex h)) :=
  graphArrowDart_eq_iff 𝔸 v₀

theorem eq_of_bassSerreArrowDart_eq {a b c d : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨a⟩} {e : a ⟶ b}
    {q : 𝔸.Path ⟨v₀⟩ ⟨c⟩} {f : c ⟶ d}
    (h : bassSerreArrowDart p e = bassSerreArrowDart q f) : e.1 = f.1 :=
  congrArg Sigma.fst h

theorem bassSerreArrowDart_congr {a b : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} (h : p.Homotopic q)
    (e : a ⟶ b) : bassSerreArrowDart p e = bassSerreArrowDart q e :=
  graphArrowDart_congr 𝔸 v₀ h e

@[simp] theorem src_bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreTree 𝔸 v₀).src (bassSerreDart e p) = bassSerreVertex p :=
  (rfl)

@[simp] theorem rev_bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreTree 𝔸 v₀).rev (bassSerreDart e p) =
      bassSerreDart (Γ.rev e) (p.cons (.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem tgt_bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreTree 𝔸 v₀).tgt (bassSerreDart e p) =
      bassSerreVertex (p.cons (.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem src_bassSerreArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreTree 𝔸 v₀).src (bassSerreArrowDart p e) = bassSerreVertex p :=
  src_graphArrowDart 𝔸 v₀ p e

@[simp] theorem rev_bassSerreArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreTree 𝔸 v₀).rev (bassSerreArrowDart p e) =
      bassSerreArrowDart (p.cons (.dart e)) (Quiver.reverse e) :=
  rev_graphArrowDart 𝔸 v₀ p e

@[simp] theorem tgt_bassSerreArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreTree 𝔸 v₀).tgt (bassSerreArrowDart p e) =
      bassSerreVertex (p.cons (.dart e)) :=
  tgt_graphArrowDart 𝔸 v₀ p e

/-- The arrow in the Bass–Serre tree from `p A_a` to `(p e) A_b` lifted from `e : a ⟶ b`. -/
def bassSerreArrow {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    bassSerreVertex p ⟶ bassSerreVertex (p.cons (.dart e)) :=
  ⟨bassSerreArrowDart p e, src_bassSerreArrowDart p e, tgt_bassSerreArrowDart p e⟩

@[simp] theorem bassSerreArrow_val {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreArrow p e).1 = bassSerreArrowDart p e :=
  (rfl)

/-- `π₁(𝔸, v₀)` acts on vertices of `bassSerreTree 𝔸 v₀` by left concatenation. -/
@[simp] theorem mk_smul_bassSerreVertex {v : Γ.V} (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : π₁.mk s • bassSerreVertex p = bassSerreVertex (s.comp p) :=
  congrArg (Sigma.mk v) (pathCosetSmul_mk 𝔸 v₀ ⊤ s p)

/-- `π₁(𝔸, v₀)` acts on darts of `bassSerreTree 𝔸 v₀` by left concatenation. -/
@[simp] theorem mk_smul_bassSerreDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk s • bassSerreDart e p = bassSerreDart e (s.comp p) :=
  congrArg (Sigma.mk e) (pathCosetSmul_mk 𝔸 v₀ (𝔸.α e).range s p)

@[simp] theorem mk_smul_bassSerreArrowDart {a b : Γ.V} (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    π₁.mk s • bassSerreArrowDart p e = bassSerreArrowDart (s.comp p) e := by
  obtain ⟨e, rfl, rfl⟩ := e
  exact mk_smul_bassSerreDart s e p

/-- An element `p a p⁻¹` of `π₁.vertexHom p` fixes `bassSerreVertex p`. -/
@[simp] theorem vertexHom_smul_bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) : π₁.vertexHom p a • bassSerreVertex p = bassSerreVertex p := by
  rw [π₁.vertexHom_apply, mk_smul_bassSerreVertex]
  refine (bassSerreVertex_congr ?_).trans (bassSerreVertex_cons_vertex p a)
  rw [Quiver.Path.comp_assoc, Path.comp_ofVertex]
  simpa only [Quiver.Path.comp_nil] using
    (Path.Homotopic.reverse_comp p).comp_left (p.cons (.vertex a))

@[simp] theorem mk_smul_bassSerreBase (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    π₁.mk s • bassSerreBase 𝔸 v₀ = bassSerreVertex s := by
  simpa only [← bassSerreVertex_nil, Quiver.Path.comp_nil] using
    mk_smul_bassSerreVertex s Quiver.Path.nil

theorem vertexHom_nil_smul_bassSerreVertex {v : Γ.V} (a : 𝔸.vertexGroup v₀)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.vertexHom Quiver.Path.nil a • bassSerreVertex p =
      bassSerreVertex ((Path.ofVertex a).comp p) := by
  rw [π₁.vertexHom_nil_apply, mk_smul_bassSerreVertex]

theorem vertexHom_nil_smul_bassSerreBase (a : 𝔸.vertexGroup v₀) :
    π₁.vertexHom Quiver.Path.nil a • bassSerreBase 𝔸 v₀ = bassSerreBase 𝔸 v₀ :=
  vertexHom_smul_bassSerreVertex Quiver.Path.nil a

/-! ### Vertex and dart stabilizers -/

/-- An element of `π₁(𝔸, v₀)` fixes `p A_v` if and only if it lies in `p A_v p⁻¹`. -/
theorem mem_stabilizer_bassSerreVertex {v : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨v⟩} {g : π₁ 𝔸 v₀} :
    g ∈ stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p) ↔ g ∈ (π₁.vertexHom p).range := by
  rw [mem_stabilizer_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Subgroup.map_top (π₁.vertexHom p) ▸
      (pathCosetSmul_eq_self_iff 𝔸 v₀ ⊤ g p).mp (eq_of_heq (Sigma.mk.inj h).2)
  · exact congrArg (Sigma.mk v)
      ((pathCosetSmul_eq_self_iff 𝔸 v₀ ⊤ g p).mpr (by rwa [Subgroup.map_top]))

/-- The stabilizer of the vertex `p A_v` in `π₁(𝔸, v₀)` is `(π₁.vertexHom p).range`, i.e.,
`p A_v p⁻¹`. -/
@[simp] theorem stabilizer_bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p) = (π₁.vertexHom p).range := by
  ext g
  exact mem_stabilizer_bassSerreVertex

@[simp] theorem stabilizer_bassSerreBase :
    stabilizer (π₁ 𝔸 v₀) (bassSerreBase 𝔸 v₀) =
      (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range :=
  stabilizer_bassSerreVertex Quiver.Path.nil

/-- Every vertex stabilizer of `bassSerreTree 𝔸 v₀` is `(π₁.vertexHom p).range` for some `𝔸`-path
`p` from `v₀`. -/
theorem exists_stabilizer_bassSerreTree_vertex (x : (bassSerreTree 𝔸 v₀).V) :
    ∃ (v : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩),
      stabilizer (π₁ 𝔸 v₀) x = (π₁.vertexHom p).range :=
  bassSerreVertex_induction_on x fun p => ⟨_, p, stabilizer_bassSerreVertex p⟩

/-- The isomorphism `A_v ≃* stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p)` given by conjugation along
`p`. -/
noncomputable def stabilizerBassSerreVertexEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.vertexGroup v ≃* stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p) :=
  MulEquiv.ofBijective
    ((π₁.vertexHom p).codRestrict (stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p))
      fun a => mem_stabilizer_bassSerreVertex.mpr ⟨a, rfl⟩)
    ⟨fun _ _ h => π₁.vertexHom_injective p (Subtype.ext_iff.mp h),
      fun ⟨_, hg⟩ => let ⟨a, ha⟩ := mem_stabilizer_bassSerreVertex.mp hg; ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem stabilizerBassSerreVertexEquiv_apply_coe {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) :
    (stabilizerBassSerreVertexEquiv p a : π₁ 𝔸 v₀) = π₁.vertexHom p a :=
  (rfl)

@[simp] theorem stabilizerBassSerreVertexEquiv_symm_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) (h : π₁.vertexHom p a ∈ stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p)) :
    (stabilizerBassSerreVertexEquiv p).symm ⟨π₁.vertexHom p a, h⟩ = a :=
  (stabilizerBassSerreVertexEquiv p).symm_apply_eq.mpr (Subtype.ext rfl)

/-- Every conjugated vertex group `(π₁.vertexHom p).range` is elliptic in `bassSerreTree 𝔸 v₀`. -/
theorem bassSerreTree_isEllipticSubgroup_range_vertexHom {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreTree 𝔸 v₀).IsEllipticSubgroup (π₁.vertexHom p).range :=
  GTree.isEllipticSubgroup_iff.mpr ⟨bassSerreVertex p, (stabilizer_bassSerreVertex p).ge⟩

/-- An element of `π₁(𝔸, v₀)` fixes `p α_e(A_e)` if and only if it lies in `p α_e(A_e) p⁻¹`. -/
theorem mem_stabilizer_bassSerreDart {e : Γ.E} {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} {g : π₁ 𝔸 v₀} :
    g ∈ stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p) ↔
      g ∈ ((π₁.vertexHom p).comp (𝔸.α e)).range := by
  rw [mem_stabilizer_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact MonoidHom.range_comp (π₁.vertexHom p) (𝔸.α e) ▸
      (pathCosetSmul_eq_self_iff 𝔸 v₀ (𝔸.α e).range g p).mp (eq_of_heq (Sigma.mk.inj h).2)
  · exact congrArg (Sigma.mk e)
      ((pathCosetSmul_eq_self_iff 𝔸 v₀ (𝔸.α e).range g p).mpr
        (by rwa [← MonoidHom.range_comp]))

/-- The stabilizer of the dart `p α_e(A_e)` in `π₁(𝔸, v₀)` is
`((π₁.vertexHom p).comp (𝔸.α e)).range`, i.e., `p α_e(A_e) p⁻¹`. -/
@[simp] theorem stabilizer_bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p) = ((π₁.vertexHom p).comp (𝔸.α e)).range := by
  ext g
  exact mem_stabilizer_bassSerreDart

/-- The stabilizer of the dart `(p a) α_e(A_e)` joining `p A_{src e}` to `(p a e) A_{tgt e}` is
`p (a α_e(A_e) a⁻¹) p⁻¹`. -/
theorem stabilizer_bassSerreDart_cons_vertex (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (a : 𝔸.vertexGroup (Γ.src e)) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreDart e (p.cons (.vertex a))) =
      (((𝔸.α e).range).map (MulAut.conj a : 𝔸.vertexGroup (Γ.src e) →* _)).map
        (π₁.vertexHom p) := by
  rw [stabilizer_bassSerreDart, π₁.vertexHom_cons_vertex, MonoidHom.range_comp, Subgroup.map_map]

@[simp] theorem stabilizer_bassSerreArrowDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreArrowDart p e) =
      ((π₁.vertexHom p).comp (𝔸.αArrow e)).range := by
  obtain ⟨e, rfl, rfl⟩ := e
  rw [𝔸.αArrow_mk]
  exact stabilizer_bassSerreDart e p

/-- Every dart stabilizer of `bassSerreTree 𝔸 v₀` is `((π₁.vertexHom p).comp (𝔸.α e)).range` for
some dart `e` of `Γ` and some `𝔸`-path `p` from `v₀` to `Γ.src e`. -/
theorem exists_stabilizer_bassSerreTree_dart (d : (bassSerreTree 𝔸 v₀).E) :
    ∃ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩),
      stabilizer (π₁ 𝔸 v₀) d = ((π₁.vertexHom p).comp (𝔸.α e)).range :=
  bassSerreDart_induction_on d fun e p => ⟨e, p, stabilizer_bassSerreDart e p⟩

/-- The isomorphism `A_e ≃* stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p)` given by `α_e` followed by
conjugation along `p`. -/
noncomputable def stabilizerBassSerreDartEquiv (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.edgeGroup (Γ.toGeomEdge e) ≃* stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p) :=
  MulEquiv.ofBijective
    (((π₁.vertexHom p).comp (𝔸.α e)).codRestrict (stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p))
      fun c => mem_stabilizer_bassSerreDart.mpr ⟨c, rfl⟩)
    ⟨fun _ _ h => ((π₁.vertexHom_injective p).comp (𝔸.α_injective e)) (Subtype.ext_iff.mp h),
      fun ⟨_, hg⟩ => let ⟨c, hc⟩ := mem_stabilizer_bassSerreDart.mp hg; ⟨c, Subtype.ext hc⟩⟩

@[simp] theorem stabilizerBassSerreDartEquiv_apply_coe (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    (stabilizerBassSerreDartEquiv e p c : π₁ 𝔸 v₀) = π₁.vertexHom p (𝔸.α e c) :=
  (rfl)

@[simp] theorem stabilizerBassSerreDartEquiv_symm_apply (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e))
    (h : π₁.vertexHom p (𝔸.α e c) ∈ stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p)) :
    (stabilizerBassSerreDartEquiv e p).symm ⟨π₁.vertexHom p (𝔸.α e c), h⟩ = c :=
  (stabilizerBassSerreDartEquiv e p).symm_apply_eq.mpr (Subtype.ext rfl)

/-- When all vertex groups of `𝔸` are trivial, `π₁(𝔸, v₀)` acts freely on the vertices of
`bassSerreTree 𝔸 v₀` (the universal cover of `Γ.component v₀`). -/
theorem stabilizer_bassSerreTree_vertex_eq_bot [∀ v, Subsingleton (𝔸.vertexGroup v)]
    (x : (bassSerreTree 𝔸 v₀).V) : stabilizer (π₁ 𝔸 v₀) x = ⊥ := by
  obtain ⟨_, p, h⟩ := exists_stabilizer_bassSerreTree_vertex x
  exact h.trans (MonoidHom.range_eq_bot_iff.mpr (Subsingleton.elim _ 1))

/-- When all vertex groups of `𝔸` are trivial, `π₁(𝔸, v₀)` acts freely on the darts of
`bassSerreTree 𝔸 v₀`. -/
theorem stabilizer_bassSerreTree_dart_eq_bot [∀ v, Subsingleton (𝔸.vertexGroup v)]
    (d : (bassSerreTree 𝔸 v₀).E) : stabilizer (π₁ 𝔸 v₀) d = ⊥ :=
  eq_bot_iff.mpr ((bassSerreTree 𝔸 v₀).stabilizer_dart_le_stabilizer_src d |>.trans_eq
    (stabilizer_bassSerreTree_vertex_eq_bot _))

/-! ### Stars and neighbors in the Bass–Serre tree -/

/-- The dart of `bassSerreTree 𝔸 v₀` issuing from `p A_v` associated to a dart `e` of `Γ` with
`src e = v` and a left coset `a α_e(A_e)` in `A_v`. -/
def bassSerreStarOfCoset {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v},
      𝔸.vertexGroup v ⧸ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range) →
      {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = bassSerreVertex p}
  | ⟨e, q⟩ =>
    Quotient.lift
      (fun a : 𝔸.vertexGroup v =>
        ⟨bassSerreArrowDart (p.cons (.vertex a)) ⟨e.1, e.2, rfl⟩, by simp⟩)
      (fun a₁ a₂ hab => Subtype.ext <| by
        have hmem : a₁⁻¹ * a₂ ∈ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range :=
          QuotientGroup.leftRel_apply.mp hab
        have hmem' : a₂⁻¹ * a₁ ∈ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range := by
          simpa using Subgroup.inv_mem _ hmem
        refine bassSerreArrowDart_eq_iff.mpr ⟨a₂⁻¹ * a₁, hmem', ?_⟩
        have hmul := (Path.Homotopic.mul p a₂ (a₂⁻¹ * a₁)).symm
        rwa [mul_inv_cancel_left] at hmul)
      q

@[simp] theorem bassSerreStarOfCoset_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    (bassSerreStarOfCoset p ⟨e, (a : 𝔸.vertexGroup v ⧸ _)⟩).1 =
      bassSerreArrowDart (p.cons (.vertex a)) ⟨e.1, e.2, rfl⟩ :=
  (rfl)

/-- `bassSerreStarOfCoset p` is a bijection onto the outgoing darts at `bassSerreVertex p`. -/
theorem bassSerreStarOfCoset_bijective {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Function.Bijective (bassSerreStarOfCoset p) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨e₁, q₁⟩ ⟨e₂, q₂⟩ h
    induction q₁ using QuotientGroup.induction_on with | _ a₁ =>
    induction q₂ using QuotientGroup.induction_on with | _ a₂ =>
    have hd : bassSerreArrowDart (p.cons (.vertex a₁)) ⟨e₁.1, e₁.2, rfl⟩ =
        bassSerreArrowDart (p.cons (.vertex a₂)) ⟨e₂.1, e₂.2, rfl⟩ := congrArg Subtype.val h
    obtain rfl : e₁ = e₂ := Subtype.ext (eq_of_bassSerreArrowDart_eq hd)
    obtain ⟨c, hc, hhom⟩ := bassSerreArrowDart_eq_iff.mp hd
    have ha : a₁ = a₂ * c :=
      Path.cons_vertex_homotopic_cons_vertex_iff.mp (hhom.trans (Path.Homotopic.mul p a₂ c))
    refine congrArg
      (Sigma.mk (β := fun e : {e : Γ.E // Γ.src e = v} =>
        𝔸.vertexGroup v ⧸ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range) e₁)
      (QuotientGroup.eq.mpr ?_)
    have hinv : a₁⁻¹ * a₂ = c⁻¹ := by simp [ha]
    rw [hinv]
    exact Subgroup.inv_mem _ hc
  · rintro ⟨d, hd⟩
    obtain ⟨e, q, rfl⟩ := exists_eq_bassSerreDart d
    rw [src_bassSerreDart] at hd
    have he : Γ.src e = v := eq_of_bassSerreVertex_eq hd
    subst he
    obtain ⟨a, ha⟩ := bassSerreVertex_eq_iff.mp hd
    refine ⟨⟨⟨e, rfl⟩, (a : 𝔸.vertexGroup (Γ.src e) ⧸ _)⟩, Subtype.ext ?_⟩
    exact bassSerreArrowDart_congr ha.symm ⟨e, rfl, rfl⟩

/-- The star of `p A_v` in `bassSerreTree 𝔸 v₀` (the darts with source `p A_v`) is in bijection
with `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ α_e(A_e)`. -/
noncomputable def bassSerreStarEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = bassSerreVertex p} ≃
      Σ e : {e : Γ.E // Γ.src e = v},
        𝔸.vertexGroup v ⧸ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range :=
  (Equiv.ofBijective (bassSerreStarOfCoset p) (bassSerreStarOfCoset_bijective p)).symm

@[simp] theorem bassSerreStarEquiv_symm_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    ((bassSerreStarEquiv p).symm ⟨e, (a : 𝔸.vertexGroup v ⧸ _)⟩).1 =
      bassSerreArrowDart (p.cons (.vertex a)) ⟨e.1, e.2, rfl⟩ := by
  rw [bassSerreStarEquiv, Equiv.symm_symm, Equiv.ofBijective_apply, bassSerreStarOfCoset_mk]

@[simp] theorem bassSerreStarEquiv_apply_arrowDart {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v)
    (h : (bassSerreTree 𝔸 v₀).src (bassSerreArrowDart (p.cons (.vertex a)) ⟨e.1, e.2, rfl⟩) =
      bassSerreVertex p) :
    bassSerreStarEquiv p ⟨bassSerreArrowDart (p.cons (.vertex a)) ⟨e.1, e.2, rfl⟩, h⟩ =
      ⟨e, (a : 𝔸.vertexGroup v ⧸ _)⟩ :=
  (bassSerreStarEquiv p).eq_symm_apply.mp
    (Subtype.ext (bassSerreStarEquiv_symm_mk p e a).symm)

/-- Because `bassSerreTree 𝔸 v₀` has no parallel darts, the adjacent vertices of `p A_v` are in
bijection with its outgoing darts, hence with `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ α_e(A_e)`. -/
noncomputable def bassSerreNeighborEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {y : (bassSerreTree 𝔸 v₀).V // Nonempty (bassSerreVertex p ⟶ y)} ≃
      Σ e : {e : Γ.E // Γ.src e = v},
        𝔸.vertexGroup v ⧸ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range :=
  (Equiv.ofBijective
    (fun (d : {d : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src d = bassSerreVertex p}) =>
      (⟨(bassSerreTree 𝔸 v₀).tgt d.1, ⟨⟨d.1, d.2, rfl⟩⟩⟩ :
        {y : (bassSerreTree 𝔸 v₀).V // Nonempty (bassSerreVertex p ⟶ y)}))
    ⟨fun d₁ d₂ h => Subtype.ext <|
        (bassSerreTree 𝔸 v₀).isAcyclic.eq_of_src_eq_of_tgt_eq (d₁.2.trans d₂.2.symm)
          (congrArg Subtype.val h),
      fun ⟨_, ⟨f⟩⟩ => ⟨⟨f.1, f.2.1⟩, Subtype.ext f.2.2⟩⟩).symm.trans
    (bassSerreStarEquiv p)

@[simp] theorem bassSerreNeighborEquiv_symm_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    ((bassSerreNeighborEquiv p).symm ⟨e, (a : 𝔸.vertexGroup v ⧸ _)⟩).1 =
      bassSerreVertex ((p.cons (.vertex a)).cons (.dart ⟨e.1, e.2, rfl⟩)) := by
  rw [bassSerreNeighborEquiv, Equiv.symm_trans_apply, Equiv.symm_symm]
  change (bassSerreTree 𝔸 v₀).tgt ((bassSerreStarEquiv p).symm ⟨e, (a : 𝔸.vertexGroup v ⧸ _)⟩).1 = _
  rw [bassSerreStarEquiv_symm_mk, tgt_bassSerreArrowDart]

@[simp] theorem bassSerreNeighborEquiv_apply_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v)
    (h : Nonempty (bassSerreVertex p ⟶
      bassSerreVertex ((p.cons (.vertex a)).cons (.dart ⟨e.1, e.2, rfl⟩)))) :
    bassSerreNeighborEquiv p
      ⟨bassSerreVertex ((p.cons (.vertex a)).cons (.dart ⟨e.1, e.2, rfl⟩)), h⟩ =
      ⟨e, (a : 𝔸.vertexGroup v ⧸ _)⟩ :=
  (bassSerreNeighborEquiv p).eq_symm_apply.mp
    (Subtype.ext (bassSerreNeighborEquiv_symm_mk p e a).symm)

end BassSerreTree

end TauCeti.GraphOfGroups
