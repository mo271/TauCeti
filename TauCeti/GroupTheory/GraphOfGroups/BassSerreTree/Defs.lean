/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# Construction of the Bass–Serre tree of a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ` with base vertex `v₀ : Γ.V`. Following Serre
and Kapovich–Weidmann–Myasnikov, the Bass–Serre covering tree `X(𝔸, v₀)` is constructed from
`𝔸`-paths starting at `v₀`:

* Its vertices are equivalence classes `p A_v` of `𝔸`-paths `p` from `v₀` to `v`, where `p ≈ q`
  when `p` is homotopic to `q g` for some `g ∈ A_v`.
* Its darts are equivalence classes `p α_e(A_e)` of `𝔸`-paths `p` from `v₀` to `a` paired with an
  arrow `e : a ⟶ b` of `Γ`, where `(p, e) ≈ (q, e)` when `p` is homotopic to `q α_e(c)` for some
  `c ∈ A_e`. Such a dart starts at `p A_a`, reverses to `(p e, rev e)`, and ends at `(p e) A_b`;
  for `g ∈ A_a` the dart `(p g, e)` joins `p A_a` to `(p g e) A_b`.
* The fundamental group `π₁(𝔸, v₀)` acts on vertices and darts by left concatenation of closed
  `𝔸`-paths at `v₀`, without inversions because left concatenation preserves the underlying dart in
  `Γ.E` whereas reversal applies `Γ.rev`.

Every vertex is reached from the base vertex `1 · A_{v₀}` by induction on its representing
`𝔸`-path, and any nonempty reduced path in `X(𝔸, v₀)` spells a reduced alternating `𝔸`-path of
the same positive length, which cannot be homotopic to a vertex group letter by the normal form
theorem (`AlternatingPath.IsReduced.length_le_length_edgePath_of_homotopic`). Thus `X(𝔸, v₀)` is
a `π₁(𝔸, v₀)`-tree (`GraphOfGroups.bassSerreTree`, `GraphOfGroups.bassSerreTree_isTree`).

## Main definitions and results

* `TauCeti.GraphOfGroups.bassSerreTree`: the Bass–Serre tree `X(𝔸, v₀)` as a `GTree (π₁ 𝔸 v₀)`.
* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: the underlying Serre graph of `X(𝔸, v₀)` is a tree.
* `TauCeti.GraphOfGroups.bassSerreTree.mkVertex`, `TauCeti.GraphOfGroups.bassSerreTree.baseVertex`,
  `TauCeti.GraphOfGroups.bassSerreTree.mkDart`: constructors for vertices and darts of
  `bassSerreTree 𝔸 v₀`, together with induction, quotient descent, equality characterizations, and
  projection maps to `Γ` (`toGraphVertex`, `toGraphDart`, `toGraphHom`).

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

variable {Γ : SerreGraph.{u, v}}

/-! ### Quotient construction of vertices and darts -/

private structure RawVertex (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) : Type (max u v w) where
  vertex : Γ.V
  path : 𝔸.Path ⟨v₀⟩ ⟨vertex⟩

private def VertexRel {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} :
    RawVertex 𝔸 v₀ → RawVertex 𝔸 v₀ → Prop
  | ⟨v₁, p⟩, ⟨v₂, q⟩ =>
    ∃ h : v₁ = v₂, ∃ g : 𝔸.vertexGroup v₂,
      Path.Homotopic (h ▸ p) (q.cons (Letter.vertex g))

private theorem vertexRel_equivalence (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Equivalence (VertexRel (𝔸 := 𝔸) (v₀ := v₀)) where
  refl | ⟨_, p⟩ => ⟨rfl, 1, (Path.Homotopic.one p).symm⟩
  symm := by
    rintro ⟨v, p⟩ ⟨_, q⟩ ⟨rfl, g, hpq⟩
    refine ⟨rfl, g⁻¹, ?_⟩
    rw [← Letter.reverse_vertex]
    exact (Path.Homotopic.cons_cons_reverse q (.vertex g)).symm.trans (hpq.symm.cons _)
  trans := by
    rintro ⟨v, p⟩ ⟨_, q⟩ ⟨_, r⟩ ⟨rfl, g, hpq⟩ ⟨rfl, h, hqr⟩
    exact ⟨rfl, h * g, hpq.trans ((hqr.cons _).trans (Path.Homotopic.mul r h g))⟩

private instance vertexSetoid (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Setoid (RawVertex 𝔸 v₀) :=
  ⟨VertexRel, vertexRel_equivalence 𝔸 v₀⟩

private structure RawDart (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) : Type (max u v w) where
  srcV : Γ.V
  tgtV : Γ.V
  arrow : srcV ⟶ tgtV
  path : 𝔸.Path ⟨v₀⟩ ⟨srcV⟩

private def DartRel {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} :
    RawDart 𝔸 v₀ → RawDart 𝔸 v₀ → Prop
  | ⟨a₁, b₁, e₁, p₁⟩, ⟨a₂, b₂, e₂, p₂⟩ =>
    ∃ (ha : a₁ = a₂) (hb : b₁ = b₂),
      ha ▸ hb ▸ e₁ = e₂ ∧
        ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e₂.1),
          Path.Homotopic (ha ▸ p₁) (p₂.cons (Letter.vertex (𝔸.αArrow e₂ c)))

private theorem dartRel_equivalence (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Equivalence (DartRel (𝔸 := 𝔸) (v₀ := v₀)) where
  refl
    | ⟨_, _, _, p⟩ => ⟨rfl, rfl, rfl, 1, by simpa only [map_one] using (Path.Homotopic.one p).symm⟩
  symm := by
    rintro ⟨a, b, e, p⟩ ⟨_, _, _, q⟩ ⟨rfl, rfl, rfl, c, hpq⟩
    refine ⟨rfl, rfl, rfl, c⁻¹, ?_⟩
    rw [map_inv, ← Letter.reverse_vertex]
    exact (Path.Homotopic.cons_cons_reverse q (.vertex (𝔸.αArrow e c))).symm.trans (hpq.symm.cons _)
  trans := by
    rintro ⟨a, b, e, p⟩ ⟨_, _, _, q⟩ ⟨_, _, _, r⟩ ⟨rfl, rfl, rfl, c₁, hpq⟩ ⟨rfl, rfl, rfl, c₂, hqr⟩
    refine ⟨rfl, rfl, rfl, c₂ * c₁, ?_⟩
    rw [map_mul]
    exact hpq.trans ((hqr.cons _).trans (Path.Homotopic.mul r _ _))

private instance dartSetoid (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Setoid (RawDart 𝔸 v₀) :=
  ⟨DartRel, dartRel_equivalence 𝔸 v₀⟩

private abbrev BassSerreVertex (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Type (max u v w) :=
  Quotient (vertexSetoid 𝔸 v₀)

private abbrev BassSerreDart (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Type (max u v w) :=
  Quotient (dartSetoid 𝔸 v₀)

private def bassSerreSrcAux (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    BassSerreDart 𝔸 v₀ → BassSerreVertex 𝔸 v₀ :=
  Quotient.lift (fun x => Quotient.mk (vertexSetoid 𝔸 v₀) ⟨x.srcV, x.path⟩) <| by
    rintro ⟨a, b, e, p⟩ ⟨_, _, _, q⟩ ⟨rfl, rfl, rfl, c, hpq⟩
    exact Quotient.sound ⟨rfl, 𝔸.αArrow e c, hpq⟩

private def bassSerreRevAux (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    BassSerreDart 𝔸 v₀ → BassSerreDart 𝔸 v₀ :=
  Quotient.lift (fun x => Quotient.mk (dartSetoid 𝔸 v₀)
      ⟨x.tgtV, x.srcV, Quiver.reverse x.arrow, x.path.cons (Letter.dart x.arrow)⟩) <| by
    rintro ⟨a, b, e, p⟩ ⟨_, _, _, q⟩ ⟨rfl, rfl, rfl, c, hpq⟩
    obtain ⟨c', hα, -⟩ := 𝔸.exists_αArrow_reverse_eq_and_ωArrow_reverse_eq e c
    refine Quotient.sound ⟨rfl, rfl, rfl, c', ?_⟩
    rw [hα]
    exact (hpq.cons (Letter.dart e)).trans (Path.Homotopic.dart_ωArrow q e c).symm

private theorem bassSerreRevAux_rev (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)
    (d : BassSerreDart 𝔸 v₀) :
    bassSerreRevAux 𝔸 v₀ (bassSerreRevAux 𝔸 v₀ d) = d := by
  induction d using Quotient.ind with | _ x =>
  obtain ⟨a, b, e, p⟩ := x
  refine Quotient.sound ⟨rfl, rfl, Quiver.reverse_reverse e, 1, ?_⟩
  rw [map_one]
  exact (Path.Homotopic.dart_reverse p e).trans (Path.Homotopic.one p).symm

private def toGraphDartAux {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} :
    BassSerreDart 𝔸 v₀ → Γ.E :=
  Quotient.lift (fun x => x.arrow.1) <| by
    rintro ⟨a, b, e, p⟩ ⟨_, _, _, q⟩ ⟨rfl, rfl, rfl, _, _⟩
    rfl

private theorem bassSerreRevAux_ne (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)
    (d : BassSerreDart 𝔸 v₀) :
    bassSerreRevAux 𝔸 v₀ d ≠ d := by
  induction d using Quotient.ind with | _ x =>
  intro h
  have hd : (Quiver.reverse x.arrow).1 = x.arrow.1 := congrArg toGraphDartAux h
  exact Γ.rev_ne x.arrow.1 ((Γ.reverse_val x.arrow).symm.trans hd)

private def bassSerreGraph (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    SerreGraph.{max u v w, max u v w} where
  V := BassSerreVertex 𝔸 v₀
  E := BassSerreDart 𝔸 v₀
  src := bassSerreSrcAux 𝔸 v₀
  rev := bassSerreRevAux 𝔸 v₀
  rev_rev := bassSerreRevAux_rev 𝔸 v₀
  rev_ne := bassSerreRevAux_ne 𝔸 v₀

private def smulVertexRaw {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
    (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) : BassSerreVertex 𝔸 v₀ → BassSerreVertex 𝔸 v₀ :=
  Quotient.map (fun x => ⟨x.vertex, s.comp x.path⟩) <| by
    rintro ⟨v, p⟩ ⟨_, q⟩ ⟨rfl, g, hpq⟩
    exact ⟨rfl, g, hpq.comp_left s⟩

private def smulVertexAux {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} :
    π₁ 𝔸 v₀ → BassSerreVertex 𝔸 v₀ → BassSerreVertex 𝔸 v₀ :=
  π₁.lift smulVertexRaw <| by
    intro s₁ s₂ hs
    funext x
    induction x using Quotient.ind with | _ x =>
    exact Quotient.sound ⟨rfl, 1, (hs.comp (.refl x.path)).trans (Path.Homotopic.one _).symm⟩

private def smulDartRaw {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
    (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) : BassSerreDart 𝔸 v₀ → BassSerreDart 𝔸 v₀ :=
  Quotient.map (fun x => ⟨x.srcV, x.tgtV, x.arrow, s.comp x.path⟩) <| by
    rintro ⟨a, b, e, p⟩ ⟨_, _, _, q⟩ ⟨rfl, rfl, rfl, c, hpq⟩
    exact ⟨rfl, rfl, rfl, c, hpq.comp_left s⟩

private def smulDartAux {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} :
    π₁ 𝔸 v₀ → BassSerreDart 𝔸 v₀ → BassSerreDart 𝔸 v₀ :=
  π₁.lift smulDartRaw <| by
    intro s₁ s₂ hs
    funext d
    induction d using Quotient.ind with | _ x =>
    refine Quotient.sound ⟨rfl, rfl, rfl, 1, ?_⟩
    rw [map_one]
    exact (hs.comp (.refl x.path)).trans (Path.Homotopic.one _).symm

private theorem smulVertexAux_one {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
    (x : BassSerreVertex 𝔸 v₀) : smulVertexAux 1 x = x := by
  induction x using Quotient.ind with | _ x =>
  obtain ⟨v, p⟩ := x
  rw [← π₁.mk_nil, smulVertexAux, π₁.lift_mk]
  exact Quotient.sound ⟨rfl, 1, by simpa using (Path.Homotopic.one p).symm⟩

private theorem smulVertexAux_mul {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
    (g₁ g₂ : π₁ 𝔸 v₀) (x : BassSerreVertex 𝔸 v₀) :
    smulVertexAux (g₁ * g₂) x = smulVertexAux g₁ (smulVertexAux g₂ x) := by
  induction g₁ using π₁.induction_on with | _ s₁ =>
  induction g₂ using π₁.induction_on with | _ s₂ =>
  induction x using Quotient.ind with | _ x =>
  obtain ⟨v, p⟩ := x
  rw [← π₁.mk_comp, smulVertexAux, π₁.lift_mk, π₁.lift_mk, π₁.lift_mk]
  exact Quotient.sound ⟨rfl, 1, by
    simpa [Quiver.Path.comp_assoc] using (Path.Homotopic.one (s₁.comp (s₂.comp p))).symm⟩

private theorem smulDartAux_one {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
    (d : BassSerreDart 𝔸 v₀) : smulDartAux 1 d = d := by
  induction d using Quotient.ind with | _ x =>
  obtain ⟨a, b, e, p⟩ := x
  rw [← π₁.mk_nil, smulDartAux, π₁.lift_mk]
  refine Quotient.sound ⟨rfl, rfl, rfl, 1, ?_⟩
  rw [map_one]
  simpa using (Path.Homotopic.one p).symm

private theorem smulDartAux_mul {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
    (g₁ g₂ : π₁ 𝔸 v₀) (d : BassSerreDart 𝔸 v₀) :
    smulDartAux (g₁ * g₂) d = smulDartAux g₁ (smulDartAux g₂ d) := by
  induction g₁ using π₁.induction_on with | _ s₁ =>
  induction g₂ using π₁.induction_on with | _ s₂ =>
  induction d using Quotient.ind with | _ x =>
  obtain ⟨a, b, e, p⟩ := x
  rw [← π₁.mk_comp, smulDartAux, π₁.lift_mk, π₁.lift_mk, π₁.lift_mk]
  refine Quotient.sound ⟨rfl, rfl, rfl, 1, ?_⟩
  rw [map_one]
  simpa [Quiver.Path.comp_assoc] using (Path.Homotopic.one (s₁.comp (s₂.comp p))).symm

private def bassSerreAut (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    π₁ 𝔸 v₀ →* (bassSerreGraph 𝔸 v₀).Aut where
  toFun g :=
    { equivV :=
        { toFun := smulVertexAux g
          invFun := smulVertexAux g⁻¹
          left_inv := fun x => by
            dsimp only [bassSerreGraph] at x
            rw [← smulVertexAux_mul, inv_mul_cancel, smulVertexAux_one]
          right_inv := fun x => by
            dsimp only [bassSerreGraph] at x
            rw [← smulVertexAux_mul, mul_inv_cancel, smulVertexAux_one] }
      equivE :=
        { toFun := smulDartAux g
          invFun := smulDartAux g⁻¹
          left_inv := fun d => by
            dsimp only [bassSerreGraph] at d
            rw [← smulDartAux_mul, inv_mul_cancel, smulDartAux_one]
          right_inv := fun d => by
            dsimp only [bassSerreGraph] at d
            rw [← smulDartAux_mul, mul_inv_cancel, smulDartAux_one] }
      map_src := fun d => by
        induction g using π₁.induction_on with | _ s =>
        induction d using Quotient.ind with | _ x =>
        simp only [bassSerreGraph, smulVertexAux, smulDartAux, π₁.lift_mk]
        rfl
      map_rev := fun d => by
        induction g using π₁.induction_on with | _ s =>
        induction d using Quotient.ind with | _ x =>
        simp only [bassSerreGraph, smulDartAux, π₁.lift_mk]
        rfl }
  map_one' := by
    ext x
    · exact smulVertexAux_one x
    · exact smulDartAux_one x
  map_mul' g₁ g₂ := by
    ext x
    · exact smulVertexAux_mul g₁ g₂ x
    · exact smulDartAux_mul g₁ g₂ x

private theorem bassSerreAut_smul_ne_rev (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)
    (g : π₁ 𝔸 v₀) (d : (bassSerreGraph 𝔸 v₀).E) :
    (bassSerreAut 𝔸 v₀ g).equivE d ≠ (bassSerreGraph 𝔸 v₀).rev d := by
  induction g using π₁.induction_on with | _ s =>
  induction d using Quotient.ind with | _ x =>
  intro h
  have hlhs : (bassSerreAut 𝔸 v₀ (π₁.mk s)).equivE (Quotient.mk (dartSetoid 𝔸 v₀) x) =
      smulDartRaw s (Quotient.mk (dartSetoid 𝔸 v₀) x) :=
    congrFun (π₁.lift_mk _ _ s) _
  have hd : x.arrow.1 = (Quiver.reverse x.arrow).1 :=
    congrArg toGraphDartAux (hlhs.symm.trans h)
  exact (Γ.rev_ne x.arrow.1).symm (hd.trans (Γ.reverse_val x.arrow))

/-! ### Connectedness and acyclicity of `bassSerreGraph` -/

private theorem bassSerreGraph_connected (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    (bassSerreGraph 𝔸 v₀).Connected := by
  let x₀ : (bassSerreGraph 𝔸 v₀).V := Quotient.mk (vertexSetoid 𝔸 v₀) ⟨v₀, .nil⟩
  refine (bassSerreGraph 𝔸 v₀).connected_iff.mpr
    ⟨⟨x₀⟩, (bassSerreGraph 𝔸 v₀).preconnected_of_forall_nonempty_path x₀ fun y => ?_⟩
  induction y using Quotient.ind with | _ y =>
  obtain ⟨v, p⟩ := y
  have key : ∀ {b : 𝔸.LetterVertex} (q : 𝔸.Path ⟨v₀⟩ b),
      Nonempty ((bassSerreGraph 𝔸 v₀).Path x₀
        (Quotient.mk (vertexSetoid 𝔸 v₀) ⟨b.as, q⟩)) := by
    intro b q
    induction q with
    | nil => exact ⟨.nil⟩
    | cons q l ih =>
      obtain ⟨P⟩ := ih
      cases l with
      | vertex g =>
        have heq : (Quotient.mk (vertexSetoid 𝔸 v₀) ⟨_, q.cons (.vertex g)⟩ :
            (bassSerreGraph 𝔸 v₀).V) = Quotient.mk (vertexSetoid 𝔸 v₀) ⟨_, q⟩ :=
          Quotient.sound ⟨rfl, g, .refl _⟩
        exact ⟨heq ▸ P⟩
      | dart e =>
        let d : (bassSerreGraph 𝔸 v₀).E := Quotient.mk (dartSetoid 𝔸 v₀) ⟨_, _, e, q⟩
        exact ⟨P.cons ⟨d, rfl, rfl⟩⟩
  exact key p

/-- If a transition `g` between two consecutive darts `(p_prev, e₀)` and `(pf, e)` cancels in an
alternating path, then the second dart in `bassSerreGraph 𝔸 v₀` is the reverse of the first. -/
private theorem dart_eq_rev_of_cancels {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ a c₀ c d : Γ.V}
    {r₀ : 𝔸.AlternatingPath a c₀} {e₀ : c₀ ⟶ c} {e : c ⟶ d} {g : 𝔸.vertexGroup c}
    {p_prev pf : 𝔸.Path ⟨v₀⟩ ⟨c⟩}
    (hg : Path.Homotopic pf (p_prev.cons (.vertex g)))
    (hcanc : AlternatingPath.Cancels (AlternatingPath.cons r₀ e₀ g) e) :
    (Quotient.mk (dartSetoid 𝔸 v₀) ⟨c, d, e, pf⟩ : (bassSerreGraph 𝔸 v₀).E) =
      Quotient.mk (dartSetoid 𝔸 v₀) ⟨c, c₀, Quiver.reverse e₀, p_prev⟩ := by
  obtain ⟨hrev, c_edge, hc_edge⟩ := (AlternatingPath.cancels_cons_iff r₀ e₀ g e).mp hcanc
  have hrev' : e.1 = Γ.rev e₀.1 := by rw [hrev, Γ.rev_rev]
  obtain rfl : c₀ = d := Γ.src_eq_tgt_of_val_eq_rev hrev
  have he_eq : Quiver.reverse e₀ = e := Subtype.ext ((Γ.reverse_val e₀).trans hrev'.symm)
  subst he_eq
  exact Quotient.sound ⟨rfl, rfl, rfl, c_edge, hc_edge ▸ hg⟩

/-- Every nonempty reduced path in `bassSerreGraph 𝔸 v₀` starting at `[p₀]` spells a reduced
alternating `𝔸`-path ending with the final dart whose concatenation with `p₀` tracks that dart. -/
private theorem exists_reduced_alternatingPath_of_path {𝔸 : GraphOfGroups.{u, v, w, x} Γ}
    {v₀ a : Γ.V} (p₀ : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    ∀ {z y : (bassSerreGraph 𝔸 v₀).V} (P : (bassSerreGraph 𝔸 v₀).Path
        (Quotient.mk (vertexSetoid 𝔸 v₀) ⟨a, p₀⟩) z)
      (f : z ⟶ y),
      SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) (P.cons f) →
      ∀ {c d : Γ.V} (e : c ⟶ d) (pf : 𝔸.Path ⟨v₀⟩ ⟨c⟩),
        f.1 = Quotient.mk (dartSetoid 𝔸 v₀) ⟨c, d, e, pf⟩ →
        ∃ r : 𝔸.AlternatingPath a c,
          (AlternatingPath.cons r e 1).IsReduced ∧
          Path.Homotopic (p₀.comp (AlternatingPath.cons r e 1).toPath) (pf.cons (Letter.dart e))
  | _, _, .nil, f, _, c, d, e, pf, hf => by
    have hsrc : Quotient.mk (vertexSetoid 𝔸 v₀) ⟨c, pf⟩ =
        Quotient.mk (vertexSetoid 𝔸 v₀) ⟨a, p₀⟩ := by
      have h₁ := f.2.1; rw [hf] at h₁; exact h₁
    obtain ⟨rfl, g₀, hg₀⟩ := Quotient.exact hsrc
    refine ⟨.single g₀, by simp, ?_⟩
    simp only [AlternatingPath.toPath_cons, AlternatingPath.toPath_single,
      Quiver.Path.comp_cons, Path.comp_ofVertex]
    exact (Path.Homotopic.one _).trans (hg₀.symm.cons (Letter.dart e))
  | _, _, .cons Q f₀, f, hred, c, d, e, pf, hf => by
    obtain ⟨hQ, hne⟩ :=
      (SerreGraph.Path.isReduced_cons_cons (bassSerreGraph 𝔸 v₀) Q f₀ f).mp hred
    obtain ⟨⟨c₀, c₁, e₀, p_prev⟩, hf₀⟩ := Quotient.exists_rep f₀.1
    obtain ⟨r₀, hr₀, hhom₀⟩ :=
      exists_reduced_alternatingPath_of_path p₀ Q f₀ hQ e₀ p_prev hf₀.symm
    have hlink : Quotient.mk (vertexSetoid 𝔸 v₀) ⟨c, pf⟩ =
        Quotient.mk (vertexSetoid 𝔸 v₀) ⟨c₁, p_prev.cons (Letter.dart e₀)⟩ := by
      have h₁ := f.2.1.trans f₀.2.2.symm; rw [hf, ← hf₀] at h₁; exact h₁
    obtain ⟨rfl, g, hg⟩ := Quotient.exact hlink
    refine ⟨AlternatingPath.cons r₀ e₀ g, ?_, ?_⟩
    · rw [AlternatingPath.isReduced_cons_iff]
      refine ⟨by simpa using hr₀, fun hcanc => hne ?_⟩
      rw [hf, ← hf₀]
      exact dart_eq_rev_of_cancels hg hcanc
    · simp only [AlternatingPath.toPath_cons, Quiver.Path.comp_cons]
      have hhom₀' :
          Path.Homotopic (((p₀.comp r₀.toPath).cons (.dart e₀)).cons (.vertex 1))
            (p_prev.cons (.dart e₀)) := by
        simpa only [AlternatingPath.toPath_cons, Quiver.Path.comp_cons] using hhom₀
      refine (Path.Homotopic.one _).trans (Path.Homotopic.cons ?_ (Letter.dart e))
      exact (((Path.Homotopic.one _).cons (.vertex g)).symm.trans
        (hhom₀'.cons (.vertex g))).trans hg.symm

private theorem bassSerreGraph_isAcyclic (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    (bassSerreGraph 𝔸 v₀).IsAcyclic := by
  rw [(bassSerreGraph 𝔸 v₀).isAcyclic_iff]
  intro u P hP
  cases P with
  | nil => rfl
  | cons Q f =>
    obtain ⟨⟨a, p₀⟩, rfl⟩ := Quotient.exists_rep u
    obtain ⟨⟨c, d, e, pf⟩, hf⟩ := Quotient.exists_rep f.1
    obtain ⟨r, hr, hhom⟩ :=
      exists_reduced_alternatingPath_of_path p₀ Q f hP e pf hf.symm
    have htgt : Quotient.mk (vertexSetoid 𝔸 v₀) ⟨d, pf.cons (.dart e)⟩ =
        Quotient.mk (vertexSetoid 𝔸 v₀) ⟨a, p₀⟩ := by
      have h₁ := f.2.2; rw [← hf] at h₁; exact h₁
    obtain ⟨rfl, g, hg⟩ := Quotient.exact htgt
    have hclosed : Path.Homotopic (AlternatingPath.cons r e 1).toPath (Path.ofVertex g) := by
      have h₁ := (hhom.trans hg).comp_left p₀.reverse
      have h₂ : Path.Homotopic (p₀.reverse.comp (p₀.comp (AlternatingPath.cons r e 1).toPath))
          (AlternatingPath.cons r e 1).toPath := by
        simpa only [Quiver.Path.nil_comp] using
          Path.Homotopic.comp_reverse_comp_comp .nil p₀ (AlternatingPath.cons r e 1).toPath
      have h₃ : Path.Homotopic (p₀.reverse.comp (p₀.cons (.vertex g))) (Path.ofVertex g) := by
        rw [← Path.comp_ofVertex]
        simpa only [Quiver.Path.nil_comp] using
          Path.Homotopic.comp_reverse_comp_comp .nil p₀ (Path.ofVertex g)
      exact h₂.symm.trans (h₁.trans h₃)
    have hle := hr.length_le_length_edgePath_of_homotopic hclosed
    simp at hle

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`, as a
`π₁(𝔸, v₀)`-tree. -/
def bassSerreTree (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := bassSerreGraph 𝔸 v₀
  isTree := (bassSerreGraph 𝔸 v₀).isTree_iff.mpr
    ⟨bassSerreGraph_connected 𝔸 v₀, bassSerreGraph_isAcyclic 𝔸 v₀⟩
  action := bassSerreAut 𝔸 v₀
  action_smul_ne_rev := bassSerreAut_smul_ne_rev 𝔸 v₀

/-- The Bass–Serre covering graph `X(𝔸, v₀)` is a tree. -/
theorem bassSerreTree_isTree (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    (bassSerreTree 𝔸 v₀).toSerreGraph.IsTree :=
  (bassSerreTree 𝔸 v₀).isTree

/-! ### Public constructors, eliminators, and action equations -/

namespace bassSerreTree

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- The vertex `p A_v` of `bassSerreTree 𝔸 v₀` represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def mkVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (bassSerreTree 𝔸 v₀).V :=
  Quotient.mk (vertexSetoid 𝔸 v₀) ⟨v, p⟩

variable (𝔸 v₀) in
/-- The distinguished base vertex `1 · A_{v₀}` of `bassSerreTree 𝔸 v₀`. -/
def baseVertex : (bassSerreTree 𝔸 v₀).V :=
  mkVertex (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)

variable (𝔸 v₀) in
theorem baseVertex_def : baseVertex 𝔸 v₀ = mkVertex (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :=
  (rfl)

/-- The dart `(p, e)` of `bassSerreTree 𝔸 v₀` represented by an `𝔸`-path `p` from `v₀` to `a` and
an arrow `e : a ⟶ b` of `Γ`. -/
def mkDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) : (bassSerreTree 𝔸 v₀).E :=
  Quotient.mk (dartSetoid 𝔸 v₀) ⟨a, b, e, p⟩

/-- Prove a property of vertices of `bassSerreTree 𝔸 v₀` by checking it on based `𝔸`-paths. -/
@[elab_as_elim] theorem vertex_induction_on {P : (bassSerreTree 𝔸 v₀).V → Prop}
    (x : (bassSerreTree 𝔸 v₀).V)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (mkVertex p)) : P x :=
  Quotient.ind (fun y => h y.path) x

/-- Prove a property of darts of `bassSerreTree 𝔸 v₀` by checking it on pairs `(p, e)`. -/
@[elab_as_elim] theorem dart_induction_on {P : (bassSerreTree 𝔸 v₀).E → Prop}
    (d : (bassSerreTree 𝔸 v₀).E)
    (h : ∀ {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b), P (mkDart p e)) : P d :=
  Quotient.ind (fun y => h y.path y.arrow) d

/-- Descend a function on based `𝔸`-paths that is invariant under homotopy and right
multiplication by vertex group elements to the vertices of `bassSerreTree 𝔸 v₀`. -/
def liftVertex {β : Sort*} (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (hf : ∀ {v : Γ.V} (p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v),
      Path.Homotopic p (q.cons (Letter.vertex g)) → f p = f q) :
    (bassSerreTree 𝔸 v₀).V → β :=
  Quotient.lift (fun x => f x.path) <| by
    rintro ⟨v, p⟩ ⟨_, q⟩ ⟨rfl, g, hpq⟩
    exact hf p q g hpq

@[simp] theorem liftVertex_mkVertex {β : Sort*} (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (hf : ∀ {v : Γ.V} (p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v),
      Path.Homotopic p (q.cons (Letter.vertex g)) → f p = f q)
    {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    liftVertex f hf (mkVertex p) = f p :=
  (rfl)

/-- Descend a function on `(p, e)` that is invariant under homotopy and right multiplication by
`α_e(A_e)` to the darts of `bassSerreTree 𝔸 v₀`. -/
def liftDart {β : Sort*} (f : ∀ {a b : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨a⟩ → (a ⟶ b) → β)
    (hf : ∀ {a b : Γ.V} (p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b)
      (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)),
      Path.Homotopic p (q.cons (Letter.vertex (𝔸.αArrow e c))) → f p e = f q e) :
    (bassSerreTree 𝔸 v₀).E → β :=
  Quotient.lift (fun x => f x.path x.arrow) <| by
    rintro ⟨a, b, e, p⟩ ⟨_, _, _, q⟩ ⟨rfl, rfl, rfl, c, hpq⟩
    exact hf p q e c hpq

@[simp] theorem liftDart_mkDart {β : Sort*}
    (f : ∀ {a b : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨a⟩ → (a ⟶ b) → β)
    (hf : ∀ {a b : Γ.V} (p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b)
      (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)),
      Path.Homotopic p (q.cons (Letter.vertex (𝔸.αArrow e c))) → f p e = f q e)
    {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    liftDart f hf (mkDart p e) = f p e :=
  (rfl)

/-- The vertex of `Γ` underlying a vertex of `bassSerreTree 𝔸 v₀`. -/
def toGraphVertex : (bassSerreTree 𝔸 v₀).V → Γ.V :=
  liftVertex (fun {v} _ => v) fun _ _ _ _ => rfl

@[simp] theorem toGraphVertex_mkVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    toGraphVertex (mkVertex p) = v :=
  (rfl)

@[simp] theorem toGraphVertex_baseVertex : toGraphVertex (baseVertex 𝔸 v₀) = v₀ :=
  (rfl)

theorem eq_of_mkVertex_eq {u v : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨u⟩} {q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}
    (h : mkVertex p = mkVertex q) : u = v :=
  congrArg toGraphVertex h

/-- Every vertex `x` of `bassSerreTree 𝔸 v₀` is represented by some `𝔸`-path from `v₀` to
`toGraphVertex x`. -/
theorem exists_mkVertex (x : (bassSerreTree 𝔸 v₀).V) :
    ∃ p : 𝔸.Path ⟨v₀⟩ ⟨toGraphVertex x⟩, mkVertex p = x := by
  induction x using vertex_induction_on with | _ p =>
  exact ⟨p, rfl⟩

/-- Every vertex `x` projecting to `v : Γ.V` is represented by an `𝔸`-path from `v₀` to `v`. -/
theorem exists_mkVertex_of_toGraphVertex_eq {v : Γ.V} {x : (bassSerreTree 𝔸 v₀).V}
    (hv : toGraphVertex x = v) : ∃ p : 𝔸.Path ⟨v₀⟩ ⟨v⟩, mkVertex p = x := by
  subst hv
  exact exists_mkVertex x

/-- The dart of `Γ` underlying a dart of `bassSerreTree 𝔸 v₀`. -/
def toGraphDart : (bassSerreTree 𝔸 v₀).E → Γ.E :=
  liftDart (fun _ e => e.1) fun _ _ _ _ _ => rfl

@[simp] theorem toGraphDart_mkDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    toGraphDart (mkDart p e) = e.1 :=
  (rfl)

theorem eq_of_mkDart_eq {a₁ b₁ a₂ b₂ : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨a₁⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨a₂⟩} {e₁ : a₁ ⟶ b₁} {e₂ : a₂ ⟶ b₂}
    (h : mkDart p e₁ = mkDart q e₂) : e₁.1 = e₂.1 :=
  congrArg toGraphDart h

/-- Two `𝔸`-paths with the same endpoint `v` define the same vertex of `bassSerreTree 𝔸 v₀` if and
only if they differ on the right by an element of `A_v` up to homotopy. -/
theorem mkVertex_eq_mkVertex_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    mkVertex p = mkVertex q ↔
      ∃ g : 𝔸.vertexGroup v, Path.Homotopic p (q.cons (Letter.vertex g)) := by
  refine Quotient.eq.trans ⟨fun ⟨h, g, hpq⟩ => ?_, fun ⟨g, hpq⟩ => ⟨rfl, g, hpq⟩⟩
  rw [Subsingleton.elim h rfl] at hpq
  exact ⟨g, hpq⟩

theorem mkVertex_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : Path.Homotopic p q) :
    mkVertex p = mkVertex q :=
  mkVertex_eq_mkVertex_iff.mpr ⟨1, h.trans (Path.Homotopic.one q).symm⟩

@[simp] theorem mkVertex_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v) :
    mkVertex (p.cons (Letter.vertex g)) = mkVertex p :=
  mkVertex_eq_mkVertex_iff.mpr ⟨g, .refl _⟩

@[simp] theorem mkVertex_ofVertex (g : 𝔸.vertexGroup v₀) :
    mkVertex (Path.ofVertex g) = baseVertex 𝔸 v₀ := by
  rw [← Quiver.Path.nil_comp (Path.ofVertex g), Path.comp_ofVertex, mkVertex_cons_vertex]
  rfl

/-- Two `𝔸`-paths paired with the same arrow `e : a ⟶ b` define the same dart of
`bassSerreTree 𝔸 v₀` if and only if they differ on the right by an element of `α_e(A_e)` up to
homotopy. -/
theorem mkDart_eq_mkDart_iff {a b : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} {e : a ⟶ b} :
    mkDart p e = mkDart q e ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e.1),
        Path.Homotopic p (q.cons (Letter.vertex (𝔸.αArrow e c))) := by
  refine Quotient.eq.trans
    ⟨fun ⟨ha, _, _, c, hpq⟩ => ?_, fun ⟨c, hpq⟩ => ⟨rfl, rfl, rfl, c, hpq⟩⟩
  rw [Subsingleton.elim ha rfl] at hpq
  exact ⟨c, hpq⟩

theorem mkDart_congr {a b : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩}
    (h : Path.Homotopic p q) (e : a ⟶ b) :
    mkDart p e = mkDart q e :=
  mkDart_eq_mkDart_iff.mpr ⟨1, by rw [map_one]; exact h.trans (Path.Homotopic.one q).symm⟩

@[simp] theorem mkDart_cons_αArrow {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    mkDart (p.cons (Letter.vertex (𝔸.αArrow e c))) e = mkDart p e :=
  mkDart_eq_mkDart_iff.mpr ⟨c, .refl _⟩

@[simp] theorem src_mkDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreTree 𝔸 v₀).src (mkDart p e) = mkVertex p :=
  (rfl)

@[simp] theorem rev_mkDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreTree 𝔸 v₀).rev (mkDart p e) = mkDart (p.cons (Letter.dart e)) (Quiver.reverse e) :=
  (rfl)

@[simp] theorem tgt_mkDart {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (e : a ⟶ b) :
    (bassSerreTree 𝔸 v₀).tgt (mkDart p e) = mkVertex (p.cons (Letter.dart e)) :=
  (rfl)

@[simp] theorem mk_smul_mkVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • mkVertex p = mkVertex (s.comp p) := by
  rw [GTree.smul_vertex_def, SerreGraph.Aut.smul_vertex_def]
  exact congrFun (π₁.lift_mk _ _ s) (mkVertex p)

@[simp] theorem mk_smul_baseVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    π₁.mk s • baseVertex 𝔸 v₀ = mkVertex s := by
  simp [baseVertex]

@[simp] theorem mk_smul_mkDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {a b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (e : a ⟶ b) :
    π₁.mk s • mkDart p e = mkDart (s.comp p) e := by
  rw [GTree.smul_dart_def, SerreGraph.Aut.smul_dart_def]
  exact congrFun (π₁.lift_mk _ _ s) (mkDart p e)

@[simp] theorem toGraphVertex_smul (g : π₁ 𝔸 v₀) (x : (bassSerreTree 𝔸 v₀).V) :
    toGraphVertex (g • x) = toGraphVertex x := by
  induction g using π₁.induction_on with | _ s =>
  induction x using vertex_induction_on with | _ p =>
  rw [mk_smul_mkVertex, toGraphVertex_mkVertex, toGraphVertex_mkVertex]

@[simp] theorem toGraphDart_smul (g : π₁ 𝔸 v₀) (d : (bassSerreTree 𝔸 v₀).E) :
    toGraphDart (g • d) = toGraphDart d := by
  induction g using π₁.induction_on with | _ s =>
  induction d using dart_induction_on with | _ p e =>
  rw [mk_smul_mkDart, toGraphDart_mkDart, toGraphDart_mkDart]

@[simp] theorem toGraphVertex_src (d : (bassSerreTree 𝔸 v₀).E) :
    toGraphVertex ((bassSerreTree 𝔸 v₀).src d) = Γ.src (toGraphDart d) := by
  induction d using dart_induction_on with | _ _ e =>
  exact e.2.1.symm

@[simp] theorem toGraphDart_rev (d : (bassSerreTree 𝔸 v₀).E) :
    toGraphDart ((bassSerreTree 𝔸 v₀).rev d) = Γ.rev (toGraphDart d) := by
  induction d using dart_induction_on with | _ _ e =>
  exact Γ.reverse_val e

@[simp] theorem toGraphVertex_tgt (d : (bassSerreTree 𝔸 v₀).E) :
    toGraphVertex ((bassSerreTree 𝔸 v₀).tgt d) = Γ.tgt (toGraphDart d) := by
  induction d using dart_induction_on with | _ _ e =>
  exact e.2.2.symm

variable (𝔸 v₀) in
/-- The natural projection morphism from `bassSerreTree 𝔸 v₀` to the underlying Serre graph `Γ`. -/
def toGraphHom : (bassSerreTree 𝔸 v₀).toSerreGraph.Hom Γ where
  mapV := toGraphVertex
  mapE := toGraphDart
  map_src d := (toGraphVertex_src d).symm
  map_rev := toGraphDart_rev

@[simp] theorem toGraphHom_mapV : (toGraphHom 𝔸 v₀).mapV = toGraphVertex :=
  (rfl)

@[simp] theorem toGraphHom_mapE : (toGraphHom 𝔸 v₀).mapE = toGraphDart :=
  (rfl)

@[simp] theorem toGraphHom_comp_action (g : π₁ 𝔸 v₀) :
    SerreGraph.Hom.comp (toGraphHom 𝔸 v₀) ((bassSerreTree 𝔸 v₀).action g).toHom =
      toGraphHom 𝔸 v₀ := by
  ext x
  · simp [← SerreGraph.Aut.smul_vertex_def, ← GTree.smul_vertex_def]
  · simp [← SerreGraph.Aut.smul_dart_def, ← GTree.smul_dart_def]

end bassSerreTree

end TauCeti.GraphOfGroups
