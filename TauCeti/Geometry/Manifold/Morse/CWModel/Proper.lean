/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel
import Mathlib.Order.SuccPred.IntervalSucc
import TauCeti.Geometry.Manifold.Morse.Deformation.Cofibration
import TauCeti.Geometry.Manifold.Morse.Exhaustion
import TauCeti.Logic.Equiv.Sum
import TauCeti.Topology.Category.TopCat.Normal
import TauCeti.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.CWComplex.Classical.SequentialColimit
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Topology.Homotopy.Extension.Tower

/-!
# The CW model of a proper Morse function

Let `f` be a Morse function on a boundaryless manifold `M`, proper and bounded below. Then `M` is
homotopy equivalent to a Hausdorff CW complex with one `λ`-cell for each critical point of `f` of
index `λ` (`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`). When `f` has infinitely many
critical points of some index, the model has infinitely many cells of that dimension; for compact
`M` it is the finite model `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`.

The model is the union of the CW models of an exhaustion of `M` by regular sublevels. Choose
regular values `a 0 < a 1 < ⋯` tending to infinity, with `a 0` below every value of `f`
(`TauCeti.IsMorse.exists_regular_sublevel_exhaustion`). The sublevel `M_{a 0}` is empty, the empty
CW complex. Each band `f⁻¹[a k, a (k + 1)]` is compact, so a CW model `W k ≃ₕ M_{a k}` extends to a
CW model `W (k + 1) ≃ₕ M_{a (k + 1)}` containing `W k` as a subcomplex, with one new `λ`-cell for
each critical point of index `λ` with value in `(a k, a (k + 1)]`
(`TauCeti.IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel`). Every stage is a finite CW
complex, since a compact band holds finitely many critical points
(`TauCeti.IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel`).

The colimit `X` of the stages `W k` is a CW complex whose cells are the new cells of all the stages
(`TauCeti.cwComplexOfIsColimit`), so its `λ`-cells correspond to the critical points of index `λ`:
each lies in exactly one band `(a k, a (k + 1)]`. It is Hausdorff, indeed normal, because each
stage is compact (`TauCeti.TopCat.normalSpace_of_isColimit`). Inside `X` the stages are linked by
closed cofibrations, since each is a subcomplex of the next, and so are the regular sublevels of
`M`, by collars of the regular levels
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`). The models of
the stages commute strictly with the inclusions, so they glue to a map `X → M` which is a homotopy
equivalence on every stage, hence a homotopy equivalence
(`TauCeti.exists_homotopyEquiv_of_isCoherentWith`).

## Main results

* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv` and
  `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le`: **the
  sublevel-compatible CW model of a proper Morse function.** A manifold carrying a proper Morse
  function bounded below is homotopy equivalent to a Hausdorff CW complex `X` exhausted by finite
  subcomplexes `W k` restricting to homotopy models of an exhausting sequence of regular sublevels
  `{f ≤ a k}`, with `j ∈ (W k).I m ↔ f (e m j) ≤ a k`, and finite-dimensional with no cells above
  `d` when every critical point has Morse index at most `d`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`: **the CW model of a proper Morse function.** A
  manifold carrying a proper Morse function bounded below is homotopy equivalent to a Hausdorff
  CW complex whose `λ`-cells correspond to the critical points of index `λ`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`: when every critical
  point of `f` has Morse index at most `d`, the CW model is finite-dimensional and has no cells in
  dimensions strictly above `d`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof.
-/

public section

noncomputable section

open Set Filter Topology Topology.RelCWComplex CategoryTheory Limits
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

/-- A finite CW model of the sublevel `{f ≤ a}`. -/
private structure SublevelCWModel {M : Type u} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) where
  /-- The model. -/
  W : Type u
  [topologicalSpace : TopologicalSpace W]
  [t2Space : T2Space W]
  [cwComplex : CWComplex (univ : Set W)]
  [finite : RelCWComplex.Finite (univ : Set W)]
  /-- The homotopy equivalence of the model with the sublevel. -/
  h : W ≃ₕ {x | f x ≤ a}

attribute [instance] SublevelCWModel.topologicalSpace SublevelCWModel.t2Space
  SublevelCWModel.cwComplex SublevelCWModel.finite

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- The sequence of models defined recursively from a first model and a rule extending each model
to the next sublevel. -/
private def sublevelCWModelSeq {M : Type u} [TopologicalSpace M] {f : M → ℝ} {a : ℕ → ℝ}
    (S₀ : SublevelCWModel f (a 0))
    (S' : ∀ k, SublevelCWModel f (a k) → SublevelCWModel f (a (k + 1))) :
    ∀ k, SublevelCWModel f (a k)
  | 0 => S₀
  | k + 1 => S' k (sublevelCWModelSeq S₀ S' k)

/-- Across a compact band between regular values, a finite CW model of the lower sublevel extends
to one of the upper sublevel, containing it as a subcomplex, with one new `m`-cell for each
critical point of index `m` in the band. -/
private theorem IsMorse.exists_sublevelCWModel_extension (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (S : SublevelCWModel f a) :
    ∃ (S' : SublevelCWModel f b) (ι : C(S.W, S'.W)), IsClosedEmbedding ι ∧
      (∀ w, (S'.h (ι w) : M) = S.h w) ∧
      ∃ e : ∀ m, cell (univ : Set S'.W) m ≃ cell (univ : Set S.W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', _, hι, -, hh, e, he⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb S.W S.h
  exact ⟨⟨W', h'⟩, ι, hι, hh, e, he⟩

/-- The critical points of index `m` are the disjoint union, over `k`, of those with value in
`(a k, a (k + 1)]`, when `a` increases to infinity from below all values of `f`. -/
private def sigmaCriticalPointsIocEquiv {a : ℕ → ℝ} (hmono : StrictMono a)
    (htop : Tendsto a atTop atTop) (ha0 : ∀ x, a 0 < f x) (m : ℕ) :
    (Σ k, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m})
      ≃ ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
  Equiv.ofBijective (fun p ↦ ⟨p.2.1, p.2.2.1.1, p.2.2.2⟩) <| by
    refine ⟨fun ⟨k, x, hx⟩ ⟨l, y, hy⟩ hxy ↦ ?_, fun ⟨x, hx, hxm⟩ ↦ ?_⟩
    · obtain rfl : x = y := congrArg Subtype.val hxy
      -- The intervals `(a k, a (k + 1)]` are pairwise disjoint.
      obtain rfl : k = l := by
        by_contra hkl
        exact hmono.monotone.pairwise_disjoint_on_Ioc_succ hkl |>.ne_of_mem hx.1.2 hy.1.2 rfl
      rfl
    · -- The intervals `(a k, a (k + 1)]` cover `(a 0, ∞)`.
      have hcover := iUnion_Ioc_map_succ_eq_Ioi (f := a) (fun k ↦ hmono.monotone (Nat.zero_le k))
        (not_bddAbove_iff.2 fun r ↦
          let ⟨k, hk⟩ := (htop.eventually_gt_atTop r).exists
          ⟨a k, mem_range_self k, hk⟩)
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hcover.symm ▸ ha0 x : f x ∈ ⋃ k, Ioc (a k) (a (k + 1)))
      exact ⟨⟨k, x, ⟨hx, hk⟩, hxm⟩, rfl⟩

omit [_root_.FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
@[simp]
private theorem coe_sigmaCriticalPointsIocEquiv_apply {a : ℕ → ℝ} (hmono : StrictMono a)
    (htop : Tendsto a atTop atTop) (ha0 : ∀ x, a 0 < f x) (m : ℕ)
    (p : Σ k, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) |
      manifoldMorseIndex I f x = m}) :
    (sigmaCriticalPointsIocEquiv hmono htop ha0 m p : M) = p.2.1 :=
  (rfl)

omit [_root_.FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- Under the colimit cell equivalence composed with band-to-critical-point equivalences and
`sigmaCriticalPointsIocEquiv`, an `m`-cell belongs to stage `k` precisely when its critical value
is at most `a k`. -/
private theorem mem_cwComplexOfIsColimitSubcomplex_I_iff_le {F : ℕ ⥤ TopCat.{u}}
    [∀ k, CWComplex (univ : Set (F.obj k))]
    (hF : ∀ k, IsClosedEmbedding (F.map (homOfLE k.le_succ)))
    {ιc : ∀ k m, cell (univ : Set (F.obj k)) m → cell (univ : Set (F.obj (k + 1))) m}
    (hιc : ∀ k m j, ⇑(map m (ιc k m j)) = F.map (homOfLE k.le_succ) ∘ map m j)
    {c : Cocone F} (hc : IsColimit c) [T2Space c.pt] {a : ℕ → ℝ} (hmono : StrictMono a)
    (htop : Tendsto a atTop atTop) (ha0 : ∀ x, a 0 < f x) {m : ℕ}
    [IsEmpty (cell (univ : Set (F.obj 0)) m)]
    (e_band : ∀ k, ↥(range (ιc k m))ᶜ ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m})
    (k : ℕ) (j : @cell c.pt _ univ ∅ (@CWComplex.instRelCWComplex _ _ _
      (cwComplexOfIsColimit hF hιc hc)) m) :
    letI := cwComplexOfIsColimit hF hιc hc
    j ∈ (cwComplexOfIsColimitSubcomplex hF hιc hc k).I m ↔
      f (((cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <| (Equiv.emptySum _ _).trans <|
        (Equiv.sigmaCongrRight e_band).trans
          (sigmaCriticalPointsIocEquiv hmono htop ha0 m)) j : M) ≤ a k := by
  let _ := cwComplexOfIsColimit hF hιc hc
  obtain ⟨i0 | ⟨l, i⟩, rfl⟩ := (cwComplexOfIsColimitCellEquiv hF hιc hc m).symm.surjective j
  · exact isEmptyElim i0
  · simp only [cwComplexOfIsColimitCellEquiv_symm_inr_mem_I_iff, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.emptySum_apply_inr, Equiv.sigmaCongrRight_apply,
      coe_sigmaCriticalPointsIocEquiv_apply]
    exact ⟨fun hlk ↦ (e_band l i).2.1.2.2.trans (hmono.monotone (Nat.succ_le_of_lt hlk)),
      fun hfk ↦ hmono.lt_iff_lt.1 ((e_band l i).2.1.2.1.trans_le hfk)⟩

/-- **The sublevel-compatible CW model of a proper Morse function** (Milnor, *Morse Theory*,
Theorem 3.5). Let `f` be a Morse function on a boundaryless manifold `M`, proper and bounded below.
Then there exist a Hausdorff CW complex `X`, a homotopy equivalence `h : X ≃ₕ M`, cell equivalences
`e m` identifying the `m`-cells of `X` with the critical points of `f` of index `m`, a strictly
increasing unbounded sequence `a` of regular values of `f`, and an exhausting increasing sequence
`W` of finite subcomplexes of `X` such that:
* an `m`-cell `j` belongs to `W k` if and only if `f (e m j) ≤ a k`;
* `h` restricts on each `W k` to a homotopy equivalence `W k ≃ₕ {x | f x ≤ a k}`, while `h.symm`
  maps `{x | f x ≤ a k}` into `W k`. -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (h : X ≃ₕ M)
      (e : ∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})
      (a : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ ⋃ k, (W k : Set X) = univ ∧ (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k m j, j ∈ (W k).I m ↔ f (e m j : M) ≤ a k) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      ∀ k, ∃ hW : (W k : Set X) ≃ₕ {x | f x ≤ a k}, ∀ w : W k, (hW w : M) = h w := by
  -- Outline: build finite CW models `S k` of the regular sublevels `M_{a k}`, each a subcomplex of
  -- the next; take their colimit `X` with its CW structure and stage subcomplexes `W k`; then glue
  -- the models to a map `X → M` and compare the two towers of closed cofibrations.
  obtain ⟨a, K, hmono, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x := by
    by_contra hx
    have hxK : x ∈ K 0 := by rw [hK]; exact not_lt.1 hx
    rw [hK0] at hxK
    exact hxK
  have hcompact (k : ℕ) : IsCompact (f ⁻¹' Icc (a k) (a (k + 1))) :=
    hp.isCompact_preimage isCompact_Icc
  choose S' ι hι hh e he using fun k (S : SublevelCWModel f (a k)) ↦
    hf.exists_sublevelCWModel_extension (hmono k.lt_succ_self).le (hcompact k) (hreg k)
      (hreg (k + 1)) S
  -- The finite CW models of the sublevels `M_{a k}`, starting from the empty one.
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (not_le.2 (ha0 x)) x.2⟩
  let S := sublevelCWModelSeq { W := PEmpty.{u + 1}, h := Homeomorph.empty.toHomotopyEquiv } S'
  -- The tower of models, its colimit `X`, and the cells of each stage among those of the next.
  let F : ℕ ⥤ TopCat.{u} :=
    Functor.ofSequence (X := fun k : ℕ ↦ TopCat.of (S k).W) fun k : ℕ ↦
      (TopCat.ofHom (ι k (S k)) : TopCat.of (S k).W ⟶ TopCat.of (S (k + 1)).W)
  have hF (k : ℕ) : IsClosedEmbedding (F.map (homOfLE k.le_succ)) := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hι k (S k)
  let (k : ℕ) : CWComplex (univ : Set (F.obj k)) := (S k).cwComplex
  have (k : ℕ) : RelCWComplex.Finite (univ : Set (F.obj k)) := (S k).finite
  have (k : ℕ) : T2Space (F.obj k) := (S k).t2Space
  let ιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) : cell (univ : Set (S (k + 1)).W) m :=
    (e k (S k) m).symm (.inl j)
  have hιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) :
      ⇑(map m (ιc k m j)) = F.map (homOfLE k.le_succ) ∘ map m j := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact funext (he k (S k) m j)
  let c := colimit.cocone F
  have hc : IsColimit c := colimit.isColimit F
  let := cwComplexOfIsColimit hF hιc hc
  -- `X` is `T4`, as a sequential colimit of compact Hausdorff spaces along closed embeddings.
  have : ∀ k, CompactSpace (F.obj k) := fun k ↦
    isCompact_univ_iff.1 (CWComplex.isCompact_of_finite (C := (univ : Set (S k).W)))
  have := TopCat.t4Space_of_isColimit hF hc
  -- The cells of `X` are the new cells of the stages after the empty initial stage, which are the
  -- critical points in the bands `(a k, a (k + 1)]`.
  have hempty0 (m : ℕ) : IsEmpty (cell (univ : Set (F.obj 0)) m) :=
    ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
  let e_cell (m : ℕ) : cell (univ : Set c.pt) m ≃
      ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
    (cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <| (Equiv.emptySum _ _).trans <|
      (Equiv.sigmaCongrRight fun k ↦ (e k (S k) m).complRangeSymmInl).trans
        (sigmaCriticalPointsIocEquiv hmono htop ha0 m)
  let W (k : ℕ) : Subcomplex (univ : Set c.pt) := cwComplexOfIsColimitSubcomplex hF hιc hc k
  -- The models glue to a map `X → M`, a homotopy equivalence on every stage.
  let φ : Cocone F :=
    { pt := TopCat.of M
      ι := NatTrans.ofSequence
        (fun k ↦ TopCat.ofHom ((ContinuousMap.subtypeVal _).comp (S k).h.toFun)) fun k ↦ by
          ext w
          rw [Functor.ofSequence_map_homOfLE_succ]
          exact hh k (S k) w }
  let g : C(c.pt, M) := (hc.desc φ).hom
  have hg (k : ℕ) (w : F.obj k) : g (c.ι.app k w) = (S k).h w :=
    ConcreteCategory.congr_hom (hc.fac φ k) w
  have hemb := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc
  let eA (k : ℕ) : (range (c.ι.app k) : Set c.pt) ≃ₕ {x | f x ≤ a k} :=
    (hemb k).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.trans (S k).h
  have heA (k : ℕ) (x : (range (c.ι.app k) : Set c.pt)) : (eA k x : M) = g x := by
    obtain ⟨_, w, rfl⟩ := x
    -- `eA k` inverts `c.ι.app k` on its range and then applies the model `(S k).h`.
    exact (congrArg (fun y ↦ ((S k).h y : M))
      ((hemb k).isEmbedding.toHomeomorph_symm_apply w)).trans (hg k w).symm
  -- The stages of `X` and the sublevels of `M` are towers of closed cofibrations, exhausting
  -- `X` and `M` with the coherent topology.
  have hBH (k : ℕ) : HasHomotopyExtensionProperty
      ((↑) ⁻¹' {x | f x ≤ a k} : Set {x | f x ≤ a (k + 1)}) := by
    rw [← range_sublevelInclusion f (hmono k.lt_succ_self).le]
    exact hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
      hf.contMDiff (hmono k.lt_succ_self) (hcompact k) (hreg k) (hmono k.lt_succ_self).le
  obtain ⟨h, h_eq, h_maps⟩ := exists_homotopyEquiv_of_isCoherentWith (TopCat.monotone_range_ι c)
    ((sublevel_mono f).comp hmono.monotone) (TopCat.iUnion_range_ι_of_isColimit hc)
    (iUnion_sublevel_eq_univ_of_tendsto f htop) (TopCat.isCoherentWith_range_ι_of_isColimit hc)
    (isCoherentWith_range_sublevel_of_tendsto hf.contMDiff.continuous htop)
    (hasHomotopyExtensionProperty_preimage_range_ι hF hιc hc) hBH g eA heA
  have hWk (k : ℕ) : (W k : Set c.pt) = range (c.ι.app k) :=
    coe_cwComplexOfIsColimitSubcomplex hF hιc hc k
  exact ⟨c.pt, _, inferInstance, ‹_›, h, e_cell, a, W, hmono, htop, hreg,
    monotone_cwComplexOfIsColimitSubcomplex hF hιc hc,
    iUnion_cwComplexOfIsColimitSubcomplex hF hιc hc,
    fun k ↦ finite_cwComplexOfIsColimitSubcomplex hF hιc hc k,
    fun k m j ↦ mem_cwComplexOfIsColimitSubcomplex_I_iff_le hF hιc hc hmono htop ha0
      (fun l ↦ (e l (S l) m).complRangeSymmInl) k j,
    fun k ↦ by rw [hWk k]; exact h_maps k, fun k ↦
      ⟨(Homeomorph.setCongr (hWk k)).toHomotopyEquiv.trans (eA k), fun w ↦ by
        simp [Homeomorph.coe_toHomotopyEquiv, Homeomorph.setCongr_apply (hWk k), heA, h_eq]⟩⟩

/-- **The sublevel-compatible CW model of an index-bounded proper Morse function.** Let `f` be a
Morse function on a boundaryless manifold `M`, proper and bounded below, whose critical points all
have Morse index at most `d`. Then `M` is homotopy equivalent via `h : X ≃ₕ M` to a
finite-dimensional Hausdorff CW complex `X` with one `m`-cell for each critical point of index `m`,
no cells in dimensions strictly above `d`, and an exhausting sequence of finite subcomplexes `W k`
restricting to homotopy models of an exhausting sequence of regular sublevels `{f ≤ a k}`. -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hidx : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (h : X ≃ₕ M)
      (e : ∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})
      (a : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ m, d < m → IsEmpty (cell (univ : Set X) m)) ∧
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ ⋃ k, (W k : Set X) = univ ∧ (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k m j, j ∈ (W k).I m ↔ f (e m j : M) ≤ a k) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      ∀ k, ∃ hW : (W k : Set X) ≃ₕ {x | f x ≤ a k}, ∀ w : W k, (hW w : M) = h w := by
  obtain ⟨X, _, _, _, h, e, a, W, hmono, htop, hreg, hWmono, hWiUnion, hWfin, hWI, hmaps, hW⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  have hempty (m : ℕ) (hm : d < m) : IsEmpty (cell (univ : Set X) m) :=
    isEmpty_cell_of_equiv_of_manifoldMorseIndex_le (e m) hidx hm
  exact ⟨X, _, ‹_›, ‹_›, h, e, a, W,
    CWComplex.finiteDimensional_of_isEmpty_cell_gt (univ : Set X) hempty, hempty,
    hmono, htop, hreg, hWmono, hWiUnion, hWfin, hWI, hmaps, hW⟩

/-- **The CW model of a proper Morse function** (Milnor, *Morse Theory*, Theorem 3.5). Let `f` be
a Morse function on a boundaryless manifold `M`, proper and bounded below. Then `M` is homotopy
equivalent to a Hausdorff CW complex `X` whose `m`-cells correspond to the critical points of `f`
of index `m`, for every `m`. When there are infinitely many critical points of index `m`, `X` has
infinitely many `m`-cells. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨X, _, _, _, h, e, -⟩ := hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  exact ⟨X, _, ‹_›, ‹_›, ⟨h.symm⟩, fun m ↦ ⟨e m⟩⟩

/-- **The finite-dimensional CW model of an index-bounded proper Morse function.** Let `f` be a
Morse function on a boundaryless manifold `M`, proper and bounded below, whose critical points all
have Morse index at most `d`. Then `M` is homotopy equivalent to a finite-dimensional Hausdorff CW
complex `X` whose `m`-cells correspond to the critical points of `f` of index `m`, and which has no
cells in dimensions strictly above `d`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hidx : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})) ∧
      ∀ m, d < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨X, _, _, _, h, e, -, -, hfd, hempty, -⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le hp hbdd hidx
  exact ⟨X, _, ‹_›, ‹_›, hfd, ⟨h.symm⟩, fun m ↦ ⟨e m⟩, hempty⟩

end TauCeti
