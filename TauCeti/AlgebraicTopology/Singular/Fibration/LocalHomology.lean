/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.OpenPartialHomeomorph.Ball

/-!
# Local homology of a Serre fibration along a fibre

Let `p : E → B` be a Serre fibration over a `T₁` space `B` and `b` a point of `B` in the source
of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such
as a chart of a topological manifold modelled on `V`. The **local homology of `E` along the
fibre** `F = p⁻¹(b)` is the relative singular homology `Hₖ(E, E ∖ F)`. This file computes it,
with coefficients in a ring `R`:

* `Hₘ(E, E ∖ F; R) = 0` for `m < r` (`TauCeti.TopCat.isZero_singularHomology_complFiber`);
* `Hₙ₊ᵣ(E, E ∖ F; R) ≅ Hₙ(F; R)` (`TauCeti.TopCat.singularHomologyComplFiberIso`).

For the identity of `B` this is the local homology of `B` at `b`
(`TauCeti.singularHomologyComplSingletonFinrankIso`). The composite
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` is a shriek map `j_!` of the inclusion `j` of the point `b`,
with untwisted coefficients on the total space. Barraud, Damian, Humilière and Oancea read their
`j_!` through `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E|_{B'}) ≅ Hₙ(F)`, where `B'` is the `(r - 1)`-skeleton of a CW
structure on `B` with a single top cell containing `b` (their Proposition 2.6), and use it to
detect classes **living over the fundamental class** of the base. A class `α ∈ Hₖ(E)` lives over
the fundamental class at `b` when its localization in `Hₖ(E, E ∖ F)` is nonzero
(`TauCeti.LivesOverFundamentalClass`). For a Serre fibration this happens exactly when
`j_! α ≠ 0` (`TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`), and
only in degrees at least `r` (`TauCeti.LivesOverFundamentalClass.finrank_le`).

The relative group, rather than the shriek map itself, is used in the definition because it does
not depend on the chart: the identification `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` depends on the chart. Its
construction `TauCeti.TopCat.singularHomologyComplFiberIso` takes a ball in the target of the
chart as an explicit argument.

## The computation

Choose a ball of positive radius `ε` about `e b` inside the target of `e`, and let `U` be its
preimage in the source of `e` (`OpenPartialHomeomorph.chartBall`), an open neighbourhood of `b`.
Excision onto the open set `p⁻¹(U)`, which contains the closed fibre `F`, identifies
`Hₖ(E, E ∖ F)` with `Hₖ(p⁻¹(U), p⁻¹(U) ∖ F)`
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`). The restriction of `p` over
`U`, followed by the homeomorphism `x ↦ e x - e b` of `U` with the ball `K` of radius `ε` about
`0` (`OpenPartialHomeomorph.chartBallHomeomorph`), is a Serre fibration over the convex
neighbourhood `K` of `0` (`OpenPartialHomeomorph.chartBallProj`) whose fibre over `0` is `F`
(`OpenPartialHomeomorph.chartBallProjFiberHomeomorph`), and the part of `p⁻¹(U)` over `K ∖ {0}` is
`p⁻¹(U) ∖ F` (`OpenPartialHomeomorph.chartBallComplFiberPairIso`). The homology of a Serre
fibration over a convex neighbourhood of `0` modulo the part over the punctured base is the shifted
homology of the fibre (`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), and vanishes below the
dimension
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`).

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplFiberIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))`,
  constructed from a ball about `e b` inside the target of `e`. After excision onto the part of `E`
  over the ball, it is `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted
  fibration (`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`
  and `TauCeti.TopCat.singularHomologyComplFiberIso_inv`).
* `TauCeti.TopCat.singularHomologyComplFiberIso_hom_naturality`: naturality of this isomorphism
  in maps of Serre fibrations over `B` (Proposition 2.12 of Barraud–Damian–Humilière–Oancea), and
  its combination with fibre localization
  (`TauCeti.homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom`).
* `TauCeti.TopCat.isZero_singularHomology_complFiber`: `Hₘ(E, E ∖ p⁻¹(b)) = 0` for `m < r`.
* `TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`: a class lives
  over the fundamental class exactly when its image in `Hₖ₋ᵣ(p⁻¹(b))` is nonzero.
* `TauCeti.LivesOverFundamentalClass.finrank_le`: such a class has degree at least `r`.
* `TauCeti.HomologicalOrientation.livesOverFundamentalClass_mapFundamentalClass_iff`:
  for a Serre fibration `p : M → B` from a compact oriented `(r + n)`-manifold whose fibre over `b`
  is a compact connected oriented `r`-manifold `F`, the shriek image of `[M]` is `±[F]`, so for any
  map `σ : M → E` over `B` into a Serre fibration `q : E → B`, the class `σ_*[M]` lives over the
  fundamental class at `b` if and only if `(σ_b)_*[F] ≠ 0` (Corollary 2.13 of
  Barraud–Damian–Humilière–Oancea).
* `TauCeti.HomologicalOrientation.fiberLocalization_mapFundamentalClass_mem_range_iff`:
  under the same hypotheses, the localization of `σ_*[M]` lies in the image of a map `τ : E₀ → E`
  of Serre fibrations over `B` if and only if `(σ_b)_*[F]` lies in the image of `τ_b` on the fibres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Example 2.4,
  Proposition 2.6, Proposition 2.12 and Corollary 2.13.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology

universe u

namespace OpenPartialHomeomorph

open TauCeti.TopCat

variable {V : Type u} [SeminormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

/-- The restriction of `p` over `chartBall e b ε`, read in the ball about `0` through
`x ↦ e x - e b` (`OpenPartialHomeomorph.chartBallHomeomorph`). -/
def chartBallProj (p : E ⟶ B) :
    _root_.TopCat.of (p ⁻¹' chartBall e b ε) ⟶ _root_.TopCat.of (ball (0 : V) ε) :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage (chartBall e b ε)) ≫
    (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (chartBall e b ε))
      (e.chartBallHomeomorph hε)).hom

/-- `chartBallProj e hε p` is the restriction of `p` over `chartBall e b ε` followed by
`OpenPartialHomeomorph.chartBallHomeomorph`. -/
lemma chartBallProj_def (p : E ⟶ B) :
    chartBallProj e hε p =
      _root_.TopCat.ofHom (p.hom.restrictPreimage (chartBall e b ε)) ≫
        (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (chartBall e b ε))
          (e.chartBallHomeomorph hε)).hom :=
  chartBallProj.eq_1 e hε p

@[simp]
lemma coe_chartBallProj_apply {p : E ⟶ B} (z : _root_.TopCat.of (p ⁻¹' chartBall e b ε)) :
    (chartBallProj e hε p z : V) = e (p z) - e b := by
  simp [chartBallProj]

include hb in
/-- A point over `chartBall e b ε` lies over `0` in the ball exactly when it lies over `b`. -/
lemma coe_chartBallProj_eq_zero_iff {p : E ⟶ B} (z : _root_.TopCat.of (p ⁻¹' chartBall e b ε)) :
    (chartBallProj e hε p z : V) = 0 ↔ p z = b := by
  rw [coe_chartBallProj_apply, sub_eq_zero]
  exact e.injOn.eq_iff (e.chartBall_subset_source b ε z.2) hb

lemma mem_serreFibrations_chartBallProj {p : E ⟶ B} (hp : serreFibrations p) :
    serreFibrations (chartBallProj e hε p) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp _)
    (serreFibrations.of_isIso _)

/-- Over `chartBall e b ε`, the complement of the fibre of `p` over `b` is the part over the
punctured ball of `chartBallProj e hε p`. -/
def chartBallComplFiberPairIso (p : E ⟶ B) :
    TopPair.interPair (X := E) (p ⁻¹' chartBall e b ε) (p ⁻¹' {b})ᶜ ≅
      TopPair.ofSubset (chartBallProj e hε p ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦
    (coe_chartBallProj_eq_zero_iff e hb hε z).not.symm

/-- The forward map of `chartBallComplFiberPairIso` is induced by the identity of
`p⁻¹(chartBall e b ε)`. -/
lemma chartBallComplFiberPairIso_hom (p : E ⟶ B) :
    (chartBallComplFiberPairIso e hb hε p).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall e b ε)))
        fun z hz ↦ (coe_chartBallProj_eq_zero_iff e hb hε z).not.2 hz :=
  TopPair.ofSubsetIso_hom _ _

/-- The inverse map of `chartBallComplFiberPairIso` is induced by the identity of
`p⁻¹(chartBall e b ε)`. -/
lemma chartBallComplFiberPairIso_inv (p : E ⟶ B) :
    (chartBallComplFiberPairIso e hb hε p).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall e b ε)))
        fun z hz ↦ (coe_chartBallProj_eq_zero_iff e hb hε z).not.1 hz :=
  TopPair.ofSubsetIso_inv _ _

/-- The fibre over `0` of `chartBallProj e hε p` is the fibre of `p` over `b`. -/
def chartBallProjFiberHomeomorph (p : E ⟶ B) (hε₀ : 0 < ε) :
    (chartBallProj e hε p ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' {b}) where
  toFun z := ⟨z.1.1, (coe_chartBallProj_eq_zero_iff e hb hε z.1).1 z.2⟩
  invFun y :=
    have hy : p y.1 = b := mem_singleton_iff.1 y.2
    ⟨⟨y.1, by
      rw [mem_preimage, hy]
      exact mem_chartBall_self e hb hε₀⟩, (coe_chartBallProj_eq_zero_iff e hb hε _).2 hy⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma coe_chartBallProjFiberHomeomorph_apply (p : E ⟶ B) (hε₀ : 0 < ε)
    (z : chartBallProj e hε p ⁻¹' {x | (x : V) = 0}) :
    (chartBallProjFiberHomeomorph e hb hε p hε₀ z : E) = z.1.1 :=
  (rfl)

lemma coe_chartBallProjFiberHomeomorph_symm_apply (p : E ⟶ B) (hε₀ : 0 < ε) (y : p ⁻¹' {b}) :
    ((chartBallProjFiberHomeomorph e hb hε p hε₀).symm y).1.1 = y.1 :=
  (rfl)

end OpenPartialHomeomorph

namespace TauCeti

namespace TopCat

section Chart

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} (R : Type u) [Ring R] (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

variable [T1Space B]

/-- Excision onto the part of `E` over `e.chartBall b ε`, followed by
`OpenPartialHomeomorph.chartBallComplFiberPairIso`. -/
private def excisionIso (hε₀ : 0 < ε) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (e.chartBallProj hε p ⁻¹' {x | (x : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))) m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) _ m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (e.chartBallComplFiberPairIso hb hε p) m

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include e hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre vanishes below the
dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the source
of an open partial homeomorphism `e : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  exact (isZero_singularHomology_preimage_ne_zero R (e.mem_serreFibrations_chartBallProj hε hp)
    (convex_ball 0 _) (ball_mem_nhds 0 hε₀) hm).of_iso (excisionIso R e hb hε hε₀ m)

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` for `m = n + r`.

The isomorphism depends on `e`, and is constructed from a ball of radius `ε` about `e b` inside
the target of `e`: it is excision onto the part of `E` over
`OpenPartialHomeomorph.chartBall e b ε`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restriction of `p` over that set
(`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`). -/
def singularHomologyComplFiberIso (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  excisionIso R e hb hε hε₀ m ≪≫
    singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
      (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso
        (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀))

/-- The isomorphism `TauCeti.TopCat.singularHomologyComplFiberIso` commutes with excision
onto the part of `E` over `OpenPartialHomeomorph.chartBall e b ε`: after excision it is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration, followed by the
identification of its fibre over `0` with the fibre over `b`. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
        (ModuleCat.of R R) m ≫
        (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom =
      TopPair.singularHomologyMap (e.chartBallComplFiberPairIso hb hε p).hom
          (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀)).hom := by
  simp [singularHomologyComplFiberIso, excisionIso]

/-- The inverse of `TauCeti.TopCat.singularHomologyComplFiberIso` is the inverse of the
identification `OpenPartialHomeomorph.chartBallProjFiberHomeomorph` of the fibre over `0` of the
restricted fibration with the fibre over `b`, followed by the inverse of
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`, the inverse of
`OpenPartialHomeomorph.chartBallComplFiberPairIso` and the excision inclusion. -/
@[reassoc]
lemma singularHomologyComplFiberIso_inv
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀)).inv ≫
        (singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).inv ≫
        TopPair.singularHomologyMap (e.chartBallComplFiberPairIso hb hε p).inv
          (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
          (ModuleCat.of R R) m := by
  simp [singularHomologyComplFiberIso, excisionIso]

/-- **The local homology of a Serre fibration along a fibre is natural in maps of fibrations**
(Barraud–Damian–Humilière–Oancea, Proposition 2.12). Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre
fibrations over a `T₁` space `B` with a chart `e` at `b`, and let `f : E ⟶ E'` be a map over `B`
restricting to `g` on the fibres over `b`. Under `TauCeti.TopCat.singularHomologyComplFiberIso`,
the map induced by `f` on relative homology is the map induced by `g` on the homology of the
fibres. -/
@[reassoc]
theorem singularHomologyComplFiberIso_hom_naturality {E' : _root_.TopCat.{u}} {p' : E' ⟶ B}
    {f : E ⟶ E'} (hε₀ : 0 < ε) (hp : serreFibrations p) (hp' : serreFibrations p')
    (hf : f ≫ p' = p) (g : _root_.TopCat.of (p ⁻¹' {b}) ⟶ _root_.TopCat.of (p' ⁻¹' {b}))
    (hg : ∀ x, (g x : E') = f x) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf ({b}ᶜ : Set B)))
        (ModuleCat.of R R) m ≫
        (singularHomologyComplFiberIso R e hb hε hε₀ hp' n m h).hom =
      (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map g := by
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))) m
  -- Restrict `f` over the chart ball `e.chartBall b ε`, where it is a map over the ball about `0`.
  let fU : _root_.TopCat.of (p ⁻¹' e.chartBall b ε) ⟶
      _root_.TopCat.of (p' ⁻¹' e.chartBall b ε) :=
    _root_.TopCat.ofHom ⟨fun z ↦ ⟨f z.1, mem_preimage.2 (by
      have hz : p' (f z.1) = p z.1 := ConcreteCategory.congr_hom hf z.1
      rw [hz]; exact z.2)⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hfU : fU ≫ e.chartBallProj hε p' = e.chartBallProj hε p := by
    refine ConcreteCategory.hom_ext _ _ fun z ↦ Subtype.ext ?_
    have hz : p' (f z.1) = p z.1 := ConcreteCategory.congr_hom hf z.1
    calc ((fU ≫ e.chartBallProj hε p') z : V)
      _ = (e.chartBallProj hε p' (fU z) : V) := rfl
      _ = e (p' (f z.1)) - e b := e.coe_chartBallProj_apply hε (fU z)
      _ = e (p z.1) - e b := by rw [hz]
      _ = (e.chartBallProj hε p z : V) := (e.coe_chartBallProj_apply hε z).symm
  let g₀ : _root_.TopCat.of (e.chartBallProj hε p ⁻¹' {x | (x : V) = 0}) ⟶
      _root_.TopCat.of (e.chartBallProj hε p' ⁻¹' {x | (x : V) = 0}) :=
    _root_.TopCat.ofHom ⟨fun z ↦ ⟨fU z.1, mem_preimage.2 (by
      have hz : e.chartBallProj hε p' (fU z.1) = e.chartBallProj hε p z.1 :=
        ConcreteCategory.congr_hom hfU z.1
      rw [mem_ofPred_eq, hz]
      exact z.2)⟩, (fU.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hExc : TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ ≫
        TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf ({b}ᶜ : Set B)) =
      TopPair.ofSubsetMap fU (fun z hz ↦ by
        have hpf : p' (f z.1) = p z.1 := ConcreteCategory.congr_hom hf z.1
        simpa [fU, hpf] using hz) ≫
        TopPair.excisionMap (X := E') (p' ⁻¹' e.chartBall b ε) (p' ⁻¹' {b})ᶜ :=
    TopPair.hom_ext_of_fst _ (by
      refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
      rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply]
      exact ((TopPair.ofSubsetMap_fst_apply f _ _).trans
        (congrArg f (TopPair.excisionMap_fst_apply _ _ z))).trans
        ((TopPair.excisionMap_fst_apply _ _ _).trans
          (congrArg Subtype.val (TopPair.ofSubsetMap_fst_apply fU _ z))).symm)
  have hPair : TopPair.ofSubsetMap fU (fun z hz ↦ by
          have hpf : p' (f z.1) = p z.1 := ConcreteCategory.congr_hom hf z.1
          simpa [fU, hpf] using hz) ≫
        (e.chartBallComplFiberPairIso hb hε p').hom =
      (e.chartBallComplFiberPairIso hb hε p).hom ≫
        TopPair.ofSubsetMap fU (fU.mapsTo_preimage_of_comp_eq hfU _) := by
    rw [OpenPartialHomeomorph.chartBallComplFiberPairIso_hom,
      OpenPartialHomeomorph.chartBallComplFiberPairIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (by ext z; rfl)
  have hFib : g₀ ≫ (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p' hε₀)).hom =
      (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀)).hom ≫ g := by
    ext z
    exact (hg ⟨z.1.1, (e.coe_chartBallProj_eq_zero_iff hb hε z.1).1 z.2⟩).symm
  -- Cancel the excision isomorphism on the left and apply naturality over the ball.
  rw [← cancel_epi (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) (ModuleCat.of R R) m)]
  rw [← TopPair.singularHomologyMap_comp_assoc, hExc, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom,
    singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom_assoc]
  rw [← TopPair.singularHomologyMap_comp_assoc, hPair, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyPreimageNeZeroIso_hom_naturality_assoc R
      (e.mem_serreFibrations_chartBallProj hε hp) (e.mem_serreFibrations_chartBallProj hε hp')
      (convex_ball 0 _) (ball_mem_nhds 0 hε₀) hfU g₀ (fun _ ↦ rfl) n m h,
    ← Functor.map_comp, ← Functor.map_comp, hFib]

end Chart

end TopCat

/-! ### Classes living over the fundamental class -/

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type u} [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)

/-- **Naturality of the shriek map for maps of Serre fibrations**
(Barraud–Damian–Humilière–Oancea, Proposition 2.12). Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre
fibrations over a `T₁` space `B` with a chart `e` at `b`, and let `f : E ⟶ E'` lie over `B`,
restricting to `g` on the fibres over `b`. Then the shriek map
`Hₘ(E) → Hₘ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` intertwines `f_*` on the total spaces with `g_*` on the
fibres. -/
@[reassoc]
theorem homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom
    {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {f : E ⟶ E'}
    {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε)
    (hp : TopCat.serreFibrations p) (hp' : TopCat.serreFibrations p') (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {b}) ⟶ _root_.TopCat.of (p' ⁻¹' {b}))
    (hg : ∀ x, (g x : E') = f x) (n m : ℕ) (h : n + finrank ℝ V = m) :
    SSet.homologyMap (_root_.TopCat.toSSet.map f) (ModuleCat.of R R) m ≫
        fiberLocalization (ModuleCat.of R R) p' b m ≫
        (TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp' n m h).hom =
      fiberLocalization (ModuleCat.of R R) p b m ≫
        (TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map g := by
  have hcomp : (p' : E' → B) ∘ (f.hom : E → E') = p := funext (ConcreteCategory.congr_hom hf)
  have hloc := homologyMap_comp_fiberLocalization_assoc (ModuleCat.of R R) f.hom hcomp b m
    (TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp' n m h).hom
  have hf_eq : _root_.TopCat.ofHom f.hom = f := rfl
  rw [hf_eq] at hloc
  rw [hloc, localHomologyMap_def]
  exact congrArg (fiberLocalization (ModuleCat.of R R) p b m ≫ ·)
    (TopCat.singularHomologyComplFiberIso_hom_naturality R e hb hε hε₀ hp hp' hf g hg n m h)

/-- **Living over the fundamental class through the shriek map.** For a Serre fibration over a
`T₁` space with a chart `e` of dimension `r` at `b`, a class `α ∈ Hₙ₊ᵣ(E; R)` lives over the
fundamental class at `b` exactly when its image under the shriek map
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` of the inclusion of `b` is nonzero, for any ball about
`e b` inside the target of `e`. -/
theorem livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero
    {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : TopCat.serreFibrations p)
    {n m : ℕ} (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) m : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p b α ↔
      (TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p b m).hom α) ≠ 0 := by
  rw [livesOverFundamentalClass_iff, not_iff_not]
  exact ⟨fun hα ↦ by rw [hα, map_zero], fun hα ↦ by
    simpa using congrArg (TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).inv.hom hα⟩

include hb in
/-- **A class living over the fundamental class has degree at least the dimension of the base.**
For a Serre fibration over a `T₁` space with a chart of dimension `r` at `b`, the local homology
`Hₖ(E, E ∖ p⁻¹(b))` vanishes for `k < r`, so no class of degree below `r` lives over the
fundamental class at `b`. -/
theorem LivesOverFundamentalClass.finrank_le (hp : TopCat.serreFibrations p) {d : ℕ}
    {α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) d : ModuleCat.{u} R)}
    (h : LivesOverFundamentalClass (ModuleCat.of R R) p b α) : finrank ℝ V ≤ d := by
  by_contra hd
  have := ModuleCat.isZero_iff_subsingleton.1 (TopCat.isZero_singularHomology_complFiber R e hb hp
    (not_le.1 hd))
  exact (livesOverFundamentalClass_iff _ _ _ _).1 h (Subsingleton.elim _ _)

/-! ### Oriented fibrations and the shriek image of the fundamental class -/

section OrientedFibration

open AlgebraicTopology

/-- The coefficient comparison `Hₘ(P; ULift ℤ) ≅ Hₘ(P; ℤ)` on relative singular homology. -/
private def pairULiftIntIso (P : TopPair.{0}) (m : ℕ) :
    P.singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) m ≅
      P.singularHomology (ModuleCat.of ℤ ℤ) m :=
  HomologicalComplex.homologyMapIso
    (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).mapIso
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso).app (TopPair.toSSetPair.obj P)) m

@[reassoc]
private lemma pairULiftIntIso_hom_naturality {P P' : TopPair.{0}} (f : P ⟶ P') (m : ℕ) :
    TopPair.singularHomologyMap f (ModuleCat.of ℤ (ULift.{0} ℤ)) m ≫
        (pairULiftIntIso P' m).hom =
      (pairULiftIntIso P m).hom ≫ TopPair.singularHomologyMap f (ModuleCat.of ℤ ℤ) m := by
  have h := ((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.hom).naturality (TopPair.toSSetPair.map f)
  exact (HomologicalComplex.homologyMap_comp _ _ m).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · m) h).trans
      (HomologicalComplex.homologyMap_comp _ _ m))

/-- `TauCeti.TopCat.singularHomologyComplFiberIso` transported to the integral coefficients
`ULift ℤ` used by `TauCeti.HomologicalOrientation`. -/
private def singularHomologyComplFiberULiftIso {V B E : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace B] [T1Space B] [TopologicalSpace E]
    (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
    (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) {p : C(E, B)}
    (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p)) (r m : ℕ) (h : r + finrank ℝ V = m) :
    localHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) (p ⁻¹' {b}) m ≅
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) r).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
        (_root_.TopCat.of (p ⁻¹' {b})) :=
  pairULiftIntIso (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (_root_.TopCat.of E))) m ≪≫
    TopCat.singularHomologyComplFiberIso ℤ e hb hε hε₀ hp r m h ≪≫
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) r).mapIso
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.symm).app
        (_root_.TopCat.of (p ⁻¹' {b}))

private lemma singularHomologyComplFiberULiftIso_hom_naturality {V B E E' : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace B]
    [T1Space B] [TopologicalSpace E] [TopologicalSpace E']
    (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
    (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) {p : C(E, B)} {p' : C(E', B)}
    (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p))
    (hp' : TopCat.serreFibrations (_root_.TopCat.ofHom p'))
    (σ : C(E, E')) (hσ : p' ∘ σ = p)
    (σb : C(p ⁻¹' {b}, p' ⁻¹' {b})) (hσb : ∀ x, (σb x : E') = σ x)
    (r m : ℕ) (h : r + finrank ℝ V = m) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) σ (by rw [← preimage_comp, hσ]) m ≫
        (singularHomologyComplFiberULiftIso e hb hε hε₀ hp' r m h).hom =
      (singularHomologyComplFiberULiftIso e hb hε hε₀ hp r m h).hom ≫
        ((singularHomologyFunctor (ModuleCat.{0} ℤ) r).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (_root_.TopCat.ofHom σb) := by
  have hcomp : _root_.TopCat.ofHom σ ≫ _root_.TopCat.ofHom p' = _root_.TopCat.ofHom p := by
    ext x
    exact congrFun hσ x
  rw [localHomologyMap_def]
  simp only [singularHomologyComplFiberULiftIso, Iso.trans_hom, Category.assoc]
  rw [pairULiftIntIso_hom_naturality_assoc,
    TopCat.singularHomologyComplFiberIso_hom_naturality_assoc ℤ e hb hε hε₀ hp hp' hcomp
      (_root_.TopCat.ofHom σb) hσb r m h]
  simp only [Iso.app_hom, Functor.mapIso_hom]
  rw [((singularHomologyFunctor (ModuleCat.{0} ℤ) r).map
    (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.symm.hom).naturality
      (_root_.TopCat.ofHom σb)]

namespace HomologicalOrientation

variable {V W U B M F E : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [TopologicalSpace B] [T1Space B]
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace W M]
  [TopologicalSpace F] [T2Space F] [CompactSpace F] [ConnectedSpace F] [ChartedSpace U F]
  [TopologicalSpace E]

/-- For a Serre fibration `p : M → B` from a compact oriented `(r + n)`-manifold whose fibre over
`b` is a compact connected oriented `r`-manifold `F`, the shriek map sends the fundamental class
`[M]` to `±[F]`. -/
private theorem singularHomologyComplFiberULiftIso_hom_fiberLocalization_fundamentalClass
    {m r : ℕ} (oM : HomologicalOrientation M W m) (hm : finrank ℝ W = m)
    (oF : HomologicalOrientation F U r) (hr : finrank ℝ U = r)
    (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
    (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) {p : C(M, B)}
    (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p))
    (eF : F ≃ₜ (p ⁻¹' {b})) (h : r + finrank ℝ V = m) :
    let Φ := singularHomologyComplFiberULiftIso e hb hε hε₀ hp r m h ≪≫
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) r).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso
        (_root_.TopCat.isoOfHomeo eF.symm)
    Φ.hom.hom ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) p b m).hom
        (oM.fundamentalClass hm)) = oF.fundamentalClass hr ∨
      Φ.hom.hom ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) p b m).hom
        (oM.fundamentalClass hm)) = -oF.fundamentalClass hr := by
  intro Φ
  -- Every top-degree class of the connected manifold `F` is a multiple `d • [F]`.
  obtain ⟨d, hd⟩ := oF.exists_eq_zsmul_fundamentalClass hr
    (Φ.hom.hom ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) p b m).hom
      (oM.fundamentalClass hm)))
  let γF : (((singularHomologyFunctor (ModuleCat.{0} ℤ) r).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (_root_.TopCat.of F)) := oF.fundamentalClass hr
  have hfib : (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) p b m).hom
      (oM.fundamentalClass hm) = d • Φ.inv.hom γF := by
    have h1 : Φ.inv.hom (Φ.hom.hom
        ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) p b m).hom (oM.fundamentalClass hm))) =
        Φ.inv.hom (d • γF) := congrArg Φ.inv.hom hd
    rw [← ModuleCat.comp_apply, Φ.hom_inv_id, ModuleCat.id_apply] at h1
    exact h1.trans (map_zsmul Φ.inv.hom d γF)
  -- Restrict to a point `x` of the fibre: `[M]` restricts to the generator `oM x`, forcing `d ∣ 1`.
  obtain ⟨y⟩ := ConnectedSpace.toNonempty (α := F)
  let x : p ⁻¹' {b} := eF y
  have hFcompact : IsCompact (p ⁻¹' {b}) := (isClosed_singleton.preimage p.continuous).isCompact
  have hloc : (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 x.2) m).hom
      ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) p b m).hom (oM.fundamentalClass hm)) =
      (oM x.1).val :=
    (congrArg (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 x.2) m).hom
      (oM.singularHomologyπ_fundamentalClass hm hFcompact)).trans
      (oM.localHomologyRestriction_fundamentalClassOn hm hFcompact x.2)
  obtain ⟨k, hk⟩ := (isLocalOrientation_iff x.1 m (oM x.1).val).1 (oM x.1).property
    ((localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 x.2) m).hom
      (Φ.inv.hom γF))
  have hdk : (d * k) • (oM x.1).val = (1 : ℤ) • (oM x.1).val := by
    rw [mul_zsmul, hk, ← map_zsmul, ← hfib, hloc, one_zsmul]
  have hunit : d * k = 1 := oM.zsmul_left_injective hm x.1 hdk
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 hunit with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · left
    rw [one_zsmul] at hd
    exact hd
  · right
    rw [neg_one_zsmul] at hd
    exact hd

/-- Under naturality of the shriek isomorphism, the localization of `σ_*[M]` maps to `±(σb)_*[F]`
in `H_r(q⁻¹(b); ℤ)`. -/
private theorem singularHomologyComplFiberULiftIso_hom_fiberLocalization_mapFundamentalClass
    {m r : ℕ} (oM : HomologicalOrientation M W m) (hm : finrank ℝ W = m)
    (oF : HomologicalOrientation F U r) (hr : finrank ℝ U = r)
    (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
    (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) {p : C(M, B)} {q : C(E, B)}
    (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p))
    (hq : TopCat.serreFibrations (_root_.TopCat.ofHom q))
    (eF : F ≃ₜ (p ⁻¹' {b}))
    (σ : C(M, E)) (hσ : q ∘ σ = p)
    (σb : C(F, (q ⁻¹' {b}))) (hσb : ∀ y : F, (σb y : E) = σ (eF y))
    (h : r + finrank ℝ V = m) :
    (singularHomologyComplFiberULiftIso e hb hε hε₀ hq r m h).hom.hom
        ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) q b m).hom
          (oM.mapFundamentalClass hm σ)) = oF.mapFundamentalClass hr σb ∨
      (singularHomologyComplFiberULiftIso e hb hε hε₀ hq r m h).hom.hom
        ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) q b m).hom
          (oM.mapFundamentalClass hm σ)) = -oF.mapFundamentalClass hr σb := by
  let R₀ := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Φp := singularHomologyComplFiberULiftIso e hb hε hε₀ hp r m h
  let Φq := singularHomologyComplFiberULiftIso e hb hε hε₀ hq r m h
  let H := (singularHomologyFunctor (ModuleCat.{0} ℤ) r).obj R₀
  -- Read `σb` on the fibre `p⁻¹(b)` via `eF.symm`.
  let g : C(p ⁻¹' {b}, q ⁻¹' {b}) := σb.comp eF.symm
  have hg : ∀ z : p ⁻¹' {b}, (g z : E) = σ z.1 := fun z ↦ by
    simpa [g] using hσb (eF.symm z)
  have hnat : Φq.hom.hom ((fiberLocalization R₀ q b m).hom (oM.mapFundamentalClass hm σ)) =
      (H.map (_root_.TopCat.ofHom g)).hom
        (Φp.hom.hom ((fiberLocalization R₀ p b m).hom (oM.fundamentalClass hm))) := by
    have h1 := ConcreteCategory.congr_hom
      (homologyMap_comp_fiberLocalization R₀ σ hσ b m) (oM.fundamentalClass hm)
    have h2 := ConcreteCategory.congr_hom
      (singularHomologyComplFiberULiftIso_hom_naturality e hb hε hε₀ hp hq σ hσ g hg r m h)
      ((fiberLocalization R₀ p b m).hom (oM.fundamentalClass hm))
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h1 h2
    rw [oM.mapFundamentalClass_def hm σ]
    exact (congrArg Φq.hom.hom h1).trans h2
  have hg_eq : H.map (_root_.TopCat.ofHom g) =
      H.map (_root_.TopCat.isoOfHomeo eF.symm).hom ≫ H.map (_root_.TopCat.ofHom σb) := by
    rw [← H.map_comp]
    rfl
  have hpm := oM.singularHomologyComplFiberULiftIso_hom_fiberLocalization_fundamentalClass hm oF hr
    e hb hε hε₀ hp eF h
  rw [hnat, hg_eq, ModuleCat.comp_apply]
  rcases hpm with hpm | hpm
  · left
    rw [Iso.trans_hom, Functor.mapIso_hom, ModuleCat.comp_apply] at hpm
    exact (congrArg (H.map (_root_.TopCat.ofHom σb)).hom hpm).trans
      (oF.mapFundamentalClass_def hr σb).symm
  · right
    rw [Iso.trans_hom, Functor.mapIso_hom, ModuleCat.comp_apply] at hpm
    calc (H.map (_root_.TopCat.ofHom σb)).hom
          ((H.map (_root_.TopCat.isoOfHomeo eF.symm).hom).hom
            (Φp.hom.hom ((fiberLocalization R₀ p b m).hom (oM.fundamentalClass hm))))
      _ = (H.map (_root_.TopCat.ofHom σb)).hom
            (-(oF.fundamentalClass hr : H.obj (_root_.TopCat.of F))) :=
        congrArg (H.map (_root_.TopCat.ofHom σb)).hom hpm
      _ = -(H.map (_root_.TopCat.ofHom σb)).hom (oF.fundamentalClass hr) := map_neg _ _
      _ = -oF.mapFundamentalClass hr σb := by rw [oF.mapFundamentalClass_def]

/-- **Corollary 2.13 of Barraud–Damian–Humilière–Oancea.** Let `p : M → B` be a Serre fibration
from a compact oriented `(r + n)`-manifold over a `T₁` space `B` with an `n`-dimensional chart `e`
at `b`, whose fibre over `b` is homeomorphic to a compact connected oriented `r`-manifold `F`.
For any Serre fibration `q : E → B` and any map `σ : M → E` over `B` restricting on the fibre `F`
to `σb : F → q⁻¹(b)`, the class `σ_*[M] ∈ H_{r+n}(E; ℤ)` lives over the fundamental class at `b`
if and only if `(σb)_*[F] ≠ 0` in `H_r(q⁻¹(b); ℤ)`. -/
theorem livesOverFundamentalClass_mapFundamentalClass_iff
    {m r : ℕ} (oM : HomologicalOrientation M W m) (hm : finrank ℝ W = m)
    (oF : HomologicalOrientation F U r) (hr : finrank ℝ U = r)
    (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {n : ℕ}
    (hn : finrank ℝ V = n) (hrm : r + n = m)
    {p : C(M, B)} {q : C(E, B)}
    (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p))
    (hq : TopCat.serreFibrations (_root_.TopCat.ofHom q))
    (eF : F ≃ₜ (p ⁻¹' {b}))
    (σ : C(M, E)) (hσ : q ∘ σ = p)
    (σb : C(F, (q ⁻¹' {b}))) (hσb : ∀ y : F, (σb y : E) = σ (eF y)) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) q b
        (oM.mapFundamentalClass hm σ) ↔
      oF.mapFundamentalClass hr σb ≠ 0 := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  have h : r + finrank ℝ V = m := hn.symm ▸ hrm
  let R₀ := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Φq := singularHomologyComplFiberULiftIso e hb hε hε₀ hq r m h
  have hiff : (fiberLocalization R₀ q b m).hom (oM.mapFundamentalClass hm σ) ≠ 0 ↔
      Φq.hom.hom ((fiberLocalization R₀ q b m).hom (oM.mapFundamentalClass hm σ)) ≠ 0 :=
    (map_ne_zero_iff _ ((ModuleCat.mono_iff_injective Φq.hom).1 inferInstance)).symm
  have h0 : LivesOverFundamentalClass R₀ q b (oM.mapFundamentalClass hm σ) ↔
      (fiberLocalization R₀ q b m).hom (oM.mapFundamentalClass hm σ) ≠ 0 :=
    livesOverFundamentalClass_iff R₀ q b (oM.mapFundamentalClass hm σ)
  rcases oM.singularHomologyComplFiberULiftIso_hom_fiberLocalization_mapFundamentalClass
      hm oF hr e hb hε hε₀ hp hq eF σ hσ σb hσb h with hshriek | hshriek
  · exact h0.trans (hiff.trans (by rw [hshriek]))
  · exact h0.trans (hiff.trans (by rw [hshriek, neg_ne_zero]))

/-- **Fibrewise range criterion for maps of Serre fibrations.** Under the hypotheses of
`TauCeti.HomologicalOrientation.livesOverFundamentalClass_mapFundamentalClass_iff`, given a second
Serre fibration `p₀ : E₀ → B` and a map `τ : E₀ → E` over `B` restricting to
`τb : p₀⁻¹(b) → q⁻¹(b)`, the localization of `σ_*[M]` lies in the image of
`localHomologyMap _ τ _ m` if and only if `(σb)_*[F]` lies in the image of `(τb)_*` on `H_r`. -/
theorem fiberLocalization_mapFundamentalClass_mem_range_iff
    {E₀ : Type} [TopologicalSpace E₀]
    {m r : ℕ} (oM : HomologicalOrientation M W m) (hm : finrank ℝ W = m)
    (oF : HomologicalOrientation F U r) (hr : finrank ℝ U = r)
    (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {n : ℕ}
    (hn : finrank ℝ V = n) (hrm : r + n = m)
    {p : C(M, B)} {p₀ : C(E₀, B)} {q : C(E, B)}
    (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p))
    (hp₀ : TopCat.serreFibrations (_root_.TopCat.ofHom p₀))
    (hq : TopCat.serreFibrations (_root_.TopCat.ofHom q))
    (eF : F ≃ₜ (p ⁻¹' {b}))
    (σ : C(M, E)) (hσ : q ∘ σ = p)
    (σb : C(F, (q ⁻¹' {b}))) (hσb : ∀ y : F, (σb y : E) = σ (eF y))
    (τ : C(E₀, E)) (hτ : q ∘ τ = p₀)
    (τb : C(p₀ ⁻¹' {b}, (q ⁻¹' {b}))) (hτb : ∀ z : p₀ ⁻¹' {b}, (τb z : E) = τ z.1) :
    (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) q b m).hom (oM.mapFundamentalClass hm σ) ∈
        LinearMap.range (localHomologyMap (S := p₀ ⁻¹' {b}) (T := q ⁻¹' {b})
          (ModuleCat.of ℤ (ULift.{0} ℤ)) τ (by rw [← preimage_comp, hτ]) m).hom ↔
      oF.mapFundamentalClass hr σb ∈
        LinearMap.range (((singularHomologyFunctor (ModuleCat.{0} ℤ) r).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map (_root_.TopCat.ofHom τb)).hom := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  have h : r + finrank ℝ V = m := hn.symm ▸ hrm
  let R₀ := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Φp₀ := singularHomologyComplFiberULiftIso e hb hε hε₀ hp₀ r m h
  let Φq := singularHomologyComplFiberULiftIso e hb hε hε₀ hq r m h
  let H := (singularHomologyFunctor (ModuleCat.{0} ℤ) r).obj R₀
  have hnatτ :=
    singularHomologyComplFiberULiftIso_hom_naturality e hb hε hε₀ hp₀ hq τ hτ τb hτb r m h
  have hmem : (fiberLocalization R₀ q b m).hom (oM.mapFundamentalClass hm σ) ∈
        LinearMap.range (localHomologyMap (S := p₀ ⁻¹' {b}) (T := q ⁻¹' {b}) R₀ τ
          (by rw [← preimage_comp, hτ]) m).hom ↔
      Φq.hom.hom ((fiberLocalization R₀ q b m).hom (oM.mapFundamentalClass hm σ)) ∈
        LinearMap.range (H.map (_root_.TopCat.ofHom τb)).hom := by
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨Φp₀.hom.hom β, ?_⟩
      have h' := ConcreteCategory.congr_hom hnatτ β
      simpa [R₀, Φp₀, Φq, H, hβ] using h'.symm
    · rintro ⟨γ, hγ⟩
      refine ⟨Φp₀.inv.hom γ, ?_⟩
      apply (ModuleCat.mono_iff_injective Φq.hom).1 inferInstance
      have hinv : Φp₀.hom.hom (Φp₀.inv.hom γ) = γ := by simp
      have h' := ConcreteCategory.congr_hom hnatτ (Φp₀.inv.hom γ)
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h'
      exact h'.trans ((congrArg (H.map (_root_.TopCat.ofHom τb)).hom hinv).trans hγ)
  rw [hmem]
  rcases oM.singularHomologyComplFiberULiftIso_hom_fiberLocalization_mapFundamentalClass
      hm oF hr e hb hε hε₀ hp hq eF σ hσ σb hσb h with hshriek | hshriek
  · rw [hshriek]
  · rw [hshriek, Submodule.neg_mem_iff]

end HomologicalOrientation

end OrientedFibration

end TauCeti
