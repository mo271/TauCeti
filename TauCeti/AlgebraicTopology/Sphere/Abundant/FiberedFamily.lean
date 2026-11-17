/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.CompactOpen
import TauCeti.Topology.MappingSpace.Fibration

/-!
# Abundance with two-spheres from fibred families

Barraud, Damian, Humilière and Oancea (Definition 6.14 and Proposition 6.15) give a geometric
criterion for a space `Q` to be abundant with two-spheres (`TauCeti.IsAbundantWithTwoSpheres`):
a **fibred family of two-spheres** consists of a Serre fibration `p : M → Q` from a compact
oriented `(r + n)`-manifold `M` with fibre `F` over `b` a compact connected oriented `r`-manifold,
together with a continuous map `σ : M → Map(S², Q)` lying over `Q` (so `ev ∘ σ = p`, where `ev`
evaluates at the north pole of `S²`).

Restricting `σ` to the fibre over `b` yields a map `σb : F → Map_*(S², Q)` into the based mapping
space at `b`. By naturality of the shriek isomorphism
(`TauCeti.TopCat.singularHomologyComplFiberIso`) and the fibrewise criteria of
`TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology`, the homology class
`σ_*[M] ∈ H_{r+n}(Map(S², Q); ℤ)` witnesses abundance with two-spheres at `b`:

* when `r > 0`, as soon as `(σb)_*[F] ≠ 0` in `H_r(Map_*(S², Q); ℤ)`
  (`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_pos`);
* when `r = 0`, as soon as `(σb)_*[F]` does not lie in the span of the class of the constant
  sphere in `H₀(Map_*(S², Q); ℤ)`
  (`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_zero`).

As an immediate consequence of the `r = 0` criterion (Example 6.17 of the source), any continuous
section `σ : Q → Map(S², Q)` of evaluation at the north pole whose value `σ b` is not homotopic
rel north pole to the constant sphere at `b` makes a compact oriented `n`-manifold `Q` abundant
with two-spheres at `b`
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_section_not_joined`).

We also record homeomorphism invariance of abundance with two-spheres
(`Homeomorph.isAbundantWithTwoSpheres_iff`), holding for arbitrary topological spaces without
manifold assumptions.

## Main results

* `Homeomorph.isAbundantWithTwoSpheres_iff`: abundance with two-spheres is invariant under
  homeomorphisms.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_pos`: positive-dimensional fibred
  family criterion (Proposition 6.15, case `r > 0`).
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_zero`: zero-dimensional fibred
  family criterion (Proposition 6.15, case `r = 0`).
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_section_not_joined`: abundance from
  a section of evaluation whose fibre sphere is not nullhomotopic (Example 6.17).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definitions 6.11 and 6.14, Proposition 6.15,
  and Example 6.17.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module Set

namespace Homeomorph

open TauCeti

/-- Pushing forward a witness of abundance with two-spheres along a homeomorphism `e : Q ≃ₜ Q'`. -/
private theorem isAbundantWithTwoSpheres_map {Q Q' : Type} [TopologicalSpace Q]
    [TopologicalSpace Q'] (e : Q ≃ₜ Q') {n : ℕ} {b : Q} (h : IsAbundantWithTwoSpheres Q n b) :
    IsAbundantWithTwoSpheres Q' n (e b) := by
  let R₀ := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Ψ : C(Sphere2, Q) ≃ₜ C(Sphere2, Q') := (Homeomorph.refl Sphere2).arrowCongr e
  have hΨ_ev : ∀ f : C(Sphere2, Q),
      mappingSpaceEval Sphere2.north (Ψ f) = e (mappingSpaceEval Sphere2.north f) := fun f ↦ by
    rw [mappingSpaceEval_apply, mappingSpaceEval_apply]
    rfl
  have hΨ_sub : (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))) ⁻¹'
      (mappingSpaceEval Sphere2.north ⁻¹' {e b}) ⊆ mappingSpaceEval Sphere2.north ⁻¹' {b} := by
    intro f hf
    exact e.injective (by simpa [hΨ_ev] using hf)
  have hΨ_symm_sub : (Ψ.symm : C(C(Sphere2, Q'), C(Sphere2, Q))) ⁻¹'
      (mappingSpaceEval Sphere2.north ⁻¹' {b}) ⊆ mappingSpaceEval Sphere2.north ⁻¹' {e b} := by
    intro f hf
    have h1 : mappingSpaceEval Sphere2.north (Ψ.symm f) = e.symm (f Sphere2.north) := by
      rw [mappingSpaceEval_apply]
      rfl
    have h2 : e.symm (f Sphere2.north) = b := by simpa [h1] using hf
    simpa [mappingSpaceEval_apply] using congrArg e h2
  obtain ⟨k, α, hα, hcond⟩ := (isAbundantWithTwoSpheres_iff Q n b).1 h
  let α' : ((_root_.TopCat.toSSet.obj (_root_.TopCat.of C(Sphere2, Q'))).homology R₀ k :
      ModuleCat.{0} ℤ) :=
    (SSet.homologyMap (_root_.TopCat.toSSet.map (_root_.TopCat.ofHom Ψ)) R₀ k).hom α
  -- Naturality of localization at the fibre under the homeomorphism `Ψ`.
  have hnat : SSet.homologyMap (_root_.TopCat.toSSet.map (_root_.TopCat.ofHom Ψ)) R₀ k ≫
        fiberLocalization R₀ (mappingSpaceEval Sphere2.north) (e b) k =
      fiberLocalization R₀ (mappingSpaceEval Sphere2.north) b k ≫
        localHomologyMap R₀ (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))) hΨ_sub k := by
    have h' := TopPair.singularHomologyπ_naturality
      (TopPair.ofSubsetMap (X := _root_.TopCat.of C(Sphere2, Q))
        (Y := _root_.TopCat.of C(Sphere2, Q'))
        (B := (mappingSpaceEval Sphere2.north ⁻¹' {b})ᶜ)
        (B' := (mappingSpaceEval Sphere2.north ⁻¹' {e b})ᶜ)
        (_root_.TopCat.ofHom Ψ)
        ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 hΨ_sub))) R₀ k
    simp only [TopPair.ofSubsetMap_fst] at h'
    rw [localHomologyMap_def]
    exact h'
  have hΦ_inv : localHomologyMap R₀ (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))) hΨ_sub k ≫
        localHomologyMap R₀ (Ψ.symm : C(C(Sphere2, Q'), C(Sphere2, Q))) hΨ_symm_sub k = 𝟙 _ := by
    rw [localHomologyMap_comp]
    have hcomp : (Ψ.symm : C(C(Sphere2, Q'), C(Sphere2, Q))).comp
        (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))) = ContinuousMap.id _ :=
      ContinuousMap.ext fun f ↦ Ψ.symm_apply_apply f
    rw [localHomologyMap_congr R₀ hcomp _ k, localHomologyMap_id]
    exact localHomologyRestriction_refl R₀ _ k
  have hΦ_inj : Function.Injective
      (localHomologyMap R₀ (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))) hΨ_sub k).hom := by
    intro x y hxy
    have hx := ConcreteCategory.congr_hom hΦ_inv x
    have hy := ConcreteCategory.congr_hom hΦ_inv y
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hx hy
    rw [← hx, ← hy, hxy]
  have hloc : (fiberLocalization R₀ (mappingSpaceEval Sphere2.north) (e b) k).hom α' =
      (localHomologyMap R₀ (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))) hΨ_sub k).hom
        ((fiberLocalization R₀ (mappingSpaceEval Sphere2.north) b k).hom α) := by
    simpa [α', ModuleCat.comp_apply] using ConcreteCategory.congr_hom hnat α
  have hα' : LivesOverFundamentalClass R₀ (mappingSpaceEval Sphere2.north) (e b) α' := by
    rw [livesOverFundamentalClass_iff, hloc]
    exact fun hz ↦ (livesOverFundamentalClass_iff R₀ _ b α).1 hα
      (hΦ_inj (hz.trans (map_zero _).symm))
  rcases hcond with hlt | ⟨rfl, hnotmem⟩
  · exact isAbundantWithTwoSpheres_of_lt hα' hlt
  · refine isAbundantWithTwoSpheres_of_eq hα' fun β' hβ' ↦ hnotmem ?_
    have he_sub : (e : C(Q, Q')) ⁻¹' {e b} ⊆ {b} := fun x hx ↦ e.injective hx
    have he_symm_sub : (e.symm : C(Q', Q)) ⁻¹' {b} ⊆ {e b} := fun y hy ↦ by
      simpa using congrArg e hy
    have he_inv : localHomologyMap R₀ (e.symm : C(Q', Q)) he_symm_sub k ≫
        localHomologyMap R₀ (e : C(Q, Q')) he_sub k = 𝟙 _ := by
      rw [localHomologyMap_comp]
      have hcomp : (e : C(Q, Q')).comp (e.symm : C(Q', Q)) = ContinuousMap.id _ :=
        ContinuousMap.ext fun y ↦ e.apply_symm_apply y
      rw [localHomologyMap_congr R₀ hcomp _ k, localHomologyMap_id]
      exact localHomologyRestriction_refl R₀ _ k
    have hsq : localHomologyMap R₀ (ContinuousMap.const' : C(Q, C(Sphere2, Q)))
          (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k ≫
        localHomologyMap R₀ (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))) hΨ_sub k =
      localHomologyMap R₀ (e : C(Q, Q')) he_sub k ≫
        localHomologyMap R₀ (ContinuousMap.const' : C(Q', C(Sphere2, Q')))
          (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north (e b)) k := by
      rw [localHomologyMap_comp, localHomologyMap_comp]
      have hcomp : (Ψ : C(C(Sphere2, Q), C(Sphere2, Q'))).comp ContinuousMap.const' =
          (ContinuousMap.const' : C(Q', C(Sphere2, Q'))).comp (e : C(Q, Q')) := by
        ext x s
        rfl
      exact localHomologyMap_congr R₀ hcomp _ k
    refine ⟨(localHomologyMap R₀ (e.symm : C(Q', Q)) he_symm_sub k).hom β', ?_⟩
    apply hΦ_inj
    have h1 := ConcreteCategory.congr_hom hsq
      ((localHomologyMap R₀ (e.symm : C(Q', Q)) he_symm_sub k).hom β')
    have h2 : (localHomologyMap R₀ (e : C(Q, Q')) he_sub k).hom
        ((localHomologyMap R₀ (e.symm : C(Q', Q)) he_symm_sub k).hom β') = β' := by
      have h := ConcreteCategory.congr_hom he_inv β'
      rw [ModuleCat.comp_apply, ModuleCat.id_apply] at h
      exact h
    simp only [ModuleCat.comp_apply] at h1
    rw [h1, h2, hβ', hloc]

/-- **Homeomorphism invariance of abundance with two-spheres.** A homeomorphism `e : Q ≃ₜ Q'`
carries `IsAbundantWithTwoSpheres Q n b` to `IsAbundantWithTwoSpheres Q' n (e b)`. -/
theorem isAbundantWithTwoSpheres_iff {Q Q' : Type} [TopologicalSpace Q] [TopologicalSpace Q']
    (e : Q ≃ₜ Q') (n : ℕ) (b : Q) :
    IsAbundantWithTwoSpheres Q n b ↔ IsAbundantWithTwoSpheres Q' n (e b) :=
  ⟨e.isAbundantWithTwoSpheres_map, fun h ↦ by
    simpa [e.symm_apply_apply] using e.symm.isAbundantWithTwoSpheres_map h⟩

end Homeomorph

namespace TauCeti

/-- The fibre of evaluation `Map(S², Q) → Q` over `b` is homeomorphic to the based mapping space
`Map_*(S², Q)` sending the north pole to `b`. -/
private def evalSphere2FiberHomeomorph {Q : Type} [TopologicalSpace Q] (b : Q) :
    (mappingSpaceEval (B := Sphere2) (X := Q) Sphere2.north ⁻¹' {b}) ≃ₜ
      BasedMap Sphere2 Q Sphere2.north b :=
  Homeomorph.setCongr (t := {f : C(Sphere2, Q) | f Sphere2.north = b})
    (by ext f; simp [mappingSpaceEval_apply])

namespace HomologicalOrientation

section FiberedFamily

variable {V W U Q M F : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [TopologicalSpace Q] [T1Space Q]
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace W M]
  [TopologicalSpace F] [T2Space F] [CompactSpace F] [ConnectedSpace F] [ChartedSpace U F]

/-- **Proposition 6.15 of Barraud–Damian–Humilière–Oancea (case `r > 0`).** Let `p : M → Q` be a
Serre fibration from a compact oriented `(r + n)`-manifold over a `T₁` space `Q` with an
`n`-dimensional chart `e` at `b`, whose fibre over `b` is homeomorphic to a compact connected
oriented `r`-manifold `F` with `0 < r`. If `σ : M → Map(S², Q)` lies over `Q` (so `ev ∘ σ = p`)
and its restriction `σb : F → Map_*(S², Q)` to the fibre sends `[F]` to a nonzero class in
`H_r(Map_*(S², Q); ℤ)`, then `Q` is abundant with two-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_pos
    {m r n : ℕ} (oM : HomologicalOrientation M W m) (hm : finrank ℝ W = m)
    (oF : HomologicalOrientation F U r) (hr : finrank ℝ U = r)
    (e : OpenPartialHomeomorph Q V) {b : Q} (hb : b ∈ e.source)
    (hn : finrank ℝ V = n) (hrm : r + n = m) (hrpos : 0 < r)
    {p : C(M, Q)} (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p))
    (eF : F ≃ₜ (p ⁻¹' {b}))
    (σ : C(M, C(Sphere2, Q))) (hσ : mappingSpaceEval Sphere2.north ∘ σ = p)
    (σb : C(F, BasedMap Sphere2 Q Sphere2.north b))
    (hσb : ∀ y : F, (σb y).1 = σ (eF y))
    (hσb_ne : oF.mapFundamentalClass hr σb ≠ 0) :
    IsAbundantWithTwoSpheres Q n b := by
  let ef := evalSphere2FiberHomeomorph b
  let efC : C((mappingSpaceEval (X := Q) Sphere2.north ⁻¹' {b} : Set C(Sphere2, Q)),
      BasedMap Sphere2 Q Sphere2.north b) := ef
  let efSymmC : C(BasedMap Sphere2 Q Sphere2.north b,
      (mappingSpaceEval (X := Q) Sphere2.north ⁻¹' {b} : Set C(Sphere2, Q))) := ef.symm
  let σb' : C(F, (mappingSpaceEval (X := Q) Sphere2.north ⁻¹' {b} : Set C(Sphere2, Q))) :=
    efSymmC.comp σb
  have hσb' : ∀ y : F, (σb' y : C(Sphere2, Q)) = σ (eF y) := fun y ↦ hσb y
  have hq : TopCat.serreFibrations
      (_root_.TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north)) :=
    (isHurewiczFibration_mappingSpaceEval_sphere.{0} 2 Sphere2.north).mem_serreFibrations
  have hne : oF.mapFundamentalClass hr σb' ≠ 0 := by
    intro hz
    have heq : σb = efC.comp σb' := by
      ext y s
      rfl
    apply hσb_ne
    rw [heq, oF.mapFundamentalClass_comp hr efC σb', hz, map_zero]
  exact isAbundantWithTwoSpheres_of_lt
    ((oM.livesOverFundamentalClass_mapFundamentalClass_iff hm oF hr e hb hn hrm hp hq eF σ hσ
      σb' hσb').2 hne) (by omega)

/-- **Proposition 6.15 of Barraud–Damian–Humilière–Oancea (case `r = 0`).** Let `p : M → Q` be a
Serre fibration from a compact oriented `n`-manifold over a `T₁` space `Q` with an `n`-dimensional
chart `e` at `b`, whose fibre over `b` is homeomorphic to a compact connected oriented `0`-manifold
`F`. If `σ : M → Map(S², Q)` lies over `Q` (so `ev ∘ σ = p`) and its restriction
`σb : F → Map_*(S², Q)` to the fibre sends `[F]` outside the span of the class of the constant
sphere in `H₀(Map_*(S², Q); ℤ)`, then `Q` is abundant with two-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_zero
    {n : ℕ} (oM : HomologicalOrientation M W n) (hm : finrank ℝ W = n)
    (oF : HomologicalOrientation F U 0) (hr : finrank ℝ U = 0)
    (e : OpenPartialHomeomorph Q V) {b : Q} (hb : b ∈ e.source)
    (hn : finrank ℝ V = n)
    {p : C(M, Q)} (hp : TopCat.serreFibrations (_root_.TopCat.ofHom p))
    (eF : F ≃ₜ (p ⁻¹' {b}))
    (σ : C(M, C(Sphere2, Q))) (hσ : mappingSpaceEval Sphere2.north ∘ σ = p)
    (σb : C(F, BasedMap Sphere2 Q Sphere2.north b))
    (hσb : ∀ y : F, (σb y).1 = σ (eF y))
    (hσb_not : oF.mapFundamentalClass hr σb ∉ LinearMap.range
      (singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
        (X := _root_.TopCat.of (BasedMap Sphere2 Q Sphere2.north b))
        ⟨ContinuousMap.const Sphere2 b, ContinuousMap.const_apply b Sphere2.north⟩).hom) :
    IsAbundantWithTwoSpheres Q n b := by
  let R₀ := ModuleCat.of ℤ (ULift.{0} ℤ)
  let H₀ := (singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj R₀
  let ef := evalSphere2FiberHomeomorph b
  let efC : C((mappingSpaceEval (X := Q) Sphere2.north ⁻¹' {b} : Set C(Sphere2, Q)),
      BasedMap Sphere2 Q Sphere2.north b) := ef
  let efSymmC : C(BasedMap Sphere2 Q Sphere2.north b,
      (mappingSpaceEval (X := Q) Sphere2.north ⁻¹' {b} : Set C(Sphere2, Q))) := ef.symm
  let σb' : C(F, (mappingSpaceEval (X := Q) Sphere2.north ⁻¹' {b} : Set C(Sphere2, Q))) :=
    efSymmC.comp σb
  have hσb' : ∀ y : F, (σb' y : C(Sphere2, Q)) = σ (eF y) := fun y ↦ hσb y
  have hq : TopCat.serreFibrations
      (_root_.TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north)) :=
    (isHurewiczFibration_mappingSpaceEval_sphere.{0} 2 Sphere2.north).mem_serreFibrations
  have hp₀ : TopCat.serreFibrations (_root_.TopCat.ofHom (ContinuousMap.id Q)) :=
    (Homeomorph.refl Q).isHurewiczFibration.{0}.mem_serreFibrations
  let τb : C((ContinuousMap.id Q ⁻¹' {b} : Set Q),
      (mappingSpaceEval (X := Q) Sphere2.north ⁻¹' {b} : Set C(Sphere2, Q))) :=
    ⟨fun z ↦ ⟨ContinuousMap.const Sphere2 z.1, by simpa using z.2⟩, by fun_prop⟩
  have hτ : mappingSpaceEval Sphere2.north ∘ (ContinuousMap.const' : C(Q, C(Sphere2, Q))) =
      ContinuousMap.id Q := by
    ext x
    simp
  have hτb : ∀ z : ContinuousMap.id Q ⁻¹' {b}, (τb z : C(Sphere2, Q)) = ContinuousMap.const' z.1 :=
    fun _ ↦ rfl
  have heq : σb = efC.comp σb' := by
    ext y s
    rfl
  have hne : oF.mapFundamentalClass hr σb' ≠ 0 := by
    intro hz
    apply hσb_not
    rw [heq, oF.mapFundamentalClass_comp hr efC σb', hz, map_zero]
    exact zero_mem _
  have hlives : LivesOverFundamentalClass R₀ (mappingSpaceEval Sphere2.north) b
      (oM.mapFundamentalClass hm σ) :=
    (oM.livesOverFundamentalClass_mapFundamentalClass_iff hm oF hr e hb hn (zero_add n)
      hp hq eF σ hσ σb' hσb').2 hne
  have hnotmem' : oF.mapFundamentalClass hr σb' ∉
      LinearMap.range (H₀.map (_root_.TopCat.ofHom τb)).hom := by
    rintro ⟨γ, hγ⟩
    apply hσb_not
    -- The singleton fibre `id⁻¹({b})` is path-connected, so its `H₀` is spanned by `[b]`.
    let S := _root_.TopCat.of (ContinuousMap.id Q ⁻¹' {b} : Set Q)
    let bpt : S := ⟨b, rfl⟩
    have : PathConnectedSpace S :=
      ⟨⟨bpt⟩, fun x y ↦ by
        obtain rfl : x = y := Subtype.ext (x.2.trans y.2.symm)
        exact Joined.refl _⟩
    have hcomp_id : S.singularHomology₀ε R₀ ≫ singularHomology₀Section (X := S) R₀ bpt = 𝟙 _ :=
      singularHomology₀ε_singularHomology₀Section (X := S) R₀ bpt
    let r : R₀ := (S.singularHomology₀ε R₀).hom γ
    have hγ_eq : (singularHomology₀Section (X := S) R₀ bpt).hom r = γ := by
      have h := ConcreteCategory.congr_hom hcomp_id γ
      rw [ModuleCat.comp_apply, ModuleCat.id_apply] at h
      exact h
    refine ⟨r, ?_⟩
    have hnat1 := ConcreteCategory.congr_hom
      (singularHomology₀Section_naturality R₀ (_root_.TopCat.ofHom τb) bpt) r
    have hnat2 := ConcreteCategory.congr_hom
      (singularHomology₀Section_naturality R₀ (_root_.TopCat.ofHom efC) (τb bpt)) r
    rw [ModuleCat.comp_apply] at hnat1 hnat2
    have hpush : (H₀.map (_root_.TopCat.ofHom efC)).hom
        (oF.mapFundamentalClass hr σb') = oF.mapFundamentalClass hr σb := by
      rw [heq, oF.mapFundamentalClass_comp hr efC σb']
    have hc : efC (τb bpt) =
        ⟨ContinuousMap.const Sphere2 b, ContinuousMap.const_apply b Sphere2.north⟩ :=
      Subtype.ext (ContinuousMap.ext fun _ ↦ rfl)
    rw [← hpush, ← hγ, ← hγ_eq]
    exact (congrArg (fun p ↦ (singularHomology₀Section R₀ p).hom r) hc.symm).trans
      (hnat2.symm.trans (congrArg (H₀.map (_root_.TopCat.ofHom efC)).hom hnat1.symm))
  refine isAbundantWithTwoSpheres_of_eq hlives fun β hβ ↦ hnotmem' ?_
  have hiff := oM.fiberLocalization_mapFundamentalClass_mem_range_iff hm oF hr e hb hn
    (zero_add n) hp hp₀ hq eF σ hσ σb' hσb' ContinuousMap.const' hτ τb hτb
  exact hiff.1 ⟨β, hβ⟩

end FiberedFamily

section SectionCase

variable {V Q : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace Q] [T2Space Q] [CompactSpace Q] [ChartedSpace V Q]

/-- **Abundance from a section whose fibre sphere is not nullhomotopic**
(Barraud–Damian–Humilière–Oancea, Example 6.17). Let `Q` be a compact oriented `n`-manifold and
let `σ : Q → Map(S², Q)` be a continuous section of evaluation at the north pole. If the sphere
`σ b` is not joined by a path in `Map_*(S², Q)` to the constant sphere at `b` (i.e. `σ b` is not
nullhomotopic rel north pole), then `Q` is abundant with two-spheres at `b`. -/
theorem isAbundantWithTwoSpheres_of_section_not_joined
    {n : ℕ} (oQ : HomologicalOrientation Q V n) (hn : finrank ℝ V = n) (b : Q)
    (σ : C(Q, C(Sphere2, Q))) (hσ : mappingSpaceEval Sphere2.north ∘ σ = id)
    (hns : ¬ Joined
      (⟨ContinuousMap.const Sphere2 b, ContinuousMap.const_apply b Sphere2.north⟩ :
        BasedMap Sphere2 Q Sphere2.north b)
      ⟨σ b, by simpa [mappingSpaceEval_apply] using congrFun hσ b⟩) :
    IsAbundantWithTwoSpheres Q n b := by
  let F := EuclideanSpace ℝ (Fin 0)
  have hF0 : finrank ℝ F = 0 := finrank_euclideanSpace_fin (n := 0)
  obtain ⟨oF⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace (M := F) (E := F) hF0
  have hp : TopCat.serreFibrations (_root_.TopCat.ofHom (ContinuousMap.id Q)) :=
    (Homeomorph.refl Q).isHurewiczFibration.{0}.mem_serreFibrations
  let eF : F ≃ₜ (ContinuousMap.id Q ⁻¹' {b} : Set Q) :=
    { toFun := fun _ ↦ ⟨b, rfl⟩
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun ⟨x, hx⟩ ↦ Subtype.ext hx.symm
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  let c₀ : BasedMap Sphere2 Q Sphere2.north b :=
    ⟨ContinuousMap.const Sphere2 b, ContinuousMap.const_apply b Sphere2.north⟩
  let s₀ : BasedMap Sphere2 Q Sphere2.north b :=
    ⟨σ b, by simpa [mappingSpaceEval_apply] using congrFun hσ b⟩
  let σb : C(F, BasedMap Sphere2 Q Sphere2.north b) := ContinuousMap.const F s₀
  have hσ' : mappingSpaceEval Sphere2.north ∘ σ = ContinuousMap.id Q := hσ
  refine oQ.isAbundantWithTwoSpheres_of_zero hn oF hF0 (chartAt V b) (mem_chart_source V b) hn
    hp eF σ hσ' σb (fun _ ↦ rfl) ?_
  -- Separate the path component of `s₀` from that of `c₀` via `singularHomology₀Desc`.
  classical
  let R₀ := ModuleCat.of ℤ (ULift.{0} ℤ)
  let H₀ := (singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj R₀
  let v : BasedMap Sphere2 Q Sphere2.north b → (R₀ ⟶ R₀) :=
    fun z ↦ if Joined s₀ z then 𝟙 R₀ else 0
  have hv : ∀ ⦃x y : BasedMap Sphere2 Q Sphere2.north b⦄, Path x y → v x = v y := fun x y γ ↦ by
    have hxy : Joined x y := ⟨γ⟩
    by_cases hx : Joined s₀ x
    · simp [v, hx, hx.trans hxy]
    · have hy : ¬ Joined s₀ y := fun h ↦ hx (h.trans hxy.symm)
      simp [v, hx, hy]
  let ψ := singularHomology₀Desc R₀
    (X := _root_.TopCat.of (BasedMap Sphere2 Q Sphere2.north b)) v hv
  have hψc : singularHomology₀Section R₀ c₀ ≫ ψ = 0 := by
    rw [singularHomology₀Section_singularHomology₀Desc]
    have hnc : ¬ Joined s₀ c₀ := fun h ↦ hns h.symm
    simp [v, hnc]
  have hψs : singularHomology₀Section R₀ s₀ ≫ ψ = 𝟙 R₀ := by
    rw [singularHomology₀Section_singularHomology₀Desc]
    simp [v, Joined.refl]
  have hψσ : H₀.map (_root_.TopCat.ofHom σb) ≫ ψ =
      (_root_.TopCat.of F).singularHomology₀ε R₀ := by
    have h1 : singularHomology₀Section R₀ (0 : F) ≫ H₀.map (_root_.TopCat.ofHom σb) ≫ ψ =
        𝟙 R₀ := by
      rw [← Category.assoc, singularHomology₀Section_naturality]
      exact hψs
    calc H₀.map (_root_.TopCat.ofHom σb) ≫ ψ
      _ = ((_root_.TopCat.of F).singularHomology₀ε R₀ ≫ singularHomology₀Section R₀ (0 : F)) ≫
            H₀.map (_root_.TopCat.ofHom σb) ≫ ψ := by
          rw [singularHomology₀ε_singularHomology₀Section, Category.id_comp]
      _ = (_root_.TopCat.of F).singularHomology₀ε R₀ ≫
            (singularHomology₀Section R₀ (0 : F) ≫ H₀.map (_root_.TopCat.ofHom σb) ≫ ψ) :=
          Category.assoc _ _ _
      _ = (_root_.TopCat.of F).singularHomology₀ε R₀ := by rw [h1, Category.comp_id]
  rintro ⟨r, hr⟩
  have hzero : ψ.hom (oF.mapFundamentalClass hF0 σb) = 0 := by
    rw [← hr]
    simpa [ModuleCat.comp_apply] using ConcreteCategory.congr_hom hψc r
  let γF : H₀.obj (_root_.TopCat.of F) := oF.fundamentalClass hF0
  have hneF : γF ≠ 0 :=
    (oF.livesOverFundamentalClass_id_iff hF0 (0 : F) (oF.fundamentalClass hF0)).1
      (oF.livesOverFundamentalClass_id_fundamentalClass hF0 0)
  have hε_eq : ψ.hom (oF.mapFundamentalClass hF0 σb) =
      ((_root_.TopCat.of F).singularHomology₀ε R₀).hom γF := by
    have hcomp := ConcreteCategory.congr_hom hψσ γF
    rw [ModuleCat.comp_apply] at hcomp
    rw [oF.mapFundamentalClass_def hF0 σb]
    exact hcomp
  have hinj : Function.Injective ((_root_.TopCat.of F).singularHomology₀ε R₀).hom :=
    (ModuleCat.mono_iff_injective ((_root_.TopCat.of F).singularHomology₀ε R₀)).1 inferInstance
  exact hneF (hinj (hε_eq.symm.trans (hzero.trans (map_zero _).symm)))

end SectionCase

end HomologicalOrientation

end TauCeti
