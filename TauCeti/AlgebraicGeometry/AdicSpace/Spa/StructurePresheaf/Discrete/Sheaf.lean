/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Discrete.Cech
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Cover
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing

import Mathlib.CategoryTheory.Sites.Preserves
import TauCeti.Algebra.Category.Grp.IsSheafFor
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Empty
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.IsSheafFor
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.KanExtension
import TauCeti.CategoryTheory.Sites.IsSheafFor
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.Topology.Algebra.GroupCompletion
import TauCeti.Topology.Category.TopCommRingCat.Sheaf
import TauCeti.Topology.Maps.OpenQuotient

/-!
# Sheafiness of discrete Huber pairs and rings

Let `A` be a commutative ring equipped with the discrete topology, `P` any pair of definition of
`A`, and `A⁺` any subring of `A`. Building on the all-degree Čech acyclicity of rational covers
proved in `TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Discrete.Cech`, this file
establishes Wedhorn's Theorem 8.28(c) and the discrete case of Corollary 8.35:

* Every cover (empty, finite, or infinite, in any universe) of a rational open `W ⊆ Spa(A, A⁺)` by
  rational opens satisfies the sheaf condition both on underlying sets
  (`isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_discreteTopology`) and on topological
  commutative rings
  (`isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_topCommRingCat_of_discreteTopology`), because
  on a finite subcover both `𝒪(W)` and the finite product of coordinate rings are discrete.
* Since `presentationLimitPresheaf P Aplus` is adapted to the basis of rational opens, it is a sheaf
  of complete separated topological rings on all opens of `Spa(A, A⁺)`
  (`isSheaf_presentationLimitPresheaf_of_discreteTopology`). No containment between `P` and `A⁺` is
  needed in the discrete case, as every element of `A` is power-bounded.
* Consequently, for every quasi-compact open `W ⊆ Spa(A, A⁺)`, the ring of sections
  `presentationLimit Aplus W` embeds into a finite product of discrete rational coordinate rings and
  therefore carries the discrete topology (`discreteTopology_presentationLimit_of_isCompact`).
* At the ring level, every ring of integral elements of a discrete ring satisfies
  `TauCeti.Huber.IsSheafyForEveryPresentation`
  (`TauCeti.Huber.isSheafyForEveryPresentation_of_discreteTopology`), and every discrete commutative
  ring with a compatible uniformity is stably sheafy and sheafy
  (`TauCeti.Huber.isStablySheafyRing_of_discreteTopology`,
  `TauCeti.Huber.isSheafyRing_of_discreteTopology`).

## Main results

* `TauCeti.ValuationSpectrum.isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_discreteTopology` :
  rational covers of rational opens glue uniquely on underlying sets over a discrete pair.
* `TauCeti.ValuationSpectrum.isSheaf_underlying_presentationLimitPresheaf_of_discreteTopology` :
  the underlying presheaf of sets of `presentationLimitPresheaf` is a sheaf over a discrete pair.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_of_discreteTopology` :
  **Wedhorn's Theorem 8.28(c) for a pair**: `presentationLimitPresheaf P Aplus` is a sheaf of
  complete separated topological rings on `Spa(A, A⁺)`.
* `TauCeti.ValuationSpectrum.discreteTopology_presentationLimit_of_isCompact` : over a discrete
  pair, sections of `presentationLimit` over any quasi-compact open carry the discrete topology.
* `TauCeti.Huber.isSheafyForEveryPresentation_of_discreteTopology` : every ring of integral elements
  of a discrete ring satisfies `IsSheafyForEveryPresentation`.
* `TauCeti.Huber.isStablySheafyRing_of_discreteTopology` : **Wedhorn's Corollary 8.35 (discrete
  case)**: every discrete commutative ring is stably sheafy.
* `TauCeti.Huber.isSheafyRing_of_discreteTopology` : **Wedhorn's Theorem 8.28(c)**: every discrete
  commutative ring is sheafy.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 8.26, Theorem 8.28(c),
  and Corollary 8.35.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  Theorem 2.5.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  TauCeti.CategoryTheory TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe u v

namespace TauCeti.ValuationSpectrum

section Pair

variable {A : Type v} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
  (P : PairOfDefinition A) {Aplus : Subring A}

/-- Degree-zero gluing on `presentationLimit` for nonempty `Type v`-indexed rational covers of a
rational open, deduced from
`quasiIso_cechAugmentation_spaRationalOpens_of_iSup_eq_of_discreteTopology`. -/
private theorem existsUnique_presentationLimitMap_of_typeV {W : Opens ↥(spa Aplus)}
    (hW : W ∈ spaRationalOpens Aplus) {ι : Type v} [Nonempty ι] {U : ι → Opens ↥(spa Aplus)}
    (hU : ∀ i, U i ∈ spaRationalOpens Aplus) (hcov : ⨆ i, U i = W)
    (x : ∀ i, presentationLimit (P := P) Aplus (U i))
    (hx : ∀ i j, (presentationLimitMap (P := P) (inf_le_left : U i ⊓ U j ≤ U i)).hom.1 (x i) =
      (presentationLimitMap (P := P) (inf_le_right : U i ⊓ U j ≤ U j)).hom.1 (x j)) :
    ∃! a : presentationLimit (P := P) Aplus W,
      ∀ i, (presentationLimitMap (P := P) ((le_iSup U i).trans_eq hcov)).hom.1 a = x i := by
  let U' : ι → Set.Iic W := fun i ↦ ⟨U i, (le_iSup U i).trans_eq hcov⟩
  have hqi := quasiIso_cechAugmentation_spaRationalOpens_of_iSup_eq_of_discreteTopology P hW U'
    hU hcov
  have hcovE := ((quasiIso_cechAugmentation_iff U' isTerminalTop _).mp hqi).1
  have hf : (fun i ↦ isTerminalTop.from (U' i)) = fun i ↦ homOfLE (le_top : U' i ≤ ⊤) :=
    funext fun _ ↦ Subsingleton.elim _ _
  rw [hf] at hcovE
  have hset := (Presieve.isSheafFor_comp_forget_addCommGrpCat_iff _ _).mpr hcovE
  rw [Presieve.isSheafFor_arrows_iff] at hset
  let e := presentationLimitAddCommGrpPresheafObjEquiv P Aplus (W := W)
  have hy : Presieve.Arrows.Compatible
      (presentationLimitAddCommGrpPresheaf P Aplus W ⋙ forget AddCommGrpCat)
      (fun i ↦ homOfLE (le_top : U' i ≤ ⊤)) (fun i ↦ (e (U' i)).symm (x i)) := by
    refine (Presieve.Arrows.compatible_homOfLE_iff (fun i ↦ (le_top : U' i ≤ ⊤)) _).mpr fun i j ↦ ?_
    apply (e (U' i ⊓ U' j)).injective
    simpa only [Functor.comp_map, ConcreteCategory.forget_map_eq_ofHom, TypeCat.ofHom_apply,
      presentationLimitAddCommGrpPresheafObjEquiv_map_apply, AddEquiv.apply_symm_apply, e]
      using hx i j
  obtain ⟨t, ht, hu⟩ := hset (fun i ↦ (e (U' i)).symm (x i)) hy
  refine ⟨e ⊤ t, fun i ↦ ?_, fun a ha ↦ ?_⟩
  · have hti := congrArg (e (U' i)) (ht i)
    simpa only [Functor.comp_map, ConcreteCategory.forget_map_eq_ofHom, TypeCat.ofHom_apply,
      presentationLimitAddCommGrpPresheafObjEquiv_map_apply, AddEquiv.apply_symm_apply, e]
      using hti
  · have hta : t = (e ⊤).symm a := (hu ((e ⊤).symm a) fun i ↦ (e (U' i)).injective <| by
      simpa only [Functor.comp_map, ConcreteCategory.forget_map_eq_ofHom, TypeCat.ofHom_apply,
        presentationLimitAddCommGrpPresheafObjEquiv_map_apply, AddEquiv.apply_symm_apply, e]
        using ha i).symm
    simpa only [hta] using ((e ⊤).apply_symm_apply a).symm

/-- **Degree-zero sheaf condition for rational covers of rational opens over a discrete pair.**
Let `A` be a discrete commutative ring, `P` a pair of definition of `A`, `A⁺` a subring of `A`, and
`W ⊆ Spa(A, A⁺)` a rational open. For any family `(U i)` of rational opens covering `W` (possibly
empty or infinite, in any universe), `presentationLimitPresheaf P Aplus` satisfies the sheaf
condition on underlying sets for `(U i)`. -/
theorem isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_discreteTopology
    {W : Opens ↥(spa Aplus)} (hW : W ∈ spaRationalOpens Aplus) {ι : Type*}
    {U : ι → Opens ↥(spa Aplus)} (hU : ∀ i, U i ∈ spaRationalOpens Aplus) (hcov : ⨆ i, U i = W) :
    (Presieve.ofArrows U fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov)).IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) := by
  classical
  have hUW : ∀ i, U i ≤ W := fun i ↦ (le_iSup U i).trans_eq hcov
  rw [isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P hUW]
  have hWcomp : IsCompact (W : Set ↥(spa Aplus)) :=
    isCompact_of_mem_spaRationalFamily (mem_spaRationalOpens.mp hW)
  obtain ⟨J, hJ⟩ := hWcomp.elim_finite_subcover (fun i ↦ (U i : Set ↥(spa Aplus)))
    (fun i ↦ (U i).isOpen) (by rw [← Opens.coe_iSup, hcov])
  rcases J.eq_empty_or_nonempty with rfl | hJne
  · have hWbot : W = ⊥ := SetLike.coe_injective (by simpa using hJ)
    subst hWbot
    have _ : Subsingleton (presentationLimit (P := P) Aplus ⊥) :=
      subsingleton_presentationLimit_bot P isPowerBounded_of_mem_of_discreteTopology
    intro _ _
    refine ⟨0, fun i ↦ ?_, fun _ _ ↦ Subsingleton.elim _ _⟩
    have _ : Subsingleton (presentationLimit (P := P) Aplus (U i)) := by
      rw [le_bot_iff.mp (hUW i)]
      infer_instance
    exact Subsingleton.elim _ _
  let K := ULift.{v} (Fin (Fintype.card ↥J))
  let e : K ≃ ↥J := Equiv.ulift.trans (Fintype.equivFin ↥J).symm
  have _ : Nonempty K := ⟨e.symm ⟨hJne.choose, hJne.choose_spec⟩⟩
  let V : K → Opens ↥(spa Aplus) := fun k ↦ U (e k).1
  have hcovV : ⨆ k, V k = W := le_antisymm (iSup_le fun k ↦ hUW (e k).1) fun y hy ↦ by
    obtain ⟨i, hiJ, hyi⟩ := Set.mem_iUnion₂.mp (hJ hy)
    exact Opens.mem_iSup.mpr ⟨e.symm ⟨i, hiJ⟩, by simpa [V] using hyi⟩
  intro x hx
  obtain ⟨a, ha, hu⟩ := existsUnique_presentationLimitMap_of_typeV P hW (fun k ↦ hU (e k).1)
    hcovV (fun k ↦ x (e k).1) (fun k₁ k₂ ↦ hx (e k₁).1 (e k₂).1)
  refine ⟨a, fun i ↦ ?_, fun b hb ↦ hu b fun k ↦ hb (e k).1⟩
  have hcovUi : ⨆ k, U i ⊓ V k = U i := le_antisymm (iSup_le fun _ ↦ inf_le_left) fun y hy ↦ by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcovV.ge (hUW i hy))
    exact Opens.mem_iSup.mpr ⟨k, hy, hk⟩
  obtain ⟨_, -, huUi⟩ := existsUnique_presentationLimitMap_of_typeV P (hU i)
    (fun k ↦ inf_mem_spaRationalOpens (hU i) (hU (e k).1)) hcovUi
    (fun k ↦ (presentationLimitMap (P := P) (inf_le_left : U i ⊓ V k ≤ U i)).hom.1 (x i))
    (fun k₁ k₂ ↦ by
      simp only [presentationLimitMap_apply_presentationLimitMap_apply])
  refine (huUi _ fun k ↦ ?_).trans (huUi (x i) fun _ ↦ rfl).symm
  have hle : U i ⊓ V k ≤ U i := (le_iSup (fun k ↦ U i ⊓ V k) k).trans_eq hcovUi
  calc (presentationLimitMap (P := P) hle).hom.1 ((presentationLimitMap (P := P) (hUW i)).hom.1 a)
      = (presentationLimitMap (P := P) (inf_le_right : U i ⊓ V k ≤ V k)).hom.1
          ((presentationLimitMap (P := P) ((le_iSup V k).trans_eq hcovV)).hom.1 a) := by
        rw [presentationLimitMap_apply_presentationLimitMap_apply,
          presentationLimitMap_apply_presentationLimitMap_apply]
    _ = (presentationLimitMap (P := P) (inf_le_left : U i ⊓ V k ≤ U i)).hom.1 (x i) := by
        rw [ha k, ← hx i (e k).1]

/-- An injective map out of a discrete topological space is inducing. -/
private theorem isInducing_of_discreteTopology_of_injective {X Y : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y] {f : X → Y}
    (hf : Function.Injective f) : Topology.IsInducing f :=
  ⟨TopologicalSpace.ext_iff.mpr fun s ↦
    ⟨fun _ ↦ ⟨f '' s, isOpen_discrete _, hf.preimage_image s⟩, fun _ ↦ isOpen_discrete s⟩⟩

/-- **Topological-ring sheaf condition for rational covers of rational opens over a discrete pair.**
Compatible continuous ring homomorphisms from any topological commutative ring `E` into the
sections on a rational cover `(U i)` of a rational open `W` glue uniquely to `W`. -/
theorem isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_topCommRingCat_of_discreteTopology
    {W : Opens ↥(spa Aplus)} (hW : W ∈ spaRationalOpens Aplus) {ι : Type*}
    {U : ι → Opens ↥(spa Aplus)} (hU : ∀ i, U i ∈ spaRationalOpens Aplus) (hcov : ⨆ i, U i = W)
    (E : _root_.TopCommRingCat.{v}) :
    (Presieve.ofArrows U fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov)).IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        coyoneda.obj (op E)) := by
  classical
  have hUW : ∀ i, U i ≤ W := fun i ↦ (le_iSup U i).trans_eq hcov
  rw [Presieve.isSheafFor_iff_generate]
  refine TauCeti.TopCommRingCat.isSheafFor_of_isSheafFor_forget
    (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι) _ ?_ ?_ E
  · rw [← Presieve.isSheafFor_iff_generate]
    exact isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_discreteTopology P hW hU hcov
  rw [TauCeti.TopCommRingCat.isInducing_restrictionMap_ofArrows_iff]
  refine (isInducing_restrictionMap_iff_isInducing_presentationLimitMap P hUW).mpr ?_
  have hWcomp : IsCompact (W : Set ↥(spa Aplus)) :=
    isCompact_of_mem_spaRationalFamily (mem_spaRationalOpens.mp hW)
  obtain ⟨J, hJ⟩ := hWcomp.elim_finite_subcover (fun i ↦ (U i : Set ↥(spa Aplus)))
    (fun i ↦ (U i).isOpen) (by rw [← Opens.coe_iSup, hcov])
  let V : ↥J → Opens ↥(spa Aplus) := fun j ↦ U j.1
  have hcovJ : ⨆ j, V j = W := le_antisymm (iSup_le fun j ↦ hUW j.1) fun y hy ↦ by
    obtain ⟨i, hiJ, hyi⟩ := Set.mem_iUnion₂.mp (hJ hy)
    exact Opens.mem_iSup.mpr ⟨⟨i, hiJ⟩, hyi⟩
  have hVW : ∀ j, V j ≤ W := fun j ↦ (le_iSup V j).trans_eq hcovJ
  have _ : DiscreteTopology (presentationLimit (P := P) Aplus W) :=
    discreteTopology_presentationLimit_of_mem_spaRationalOpens P hW
  have _ : ∀ j, DiscreteTopology (presentationLimit (P := P) Aplus (V j)) :=
    fun j ↦ discreteTopology_presentationLimit_of_mem_spaRationalOpens P (hU j.1)
  have hshJ := (isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P hVW).mp
    (isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_discreteTopology P hW
      (fun (j : ↥J) ↦ hU j.1) hcovJ)
  have hrJ_inj : Function.Injective (fun (x : presentationLimit (P := P) Aplus W) (j : ↥J) ↦
      (presentationLimitMap (P := P) (hVW j)).hom.1 x) := by
    intro a b hab
    obtain ⟨_, -, hu⟩ := hshJ (fun j ↦ (presentationLimitMap (P := P) (hVW j)).hom.1 b) fun _ _ ↦ by
      rw [presentationLimitMap_apply_presentationLimitMap_apply,
        presentationLimitMap_apply_presentationLimitMap_apply]
    exact (hu a (congrFun hab)).trans (hu b fun _ ↦ rfl).symm
  exact Topology.IsInducing.of_comp
    (continuous_pi fun i ↦ (presentationLimitMap (P := P) (hUW i)).hom.2)
    (continuous_pi fun j : ↥J ↦ continuous_apply j.1)
    (isInducing_of_discreteTopology_of_injective hrJ_inj)

/-- **The underlying presheaf of sets of `presentationLimitPresheaf` is a sheaf over a discrete
pair.** Neither completeness nor any containment between `P` and `A⁺` is needed. -/
theorem isSheaf_underlying_presentationLimitPresheaf_of_discreteTopology (Aplus : Subring A) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) := by
  let G := TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat
  have hAdapted : TopCat.Presheaf.IsAdapted (X := TopCat.of ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ G) (spaRationalOpens Aplus) :=
    ⟨(presentationLimitPresheafIsPointwiseRightKanExtension
      (P := P) (Aplus := Aplus)).postcompose G⟩
  apply TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology
    (X := TopCat.of ↥(spa Aplus)) _ _ (isBasis_spaRationalOpens Aplus) hAdapted
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (isSheaf_rational_comp_of_isSheafFor_ofArrows P G fun hW hU hcov ↦
      isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_discreteTopology P hW hU hcov)

/-- **Wedhorn's Theorem 8.28(c) for a pair: `presentationLimitPresheaf` is a sheaf of complete
separated topological rings over any discrete pair.** Let `A` be a discrete commutative ring, `P`
any pair of definition of `A`, and `A⁺` any subring of `A`. Then `presentationLimitPresheaf P Aplus`
is a sheaf on all opens of `Spa(A, A⁺)`. -/
theorem isSheaf_presentationLimitPresheaf_of_discreteTopology (Aplus : Subring A) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) := by
  refine isSheaf_presentationLimitPresheaf_of_isSheaf_rational <|
    Presheaf.isSheaf_of_isSheaf_comp _ _ TopCommRingCat.isCompleteSeparated.ι fun E ↦ ?_
  exact isSheaf_rational_comp_of_isSheafFor_ofArrows P _ fun hW hU hcov ↦
    isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_topCommRingCat_of_discreteTopology P hW hU hcov
      E

/-- **Over a discrete pair, sections of `presentationLimit` over any quasi-compact open carry the
discrete topology.** Covering a quasi-compact open `W` by finitely many rational opens embeds
`presentationLimit Aplus W` into a finite product of discrete coordinate rings. -/
theorem discreteTopology_presentationLimit_of_isCompact {W : Opens ↥(spa Aplus)}
    (hW : IsCompact (W : Set ↥(spa Aplus))) :
    DiscreteTopology (presentationLimit (P := P) Aplus W) := by
  classical
  have hnbhd : ∀ x : W, ∃ V ∈ spaRationalOpens Aplus, x.1 ∈ V ∧ V ≤ W := fun x ↦
    (Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens Aplus)) x.2
  choose V hVrat hxV hVW using hnbhd
  obtain ⟨J, hJ⟩ := hW.elim_finite_subcover (fun x : W ↦ (V x : Set ↥(spa Aplus)))
    (fun x ↦ (V x).isOpen) fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  let U : ↥J → Opens ↥(spa Aplus) := fun j ↦ V j.1
  have hUW : ∀ j, U j ≤ W := fun j ↦ hVW j.1
  let S := Sieve.ofArrows U fun j ↦ homOfLE (hUW j)
  have hS : S ∈ Opens.grothendieckTopology ↥(spa Aplus) W := fun y hy ↦ by
    obtain ⟨x, hxJ, hyx⟩ := Set.mem_iUnion₂.mp (hJ hy)
    let j : ↥J := ⟨x, hxJ⟩
    exact ⟨U j, homOfLE (hUW j), Sieve.ofArrows_mk U (fun k ↦ homOfLE (hUW k)) j, hyx⟩
  let F := presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι
  have hO : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus)) F :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _
      (isSheaf_presentationLimitPresheaf_of_discreteTopology P Aplus)
  have hindF := (TauCeti.TopCommRingCat.isInducing_restrictionMap_ofArrows_iff F U
    fun j ↦ homOfLE (hUW j)).mp
      (TauCeti.TopCommRingCat.isInducing_restrictionMap_of_isSheafFor F S.arrows
        fun E ↦ hO E S hS)
  have hind : Topology.IsInducing (fun (a : presentationLimit (P := P) Aplus W) (j : ↥J) ↦
      (presentationLimitMap (P := P) (hUW j)).hom.1 a) :=
    (isInducing_restrictionMap_iff_isInducing_presentationLimitMap P hUW).mp hindF
  have hset : (Presieve.ofArrows U fun j ↦ homOfLE (hUW j)).IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).mp
      (isSheaf_underlying_presentationLimitPresheaf_of_discreteTopology P Aplus)) S hS
  have hinj : Function.Injective (fun (a : presentationLimit (P := P) Aplus W) (j : ↥J) ↦
      (presentationLimitMap (P := P) (hUW j)).hom.1 a) := by
    intro a b hab
    obtain ⟨_, -, hu⟩ := (isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P hUW).mp hset
      (fun j ↦ (presentationLimitMap (P := P) (hUW j)).hom.1 b) fun _ _ ↦ by
        rw [presentationLimitMap_apply_presentationLimitMap_apply,
          presentationLimitMap_apply_presentationLimitMap_apply]
    exact (hu a (congrFun hab)).trans (hu b fun _ ↦ rfl).symm
  have _ : ∀ j, DiscreteTopology (presentationLimit (P := P) Aplus (U j)) :=
    fun j ↦ discreteTopology_presentationLimit_of_mem_spaRationalOpens P (hVrat j.1)
  exact Topology.IsEmbedding.discreteTopology ⟨hind, hinj⟩

/-- Over a discrete pair, the value of `presentationLimitPresheaf` on any quasi-compact open
carries the discrete topology. -/
theorem discreteTopology_presentationLimitPresheaf_obj_of_isCompact {W : Opens ↥(spa Aplus)}
    (hW : IsCompact (W : Set ↥(spa Aplus))) :
    DiscreteTopology ((presentationLimitPresheaf P Aplus).obj (op W)).obj := by
  rw [presentationLimitPresheaf_obj]
  exact discreteTopology_presentationLimit_of_isCompact P hW

end Pair

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber

open TauCeti.ValuationSpectrum

/-- **Discrete Huber pairs are sheafy**: every ring of integral elements `A⁺` of a discrete
commutative ring `A` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`, so the structure
presheaf of `Spa(A, A⁺)` is a sheaf of complete separated topological rings. This is Wedhorn's
Theorem 8.28(c) for the pair `(A, A⁺)`. -/
theorem isSheafyForEveryPresentation_of_discreteTopology {A : Type v} [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] {Aplus : Subring A}
    (hAplus : IsRingOfIntegralElements Aplus) :
    IsSheafyForEveryPresentation Aplus :=
  ⟨hAplus, fun P _ ↦ isSheaf_presentationLimitPresheaf_of_discreteTopology P Aplus⟩

/-- **Every discrete commutative ring is stably sheafy** (Wedhorn's Corollary 8.35, discrete case):
every complete Hausdorff Huber ring `B` topologically of finite type over the completion `Â` is
discrete (`TauCeti.Huber.IsTopologicallyFiniteType.discreteTopology`) and therefore sheafy. -/
theorem isStablySheafyRing_of_discreteTopology {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [DiscreteTopology A] :
    IsStablySheafyRing.{u, v} A := by
  have : DiscreteTopology (UniformSpace.Completion A) :=
    UniformSpace.Completion.discreteTopology_iff_separationQuotient.mpr
      SeparationQuotient.isQuotientMap_mk.discreteTopology
  refine isStablySheafyRing_iff.mpr fun B _ _ _ _ _ _ _ φ hφ ↦ ?_
  have : DiscreteTopology B := hφ.discreteTopology
  exact isSheafyRing_iff_forall_isSheafyForEveryPresentation.mpr fun _ ↦
    isSheafyForEveryPresentation_of_discreteTopology

/-- **Every discrete commutative ring is sheafy** in the sense of Wedhorn's Definition 8.26
(`TauCeti.Huber.IsSheafyRing`). This is Wedhorn's Theorem 8.28(c). -/
theorem isSheafyRing_of_discreteTopology {A : Type v} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [DiscreteTopology A] :
    IsSheafyRing A :=
  isStablySheafyRing_of_discreteTopology.isSheafyRing

end TauCeti.Huber
