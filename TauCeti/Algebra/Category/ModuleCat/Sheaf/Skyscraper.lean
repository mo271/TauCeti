/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Stalk and skyscraper functors for sheaves of modules

Let `X` be a topological space, `R` a sheaf of rings on `X`, and `x : X`. This file constructs the
stalk functor `SheafOfModules.stalkFunctor R x : SheafOfModules R ⥤ ModuleCat ↑(stalk R.obj x)`
and its right adjoint, the skyscraper module sheaf functor
`SheafOfModules.skyscraperFunctor R x : ModuleCat ↑(stalk R.obj x) ⥤ SheafOfModules R`, together
with the adjunction `SheafOfModules.stalkSkyscraperAdjunction R x`. Over an open set `U`, the
sections of the skyscraper sheaf with value `T` are canonically identified with functions
`x ∈ U → T` (`SheafOfModules.skyscraperSectionEquiv`), with `R(U)` acting through the germ map
`R(U) → R_x`; this presentation avoids any decidability hypothesis on `x ∈ U`.

For a sheaf of commutative rings `S`, the stalk `TopCat.Presheaf.stalk S.obj x` in `CommRingCat`
differs from the stalk of the underlying sheaf of rings `(ringCatSheaf S).obj` in `RingCat`. We
therefore also provide the commutative-ring variants `SheafOfModules.stalkFunctorCommRing S x`,
`SheafOfModules.skyscraperFunctorCommRing S x`, and
`SheafOfModules.stalkSkyscraperAdjunctionCommRing S x`, built from the same underlying skyscraper
construction and compatible with `SheafOfModules.stalkModule` and
`PresheafOfModules.stalkMapCommRing`.

Finally, we record that a morphism of sheaves of modules on a topological space is an isomorphism
if and only if its induced map on stalks is an isomorphism at every point
(`SheafOfModules.isIso_iff_stalkFunctor_map_isIso` and
`SheafOfModules.isIso_iff_stalkFunctorCommRing_map_isIso`).

## Main declarations

* `SheafOfModules.stalkFunctor`, `SheafOfModules.skyscraperFunctor`,
  `SheafOfModules.stalkSkyscraperAdjunction`: the stalk--skyscraper adjunction for sheaves of
  modules over a sheaf of rings;
* `SheafOfModules.skyscraperSectionEquiv`: identification of sections of a skyscraper sheaf over
  `U` with functions `x ∈ U → T`;
* `SheafOfModules.isIso_iff_stalkFunctor_map_isIso`: invertibility of a morphism of sheaves of
  modules checked on stalks;
* `SheafOfModules.stalkFunctorCommRing`, `SheafOfModules.skyscraperFunctorCommRing`,
  `SheafOfModules.stalkSkyscraperAdjunctionCommRing`,
  `SheafOfModules.skyscraperSectionCommRingEquiv`,
  `SheafOfModules.isIso_iff_stalkFunctorCommRing_map_isIso`: the corresponding API retaining the
  commutative-ring stalk as coefficient ring.

## References

* The Stacks Project, *Modules on Ringed Spaces*, Tag 01C0 (stalks of modules) and Tag 008I
  (skyscraper sheaves).
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe u

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}}

section SharedSkyscraper

variable {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (x : X)
  {A : Type u} [Ring A]
  (g : ∀ (U : Opens X), x ∈ U → R.obj.obj (op U) →+* A)
  (hg : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (r : R.obj.obj (op V)),
    g U hx (R.obj.map i.op r) = g V (i.le hx) r)

/-- Scalar action of `R(U)` on `PLift (x ∈ U) → T` through the compatible ring homomorphism
`g U hx`. -/
@[instance_reducible]
private def skyscraperSectionModule (U : Opens X) (T : ModuleCat.{u} A) :
    Module (R.obj.obj (op U)) (PLift (x ∈ U) → T) where
  smul r s hx := g U hx.down r • s hx
  one_smul s := funext fun hx ↦ (congrArg (· • s hx) (map_one _)).trans (one_smul _ _)
  mul_smul r₁ r₂ s := funext fun hx ↦
    (congrArg (· • s hx) (map_mul _ r₁ r₂)).trans (mul_smul _ _ _)
  smul_zero _ := funext fun _ ↦ smul_zero _
  smul_add _ _ _ := funext fun _ ↦ smul_add _ _ _
  add_smul r₁ r₂ s := funext fun hx ↦
    (congrArg (· • s hx) (map_add _ r₁ r₂)).trans (add_smul _ _ _)
  zero_smul s := funext fun hx ↦ (congrArg (· • s hx) (map_zero _)).trans (zero_smul _ _)

/-- The underlying presheaf of modules of a skyscraper sheaf at `x` with value `T`. -/
private def skyscraperPresheaf (T : ModuleCat.{u} A) : PresheafOfModules.{u} R.obj where
  obj U :=
    letI : Module (R.obj.obj U) (PLift (x ∈ U.unop) → T) := skyscraperSectionModule x g U.unop T
    ModuleCat.of (R.obj.obj U) (PLift (x ∈ U.unop) → T)
  map {U V} i :=
    letI : Module (R.obj.obj U) (PLift (x ∈ U.unop) → T) := skyscraperSectionModule x g U.unop T
    letI : Module (R.obj.obj V) (PLift (x ∈ V.unop) → T) := skyscraperSectionModule x g V.unop T
    ModuleCat.ofHom
      (X := ModuleCat.of (R.obj.obj U) (PLift (x ∈ U.unop) → T))
      (Y := (ModuleCat.restrictScalars (R.obj.map i).hom).obj
        (ModuleCat.of (R.obj.obj V) (PLift (x ∈ V.unop) → T)))
      { toFun := fun s hx ↦ s ⟨i.unop.le hx.down⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r s ↦ funext fun hx ↦
          congrArg (· • s ⟨i.unop.le hx.down⟩) (hg i.unop hx.down r).symm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The skyscraper presheaf of modules satisfies the unique gluing sheaf condition. -/
private theorem skyscraperPresheaf_isSheaf (T : ModuleCat.{u} A) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (skyscraperPresheaf x g hg T).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf ↦ ?_
  refine ⟨fun hx ↦ sf (Classical.choose (Opens.mem_iSup.mp hx.down))
      ⟨Classical.choose_spec (Opens.mem_iSup.mp hx.down)⟩,
    fun i ↦ ?_, fun s hs ↦ ?_⟩
  · funext hx
    let h := Opens.mem_iSup.mp ((Opens.leSupr U i).le hx.down)
    exact congrFun (hsf (Classical.choose h) i) ⟨⟨Classical.choose_spec h, hx.down⟩⟩
  · funext hx
    let h := Opens.mem_iSup.mp hx.down
    exact congrFun (hs (Classical.choose h)) ⟨Classical.choose_spec h⟩

/-- The skyscraper functor `ModuleCat A ⥤ SheafOfModules R` associated to a compatible family of
ring homomorphisms `R(U) →+* A` at `x`. -/
private def skyscraperFunctorAux : ModuleCat.{u} A ⥤ SheafOfModules.{u} R where
  obj T := ⟨skyscraperPresheaf x g hg T, skyscraperPresheaf_isSheaf x g hg T⟩
  map {T₁ T₂} f :=
    { val :=
        { app := fun U ↦
            letI : Module (R.obj.obj U) (PLift (x ∈ U.unop) → T₁) :=
              skyscraperSectionModule x g U.unop T₁
            letI : Module (R.obj.obj U) (PLift (x ∈ U.unop) → T₂) :=
              skyscraperSectionModule x g U.unop T₂
            ModuleCat.ofHom
              (X := ModuleCat.of (R.obj.obj U) (PLift (x ∈ U.unop) → T₁))
              (Y := ModuleCat.of (R.obj.obj U) (PLift (x ∈ U.unop) → T₂))
              { toFun := fun s hx ↦ f (s hx)
                map_add' := fun _ _ ↦ funext fun _ ↦ map_add f.hom _ _
                map_smul' := fun r s ↦ funext fun hx ↦
                  map_smul f.hom (g U.unop hx.down r) (s hx) }
          naturality := fun _ ↦ rfl } }
  map_id _ := rfl
  map_comp _ _ := rfl

end SharedSkyscraper

section RingCat

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- The stalk functor on sheaves of modules over a sheaf of rings `R`, sending `M` to its stalk
`M_x` as a module over the ring stalk `R_x`. -/
-- Exposed so that germs `TopCat.Presheaf.germ M.val.presheaf U x hx m` have type
-- `(stalkFunctor R x).obj M` directly.
@[expose]
def stalkFunctor : SheafOfModules.{u} R ⥤ ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x) where
  obj M := ModuleCat.of ↑(TopCat.Presheaf.stalk R.obj x)
    ↑(TopCat.Presheaf.stalk M.val.presheaf x)
  map {M N} f := ModuleCat.ofHom <| M.val.stalkLift x
    (fun U hx ↦
      AddMonoidHom.mk'
        (fun m ↦ TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) m))
        (fun a b ↦ (congrArg (TopCat.Presheaf.germ N.val.presheaf U x hx)
          ((f.val.app (op U)).hom.map_add a b)).trans (map_add _ _ _)))
    (fun {U V} i hx m ↦
      (congrArg (TopCat.Presheaf.germ N.val.presheaf U x hx)
        (PresheafOfModules.naturality_apply f.val i.op m)).trans
        (TopCat.Presheaf.germ_res_apply N.val.presheaf i x hx _))
    (fun U hx r m ↦
      (congrArg (TopCat.Presheaf.germ N.val.presheaf U x hx)
        ((f.val.app (op U)).hom.map_smul r m)).trans
        (N.val.germ_ringCat_smul (R := R.obj) x U hx r _))
  map_id M := by
    ext m
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    exact M.val.stalkLift_germ x _ _ _ U hx m
  map_comp {M N P} f g := by
    ext m
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    change (M.val.stalkLift x _ _ _) (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      (N.val.stalkLift x _ _ _)
        ((M.val.stalkLift x _ _ _) (TopCat.Presheaf.germ M.val.presheaf U x hx m))
    erw [M.val.stalkLift_germ, M.val.stalkLift_germ, N.val.stalkLift_germ]
    rfl

/-- The stalk functor sends a morphism of sheaves of modules to the map sending germs to germs of
images. -/
theorem stalkFunctor_map_germ {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    (stalkFunctor R x).map f (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) m) :=
by
  change (M.val.stalkLift (T := ↑(TopCat.Presheaf.stalk N.val.presheaf x)) x _ _ _)
    (TopCat.Presheaf.germ M.val.presheaf U x hx m) = _
  refine (M.val.stalkLift_germ (T := ↑(TopCat.Presheaf.stalk N.val.presheaf x)) x _
    (fun {U V} i hx m ↦
      (congrArg (TopCat.Presheaf.germ N.val.presheaf U x hx)
        (PresheafOfModules.naturality_apply f.val i.op m)).trans
        (TopCat.Presheaf.germ_res_apply N.val.presheaf i x hx _))
    _ U hx m)

/-- As a map of underlying types, the module stalk map agrees with the abelian-presheaf stalk
map of `SheafOfModules.toSheaf`. -/
theorem stalkFunctor_map_coe_eq {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    ((stalkFunctor R x).map f :
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) → ↑(TopCat.Presheaf.stalk N.val.presheaf x)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toSheaf R).map f).hom := by
  funext m
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  exact (stalkFunctor_map_germ R x f U hx m).trans
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ((toSheaf R).map f).hom m).symm

/-- The skyscraper module sheaf functor `ModuleCat ↑(R_x) ⥤ SheafOfModules R` at `x`: over an
open set `U`, the sections of `(skyscraperFunctor R x).obj T` are identified with functions
`x ∈ U → T` (`skyscraperSectionEquiv`). -/
def skyscraperFunctor : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x) ⥤ SheafOfModules.{u} R :=
  skyscraperFunctorAux x (fun U hx ↦ (TopCat.Presheaf.germ R.obj U x hx).hom)
    (fun i hx r ↦ TopCat.Presheaf.germ_res_apply R.obj i x hx r)

/-- Identification of the sections of a skyscraper module sheaf over `U` with functions
`x ∈ U → T`. -/
def skyscraperSectionEquiv (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) (U : Opens X) :
    ((skyscraperFunctor R x).obj T).val.obj (op U) ≃ (x ∈ U → T) where
  toFun s hx := s ⟨hx⟩
  invFun s hx := s hx.down
  left_inv _ := rfl
  right_inv _ := rfl

/-- The zero section of a skyscraper sheaf evaluates to `0`. -/
@[simp]
theorem skyscraperSectionEquiv_zero (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x))
    (U : Opens X) (hx : x ∈ U) :
    skyscraperSectionEquiv R x T U 0 hx = 0 :=
  (rfl)

/-- Addition on sections of a skyscraper sheaf acts pointwise. -/
@[simp]
theorem skyscraperSectionEquiv_add (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x))
    (U : Opens X) (s₁ s₂ : ((skyscraperFunctor R x).obj T).val.obj (op U)) (hx : x ∈ U) :
    skyscraperSectionEquiv R x T U (s₁ + s₂) hx =
      skyscraperSectionEquiv R x T U s₁ hx + skyscraperSectionEquiv R x T U s₂ hx :=
  (rfl)

/-- Scalar multiplication on sections of a skyscraper sheaf acts pointwise through the ring germ
map. -/
@[simp]
theorem skyscraperSectionEquiv_smul (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x))
    (U : Opens X) (r : R.obj.obj (op U)) (s : ((skyscraperFunctor R x).obj T).val.obj (op U))
    (hx : x ∈ U) :
    skyscraperSectionEquiv R x T U (r • s) hx =
      TopCat.Presheaf.germ R.obj U x hx r • skyscraperSectionEquiv R x T U s hx :=
  (rfl)

/-- Restriction of sections of a skyscraper sheaf acts by restricting the membership proof. -/
@[simp]
theorem skyscraperSectionEquiv_map (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x))
    {U V : Opens X} (i : U ⟶ V) (s : ((skyscraperFunctor R x).obj T).val.obj (op V))
    (hx : x ∈ U) :
    skyscraperSectionEquiv R x T U (((skyscraperFunctor R x).obj T).val.map i.op s) hx =
      skyscraperSectionEquiv R x T V s (i.le hx) :=
  (rfl)

/-- A morphism of `R_x`-modules acts pointwise on sections of the skyscraper sheaf. -/
@[simp]
theorem skyscraperSectionEquiv_skyscraperFunctor_map
    {T₁ T₂ : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (f : T₁ ⟶ T₂) (U : Opens X) (s : ((skyscraperFunctor R x).obj T₁).val.obj (op U))
    (hx : x ∈ U) :
    skyscraperSectionEquiv R x T₂ U (((skyscraperFunctor R x).map f).val.app (op U) s) hx =
      f (skyscraperSectionEquiv R x T₁ U s hx) :=
  (rfl)

private def stalkSkyscraperToFun {M : SheafOfModules.{u} R}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (α : (stalkFunctor R x).obj M ⟶ T) :
    M ⟶ (skyscraperFunctor R x).obj T :=
  { val :=
      { app := Opposite.rec fun U ↦
          ModuleCat.ofHom
            (X := M.val.obj (op U))
            (Y := ((skyscraperFunctor R x).obj T).val.obj (op U))
            { toFun := fun m ↦
                (skyscraperSectionEquiv R x T U).symm fun hx ↦
                  α (TopCat.Presheaf.germ M.val.presheaf U x hx m)
              map_add' := fun m₁ m₂ ↦ by
                apply (skyscraperSectionEquiv R x T U).injective
                funext hx
                rw [skyscraperSectionEquiv_add, Equiv.apply_symm_apply,
                  Equiv.apply_symm_apply, Equiv.apply_symm_apply]
                erw [map_add, map_add]
              map_smul' := fun r m ↦ by
                apply (skyscraperSectionEquiv R x T U).injective
                funext hx
                change α (TopCat.Presheaf.germ M.val.presheaf U x hx (r • m)) =
                  TopCat.Presheaf.germ R.obj U x hx r •
                    α (TopCat.Presheaf.germ M.val.presheaf U x hx m)
                erw [M.val.germ_ringCat_smul (R := R.obj) x U hx r m]
                exact map_smul α.hom _ _ }
        naturality := fun {U V} i ↦ by
          induction U with | op U =>
          induction V with | op V =>
          ext m
          apply (skyscraperSectionEquiv R x T V).injective
          funext hx
          change skyscraperSectionEquiv R x T V
              ((skyscraperSectionEquiv R x T V).symm fun hx ↦
                α (TopCat.Presheaf.germ M.val.presheaf V x hx (M.val.map i m))) hx =
            skyscraperSectionEquiv R x T V
              (((skyscraperFunctor R x).obj T).val.map i.unop.op
                ((skyscraperSectionEquiv R x T U).symm fun hx ↦
                  α (TopCat.Presheaf.germ M.val.presheaf U x hx m))) hx
          rw [skyscraperSectionEquiv_map R x T i.unop, Equiv.apply_symm_apply,
            Equiv.apply_symm_apply]
          erw [TopCat.Presheaf.germ_res_apply M.val.presheaf i.unop x hx m] } }

private lemma stalkSkyscraperToFun_app {M : SheafOfModules.{u} R}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (α : (stalkFunctor R x).obj M ⟶ T) (U : Opens X) (m : M.val.obj (op U)) (hx : x ∈ U) :
    skyscraperSectionEquiv R x T U ((stalkSkyscraperToFun R x α).val.app (op U) m) hx =
      α (TopCat.Presheaf.germ M.val.presheaf U x hx m) :=
  congrFun (Equiv.apply_symm_apply _ _) hx

private def stalkSkyscraperInvSection {M : SheafOfModules.{u} R}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (β : M ⟶ (skyscraperFunctor R x).obj T) (U : Opens X) (hx : x ∈ U) :
    M.val.obj (op U) →+ T :=
  AddMonoidHom.mk'
    (fun m ↦ skyscraperSectionEquiv R x T U (β.val.app (op U) m) hx)
    (fun a b ↦ by rw [map_add, skyscraperSectionEquiv_add])

private lemma stalkSkyscraperInvSection_res {M : SheafOfModules.{u} R}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (β : M ⟶ (skyscraperFunctor R x).obj T) {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (m : M.val.obj (op V)) :
    stalkSkyscraperInvSection R x β U hx (M.val.map i.op m) =
      stalkSkyscraperInvSection R x β V (i.le hx) m := by
  dsimp only [stalkSkyscraperInvSection, AddMonoidHom.mk'_apply]
  have h := PresheafOfModules.naturality_apply β.val i.op m
  exact (congrArg (fun t ↦ skyscraperSectionEquiv R x T U t hx) h).trans
    (skyscraperSectionEquiv_map R x T i (β.val.app (op V) m) hx)

private lemma stalkSkyscraperInvSection_smul {M : SheafOfModules.{u} R}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (β : M ⟶ (skyscraperFunctor R x).obj T) (U : Opens X) (hx : x ∈ U) (r : R.obj.obj (op U))
    (m : M.val.obj (op U)) :
    stalkSkyscraperInvSection R x β U hx (r • m) =
      TopCat.Presheaf.germ R.obj U x hx r • stalkSkyscraperInvSection R x β U hx m := by
  change skyscraperSectionEquiv R x T U (β.val.app (op U) (r • m)) hx =
    TopCat.Presheaf.germ R.obj U x hx r •
      skyscraperSectionEquiv R x T U (β.val.app (op U) m) hx
  rw [map_smul (β.val.app (op U)).hom r m, skyscraperSectionEquiv_smul]

private def stalkSkyscraperInvFun {M : SheafOfModules.{u} R}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (β : M ⟶ (skyscraperFunctor R x).obj T) :
    (stalkFunctor R x).obj M ⟶ T :=
  ModuleCat.ofHom <| M.val.stalkLift x
    (stalkSkyscraperInvSection R x β)
    (stalkSkyscraperInvSection_res R x β)
    (stalkSkyscraperInvSection_smul R x β)

private lemma stalkSkyscraperInvFun_germ {M : SheafOfModules.{u} R}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (β : M ⟶ (skyscraperFunctor R x).obj T) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    stalkSkyscraperInvFun R x β (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperSectionEquiv R x T U (β.val.app (op U) m) hx :=
  M.val.stalkLift_germ x (stalkSkyscraperInvSection R x β)
    (stalkSkyscraperInvSection_res R x β) (stalkSkyscraperInvSection_smul R x β) U hx m

/-- The stalk functor at `x` is left adjoint to the skyscraper module sheaf functor at `x`. -/
def stalkSkyscraperAdjunction : stalkFunctor R x ⊣ skyscraperFunctor R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M T ↦
        { toFun := stalkSkyscraperToFun R x
          invFun := stalkSkyscraperInvFun R x
          left_inv := fun α ↦ by
            ext m
            obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
            exact (stalkSkyscraperInvFun_germ R x _ U hx m).trans
              (stalkSkyscraperToFun_app R x α U m hx)
          right_inv := fun β ↦ by
            ext U m
            induction U with | op U =>
            apply (skyscraperSectionEquiv R x T U).injective
            funext hx
            exact (stalkSkyscraperToFun_app R x _ U m hx).trans
              (stalkSkyscraperInvFun_germ R x β U hx m) }
      homEquiv_naturality_left_symm := fun {M₁ M₂ T} f β ↦ by
        ext m
        obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M₁.val.presheaf m
        change stalkSkyscraperInvFun R x (f ≫ β)
            (TopCat.Presheaf.germ M₁.val.presheaf U x hx m) =
          stalkSkyscraperInvFun R x β
            ((stalkFunctor R x).map f (TopCat.Presheaf.germ M₁.val.presheaf U x hx m))
        erw [stalkFunctor_map_germ, stalkSkyscraperInvFun_germ, stalkSkyscraperInvFun_germ]
        rfl
      homEquiv_naturality_right := fun {M T₁ T₂} α f ↦ by
        ext U m
        induction U with | op U =>
        apply (skyscraperSectionEquiv R x T₂ U).injective
        funext hx
        change skyscraperSectionEquiv R x T₂ U
            ((stalkSkyscraperToFun R x (α ≫ f)).val.app (op U) m) hx =
          skyscraperSectionEquiv R x T₂ U
            (((skyscraperFunctor R x).map f).val.app (op U)
              ((stalkSkyscraperToFun R x α).val.app (op U) m)) hx
        rw [stalkSkyscraperToFun_app, skyscraperSectionEquiv_skyscraperFunctor_map,
          stalkSkyscraperToFun_app]
        rfl }

/-- The forward direction of `stalkSkyscraperAdjunction.homEquiv` evaluates on a section over `U`
by taking its germ at `x` and applying `α`. -/
@[simp]
theorem stalkSkyscraperAdjunction_homEquiv_apply
    {M : SheafOfModules.{u} R} {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (α : (stalkFunctor R x).obj M ⟶ T) (U : Opens X) (m : M.val.obj (op U)) (hx : x ∈ U) :
    skyscraperSectionEquiv R x T U
      (((stalkSkyscraperAdjunction R x).homEquiv M T α).val.app (op U) m) hx =
      α (TopCat.Presheaf.germ M.val.presheaf U x hx m) := by
  rw [stalkSkyscraperAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact stalkSkyscraperToFun_app R x α U m hx

/-- The inverse direction of `stalkSkyscraperAdjunction.homEquiv` sends the germ of `m` over `U`
to the value at `x` of `β_U(m)`. -/
theorem stalkSkyscraperAdjunction_homEquiv_symm_germ
    {M : SheafOfModules.{u} R} {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)}
    (β : M ⟶ (skyscraperFunctor R x).obj T) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    ((stalkSkyscraperAdjunction R x).homEquiv M T).symm β
        (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperSectionEquiv R x T U (β.val.app (op U) m) hx := by
  rw [stalkSkyscraperAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact stalkSkyscraperInvFun_germ R x β U hx m

/-- The unit of `stalkSkyscraperAdjunction` evaluates a section over `U ∋ x` to its germ at
`x`. -/
theorem stalkSkyscraperAdjunction_unit_app_val_app
    (M : SheafOfModules.{u} R) (U : Opens X) (m : M.val.obj (op U)) (hx : x ∈ U) :
    skyscraperSectionEquiv R x ((stalkFunctor R x).obj M) U
      (((stalkSkyscraperAdjunction R x).unit.app M).val.app (op U) m) hx =
      TopCat.Presheaf.germ M.val.presheaf U x hx m := by
  rw [← (stalkSkyscraperAdjunction R x).homEquiv_id M]
  exact stalkSkyscraperAdjunction_homEquiv_apply R x (𝟙 _) U m hx

/-- A morphism of sheaves of modules on a topological space is an isomorphism if its induced map
on stalks is an isomorphism at every point. -/
theorem isIso_of_stalkFunctor_map_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ x : X, IsIso ((stalkFunctor R x).map f)) : IsIso f := by
  have : IsIso ((toSheaf R).map f) := by
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (C := AddCommGrpCat.{u}) (X := X)]
    intro x
    rw [ConcreteCategory.isIso_iff_bijective, ← stalkFunctor_map_coe_eq R x f]
    have := hf x
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact isIso_of_reflects_iso f (toSheaf R)

/-- A morphism of sheaves of modules on a topological space is an isomorphism if and only if its
induced map on stalks is an isomorphism at every point. -/
theorem isIso_iff_stalkFunctor_map_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctor R x).map f) :=
  ⟨fun _ _ ↦ inferInstance, isIso_of_stalkFunctor_map_isIso R f⟩

end RingCat

section CommRingCat

variable (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)

/-- The stalk functor on sheaves of modules over a sheaf of commutative rings `S`, landing in
modules over the commutative-ring stalk `S.obj.stalk x` via `SheafOfModules.stalkModule`. -/
-- Exposed so that germs `TopCat.Presheaf.germ M.val.presheaf U x hx m` have type
-- `(stalkFunctorCommRing S x).obj M` directly.
@[expose]
def stalkFunctorCommRing :
    SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S) ⥤
      ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x) where
  obj M := ModuleCat.of ↑(TopCat.Presheaf.stalk S.obj x)
    ↑(TopCat.Presheaf.stalk M.val.presheaf x)
  map {M N} f := ModuleCat.ofHom (PresheafOfModules.stalkMapCommRing (S := S.obj) x f.val)
  map_id M := by
    ext m
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    exact PresheafOfModules.stalkMapCommRing_germ (S := S.obj) x (𝟙 M.val) U hx m
  map_comp {M N P} f g := by
    ext m
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    change PresheafOfModules.stalkMapCommRing (S := S.obj) x (f.val ≫ g.val)
        (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      PresheafOfModules.stalkMapCommRing (S := S.obj) x g.val
        (PresheafOfModules.stalkMapCommRing (S := S.obj) x f.val
          (TopCat.Presheaf.germ M.val.presheaf U x hx m))
    erw [PresheafOfModules.stalkMapCommRing_germ, PresheafOfModules.stalkMapCommRing_germ,
      PresheafOfModules.stalkMapCommRing_germ]
    rfl

/-- The commutative-ring stalk functor sends a morphism to the map sending germs to germs of
images. -/
theorem stalkFunctorCommRing_map_germ
    {M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)} (f : M ⟶ N)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    (stalkFunctorCommRing S x).map f (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) m) :=
  PresheafOfModules.stalkMapCommRing_germ (S := S.obj) x f.val U hx m

/-- As a map of underlying types, the commutative-ring stalk map agrees with the abelian-presheaf
stalk map of `SheafOfModules.toSheaf`. -/
theorem stalkFunctorCommRing_map_coe_eq
    {M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)} (f : M ⟶ N) :
    ((stalkFunctorCommRing S x).map f :
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) → ↑(TopCat.Presheaf.stalk N.val.presheaf x)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toSheaf (TauCeti.SheafOfModules.ringCatSheaf S)).map f).hom := by
  funext m
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  exact (stalkFunctorCommRing_map_germ S x f U hx m).trans
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ((toSheaf _).map f).hom m).symm

/-- The skyscraper module sheaf functor `ModuleCat ↑(S_x) ⥤ SheafOfModules (ringCatSheaf S)` at
`x`, retaining the commutative-ring stalk `TopCat.Presheaf.stalk S.obj x` as coefficient ring. -/
def skyscraperFunctorCommRing :
    ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x) ⥤
      SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S) :=
  skyscraperFunctorAux (R := TauCeti.SheafOfModules.ringCatSheaf S) x
    (fun U hx ↦ (TopCat.Presheaf.germ S.obj U x hx).hom)
    (fun i hx r ↦ TopCat.Presheaf.germ_res_apply S.obj i x hx r)

/-- Identification of the sections of a commutative-ring skyscraper module sheaf over `U` with
functions `x ∈ U → T`. -/
def skyscraperSectionCommRingEquiv (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x))
    (U : Opens X) :
    ((skyscraperFunctorCommRing S x).obj T).val.obj (op U) ≃ (x ∈ U → T) where
  toFun s hx := s ⟨hx⟩
  invFun s hx := s hx.down
  left_inv _ := rfl
  right_inv _ := rfl

/-- The zero section of a commutative-ring skyscraper sheaf evaluates to `0`. -/
@[simp]
theorem skyscraperSectionCommRingEquiv_zero (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x))
    (U : Opens X) (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x T U 0 hx = 0 :=
  (rfl)

/-- Addition on sections of a commutative-ring skyscraper sheaf acts pointwise. -/
@[simp]
theorem skyscraperSectionCommRingEquiv_add (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x))
    (U : Opens X) (s₁ s₂ : ((skyscraperFunctorCommRing S x).obj T).val.obj (op U))
    (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x T U (s₁ + s₂) hx =
      skyscraperSectionCommRingEquiv S x T U s₁ hx +
        skyscraperSectionCommRingEquiv S x T U s₂ hx :=
  (rfl)

/-- Scalar multiplication on sections of a commutative-ring skyscraper sheaf acts pointwise through
the ring germ map. -/
@[simp]
theorem skyscraperSectionCommRingEquiv_smul (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x))
    (U : Opens X) (r : S.obj.obj (op U))
    (s : ((skyscraperFunctorCommRing S x).obj T).val.obj (op U)) (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x T U (r • s) hx =
      TopCat.Presheaf.germ S.obj U x hx r • skyscraperSectionCommRingEquiv S x T U s hx :=
  (rfl)

/-- Restriction of sections of a commutative-ring skyscraper sheaf acts by restricting the
membership proof. -/
theorem skyscraperSectionCommRingEquiv_map (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x))
    {U V : Opens X} (i : U ⟶ V) (s : ((skyscraperFunctorCommRing S x).obj T).val.obj (op V))
    (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x T U
        (((skyscraperFunctorCommRing S x).obj T).val.map i.op s) hx =
      skyscraperSectionCommRingEquiv S x T V s (i.le hx) :=
  (rfl)

/-- A morphism of `S_x`-modules acts pointwise on sections of the commutative-ring skyscraper
sheaf. -/
theorem skyscraperSectionCommRingEquiv_skyscraperFunctorCommRing_map
    {T₁ T₂ : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)} (f : T₁ ⟶ T₂) (U : Opens X)
    (s : ((skyscraperFunctorCommRing S x).obj T₁).val.obj (op U)) (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x T₂ U
        (((skyscraperFunctorCommRing S x).map f).val.app (op U) s) hx =
      f (skyscraperSectionCommRingEquiv S x T₁ U s hx) :=
  (rfl)

private def stalkSkyscraperCommRingToFun
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (α : (stalkFunctorCommRing S x).obj M ⟶ T) :
    M ⟶ (skyscraperFunctorCommRing S x).obj T :=
  { val :=
      { app := Opposite.rec fun U ↦
          ModuleCat.ofHom
            (X := M.val.obj (op U))
            (Y := ((skyscraperFunctorCommRing S x).obj T).val.obj (op U))
            { toFun := fun m ↦
                (skyscraperSectionCommRingEquiv S x T U).symm fun hx ↦
                  α (TopCat.Presheaf.germ M.val.presheaf U x hx m)
              map_add' := fun m₁ m₂ ↦ by
                apply (skyscraperSectionCommRingEquiv S x T U).injective
                funext hx
                rw [skyscraperSectionCommRingEquiv_add, Equiv.apply_symm_apply,
                  Equiv.apply_symm_apply, Equiv.apply_symm_apply]
                erw [map_add, map_add]
              map_smul' := fun r m ↦ by
                apply (skyscraperSectionCommRingEquiv S x T U).injective
                funext hx
                change α (TopCat.Presheaf.germ M.val.presheaf U x hx (r • m)) =
                  TopCat.Presheaf.germ S.obj U x hx r •
                    α (TopCat.Presheaf.germ M.val.presheaf U x hx m)
                erw [PresheafOfModules.germ_smul (R := S.obj) M.val x U hx r m]
                exact map_smul α.hom _ _ }
        naturality := fun {U V} i ↦ by
          induction U with | op U =>
          induction V with | op V =>
          ext m
          apply (skyscraperSectionCommRingEquiv S x T V).injective
          funext hx
          change skyscraperSectionCommRingEquiv S x T V
              ((skyscraperSectionCommRingEquiv S x T V).symm fun hx ↦
                α (TopCat.Presheaf.germ M.val.presheaf V x hx (M.val.map i m))) hx =
            skyscraperSectionCommRingEquiv S x T V
              (((skyscraperFunctorCommRing S x).obj T).val.map i.unop.op
                ((skyscraperSectionCommRingEquiv S x T U).symm fun hx ↦
                  α (TopCat.Presheaf.germ M.val.presheaf U x hx m))) hx
          rw [skyscraperSectionCommRingEquiv_map S x T i.unop, Equiv.apply_symm_apply,
            Equiv.apply_symm_apply]
          erw [TopCat.Presheaf.germ_res_apply M.val.presheaf i.unop x hx m] } }

private lemma stalkSkyscraperCommRingToFun_app
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (α : (stalkFunctorCommRing S x).obj M ⟶ T) (U : Opens X) (m : M.val.obj (op U))
    (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x T U
      ((stalkSkyscraperCommRingToFun S x α).val.app (op U) m) hx =
      α (TopCat.Presheaf.germ M.val.presheaf U x hx m) :=
  congrFun (Equiv.apply_symm_apply _ _) hx

private def stalkSkyscraperCommRingInvSection
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (β : M ⟶ (skyscraperFunctorCommRing S x).obj T) (U : Opens X) (hx : x ∈ U) :
    M.val.obj (op U) →+ T :=
  AddMonoidHom.mk'
    (fun m ↦ skyscraperSectionCommRingEquiv S x T U (β.val.app (op U) m) hx)
    (fun a b ↦ by rw [map_add, skyscraperSectionCommRingEquiv_add])

private lemma stalkSkyscraperCommRingInvSection_res
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (β : M ⟶ (skyscraperFunctorCommRing S x).obj T) {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (m : M.val.obj (op V)) :
    stalkSkyscraperCommRingInvSection S x β U hx (M.val.map i.op m) =
      stalkSkyscraperCommRingInvSection S x β V (i.le hx) m := by
  dsimp only [stalkSkyscraperCommRingInvSection, AddMonoidHom.mk'_apply]
  have h := PresheafOfModules.naturality_apply β.val i.op m
  exact (congrArg (fun t ↦ skyscraperSectionCommRingEquiv S x T U t hx) h).trans
    (skyscraperSectionCommRingEquiv_map S x T i (β.val.app (op V) m) hx)

private lemma stalkSkyscraperCommRingInvSection_smul
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (β : M ⟶ (skyscraperFunctorCommRing S x).obj T) (U : Opens X) (hx : x ∈ U)
    (r : S.obj.obj (op U)) (m : M.val.obj (op U)) :
    stalkSkyscraperCommRingInvSection S x β U hx (r • m) =
      TopCat.Presheaf.germ S.obj U x hx r •
        stalkSkyscraperCommRingInvSection S x β U hx m := by
  change skyscraperSectionCommRingEquiv S x T U (β.val.app (op U) (r • m)) hx =
    TopCat.Presheaf.germ S.obj U x hx r •
      skyscraperSectionCommRingEquiv S x T U (β.val.app (op U) m) hx
  have hsmul : β.val.app (op U) (r • m) = r • β.val.app (op U) m :=
    (β.val.app (op U)).hom.map_smul r m
  rw [hsmul]
  exact skyscraperSectionCommRingEquiv_smul S x T U r (β.val.app (op U) m) hx

private def stalkSkyscraperCommRingInvFun
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (β : M ⟶ (skyscraperFunctorCommRing S x).obj T) :
    (stalkFunctorCommRing S x).obj M ⟶ T :=
  ModuleCat.ofHom <|
    PresheafOfModules.stalkLiftCommRing (S := S.obj) (N := M.val) x
      (stalkSkyscraperCommRingInvSection S x β)
      (stalkSkyscraperCommRingInvSection_res S x β)
      (stalkSkyscraperCommRingInvSection_smul S x β)

private lemma stalkSkyscraperCommRingInvFun_germ
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (β : M ⟶ (skyscraperFunctorCommRing S x).obj T) (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) :
    stalkSkyscraperCommRingInvFun S x β (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperSectionCommRingEquiv S x T U (β.val.app (op U) m) hx :=
  PresheafOfModules.stalkLiftCommRing_germ (S := S.obj) (N := M.val) x
    (stalkSkyscraperCommRingInvSection S x β)
    (stalkSkyscraperCommRingInvSection_res S x β)
    (stalkSkyscraperCommRingInvSection_smul S x β) U hx m

/-- The commutative-ring stalk functor at `x` is left adjoint to the commutative-ring skyscraper
module sheaf functor at `x`. -/
def stalkSkyscraperAdjunctionCommRing :
    stalkFunctorCommRing S x ⊣ skyscraperFunctorCommRing S x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M T ↦
        { toFun := stalkSkyscraperCommRingToFun S x
          invFun := stalkSkyscraperCommRingInvFun S x
          left_inv := fun α ↦ by
            ext m
            obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
            exact (stalkSkyscraperCommRingInvFun_germ S x _ U hx m).trans
              (stalkSkyscraperCommRingToFun_app S x α U m hx)
          right_inv := fun β ↦ by
            ext U m
            induction U with | op U =>
            apply (skyscraperSectionCommRingEquiv S x T U).injective
            funext hx
            exact (stalkSkyscraperCommRingToFun_app S x _ U m hx).trans
              (stalkSkyscraperCommRingInvFun_germ S x β U hx m) }
      homEquiv_naturality_left_symm := fun {M₁ M₂ T} f β ↦ by
        ext m
        obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M₁.val.presheaf m
        change stalkSkyscraperCommRingInvFun S x (f ≫ β)
            (TopCat.Presheaf.germ M₁.val.presheaf U x hx m) =
          stalkSkyscraperCommRingInvFun S x β
            ((stalkFunctorCommRing S x).map f (TopCat.Presheaf.germ M₁.val.presheaf U x hx m))
        erw [stalkFunctorCommRing_map_germ, stalkSkyscraperCommRingInvFun_germ,
          stalkSkyscraperCommRingInvFun_germ]
        rfl
      homEquiv_naturality_right := fun {M T₁ T₂} α f ↦ by
        ext U m
        induction U with | op U =>
        apply (skyscraperSectionCommRingEquiv S x T₂ U).injective
        funext hx
        change skyscraperSectionCommRingEquiv S x T₂ U
            ((stalkSkyscraperCommRingToFun S x (α ≫ f)).val.app (op U) m) hx =
          skyscraperSectionCommRingEquiv S x T₂ U
            (((skyscraperFunctorCommRing S x).map f).val.app (op U)
              ((stalkSkyscraperCommRingToFun S x α).val.app (op U) m)) hx
        rw [stalkSkyscraperCommRingToFun_app,
          skyscraperSectionCommRingEquiv_skyscraperFunctorCommRing_map,
          stalkSkyscraperCommRingToFun_app]
        rfl }

/-- The forward direction of `stalkSkyscraperAdjunctionCommRing.homEquiv` evaluates on a section
over `U` by taking its germ at `x` and applying `α`. -/
theorem stalkSkyscraperAdjunctionCommRing_homEquiv_apply
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (α : (stalkFunctorCommRing S x).obj M ⟶ T) (U : Opens X) (m : M.val.obj (op U))
    (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x T U
      (((stalkSkyscraperAdjunctionCommRing S x).homEquiv M T α).val.app (op U) m) hx =
      α (TopCat.Presheaf.germ M.val.presheaf U x hx m) := by
  rw [stalkSkyscraperAdjunctionCommRing, Adjunction.mkOfHomEquiv_homEquiv]
  exact stalkSkyscraperCommRingToFun_app S x α U m hx

/-- The inverse direction of `stalkSkyscraperAdjunctionCommRing.homEquiv` sends the germ of `m`
over `U` to the value at `x` of `β_U(m)`. -/
theorem stalkSkyscraperAdjunctionCommRing_homEquiv_symm_germ
    {M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)}
    {T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk S.obj x)}
    (β : M ⟶ (skyscraperFunctorCommRing S x).obj T) (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) :
    ((stalkSkyscraperAdjunctionCommRing S x).homEquiv M T).symm β
        (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      skyscraperSectionCommRingEquiv S x T U (β.val.app (op U) m) hx := by
  rw [stalkSkyscraperAdjunctionCommRing, Adjunction.mkOfHomEquiv_homEquiv]
  exact stalkSkyscraperCommRingInvFun_germ S x β U hx m

/-- The unit of `stalkSkyscraperAdjunctionCommRing` evaluates a section over `U ∋ x` to its germ
at `x`. -/
theorem stalkSkyscraperAdjunctionCommRing_unit_app_val_app
    (M : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S))
    (U : Opens X) (m : M.val.obj (op U)) (hx : x ∈ U) :
    skyscraperSectionCommRingEquiv S x ((stalkFunctorCommRing S x).obj M) U
      (((stalkSkyscraperAdjunctionCommRing S x).unit.app M).val.app (op U) m) hx =
      TopCat.Presheaf.germ M.val.presheaf U x hx m := by
  rw [← (stalkSkyscraperAdjunctionCommRing S x).homEquiv_id M]
  exact stalkSkyscraperAdjunctionCommRing_homEquiv_apply S x (𝟙 _) U m hx

/-- A morphism of sheaves of modules over a sheaf of commutative rings is an isomorphism if its
induced commutative-ring stalk map is an isomorphism at every point. -/
theorem isIso_of_stalkFunctorCommRing_map_isIso
    {M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)} (f : M ⟶ N)
    (hf : ∀ x : X, IsIso ((stalkFunctorCommRing S x).map f)) : IsIso f := by
  have : IsIso ((toSheaf (TauCeti.SheafOfModules.ringCatSheaf S)).map f) := by
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (C := AddCommGrpCat.{u}) (X := X)]
    intro x
    rw [ConcreteCategory.isIso_iff_bijective, ← stalkFunctorCommRing_map_coe_eq S x f]
    have := hf x
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact isIso_of_reflects_iso f (toSheaf (TauCeti.SheafOfModules.ringCatSheaf S))

/-- A morphism of sheaves of modules over a sheaf of commutative rings is an isomorphism if and
only if its induced commutative-ring stalk map is an isomorphism at every point. -/
theorem isIso_iff_stalkFunctorCommRing_map_isIso
    {M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf S)} (f : M ⟶ N) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctorCommRing S x).map f) :=
  ⟨fun _ _ ↦ inferInstance, isIso_of_stalkFunctorCommRing_map_isIso S f⟩

end CommRingCat

end SheafOfModules

end
