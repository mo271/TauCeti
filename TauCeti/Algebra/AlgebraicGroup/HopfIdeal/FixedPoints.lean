/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.FixedPoints
public import TauCeti.RingTheory.Smooth.FixedPoints

/-!
# Fixed-point closed subgroup schemes and Edixhoven's smoothness theorem for affine groups

Let a family of group-scheme endomorphisms act on an affine group scheme `G = Spec H` over a
commutative ring `R` — contravariantly, let `f : ι → (H ⟶ H)` be a family of endomorphisms in
`CommHopfAlgCat R`. The **fixed-point Hopf ideal** `fixedPointHopfIdeal f` is the supremum of the
equalizer Hopf ideals `equalizerHopfIdeal (f i) (𝟙 H)` (wrapping the unbundled construction in
`TauCeti.Algebra.HopfAlgebra.HopfIdeal.FixedPoints`). Because suprema and equalizers of Hopf ideals
are Hopf ideals, the quotient `quotient H (fixedPointHopfIdeal f)` is a commutative Hopf algebra
representing a *closed subgroup scheme* `G^f ⊆ G` whose `A`-points are the `A`-points of `G` fixed
by every `f i` (`mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`,
`range_mapDomain_mkQuotient_fixedPointHopfIdeal`).

When a finite group `Θ` of order invertible in `R` acts on a smooth commutative Hopf algebra `H` by
Hopf-algebra automorphisms `ρ : Θ →* CategoryTheory.Aut H`, the underlying ideal of
`fixedPointHopfIdeal` coincides with `TauCeti.MulSemiringAction.fixedPointIdeal Θ H`. Edixhoven's
smoothness theorem (`TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal`) therefore makes the
fixed-point closed subgroup scheme smooth over `R`
(`CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal`,
`FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints`,
`FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`).

We also record two structural computations (see
`TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Inversion` for the `𝔾ₘ`-inversion example):
* Trivial actions have vanishing fixed-point Hopf ideal and leave the group unchanged
  (`FiniteTypeCommHopfAlgCat.fixedPointsIsoOfEqOne`).
* On the product `G × G` (`H ⊗[R] H`), the fixed-point subgroup of the factor-swapping involution
  is isomorphic to the diagonal `G` via multiplication (`CommHopfAlgCat.quotientSwapEqualizerIso`).

## Main definitions

* `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal` and `TauCeti.CommHopfAlgCat.liftFixedPoints`: the
  categorical fixed-point Hopf ideal and its universal property.
* `CommHopfAlgCat.quotientSwapEqualizerIso`: diagonal identification for the swap involution
  `CommHopfAlgCat.tensorSwapEnd` on `H ⊗[R] H`.
* `TauCeti.FiniteTypeCommHopfAlgCat.fixedPoints`,
  `TauCeti.FiniteTypeCommHopfAlgCat.mkFixedPoints`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.liftFixedPoints`: the fixed-point quotient object, quotient
  morphism, and coequalizer universal property in `FiniteTypeCommHopfAlgCat R` for
  `ρ : Θ →* CategoryTheory.Aut H`.

## Main results

* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff` and
  `TauCeti.FiniteTypeCommHopfAlgCat.range_mapDomain_mkFixedPoints`: characterization of `A`-points
  of the fixed-point closed subgroup scheme.
* `TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints` and
  `TauCeti.FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`: Edixhoven's theorem for smooth
  affine group schemes of finite type under finite groups of invertible order.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
* J. S. Milne, *Algebraic Groups* (2017), §1.h.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H T : _root_.CommHopfAlgCat.{v} R} {ι : Type w}

/-- The **fixed-point Hopf ideal** of a family `f : ι → (H ⟶ H)` of endomorphisms in
`CommHopfAlgCat R`. Contravariantly, its quotient represents the closed subgroup scheme of `Spec H`
fixed by every endomorphism in the family. -/
noncomputable def fixedPointHopfIdeal (f : ι → (H ⟶ H)) : HopfIdeal R H :=
  HopfIdeal.fixedPoints fun i ↦ (f i).hom

/-- `fixedPointHopfIdeal f` is the unbundled `HopfIdeal.fixedPoints` of the underlying bialgebra
endomorphisms. -/
theorem fixedPointHopfIdeal_def (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = HopfIdeal.fixedPoints fun i ↦ (f i).hom :=
  (rfl)

/-- The ideal underlying `fixedPointHopfIdeal f` is spanned by all displacements
`(f i).hom a - a`. -/
@[simp]
theorem fixedPointHopfIdeal_toIdeal (f : ι → (H ⟶ H)) :
    (fixedPointHopfIdeal f).toIdeal =
      Ideal.span {y : H | ∃ (i : ι) (a : H), (f i).hom a - a = y} := by
  rw [fixedPointHopfIdeal_def, HopfIdeal.fixedPoints_toIdeal]

/-- Every displacement `(f i).hom a - a` belongs to `fixedPointHopfIdeal f`. -/
theorem sub_mem_fixedPointHopfIdeal (f : ι → (H ⟶ H)) (i : ι) (a : H) :
    (f i).hom a - a ∈ fixedPointHopfIdeal f :=
  HopfIdeal.sub_mem_fixedPoints (fun i ↦ (f i).hom) i a

/-- Universal property of `fixedPointHopfIdeal f` among Hopf ideals of `H`. -/
theorem fixedPointHopfIdeal_le_iff {f : ι → (H ⟶ H)} {J : HopfIdeal R H} :
    fixedPointHopfIdeal f ≤ J ↔ ∀ (i : ι) (a : H), (f i).hom a - a ∈ J :=
  HopfIdeal.fixedPoints_le_iff

/-- A ring homomorphism out of `H` kills `fixedPointHopfIdeal f` if and only if it equalizes every
`(f i).hom` with the identity. -/
theorem fixedPointHopfIdeal_le_ker_iff {A : Type*} [Ring A] (f : ι → (H ⟶ H)) (φ : H →+* A) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker φ ↔
      ∀ (i : ι) (a : H), φ ((f i).hom a) = φ a :=
  HopfIdeal.fixedPoints_le_ker_iff (fun i ↦ (f i).hom) φ

/-- `fixedPointHopfIdeal f` is the supremum of `equalizerHopfIdeal (f i) (𝟙 H)`. -/
theorem fixedPointHopfIdeal_eq_iSup (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H) := by
  rw [fixedPointHopfIdeal_def, HopfIdeal.fixedPoints_eq_iSup]
  simp_rw [equalizerHopfIdeal_def]
  rfl

/-- A morphism `p : H ⟶ T` kills `fixedPointHopfIdeal f` if and only if it coequalizes every `f i`
with `𝟙 H`. -/
theorem fixedPointHopfIdeal_toIdeal_le_ker_iff (f : ι → (H ⟶ H)) (p : H ⟶ T) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker p.hom.toAlgHom.toRingHom ↔
      ∀ i, f i ≫ p = p := by
  rw [fixedPointHopfIdeal_eq_iSup, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  refine forall_congr' fun i ↦ ?_
  simpa only [Category.id_comp] using equalizerHopfIdeal_toIdeal_le_ker_iff (f i) (𝟙 H) p

/-- `fixedPointHopfIdeal f` vanishes if and only if every `f i` is the identity morphism. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_iff (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⊥ ↔ ∀ i, f i = 𝟙 H := by
  rw [fixedPointHopfIdeal_def, HopfIdeal.fixedPoints_eq_bot_iff]
  exact forall_congr' fun i ↦ ⟨fun h ↦ _root_.CommHopfAlgCat.hom_ext h, fun h ↦ by rw [h]; rfl⟩

/-- The quotient morphism `H ⟶ quotient H (fixedPointHopfIdeal f)` coequalizes every `f i` with
`𝟙 H`. -/
@[reassoc]
theorem comp_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H)) (i : ι) :
    f i ≫ mkQuotient H (fixedPointHopfIdeal f) = mkQuotient H (fixedPointHopfIdeal f) :=
  ((fixedPointHopfIdeal_toIdeal_le_ker_iff f
    (mkQuotient H (fixedPointHopfIdeal f))).mp (mkQuotient_ker H _).ge) i

/-- Universal property of the fixed-point quotient in `CommHopfAlgCat R`: any morphism `p : H ⟶ T`
satisfying `f i ≫ p = p` for all `i` factors through `quotient H (fixedPointHopfIdeal f)`. -/
noncomputable def liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ T) (hp : ∀ i, f i ≫ p = p) :
    quotient H (fixedPointHopfIdeal f) ⟶ T :=
  liftQuotient (fixedPointHopfIdeal f) p ((fixedPointHopfIdeal_toIdeal_le_ker_iff f p).mpr hp)

@[reassoc (attr := simp)]
theorem mkQuotient_comp_liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ T)
    (hp : ∀ i, f i ≫ p = p) :
    mkQuotient H (fixedPointHopfIdeal f) ≫ liftFixedPoints p hp = p :=
  mkQuotient_comp_liftQuotient _ _ _

theorem liftFixedPoints_unique {f : ι → (H ⟶ H)} (p : H ⟶ T) (hp : ∀ i, f i ≫ p = p)
    (q : quotient H (fixedPointHopfIdeal f) ⟶ T)
    (hq : mkQuotient H (fixedPointHopfIdeal f) ≫ q = p) :
    q = liftFixedPoints p hp :=
  liftQuotient_unique _ _ _ q hq

/-- On `A`-points, the closed subgroup cut out by `fixedPointHopfIdeal f` consists of those points
fixed by every `BialgHom.mapDomain (f i).hom`. -/
theorem mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff (f : ι → (H ⟶ H))
    (A : CommAlgCat.{x} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H (fixedPointHopfIdeal f) A ↔
      ∀ i, BialgHom.mapDomain (f i).hom g = g := by
  have hker (I : HopfIdeal R H) :
      g ∈ quotientPointsSubgroup H I A ↔
        I.toIdeal ≤ RingHom.ker (g.ofConv : H →ₐ[R] A).toRingHom := by
    rw [mem_quotientPointsSubgroup_iff]
    exact ⟨fun h x hx ↦ RingHom.mem_ker.mpr (h x (HopfIdeal.mem_toIdeal.mp hx)),
      fun h x hx ↦ RingHom.mem_ker.mp (h (HopfIdeal.mem_toIdeal.mpr hx))⟩
  rw [hker, fixedPointHopfIdeal_eq_iSup, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  refine forall_congr' fun i ↦ ?_
  have hid : (𝟙 H : H ⟶ H).hom = BialgHom.id R H := rfl
  rw [← hker, mem_quotientPointsSubgroup_equalizerHopfIdeal_iff, hid, BialgHom.mapDomain_id,
    MonoidHom.id_apply]

/-- Image-of-`mapDomain` form of `mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`: for every
commutative `R`-algebra `A`, the `A`-points of `quotient H (fixedPointHopfIdeal f)` map onto the
subset of `A`-points of `H` fixed by every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H))
    (A : Type x) [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom) =
      {g : WithConv (H →ₐ[R] A) | ∀ i, BialgHom.mapDomain (A := A) (f i).hom g = g} := by
  have hfun :
      (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom :
        HopfAlgebra.points (R := R) (H := quotient H (fixedPointHopfIdeal f))
          (CommAlgCat.of R A) →
        HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R A)) =
      quotientPointsHom H (fixedPointHopfIdeal f) (CommAlgCat.of R A) := by
    funext y
    rw [BialgHom.mapDomain_apply, quotientPointsHom_apply]
  ext g
  rw [hfun, Set.mem_ofPred_eq]
  exact (mem_range_quotientPointsHom_iff H (fixedPointHopfIdeal f) (CommAlgCat.of R A) g).trans
    ((mem_quotientPointsSubgroup_iff H (fixedPointHopfIdeal f) (CommAlgCat.of R A) g).symm.trans
      (mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff f (CommAlgCat.of R A) g))

/-- **Edixhoven's smoothness theorem for commutative Hopf algebras.** If a finite group `Θ` with
`(Nat.card Θ : R)` invertible acts on a smooth commutative Hopf algebra `H` by Hopf-algebra
automorphisms `ρ : Θ →* CategoryTheory.Aut H`, then the fixed-point quotient Hopf algebra is
smooth over `R`. -/
theorem smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal
    {H : _root_.CommHopfAlgCat.{v} R} (hH : smoothCommHopfAlgProperty R H)
    {Θ : Type w} [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R
      (quotient H (fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom)) := by
  let _ : Algebra.Smooth R H := (smoothCommHopfAlgProperty_iff H).mp hH
  let actHom : Θ →* (H ≃ₐ[R] H) := H.autToAlgEquivHom.comp ρ
  let _ : MulSemiringAction Θ H := MulSemiringAction.compHom H actHom
  have : SMulCommClass Θ R H :=
    ⟨fun θ r a ↦ by
      rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, AlgEquiv.smul_def,
        AlgEquiv.smul_def, map_smul]⟩
  have hI : (fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom).toIdeal =
      MulSemiringAction.fixedPointIdeal Θ H :=
    HopfIdeal.fixedPoints_toIdeal_eq_fixedPointIdeal _ fun θ a ↦ by
      rw [MulAction.compHom_smul_def, MonoidHom.comp_apply, AlgEquiv.smul_def,
        _root_.CommHopfAlgCat.autToAlgEquivHom_apply]
  let _ : Algebra.Smooth R (H ⧸ MulSemiringAction.fixedPointIdeal Θ H) :=
    MulSemiringAction.smooth_quotient_fixedPointIdeal hΘ
  rw [smoothCommHopfAlgProperty_iff]
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq R hI.symm)

end CommHopfAlgCat

end TauCeti

namespace CommHopfAlgCat

universe u v
variable {R : Type u} [CommRing R]

/-- The factor-swapping endomorphism of `H ⊗[R] H` in `CommHopfAlgCat R`. -/
noncomputable abbrev tensorSwapEnd (H : _root_.CommHopfAlgCat.{v} R) :
    _root_.CommHopfAlgCat.of R (H ⊗[R] H) ⟶ _root_.CommHopfAlgCat.of R (H ⊗[R] H) :=
  _root_.CommHopfAlgCat.ofHom (_root_.Bialgebra.TensorProduct.comm R H H).toBialgHom

/-- The underlying ideal of the swap equalizer Hopf ideal on `H ⊗[R] H` equals the kernel of the
multiplication map `Algebra.TensorProduct.lmul' R`. -/
theorem equalizerHopfIdeal_tensorSwapEnd_toIdeal (H : _root_.CommHopfAlgCat.{v} R) :
    (TauCeti.CommHopfAlgCat.equalizerHopfIdeal H.tensorSwapEnd (𝟙 _)).toIdeal =
      RingHom.ker (Algebra.TensorProduct.lmul' R (S := H)) := by
  rw [← TauCeti.MulSemiringAction.fixedPointIdeal_tensorSwapSubgroup_eq_ker_lmul' R H,
    TauCeti.CommHopfAlgCat.equalizerHopfIdeal_toIdeal, TauCeti.HopfIdeal.equalizerIdeal_eq_span,
    TauCeti.MulSemiringAction.fixedPointIdeal_zpowers_eq_span]
  rfl

/-- **Diagonal fixed-point subgroup of `G × G`.** For any commutative Hopf algebra `H`, the
quotient of `H ⊗[R] H` by the equalizer Hopf ideal of the swap involution is isomorphic in
`CommHopfAlgCat R` to `H` via coordinate multiplication `_root_.Bialgebra.mulBialgHom R H`. -/
noncomputable def quotientSwapEqualizerIso (H : _root_.CommHopfAlgCat.{v} R) :
    _root_.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R (H ⊗[R] H))
      (TauCeti.CommHopfAlgCat.equalizerHopfIdeal H.tensorSwapEnd (𝟙 _)) ≅ H := by
  let mulHom : _root_.CommHopfAlgCat.of R (H ⊗[R] H) ⟶ H :=
    _root_.CommHopfAlgCat.ofHom (_root_.Bialgebra.mulBialgHom R H)
  have hsurj : Function.Surjective mulHom.hom := fun a ↦
    ⟨a ⊗ₜ[R] 1, by simp [mulHom]⟩
  refine _root_.CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq mulHom hsurj ?_
  have hto : (TauCeti.HopfIdeal.kerOfSurjective mulHom.hom hsurj).toIdeal =
      (TauCeti.CommHopfAlgCat.equalizerHopfIdeal H.tensorSwapEnd (𝟙 _)).toIdeal := by
    rw [TauCeti.HopfIdeal.kerOfSurjective_toIdeal, H.equalizerHopfIdeal_tensorSwapEnd_toIdeal]
    simp [mulHom]
  exact TauCeti.HopfIdeal.ext fun x ↦ by
    rw [← TauCeti.HopfIdeal.mem_toIdeal, ← TauCeti.HopfIdeal.mem_toIdeal, hto]

/-- The forward morphism of `quotientSwapEqualizerIso H` factors coordinate multiplication
`Bialgebra.mulBialgHom R H` through the swap-equalizer quotient. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_quotientSwapEqualizerIso_hom (H : _root_.CommHopfAlgCat.{v} R) :
    _root_.CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R (H ⊗[R] H))
        (TauCeti.CommHopfAlgCat.equalizerHopfIdeal H.tensorSwapEnd (𝟙 _)) ≫
      H.quotientSwapEqualizerIso.hom =
    _root_.CommHopfAlgCat.ofHom (_root_.Bialgebra.mulBialgHom R H) := by
  rw [quotientSwapEqualizerIso]
  exact _root_.CommHopfAlgCat.Hom.mkQuotient_comp_quotientIsoOfKerOfSurjectiveEq_hom _ _ _

/-- Precomposing the inverse of `quotientSwapEqualizerIso H` with coordinate multiplication
recovers the swap-equalizer quotient morphism. -/
@[reassoc (attr := simp)]
theorem ofHom_mulBialgHom_comp_quotientSwapEqualizerIso_inv (H : _root_.CommHopfAlgCat.{v} R) :
    _root_.CommHopfAlgCat.ofHom (_root_.Bialgebra.mulBialgHom R H) ≫
      H.quotientSwapEqualizerIso.inv =
    _root_.CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R (H ⊗[R] H))
      (TauCeti.CommHopfAlgCat.equalizerHopfIdeal H.tensorSwapEnd (𝟙 _)) := by
  rw [quotientSwapEqualizerIso]
  exact _root_.CommHopfAlgCat.Hom.comp_quotientIsoOfKerOfSurjectiveEq_inv _ _ _

end CommHopfAlgCat

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u v w x
variable {R : Type u} [CommRing R]

/-- The fixed-point Hopf ideal of a monoid action `ρ : Θ →* CategoryTheory.Aut H` on a finite-type
commutative Hopf algebra `H`. -/
noncomputable def fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) : HopfIdeal R H :=
  CommHopfAlgCat.fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom.hom

theorem fixedPointHopfIdeal_def {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    fixedPointHopfIdeal ρ = CommHopfAlgCat.fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom.hom :=
  (rfl)

/-- The fixed-point closed subgroup scheme of `ρ : Θ →* CategoryTheory.Aut H`, represented as a
bundled object of `FiniteTypeCommHopfAlgCat R`. -/
noncomputable abbrev fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  quotient H (fixedPointHopfIdeal ρ)

theorem fixedPoints_def {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    fixedPoints ρ = quotient H (fixedPointHopfIdeal ρ) :=
  (rfl)

theorem fixedPoints_obj {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    (fixedPoints ρ).obj = _root_.CommHopfAlgCat.quotient H.obj (fixedPointHopfIdeal ρ) :=
  (rfl)

/-- The surjective coordinate morphism `H ⟶ fixedPoints ρ` in `FiniteTypeCommHopfAlgCat R`,
representing the closed immersion `(Spec H)^Θ ↪ Spec H`. -/
noncomputable def mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) : H ⟶ fixedPoints ρ :=
  mkQuotient H (fixedPointHopfIdeal ρ)

/-- Under the forgetful functor to `CommHopfAlgCat R`, `mkFixedPoints ρ` maps to
`CommHopfAlgCat.mkQuotient H.obj (fixedPointHopfIdeal ρ)`. -/
theorem forget₂_commHopfAlgCat_map_mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
      (mkFixedPoints ρ) = _root_.CommHopfAlgCat.mkQuotient H.obj (fixedPointHopfIdeal ρ) :=
  (rfl)

@[simp]
theorem mkFixedPoints_hom {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    (mkFixedPoints ρ).hom = _root_.CommHopfAlgCat.mkQuotient H.obj (fixedPointHopfIdeal ρ) :=
  (rfl)

/-- `mkFixedPoints ρ` coequalizes every `(ρ θ).asIso.hom` with `𝟙 H`. -/
@[reassoc]
theorem comp_mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) (θ : Θ) :
    (ρ θ).asIso.hom ≫ mkFixedPoints ρ = mkFixedPoints ρ := by
  apply ObjectProperty.hom_ext
  exact CommHopfAlgCat.comp_mkQuotient_fixedPointHopfIdeal (fun θ' ↦ (ρ θ').asIso.hom.hom) θ

/-- The kernel of `mkFixedPoints ρ` is the underlying ideal of `fixedPointHopfIdeal ρ`. -/
theorem mkFixedPoints_ker {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    RingHom.ker (toBialgHom (mkFixedPoints ρ)).toAlgHom.toRingHom =
      (fixedPointHopfIdeal ρ).toIdeal :=
  mkQuotient_ker H (fixedPointHopfIdeal ρ)

/-- Morphisms out of `fixedPoints ρ` are determined by precomposition with `mkFixedPoints ρ`. -/
@[ext]
theorem mkFixedPoints_hom_ext {H T : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H}
    {f g : fixedPoints ρ ⟶ T} (h : mkFixedPoints ρ ≫ f = mkFixedPoints ρ ≫ g) :
    f = g :=
  mkQuotient_hom_ext h

/-- Coequalizer universal property of `fixedPoints ρ` in `FiniteTypeCommHopfAlgCat R`: any morphism
`p : H ⟶ T` coequalizing every `(ρ θ).asIso.hom` with `𝟙 H` factors uniquely through
`mkFixedPoints ρ`. -/
noncomputable def liftFixedPoints {H T : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H}
    (p : H ⟶ T) (hp : ∀ θ, (ρ θ).asIso.hom ≫ p = p) :
    fixedPoints ρ ⟶ T :=
  ObjectProperty.homMk <|
    CommHopfAlgCat.liftFixedPoints (f := fun θ ↦ (ρ θ).asIso.hom.hom) p.hom
      fun θ ↦ congrArg (fun q ↦ q.hom) (hp θ)

@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_liftFixedPoints {H T : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H}
    (p : H ⟶ T) (hp : ∀ θ, (ρ θ).asIso.hom ≫ p = p) :
    mkFixedPoints ρ ≫ liftFixedPoints p hp = p := by
  apply ObjectProperty.hom_ext
  exact CommHopfAlgCat.mkQuotient_comp_liftFixedPoints (f := fun θ ↦ (ρ θ).asIso.hom.hom) p.hom
    fun θ ↦ congrArg (fun q ↦ q.hom) (hp θ)

theorem liftFixedPoints_unique {H T : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H}
    (p : H ⟶ T) (hp : ∀ θ, (ρ θ).asIso.hom ≫ p = p)
    (q : fixedPoints ρ ⟶ T) (hq : mkFixedPoints ρ ≫ q = p) :
    q = liftFixedPoints p hp :=
  mkFixedPoints_hom_ext (hq.trans (mkFixedPoints_comp_liftFixedPoints p hp).symm)

/-- The coordinate map `H ⟶ fixedPoints ρ` is surjective. -/
theorem mkFixedPoints_surjective {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    Function.Surjective (toBialgHom (mkFixedPoints ρ)) :=
  _root_.CommHopfAlgCat.mkQuotient_surjective H.obj (fixedPointHopfIdeal ρ)

/-- For every commutative `R`-algebra `A`, precomposition with `mkFixedPoints ρ` identifies the
`A`-points of `fixedPoints ρ` with the `A`-points of `H` fixed by every `ρ θ`. -/
theorem range_mapDomain_mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (A : Type x) [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (toBialgHom (mkFixedPoints ρ))) =
      {g : WithConv (H →ₐ[R] A) |
        ∀ θ : Θ, BialgHom.mapDomain (A := A) (toBialgHom (ρ θ).asIso.hom) g = g} :=
  CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal
    (fun θ ↦ (ρ θ).asIso.hom.hom) A

/-- When `ρ = 1` is the trivial action, `fixedPointHopfIdeal ρ` vanishes. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_of_eq_one {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    fixedPointHopfIdeal ρ = ⊥ := by
  subst hρ
  rw [fixedPointHopfIdeal_def, CommHopfAlgCat.fixedPointHopfIdeal_eq_bot_iff]
  intro _θ
  simp

/-- When `ρ = 1` is the trivial action, `fixedPoints ρ` is canonically isomorphic to `H` in
`FiniteTypeCommHopfAlgCat R`. -/
noncomputable def fixedPointsIsoOfEqOne {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    fixedPoints ρ ≅ H :=
  eqToIso (congrArg (quotient H) (fixedPointHopfIdeal_eq_bot_of_eq_one hρ)) ≪≫
    quotientBotIso H

@[simp]
theorem fixedPointsIsoOfEqOne_inv {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    (fixedPointsIsoOfEqOne hρ).inv = mkFixedPoints ρ := by
  rw [fixedPointsIsoOfEqOne, Iso.trans_inv, quotientBotIso_inv, eqToIso.inv, mkFixedPoints]
  exact mkQuotient_comp_eqToHom (fixedPointHopfIdeal_eq_bot_of_eq_one hρ)

@[simp]
theorem fixedPointsIsoOfEqOne_hom {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    (fixedPointsIsoOfEqOne hρ).hom =
      liftFixedPoints (𝟙 H) (fun _θ ↦ by subst hρ; simp) := by
  apply liftFixedPoints_unique
  rw [← fixedPointsIsoOfEqOne_inv hρ, Iso.inv_hom_id]

/-- **Edixhoven's smoothness theorem for finite-type affine group schemes.** Let `H` be a smooth
finite-type commutative Hopf algebra over `R` and let a finite group `Θ` with `(Nat.card Θ : R)`
invertible act on `H` via `ρ : Θ →* CategoryTheory.Aut H`. Then `fixedPoints ρ` is smooth over
`R`. -/
theorem smoothCommHopfAlgProperty_fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    (hH : smoothCommHopfAlgProperty R H.obj) {Θ : Type w} [Group Θ] [Finite Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R (fixedPoints ρ).obj := by
  let ρ' : Θ →* CategoryTheory.Aut H.obj :=
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).mapAut H).comp ρ
  have hI : fixedPointHopfIdeal ρ =
      CommHopfAlgCat.fixedPointHopfIdeal (fun θ ↦ (ρ' θ).asIso.hom) := by
    rw [fixedPointHopfIdeal_def]
    rfl
  rw [fixedPoints_obj, hI]
  exact CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal hH ρ' hΘ

/-- **Edixhoven's theorem (existential closed-subgroup form, Propositions 3.1 and 3.4).** Fixed
points of a finite group `Θ` of invertible order acting on a smooth affine group scheme of finite
type over `R` are represented by a smooth closed subgroup scheme (`fixedPoints ρ`, via the
surjective coordinate Hopf-algebra morphism `mkFixedPoints ρ`). -/
theorem exists_smooth_fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    (hH : smoothCommHopfAlgProperty R H.obj) (Θ : Type w) [Group Θ] [Finite Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} R) (f : H ⟶ H'),
      smoothCommHopfAlgProperty R H'.obj ∧ Function.Surjective (toBialgHom f) ∧
      ∀ (A : Type x) [CommRing A] [Algebra R A],
        Set.range (BialgHom.mapDomain (A := A) (toBialgHom f)) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := A) (toBialgHom (ρ θ).asIso.hom) g = g} :=
  ⟨fixedPoints ρ, mkFixedPoints ρ, smoothCommHopfAlgProperty_fixedPoints hH ρ hΘ,
    mkFixedPoints_surjective ρ, range_mapDomain_mkFixedPoints ρ⟩

end TauCeti.FiniteTypeCommHopfAlgCat
