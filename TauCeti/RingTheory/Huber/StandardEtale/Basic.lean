/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.QuotientMapping
public import TauCeti.RingTheory.Huber.StandardEtale.TateSeries

/-!
# Standard étale presentations of Huber pairs over a complete Tate pair

Let `(A, A⁺)` be a complete Hausdorff Tate pair with pseudouniformiser `ϖ ∈ A`, and let `(C, C⁺)`
be a Huber pair over `A`. Following Huber (§1.6), Scholze (*Étale cohomology of diamonds*, §24),
and Kedlaya–Liu, a *standard étale presentation* of `(C, C⁺)` over `(A, A⁺)` at scale `ϖ` is a
tuple `(N, F, k, π)` (`TauCeti.Huber.StandardEtalePresentation`) consisting of:

* a variable count `N : ℕ` and `N` restricted power series `F₁, …, F_N ∈ A⁺⟨T₁, …, T_N⟩`;
* an exponent `k : ℕ` and an `A`-algebra map `π : A⟨T₁, …, T_N⟩ →ₐ[A] C` that is a topological
  quotient map with kernel equal to the topological closure of `(F₁, …, F_N)`;
* the quotient-pair condition identifying `C⁺` with the integral closure in `C` of
  `π(A⁺⟨T₁, …, T_N⟩)`; and
* invertibility of `π(det (∂Fᵢ/∂Tⱼ))` as a unit `u ∈ Cˣ` with `ϖ ^ k · u⁻¹ ∈ C⁺`.

Because `ker π` is closed and `π` is a topological quotient map of rings, `π` is automatically an
open quotient map, `C` is automatically Hausdorff (`T2Space`), and `(C, C⁺)` is canonically
isomorphic as a Huber pair to the quotient of `(A⟨T⟩, A⁺⟨T⟩)` by the closure of `(F₁, …, F_N)`.
Conversely, any system `F` in `A⁺⟨T₁, …, T_N⟩` whose Jacobian determinant becomes a `ϖ ^ k`-bounded
unit in that quotient yields a standard étale presentation via
`TauCeti.Huber.StandardEtalePresentation.ofQuotient`. In zero variables (`N = 0`, `k = 0`),
`tateSeries.finZeroAlgEquiv` supplies the identity presentation of `(A, A⁺)` over itself
(`TauCeti.Huber.StandardEtalePresentation.identity`).

## Main definitions

* `TauCeti.Huber.StandardEtalePresentation`: standard étale presentation of `(C, C⁺)` over
  `(A, A⁺)` with respect to `ϖ`.
* `TauCeti.Huber.StandardEtalePresentation.jacobian`: the Jacobian determinant `det (∂Fᵢ/∂Tⱼ)` in
  `tateSeries P.N A`.
* `TauCeti.Huber.StandardEtalePresentation.toPairHom`,
  `TauCeti.Huber.StandardEtalePresentation.fromQuotientHom`, and
  `TauCeti.Huber.StandardEtalePresentation.toQuotientHom`: the Huber-pair quotient morphism and its
  mutually inverse comparison morphisms with the canonical quotient pair.
* `TauCeti.Huber.StandardEtalePresentation.ofQuotient`,
  `TauCeti.Huber.StandardEtalePresentation.ofAlgEquiv`, and
  `TauCeti.Huber.StandardEtalePresentation.id`: canonical quotient constructor, transport along a
  topological algebra equivalence, and the zero-variable identity presentation.

## Main results

* `TauCeti.Huber.StandardEtalePresentation.isOpenQuotientMap_π`,
  `TauCeti.Huber.StandardEtalePresentation.t2Space_target`, and
  `TauCeti.Huber.StandardEtalePresentation.isQuotientMapping_toPairHom`: `π` is an open quotient
  map onto a Hausdorff target and defines a quotient mapping of Huber pairs.
* `TauCeti.Huber.StandardEtalePresentation.identity`: `(A, A⁺)` admits a presentation over itself
  with `N = 0` and `k = 0`.

## References

* [R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*][huber1996], §1.6 and
  Proposition 1.7.1.
* [P. Scholze, *Étale cohomology of diamonds*][scholze2017], §24.
* [K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*][kedlaya_liu2015], §3.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Definitions 7.22 and 8.42.
-/

public section

open Topology

namespace TauCeti.Huber

/-- **A standard étale presentation of a Huber pair `(C, C⁺)` over a Tate pair `(A, A⁺)` at scale
`ϖ`.** It presents `(C, C⁺)` as the topological quotient Huber pair of
`(A⟨T₁, …, T_N⟩, A⁺⟨T₁, …, T_N⟩)` by the closure of `(F₁, …, F_N)` for `F₁, …, F_N ∈ A⁺⟨T⟩`
whose Jacobian determinant maps to a unit `u ∈ Cˣ` satisfying `ϖ ^ k · u⁻¹ ∈ C⁺`. -/
structure StandardEtalePresentation {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] (Aplus : Pair A) (ϖ : A)
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] (Cplus : Pair C) where
  /-- `ϖ` is a pseudouniformiser of `A`. -/
  isPseudoUniformizer : IsPseudoUniformizer ϖ
  /-- Number of restricted variables. -/
  N : ℕ
  /-- Defining equations in `A⟨T₁, …, T_N⟩`. -/
  F : Fin N → tateSeries N A
  /-- Each `F i` has coefficients in `A⁺`. -/
  F_mem_plus : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus
  /-- Exponent bounding the inverse Jacobian in `C⁺`. -/
  k : ℕ
  /-- Quotient `A`-algebra map `A⟨T₁, …, T_N⟩ → C`. -/
  π : tateSeries N A →ₐ[A] C
  /-- `π` is a topological quotient map. -/
  isQuotientMap_π : IsQuotientMap π
  /-- The kernel of `π` is the closure of `(F₁, …, F_N)`. -/
  ker_π : RingHom.ker π = (Ideal.span (Set.range F)).closure
  /-- `C⁺` is the integral closure in `C` of `π(A⁺⟨T₁, …, T_N⟩)`. -/
  mem_plus_iff : ∀ c : C, c ∈ Cplus.plus ↔
    ((tateSeriesPlus N A Aplus.plus).map (π : tateSeries N A →+* C)).subtype.IsIntegralElem c
  /-- The Jacobian determinant maps to a unit of `C` whose inverse is bounded in `C⁺` after
  multiplying by `ϖ ^ k`. -/
  exists_unit_jacobian : ∃ J : tateSeries N A,
    (J : MvPowerSeries (Fin N) A) =
      (Matrix.of fun i j ↦ MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A)).det ∧
    ∃ u : Cˣ, (u : C) = π J ∧ algebraMap A C (ϖ ^ k) * ↑u⁻¹ ∈ Cplus.plus

namespace StandardEtalePresentation

section BasicAPI

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsTateRing A] {Aplus : Pair A} {ϖ : A}
  {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [Algebra A C] {Cplus : Pair C}
  (P : StandardEtalePresentation Aplus ϖ Cplus)

/-- Two standard étale presentations are equal if and only if their data `(N, F, k, π)` agree. -/
theorem ext_iff {P Q : StandardEtalePresentation Aplus ϖ Cplus} :
    P = Q ↔ P.N = Q.N ∧ HEq P.F Q.F ∧ P.k = Q.k ∧ HEq P.π Q.π := by
  refine ⟨fun h ↦ by subst h; exact ⟨rfl, .rfl, rfl, .rfl⟩, ?_⟩
  rcases P with ⟨_, NP, FP, _, kP, πP, _, _, _, _⟩
  rcases Q with ⟨_, NQ, FQ, _, kQ, πQ, _, _, _, _⟩
  rintro ⟨rfl, hF, rfl, hπ⟩
  cases eq_of_heq hF
  cases eq_of_heq hπ
  rfl

/-- **The Jacobian determinant `det (∂Fᵢ/∂Tⱼ)` of `P.F`**, as an element of `tateSeries P.N A`. -/
noncomputable abbrev jacobian : tateSeries P.N A :=
  tateSeriesJacobian P.F

/-- Coercion of `P.jacobian` to `MvPowerSeries (Fin P.N) A`. -/
theorem coe_jacobian :
    (P.jacobian : MvPowerSeries (Fin P.N) A) =
      (Matrix.of fun i j ↦ MvPowerSeries.pderiv j (P.F i : MvPowerSeries (Fin P.N) A)).det :=
  coe_tateSeriesJacobian P.F

/-- The Jacobian determinant of `P` has coefficients in `A⁺`. -/
theorem jacobian_mem_plus : P.jacobian ∈ tateSeriesPlus P.N A Aplus.plus :=
  tateSeriesJacobian_mem_tateSeriesPlus P.F_mem_plus

/-- `P.π P.jacobian` is a unit `u ∈ Cˣ` satisfying `ϖ ^ P.k · u⁻¹ ∈ C⁺`. -/
theorem exists_unit_eq_π_jacobian :
    ∃ u : Cˣ, (u : C) = P.π P.jacobian ∧ algebraMap A C (ϖ ^ P.k) * ↑u⁻¹ ∈ Cplus.plus := by
  obtain ⟨J, hJ, u, hu, hbound⟩ := P.exists_unit_jacobian
  have hJP : J = P.jacobian := Subtype.ext (hJ.trans P.coe_jacobian.symm)
  exact ⟨u, hJP ▸ hu, hbound⟩

/-- `P.π P.jacobian` is a unit in `C`. -/
theorem isUnit_π_jacobian : IsUnit (P.π P.jacobian) := by
  obtain ⟨u, hu, -⟩ := P.exists_unit_eq_π_jacobian
  exact hu ▸ u.isUnit

/-- **The canonical unit `u ∈ Cˣ` whose underlying element is `P.π P.jacobian`.** -/
noncomputable def jacobianUnit : Cˣ :=
  P.isUnit_π_jacobian.unit

@[simp]
theorem coe_jacobianUnit : (P.jacobianUnit : C) = P.π P.jacobian :=
  P.isUnit_π_jacobian.unit_spec

/-- The inverse of `P.jacobianUnit` lies in `Cplus.plus` after scaling by `ϖ ^ P.k`. -/
theorem pow_mul_jacobianUnit_inv_mem_plus :
    algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹ ∈ Cplus.plus := by
  obtain ⟨u, hu, hbound⟩ := P.exists_unit_eq_π_jacobian
  have hu_eq : P.jacobianUnit = u := Units.ext (P.coe_jacobianUnit.trans hu.symm)
  exact hu_eq ▸ hbound

/-- The quotient map `P.π` is continuous. -/
theorem continuous_π : Continuous P.π :=
  P.isQuotientMap_π.continuous

/-- The quotient map `P.π` is surjective. -/
theorem surjective_π : Function.Surjective P.π :=
  P.isQuotientMap_π.surjective

/-- Every defining series `P.F i` lies in `RingHom.ker P.π`. -/
theorem F_mem_ker_π (i : Fin P.N) : P.F i ∈ RingHom.ker P.π := by
  rw [P.ker_π, ← SetLike.mem_coe, Ideal.coe_closure]
  exact subset_closure (Ideal.subset_span (Set.mem_range_self i))

/-- `P.π` annihilates each defining series `P.F i`. -/
@[simp]
theorem π_F_eq_zero (i : Fin P.N) : P.π (P.F i) = 0 :=
  RingHom.mem_ker.mp (P.F_mem_ker_π i)

/-- The kernel of `P.π` is closed in `tateSeries P.N A`. -/
theorem isClosed_ker_π : IsClosed (RingHom.ker P.π : Set (tateSeries P.N A)) := by
  rw [P.ker_π, Ideal.coe_closure]
  exact isClosed_closure

/-- **Any ring admitting a standard étale presentation is Hausdorff (`T2Space`)**, because `P.π`
identifies `C` homeomorphically with the quotient of `tateSeries P.N A` by the closed ideal
`RingHom.ker P.π`. -/
theorem t2Space_target (P : StandardEtalePresentation Aplus ϖ Cplus) : T2Space C := by
  let I : Ideal (tateSeries P.N A) := RingHom.ker (P.π : tateSeries P.N A →+* C)
  have : IsClosed (I : Set (tateSeries P.N A)) := P.isClosed_ker_π
  have : T1Space (tateSeries P.N A ⧸ I) := Ideal.Quotient.instT1Space I
  have hhome : IsHomeomorph (RingHom.kerLift (P.π : tateSeries P.N A →+* C)) :=
    (P.π : tateSeries P.N A →+* C).isHomeomorph_kerLift P.isQuotientMap_π
  exact hhome.homeomorph.t2Space

/-- **The presentation map `P.π` is an open quotient map**, since the quotient map onto
`tateSeries P.N A ⧸ ker P.π` is open and `RingHom.kerLift` is a homeomorphism under
`P.isQuotientMap_π`. -/
theorem isOpenQuotientMap_π : IsOpenQuotientMap P.π := by
  let φ : tateSeries P.N A →+* C := P.π
  have hhome : IsHomeomorph (RingHom.kerLift φ) := φ.isHomeomorph_kerLift P.isQuotientMap_π
  have hlift : IsOpenQuotientMap (RingHom.kerLift φ) :=
    ⟨hhome.surjective, hhome.continuous, hhome.isOpenMap⟩
  have hcomp : IsOpenQuotientMap (RingHom.kerLift φ ∘ Ideal.Quotient.mk (RingHom.ker φ)) :=
    hlift.comp (QuotientRing.isOpenQuotientMap_mk (RingHom.ker φ))
  have heq : (RingHom.kerLift φ ∘ Ideal.Quotient.mk (RingHom.ker φ)) = P.π := by
    funext x
    exact RingHom.kerLift_mk φ x
  exact heq ▸ hcomp

/-- The presentation map `P.π` is an open map. -/
theorem isOpenMap_π : IsOpenMap P.π :=
  P.isOpenQuotientMap_π.isOpenMap

/-- Membership in `Cplus.plus` restated via `IsIntegral`. -/
theorem mem_plus_iff_isIntegral {c : C} :
    c ∈ Cplus.plus ↔
      IsIntegral ((tateSeriesPlus P.N A Aplus.plus).map (P.π : tateSeries P.N A →+* C)) c :=
  P.mem_plus_iff c

/-- `P.π` maps `tateSeriesPlus P.N A Aplus.plus` into `Cplus.plus`. -/
theorem map_mem_plus {f : tateSeries P.N A} (hf : f ∈ tateSeriesPlus P.N A Aplus.plus) :
    P.π f ∈ Cplus.plus :=
  P.mem_plus_iff_isIntegral.mpr <|
    isIntegral_algebraMap
      (R := (tateSeriesPlus P.N A Aplus.plus).map (P.π : tateSeries P.N A →+* C))
      (x := ⟨P.π f, Subring.mem_map.mpr ⟨f, hf, rfl⟩⟩)

/-- **The presentation map bundled as a morphism of Huber pairs**
`(A⟨T₁, …, T_N⟩, A⁺⟨T₁, …, T_N⟩) → (C, C⁺)`. -/
noncomputable def toPairHom :
    Pair.Hom (Aplus.weighted (k := P.N) isWeightFamily_one_weight) Cplus where
  toRingHom := P.π
  continuous_toRingHom := P.continuous_π
  map_mem_plus _ hf := P.map_mem_plus ((Aplus.weighted_plus_eq_tateSeriesPlus P.N) ▸ hf)

@[simp]
theorem toRingHom_toPairHom : P.toPairHom.toRingHom = (P.π : tateSeries P.N A →+* C) :=
  (rfl)

/-- **`P.toPairHom` is a quotient mapping of Huber pairs** in the sense of Wedhorn
Definition 8.42 (`TauCeti.Huber.Pair.Hom.IsQuotientMapping`). -/
theorem isQuotientMapping_toPairHom : P.toPairHom.IsQuotientMapping := by
  refine (Pair.Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral P.toPairHom).mpr
    ⟨P.isOpenQuotientMap_π, fun c hc ↦ ?_⟩
  rw [P.toRingHom_toPairHom, Aplus.weighted_plus_eq_tateSeriesPlus]
  exact P.mem_plus_iff_isIntegral.mp hc

/-- **The induced base morphism `(A, A⁺) → (C, C⁺)`** obtained by composing `P.toPairHom` with the
constant-series morphism `Aplus.weightedHom isWeightFamily_one_weight`. -/
noncomputable def basePairHom : Pair.Hom Aplus Cplus :=
  P.toPairHom.comp (Aplus.weightedHom isWeightFamily_one_weight)

@[simp]
theorem toRingHom_basePairHom : P.basePairHom.toRingHom = algebraMap A C := by
  ext a
  simpa [basePairHom, algebraMap_weightedRestrictedSubring] using P.π.commutes a

/-- For any standard étale presentation, `algebraMap A C` is continuous. -/
theorem continuous_algebraMap (P : StandardEtalePresentation Aplus ϖ Cplus) :
    Continuous (algebraMap A C) :=
  P.toRingHom_basePairHom ▸ P.basePairHom.continuous_toRingHom

/-- For any standard étale presentation, `algebraMap A C` maps `Aplus.plus` into `Cplus.plus`. -/
theorem algebraMap_mem_plus (P : StandardEtalePresentation Aplus ϖ Cplus) {a : A}
    (ha : a ∈ Aplus.plus) :
    algebraMap A C a ∈ Cplus.plus := by
  rw [← P.toRingHom_basePairHom]
  exact P.basePairHom.map_mem_plus a ha

/-! ### Comparison with the canonical quotient Huber pair -/

/-- The closed ideal `overline{(F₁, …, F_N)}` of `tateSeries P.N A` cut out by `P.F`. -/
noncomputable abbrev quotientIdeal : Ideal (tateSeries P.N A) :=
  (Ideal.span (Set.range P.F)).closure

/-- The canonical quotient Huber pair `(A⟨T⟩ ⧸ overline{(F)}, …)` associated to `P`. -/
noncomputable abbrev quotientPair : Pair (tateSeries P.N A ⧸ P.quotientIdeal) :=
  (Aplus.weighted (k := P.N) isWeightFamily_one_weight).quotient P.quotientIdeal

/-- **Forward Huber-pair morphism from `P.quotientPair` to `Cplus`** induced by `P.toPairHom`. -/
noncomputable def fromQuotientHom : Pair.Hom P.quotientPair Cplus :=
  P.toPairHom.quotientLift P.quotientIdeal (by rw [toRingHom_toPairHom]; exact P.ker_π.ge)

/-- **Inverse Huber-pair morphism from `Cplus` to `P.quotientPair`**, identifying `(C, C⁺)` with
the canonical quotient Huber pair via `IsQuotientMapping.quotientKerInverse`. -/
noncomputable def toQuotientHom : Pair.Hom Cplus P.quotientPair :=
  (Pair.quotientHom _ P.quotientIdeal).quotientLift
      (RingHom.ker P.toPairHom.toRingHom)
      (by
        rw [Pair.Hom.toRingHom_quotientHom, Ideal.mk_ker, toRingHom_toPairHom]
        exact P.ker_π.le)
    |>.comp P.isQuotientMapping_toPairHom.quotientKerInverse

@[simp]
theorem fromQuotientHom_comp_toQuotientHom :
    P.fromQuotientHom.comp P.toQuotientHom = Pair.Hom.id Cplus := by
  have hcomp :
      P.fromQuotientHom.comp
          ((Pair.quotientHom _ P.quotientIdeal).quotientLift
            (RingHom.ker P.toPairHom.toRingHom)
            (by
              rw [Pair.Hom.toRingHom_quotientHom, Ideal.mk_ker, toRingHom_toPairHom]
              exact P.ker_π.le)) =
        P.toPairHom.quotientLift (RingHom.ker P.toPairHom.toRingHom) le_rfl := by
    refine Pair.Hom.quotientLift_unique (RingHom.ker P.toPairHom.toRingHom) P.toPairHom le_rfl _ ?_
    rw [Pair.Hom.comp_assoc, Pair.Hom.quotientLift_comp_quotientHom, fromQuotientHom,
      Pair.Hom.quotientLift_comp_quotientHom]
  rw [toQuotientHom, ← Pair.Hom.comp_assoc, hcomp,
    P.isQuotientMapping_toPairHom.quotientLift_comp_quotientKerInverse]

@[simp]
theorem toQuotientHom_comp_fromQuotientHom :
    P.toQuotientHom.comp P.fromQuotientHom = Pair.Hom.id P.quotientPair := by
  have hker : P.quotientIdeal ≤ RingHom.ker (Pair.quotientHom
      (Aplus.weighted (k := P.N) isWeightFamily_one_weight) P.quotientIdeal).toRingHom := by
    rw [Pair.Hom.toRingHom_quotientHom, Ideal.mk_ker]
  have hid : Pair.Hom.id P.quotientPair =
      (Pair.quotientHom _ P.quotientIdeal).quotientLift P.quotientIdeal hker :=
    Pair.Hom.quotientLift_unique P.quotientIdeal _ hker (Pair.Hom.id P.quotientPair)
      (Pair.Hom.id_comp _)
  rw [hid]
  refine Pair.Hom.quotientLift_unique P.quotientIdeal _ hker _ ?_
  rw [Pair.Hom.comp_assoc, fromQuotientHom, Pair.Hom.quotientLift_comp_quotientHom]
  conv_lhs =>
    rw [← Pair.Hom.quotientLift_comp_quotientHom (RingHom.ker P.toPairHom.toRingHom) P.toPairHom
      le_rfl]
  rw [toQuotientHom, Pair.Hom.comp_assoc,
    ← Pair.Hom.comp_assoc P.isQuotientMapping_toPairHom.quotientKerInverse,
    P.isQuotientMapping_toPairHom.quotientKerInverse_comp_quotientLift, Pair.Hom.id_comp,
    Pair.Hom.quotientLift_comp_quotientHom]

end BasicAPI

/-! ### Canonical quotient constructor, equivalence transport, and identity presentation -/

section Constructors

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- **Canonical quotient constructor.** Given `F : Fin N → tateSeries N A` with coefficients in
`A⁺` whose Jacobian determinant becomes a unit `u` in
`Q := tateSeries N A ⧸ (Ideal.span (Set.range F)).closure` satisfying `ϖ ^ k · u⁻¹ ∈ Q⁺`, the
canonical quotient map `Ideal.Quotient.mkₐ A _` defines a `StandardEtalePresentation` of the
quotient Huber pair `(Q, Q⁺)` over `(A, A⁺)`.

Marked `@[expose]` so `(ofQuotient …).N` is definitionally `N`, allowing the dependent projections
`ofQuotient_F` and `ofQuotient_π` to elaborate across modules. -/
@[expose]
noncomputable def ofQuotient (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) {N : ℕ}
    (F : Fin N → tateSeries N A) (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ)
    (hJ : ∃ u : (tateSeries N A ⧸ (Ideal.span (Set.range F)).closure)ˣ,
      (u : tateSeries N A ⧸ (Ideal.span (Set.range F)).closure) =
        Ideal.Quotient.mk (Ideal.span (Set.range F)).closure (tateSeriesJacobian F) ∧
      algebraMap A (tateSeries N A ⧸ (Ideal.span (Set.range F)).closure) (ϖ ^ k) * ↑u⁻¹ ∈
        ((Aplus.weighted (k := N) isWeightFamily_one_weight).quotient
          (Ideal.span (Set.range F)).closure).plus) :
    StandardEtalePresentation Aplus ϖ
      ((Aplus.weighted (k := N) isWeightFamily_one_weight).quotient
        (Ideal.span (Set.range F)).closure) where
  isPseudoUniformizer := hϖ
  N := N
  F := F
  F_mem_plus := hF
  k := k
  π := Ideal.Quotient.mkₐ A (Ideal.span (Set.range F)).closure
  isQuotientMap_π :=
    (QuotientRing.isOpenQuotientMap_mk (Ideal.span (Set.range F)).closure).isQuotientMap
  ker_π := Ideal.mk_ker
  mem_plus_iff c := by
    rw [Pair.quotient_plus, Aplus.weighted_plus_eq_tateSeriesPlus, Subalgebra.mem_toSubring,
      mem_integralClosure_iff]
    rfl
  exists_unit_jacobian := ⟨tateSeriesJacobian F, coe_tateSeriesJacobian F, hJ⟩

@[simp]
theorem ofQuotient_N (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) {N : ℕ}
    (F : Fin N → tateSeries N A) (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) (hJ) :
    (ofQuotient Aplus hϖ F hF k hJ).N = N :=
  (rfl)

@[simp]
theorem ofQuotient_F (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) {N : ℕ}
    (F : Fin N → tateSeries N A) (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) (hJ) :
    (ofQuotient Aplus hϖ F hF k hJ).F = F :=
  (rfl)

@[simp]
theorem ofQuotient_k (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) {N : ℕ}
    (F : Fin N → tateSeries N A) (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) (hJ) :
    (ofQuotient Aplus hϖ F hF k hJ).k = k :=
  (rfl)

@[simp]
theorem ofQuotient_π (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) {N : ℕ}
    (F : Fin N → tateSeries N A) (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) (hJ) :
    (ofQuotient Aplus hϖ F hF k hJ).π = Ideal.Quotient.mkₐ A (Ideal.span (Set.range F)).closure :=
  (rfl)

/-- Integral-closure characterization of `D⁺` after transporting a presentation along an
`A`-algebra equivalence `e : C ≃ₐ[A] D` preserving plus subrings. -/
theorem mem_plus_iff_ofAlgEquiv {Aplus : Pair A} {ϖ : A}
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] {Cplus : Pair C}
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    [Algebra A D] {Dplus : Pair D}
    (P : StandardEtalePresentation Aplus ϖ Cplus) (e : C ≃ₐ[A] D)
    (hplus : Cplus.plus.map (e : C →+* D) = Dplus.plus) (d : D) :
    d ∈ Dplus.plus ↔
      ((tateSeriesPlus P.N A Aplus.plus).map
        ((e.toAlgHom.comp P.π : tateSeries P.N A →ₐ[A] D) :
          tateSeries P.N A →+* D)).subtype.IsIntegralElem d := by
  let R : Subring C := (tateSeriesPlus P.N A Aplus.plus).map (P.π : tateSeries P.N A →+* C)
  let S : Subring D :=
    (tateSeriesPlus P.N A Aplus.plus).map ((e.toAlgHom.comp P.π : tateSeries P.N A →ₐ[A] D) :
      tateSeries P.N A →+* D)
  have hRS : R.map (e : C →+* D) = S := Subring.map_map _ _ _
  have hd_mem : d ∈ Dplus.plus ↔ e.symm d ∈ Cplus.plus := by
    rw [← hplus]
    exact ⟨fun hd ↦ by
      obtain ⟨c, hc, rfl⟩ := Subring.mem_map.mp hd
      simpa using hc,
      fun hc ↦ Subring.mem_map.mpr ⟨e.symm d, hc, e.apply_symm_apply d⟩⟩
  rw [hd_mem, P.mem_plus_iff_isIntegral]
  refine ⟨fun hint ↦ ?_, fun hint ↦ ?_⟩
  · let φ : R →+* S := (e : C →+* D).restrict R S fun x hx ↦
      hRS ▸ Subring.mem_map.mpr ⟨x, hx, rfl⟩
    have himg : IsIntegral S (e (e.symm d)) :=
      hint.map_of_comp_eq φ (e : C →+* D) (by ext; rfl)
    rwa [e.apply_symm_apply] at himg
  · let ψ : S →+* R := (e.symm : D →+* C).restrict S R fun y hy ↦ by
      rw [← hRS] at hy
      obtain ⟨x, hx, rfl⟩ := Subring.mem_map.mp hy
      simpa using hx
    have hint' : IsIntegral S d := hint
    exact hint'.map_of_comp_eq ψ (e.symm : D →+* C) (by ext; rfl)

/-- **Transport of a standard étale presentation along a topological `A`-algebra equivalence**
preserving plus rings.

Marked `@[expose]` so `(P.ofAlgEquiv ...).N` is definitionally `P.N`, allowing `ofAlgEquiv_F` and
`ofAlgEquiv_π` to elaborate across modules. -/
@[expose]
noncomputable def ofAlgEquiv {Aplus : Pair A} {ϖ : A}
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] {Cplus : Pair C}
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    [Algebra A D] {Dplus : Pair D}
    (P : StandardEtalePresentation Aplus ϖ Cplus) (e : C ≃ₐ[A] D)
    (he : Continuous e) (he_symm : Continuous e.symm)
    (hplus : Cplus.plus.map (e : C →+* D) = Dplus.plus) :
    StandardEtalePresentation Aplus ϖ Dplus where
  isPseudoUniformizer := P.isPseudoUniformizer
  N := P.N
  F := P.F
  F_mem_plus := P.F_mem_plus
  k := P.k
  π := e.toAlgHom.comp P.π
  isQuotientMap_π :=
    (Homeomorph.mk e.toEquiv he he_symm).isQuotientMap.comp P.isQuotientMap_π
  ker_π := by
    ext f
    rw [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      map_eq_zero_iff e e.injective, ← RingHom.mem_ker, P.ker_π]
  mem_plus_iff := mem_plus_iff_ofAlgEquiv P e hplus
  exists_unit_jacobian := by
    refine ⟨P.jacobian, P.coe_jacobian, Units.map (e : C →+* D).toMonoidHom P.jacobianUnit,
      by simp, ?_⟩
    rw [← hplus]
    refine Subring.mem_map.mpr ⟨algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹,
      P.pow_mul_jacobianUnit_inv_mem_plus, ?_⟩
    simp

@[simp]
theorem ofAlgEquiv_N {Aplus : Pair A} {ϖ : A}
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] {Cplus : Pair C}
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    [Algebra A D] {Dplus : Pair D}
    (P : StandardEtalePresentation Aplus ϖ Cplus) (e : C ≃ₐ[A] D)
    (he : Continuous e) (he_symm : Continuous e.symm)
    (hplus : Cplus.plus.map (e : C →+* D) = Dplus.plus) :
    (P.ofAlgEquiv e he he_symm hplus).N = P.N :=
  (rfl)

@[simp]
theorem ofAlgEquiv_F {Aplus : Pair A} {ϖ : A}
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] {Cplus : Pair C}
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    [Algebra A D] {Dplus : Pair D}
    (P : StandardEtalePresentation Aplus ϖ Cplus) (e : C ≃ₐ[A] D)
    (he : Continuous e) (he_symm : Continuous e.symm)
    (hplus : Cplus.plus.map (e : C →+* D) = Dplus.plus) :
    (P.ofAlgEquiv e he he_symm hplus).F = P.F :=
  (rfl)

@[simp]
theorem ofAlgEquiv_k {Aplus : Pair A} {ϖ : A}
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] {Cplus : Pair C}
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    [Algebra A D] {Dplus : Pair D}
    (P : StandardEtalePresentation Aplus ϖ Cplus) (e : C ≃ₐ[A] D)
    (he : Continuous e) (he_symm : Continuous e.symm)
    (hplus : Cplus.plus.map (e : C →+* D) = Dplus.plus) :
    (P.ofAlgEquiv e he he_symm hplus).k = P.k :=
  (rfl)

@[simp]
theorem ofAlgEquiv_π {Aplus : Pair A} {ϖ : A}
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] {Cplus : Pair C}
    {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
    [Algebra A D] {Dplus : Pair D}
    (P : StandardEtalePresentation Aplus ϖ Cplus) (e : C ≃ₐ[A] D)
    (he : Continuous e) (he_symm : Continuous e.symm)
    (hplus : Cplus.plus.map (e : C →+* D) = Dplus.plus) :
    (P.ofAlgEquiv e he he_symm hplus).π = e.toAlgHom.comp P.π :=
  (rfl)

/-- Integral-closure characterization of `A⁺` under the zero-variable equivalence
`tateSeries.finZeroAlgEquiv A`. -/
theorem mem_plus_iff_id (Aplus : Pair A) (a : A) :
    a ∈ Aplus.plus ↔
      ((tateSeriesPlus 0 A Aplus.plus).map
        (((tateSeries.finZeroAlgEquiv A).toAlgHom : tateSeries 0 A →ₐ[A] A) :
          tateSeries 0 A →+* A)).subtype.IsIntegralElem a := by
  have hmap :
      (tateSeriesPlus 0 A Aplus.plus).map
          (((tateSeries.finZeroAlgEquiv A).toAlgHom : tateSeries 0 A →ₐ[A] A) :
            tateSeries 0 A →+* A) =
        Aplus.plus :=
    tateSeries.map_tateSeriesPlus_finZeroAlgEquiv Aplus.plus
  have := Aplus.isRingOfIntegralElements.isIntegrallyClosedIn
  refine ⟨fun ha ↦ ?_, fun hint ↦ ?_⟩
  · exact isIntegral_algebraMap
      (R := (tateSeriesPlus 0 A Aplus.plus).map _) (x := ⟨a, hmap.symm ▸ ha⟩)
  · exact Subring.isIntegrallyClosedIn_iff.mp ‹_› (hmap ▸ hint)

section IdentityPresentation

variable [T2Space A]

/-- Over a Hausdorff Tate ring `A`, the kernel of `tateSeries.finZeroAlgEquiv A` equals the closure
of the empty-system ideal. -/
theorem ker_finZeroAlgEquiv :
    RingHom.ker ((tateSeries.finZeroAlgEquiv A).toAlgHom : tateSeries 0 A →ₐ[A] A) =
      (Ideal.span (Set.range (Fin.elim0 : Fin 0 → tateSeries 0 A))).closure := by
  have hrange : Set.range (Fin.elim0 : Fin 0 → tateSeries 0 A) = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨i, _⟩ ↦ i.elim0
  rw [hrange, Ideal.span_empty]
  have hcl : IsClosed ((⊥ : Ideal (tateSeries 0 A)) : Set (tateSeries 0 A)) := by
    simpa only [Submodule.bot_coe] using isClosed_singleton (x := (0 : tateSeries 0 A))
  have hbot : (⊥ : Ideal (tateSeries 0 A)).closure = ⊥ :=
    SetLike.ext' (Ideal.coe_closure (⊥ : Ideal (tateSeries 0 A)) ▸ hcl.closure_eq)
  rw [hbot]
  ext f
  rw [RingHom.mem_ker, Submodule.mem_bot, AlgEquiv.coe_toAlgHom,
    map_eq_zero_iff (tateSeries.finZeroAlgEquiv A) (tateSeries.finZeroAlgEquiv A).injective]

/-- **The explicit zero-variable identity presentation of `(A, A⁺)` over itself** at scale `ϖ`.

Marked `@[expose]` so `(id Aplus hϖ).N` is definitionally `0`, allowing `id_F` and `id_π` to
elaborate across modules. -/
@[expose]
noncomputable def id (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    StandardEtalePresentation Aplus ϖ Aplus where
  isPseudoUniformizer := hϖ
  N := 0
  F := Fin.elim0
  F_mem_plus i := i.elim0
  k := 0
  π := (tateSeries.finZeroAlgEquiv A).toAlgHom
  isQuotientMap_π := tateSeries.isQuotientMap_finZeroAlgEquiv
  ker_π := ker_finZeroAlgEquiv
  mem_plus_iff := mem_plus_iff_id Aplus
  exists_unit_jacobian := ⟨1, by simp, 1, by simp, by simp⟩

@[simp]
theorem id_N (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    (id Aplus hϖ).N = 0 :=
  (rfl)

@[simp]
theorem id_F (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    (id Aplus hϖ).F = Fin.elim0 :=
  (rfl)

@[simp]
theorem id_k (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    (id Aplus hϖ).k = 0 :=
  (rfl)

@[simp]
theorem id_π (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    (id Aplus hϖ).π = (tateSeries.finZeroAlgEquiv A).toAlgHom :=
  (rfl)

/-- **The identity presentation theorem**: any Hausdorff Tate pair `(A, A⁺)` admits a standard
étale presentation over itself with `N = 0` and `k = 0`. -/
theorem identity {Aplus : Pair A} {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    ∃ P : StandardEtalePresentation Aplus ϖ Aplus,
      P.N = 0 ∧ P.k = 0 ∧ ∀ a : A, P.π (algebraMap A (tateSeries P.N A) a) = a :=
  ⟨id Aplus hϖ, rfl, rfl, fun a ↦ (tateSeries.finZeroAlgEquiv A).commutes a⟩

end IdentityPresentation

end Constructors

end StandardEtalePresentation

end TauCeti.Huber

end
