/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.RingTheory.PreLambdaRing.Binomial

/-!
# Line-monomial pre-`λ`-ring structure on `MonoidAlgebra ℤ M`

For a commutative multiplicative monoid `M`, the integral monoid algebra `MonoidAlgebra ℤ M`
carries a canonical **line-monomial** `PreLambdaRing` structure (`MonoidAlgebra.instPreLambdaRing`)
characterized on basis elements `[m] = single m 1` by `λ_t([m]) = 1 + [m] t`
(Weibel, *The K-book*, Example II.4.1.2 and Exercise II.4.4). Under this structure:
* every basis monomial `single m 1` (`MonoidAlgebra.of ℤ M m`) is a line element;
* general monomials satisfy `λ^n(z • [m]) = choose z n • [m^n]`, i.e.
  `lambdaOp n (single m z) = single (m ^ n) (Ring.choose z n)` (`MonoidAlgebra.lambdaOp_single`);
* `MonoidAlgebra.instPreLambdaRing` is the unique `PreLambdaRing` structure on `MonoidAlgebra ℤ M`
  for which all basis monomials `single m 1` are line elements
  (`MonoidAlgebra.preLambdaRing_unique`);
* pushforward along any monoid homomorphism `f : M →* N` (`MonoidAlgebra.mapDomainRingHom ℤ f`) is
  a pre-`λ` morphism (`MonoidAlgebra.mapDomainPreLambdaRingHom`), functorially in `f`;
* for a subsingleton monoid `M`, `MonoidAlgebra.uniqueRingEquiv M` upgrades to a pre-`λ`
  isomorphism `MonoidAlgebra ℤ M ≃λ+* ℤ` with binomial `ℤ`
  (`MonoidAlgebra.uniquePreLambdaRingEquiv`).
-/

public section

open PowerSeries

namespace MonoidAlgebra

section LineMonomial

variable {M N O : Type*} [CommMonoid M] [CommMonoid N] [CommMonoid O]

/-- Canonical **line-monomial** `PreLambdaRing` structure on `MonoidAlgebra ℤ M` for a commutative
monoid `M`, characterized by `λ_t([m]) = 1 + [m] t` for every `m : M`. -/
noncomputable instance instPreLambdaRing : TauCeti.PreLambdaRing (MonoidAlgebra ℤ M) :=
  TauCeti.PreLambdaRing.ofTotalLambda
    { toFun := fun x ↦ Additive.toMul <|
        ((Finsupp.liftAddHom fun m : M ↦
            zmultiplesHom (Additive (principalUnitSubgroup (MonoidAlgebra ℤ M)))
              (Additive.ofMul (principalUnitMk (1 + C (single m (1 : ℤ)) * X) (by simp)))).comp
          coeffAddEquiv.toAddMonoidHom) (Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' := fun x y ↦ by rw [toAdd_mul, map_add, toMul_add] }
    fun x ↦ by
      let f : MonoidAlgebra ℤ M →+ MonoidAlgebra ℤ M :=
        (Finsupp.liftAddHom fun m : M ↦
          zmultiplesHom (Additive (principalUnitSubgroup (MonoidAlgebra ℤ M)))
            (Additive.ofMul (principalUnitMk (1 + C (single m (1 : ℤ)) * X) (by simp)))).comp
          coeffAddEquiv.toAddMonoidHom |> fun g ↦
        { toFun := fun a ↦
            PowerSeries.coeff 1 (principalUnitSeries (Additive.toMul (g a)))
          map_zero' := by simp
          map_add' := fun a b ↦ by rw [map_add, toMul_add, coeff_one_principalUnitSeries_mul] }
      have hf : f = AddMonoidHom.id (MonoidAlgebra ℤ M) := by
        ext m
        simp [f]
      exact DFunLike.congr_fun hf x

/-- Total `λ`-series on `single m z` is `(1 + [m] X)^z` in `1 + X (MonoidAlgebra ℤ M)⟦X⟧`. -/
theorem totalSeries_single_eq (m : M) (z : ℤ) :
    TauCeti.PreLambdaRing.totalSeries (single m z) =
      principalUnitSeries
        (principalUnitMk (1 + C (single m (1 : ℤ)) * X) (by simp) ^ z) := by
  rw [instPreLambdaRing, TauCeti.PreLambdaRing.totalSeries_ofTotalLambda]
  simp

@[simp]
theorem totalSeries_single_one (m : M) :
    TauCeti.PreLambdaRing.totalSeries (single m (1 : ℤ)) =
      1 + C (single m (1 : ℤ)) * X := by
  rw [totalSeries_single_eq, zpow_one, principalUnitSeries_mk]

theorem totalSeries_of (m : M) :
    TauCeti.PreLambdaRing.totalSeries (MonoidAlgebra.of ℤ M m) =
      1 + C (MonoidAlgebra.of ℤ M m) * X :=
  totalSeries_single_one m

/-- Every basis monomial `single m 1` in `MonoidAlgebra ℤ M` is a line element. -/
@[simp]
theorem isLineElement_single_one (m : M) :
    TauCeti.IsLineElement (single m (1 : ℤ)) := by
  rw [TauCeti.PreLambdaRing.isLineElement_def, totalSeries_single_one]

theorem isLineElement_of (m : M) :
    TauCeti.IsLineElement (MonoidAlgebra.of ℤ M m) :=
  isLineElement_single_one m

theorem lambdaOp_single_one_of_two_le {n : ℕ} (hn : 2 ≤ n) (m : M) :
    TauCeti.lambdaOp n (single m (1 : ℤ)) = 0 :=
  (isLineElement_single_one m).lambdaOp_eq_zero hn

/-- Basis-monomial formula: `λ^n(z • [m]) = choose z n • [m^n]` for all `n : ℕ`, `m : M`, `z : ℤ`.
In particular `λ^n([m]) = 0` for `n ≥ 2` and `λ^n(-[m]) = (-1)^n [m^n]`. -/
@[simp]
theorem lambdaOp_single (n : ℕ) (m : M) (z : ℤ) :
    TauCeti.lambdaOp n (single m z) = single (m ^ n) (Ring.choose z n) := by
  have hsmul : single m z = z • single m (1 : ℤ) := by
    ext
    simp
  rw [hsmul, (isLineElement_single_one m).lambdaOp_zsmul, single_pow, one_pow]
  ext
  simp

/-! ### Additive generation and uniqueness -/

/-- Basis monomials `single m 1` generate `MonoidAlgebra ℤ M` as an additive subgroup. -/
theorem addSubgroupClosure_range_single_one :
    AddSubgroup.closure (Set.range fun m : M ↦ single m (1 : ℤ)) = ⊤ :=
  top_unique fun x _ ↦
    MonoidAlgebra.induction_linear x (AddSubgroup.zero_mem _)
      (fun _ _ ↦ AddSubgroup.add_mem _) fun m z ↦ by
        have hsmul : single m z = z • single m (1 : ℤ) := by
          ext
          simp
        have hmem : single m (1 : ℤ) ∈
            AddSubgroup.closure (Set.range fun m : M ↦ single m (1 : ℤ)) :=
          AddSubgroup.subset_closure ⟨m, rfl⟩
        rw [hsmul]
        exact AddSubgroup.zsmul_mem _ hmem z

/-- `MonoidAlgebra.instPreLambdaRing` is the unique `PreLambdaRing` structure on `MonoidAlgebra ℤ M`
for which every basis monomial `single m 1` is a line element. -/
theorem preLambdaRing_unique (l : TauCeti.PreLambdaRing (MonoidAlgebra ℤ M))
    (hl : ∀ m : M, @TauCeti.IsLineElement (MonoidAlgebra ℤ M) _ l (single m 1)) :
    l = instPreLambdaRing := by
  refine TauCeti.PreLambdaRing.ext_addSubgroupClosure addSubgroupClosure_range_single_one ?_
  rintro _ ⟨m, rfl⟩ n
  rw [← @TauCeti.PreLambdaRing.coeff_totalSeries (MonoidAlgebra ℤ M) _ l,
    ← @TauCeti.PreLambdaRing.coeff_totalSeries (MonoidAlgebra ℤ M) _ instPreLambdaRing,
    (@TauCeti.PreLambdaRing.isLineElement_def (MonoidAlgebra ℤ M) _ l _).mp (hl m),
    totalSeries_single_one]

/-- Uniqueness phrased via the total `λ`-series `λ_t([m]) = 1 + [m] t` on basis monomials. -/
theorem preLambdaRing_unique_of_totalSeries (l : TauCeti.PreLambdaRing (MonoidAlgebra ℤ M))
    (hl : ∀ m : M, @TauCeti.PreLambdaRing.totalSeries (MonoidAlgebra ℤ M) _ l (single m 1) =
      1 + C (single m 1) * X) :
    l = instPreLambdaRing :=
  preLambdaRing_unique l fun m ↦ by
    rw [@TauCeti.PreLambdaRing.isLineElement_def (MonoidAlgebra ℤ M) _ l]
    exact hl m

/-- Two pre-`λ` morphisms out of `MonoidAlgebra ℤ M` agreeing on all basis monomials `single m 1`
are equal. -/
theorem preLambdaRingHom_ext {R : Type*} [CommRing R] [TauCeti.PreLambdaRing R]
    {f g : TauCeti.PreLambdaRingHom (MonoidAlgebra ℤ M) R}
    (h : ∀ m : M, f (single m 1) = g (single m 1)) : f = g := by
  apply TauCeti.PreLambdaRingHom.ext
  intro x
  have hadd : f.toRingHom.toAddMonoidHom = g.toRingHom.toAddMonoidHom := by
    ext m
    exact h m
  exact DFunLike.congr_fun hadd x

/-! ### Naturality in the monoid and trivial-monoid comparison -/

private theorem singleOneRingHom_eq_single (z : ℤ) :
    (singleOneRingHom : ℤ →+* MonoidAlgebra ℤ M) z = single 1 z :=
  rfl

/-- The scalar inclusion `ℤ →+* MonoidAlgebra ℤ M` (`r ↦ single 1 r`) is a pre-`λ` morphism from
binomial `ℤ`. -/
theorem isPreLambdaHom_singleOneRingHom :
    (singleOneRingHom : ℤ →+* MonoidAlgebra ℤ M).IsPreLambdaHom :=
  RingHom.IsPreLambdaHom.mk fun n z ↦ by
    rw [singleOneRingHom_eq_single, singleOneRingHom_eq_single, lambdaOp_single, one_pow,
      TauCeti.lambdaOp_int_eq_choose]

variable (M) in
/-- Scalar inclusion `ℤ → MonoidAlgebra ℤ M` as a bundled `PreLambdaRingHom`. -/
noncomputable def singleOnePreLambdaRingHom :
    TauCeti.PreLambdaRingHom ℤ (MonoidAlgebra ℤ M) :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom singleOneRingHom isPreLambdaHom_singleOneRingHom

theorem singleOnePreLambdaRingHom_apply (z : ℤ) :
    singleOnePreLambdaRingHom M z = single 1 z := by
  rw [singleOnePreLambdaRingHom, TauCeti.PreLambdaRingHom.ofIsPreLambdaHom_apply,
    singleOneRingHom_eq_single]

/-- Pushforward `MonoidAlgebra.mapDomainRingHom ℤ f` along a monoid homomorphism `f : M →* N` is a
pre-`λ` morphism for the line-monomial structures. -/
theorem isPreLambdaHom_mapDomainRingHom (f : M →* N) :
    (mapDomainRingHom ℤ f).IsPreLambdaHom :=
  RingHom.isPreLambdaHom_of_isLineElement_addSubgroupClosure
    addSubgroupClosure_range_single_one
    (by rintro _ ⟨m, rfl⟩; exact isLineElement_single_one m)
    (by rintro _ ⟨m, rfl⟩; simp)

/-- Functorial pushforward of `MonoidAlgebra ℤ M` along a monoid homomorphism `f : M →* N` as a
bundled `PreLambdaRingHom`. -/
noncomputable def mapDomainPreLambdaRingHom (f : M →* N) :
    TauCeti.PreLambdaRingHom (MonoidAlgebra ℤ M) (MonoidAlgebra ℤ N) :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom (mapDomainRingHom ℤ f)
    (isPreLambdaHom_mapDomainRingHom f)

@[simp]
theorem mapDomainPreLambdaRingHom_apply (f : M →* N) (x : MonoidAlgebra ℤ M) :
    mapDomainPreLambdaRingHom f x = mapDomain f x := by
  simp [mapDomainPreLambdaRingHom]

theorem mapDomainPreLambdaRingHom_single (f : M →* N) (m : M) (z : ℤ) :
    mapDomainPreLambdaRingHom f (single m z) = single (f m) z := by
  simp [mapDomainPreLambdaRingHom]

@[simp]
theorem mapDomainPreLambdaRingHom_id :
    mapDomainPreLambdaRingHom (MonoidHom.id M) =
      TauCeti.PreLambdaRingHom.id (MonoidAlgebra ℤ M) := by
  apply preLambdaRingHom_ext
  intro m
  simp

theorem mapDomainPreLambdaRingHom_comp (g : N →* O) (f : M →* N) :
    mapDomainPreLambdaRingHom (g.comp f) =
      (mapDomainPreLambdaRingHom g).comp (mapDomainPreLambdaRingHom f) := by
  apply preLambdaRingHom_ext
  intro m
  simp

/-- A monoid isomorphism `M ≃* N` induces a pre-`λ` ring isomorphism
`MonoidAlgebra ℤ M ≃λ+* MonoidAlgebra ℤ N`. -/
noncomputable def mapDomainPreLambdaRingEquiv (e : M ≃* N) :
    TauCeti.PreLambdaRingEquiv (MonoidAlgebra ℤ M) (MonoidAlgebra ℤ N) where
  toRingEquiv := mapDomainRingEquiv ℤ e
  map_lambdaOp' n x := (isPreLambdaHom_mapDomainRingHom e.toMonoidHom).apply n x

@[simp]
theorem mapDomainPreLambdaRingEquiv_single (e : M ≃* N) (m : M) (z : ℤ) :
    mapDomainPreLambdaRingEquiv e (single m z) = single (e m) z := by
  rw [← TauCeti.PreLambdaRingEquiv.coe_toRingEquiv]
  exact mapDomainRingEquiv_single e z m

variable (M) in
/-- For a trivial (subsingleton) monoid `M`, the line-monomial `PreLambdaRing` structure on
`MonoidAlgebra ℤ M` identifies canonically with binomial `ℤ`. -/
noncomputable def uniquePreLambdaRingEquiv [Subsingleton M] :
    TauCeti.PreLambdaRingEquiv (MonoidAlgebra ℤ M) ℤ :=
  (TauCeti.PreLambdaRingEquiv.ofBijective (singleOnePreLambdaRingHom M)
    ⟨fun x y h ↦ by
        have h' : single (1 : M) x = single (1 : M) y := by
          simpa only [singleOnePreLambdaRingHom_apply] using h
        exact single_right_injective h',
      fun x ↦ ⟨x.coeff 1, by
        rw [singleOnePreLambdaRingHom_apply]
        ext m
        have hm : m = 1 := Subsingleton.elim m 1
        subst hm
        simp⟩⟩).symm

theorem uniquePreLambdaRingEquiv_symm_apply [Subsingleton M] (z : ℤ) :
    (uniquePreLambdaRingEquiv M).symm z = single 1 z := by
  simp [intCast_def]

theorem uniquePreLambdaRingEquiv_single_one [Subsingleton M] (z : ℤ) :
    uniquePreLambdaRingEquiv M (single 1 z) = z := by
  rw [← uniquePreLambdaRingEquiv_symm_apply (M := M) z,
    (uniquePreLambdaRingEquiv M).apply_symm_apply]

@[simp]
theorem uniquePreLambdaRingEquiv_apply [Subsingleton M] (x : MonoidAlgebra ℤ M) :
    uniquePreLambdaRingEquiv M x = x.coeff 1 := by
  have hx : x = single 1 (x.coeff 1) := by
    ext m
    have hm : m = 1 := Subsingleton.elim m 1
    subst hm
    simp
  conv_lhs => rw [hx]
  exact uniquePreLambdaRingEquiv_single_one (x.coeff 1)

end LineMonomial

end MonoidAlgebra
