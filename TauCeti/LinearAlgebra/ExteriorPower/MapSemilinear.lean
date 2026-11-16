/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Semilinear functoriality of exterior algebras and exterior powers

A `σ`-semilinear map `f : M →ₛₗ[σ] N` along a ring homomorphism `σ : R →+* S` between commutative
rings induces a ring homomorphism `ExteriorAlgebra.mapSemilinear f` between exterior algebras that
sends `ι R m` to `ι S (f m)` and is `σ`-semilinear. Because it maps homogeneous generators of degree
one to homogeneous generators of degree one, it carries `⋀[R]^n M` into `⋀[S]^n N` in every degree
`n` and restricts to a `σ`-semilinear map `exteriorPower.mapSemilinear n f` compatible with wedge
products, identities, and composition.

When `σ` is the identity on `R`, `exteriorPower.mapSemilinear n f` agrees with Mathlib's linear
functoriality `exteriorPower.map n f`. The semilinear generality is required when pulling back
exterior powers of Kähler differentials along an algebra homomorphism `B →ₐ[A] C`, where no global
`B`-algebra structure on `C` is available (for example for an endomorphism such as Frobenius).

## Main definitions

* `ExteriorAlgebra.mapSemilinear f`: the ring homomorphism
  `ExteriorAlgebra R M →+* ExteriorAlgebra S N` induced by `f : M →ₛₗ[σ] N`.
* `exteriorPower.mapSemilinear n f`: the induced `σ`-semilinear map `⋀[R]^n M →ₛₗ[σ] ⋀[S]^n N`.

## Main results

* `ExteriorAlgebra.mapSemilinear_ι`, `ExteriorAlgebra.mapSemilinear_smul`,
  `ExteriorAlgebra.mapSemilinear_ιMulti`: action on vectors, scalars, and pure exterior products.
* `exteriorPower.mapSemilinear_apply_ιMulti`: `mapSemilinear n f` sends `v₀ ∧ ⋯ ∧ vₙ₋₁` to
  `f v₀ ∧ ⋯ ∧ f vₙ₋₁`.
* `exteriorPower.mapSemilinear_wedge`: compatibility with `exteriorPower.wedge`.
* `exteriorPower.mapSemilinear_id`, `exteriorPower.mapSemilinear_comp`: functoriality.
* `exteriorPower.zeroEquiv_mapSemilinear`, `exteriorPower.oneEquiv_mapSemilinear`: in degrees `0`
  and `1`, `mapSemilinear` recovers `σ` and `f`.

## References

* Mathlib's `ExteriorAlgebra.lift` (`Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`) and
  `exteriorPower.map` (`Mathlib.LinearAlgebra.ExteriorPower.Basic`).
-/

public section

noncomputable section

namespace ExteriorAlgebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  {σ : R →+* S} {τ : S →+* T} {υ : R →+* T}
  {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module T P]

/-- The ring homomorphism `ExteriorAlgebra R M →+* ExteriorAlgebra S N` induced by a `σ`-semilinear
map `f : M →ₛₗ[σ] N`, sending `ι R m` to `ι S (f m)` and `algebraMap R _ r` to
`algebraMap S _ (σ r)`. -/
def mapSemilinear (f : M →ₛₗ[σ] N) : ExteriorAlgebra R M →+* ExteriorAlgebra S N :=
  letI : Algebra R S := σ.toAlgebra
  letI : Module R N := Module.compHom N σ
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f' : M →ₗ[R] ExteriorAlgebra S N :=
    { toFun := fun m ↦ ι S (f m)
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_smul' := fun r m ↦ by
        rw [f.map_smulₛₗ, LinearMap.map_smul, RingHom.id_apply]
        exact (IsScalarTower.algebraMap_smul S r (ι S (f m))).symm }
  (lift R ⟨f', fun m ↦ ι_sq_zero (f m)⟩).toRingHom

/-- `mapSemilinear f` sends a generator `ι R m` to `ι S (f m)`. -/
@[simp]
theorem mapSemilinear_ι (f : M →ₛₗ[σ] N) (m : M) :
    mapSemilinear f (ι R m) = ι S (f m) :=
  letI : Algebra R S := σ.toAlgebra
  letI : Module R N := Module.compHom N σ
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  lift_ι_apply R _ _ m

/-- `mapSemilinear f` intertwines `algebraMap` through `σ`. -/
@[simp]
theorem mapSemilinear_algebraMap (f : M →ₛₗ[σ] N) (r : R) :
    mapSemilinear f (algebraMap R (ExteriorAlgebra R M) r) =
      algebraMap S (ExteriorAlgebra S N) (σ r) :=
  letI : Algebra R S := σ.toAlgebra
  letI : Module R N := Module.compHom N σ
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (AlgHom.commutes (lift R _) r).trans
    (IsScalarTower.algebraMap_apply R S (ExteriorAlgebra S N) r)

/-- `mapSemilinear f` is `σ`-semilinear for the base-ring scalar actions. -/
@[simp]
theorem mapSemilinear_smul (f : M →ₛₗ[σ] N) (r : R) (x : ExteriorAlgebra R M) :
    mapSemilinear f (r • x) = σ r • mapSemilinear f x := by
  rw [Algebra.smul_def, map_mul, mapSemilinear_algebraMap, ← Algebra.smul_def]

/-- Two ring homomorphisms out of `ExteriorAlgebra R M` that intertwine `algebraMap` via `σ` and
agree on `ι R` are equal. -/
theorem ringHom_ext_of_algebraMap {g₁ g₂ : ExteriorAlgebra R M →+* ExteriorAlgebra S N}
    (halg : ∀ r, g₁ (algebraMap R _ r) = g₂ (algebraMap R _ r))
    (hι : ∀ m, g₁ (ι R m) = g₂ (ι R m)) : g₁ = g₂ := by
  ext x
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact halg r
  | ι m => exact hι m
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- `mapSemilinear f` sends an `n`-fold exterior product `ιMulti R n v` to `ιMulti S n (f ∘ v)`. -/
@[simp]
theorem mapSemilinear_ιMulti (f : M →ₛₗ[σ] N) (n : ℕ) (v : Fin n → M) :
    mapSemilinear f (ιMulti R n v) = ιMulti S n (f ∘ v) := by
  rw [ιMulti_apply, ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  ext i
  simp

/-- `mapSemilinear f` preserves exterior degree, carrying `⋀[R]^n M` into `⋀[S]^n N`. -/
theorem mapSemilinear_mem_exteriorPower (f : M →ₛₗ[σ] N) {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) : mapSemilinear f x ∈ ⋀[S]^n N := by
  rw [← exteriorPower.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [mapSemilinear_ιMulti]
    exact (exteriorPower.ιMulti S n (f ∘ v)).2
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r _ _ hx => rw [mapSemilinear_smul]; exact Submodule.smul_mem _ (σ r) hx

/-- For a plain `R`-linear map `f : M →ₗ[R] M'`, `mapSemilinear f` agrees with Mathlib's
`ExteriorAlgebra.map f`. -/
theorem mapSemilinear_eq_map {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') :
    mapSemilinear f = (ExteriorAlgebra.map f).toRingHom :=
  ringHom_ext_of_algebraMap (fun r ↦ by simp [AlgHom.commutes]) (fun m ↦ by simp)

/-- `mapSemilinear` of the identity linear map is the identity ring homomorphism. -/
@[simp]
theorem mapSemilinear_id :
    mapSemilinear (LinearMap.id : M →ₗ[R] M) = RingHom.id (ExteriorAlgebra R M) :=
  ringHom_ext_of_algebraMap (fun _ ↦ by simp) (fun _ ↦ by simp)

/-- `mapSemilinear` preserves composition of semilinear maps. -/
theorem mapSemilinear_comp [RingHomCompTriple σ τ υ] (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) :
    mapSemilinear (g.comp f) = (mapSemilinear g).comp (mapSemilinear f) :=
  ringHom_ext_of_algebraMap
    (fun r ↦ by simp [RingHomCompTriple.comp_apply])
    (fun m ↦ by simp)

@[simp]
theorem mapSemilinear_comp_apply [RingHomCompTriple σ τ υ] (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N)
    (x : ExteriorAlgebra R M) :
    mapSemilinear (g.comp f) x = mapSemilinear g (mapSemilinear f x) :=
  RingHom.congr_fun (mapSemilinear_comp g f) x

end ExteriorAlgebra

namespace exteriorPower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  {σ : R →+* S} {τ : S →+* T} {υ : R →+* T}
  {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module T P]

/-- The `σ`-semilinear map `⋀[R]^n M →ₛₗ[σ] ⋀[S]^n N` on `n`th exterior powers induced by a
`σ`-semilinear map `f : M →ₛₗ[σ] N`. -/
def mapSemilinear (n : ℕ) (f : M →ₛₗ[σ] N) : ⋀[R]^n M →ₛₗ[σ] ⋀[S]^n N where
  toFun x := ⟨ExteriorAlgebra.mapSemilinear f x.1,
    ExteriorAlgebra.mapSemilinear_mem_exteriorPower f x.2⟩
  map_add' x y := Subtype.ext (map_add (ExteriorAlgebra.mapSemilinear f) x.1 y.1)
  map_smul' r x := Subtype.ext (ExteriorAlgebra.mapSemilinear_smul f r x.1)

/-- Coercing `mapSemilinear n f x` to the exterior algebra applies
`ExteriorAlgebra.mapSemilinear f`. -/
@[simp]
theorem coe_mapSemilinear (n : ℕ) (f : M →ₛₗ[σ] N) (x : ⋀[R]^n M) :
    (mapSemilinear n f x : ExteriorAlgebra S N) = ExteriorAlgebra.mapSemilinear f x.1 :=
  (rfl)

/-- `mapSemilinear n f` sends a pure exterior product `v₀ ∧ ⋯ ∧ vₙ₋₁` to `f v₀ ∧ ⋯ ∧ f vₙ₋₁`. -/
@[simp]
theorem mapSemilinear_apply_ιMulti (n : ℕ) (f : M →ₛₗ[σ] N) (v : Fin n → M) :
    mapSemilinear n f (ιMulti R n v) = ιMulti S n (f ∘ v) :=
  Subtype.ext (ExteriorAlgebra.mapSemilinear_ιMulti f n v)

/-- Two `σ`-semilinear maps out of `⋀[R]^n M` that agree on all pure exterior products are equal. -/
theorem semilinearMap_ext {n : ℕ} {g₁ g₂ : ⋀[R]^n M →ₛₗ[σ] N}
    (h : ∀ v : Fin n → M, g₁ (ιMulti R n v) = g₂ (ιMulti R n v)) : g₁ = g₂ := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  exact h v

/-- `mapSemilinear` preserves wedge products of exterior powers. -/
theorem mapSemilinear_wedge (k l : ℕ) (f : M →ₛₗ[σ] N) (x : ⋀[R]^k M) (y : ⋀[R]^l M) :
    mapSemilinear (k + l) f (wedge R M k l x y) =
      wedge S N k l (mapSemilinear k f x) (mapSemilinear l f y) :=
  Subtype.ext (map_mul (ExteriorAlgebra.mapSemilinear f) x.1 y.1)

/-- For an `R`-linear map `f`, `mapSemilinear n f` agrees with `exteriorPower.map n f`. -/
theorem mapSemilinear_eq_map {M' : Type*} [AddCommGroup M'] [Module R M']
    (n : ℕ) (f : M →ₗ[R] M') : mapSemilinear n f = map n f :=
  LinearMap.ext fun x ↦ Subtype.ext <| by
    rw [coe_mapSemilinear, coe_map, ExteriorAlgebra.mapSemilinear_eq_map]
    rfl

/-- `mapSemilinear` of the identity map is the identity. -/
@[simp]
theorem mapSemilinear_id (n : ℕ) :
    mapSemilinear n (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  rw [mapSemilinear_eq_map, map_id]

theorem mapSemilinear_id_apply (n : ℕ) (x : ⋀[R]^n M) :
    mapSemilinear n (LinearMap.id : M →ₗ[R] M) x = x :=
  DFunLike.congr_fun (mapSemilinear_id n) x

/-- `mapSemilinear` preserves composition of semilinear maps. -/
theorem mapSemilinear_comp [RingHomCompTriple σ τ υ] (n : ℕ) (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) :
    mapSemilinear n (g.comp f) = (mapSemilinear n g).comp (mapSemilinear n f) := by
  ext x : 1
  apply Subtype.ext
  exact ExteriorAlgebra.mapSemilinear_comp_apply g f x.1

@[simp]
theorem mapSemilinear_comp_apply [RingHomCompTriple σ τ υ] (n : ℕ)
    (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) (x : ⋀[R]^n M) :
    mapSemilinear n (g.comp f) x = mapSemilinear n g (mapSemilinear n f x) :=
  DFunLike.congr_fun (mapSemilinear_comp n g f) x

/-- Under `zeroEquiv`, `mapSemilinear 0 f` acts on scalars as `σ`. -/
@[simp]
theorem zeroEquiv_mapSemilinear (f : M →ₛₗ[σ] N) (x : ⋀[R]^0 M) :
    zeroEquiv S N (mapSemilinear 0 f x) = σ (zeroEquiv R M x) := by
  have hx : x ∈ Submodule.span R (Set.range (ιMulti R 0)) := by
    rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨v, rfl⟩ := h
    simp
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul r _ _ hx => simp [hx]

/-- `mapSemilinear 0 f` intertwines `zeroEquiv.symm` via `σ`. -/
@[simp]
theorem mapSemilinear_zeroEquiv_symm (f : M →ₛₗ[σ] N) (r : R) :
    mapSemilinear 0 f ((zeroEquiv R M).symm r) = (zeroEquiv S N).symm (σ r) := by
  apply (zeroEquiv S N).injective
  simp

/-- Under `oneEquiv`, `mapSemilinear 1 f` recovers `f`. -/
@[simp]
theorem oneEquiv_mapSemilinear (f : M →ₛₗ[σ] N) (x : ⋀[R]^1 M) :
    oneEquiv S N (mapSemilinear 1 f x) = f (oneEquiv R M x) := by
  have hx : x ∈ Submodule.span R (Set.range (ιMulti R 1)) := by
    rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨v, rfl⟩ := h
    simp
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul r _ _ hx => simp [hx]

/-- `mapSemilinear 1 f` intertwines `oneEquiv.symm` with `f`. -/
@[simp]
theorem mapSemilinear_oneEquiv_symm (f : M →ₛₗ[σ] N) (m : M) :
    mapSemilinear 1 f ((oneEquiv R M).symm m) = (oneEquiv S N).symm (f m) := by
  apply (oneEquiv S N).injective
  simp

end exteriorPower
