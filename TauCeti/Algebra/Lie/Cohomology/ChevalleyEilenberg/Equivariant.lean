/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.Relative
public import TauCeti.RepresentationTheory.ExteriorPower

/-!
# Group-equivariant and `(L, H, G)`-relative Chevalley–Eilenberg cochains

Given a Lie algebra `L` over a commutative ring `R`, a Lie subalgebra `H : LieSubalgebra R L`,
an `L`-module `M`, and a monoid `G` acting linearly on `L` and `M` via
`ρL : Representation R G L` and `ρM : Representation R G M`, this file defines the
`G`-equivariant and `(L, H, G)`-relative Chevalley–Eilenberg complexes:

* When `ρL` preserves `H`, `quotientRepresentation` equips `L ⧸ H.toLieSubmodule` with the
  induced `G`-representation.
* `equivariantCochain` is the submodule of `G`-equivariant `n`-cochains
  (`ρM g (ω v) = ω (ρL g ∘ v)`). Intersecting with `horizontalCochain` gives
  `Hom_G(⋀^n(L ⧸ H), M)` via `horizontalEquivariantCochainEquivIntertwiningMap`, using Mathlib's
  `Representation.IntertwiningMap` and avoiding any typeclass diamond with Mathlib's pointwise
  action on `AlternatingMap`.
* Whenever `ρL` acts by Lie endomorphisms compatibly with the `L`-action on `M`, the
  Chevalley–Eilenberg differential `d` preserves `equivariantCochain`
  (`d_mem_equivariantCochain`). Intersecting with `relativeCochain` gives the
  `(L, H, G)`-relative cochain complex `groupRelativeCochainComplex` and cohomology
  `groupRelativeCohomology`.
* When `G`-equivariance on horizontal cochains implies `H`-invariance (for instance when `G` is a
  connected Lie group with Lie algebra `H`), `groupRelativeCochainEquivIntertwiningMap` identifies
  `C^n(L, H, G; M)` with `Hom_G(⋀^n(L ⧸ H), M)`.
* In degree `0` (for a group `G`), `groupRelativeCohomologyZeroEquiv` identifies
  `H⁰(L, H, G; M)` with `M^L ∩ M^G`. In positive degree `n + 1`,
  `groupRelativeCohomologySuccIso` / `groupRelativeCohomologySuccEquiv` present
  `H^(n+1)(L, H, G; M)` as `groupRelativeCocycle / range groupRelativeDToCycles`.
* When `G` is a group, `cochainRepresentation` equips `L [⋀^Fin n]→ₗ[R] M` with the conjugation
  representation `(g · ω)(v) = ρM g (ω (ρL g⁻¹ ∘ v))` and `dIntertwiningMap` upgrades `d` to an
  intertwining map.

## Main definitions

* `TauCeti.LieModule.Cohomology.quotientRepresentation`: induced `G`-representation on
  `L ⧸ H.toLieSubmodule`.
* `TauCeti.LieModule.Cohomology.equivariantCochain`: `G`-equivariant cochains.
* `TauCeti.LieModule.Cohomology.horizontalEquivariantCochainEquivIntertwiningMap`:
  identification of horizontal `G`-equivariant cochains with `Hom_G(⋀^n(L ⧸ H), M)`.
* `TauCeti.LieModule.Cohomology.groupRelativeCochain` / `groupRelativeD` /
  `groupRelativeCochainComplex` / `groupRelativeCohomology`: the relative complex
  `C^•(L, H, G; M)` and its cohomology `H^•(L, H, G; M)`.
* `TauCeti.LieModule.Cohomology.groupRelativeCochainEquivIntertwiningMap`: identification of
  `C^n(L, H, G; M)` with `Hom_G(⋀^n(L ⧸ H), M)` when `G`-invariance implies `H`-invariance.
* `TauCeti.LieModule.Cohomology.groupRelativeCocycle` / `groupRelativeDToCycles` /
  `groupRelativeCohomologySuccIso` / `groupRelativeCohomologySuccEquiv` /
  `groupRelativeCohomologyZeroEquiv`.
* `TauCeti.LieModule.Cohomology.cochainRepresentation` / `dIntertwiningMap`: conjugation
  representation of a group `G` on cochains and equivariance of `d`.

## References

* A. Borel and N. Wallach, *Continuous Cohomology, Discrete Subgroups, and Representations of
  Reductive Groups*, 2nd ed., AMS, 2000, Ch. I, §1.
* G. Harder and A. Raghuram, *Eisenstein Cohomology for GL_N and the Special Values of
  Rankin–Selberg L-Functions*, Princeton University Press, 2020, §3.1.1.
-/

public section

open CategoryTheory

namespace TauCeti.LieModule.Cohomology

/-! ### Quotient representation and equivariant cochains -/

section EquivariantBasic

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {G : Type*} [Monoid G]

/-- The induced representation of `G` on `L ⧸ H.toLieSubmodule` when `ρL` stabilizes `H`. -/
def quotientRepresentation (H : LieSubalgebra R L) (ρL : Representation R G L)
    (hH : ∀ g, ∀ x ∈ H, ρL g x ∈ H) :
    Representation R G (L ⧸ H.toLieSubmodule) where
  toFun g :=
    Submodule.mapQ H.toLieSubmodule.toSubmodule H.toLieSubmodule.toSubmodule (ρL g)
      fun x hx ↦ hH g x hx
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    change LieSubmodule.Quotient.mk ((ρL 1) x) = LieSubmodule.Quotient.mk x
    rw [map_one]
    rfl
  map_mul' g₁ g₂ := by
    apply Submodule.linearMap_qext
    ext x
    change LieSubmodule.Quotient.mk ((ρL (g₁ * g₂)) x) =
      LieSubmodule.Quotient.mk ((ρL g₁) ((ρL g₂) x))
    rw [map_mul]
    rfl

@[simp]
theorem quotientRepresentation_apply_mk (H : LieSubalgebra R L) (ρL : Representation R G L)
    (hH : ∀ g, ∀ x ∈ H, ρL g x ∈ H) (g : G) (x : L) :
    quotientRepresentation H ρL hH g (LieSubmodule.Quotient.mk x) =
      LieSubmodule.Quotient.mk (ρL g x) := (rfl)

/-- The submodule of `G`-equivariant `n`-cochains: alternating maps `ω` satisfying
`ρM g (ω v) = ω (ρL g ∘ v)` for all `g : G` and `v : Fin n → L`. -/
def equivariantCochain (ρL : Representation R G L) (ρM : Representation R G M) (n : ℕ) :
    Submodule R (L [⋀^Fin n]→ₗ[R] M) where
  carrier := {ω | ∀ (g : G) (v : Fin n → L), ρM g (ω v) = ω (ρL g ∘ v)}
  add_mem' {ω₁ ω₂} h₁ h₂ g v := by simp [map_add, h₁ g v, h₂ g v]
  zero_mem' _ _ := by simp
  smul_mem' r ω h g v := by simp [map_smul, h g v]

@[simp]
theorem mem_equivariantCochain_iff {ρL : Representation R G L} {ρM : Representation R G M}
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ equivariantCochain ρL ρM n ↔ ∀ (g : G) (v : Fin n → L), ρM g (ω v) = ω (ρL g ∘ v) :=
  Iff.rfl

/-- Pullback along `L → L ⧸ H.toLieSubmodule` together with the exterior-power universal property
identifies horizontal `G`-equivariant cochains with `Hom_G(⋀^n(L ⧸ H), M)`. -/
noncomputable def horizontalEquivariantCochainEquivIntertwiningMap
    (H : LieSubalgebra R L) (ρL : Representation R G L) (ρM : Representation R G M)
    (hH : ∀ g, ∀ x ∈ H, ρL g x ∈ H) (n : ℕ) :
    (horizontalCochain R L H M n ⊓ equivariantCochain ρL ρM n :
        Submodule R (L [⋀^Fin n]→ₗ[R] M)) ≃ₗ[R]
      Representation.IntertwiningMap ((quotientRepresentation H ρL hH).exteriorPower n) ρM where
  toFun ω :=
    { toLinearMap := exteriorPower.alternatingMapLinearEquiv
        ((horizontalCochainEquiv R L H M n).symm ⟨ω.1, (Submodule.mem_inf.mp ω.2).1⟩)
      isIntertwining' g := by
        refine exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ ?_
        choose w hw using fun i ↦ H.toLieSubmodule.toSubmodule.mkQ_surjective (v i)
        have hfun : (fun i ↦ LieSubmodule.Quotient.mk (w i)) = v := funext hw
        rw [← hfun]
        change exteriorPower.alternatingMapLinearEquiv
            ((horizontalCochainEquiv R L H M n).symm ⟨ω.1, (Submodule.mem_inf.mp ω.2).1⟩)
            ((quotientRepresentation H ρL hH).exteriorPower n g
              (exteriorPower.ιMulti R n (fun i ↦ LieSubmodule.Quotient.mk (w i)))) =
          ρM g (exteriorPower.alternatingMapLinearEquiv
            ((horizontalCochainEquiv R L H M n).symm ⟨ω.1, (Submodule.mem_inf.mp ω.2).1⟩)
            (exteriorPower.ιMulti R n (fun i ↦ LieSubmodule.Quotient.mk (w i))))
        rw [Representation.exteriorPower_apply_ιMulti,
          exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
          exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
        have hcomp : quotientRepresentation H ρL hH g ∘
            (fun i ↦ LieSubmodule.Quotient.mk (w i)) =
            fun i ↦ LieSubmodule.Quotient.mk (ρL g (w i)) := by
          ext i
          rfl
        rw [hcomp, horizontalCochainEquiv_symm_apply_mk, horizontalCochainEquiv_symm_apply_mk]
        exact ((Submodule.mem_inf.mp ω.2).2 g w).symm }
  map_add' ω₁ ω₂ := Representation.IntertwiningMap.ext <| by
    change exteriorPower.alternatingMapLinearEquiv
        ((horizontalCochainEquiv R L H M n).symm
          (⟨ω₁.1, (Submodule.mem_inf.mp ω₁.2).1⟩ + ⟨ω₂.1, (Submodule.mem_inf.mp ω₂.2).1⟩)) =
      exteriorPower.alternatingMapLinearEquiv
          ((horizontalCochainEquiv R L H M n).symm ⟨ω₁.1, (Submodule.mem_inf.mp ω₁.2).1⟩) +
        exteriorPower.alternatingMapLinearEquiv
          ((horizontalCochainEquiv R L H M n).symm ⟨ω₂.1, (Submodule.mem_inf.mp ω₂.2).1⟩)
    rw [map_add, map_add]
  map_smul' r ω := Representation.IntertwiningMap.ext <| by
    change exteriorPower.alternatingMapLinearEquiv
        ((horizontalCochainEquiv R L H M n).symm
          (r • ⟨ω.1, (Submodule.mem_inf.mp ω.2).1⟩)) =
      r • exteriorPower.alternatingMapLinearEquiv
        ((horizontalCochainEquiv R L H M n).symm ⟨ω.1, (Submodule.mem_inf.mp ω.2).1⟩)
    rw [map_smul, map_smul]
  invFun f :=
    ⟨(horizontalCochainEquiv R L H M n
        (exteriorPower.alternatingMapLinearEquiv.symm f.toLinearMap)).1,
      (horizontalCochainEquiv R L H M n _).2, fun g v ↦ by
        have h := congrArg
          (fun φ ↦ φ (exteriorPower.ιMulti R n (fun i ↦ LieSubmodule.Quotient.mk (v i))))
          (f.isIntertwining' g)
        simp only [LinearMap.comp_apply, Representation.exteriorPower_apply_ιMulti] at h
        have hcomp : quotientRepresentation H ρL hH g ∘
            (fun i ↦ LieSubmodule.Quotient.mk (v i)) =
            fun i ↦ LieSubmodule.Quotient.mk (ρL g (v i)) := by
          ext i
          rfl
        rw [hcomp] at h
        rw [horizontalCochainEquiv_apply_val]
        change ρM g (exteriorPower.alternatingMapLinearEquiv.symm f.toLinearMap
            (fun i ↦ LieSubmodule.Quotient.mk (v i))) =
          exteriorPower.alternatingMapLinearEquiv.symm f.toLinearMap
            (fun i ↦ LieSubmodule.Quotient.mk (ρL g (v i)))
        rw [exteriorPower.alternatingMapLinearEquiv_symm_apply,
          exteriorPower.alternatingMapLinearEquiv_symm_apply]
        exact h.symm⟩
  left_inv ω := Subtype.ext <| AlternatingMap.ext fun v ↦ by
    dsimp only
    rw [LinearEquiv.symm_apply_apply, horizontalCochainEquiv_apply_val]
    exact horizontalCochainEquiv_symm_apply_mk R L H M n
      ⟨ω.1, (Submodule.mem_inf.mp ω.2).1⟩ v
  right_inv f := Representation.IntertwiningMap.ext <|
    exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      choose w hw using fun i ↦ H.toLieSubmodule.toSubmodule.mkQ_surjective (v i)
      have hfun : (fun i ↦ LieSubmodule.Quotient.mk (w i)) = v := funext hw
      rw [← hfun]
      change exteriorPower.alternatingMapLinearEquiv
          ((horizontalCochainEquiv R L H M n).symm
            (horizontalCochainEquiv R L H M n
              (exteriorPower.alternatingMapLinearEquiv.symm f.toLinearMap)))
          (exteriorPower.ιMulti R n (fun i ↦ LieSubmodule.Quotient.mk (w i))) =
        f (exteriorPower.ιMulti R n (fun i ↦ LieSubmodule.Quotient.mk (w i)))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
      rfl

@[simp]
theorem horizontalEquivariantCochainEquivIntertwiningMap_apply_ιMulti
    (H : LieSubalgebra R L) (ρL : Representation R G L) (ρM : Representation R G M)
    (hH : ∀ g, ∀ x ∈ H, ρL g x ∈ H) (n : ℕ)
    (ω : (horizontalCochain R L H M n ⊓ equivariantCochain ρL ρM n :
      Submodule R (L [⋀^Fin n]→ₗ[R] M))) (v : Fin n → L) :
    (horizontalEquivariantCochainEquivIntertwiningMap H ρL ρM hH n ω)
      (exteriorPower.ιMulti R n (fun i ↦ LieSubmodule.Quotient.mk (v i))) = ω.1 v := by
  change exteriorPower.alternatingMapLinearEquiv
      ((horizontalCochainEquiv R L H M n).symm ⟨ω.1, ω.2.1⟩)
      (exteriorPower.ιMulti R n (fun i ↦ LieSubmodule.Quotient.mk (v i))) = ω.1 v
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, horizontalCochainEquiv_symm_apply_mk]

end EquivariantBasic

/-! ### `(L, H, G)`-relative cochain complex `C^•(L, H, G; M)` -/

section GroupRelative

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable {G : Type*} [Monoid G]

/-- The Chevalley–Eilenberg differential preserves `G`-equivariant cochains whenever `G` acts by
Lie endomorphisms on `L` compatibly with the `L`-action on `M`. -/
theorem d_mem_equivariantCochain {ρL : Representation R G L} {ρM : Representation R G M}
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆)
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ equivariantCochain ρL ρM n) :
    d R L M n ω ∈ equivariantCochain ρL ρM (n + 1) := by
  intro g v
  cases n with
  | zero =>
    rw [d_zero_apply, d_zero_apply, hρM, hω g ![]]
    simp [Subsingleton.elim (ρL g ∘ ![]) ![]]
  | succ k =>
    rw [d_succ_apply, d_succ_apply, map_add, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_zsmul, hρM, hω g (i.removeNth v)]
      rfl
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_zsmul, hω g]
      congr 2
      ext t
      refine Fin.cases ?_ (fun s ↦ ?_) t
      · simp [hρL]
      · simp [Fin.removeNth]

/-- The submodule of `(L, H, G)`-relative `n`-cochains: cochains that are `H`-horizontal,
`H`-invariant, and `G`-equivariant. -/
def groupRelativeCochain (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M) (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  relativeCochain R L H M n ⊓ equivariantCochain ρL ρM n

/-- Membership in `groupRelativeCochain` is membership in both `relativeCochain` and
`equivariantCochain`. -/
theorem mem_groupRelativeCochain_iff {H : LieSubalgebra R L} {ρL : Representation R G L}
    {ρM : Representation R G M} {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ groupRelativeCochain H ρL ρM n ↔
      ω ∈ relativeCochain R L H M n ∧ ω ∈ equivariantCochain ρL ρM n :=
  Iff.rfl

/-- The Chevalley–Eilenberg differential preserves `(L, H, G)`-relative cochains. -/
theorem d_mem_groupRelativeCochain {H : LieSubalgebra R L} {ρL : Representation R G L}
    {ρM : Representation R G M}
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆)
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ groupRelativeCochain H ρL ρM n) :
    d R L M n ω ∈ groupRelativeCochain H ρL ρM (n + 1) :=
  ⟨d_mem_relativeCochain hω.1, d_mem_equivariantCochain hρL hρM hω.2⟩

/-- The `(L, H, G)`-relative Chevalley–Eilenberg differential. -/
def groupRelativeD (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    groupRelativeCochain H ρL ρM n →ₗ[R] groupRelativeCochain H ρL ρM (n + 1) :=
  ((d R L M n).comp (groupRelativeCochain H ρL ρM n).subtype).codRestrict
    (groupRelativeCochain H ρL ρM (n + 1)) fun ω ↦ d_mem_groupRelativeCochain hρL hρM ω.2

@[simp]
theorem groupRelativeD_coe (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) {n : ℕ}
    (ω : groupRelativeCochain H ρL ρM n) :
    (groupRelativeD H ρL ρM hρL hρM n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω.1 := (rfl)

/-- Consecutive `(L, H, G)`-relative differentials vanish on every cochain. -/
@[simp]
theorem groupRelativeD_groupRelativeD (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ)
    (ω : groupRelativeCochain H ρL ρM n) :
    groupRelativeD H ρL ρM hρL hρM (n + 1) (groupRelativeD H ρL ρM hρL hρM n ω) = 0 :=
  Subtype.ext (d_d n ω.1)

/-- Consecutive `(L, H, G)`-relative differentials compose to zero. -/
theorem groupRelativeD_comp_groupRelativeD (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    (groupRelativeD H ρL ρM hρL hρM (n + 1)).comp (groupRelativeD H ρL ρM hρL hρM n) = 0 :=
  LinearMap.ext (groupRelativeD_groupRelativeD H ρL ρM hρL hρM n)

/-- The `(L, H, G)`-relative Chevalley–Eilenberg cochain complex `C^•(L, H, G; M)`. -/
@[expose] noncomputable def groupRelativeCochainComplex (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (groupRelativeCochain H ρL ρM n))
    (fun n ↦ ModuleCat.ofHom (groupRelativeD H ρL ρM hρL hρM n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, groupRelativeD_comp_groupRelativeD, ModuleCat.ofHom_zero]

@[simp]
theorem groupRelativeCochainComplex_X (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    (groupRelativeCochainComplex H ρL ρM hρL hρM).X n =
      ModuleCat.of R (groupRelativeCochain H ρL ρM n) := (rfl)

@[simp]
theorem groupRelativeCochainComplex_d_succ (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    (groupRelativeCochainComplex H ρL ρM hρL hρM).d n (n + 1) =
      ModuleCat.ofHom (groupRelativeD H ρL ρM hρL hρM n) := by
  simp [groupRelativeCochainComplex]

/-- `(L, H, G)`-relative cohomology `H^n(L, H, G; M)`. -/
noncomputable abbrev groupRelativeCohomology (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) : ModuleCat R :=
  (groupRelativeCochainComplex H ρL ρM hρL hρM).homology n

/-- The canonical subcomplex inclusion `C^•(L, H, G; M) ⟶ C^•(L, H; M)`. -/
noncomputable def groupRelativeCochainComplexIncl (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) :
    groupRelativeCochainComplex H ρL ρM hρL hρM ⟶ relativeCochainComplex R L H M where
  f n := ModuleCat.ofHom
    (Submodule.inclusion (inf_le_left : groupRelativeCochain H ρL ρM n ≤ relativeCochain R L H M n))
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst hj
    let incl := fun n ↦
      Submodule.inclusion (inf_le_left : groupRelativeCochain H ρL ρM n ≤ relativeCochain R L H M n)
    change ModuleCat.ofHom (incl i) ≫ (relativeCochainComplex R L H M).d i (i + 1) =
      (groupRelativeCochainComplex H ρL ρM hρL hρM).d i (i + 1) ≫ ModuleCat.ofHom (incl (i + 1))
    rw [relativeCochainComplex_d_succ, groupRelativeCochainComplex_d_succ]
    apply ModuleCat.hom_ext
    ext (ω : groupRelativeCochain H ρL ρM i)
    apply Subtype.ext
    change (relativeD R L H M i (incl i ω) : L [⋀^Fin (i + 1)]→ₗ[R] M) =
      (groupRelativeD H ρL ρM hρL hρM i ω : L [⋀^Fin (i + 1)]→ₗ[R] M)
    rw [relativeD_coe, groupRelativeD_coe]
    rfl

/-- Canonical embedding of `(L, H, G)`-relative cochains into `Hom_G(⋀^n(L ⧸ H), M)`. -/
noncomputable def groupRelativeCochainToIntertwiningMap (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hH : ∀ g, ∀ x ∈ H, ρL g x ∈ H) (n : ℕ) :
    groupRelativeCochain H ρL ρM n →ₗ[R]
      Representation.IntertwiningMap ((quotientRepresentation H ρL hH).exteriorPower n) ρM :=
  (horizontalEquivariantCochainEquivIntertwiningMap H ρL ρM hH n).toLinearMap.comp
    (Submodule.inclusion fun _ hω ↦
      ⟨relativeCochain_le_horizontalCochain n (mem_groupRelativeCochain_iff.mp hω).1,
        (mem_groupRelativeCochain_iff.mp hω).2⟩)

/-- The canonical map from `(L, H, G)`-relative cochains into `Hom_G(⋀^n(L ⧸ H), M)` is
injective. -/
theorem groupRelativeCochainToIntertwiningMap_injective (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hH : ∀ g, ∀ x ∈ H, ρL g x ∈ H) (n : ℕ) :
    Function.Injective (groupRelativeCochainToIntertwiningMap H ρL ρM hH n) :=
  (horizontalEquivariantCochainEquivIntertwiningMap H ρL ρM hH n).injective.comp
    (Submodule.inclusion_injective _)

/-- When `G`-equivariance on horizontal cochains implies `H`-invariance (as holds whenever `G` is
a connected Lie group with Lie algebra `H`), `(L, H, G)`-relative cochains are canonically
identified with `Hom_G(⋀^n(L ⧸ H), M)`. -/
noncomputable def groupRelativeCochainEquivIntertwiningMap (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hH : ∀ g, ∀ x ∈ H, ρL g x ∈ H) (n : ℕ)
    (hGH : ∀ ω : L [⋀^Fin n]→ₗ[R] M,
      ω ∈ horizontalCochain R L H M n → ω ∈ equivariantCochain ρL ρM n →
        ∀ x ∈ H, ⁅x, ω⁆ = 0) :
    groupRelativeCochain H ρL ρM n ≃ₗ[R]
      Representation.IntertwiningMap ((quotientRepresentation H ρL hH).exteriorPower n) ρM :=
  (LinearEquiv.ofEq (groupRelativeCochain H ρL ρM n)
    (horizontalCochain R L H M n ⊓ equivariantCochain ρL ρM n) (by
      ext ω
      rw [mem_groupRelativeCochain_iff, Submodule.mem_inf, mem_relativeCochain_iff]
      exact ⟨fun h ↦ ⟨mem_horizontalCochain_iff.mpr h.1.1, h.2⟩,
        fun h ↦ ⟨⟨mem_horizontalCochain_iff.mp h.1, hGH ω h.1 h.2⟩, h.2⟩⟩)) ≪≫ₗ
    horizontalEquivariantCochainEquivIntertwiningMap H ρL ρM hH n

/-! ### Explicit presentation of `(L, H, G)`-relative cohomology -/

/-- The flat submodule of `(L, H, G)`-relative `n`-cocycles. -/
def groupRelativeCocycle (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M) (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  groupRelativeCochain H ρL ρM n ⊓ LinearMap.ker (d R L M n)

@[simp]
theorem mem_groupRelativeCocycle_iff {H : LieSubalgebra R L} {ρL : Representation R G L}
    {ρM : Representation R G M} {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ groupRelativeCocycle H ρL ρM n ↔
      ω ∈ groupRelativeCochain H ρL ρM n ∧ d R L M n ω = 0 :=
  Iff.rfl

/-- The `n`-th `(L, H, G)`-relative differential with codomain restricted to `(n + 1)`-cocycles. -/
def groupRelativeDToCycles (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    groupRelativeCochain H ρL ρM n →ₗ[R] groupRelativeCocycle H ρL ρM (n + 1) :=
  ((d R L M n).comp (groupRelativeCochain H ρL ρM n).subtype).codRestrict
    (groupRelativeCocycle H ρL ρM (n + 1)) fun ω ↦
      ⟨d_mem_groupRelativeCochain hρL hρM ω.2, d_d n ω.1⟩

@[simp]
theorem groupRelativeDToCycles_coe (H : LieSubalgebra R L) (ρL : Representation R G L)
    (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ)
    (ω : groupRelativeCochain H ρL ρM n) :
    (groupRelativeDToCycles H ρL ρM hρL hρM n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω.1 :=
  (rfl)

/-- In degree `n + 1`, `(L, H, G)`-relative cohomology is isomorphic to
`groupRelativeCocycle / range groupRelativeDToCycles`. -/
noncomputable def groupRelativeCohomologySuccIso (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    groupRelativeCohomology H ρL ρM hρL hρM (n + 1) ≅
      ModuleCat.of R (groupRelativeCocycle H ρL ρM (n + 1) ⧸
        LinearMap.range (groupRelativeDToCycles H ρL ρM hρL hρM n)) :=
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (ModuleCat.ofHom (groupRelativeD H ρL ρM hρL hρM n))
      (ModuleCat.ofHom (groupRelativeD H ρL ρM hρL hρM (n + 1))) (by
        rw [← ModuleCat.ofHom_comp, groupRelativeD_comp_groupRelativeD, ModuleCat.ofHom_zero])
  let eKer : LinearMap.ker S.g.hom ≃ₗ[R] groupRelativeCocycle H ρL ρM (n + 1) :=
    { toFun ω := ⟨ω.1.1, ω.1.2, congrArg Subtype.val (LinearMap.mem_ker.mp ω.2)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      invFun ω := ⟨⟨ω.1, ω.2.1⟩, Subtype.ext ω.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let hMap :
      (LinearMap.range S.moduleCatToCycles).map eKer.toLinearMap =
        LinearMap.range (groupRelativeDToCycles H ρL ρM hρL hρM n) := by
    ext ⟨ω, hω⟩
    constructor
    · rintro ⟨_, ⟨η, rfl⟩, h⟩
      exact ⟨η, Subtype.ext (congrArg Subtype.val h)⟩
    · rintro ⟨η, h⟩
      exact ⟨S.moduleCatToCycles η, ⟨η, rfl⟩, Subtype.ext (congrArg Subtype.val h)⟩
  let eSC : (groupRelativeCochainComplex H ρL ρM hρL hρM).sc' n (n + 1) (n + 2) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (groupRelativeCochainComplex_d_succ H ρL ρM hρL hρM n).symm
      (groupRelativeCochainComplex_d_succ H ρL ρM hρL hρM (n + 1)).symm
  ((groupRelativeCochainComplex H ρL ρM hρL hρM).homologyIsoSc' n (n + 1) (n + 2)
    (by simp) (by simp)).trans <|
    (ShortComplex.homologyMapIso eSC).trans <|
      S.moduleCatHomologyIso.trans
        (Submodule.Quotient.equiv _ _ eKer hMap).toModuleIso

/-- In degree `n + 1`, `(L, H, G)`-relative cohomology is linearly equivalent to
`groupRelativeCocycle / range groupRelativeDToCycles`. -/
noncomputable def groupRelativeCohomologySuccEquiv (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    groupRelativeCohomology H ρL ρM hρL hρM (n + 1) ≃ₗ[R]
      groupRelativeCocycle H ρL ρM (n + 1) ⧸
        LinearMap.range (groupRelativeDToCycles H ρL ρM hρL hρM n) :=
  (groupRelativeCohomologySuccIso H ρL ρM hρL hρM n).toLinearEquiv

/-- In degree `0`, `(L, H, G)`-relative cohomology is isomorphic to the kernel of
`groupRelativeD ... 0`. -/
noncomputable def groupRelativeCohomologyZeroIsoKer (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) :
    groupRelativeCohomology H ρL ρM hρL hρM 0 ≅
      ModuleCat.of R (LinearMap.ker (groupRelativeD H ρL ρM hρL hρM 0)) :=
  (((groupRelativeCochainComplex H ρL ρM hρL hρM).homologyIsoSc' 0 0 1
      (by simp) (by simp)).trans
    (ShortComplex.asIsoHomologyπ
      (S := (groupRelativeCochainComplex H ρL ρM hρL hρM).sc' 0 0 1)
      ((groupRelativeCochainComplex H ρL ρM hρL hρM).shape 0 0 (by simp))).symm).trans
    (((groupRelativeCochainComplex H ρL ρM hρL hρM).sc' 0 0 1).moduleCatCyclesIso.trans
      (LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ (by
        change LinearMap.ker ((groupRelativeCochainComplex H ρL ρM hρL hρM).d 0 1).hom =
          LinearMap.ker (groupRelativeD H ρL ρM hρL hρM 0)
        rw [groupRelativeCochainComplex_d_succ]
        rfl))))

/-- `(L, H, G)`-relative cohomology vanishes whenever the relative cochain module is subsingleton.
-/
theorem subsingleton_groupRelativeCohomology_of_subsingleton {H : LieSubalgebra R L}
    {ρL : Representation R G L} {ρM : Representation R G M}
    {hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆}
    {hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆} {n : ℕ}
    [h : Subsingleton (groupRelativeCochain H ρL ρM n)] :
    Subsingleton (groupRelativeCohomology H ρL ρM hρL hρM n) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact ShortComplex.isZero_homology_of_isZero_X₂
    (S := (groupRelativeCochainComplex H ρL ρM hρL hρM).sc n)
    (ModuleCat.isZero_iff_subsingleton.mpr h)

/-- `(L, H, G)`-relative cochains vanish in degrees strictly above the rank of a finite free
quotient `L ⧸ H.toLieSubmodule`. -/
theorem subsingleton_groupRelativeCochain_of_finrank_lt {H : LieSubalgebra R L}
    {ρL : Representation R G L} {ρM : Representation R G M}
    [Module.Free R (L ⧸ H.toLieSubmodule)] [Module.Finite R (L ⧸ H.toLieSubmodule)]
    {n : ℕ} (h : Module.finrank R (L ⧸ H.toLieSubmodule) < n) :
    Subsingleton (groupRelativeCochain H ρL ρM n) := by
  have : Subsingleton (relativeCochain R L H M n) :=
    subsingleton_relativeCochain_of_finrank_lt h
  refine ⟨fun ω₁ ω₂ ↦ ?_⟩
  have hEq : (⟨ω₁.1, ω₁.2.1⟩ : relativeCochain R L H M n) = ⟨ω₂.1, ω₂.2.1⟩ :=
    Subsingleton.elim _ _
  exact Subtype.ext (congrArg (fun z : relativeCochain R L H M n ↦ z.1) hEq)

/-- `(L, H, G)`-relative cohomology vanishes in degrees strictly above the rank of a finite free
quotient `L ⧸ H.toLieSubmodule`. -/
theorem subsingleton_groupRelativeCohomology_of_finrank_lt {H : LieSubalgebra R L}
    {ρL : Representation R G L} {ρM : Representation R G M}
    {hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆}
    {hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆}
    [Module.Free R (L ⧸ H.toLieSubmodule)] [Module.Finite R (L ⧸ H.toLieSubmodule)]
    {n : ℕ} (h : Module.finrank R (L ⧸ H.toLieSubmodule) < n) :
    Subsingleton (groupRelativeCohomology H ρL ρM hρL hρM n) := by
  have : Subsingleton (groupRelativeCochain H ρL ρM n) :=
    subsingleton_groupRelativeCochain_of_finrank_lt h
  exact subsingleton_groupRelativeCohomology_of_subsingleton

end GroupRelative

/-! ### Conjugation representation of a group `G` on cochains -/

section GroupInvariants

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {G : Type*} [Group G]

/-- The conjugation representation of a group `G` on `n`-cochains `L [⋀^Fin n]→ₗ[R] M`:
`(g · ω)(v) = ρM g (ω (ρL g⁻¹ ∘ v))`. Expressed via `Representation` rather than a global
`DistribMulAction` instance to avoid conflicting with Mathlib's pointwise action on
`AlternatingMap`. -/
def cochainRepresentation (ρL : Representation R G L) (ρM : Representation R G M) (n : ℕ) :
    Representation R G (L [⋀^Fin n]→ₗ[R] M) where
  toFun g :=
    { toFun ω := LinearMap.compAlternatingMap (ρM g) (ω.compLinearMap (ρL g⁻¹))
      map_add' _ _ := AlternatingMap.ext fun _ ↦ by simp
      map_smul' _ _ := AlternatingMap.ext fun _ ↦ by simp }
  map_one' := by
    ext ω v
    simp
  map_mul' g₁ g₂ := by
    ext ω v
    simp [mul_inv_rev]

@[simp]
theorem cochainRepresentation_apply (ρL : Representation R G L) (ρM : Representation R G M)
    (n : ℕ) (g : G) (ω : L [⋀^Fin n]→ₗ[R] M) (v : Fin n → L) :
    cochainRepresentation ρL ρM n g ω v = ρM g (ω (ρL g⁻¹ ∘ v)) := (rfl)

/-- A cochain is invariant under `cochainRepresentation` if and only if it is `G`-equivariant. -/
theorem mem_cochainRepresentation_invariants_iff (ρL : Representation R G L)
    (ρM : Representation R G M) {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ (cochainRepresentation ρL ρM n).invariants ↔ ω ∈ equivariantCochain ρL ρM n := by
  rw [Representation.mem_invariants, mem_equivariantCochain_iff]
  constructor
  · intro h g v
    have hv := congrArg (fun f : L [⋀^Fin n]→ₗ[R] M ↦ f (ρL g ∘ v)) (h g)
    have hcomp : ρL g⁻¹ ∘ (ρL g ∘ v) = v := by
      ext i
      change (ρL g⁻¹ * ρL g) (v i) = v i
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    simpa [cochainRepresentation_apply, hcomp] using hv
  · intro h g
    ext v
    rw [cochainRepresentation_apply, h g (ρL g⁻¹ ∘ v)]
    congr 1
    ext i
    change (ρL g * ρL g⁻¹) (v i) = v i
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

variable [LieRingModule L M] [LieModule R L M]

/-- In degree `0`, `(L, H, G)`-relative cohomology for a group `G` is the submodule of
`(L, G)`-invariants `M^L ∩ M^G`. -/
noncomputable def groupRelativeCohomologyZeroEquiv (H : LieSubalgebra R L)
    (ρL : Representation R G L) (ρM : Representation R G M)
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) :
    groupRelativeCohomology H ρL ρM hρL hρM 0 ≃ₗ[R]
      ((LieModule.maxTrivSubmodule R L M).toSubmodule ⊓ ρM.invariants : Submodule R M) :=
  (groupRelativeCohomologyZeroIsoKer H ρL ρM hρL hρM).toLinearEquiv ≪≫ₗ
    { toFun := fun ω ↦ ⟨ω.1.1 ![], fun x ↦ by
        have h : d R L M 0 ω.1.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ω.2)
        have hx := congrArg (fun f : L [⋀^Fin 1]→ₗ[R] M ↦ f ![x]) h
        rw [d_zero_apply] at hx
        exact hx, fun g ↦ by
        simpa [Subsingleton.elim (ρL g ∘ ![]) ![]] using ω.1.2.2 g ![]⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun m ↦
        ⟨⟨AlternatingMap.constLinearEquivOfIsEmpty (R' := R) (M'' := L) (N'' := M) (ι := Fin 0)
            m.1,
          (mem_relativeCochain_zero_iff).mpr fun x _ ↦ m.2.1 x,
          fun g _ ↦ m.2.2 g⟩, by
          rw [LinearMap.mem_ker]
          apply Subtype.ext
          ext v
          rw [groupRelativeD_coe, d_zero_apply]
          exact m.2.1 (v 0)⟩
      left_inv := fun ω ↦ by
        apply Subtype.ext
        apply Subtype.ext
        ext v
        simp [Subsingleton.elim v ![]]
      right_inv := fun _ ↦ rfl }

/-- The Chevalley–Eilenberg differential is a `G`-intertwining map for the conjugation
representation on cochains. -/
def dIntertwiningMap {ρL : Representation R G L} {ρM : Representation R G M}
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) :
    Representation.IntertwiningMap (cochainRepresentation ρL ρM n)
      (cochainRepresentation ρL ρM (n + 1)) where
  toLinearMap := d R L M n
  isIntertwining' g := by
    ext ω v
    change d R L M n (cochainRepresentation ρL ρM n g ω) v =
      ρM g (d R L M n ω (ρL g⁻¹ ∘ v))
    have hgi : ∀ x : L, ρL g (ρL g⁻¹ x) = x := fun x ↦ by
      change (ρL g * ρL g⁻¹) x = x
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    cases n with
    | zero =>
      simp only [d_zero_apply, cochainRepresentation_apply, hρM, Function.comp_apply, hgi]
      congr 1
      exact congrArg (ρM g) (congrArg ω (Subsingleton.elim _ _))
    | succ k =>
      rw [d_succ_apply, d_succ_apply, map_add, map_sum, map_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_zsmul, hρM, cochainRepresentation_apply]
        simp only [Function.comp_apply, hgi]
        rfl
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_zsmul, cochainRepresentation_apply]
        congr 3
        ext t
        refine Fin.cases ?_ (fun s ↦ ?_) t
        · simp [hρL]
        · simp [Fin.removeNth]

@[simp]
theorem dIntertwiningMap_apply {ρL : Representation R G L} {ρM : Representation R G M}
    (hρL : ∀ g x y, ρL g ⁅x, y⁆ = ⁅ρL g x, ρL g y⁆)
    (hρM : ∀ g x m, ρM g ⁅x, m⁆ = ⁅ρL g x, ρM g m⁆) (n : ℕ) (ω : L [⋀^Fin n]→ₗ[R] M) :
    dIntertwiningMap hρL hρM n ω = d R L M n ω := (rfl)

end GroupInvariants

end TauCeti.LieModule.Cohomology
