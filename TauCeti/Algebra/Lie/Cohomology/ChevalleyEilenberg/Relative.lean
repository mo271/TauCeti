/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.LowDegree
public import TauCeti.LinearAlgebra.Multilinear.Quotient

/-!
# Relative Chevalley–Eilenberg cochains and cohomology

Given a Lie algebra `L` over a commutative ring `R`, a Lie subalgebra `H : LieSubalgebra R L`,
and an `L`-module `M`, this file defines the purely Lie-algebraic relative Chevalley–Eilenberg
complex `C^•(L, H; M)` and its cohomology `H^•(L, H; M)`:

* An `n`-cochain `ω : L [⋀^Fin n]→ₗ[R] M` is *horizontal* (`horizontalCochain`) if it vanishes
  whenever one of its arguments lies in `H`. Pullback along the quotient map `L → L ⧸ H` identifies
  `horizontalCochain` with `(L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M` (`horizontalCochainEquiv`).
* An `n`-cochain is *relative* (`relativeCochain`) if it is both horizontal and `H`-invariant
  (`∀ x ∈ H, ⁅x, ω⁆ = 0`). Cartan's formula `ι_x d ω = ⁅x, ω⁆ - d ι_x ω` shows that the
  Chevalley–Eilenberg differential `d` preserves relative cochains (`d_mem_relativeCochain`),
  producing a subcomplex `relativeCochainComplex R L H M ⟶ cochainComplex R L M`.
* `relativeCochainEquiv` identifies `relativeCochain` with the `H`-invariants of alternating maps
  on `L ⧸ H.toLieSubmodule`.
* When `H = ⊥`, the relative complex coincides with the full Chevalley–Eilenberg complex
  (`relativeCochainComplexBotIso`).
* In degree `0`, `relativeCohomologyZeroEquiv` identifies `H⁰(L, H; M)` with `M^L`.
* In positive degree `n + 1`, `relativeCohomologySuccIso` and `relativeCohomologySuccEquiv`
  present `H^(n+1)(L, H; M)` as `relativeCocycle / range relativeDToCycles`.
* Above `Module.finrank R (L ⧸ H.toLieSubmodule)`, relative cochains and cohomology vanish when
  the quotient is finite free (`subsingleton_relativeCochain_of_finrank_lt`,
  `subsingleton_relativeCohomology_of_finrank_lt`).

For the group-enhanced relative complex `C^•(L, H, G; M)`, see
`TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg.Equivariant`.

## Main definitions

* `TauCeti.LieModule.Cohomology.horizontalCochain` / `horizontalCochainEquiv`: horizontal
  cochains and descent to `L ⧸ H.toLieSubmodule`.
* `TauCeti.LieModule.Cohomology.relativeCochain` / `relativeD` / `relativeCochainComplex` /
  `relativeCohomology`: the relative complex `C^•(L, H; M)` and its cohomology `H^•(L, H; M)`.
* `TauCeti.LieModule.Cohomology.relativeCochainComplexIncl` / `relativeCochainComplexBotIso`:
  subcomplex inclusion into `cochainComplex` and trivial-subalgebra isomorphism.
* `TauCeti.LieModule.Cohomology.relativeCochainEquiv`: identification of `C^n(L, H; M)` with
  `H`-invariant alternating maps on `L ⧸ H.toLieSubmodule`.
* `TauCeti.LieModule.Cohomology.relativeCocycle` / `relativeDToCycles`: flat cocycle submodule
  and restricted differential for `relativeCohomologySuccIso` / `relativeCohomologySuccEquiv`.
* `TauCeti.LieModule.Cohomology.relativeCohomologyZeroEquiv` /
  `relativeCohomologyZeroEquivOfIsTrivial`: `H⁰(L, H; M) ≃ M^L` (and `≃ M` for trivial `M`).

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), §22–§28.
* A. Borel and N. Wallach, *Continuous Cohomology, Discrete Subgroups, and Representations of
  Reductive Groups*, 2nd ed., AMS, 2000, Ch. I, §1.
-/

public section

open CategoryTheory

namespace TauCeti.LieModule.Cohomology

/-! ### Horizontal cochains -/

section Horizontal

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (H : LieSubalgebra R L)
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The submodule of `H`-horizontal `n`-cochains: alternating maps `L [⋀^Fin n]→ₗ[R] M` that
vanish whenever one of their arguments lies in `H`. -/
def horizontalCochain (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) where
  carrier := {ω | ∀ (v : Fin n → L) (i : Fin n), v i ∈ H → ω v = 0}
  add_mem' {ω₁ ω₂} h₁ h₂ v i hi := by simp [h₁ v i hi, h₂ v i hi]
  zero_mem' _ _ _ := rfl
  smul_mem' r ω h v i hi := by simp [h v i hi]

variable {R L H M}

/-- Membership in `horizontalCochain` is vanishing on every tuple with an entry in `H`. -/
@[simp]
theorem mem_horizontalCochain_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ horizontalCochain R L H M n ↔ ∀ (v : Fin n → L) (i : Fin n), v i ∈ H → ω v = 0 :=
  Iff.rfl

/-- Every `0`-cochain is horizontal. -/
@[simp]
theorem horizontalCochain_zero : horizontalCochain R L H M 0 = ⊤ := by
  ext ω
  simp only [mem_horizontalCochain_iff, Submodule.mem_top, iff_true]
  exact fun _ i _ ↦ i.elim0

/-- Every cochain is horizontal with respect to the trivial subalgebra `⊥`. -/
@[simp]
theorem horizontalCochain_bot (n : ℕ) :
    horizontalCochain R L (⊥ : LieSubalgebra R L) M n = ⊤ := by
  ext ω
  simp only [mem_horizontalCochain_iff, LieSubalgebra.mem_bot, Submodule.mem_top, iff_true]
  exact fun v i hi ↦ ω.map_coord_zero i hi

/-- In positive degree, a cochain is horizontal if and only if its interior product with every
element of `H` vanishes. -/
theorem mem_horizontalCochain_succ_iff {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M} :
    ω ∈ horizontalCochain R L H M (n + 1) ↔ ∀ x ∈ H, ω.curryLeft x = 0 := by
  constructor
  · intro hω x hx
    ext w
    exact hω (Matrix.vecCons x w) 0 hx
  · intro hω v i hi
    have hcons : ∀ u : Fin (n + 1) → L, Matrix.vecCons (u 0) (Fin.tail u) = u := fun u ↦ by
      ext k
      refine Fin.cases rfl (fun _ ↦ rfl) k
    by_cases hi0 : i = 0
    · subst hi0
      rw [← hcons v]
      have h := congrArg (fun f : L [⋀^Fin n]→ₗ[R] M ↦ f (Fin.tail v)) (hω (v 0) hi)
      simpa [AlternatingMap.curryLeft_apply_apply] using h
    · have hswap := ω.map_swap v (Ne.symm hi0)
      have hv0 : (v ∘ Equiv.swap 0 i) 0 = v i := by simp
      have hzero : ω (v ∘ Equiv.swap 0 i) = 0 := by
        rw [← hcons (v ∘ Equiv.swap 0 i), hv0]
        have h := congrArg (fun f : L [⋀^Fin n]→ₗ[R] M ↦ f (Fin.tail (v ∘ Equiv.swap 0 i)))
          (hω (v i) hi)
        simpa [AlternatingMap.curryLeft_apply_apply] using h
      rw [hzero] at hswap
      exact neg_eq_zero.mp hswap.symm

/-- Interior product with any element of `L` preserves horizontality. -/
theorem curryLeft_mem_horizontalCochain {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M}
    (hω : ω ∈ horizontalCochain R L H M (n + 1)) (x : L) :
    ω.curryLeft x ∈ horizontalCochain R L H M n := by
  intro v i hi
  exact hω (Matrix.vecCons x v) i.succ hi

/-- Pullback of alternating maps from `L ⧸ H.toLieSubmodule` along the quotient map lands in
`horizontalCochain`. -/
def horizontalPullback (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
    (H : LieSubalgebra R L) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) →ₗ[R] horizontalCochain R L H M n where
  toFun η := ⟨η.compLinearMap H.toLieSubmodule.toSubmodule.mkQ, fun v i hi ↦ by
    apply η.map_coord_zero i
    exact (Submodule.Quotient.mk_eq_zero H.toLieSubmodule.toSubmodule).mpr hi⟩
  map_add' η₁ η₂ := Subtype.ext (AlternatingMap.add_compLinearMap η₁ η₂ _)
  map_smul' _ _ := Subtype.ext (AlternatingMap.ext fun _ ↦ rfl)

@[simp]
theorem horizontalPullback_apply_val (R : Type*) [CommRing R] (L : Type*) [LieRing L]
    [LieAlgebra R L] (H : LieSubalgebra R L) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ)
    (η : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) :
    (horizontalPullback R L H M n η : L [⋀^Fin n]→ₗ[R] M) =
      η.compLinearMap H.toLieSubmodule.toSubmodule.mkQ := (rfl)

/-- Pullback along `L → L ⧸ H.toLieSubmodule` is a bijection onto `horizontalCochain`. -/
theorem horizontalPullback_bijective (R : Type*) [CommRing R] (L : Type*) [LieRing L]
    [LieAlgebra R L] (H : LieSubalgebra R L) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Bijective (horizontalPullback R L H M n) := by
  refine ⟨fun η₁ η₂ h ↦ ?_, fun ω ↦ ?_⟩
  · exact AlternatingMap.compLinearMap_injective H.toLieSubmodule.toSubmodule.mkQ
      H.toLieSubmodule.toSubmodule.mkQ_surjective (congrArg Subtype.val h)
  · classical
    let W : Submodule R L := H.toLieSubmodule.toSubmodule
    have hf : ∀ [DecidableEq (Fin n)] (m : Fin n → L) (j : Fin n) (x : L), x ∈ W →
        ω.1.toMultilinearMap (Function.update m j x) = 0 :=
      fun _ j _ hx ↦ ω.2 _ j (by simpa [W] using hx)
    refine ⟨{ ω.1.toMultilinearMap.liftQ (fun _ ↦ W) hf with
      map_eq_zero_of_eq' := fun v i j hij hne ↦ ?_ }, Subtype.ext (AlternatingMap.ext fun v ↦ ?_)⟩
    · have h := ω.1.toMultilinearMap.liftQ_apply (fun _ ↦ W) hf (fun k ↦ (v k).out)
      simp only [Submodule.Quotient.mk_out] at h
      exact h.trans (ω.1.map_eq_zero_of_eq _ (congrArg Quotient.out hij) hne)
    · exact ω.1.toMultilinearMap.liftQ_apply (fun _ ↦ W) hf v

/-- **Descent of horizontal cochains.** Pullback along `L → L ⧸ H.toLieSubmodule` identifies
alternating maps on the quotient `L ⧸ H.toLieSubmodule` with `H`-horizontal cochains on `L`. -/
noncomputable def horizontalCochainEquiv (R : Type*) [CommRing R] (L : Type*) [LieRing L]
    [LieAlgebra R L] (H : LieSubalgebra R L) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) ≃ₗ[R] horizontalCochain R L H M n :=
  LinearEquiv.ofBijective _ (horizontalPullback_bijective R L H M n)

@[simp]
theorem horizontalCochainEquiv_apply_val (R : Type*) [CommRing R] (L : Type*) [LieRing L]
    [LieAlgebra R L] (H : LieSubalgebra R L) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ)
    (η : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) :
    (horizontalCochainEquiv R L H M n η : L [⋀^Fin n]→ₗ[R] M) =
      η.compLinearMap H.toLieSubmodule.toSubmodule.mkQ := (rfl)

@[simp]
theorem horizontalCochainEquiv_symm_apply_mk (R : Type*) [CommRing R] (L : Type*) [LieRing L]
    [LieAlgebra R L] (H : LieSubalgebra R L) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ)
    (ω : horizontalCochain R L H M n) (v : Fin n → L) :
    (horizontalCochainEquiv R L H M n).symm ω (fun i ↦ LieSubmodule.Quotient.mk (v i)) =
      ω.1 v :=
  AlternatingMap.congr_fun
    (congrArg Subtype.val ((horizontalCochainEquiv R L H M n).apply_symm_apply ω)) v

variable [LieRingModule L M] [LieModule R L M]

/-- The Lie action of elements of `H` preserves `horizontalCochain`. -/
theorem lie_mem_horizontalCochain {n : ℕ} {x : L} (hx : x ∈ H) {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ horizontalCochain R L H M n) :
    ⁅x, ω⁆ ∈ horizontalCochain R L H M n := by
  intro v i hi
  rw [AlternatingMap.lie_apply, hω v i hi, lie_zero, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_cases hji : j = i
  · subst hji
    exact hω _ j (by simpa using H.lie_mem hx hi)
  · exact hω _ i (by simpa [Function.update_of_ne (Ne.symm hji)] using hi)

/-- Pullback along `L → L ⧸ H.toLieSubmodule` intertwines the Lie action of `H`. -/
theorem lie_compLinearMap_mkQ {n : ℕ} (h : H)
    (η : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) :
    ⁅(h : L), η.compLinearMap H.toLieSubmodule.toSubmodule.mkQ⁆ =
      ⁅h, η⁆.compLinearMap H.toLieSubmodule.toSubmodule.mkQ := by
  ext v
  simp only [AlternatingMap.lie_apply, AlternatingMap.compLinearMap_apply]
  change ⁅(h : L), η (fun i ↦ LieSubmodule.Quotient.mk (v i))⁆ -
      ∑ i, η (H.toLieSubmodule.toSubmodule.mkQ ∘ Function.update v i ⁅(h : L), v i⁆) =
    ⁅(h : L), η (fun i ↦ LieSubmodule.Quotient.mk (v i))⁆ -
      ∑ i, η (Function.update (fun j ↦ LieSubmodule.Quotient.mk (v j)) i
        ⁅h, (LieSubmodule.Quotient.mk (v i) : L ⧸ H.toLieSubmodule)⁆)
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  ext j
  by_cases hji : j = i
  · subst hji
    change LieSubmodule.Quotient.mk (Function.update v j ⁅(h : L), v j⁆ j) =
      Function.update (fun k ↦ LieSubmodule.Quotient.mk (v k)) j
        ⁅h, (LieSubmodule.Quotient.mk (v j) : L ⧸ H.toLieSubmodule)⁆ j
    rw [Function.update_self, Function.update_self]
    rfl
  · change LieSubmodule.Quotient.mk (Function.update v i ⁅(h : L), v i⁆ j) =
      Function.update (fun k ↦ LieSubmodule.Quotient.mk (v k)) i _ j
    rw [Function.update_of_ne hji, Function.update_of_ne hji]

end Horizontal

/-! ### Relative cochains and cohomology `C^•(L, H; M)` -/

section Relative

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (H : LieSubalgebra R L)
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The submodule of `H`-relative `n`-cochains of `L` with coefficients in `M`: alternating maps
that are both `H`-horizontal and `H`-invariant (`∀ x ∈ H, ⁅x, ω⁆ = 0`). -/
def relativeCochain (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) where
  carrier := {ω | ω ∈ horizontalCochain R L H M n ∧ ∀ x ∈ H, ⁅x, ω⁆ = 0}
  add_mem' {ω₁ ω₂} h₁ h₂ :=
    ⟨Submodule.add_mem _ h₁.1 h₂.1, fun x hx ↦ by rw [lie_add, h₁.2 x hx, h₂.2 x hx, add_zero]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ ↦ lie_zero _⟩
  smul_mem' r ω h :=
    ⟨Submodule.smul_mem _ r h.1, fun x hx ↦ by rw [lie_smul, h.2 x hx, smul_zero]⟩

variable {R L H M}

/-- Membership in `relativeCochain` is horizontality together with `H`-invariance. -/
theorem mem_relativeCochain_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ relativeCochain R L H M n ↔
      (∀ (v : Fin n → L) (i : Fin n), v i ∈ H → ω v = 0) ∧ ∀ x ∈ H, ⁅x, ω⁆ = 0 :=
  Iff.rfl

/-- Relative cochains are horizontal. -/
theorem relativeCochain_le_horizontalCochain (n : ℕ) :
    relativeCochain R L H M n ≤ horizontalCochain R L H M n :=
  fun _ h ↦ h.1

/-- A `0`-cochain is `H`-relative if and only if its value `ω ![]` is `H`-invariant. -/
theorem mem_relativeCochain_zero_iff {ω : L [⋀^Fin 0]→ₗ[R] M} :
    ω ∈ relativeCochain R L H M 0 ↔ ∀ x ∈ H, ⁅x, ω ![]⁆ = 0 := by
  rw [mem_relativeCochain_iff]
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ⟨fun _ i _ ↦ i.elim0, fun x hx ↦ ?_⟩⟩
  · have := congrArg (fun f : L [⋀^Fin 0]→ₗ[R] M ↦ f ![]) (h.2 x hx)
    simpa [AlternatingMap.lie_apply] using this
  · ext v
    simp [AlternatingMap.lie_apply, Subsingleton.elim v ![], h x hx]

/-- In positive degree, a cochain is `H`-relative if and only if both `ι_x ω = 0` and
`⁅x, ω⁆ = 0` for all `x ∈ H`. -/
theorem mem_relativeCochain_succ_iff {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M} :
    ω ∈ relativeCochain R L H M (n + 1) ↔
      (∀ x ∈ H, ω.curryLeft x = 0) ∧ ∀ x ∈ H, ⁅x, ω⁆ = 0 := by
  rw [← mem_horizontalCochain_succ_iff]
  rfl

/-- With respect to the trivial subalgebra `⊥`, every cochain is relative. -/
@[simp]
theorem relativeCochain_bot (n : ℕ) :
    relativeCochain R L (⊥ : LieSubalgebra R L) M n = ⊤ := by
  ext ω
  simp only [mem_relativeCochain_iff, LieSubalgebra.mem_bot, Submodule.mem_top, iff_true]
  exact ⟨fun v i hi ↦ ω.map_coord_zero i hi, fun x hx ↦ by rw [hx, zero_lie]⟩

/-- The Chevalley–Eilenberg differential maps `H`-relative cochains into `H`-relative cochains. -/
theorem d_mem_relativeCochain {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ relativeCochain R L H M n) :
    d R L M n ω ∈ relativeCochain R L H M (n + 1) := by
  rw [mem_relativeCochain_succ_iff]
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ by rw [lie_d, hω.2 x hx, map_zero]⟩
  cases n with
  | zero =>
    rw [curryLeft_d_zero, hω.2 x hx]
  | succ k =>
    rw [curryLeft_d_succ, hω.2 x hx, (mem_horizontalCochain_succ_iff.mp hω.1) x hx, map_zero,
      sub_zero]

variable (R L H M)

/-- The relative Chevalley–Eilenberg differential `C^n(L, H; M) → C^(n+1)(L, H; M)`. -/
def relativeD (n : ℕ) :
    relativeCochain R L H M n →ₗ[R] relativeCochain R L H M (n + 1) :=
  ((d R L M n).comp (relativeCochain R L H M n).subtype).codRestrict
    (relativeCochain R L H M (n + 1)) fun ω ↦ d_mem_relativeCochain ω.2

@[simp]
theorem relativeD_coe {n : ℕ} (ω : relativeCochain R L H M n) :
    (relativeD R L H M n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω.1 := (rfl)

/-- Consecutive relative differentials vanish on every cochain. -/
@[simp]
theorem relativeD_relativeD (n : ℕ) (ω : relativeCochain R L H M n) :
    relativeD R L H M (n + 1) (relativeD R L H M n ω) = 0 :=
  Subtype.ext (d_d n ω.1)

/-- Consecutive relative differentials compose to zero. -/
theorem relativeD_comp_relativeD (n : ℕ) :
    (relativeD R L H M (n + 1)).comp (relativeD R L H M n) = 0 :=
  LinearMap.ext (relativeD_relativeD R L H M n)

/-- The relative Chevalley–Eilenberg cochain complex `C^•(L, H; M)`. -/
@[expose] noncomputable def relativeCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (relativeCochain R L H M n))
    (fun n ↦ ModuleCat.ofHom (relativeD R L H M n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, relativeD_comp_relativeD, ModuleCat.ofHom_zero]

@[simp]
theorem relativeCochainComplex_X (n : ℕ) :
    (relativeCochainComplex R L H M).X n = ModuleCat.of R (relativeCochain R L H M n) := (rfl)

@[simp]
theorem relativeCochainComplex_d_succ (n : ℕ) :
    (relativeCochainComplex R L H M).d n (n + 1) = ModuleCat.ofHom (relativeD R L H M n) := by
  simp [relativeCochainComplex]

/-- Relative Lie algebra cohomology `H^n(L, H; M)`. -/
noncomputable abbrev relativeCohomology (n : ℕ) : ModuleCat R :=
  (relativeCochainComplex R L H M).homology n

/-- The canonical subcomplex inclusion `C^•(L, H; M) ⟶ C^•(L, M)`. -/
noncomputable def relativeCochainComplexIncl :
    relativeCochainComplex R L H M ⟶ cochainComplex R L M where
  f n := ModuleCat.ofHom (relativeCochain R L H M n).subtype
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst hj
    change ModuleCat.ofHom (relativeCochain R L H M i).subtype ≫
        (cochainComplex R L M).d i (i + 1) =
      (relativeCochainComplex R L H M).d i (i + 1) ≫
        ModuleCat.ofHom (relativeCochain R L H M (i + 1)).subtype
    rw [cochainComplex_d_succ, relativeCochainComplex_d_succ]
    apply ModuleCat.hom_ext
    ext ω
    rfl

/-- For the trivial subalgebra `⊥`, the relative cochain complex is canonically isomorphic to the
full Chevalley–Eilenberg complex `C^•(L, M)`. -/
noncomputable def relativeCochainComplexBotIso :
    relativeCochainComplex R L (⊥ : LieSubalgebra R L) M ≅ cochainComplex R L M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (LinearEquiv.ofTop (relativeCochain R L ⊥ M n) (relativeCochain_bot n)).toModuleIso)
    (fun i j hij ↦ by
      have hj : i + 1 = j := hij
      subst hj
      change ModuleCat.ofHom (relativeCochain R L ⊥ M i).subtype ≫
          (cochainComplex R L M).d i (i + 1) =
        (relativeCochainComplex R L ⊥ M).d i (i + 1) ≫
          ModuleCat.ofHom (relativeCochain R L ⊥ M (i + 1)).subtype
      rw [cochainComplex_d_succ, relativeCochainComplex_d_succ]
      apply ModuleCat.hom_ext
      ext ω
      rfl)

/-- **Identification of relative cochains with `H`-invariant alternating maps on `L ⧸ H`.** -/
noncomputable def relativeCochainEquiv (n : ℕ) :
    relativeCochain R L H M n ≃ₗ[R]
      LieModule.maxTrivSubmodule R H ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) where
  toFun ω :=
    ⟨(horizontalCochainEquiv R L H M n).symm ⟨ω.1, (mem_relativeCochain_iff.mp ω.2).1⟩, fun h ↦ by
      refine AlternatingMap.compLinearMap_injective H.toLieSubmodule.toSubmodule.mkQ
        H.toLieSubmodule.toSubmodule.mkQ_surjective ?_
      change ⁅h, (horizontalCochainEquiv R L H M n).symm
          ⟨ω.1, (mem_relativeCochain_iff.mp ω.2).1⟩⁆.compLinearMap
          H.toLieSubmodule.toSubmodule.mkQ =
        (0 : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M).compLinearMap
          H.toLieSubmodule.toSubmodule.mkQ
      rw [AlternatingMap.zero_compLinearMap, ← lie_compLinearMap_mkQ]
      have hEq : ((horizontalCochainEquiv R L H M n).symm
          ⟨ω.1, (mem_relativeCochain_iff.mp ω.2).1⟩).compLinearMap
          H.toLieSubmodule.toSubmodule.mkQ = ω.1 :=
        congrArg Subtype.val ((horizontalCochainEquiv R L H M n).apply_symm_apply
          ⟨ω.1, (mem_relativeCochain_iff.mp ω.2).1⟩)
      rw [hEq]
      exact (mem_relativeCochain_iff.mp ω.2).2 h.1 h.2⟩
  map_add' ω₁ ω₂ := Subtype.ext <|
    map_add (horizontalCochainEquiv R L H M n).symm
      ⟨ω₁.1, (mem_relativeCochain_iff.mp ω₁.2).1⟩ ⟨ω₂.1, (mem_relativeCochain_iff.mp ω₂.2).1⟩
  map_smul' r ω := Subtype.ext <|
    map_smul (horizontalCochainEquiv R L H M n).symm r
      ⟨ω.1, (mem_relativeCochain_iff.mp ω.2).1⟩
  invFun η :=
    ⟨η.1.compLinearMap H.toLieSubmodule.toSubmodule.mkQ,
      (horizontalPullback R L H M n η.1).2, fun x hx ↦ by
        have h := lie_compLinearMap_mkQ (⟨x, hx⟩ : H) η.1
        rw [η.2 ⟨x, hx⟩, AlternatingMap.zero_compLinearMap] at h
        exact h⟩
  left_inv ω := Subtype.ext <| AlternatingMap.ext fun v ↦
    horizontalCochainEquiv_symm_apply_mk R L H M n ⟨ω.1, (mem_relativeCochain_iff.mp ω.2).1⟩ v
  right_inv η := Subtype.ext <| AlternatingMap.ext fun v ↦ by
    choose w hw using fun i ↦ H.toLieSubmodule.toSubmodule.mkQ_surjective (v i)
    have hfun : (fun i ↦ LieSubmodule.Quotient.mk (w i)) = v := funext hw
    rw [← hfun]
    exact horizontalCochainEquiv_symm_apply_mk R L H M n (horizontalPullback R L H M n η.1) w

@[simp]
theorem relativeCochainEquiv_apply_mk (n : ℕ) (ω : relativeCochain R L H M n) (v : Fin n → L) :
    (relativeCochainEquiv R L H M n ω).1 (fun i ↦ LieSubmodule.Quotient.mk (v i)) = ω.1 v :=
  horizontalCochainEquiv_symm_apply_mk R L H M n ⟨ω.1, (mem_relativeCochain_iff.mp ω.2).1⟩ v

@[simp]
theorem relativeCochainEquiv_symm_apply_val (n : ℕ)
    (η : LieModule.maxTrivSubmodule R H ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)) :
    ((relativeCochainEquiv R L H M n).symm η : L [⋀^Fin n]→ₗ[R] M) =
      η.1.compLinearMap H.toLieSubmodule.toSubmodule.mkQ := (rfl)

/-! ### Explicit presentation of relative cohomology -/

/-- The flat submodule of `H`-relative `n`-cocycles: cochains in `relativeCochain` whose
differential vanishes. -/
def relativeCocycle (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  relativeCochain R L H M n ⊓ LinearMap.ker (d R L M n)

variable {R L H M} in
@[simp]
theorem mem_relativeCocycle_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ relativeCocycle R L H M n ↔ ω ∈ relativeCochain R L H M n ∧ d R L M n ω = 0 :=
  Iff.rfl

/-- The `n`-th relative differential with codomain restricted to `(n + 1)`-cocycles. -/
def relativeDToCycles (n : ℕ) :
    relativeCochain R L H M n →ₗ[R] relativeCocycle R L H M (n + 1) :=
  ((d R L M n).comp (relativeCochain R L H M n).subtype).codRestrict
    (relativeCocycle R L H M (n + 1)) fun ω ↦ ⟨d_mem_relativeCochain ω.2, d_d n ω.1⟩

@[simp]
theorem relativeDToCycles_coe (n : ℕ) (ω : relativeCochain R L H M n) :
    (relativeDToCycles R L H M n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω.1 := (rfl)

/-- In degree `n + 1`, relative cohomology is isomorphic to the quotient of
`relativeCocycle R L H M (n + 1)` by the range of `relativeDToCycles R L H M n`. -/
noncomputable def relativeCohomologySuccIso (n : ℕ) :
    relativeCohomology R L H M (n + 1) ≅
      ModuleCat.of R (relativeCocycle R L H M (n + 1) ⧸
        LinearMap.range (relativeDToCycles R L H M n)) :=
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (ModuleCat.ofHom (relativeD R L H M n))
      (ModuleCat.ofHom (relativeD R L H M (n + 1))) (by
        rw [← ModuleCat.ofHom_comp, relativeD_comp_relativeD, ModuleCat.ofHom_zero])
  let eKer : LinearMap.ker S.g.hom ≃ₗ[R] relativeCocycle R L H M (n + 1) :=
    { toFun ω := ⟨ω.1.1, ω.1.2, congrArg Subtype.val (LinearMap.mem_ker.mp ω.2)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      invFun ω := ⟨⟨ω.1, ω.2.1⟩, Subtype.ext ω.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let hMap :
      (LinearMap.range S.moduleCatToCycles).map eKer.toLinearMap =
        LinearMap.range (relativeDToCycles R L H M n) := by
    ext ⟨ω, hω⟩
    constructor
    · rintro ⟨_, ⟨η, rfl⟩, h⟩
      exact ⟨η, Subtype.ext (congrArg Subtype.val h)⟩
    · rintro ⟨η, h⟩
      exact ⟨S.moduleCatToCycles η, ⟨η, rfl⟩, Subtype.ext (congrArg Subtype.val h)⟩
  let eSC : (relativeCochainComplex R L H M).sc' n (n + 1) (n + 2) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (relativeCochainComplex_d_succ R L H M n).symm
      (relativeCochainComplex_d_succ R L H M (n + 1)).symm
  ((relativeCochainComplex R L H M).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).trans <|
    (ShortComplex.homologyMapIso eSC).trans <|
      S.moduleCatHomologyIso.trans
        (Submodule.Quotient.equiv _ _ eKer hMap).toModuleIso

/-- In degree `n + 1`, relative cohomology is linearly equivalent to `relativeCocycle / range`. -/
noncomputable def relativeCohomologySuccEquiv (n : ℕ) :
    relativeCohomology R L H M (n + 1) ≃ₗ[R]
      relativeCocycle R L H M (n + 1) ⧸ LinearMap.range (relativeDToCycles R L H M n) :=
  (relativeCohomologySuccIso R L H M n).toLinearEquiv

/-- In degree `0`, relative cohomology is isomorphic to the kernel of `relativeD 0`. -/
noncomputable def relativeCohomologyZeroIsoKer :
    relativeCohomology R L H M 0 ≅ ModuleCat.of R (LinearMap.ker (relativeD R L H M 0)) :=
  (((relativeCochainComplex R L H M).homologyIsoSc' 0 0 1 (by simp) (by simp)).trans
    (ShortComplex.asIsoHomologyπ (S := (relativeCochainComplex R L H M).sc' 0 0 1)
      ((relativeCochainComplex R L H M).shape 0 0 (by simp))).symm).trans
    (((relativeCochainComplex R L H M).sc' 0 0 1).moduleCatCyclesIso.trans
      (LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ (by
        change LinearMap.ker ((relativeCochainComplex R L H M).d 0 1).hom =
          LinearMap.ker (relativeD R L H M 0)
        rw [relativeCochainComplex_d_succ]
        rfl))))

/-- In degree `0`, relative cohomology is linearly equivalent to the `L`-invariants `M^L`. -/
noncomputable def relativeCohomologyZeroEquiv :
    relativeCohomology R L H M 0 ≃ₗ[R] LieModule.maxTrivSubmodule R L M :=
  (relativeCohomologyZeroIsoKer R L H M).toLinearEquiv ≪≫ₗ
    { toFun := fun ω ↦ ⟨ω.1.1 ![], fun x ↦ by
        have h : d R L M 0 ω.1.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ω.2)
        have hx := congrArg (fun f : L [⋀^Fin 1]→ₗ[R] M ↦ f ![x]) h
        rw [d_zero_apply] at hx
        exact hx⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun m ↦
        ⟨⟨AlternatingMap.constLinearEquivOfIsEmpty (R' := R) (M'' := L) (N'' := M) (ι := Fin 0)
            m.1, (mem_relativeCochain_zero_iff).mpr fun x _ ↦ m.2 x⟩, by
          rw [LinearMap.mem_ker]
          apply Subtype.ext
          ext v
          rw [relativeD_coe, d_zero_apply]
          exact m.2 (v 0)⟩
      left_inv := fun ω ↦ by
        apply Subtype.ext
        apply Subtype.ext
        ext v
        simp [Subsingleton.elim v ![]]
      right_inv := fun _ ↦ rfl }

/-- In degree `0`, relative cohomology with trivial coefficients `M` is linearly equivalent to
`M`. -/
noncomputable def relativeCohomologyZeroEquivOfIsTrivial [LieModule.IsTrivial L M] :
    relativeCohomology R L H M 0 ≃ₗ[R] M :=
  relativeCohomologyZeroEquiv R L H M ≪≫ₗ
    LinearEquiv.ofTop (LieModule.maxTrivSubmodule R L M).toSubmodule
      (congrArg LieSubmodule.toSubmodule
        ((LieModule.isTrivial_iff_max_triv_eq_top R L M).mp inferInstance))

variable {R L H M}

/-- Relative cohomology vanishes in any degree where the relative cochain module is subsingleton.
-/
theorem subsingleton_relativeCohomology_of_subsingleton {n : ℕ}
    [h : Subsingleton (relativeCochain R L H M n)] :
    Subsingleton (relativeCohomology R L H M n) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact ShortComplex.isZero_homology_of_isZero_X₂ (S := (relativeCochainComplex R L H M).sc n)
    (ModuleCat.isZero_iff_subsingleton.mpr h)

/-- Relative cochains vanish in degrees strictly above the rank of a finite free quotient
`L ⧸ H.toLieSubmodule`. -/
theorem subsingleton_relativeCochain_of_finrank_lt
    [Module.Free R (L ⧸ H.toLieSubmodule)] [Module.Finite R (L ⧸ H.toLieSubmodule)]
    {n : ℕ} (h : Module.finrank R (L ⧸ H.toLieSubmodule) < n) :
    Subsingleton (relativeCochain R L H M n) := by
  have : Subsingleton ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) := by
    refine ⟨fun f g ↦ exteriorPower.alternatingMapLinearEquiv.injective (LinearMap.ext fun x ↦ ?_)⟩
    simp [exteriorPower.eq_zero_of_finrank_lt n h x]
  refine ⟨fun ω₁ ω₂ ↦ (relativeCochainEquiv R L H M n).injective ?_⟩
  exact Subtype.ext (Subsingleton.elim _ _)

/-- Relative cohomology vanishes in degrees strictly above the rank of a finite free quotient
`L ⧸ H.toLieSubmodule`. -/
theorem subsingleton_relativeCohomology_of_finrank_lt
    [Module.Free R (L ⧸ H.toLieSubmodule)] [Module.Finite R (L ⧸ H.toLieSubmodule)]
    {n : ℕ} (h : Module.finrank R (L ⧸ H.toLieSubmodule) < n) :
    Subsingleton (relativeCohomology R L H M n) := by
  have : Subsingleton (relativeCochain R L H M n) :=
    subsingleton_relativeCochain_of_finrank_lt h
  exact subsingleton_relativeCohomology_of_subsingleton

end Relative

end TauCeti.LieModule.Cohomology
