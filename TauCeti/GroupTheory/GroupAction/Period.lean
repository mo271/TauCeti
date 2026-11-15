/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Period
public import TauCeti.Algebra.GroupAction.CosetRepresentation
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Orbit invariance, coset formulas, and tower sums for `MulAction.period`

For a monoid or group acting on a type `α`, `MulAction.period g a` is the minimal positive exponent
`k` with `g ^ k • a = a` (or `0` when no positive power fixes `a`). This file supplies its `sInf`
characterization, invariance along cyclic orbits and equivariant maps, compatibility with
`Equiv.permutationRepresentation`, and explicit formulas on coset spaces `G ⧸ H` and subgroup
towers `H₁ ≤ H₂`:

* **Infimum, equivariance, and orbit invariance (`MulAction.period_eq_sInf`,
  `MulAction.period_eq_of_injective_of_map_smul`, `MulAction.period_zpow_smul`,
  `MulAction.natCard_orbit_zpowers`).** The period is `sInf {k : ℕ | 0 < k ∧ m ^ k • a = a}`, is
  preserved by injective equivariant maps and along `(Subgroup.zpowers g)`-orbits, and equals
  `Nat.card (MulAction.orbit (Subgroup.zpowers g) a)`.
* **Permutation representations (`Equiv.period_permutationRepresentation`,
  `Equiv.sameCycleQuotientPermutationRepresentationEquiv`,
  `Equiv.orbitCount_permutationRepresentation`).** Reading an action through `e : α ≃ β` preserves
  pointwise periods and identifies cycles of `e.permutationRepresentation g` with
  `(Subgroup.zpowers g)`-orbits on `α`.
* **Cosets and subgroup towers (`Subgroup.period_mk_dvd_iff`, `Subgroup.period_mk_eq_sInf`,
  `Subgroup.period_mk_eq_relIndex`, `Subgroup.quotientOrbitRelQuotientMapOfLE`,
  `Subgroup.sum_natCard_orbit_fiber_quotientOrbitRelQuotientMapOfLE`).** On `G ⧸ H`, `g ^ n` fixes
  `x H` iff `x⁻¹ * g ^ n * x ∈ H`; for `H₁ ≤ H₂` and any `K ≤ G`, the `K`-orbit sizes in a fiber of
  `G ⧸ H₁ → G ⧸ H₂` sum to `[H₂ : H₁]` times the base `K`-orbit size.
-/

open scoped Pointwise

public section

namespace MulAction

variable {M G α β : Type*}

section Monoid

variable [Monoid M] [MulAction M α] [MulAction M β]

/-- The period of `m` on `a` is the infimum of positive exponents fixing `a` (with `sInf ∅ = 0`
when no positive power fixes `a`). -/
@[to_additive /-- The period of `m` on `a` is the infimum of positive multiples fixing `a` (with
`sInf ∅ = 0` when no positive multiple fixes `a`). -/]
theorem period_eq_sInf (m : M) (a : α) :
    period m a = sInf {k : ℕ | 0 < k ∧ m ^ k • a = a} := by
  by_cases h : ∃ k : ℕ, 0 < k ∧ m ^ k • a = a
  · refine le_antisymm (le_csInf h fun k ⟨hk0, hka⟩ ↦ period_le_of_fixed hk0 hka) ?_
    obtain ⟨k, hk0, hka⟩ := h
    exact csInf_le ⟨0, fun _ _ ↦ Nat.zero_le _⟩
      ⟨period_pos_of_fixed hk0 hka, pow_period_smul m a⟩
  · have hempty : {k : ℕ | 0 < k ∧ m ^ k • a = a} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun k hk ↦ h ⟨k, hk⟩
    have hp0 : period m a = 0 :=
      Nat.eq_zero_of_not_pos fun hp ↦ h ⟨period m a, hp, pow_period_smul m a⟩
    rw [hp0, hempty, Nat.sInf_empty]

/-- A map intertwining the action of `m` sends a point to one whose period divides the original
period. -/
@[to_additive /-- A map intertwining the action of `m` sends a point to one whose period divides
the original period. -/]
theorem period_dvd_of_map_smul {m : M} {f : α → β} (hf : ∀ x, f (m • x) = m • f x) (a : α) :
    period m (f a) ∣ period m a := by
  have hpow (k : ℕ) : f (m ^ k • a) = m ^ k • f a := by
    induction k with
    | zero => simp [one_smul]
    | succ k ih => rw [pow_succ', mul_smul, hf, ih, ← mul_smul, ← pow_succ']
  rw [← pow_smul_eq_iff_period_dvd, ← hpow, pow_period_smul]

/-- An injective map intertwining the action of `m` preserves `MulAction.period`. -/
@[to_additive /-- An injective map intertwining the action of `m` preserves `AddAction.period`. -/]
theorem period_eq_of_injective_of_map_smul {m : M} {f : α → β} (hinj : Function.Injective f)
    (hf : ∀ x, f (m • x) = m • f x) (a : α) :
    period m (f a) = period m a := by
  have hpow (k : ℕ) : f (m ^ k • a) = m ^ k • f a := by
    induction k with
    | zero => simp [one_smul]
    | succ k ih => rw [pow_succ', mul_smul, hf, ih, ← mul_smul, ← pow_succ']
  refine Nat.dvd_antisymm (period_dvd_of_map_smul hf a) ?_
  rw [← pow_smul_eq_iff_period_dvd]
  exact hinj (by rw [hpow, pow_period_smul])

end Monoid

section Group

variable [Group G] [MulAction G α]

/-- `MulAction.period g` is invariant along integer-power translates by `g`. -/
@[to_additive (attr := simp) /-- `AddAction.period g` is invariant along integer-multiple
translates by `g`. -/]
theorem period_zpow_smul (g : G) (k : ℤ) (a : α) : period g (g ^ k • a) = period g a := by
  have key (b : α) (j : ℤ) : period g (g ^ j • b) ∣ period g b := by
    rw [← pow_smul_eq_iff_period_dvd, ← mul_smul, ← zpow_natCast, ← zpow_add, add_comm,
      zpow_add, zpow_natCast, mul_smul, pow_period_smul]
  refine Nat.dvd_antisymm (key a k) ?_
  simpa [← mul_smul, ← zpow_add] using key (g ^ k • a) (-k)

/-- `MulAction.period g` is invariant under a single step of `g`. -/
@[to_additive (attr := simp) /-- `AddAction.period g` is invariant under a single step of `g`. -/]
theorem period_smul_self (g : G) (a : α) : period g (g • a) = period g a := by
  simpa using period_zpow_smul g 1 a

/-- `MulAction.period g` is invariant under natural-power translates by `g`. -/
@[to_additive (attr := simp) /-- `AddAction.period g` is invariant under natural-multiple
translates by `g`. -/]
theorem period_pow_smul (g : G) (k : ℕ) (a : α) : period g (g ^ k • a) = period g a := by
  simpa using period_zpow_smul g (k : ℤ) a

/-- Points in the same `(Subgroup.zpowers g)`-orbit have the same `MulAction.period g`. -/
@[to_additive /-- Points in the same `(AddSubgroup.zmultiples g)`-orbit have the same
`AddAction.period g`. -/]
theorem period_eq_of_orbitRel {g : G} {a b : α} (h : orbitRel (Subgroup.zpowers g) α a b) :
    period g a = period g b := by
  obtain ⟨⟨_, k, rfl⟩, rfl⟩ := h
  exact period_zpow_smul g k b

/-- The `Nat.card` of the `(Subgroup.zpowers g)`-orbit of `a` equals `MulAction.period g a` (with
both sides equal to `0` when the orbit is infinite). -/
-- Not `@[simp]`: `simpNF` rewrites `Nat.card` of a coerced set to `Set.ncard`.
@[to_additive /-- The `Nat.card` of the `(AddSubgroup.zmultiples g)`-orbit of `a`
equals `AddAction.period g a` (with both sides equal to `0` when the orbit is infinite). -/]
theorem natCard_orbit_zpowers (g : G) (a : α) :
    Nat.card (orbit (Subgroup.zpowers g) a) = period g a := by
  rw [Nat.card_congr (orbitZPowersEquiv g a), Nat.card_zmod, period_eq_minimalPeriod]

end Group

end MulAction

namespace Equiv

variable {G α β : Type*} [Group G] [MulAction G α]

/-- Reading an action through an equivalence `e : α ≃ β` preserves pointwise periods. -/
@[simp]
theorem period_permutationRepresentation (e : α ≃ β) (g : G) (a : α) :
    MulAction.period (e.permutationRepresentation g) (e a) = MulAction.period g a := by
  have hpow (k : ℕ) : (e.permutationRepresentation g ^ k) (e a) = e (g ^ k • a) := by
    rw [← map_pow, permutationRepresentation_apply, symm_apply_apply]
  refine Nat.dvd_right_iff_eq.mp fun k ↦ ?_
  rw [← MulAction.pow_smul_eq_iff_period_dvd, ← MulAction.pow_smul_eq_iff_period_dvd,
    Perm.smul_def, hpow, e.injective.eq_iff]

/-- Two points `e a` and `e b` lie in the same cycle of `e.permutationRepresentation g` if and only
if `a` and `b` lie in the same `(Subgroup.zpowers g)`-orbit. -/
theorem sameCycle_permutationRepresentation_iff (e : α ≃ β) (g : G) {a b : α} :
    (e.permutationRepresentation g).SameCycle (e a) (e b) ↔
      MulAction.orbitRel (Subgroup.zpowers g) α a b := by
  rw [Perm.SameCycle, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨⟨g ^ (-i), Subgroup.zpow_mem_zpowers g (-i)⟩, ?_⟩,
    fun ⟨⟨_, i, rfl⟩, hi⟩ ↦ ⟨-i, ?_⟩⟩
  · rw [← map_zpow, permutationRepresentation_apply, symm_apply_apply, e.injective.eq_iff] at hi
    rw [Subgroup.smul_def, ← hi, ← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul]
  · rw [← map_zpow, permutationRepresentation_apply, symm_apply_apply, e.injective.eq_iff]
    rw [Subgroup.smul_def] at hi
    rw [← hi, ← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul]

/-- `e.symm` identifies the cycle quotient of `e.permutationRepresentation g` on `β` with the
`(Subgroup.zpowers g)`-orbit quotient on `α`. -/
def sameCycleQuotientPermutationRepresentationEquiv (e : α ≃ β) (g : G) :
    Quotient (Perm.SameCycle.setoid (e.permutationRepresentation g)) ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers g) α :=
  Quotient.congr (ra := Perm.SameCycle.setoid (e.permutationRepresentation g))
    (rb := MulAction.orbitRel (Subgroup.zpowers g) α) e.symm fun i j ↦ by
      have h := e.sameCycle_permutationRepresentation_iff g (a := e.symm i) (b := e.symm j)
      rwa [apply_symm_apply, apply_symm_apply] at h

/-- `sameCycleQuotientPermutationRepresentationEquiv` sends the cycle of `i` to the orbit of
`e.symm i`. -/
@[simp]
theorem sameCycleQuotientPermutationRepresentationEquiv_mk (e : α ≃ β) (g : G) (i : β) :
    e.sameCycleQuotientPermutationRepresentationEquiv g
        (Quotient.mk (Perm.SameCycle.setoid (e.permutationRepresentation g)) i) =
      Quotient.mk'' (e.symm i) := (rfl)

/-- The inverse of `sameCycleQuotientPermutationRepresentationEquiv` sends the orbit of `a` to the
cycle of `e a`. -/
@[simp]
theorem sameCycleQuotientPermutationRepresentationEquiv_symm_mk (e : α ≃ β) (g : G) (a : α) :
    (e.sameCycleQuotientPermutationRepresentationEquiv g).symm (Quotient.mk'' a) =
      Quotient.mk (Perm.SameCycle.setoid (e.permutationRepresentation g)) (e a) :=
  (e.sameCycleQuotientPermutationRepresentationEquiv g).injective <| by simp

/-- The number of orbits of `e.permutationRepresentation g` on `β` equals the `Nat.card` of the
`(Subgroup.zpowers g)`-orbit quotient on `α`. -/
@[simp]
theorem orbitCount_permutationRepresentation (e : α ≃ β) (g : G) :
    TauCeti.orbitCount (e.permutationRepresentation g) =
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) α) := by
  rw [TauCeti.orbitCount_def]
  exact Nat.card_congr (e.sameCycleQuotientPermutationRepresentationEquiv g)

end Equiv

namespace Subgroup

variable {G : Type*} [Group G]

/-! ### Periods on left coset spaces -/

/-- The period of `g` on the left coset `x H` divides `n` if and only if `x⁻¹ * g ^ n * x ∈ H`. -/
theorem period_mk_dvd_iff (H : Subgroup G) (g x : G) (n : ℕ) :
    MulAction.period g (x : G ⧸ H) ∣ n ↔ x⁻¹ * g ^ n * x ∈ H := by
  have hconj : (g ^ n * x)⁻¹ * x = (x⁻¹ * g ^ n * x)⁻¹ := by group
  rw [← MulAction.pow_smul_eq_iff_period_dvd, MulAction.Quotient.smul_mk, smul_eq_mul,
    QuotientGroup.eq, hconj, H.inv_mem_iff]

/-- The period of `g` on the left coset `x H` is the least positive `n` with `x⁻¹ * g ^ n * x ∈ H`
(or `0` if none exists). -/
theorem period_mk_eq_sInf (H : Subgroup G) (g x : G) :
    MulAction.period g (x : G ⧸ H) = sInf {n : ℕ | 0 < n ∧ x⁻¹ * g ^ n * x ∈ H} := by
  rw [MulAction.period_eq_sInf]
  congr 1
  ext n
  exact and_congr_right' (MulAction.pow_smul_eq_iff_period_dvd.trans (H.period_mk_dvd_iff g x n))

/-- On the identity coset `1 : G ⧸ H`, the period of `g` divides `n` if and only if `g ^ n ∈ H`. -/
@[simp]
theorem period_mk_one_dvd_iff (H : Subgroup G) (g : G) (n : ℕ) :
    MulAction.period g ((1 : G) : G ⧸ H) ∣ n ↔ g ^ n ∈ H := by
  simpa using H.period_mk_dvd_iff g 1 n

/-- On the identity coset `1 : G ⧸ H`, the period of `g` is the least positive `n` with
`g ^ n ∈ H` (or `0` if none exists). -/
theorem period_mk_one_eq_sInf (H : Subgroup G) (g : G) :
    MulAction.period g ((1 : G) : G ⧸ H) = sInf {n : ℕ | 0 < n ∧ g ^ n ∈ H} := by
  simpa using H.period_mk_eq_sInf g 1

/-- The period of `g` on `x H` equals the relative index `[⟨g⟩ : ⟨g⟩ ⊓ x H x⁻¹]`. -/
theorem period_mk_eq_relIndex (H : Subgroup G) (g x : G) :
    MulAction.period g (x : G ⧸ H) = (ConjAct.toConjAct x • H).relIndex (Subgroup.zpowers g) := by
  have hstab : MulAction.stabilizer (Subgroup.zpowers g) (x : G ⧸ H) =
      (ConjAct.toConjAct x • H).subgroupOf (Subgroup.zpowers g) := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv]
    have hconj : ((k : G) * x)⁻¹ * x = (x⁻¹ * (k : G) * x)⁻¹ := by group
    rw [hconj, H.inv_mem_iff]
  rw [← MulAction.natCard_orbit_zpowers,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ _), hstab]
  rfl

/-! ### Orbit projections and fiber-sum identity along subgroup inclusions -/

/-- Enlarging the subgroup from `H₁` to `H₂` makes the coset period of `g` divide the smaller
subgroup's coset period. -/
theorem period_quotientMapOfLE_dvd {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (g : G) (q : G ⧸ H₁) :
    MulAction.period g (quotientMapOfLE h q) ∣ MulAction.period g q :=
  MulAction.period_dvd_of_map_smul
    (fun r ↦ QuotientGroup.induction_on r fun _ ↦ rfl) q

/-- For `H₁ ≤ H₂` and any subgroup `K ≤ G`, `Subgroup.quotientMapOfLE h` descends to a map on
`K`-orbit quotients `MulAction.orbitRel.Quotient K (G ⧸ H₁)` to
`MulAction.orbitRel.Quotient K (G ⧸ H₂)`. -/
def quotientOrbitRelQuotientMapOfLE {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (K : Subgroup G) :
    MulAction.orbitRel.Quotient K (G ⧸ H₁) → MulAction.orbitRel.Quotient K (G ⧸ H₂) :=
  Quotient.map' (quotientMapOfLE h) fun a b ⟨k, hk⟩ ↦
    ⟨k, by
      rw [← hk]
      exact QuotientGroup.induction_on b fun _ ↦ rfl⟩

/-- `quotientOrbitRelQuotientMapOfLE` sends the `K`-orbit of `q` to that of
`quotientMapOfLE h q`. -/
@[simp]
theorem quotientOrbitRelQuotientMapOfLE_mk {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (K : Subgroup G)
    (q : G ⧸ H₁) :
    quotientOrbitRelQuotientMapOfLE h K (Quotient.mk'' q) =
      Quotient.mk'' (quotientMapOfLE h q) := (rfl)

/-- Every `K`-orbit quotient projection along `H₁ ≤ H₂` is surjective. -/
theorem quotientOrbitRelQuotientMapOfLE_surjective {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂)
    (K : Subgroup G) :
    Function.Surjective (quotientOrbitRelQuotientMapOfLE h K) :=
  Quotient.ind' fun q ↦ QuotientGroup.induction_on q fun x ↦ ⟨Quotient.mk'' (x : G ⧸ H₁), rfl⟩

/-- Equivalence between the disjoint union of the `K`-orbits in the fiber of
`quotientOrbitRelQuotientMapOfLE h K` over `ω` and `ω.orbit × (H₂ ⧸ H₁.subgroupOf H₂)`. -/
private noncomputable def sigmaOrbitFiberEquivProd {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂)
    (K : Subgroup G) (ω : MulAction.orbitRel.Quotient K (G ⧸ H₂)) :
    (Σ c : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
        quotientOrbitRelQuotientMapOfLE h K c = ω}, c.1.orbit) ≃
      ω.orbit × (H₂ ⧸ H₁.subgroupOf H₂) := by
  have hmem (q : G ⧸ H₁) :
      quotientOrbitRelQuotientMapOfLE h K (Quotient.mk'' q) = ω ↔
        quotientMapOfLE h q ∈ ω.orbit := by
    rw [quotientOrbitRelQuotientMapOfLE_mk, MulAction.orbitRel.Quotient.mem_orbit]
  let e₁ : (Σ c : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
        quotientOrbitRelQuotientMapOfLE h K c = ω}, c.1.orbit) ≃
      {q : G ⧸ H₁ // quotientMapOfLE h q ∈ ω.orbit} :=
    { toFun := fun ⟨c, x⟩ ↦
        ⟨x.1, (hmem x.1).mp <| by
          rw [MulAction.orbitRel.Quotient.mem_orbit.mp x.2, c.2]⟩
      invFun := fun q ↦
        ⟨⟨Quotient.mk'' q.1, (hmem q.1).mpr q.2⟩,
          ⟨q.1, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩⟩
      left_inv := fun ⟨⟨c, hc⟩, ⟨x, hx⟩⟩ ↦ by
        have hcx : Quotient.mk'' x = c := MulAction.orbitRel.Quotient.mem_orbit.mp hx
        subst hcx
        rfl
      right_inv := fun _ ↦ rfl }
  let e₂ : {q : G ⧸ H₁ // quotientMapOfLE h q ∈ ω.orbit} ≃
      {p : (G ⧸ H₂) × (H₂ ⧸ H₁.subgroupOf H₂) // p.1 ∈ ω.orbit} :=
    (quotientEquivProdOfLE h).subtypeEquiv fun _ ↦ Iff.rfl
  exact e₁.trans <| e₂.trans <|
    Equiv.prodSubtypeFstEquivSubtypeProd (p := fun a : G ⧸ H₂ ↦ a ∈ ω.orbit)

/-- When `H₁` has finite relative index in `H₂` and `ω.orbit` is finite, the fiber of
`quotientOrbitRelQuotientMapOfLE h K` over `ω` is finite. -/
theorem finite_fiber_quotientOrbitRelQuotientMapOfLE {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂)
    [H₁.IsFiniteRelIndex H₂] (K : Subgroup G) (ω : MulAction.orbitRel.Quotient K (G ⧸ H₂))
    [Finite ω.orbit] :
    Finite {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
      quotientOrbitRelQuotientMapOfLE h K c = ω} := by
  have : Finite (H₂ ⧸ H₁.subgroupOf H₂) := inferInstance
  have : Finite (Σ c : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
      quotientOrbitRelQuotientMapOfLE h K c = ω}, c.1.orbit) :=
    Finite.of_equiv _ (sigmaOrbitFiberEquivProd h K ω).symm
  exact Finite.of_surjective
    (fun p : (Σ c : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
        quotientOrbitRelQuotientMapOfLE h K c = ω}, c.1.orbit) ↦ p.1)
    fun c ↦ ⟨⟨c, ⟨c.1.out, MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' c.1)⟩⟩,
      rfl⟩

/-- **Tower orbit-sum identity.** For `H₁ ≤ H₂` with finite relative index and any finite
`K`-orbit `ω` on `G ⧸ H₂`, the sizes of the `K`-orbits on `G ⧸ H₁` lying over `ω` sum to
`Nat.card ω.orbit * [H₂ : H₁]`. -/
theorem sum_natCard_orbit_fiber_quotientOrbitRelQuotientMapOfLE {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂)
    [H₁.IsFiniteRelIndex H₂] (K : Subgroup G) (ω : MulAction.orbitRel.Quotient K (G ⧸ H₂))
    [Finite ω.orbit]
    [Fintype {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
      quotientOrbitRelQuotientMapOfLE h K c = ω}] :
    (∑ c : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
        quotientOrbitRelQuotientMapOfLE h K c = ω}, Nat.card c.1.orbit) =
      Nat.card ω.orbit * H₁.relIndex H₂ := by
  have : Finite (H₂ ⧸ H₁.subgroupOf H₂) := inferInstance
  have : Finite (Σ c : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
      quotientOrbitRelQuotientMapOfLE h K c = ω}, c.1.orbit) :=
    Finite.of_equiv _ (sigmaOrbitFiberEquivProd h K ω).symm
  have (a : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
      quotientOrbitRelQuotientMapOfLE h K c = ω}) : Finite a.1.orbit :=
    Finite.of_injective
      (Sigma.mk (β := fun c : {c : MulAction.orbitRel.Quotient K (G ⧸ H₁) //
        quotientOrbitRelQuotientMapOfLE h K c = ω} ↦ c.1.orbit) a) sigma_mk_injective
  rw [← Nat.card_sigma, Nat.card_congr (sigmaOrbitFiberEquivProd h K ω), Nat.card_prod]
  rfl

end Subgroup
