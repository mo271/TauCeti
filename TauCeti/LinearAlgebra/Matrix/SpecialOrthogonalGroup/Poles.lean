/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.NatCard
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Axis
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.CoordinateRotation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Poles, Burnside's orbit equation, and Klein's Diophantine classification in `SO(3)`

Let `K ≤ SO(3)` be a finite subgroup of the three-dimensional real rotation group acting on the
unit sphere `S² ⊆ ℝ³`. A **pole** of `K` is a point `p ∈ S²` fixed by some nonidentity element of
`K` (equivalently, `MulAction.stabilizer K p ≠ ⊥`). Because every nonidentity rotation in `SO(3)`
fixes exactly two antipodal points on `S²` (`natCard_fixedBy_unitSphere_of_ne_one`), the set of
poles `poles K` is a finite `K`-invariant subset of `S²`, empty if and only if `K = ⊥`.

Applying Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) to the
action of `K` on `poles K` yields the classical pole-orbit counting equation: if `K` has `r`
orbits on `poles K` with stabilizer orders `m_ω = poleOrbitOrder K ω ≥ 2`, then
`|poles K| + 2 (|K| - 1) = r |K|`, or in rational reciprocal form
`∑ ω, (1 - (m_ω : ℚ)⁻¹) = 2 - 2 / |K|`.

## Main declarations

* `TauCeti.Matrix.SpecialOrthogonalGroup.poles` and
  `TauCeti.Matrix.SpecialOrthogonalGroup.poleOrbitOrder`: the finite `K`-sub-action of poles on
  `S²` and the stabilizer-order invariant on `MulAction.orbitRel.Quotient K (poles K)`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.natCard_poles_add_two_mul_natCard_sub_one`,
  `TauCeti.Matrix.SpecialOrthogonalGroup.sum_one_sub_inv_poleOrbitOrder`, and
  `TauCeti.Matrix.SpecialOrthogonalGroup.finsum_one_sub_inv_poleOrbitOrder`: Burnside's pole-orbit
  equation in `ℕ`, `Finset.univ`, and `finsum` forms.
* `TauCeti.Matrix.SpecialOrthogonalGroup.natCard_orbitRelQuotient_poles_eq_two_or_three`: every
  nontrivial finite subgroup of `SO(3)` has `2` or `3` pole orbits.
* `TauCeti.Matrix.SpecialOrthogonalGroup.natCard_orbitRelQuotient_poles_eq_two_iff` and
  `natCard_orbitRelQuotient_poles_eq_two_iff_exists_conj_cyclicAxisSubgroup`: characterizations of
  the two-orbit case by a common fixed pole and by conjugacy to
  `cyclicAxisSubgroup (Nat.card K)`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.poleOrbitOrder_classification_of_three_orbits` and
  `TauCeti.Matrix.SpecialOrthogonalGroup.finite_subgroup_orbit_classification`: Klein's
  Diophantine classification into types `(2, 2, n)`, `(2, 3, 3)`, `(2, 3, 4)`, and `(2, 3, 5)`, and
  the full pole-orbit trichotomy.
* `TauCeti.Matrix.SpecialOrthogonalGroup.dihedralAxisSubgroup` and
  `TauCeti.Matrix.SpecialOrthogonalGroup.natCard_orbitRelQuotient_poles_dihedralAxisSubgroup`: the
  concrete dihedral rotation subgroup of order `2 * n`, having `3` pole orbits for `2 ≤ n`.

## References

* F. Klein, *Lectures on the Icosahedron and the Solution of Equations of the Fifth Degree* (1884),
  Part I, Chapter I, §§2–4.
* T. A. Springer, *Invariant Theory*, Lecture Notes in Mathematics 585, Springer, 1977, §4.4.
* J. Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008, §2.2.
-/

public section

open Metric Matrix

namespace TauCeti.Matrix.SpecialOrthogonalGroup

section Poles

/-- **The pole sub-action of a subgroup `K ≤ SO(3)`.** A point `p ∈ S²` is a pole of `K` if it is
fixed by at least one nonidentity rotation in `K`. -/
def poles (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) :
    SubMulAction K (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) where
  carrier := {p | ∃ g ∈ K, g ≠ 1 ∧ g • p = p}
  smul_mem' := by
    rintro k p ⟨g, hgK, hg1, hgp⟩
    refine ⟨(k : specialOrthogonalGroup (Fin 3) ℝ) * g * (k : specialOrthogonalGroup (Fin 3) ℝ)⁻¹,
      K.mul_mem (K.mul_mem k.2 hgK) (K.inv_mem k.2), ?_, ?_⟩
    · intro hconj
      apply hg1
      calc
        g = (k : specialOrthogonalGroup (Fin 3) ℝ)⁻¹ *
            ((k : specialOrthogonalGroup (Fin 3) ℝ) * g *
              (k : specialOrthogonalGroup (Fin 3) ℝ)⁻¹) *
            (k : specialOrthogonalGroup (Fin 3) ℝ) := by simp [mul_assoc]
        _ = 1 := by simp [hconj]
    · have hksmul : k • p = (k : specialOrthogonalGroup (Fin 3) ℝ) • p := rfl
      rw [hksmul, mul_smul, mul_smul, inv_smul_smul, hgp]

@[simp]
theorem mem_poles_iff {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} :
    p ∈ poles K ↔ ∃ g ∈ K, g ≠ 1 ∧ g • p = p :=
  Iff.rfl

/-- A point `p ∈ S²` is a pole of `K` if and only if its stabilizer in `K` is nontrivial. -/
theorem mem_poles_iff_stabilizer_ne_bot {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} :
    p ∈ poles K ↔ MulAction.stabilizer K p ≠ ⊥ := by
  rw [Ne, Subgroup.eq_bot_iff_forall]
  push Not
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hgK, hg1, hgp⟩
    exact ⟨⟨g, hgK⟩, hgp, fun h1 ↦ hg1 (congrArg Subtype.val h1)⟩
  · rintro ⟨k, hkp, hk1⟩
    exact ⟨k.1, k.2, fun h1 ↦ hk1 (Subtype.ext h1), hkp⟩

/-- The pole set of `K` is closed under the antipodal map. -/
@[simp]
theorem neg_mem_poles_iff {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} :
    -p ∈ poles K ↔ p ∈ poles K := by
  have hneg : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, q ∈ poles K → -q ∈ poles K := by
    rintro q ⟨g, hgK, hg1, hgq⟩
    exact ⟨g, hgK, hg1, by rw [specialUnitaryGroup.smul_neg_unitSphere, hgq]⟩
  exact ⟨fun h ↦ by simpa using hneg (-p) h, hneg p⟩

@[simp]
theorem poles_bot : poles (⊥ : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) = ⊥ :=
  eq_bot_iff.mpr fun _ ⟨_, hg, hg1, _⟩ ↦ absurd (Subgroup.mem_bot.mp hg) hg1

@[simp]
theorem poles_eq_bot_iff {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} :
    poles K = ⊥ ↔ K = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ poles_bot⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro g hgK
  by_contra hg1
  obtain ⟨p, hp⟩ := _root_.Matrix.SpecialOrthogonalGroup.exists_smul_eq_self_unitSphere g
  have hmem : p ∈ poles K := ⟨g, hgK, hg1, hp⟩
  rw [h, ← iSup_of_empty (fun _ : Empty ↦ (⊥ : SubMulAction _ _)), SubMulAction.mem_iSup] at hmem
  obtain ⟨⟨⟩, _⟩ := hmem

theorem nonempty_poles_iff {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} :
    Nonempty (poles K) ↔ K ≠ ⊥ := by
  refine ⟨?_, fun hne ↦ ?_⟩
  · rintro ⟨⟨_, g, hgK, hg1, _⟩⟩ rfl
    exact hg1 (Subgroup.mem_bot.mp hgK)
  · have hex : ∃ g ∈ K, g ≠ 1 := by
      by_contra! hall
      exact hne ((Subgroup.eq_bot_iff_forall _).mpr hall)
    obtain ⟨g, hgK, hg1⟩ := hex
    obtain ⟨p, hp⟩ := _root_.Matrix.SpecialOrthogonalGroup.exists_smul_eq_self_unitSphere g
    exact ⟨⟨p, g, hgK, hg1, hp⟩⟩

/-- The underlying set of `poles K` is the union of the `S²` fixed-point sets of the nonidentity
elements of `K`. -/
theorem coe_poles_eq_iUnion_fixedBy (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) :
    (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) =
      ⋃ k : {k : K // k ≠ 1},
        MulAction.fixedBy (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (k.1 : specialOrthogonalGroup (Fin 3) ℝ) := by
  ext p
  simp only [SetLike.mem_coe, mem_poles_iff, Set.mem_iUnion, MulAction.mem_fixedBy]
  exact ⟨fun ⟨g, hgK, hg1, hgp⟩ ↦ ⟨⟨⟨g, hgK⟩, fun h ↦ hg1 (congrArg Subtype.val h)⟩, hgp⟩,
    fun ⟨k, hkp⟩ ↦ ⟨k.1.1, k.1.2, fun h ↦ k.2 (Subtype.ext h), hkp⟩⟩

/-- **A finite subgroup of `SO(3)` has only finitely many poles on `S²`.** -/
instance instFinitePoles (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K] :
    Finite (poles K) := by
  have hfin : (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).Finite := by
    rw [coe_poles_eq_iUnion_fixedBy]
    refine Set.finite_iUnion fun k ↦ ?_
    rw [← Set.finite_coe_iff]
    have hk : (k.1 : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 :=
      fun h ↦ k.2 (Subtype.ext h)
    exact Nat.finite_of_card_ne_zero (by rw [natCard_fixedBy_unitSphere_of_ne_one hk]; decide)
  exact hfin.to_subtype

end Poles

section OrbitOrder

/-- **The stabilizer order of a pole orbit.** Because point stabilizers along an orbit are
conjugate (`MulAction.stabilizerEquivStabilizer`), `p ↦ Nat.card (MulAction.stabilizer K p)`
descends to the quotient `MulAction.orbitRel.Quotient K (poles K)`. -/
noncomputable def poleOrbitOrder (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) :
    MulAction.orbitRel.Quotient K (poles K) → ℕ :=
  TauCeti.MulAction.orbitRelQuotientLift
    (fun p : poles K ↦
      Nat.card (MulAction.stabilizer K (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)))
    fun k p ↦ by
      rw [SubMulAction.val_smul_of_tower]
      exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := k) rfl).toEquiv).symm

@[simp]
theorem poleOrbitOrder_mk (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) (p : poles K) :
    poleOrbitOrder K (Quotient.mk (MulAction.orbitRel K (poles K)) p) =
      Nat.card (MulAction.stabilizer K (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  TauCeti.MulAction.orbitRelQuotientLift_mk p

theorem poleOrbitOrder_out (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))
    (ω : MulAction.orbitRel.Quotient K (poles K)) :
    poleOrbitOrder K ω =
      Nat.card (MulAction.stabilizer K (ω.out : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  conv_lhs => rw [← Quotient.out_eq' ω]
  exact poleOrbitOrder_mk K ω.out

/-- Every pole orbit of a finite subgroup `K ≤ SO(3)` has stabilizer order at least `2`. -/
theorem two_le_poleOrbitOrder {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} [Finite K]
    (ω : MulAction.orbitRel.Quotient K (poles K)) :
    2 ≤ poleOrbitOrder K ω := by
  rw [poleOrbitOrder_out]
  have hne : MulAction.stabilizer K (ω.out : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≠ ⊥ :=
    mem_poles_iff_stabilizer_ne_bot.mp ω.out.2
  have hpos : 0 < Nat.card
      (MulAction.stabilizer K (ω.out : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := Nat.card_pos
  have hne1 : Nat.card
      (MulAction.stabilizer K (ω.out : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ≠ 1 := by
    rwa [Ne, ← Subgroup.eq_bot_iff_card]
  omega

/-- The stabilizer order of a pole orbit divides `Nat.card K`. -/
theorem poleOrbitOrder_dvd_natCard {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    (ω : MulAction.orbitRel.Quotient K (poles K)) :
    poleOrbitOrder K ω ∣ Nat.card K := by
  rw [poleOrbitOrder_out]
  exact Subgroup.card_subgroup_dvd_card _

theorem poleOrbitOrder_le_natCard {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} [Finite K]
    (ω : MulAction.orbitRel.Quotient K (poles K)) :
    poleOrbitOrder K ω ≤ Nat.card K :=
  Nat.le_of_dvd Nat.card_pos (poleOrbitOrder_dvd_natCard ω)

/-- **Orbit-stabilizer formula for pole orbits**: `Nat.card ω.orbit * poleOrbitOrder K ω = |K|`. -/
theorem natCard_orbit_mul_poleOrbitOrder {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    [Finite K] (ω : MulAction.orbitRel.Quotient K (poles K)) :
    Nat.card ω.orbit * poleOrbitOrder K ω = Nat.card K := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (poles K) := Fintype.ofFinite (poles K)
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq', poleOrbitOrder_out,
    ← SubMulAction.stabilizer_of_subMul ω.out]
  let _ : Fintype (MulAction.orbit K ω.out) := Fintype.ofFinite _
  let _ : Fintype (MulAction.stabilizer K ω.out) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group K ω.out

end OrbitOrder

section Burnside

/-- Every nonidentity element of `K` fixes exactly `2` points in `poles K` (its two poles on
`S²`). -/
theorem natCard_fixedBy_poles_of_ne_one (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))
    {k : K} (hk : k ≠ 1) :
    Nat.card (MulAction.fixedBy (poles K) k) = 2 := by
  have hk' : (k : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := fun h ↦ hk (Subtype.ext h)
  let e : MulAction.fixedBy (poles K) k ≃
      MulAction.fixedBy (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (k : specialOrthogonalGroup (Fin 3) ℝ) :=
    { toFun := fun p ↦ ⟨p.1.1, congrArg Subtype.val p.2⟩
      invFun := fun q ↦ ⟨⟨q.1, ⟨k.1, k.2, hk', q.2⟩⟩, Subtype.ext q.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr e]
  exact natCard_fixedBy_unitSphere_of_ne_one hk'

/-- **Burnside's pole-orbit equation (natural-number form).** For any finite subgroup `K ≤ SO(3)`,
`|poles K| + 2 (|K| - 1) = |poles K / K| * |K|`. -/
theorem natCard_poles_add_two_mul_natCard_sub_one
    (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K] :
    Nat.card (poles K) + 2 * (Nat.card K - 1) =
      Nat.card (MulAction.orbitRel.Quotient K (poles K)) * Nat.card K := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (poles K) := Fintype.ofFinite (poles K)
  let _ : ∀ k : K, Fintype (MulAction.fixedBy (poles K) k) := fun _ ↦ Fintype.ofFinite _
  let _ : Fintype (MulAction.orbitRel.Quotient K (poles K)) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group K (poles K)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : K))] at hburn
  have hone : Fintype.card (MulAction.fixedBy (poles K) (1 : K)) = Nat.card (poles K) := by
    have hfix1 : MulAction.fixedBy (poles K) (1 : K) = Set.univ := by ext; simp
    rw [← Nat.card_eq_fintype_card, hfix1]
    exact Nat.card_congr (Equiv.Set.univ (poles K))
  have hrest : ∑ k ∈ Finset.univ.erase (1 : K),
      Fintype.card (MulAction.fixedBy (poles K) k) = 2 * (Nat.card K - 1) := by
    have hconst : ∀ k ∈ Finset.univ.erase (1 : K),
        Fintype.card (MulAction.fixedBy (poles K) k) = 2 := by
      intro k hk
      rw [← Nat.card_eq_fintype_card]
      exact natCard_fixedBy_poles_of_ne_one K (Finset.ne_of_mem_erase hk)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]
  rw [hone, hrest] at hburn
  simpa only [Nat.card_eq_fintype_card] using hburn

/-- Partitioning `poles K` into `K`-orbits expresses `Nat.card (poles K)` as the sum of orbit
sizes. -/
theorem sum_natCard_orbit_poles (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K]
    [Fintype (MulAction.orbitRel.Quotient K (poles K))] :
    ∑ ω : MulAction.orbitRel.Quotient K (poles K), Nat.card ω.orbit = Nat.card (poles K) := by
  classical
  let _ : Fintype (poles K) := Fintype.ofFinite (poles K)
  let _ : ∀ ω : MulAction.orbitRel.Quotient K (poles K), Fintype ω.orbit :=
    fun _ ↦ Fintype.ofFinite _
  have heq := Fintype.card_congr (MulAction.selfEquivSigmaOrbits' K (poles K))
  rw [Fintype.card_sigma] at heq
  simpa only [Nat.card_eq_fintype_card] using heq.symm

/-- **Burnside's pole-orbit equation in rational reciprocal form** (`Finset.univ` sum):
`∑ ω, (1 - (poleOrbitOrder K ω : ℚ)⁻¹) = 2 - 2 / |K|`. -/
theorem sum_one_sub_inv_poleOrbitOrder (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K]
    [Fintype (MulAction.orbitRel.Quotient K (poles K))] :
    ∑ ω : MulAction.orbitRel.Quotient K (poles K), (1 - (poleOrbitOrder K ω : ℚ)⁻¹) =
      2 - 2 / (Nat.card K : ℚ) := by
  have hNpos : 0 < Nat.card K := Nat.card_pos
  have hNne : (Nat.card K : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have hterm : ∀ ω : MulAction.orbitRel.Quotient K (poles K),
      (Nat.card K : ℚ) * (1 - (poleOrbitOrder K ω : ℚ)⁻¹) =
        (Nat.card K : ℚ) - (Nat.card ω.orbit : ℚ) := by
    intro ω
    have hm_ne : (poleOrbitOrder K ω : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by have := two_le_poleOrbitOrder ω; omega)
    have horb : (Nat.card ω.orbit : ℚ) * (poleOrbitOrder K ω : ℚ) = (Nat.card K : ℚ) := by
      exact_mod_cast natCard_orbit_mul_poleOrbitOrder ω
    rw [mul_sub, mul_one, ← horb, mul_assoc, mul_inv_cancel₀ hm_ne, mul_one]
  have hmul : (Nat.card K : ℚ) *
      (∑ ω : MulAction.orbitRel.Quotient K (poles K), (1 - (poleOrbitOrder K ω : ℚ)⁻¹)) =
      2 * ((Nat.card K : ℚ) - 1) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun ω _ ↦ hterm ω, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    have hsumQ : (∑ ω : MulAction.orbitRel.Quotient K (poles K), (Nat.card ω.orbit : ℚ)) =
        (Nat.card (poles K) : ℚ) := by
      exact_mod_cast sum_natCard_orbit_poles K
    have hburnQ : (Nat.card (poles K) : ℚ) + 2 * ((Nat.card K : ℚ) - 1) =
        (Nat.card (MulAction.orbitRel.Quotient K (poles K)) : ℚ) * (Nat.card K : ℚ) := by
      have h1 : 1 ≤ Nat.card K := hNpos
      have hb := natCard_poles_add_two_mul_natCard_sub_one K
      zify [h1] at hb
      exact_mod_cast hb
    rw [hsumQ]
    linear_combination -hburnQ
  apply mul_left_cancel₀ hNne
  rw [hmul]
  field_simp

/-- **Burnside's pole-orbit equation (`finsum` form)**, requiring only `[Finite K]`. -/
theorem finsum_one_sub_inv_poleOrbitOrder (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))
    [Finite K] :
    (∑ᶠ ω : MulAction.orbitRel.Quotient K (poles K), (1 - (poleOrbitOrder K ω : ℚ)⁻¹)) =
      2 - 2 / (Nat.card K : ℚ) := by
  let _ : Fintype (MulAction.orbitRel.Quotient K (poles K)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact sum_one_sub_inv_poleOrbitOrder K

end Burnside

section TwoOrThreeOrbits

/-- **Every nontrivial finite subgroup of `SO(3)` has either `2` or `3` orbits on its poles.** -/
theorem natCard_orbitRelQuotient_poles_eq_two_or_three
    {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} [Finite K] (hK : K ≠ ⊥) :
    Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 2 ∨
      Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 3 := by
  let _ : Fintype (MulAction.orbitRel.Quotient K (poles K)) := Fintype.ofFinite _
  set N := Nat.card K
  set P := Nat.card (poles K)
  set r := Nat.card (MulAction.orbitRel.Quotient K (poles K))
  have hN : 2 ≤ N := by
    have hpos : 0 < N := Nat.card_pos
    have hne1 : N ≠ 1 := by rwa [Ne, ← Subgroup.eq_bot_iff_card]
    omega
  have hr_pos : 1 ≤ r := by
    have : Nonempty (poles K) := nonempty_poles_iff.mpr hK
    have : Nonempty (MulAction.orbitRel.Quotient K (poles K)) :=
      ⟨Quotient.mk _ (Classical.arbitrary (poles K))⟩
    exact Nat.card_pos
  have horb_pos : ∀ ω : MulAction.orbitRel.Quotient K (poles K), 1 ≤ Nat.card ω.orbit := by
    intro ω
    have : Nonempty ω.orbit := ⟨⟨ω.out, by
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
      exact MulAction.mem_orbit_self ω.out⟩⟩
    exact Nat.card_pos
  have hr_le_P : r ≤ P := by
    have h1 : ∑ _ω : MulAction.orbitRel.Quotient K (poles K), 1 ≤
        ∑ ω : MulAction.orbitRel.Quotient K (poles K), Nat.card ω.orbit :=
      Finset.sum_le_sum fun ω _ ↦ horb_pos ω
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, mul_one,
      sum_natCard_orbit_poles K] at h1
    exact h1
  have h2P_le : 2 * P ≤ r * N := by
    have hle : ∀ ω : MulAction.orbitRel.Quotient K (poles K), 2 * Nat.card ω.orbit ≤ N := by
      intro ω
      calc
        2 * Nat.card ω.orbit = Nat.card ω.orbit * 2 := mul_comm _ _
        _ ≤ Nat.card ω.orbit * poleOrbitOrder K ω :=
          Nat.mul_le_mul_left _ (two_le_poleOrbitOrder ω)
        _ = N := natCard_orbit_mul_poleOrbitOrder ω
    have hsum : ∑ ω : MulAction.orbitRel.Quotient K (poles K), 2 * Nat.card ω.orbit ≤
        ∑ _ω : MulAction.orbitRel.Quotient K (poles K), N :=
      Finset.sum_le_sum fun ω _ ↦ hle ω
    rw [← Finset.mul_sum, sum_natCard_orbit_poles K, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, smul_eq_mul] at hsum
    exact hsum
  have hburn : P + 2 * (N - 1) = r * N := natCard_poles_add_two_mul_natCard_sub_one K
  have hr_ge_2 : 2 ≤ r := by
    by_contra hlt
    have hr1 : r = 1 := by omega
    rw [hr1, one_mul] at hburn
    omega
  have hr_le_3 : r ≤ 3 := by
    have hburn' : P + 2 * N = r * N + 2 := by omega
    nlinarith
  omega

end TwoOrThreeOrbits

section TwoOrbits

/-- If a nontrivial subgroup `K ≤ SO(3)` fixes `p ∈ S²`, then its pole set is `{p, -p}`. -/
theorem coe_poles_eq_pair_of_le_stabilizer {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}
    (hK : K ≠ ⊥) {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hle : K ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p) :
    (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) = {p, -p} := by
  have hex : ∃ g ∈ K, g ≠ 1 := by
    by_contra! hall
    exact hK ((Subgroup.eq_bot_iff_forall _).mpr hall)
  obtain ⟨g₀, hg₀K, hg₀1⟩ := hex
  ext q
  simp only [SetLike.mem_coe, mem_poles_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hgK, hg1, hgq⟩
    exact (smul_eq_self_unitSphere_iff_of_ne_one hg1 (hle hgK) q).mp hgq
  · rintro (rfl | rfl)
    · exact ⟨g₀, hg₀K, hg₀1, hle hg₀K⟩
    · exact ⟨g₀, hg₀K, hg₀1, by rw [specialUnitaryGroup.smul_neg_unitSphere, hle hg₀K]⟩

/-- Any nontrivial subgroup `K ≤ SO(3)` fixing a point `p ∈ S²` has `2` pole orbits (`{p}` and
`{-p}`). -/
theorem natCard_orbitRelQuotient_poles_of_le_stabilizer
    {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} (hK : K ≠ ⊥)
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hle : K ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p) :
    Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 2 := by
  have hfix : ∀ (k : K) (q : poles K), k • q = q := by
    intro k q
    apply Subtype.ext
    rw [SubMulAction.val_smul_of_tower]
    have hq : (q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∈ ({p, -p} : Set _) := by
      rw [← coe_poles_eq_pair_of_le_stabilizer hK hle]
      exact q.2
    rcases hq with hq | hq
    · rw [hq]
      exact hle k.2
    · have hk_smul : k • (-p) = (k : specialOrthogonalGroup (Fin 3) ℝ) • (-p) := rfl
      rw [Set.mem_singleton_iff.mp hq, hk_smul, specialUnitaryGroup.smul_neg_unitSphere, hle k.2]
  have hequiv : MulAction.orbitRel.Quotient K (poles K) ≃ poles K :=
    (Quotient.congrRight fun x y ↦ by
      simp [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, hfix, eq_comm]).trans
      Setoid.quotientBotEquiv
  have hcard_poles : Nat.card (poles K) = 2 := by
    have hset : Nat.card (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) = 2 := by
      rw [coe_poles_eq_pair_of_le_stabilizer hK hle, Nat.card_coe_set_eq,
        Set.ncard_pair (neg_ne_self_unitSphere p).symm]
    exact hset
  rw [Nat.card_congr hequiv, hcard_poles]

/-- For `2 ≤ n`, the concrete cyclic axis subgroup `cyclicAxisSubgroup n` has `2` pole orbits. -/
theorem natCard_orbitRelQuotient_poles_cyclicAxisSubgroup {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Nat.card (MulAction.orbitRel.Quotient (cyclicAxisSubgroup n)
      (poles (cyclicAxisSubgroup n))) = 2 :=
  natCard_orbitRelQuotient_poles_of_le_stabilizer
    ((cyclicAxisSubgroup_ne_bot_iff n).mpr hn)
    (cyclicAxisSubgroup_le_stabilizer_basePole n)

/-- **Characterization of the two-orbit case by a common fixed pole.** A finite subgroup `K ≤ SO(3)`
has `2` pole orbits if and only if `K ≠ ⊥` and `K` fixes a point of `S²`. -/
theorem natCard_orbitRelQuotient_poles_eq_two_iff
    (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K] :
    Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 2 ↔
      K ≠ ⊥ ∧ ∃ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        K ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p := by
  refine ⟨fun h2 ↦ ?_, fun ⟨hK, p, hle⟩ ↦ natCard_orbitRelQuotient_poles_of_le_stabilizer hK hle⟩
  have hK : K ≠ ⊥ := by
    rintro rfl
    have hempty : IsEmpty (poles (⊥ : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))) := by
      rw [← not_nonempty_iff, nonempty_poles_iff]
      exact not_not.mpr rfl
    have : IsEmpty (MulAction.orbitRel.Quotient (⊥ : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))
        (poles ⊥)) := ⟨fun q ↦ Quotient.inductionOn' q hempty.elim⟩
    simp at h2
  have hNpos : 1 ≤ Nat.card K := Nat.card_pos
  have hburn := natCard_poles_add_two_mul_natCard_sub_one K
  rw [h2] at hburn
  have hP2 : Nat.card (poles K) = 2 := by omega
  obtain ⟨⟨p, hp⟩⟩ := nonempty_poles_iff.mpr hK
  have hpair_sub : ({p, -p} : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ⊆
      (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
    rintro q (rfl | rfl)
    · exact hp
    · exact neg_mem_poles_iff.mpr hp
  have : Finite (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    inferInstanceAs (Finite (poles K))
  have hfin : (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).Finite :=
    Set.toFinite _
  have hncard_poles : (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hP2
  have hncard_pair : ({p, -p} : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).ncard = 2 :=
    Set.ncard_pair (neg_ne_self_unitSphere p).symm
  have heq_set : ({p, -p} : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) =
      (poles K : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    Set.eq_of_subset_of_ncard_le hpair_sub (by rw [hncard_poles, hncard_pair]) hfin
  refine ⟨hK, p, fun g hgK ↦ ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  by_cases hg1 : g = 1
  · simp [hg1]
  · obtain ⟨q, hq⟩ := _root_.Matrix.SpecialOrthogonalGroup.exists_smul_eq_self_unitSphere g
    have hq_mem : q ∈ ({p, -p} : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
      rw [heq_set]
      exact ⟨g, hgK, hg1, hq⟩
    rcases hq_mem with rfl | hneg
    · exact hq
    · rw [Set.mem_singleton_iff] at hneg
      rw [hneg, specialUnitaryGroup.smul_neg_unitSphere, neg_inj] at hq
      exact hq

/-- **Characterization of the two-orbit case by conjugacy to `cyclicAxisSubgroup`.** -/
theorem natCard_orbitRelQuotient_poles_eq_two_iff_exists_conj_cyclicAxisSubgroup
    (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K] :
    Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 2 ↔
      2 ≤ Nat.card K ∧ ∃ F : specialOrthogonalGroup (Fin 3) ℝ,
        K = (cyclicAxisSubgroup (Nat.card K)).map (MulAut.conj F).toMonoidHom := by
  rw [natCard_orbitRelQuotient_poles_eq_two_iff]
  have : NeZero (Nat.card K) := ⟨Nat.card_pos.ne'⟩
  have hK_iff : K ≠ ⊥ ↔ 2 ≤ Nat.card K := by
    rw [Ne, Subgroup.eq_bot_iff_card]
    have hpos : 0 < Nat.card K := Nat.card_pos
    omega
  refine and_congr hK_iff ⟨?_, ?_⟩
  · rintro ⟨p, hle⟩
    exact exists_conj_cyclicAxisSubgroup_of_le_stabilizer K hle
  · rintro ⟨F, hF⟩
    refine ⟨F • basePole, ?_⟩
    rw [hF, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact Subgroup.map_mono (cyclicAxisSubgroup_le_stabilizer_basePole (Nat.card K))

/-- Any finite subgroup `K ≤ SO(3)` with `2` pole orbits is cyclic. -/
theorem isCyclic_of_natCard_orbitRelQuotient_poles_eq_two
    {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} [Finite K]
    (h2 : Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 2) :
    IsCyclic K := by
  obtain ⟨_, p, hle⟩ := (natCard_orbitRelQuotient_poles_eq_two_iff K).mp h2
  have htop : MulAction.stabilizer K p = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun k ↦ hle k.2
  let e : MulAction.stabilizer K p ≃* K :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact isCyclic_of_surjective e e.surjective

end TwoOrbits

section ThreeOrbitsClassification

/-- Every three-element pole-orbit space admits an enumeration `Fin 3 ≃ _` along which
`poleOrbitOrder K` is nondecreasing. -/
theorem exists_equiv_fin_three_poleOrbitOrder_mono
    {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} [Finite K]
    (h3 : Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 3) :
    ∃ e : Fin 3 ≃ MulAction.orbitRel.Quotient K (poles K),
      Monotone (poleOrbitOrder K ∘ e) := by
  let e₀ : Fin 3 ≃ MulAction.orbitRel.Quotient K (poles K) :=
    (Finite.equivFinOfCardEq h3).symm
  let σ : Equiv.Perm (Fin 3) := Tuple.sort (poleOrbitOrder K ∘ e₀)
  refine ⟨σ.trans e₀, ?_⟩
  have hcomp : poleOrbitOrder K ∘ σ.trans e₀ = (poleOrbitOrder K ∘ e₀) ∘ σ := rfl
  rw [hcomp]
  exact Tuple.monotone_sort (poleOrbitOrder K ∘ e₀)

/-- **Klein's Diophantine lemma for three pole orbits.** Solutions in integers `N ≥ 2` and
`2 ≤ m₀ ≤ m₁ ≤ m₂` to `q_i * m_i = N` and `q₀ + q₁ + q₂ + 2 * (N - 1) = 3 * N` are exhausted by
`(2, 2, m₂)` (`N = 2 * m₂`), `(2, 3, 3)` (`N = 12`), `(2, 3, 4)` (`N = 24`), and `(2, 3, 5)`
(`N = 60`). -/
theorem diophantine_pole_orders {N m₀ m₁ m₂ q₀ q₁ q₂ : ℕ}
    (hN : 2 ≤ N) (hm₀ : 2 ≤ m₀) (h01 : m₀ ≤ m₁) (h12 : m₁ ≤ m₂)
    (hq₀ : q₀ * m₀ = N) (hq₁ : q₁ * m₁ = N) (hq₂ : q₂ * m₂ = N)
    (hsum : q₀ + q₁ + q₂ + 2 * (N - 1) = 3 * N) :
    (m₀ = 2 ∧ m₁ = 2 ∧ 2 ≤ m₂ ∧ N = 2 * m₂) ∨
      (m₀ = 2 ∧ m₁ = 3 ∧ m₂ = 3 ∧ N = 12) ∨
      (m₀ = 2 ∧ m₁ = 3 ∧ m₂ = 4 ∧ N = 24) ∨
      (m₀ = 2 ∧ m₁ = 3 ∧ m₂ = 5 ∧ N = 60) := by
  have hq_sum : q₀ + q₁ + q₂ = N + 2 := by omega
  have heq : N * (m₁ * m₂ + m₀ * m₂ + m₀ * m₁) = (N + 2) * (m₀ * m₁ * m₂) := by
    calc
      N * (m₁ * m₂ + m₀ * m₂ + m₀ * m₁)
        = (q₀ * m₀) * (m₁ * m₂) + (q₁ * m₁) * (m₀ * m₂) + (q₂ * m₂) * (m₀ * m₁) := by
            rw [hq₀, hq₁, hq₂]; ring
      _ = (q₀ + q₁ + q₂) * (m₀ * m₁ * m₂) := by ring
      _ = (N + 2) * (m₀ * m₁ * m₂) := by rw [hq_sum]
  have hm₀_eq : m₀ = 2 := by
    by_contra hne
    have h3₀ : 3 ≤ m₀ := by omega
    have h3₁ : 3 ≤ m₁ := by omega
    have h3₂ : 3 ≤ m₂ := by omega
    have ha : 3 * (m₁ * m₂) ≤ m₀ * (m₁ * m₂) := Nat.mul_le_mul_right _ h3₀
    have hb : 3 * (m₀ * m₂) ≤ m₁ * (m₀ * m₂) := Nat.mul_le_mul_right _ h3₁
    have hc : 3 * (m₀ * m₁) ≤ m₂ * (m₀ * m₁) := Nat.mul_le_mul_right _ h3₂
    have hle_sum : m₁ * m₂ + m₀ * m₂ + m₀ * m₁ ≤ m₀ * m₁ * m₂ := by nlinarith
    have hleN : N * (m₁ * m₂ + m₀ * m₂ + m₀ * m₁) ≤ N * (m₀ * m₁ * m₂) :=
      Nat.mul_le_mul_left N hle_sum
    have hpos_prod : 0 < m₀ * m₁ * m₂ := by positivity
    nlinarith
  subst hm₀_eq
  have heqZ : (N : ℤ) * (4 - ((m₁ : ℤ) - 2) * ((m₂ : ℤ) - 2)) =
      4 * (m₁ : ℤ) * (m₂ : ℤ) := by
    have heq' : (N : ℤ) * ((m₁ : ℤ) * m₂ + 2 * m₂ + 2 * m₁) =
        ((N : ℤ) + 2) * (2 * m₁ * m₂) := by exact_mod_cast heq
    linear_combination heq'
  have hm₁_lt_4 : m₁ < 4 := by
    by_contra hge4
    have : (4 : ℤ) ≤ m₁ := by omega
    have : (4 : ℤ) ≤ m₂ := by omega
    have : (2 : ℤ) ≤ N := by omega
    nlinarith
  have hm₁_cases : m₁ = 2 ∨ m₁ = 3 := by omega
  rcases hm₁_cases with rfl | rfl
  · left
    refine ⟨rfl, rfl, by omega, ?_⟩
    omega
  · have hm₂_lt_6 : m₂ < 6 := by
      by_contra hge6
      have : (6 : ℤ) ≤ m₂ := by omega
      have : (2 : ℤ) ≤ N := by omega
      nlinarith
    have hm₂_cases : m₂ = 3 ∨ m₂ = 4 ∨ m₂ = 5 := by omega
    rcases hm₂_cases with rfl | rfl | rfl
    · right; left; exact ⟨rfl, rfl, rfl, by omega⟩
    · right; right; left; exact ⟨rfl, rfl, rfl, by omega⟩
    · right; right; right; exact ⟨rfl, rfl, rfl, by omega⟩

/-- **Klein's Diophantine classification of three-orbit finite subgroups of `SO(3)`.** Along any
nondecreasing enumeration `e : Fin 3 ≃ MulAction.orbitRel.Quotient K (poles K)` of the three pole
orbits, the stabilizer orders `(m₀, m₁, m₂)` and group order `|K|` belong to one of the four types
`(2, 2, n)` (`|K| = 2n`), `(2, 3, 3)` (`|K| = 12`), `(2, 3, 4)` (`|K| = 24`), or `(2, 3, 5)`
(`|K| = 60`). -/
theorem poleOrbitOrder_classification_of_three_orbits
    {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} [Finite K]
    (e : Fin 3 ≃ MulAction.orbitRel.Quotient K (poles K))
    (hmono : Monotone (poleOrbitOrder K ∘ e)) :
    (poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 2 ∧
        2 ≤ poleOrbitOrder K (e 2) ∧ Nat.card K = 2 * poleOrbitOrder K (e 2)) ∨
      (poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 3 ∧
        poleOrbitOrder K (e 2) = 3 ∧ Nat.card K = 12) ∨
      (poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 3 ∧
        poleOrbitOrder K (e 2) = 4 ∧ Nat.card K = 24) ∨
      (poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 3 ∧
        poleOrbitOrder K (e 2) = 5 ∧ Nat.card K = 60) := by
  let _ : Fintype (MulAction.orbitRel.Quotient K (poles K)) := Fintype.ofFinite _
  have h3 : Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 3 := by
    rw [← Nat.card_congr e]
    exact Nat.card_fin 3
  have hK : K ≠ ⊥ := by
    rintro rfl
    have hempty : IsEmpty (poles (⊥ : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))) := by
      rw [← not_nonempty_iff, nonempty_poles_iff]
      exact not_not.mpr rfl
    have : IsEmpty (MulAction.orbitRel.Quotient (⊥ : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))
        (poles ⊥)) := ⟨fun q ↦ Quotient.inductionOn' q hempty.elim⟩
    simp at h3
  have hN : 2 ≤ Nat.card K := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hne1 : Nat.card K ≠ 1 := by rwa [Ne, ← Subgroup.eq_bot_iff_card]
    omega
  have hsum_orb : Nat.card (e 0).orbit + Nat.card (e 1).orbit + Nat.card (e 2).orbit =
      Nat.card (poles K) := by
    have hs := sum_natCard_orbit_poles K
    rw [← Equiv.sum_comp e, Fin.sum_univ_three] at hs
    exact hs
  have hburn := natCard_poles_add_two_mul_natCard_sub_one K
  rw [← hsum_orb, h3] at hburn
  exact diophantine_pole_orders hN (two_le_poleOrbitOrder (e 0))
    (hmono (by decide : (0 : Fin 3) ≤ 1)) (hmono (by decide : (1 : Fin 3) ≤ 2))
    (natCard_orbit_mul_poleOrbitOrder (e 0)) (natCard_orbit_mul_poleOrbitOrder (e 1))
    (natCard_orbit_mul_poleOrbitOrder (e 2)) hburn

/-- **Full pole-orbit trichotomy for finite subgroups of `SO(3)`.** Every finite subgroup
`K ≤ SO(3)` is either trivial (`K = ⊥`), cyclic and conjugate to `cyclicAxisSubgroup (Nat.card K)`
with `2` pole orbits, or has `3` pole orbits of numerical type `(2, 2, n)`, `(2, 3, 3)`,
`(2, 3, 4)`, or `(2, 3, 5)`. -/
theorem finite_subgroup_orbit_classification
    (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K] :
    K = ⊥ ∨
      (Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 2 ∧ 2 ≤ Nat.card K ∧
        ∃ F : specialOrthogonalGroup (Fin 3) ℝ,
          K = (cyclicAxisSubgroup (Nat.card K)).map (MulAut.conj F).toMonoidHom) ∨
      (Nat.card (MulAction.orbitRel.Quotient K (poles K)) = 3 ∧
        ∃ e : Fin 3 ≃ MulAction.orbitRel.Quotient K (poles K),
          Monotone (poleOrbitOrder K ∘ e) ∧
          ((poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 2 ∧
              2 ≤ poleOrbitOrder K (e 2) ∧ Nat.card K = 2 * poleOrbitOrder K (e 2)) ∨
            (poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 3 ∧
              poleOrbitOrder K (e 2) = 3 ∧ Nat.card K = 12) ∨
            (poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 3 ∧
              poleOrbitOrder K (e 2) = 4 ∧ Nat.card K = 24) ∨
            (poleOrbitOrder K (e 0) = 2 ∧ poleOrbitOrder K (e 1) = 3 ∧
              poleOrbitOrder K (e 2) = 5 ∧ Nat.card K = 60))) := by
  by_cases hK : K = ⊥
  · exact Or.inl hK
  · rcases natCard_orbitRelQuotient_poles_eq_two_or_three hK with h2 | h3
    · right; left
      obtain ⟨hcard, hconj⟩ :=
        (natCard_orbitRelQuotient_poles_eq_two_iff_exists_conj_cyclicAxisSubgroup K).mp h2
      exact ⟨h2, hcard, hconj⟩
    · right; right
      obtain ⟨e, hmono⟩ := exists_equiv_fin_three_poleOrbitOrder_mono h3
      exact ⟨h3, e, hmono, poleOrbitOrder_classification_of_three_orbits e hmono⟩

end ThreeOrbitsClassification

section DihedralModel

private theorem matrix_eq_of_mulVec_eq {M N : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ w : Fin 3 → ℝ, M *ᵥ w = N *ᵥ w) : M = N := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

/-- The half-turn `diag(-1, -1, 1) ∈ SO(3)` about `e₂`, which reverses `basePole = e₀` and
inverts rotations about `basePole` under conjugation. -/
def basePoleFlip : specialOrthogonalGroup (Fin 3) ℝ :=
  coordinateHalfTurn (R := ℝ) 0 1 (by decide)

theorem basePoleFlip_eq_coordinateHalfTurn :
    basePoleFlip = coordinateHalfTurn (R := ℝ) 0 1 (by decide) :=
  (rfl)

@[simp]
theorem basePoleFlip_mulVec (w : Fin 3 → ℝ) (a : Fin 3) :
    ((basePoleFlip : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) a =
      if a = 0 ∨ a = 1 then -w a else w a :=
  coordinateHalfTurn_mulVec 0 1 (by decide) w a

@[simp]
theorem basePoleFlip_mul_self : basePoleFlip * basePoleFlip = 1 := by
  refine Subtype.ext <| matrix_eq_of_mulVec_eq fun w ↦ ?_
  rw [Submonoid.coe_mul, OneMemClass.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;> simp

@[simp]
theorem basePoleFlip_mul_self_right (g : specialOrthogonalGroup (Fin 3) ℝ) :
    basePoleFlip * (basePoleFlip * g) = g := by
  rw [← mul_assoc, basePoleFlip_mul_self, one_mul]

@[simp]
theorem basePoleFlip_inv : basePoleFlip⁻¹ = basePoleFlip :=
  inv_eq_of_mul_eq_one_right basePoleFlip_mul_self

@[simp]
theorem basePoleFlip_smul_basePole : basePoleFlip • basePole = -basePole := by
  refine Subtype.ext <| (WithLp.ofLp_injective 2) <| funext fun i ↦ ?_
  rw [specialUnitaryGroup.ofLp_coe_smul_unitSphere, ofLp_coe_basePole]
  have hneg : ((-basePole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)).ofLp = -Pi.single 0 1 := by simp
  rw [hneg]
  fin_cases i <;> simp

theorem basePoleFlip_ne_one : basePoleFlip ≠ 1 := by
  intro h1
  have hfix : basePoleFlip • basePole = basePole := by simp [h1]
  rw [basePoleFlip_smul_basePole] at hfix
  exact neg_ne_self_unitSphere basePole hfix

/-- Conjugating an axis rotation `basePoleAxisHom ζ` by `basePoleFlip` inverts the rotation
angle. -/
theorem basePoleFlip_mul_basePoleAxisHom_mul_basePoleFlip (ζ : Circle) :
    basePoleFlip * basePoleAxisHom ζ * basePoleFlip = basePoleAxisHom ζ⁻¹ := by
  have hconj : ((ζ⁻¹ : Circle) : ℂ) = starRingEnd ℂ (ζ : ℂ) := Circle.coe_inv_eq_conj ζ
  have hre : ((ζ⁻¹ : Circle) : ℂ).re = (ζ : ℂ).re := by simp [hconj]
  have him : ((ζ⁻¹ : Circle) : ℂ).im = -(ζ : ℂ).im := by simp [hconj]
  refine Subtype.ext <| matrix_eq_of_mulVec_eq fun w ↦ ?_
  let v : Fin 3 → ℝ := (basePoleFlip : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w
  let u : Fin 3 → ℝ := (basePoleAxisHom ζ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v
  have hlhs : ((basePoleFlip * basePoleAxisHom ζ * basePoleFlip :
      specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w =
      (basePoleFlip : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u := by
    simp [u, v, Matrix.mulVec_mulVec, mul_assoc]
  rw [hlhs]
  have h0 : ((basePoleFlip : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u) 0 =
      ((basePoleAxisHom ζ⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) 0 := by
    dsimp only [u, v]
    rw [basePoleFlip_mulVec, ite_eq_left (Or.inl rfl), basePoleAxisHom_mulVec_zero,
      basePoleAxisHom_mulVec_zero, basePoleFlip_mulVec, ite_eq_left (Or.inl rfl), neg_neg]
  have h1 : ((basePoleFlip : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u) 1 =
      ((basePoleAxisHom ζ⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) 1 := by
    rw [basePoleFlip_mulVec, basePoleAxisHom_mulVec_one]
    simp only [u, v, Fin.isValue, or_true, reduceIte, basePoleAxisHom_mulVec_one,
      basePoleFlip_mulVec, Fin.reduceEq, or_self]
    rw [hre, him]
    ring
  have h2 : ((basePoleFlip : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u) 2 =
      ((basePoleAxisHom ζ⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) 2 := by
    rw [basePoleFlip_mulVec, basePoleAxisHom_mulVec_two]
    simp only [u, v, Fin.isValue, Fin.reduceEq, or_self, reduceIte,
      basePoleAxisHom_mulVec_two, basePoleFlip_mulVec, or_true]
    rw [hre, him]
    ring
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem basePoleFlip_conj_mem_cyclicAxisSubgroup (n : ℕ) [NeZero n]
    {g : specialOrthogonalGroup (Fin 3) ℝ} (hg : g ∈ cyclicAxisSubgroup n) :
    basePoleFlip * g * basePoleFlip ∈ cyclicAxisSubgroup n := by
  rw [mem_cyclicAxisSubgroup_iff] at hg ⊢
  obtain ⟨j, rfl⟩ := hg
  refine ⟨j⁻¹, ?_⟩
  simp only [cyclicAxisHom_apply]
  rw [basePoleFlip_mul_basePoleAxisHom_mul_basePoleFlip, toAdd_inv, AddChar.map_neg_eq_inv]

/-- **The concrete dihedral subgroup of order `2 * n` in `SO(3)`**, consisting of the rotations
`cyclicAxisSubgroup n` about `basePole` together with their right coset by the half-turn
`basePoleFlip`. -/
noncomputable def dihedralAxisSubgroup (n : ℕ) [NeZero n] :
    Subgroup (specialOrthogonalGroup (Fin 3) ℝ) where
  carrier := {g | g ∈ cyclicAxisSubgroup n ∨ g * basePoleFlip ∈ cyclicAxisSubgroup n}
  one_mem' := Or.inl (cyclicAxisSubgroup n).one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl ((cyclicAxisSubgroup n).mul_mem ha hb)
    · right
      rw [mul_assoc]
      exact (cyclicAxisSubgroup n).mul_mem ha hb
    · right
      have hconj := basePoleFlip_conj_mem_cyclicAxisSubgroup n hb
      have hprod := (cyclicAxisSubgroup n).mul_mem ha hconj
      have heq : (a * basePoleFlip) * (basePoleFlip * b * basePoleFlip) =
          a * b * basePoleFlip := by simp [mul_assoc]
      rwa [heq] at hprod
    · left
      have hconj := basePoleFlip_conj_mem_cyclicAxisSubgroup n hb
      have hprod := (cyclicAxisSubgroup n).mul_mem ha hconj
      have heq : (a * basePoleFlip) * (basePoleFlip * (b * basePoleFlip) * basePoleFlip) =
          a * b := by simp [mul_assoc]
      rwa [heq] at hprod
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl ((cyclicAxisSubgroup n).inv_mem ha)
    · right
      have hinv := (cyclicAxisSubgroup n).inv_mem ha
      rw [_root_.mul_inv_rev, basePoleFlip_inv] at hinv
      have hconj := basePoleFlip_conj_mem_cyclicAxisSubgroup n hinv
      have heq : basePoleFlip * (basePoleFlip * a⁻¹) * basePoleFlip = a⁻¹ * basePoleFlip := by
        simp
      rwa [heq] at hconj

@[simp]
theorem mem_dihedralAxisSubgroup_iff (n : ℕ) [NeZero n]
    {g : specialOrthogonalGroup (Fin 3) ℝ} :
    g ∈ dihedralAxisSubgroup n ↔
      g ∈ cyclicAxisSubgroup n ∨ g * basePoleFlip ∈ cyclicAxisSubgroup n :=
  Iff.rfl

theorem cyclicAxisSubgroup_le_dihedralAxisSubgroup (n : ℕ) [NeZero n] :
    cyclicAxisSubgroup n ≤ dihedralAxisSubgroup n :=
  fun _ hg ↦ Or.inl hg

theorem basePoleFlip_mem_dihedralAxisSubgroup (n : ℕ) [NeZero n] :
    basePoleFlip ∈ dihedralAxisSubgroup n :=
  Or.inr (by simp [(cyclicAxisSubgroup n).one_mem])

theorem basePoleFlip_notMem_cyclicAxisSubgroup (n : ℕ) [NeZero n] :
    basePoleFlip ∉ cyclicAxisSubgroup n := by
  intro hmem
  have hfix := cyclicAxisSubgroup_le_stabilizer_basePole n hmem
  rw [MulAction.mem_stabilizer_iff, basePoleFlip_smul_basePole] at hfix
  exact neg_ne_self_unitSphere basePole hfix

private noncomputable def dihedralAxisSubgroupEquivSum (n : ℕ) [NeZero n] :
    cyclicAxisSubgroup n ⊕ cyclicAxisSubgroup n ≃ dihedralAxisSubgroup n := by
  refine Equiv.ofBijective
    (Sum.elim (fun h ↦ ⟨h.1, Or.inl h.2⟩)
      (fun h ↦ ⟨h.1 * basePoleFlip, Or.inr (by
        have heq : h.1 * basePoleFlip * basePoleFlip = h.1 := by simp [mul_assoc]
        rw [heq]
        exact h.2)⟩))
    ⟨?_, ?_⟩
  · rintro (h₁ | h₁) (h₂ | h₂) heq <;> dsimp at heq
    · have hval : h₁.1 = h₂.1 := congrArg (Subtype.val : dihedralAxisSubgroup n → _) heq
      exact congrArg Sum.inl (Subtype.ext hval)
    · exfalso
      have hval : h₁.1 = h₂.1 * basePoleFlip := Subtype.ext_iff.mp heq
      have hflip : basePoleFlip = h₂.1⁻¹ * h₁.1 := by
        rw [hval]
        simp
      exact basePoleFlip_notMem_cyclicAxisSubgroup n
        (hflip ▸ (cyclicAxisSubgroup n).mul_mem ((cyclicAxisSubgroup n).inv_mem h₂.2) h₁.2)
    · exfalso
      have hval : h₁.1 * basePoleFlip = h₂.1 := Subtype.ext_iff.mp heq
      have hflip : basePoleFlip = h₁.1⁻¹ * h₂.1 := by
        rw [← hval]
        simp
      exact basePoleFlip_notMem_cyclicAxisSubgroup n
        (hflip ▸ (cyclicAxisSubgroup n).mul_mem ((cyclicAxisSubgroup n).inv_mem h₁.2) h₂.2)
    · refine congrArg Sum.inr (Subtype.ext ?_)
      have hval : h₁.1 * basePoleFlip = h₂.1 * basePoleFlip := Subtype.ext_iff.mp heq
      exact mul_right_cancel hval
  · rintro ⟨g, hg | hg⟩
    · exact ⟨Sum.inl ⟨g, hg⟩, rfl⟩
    · refine ⟨Sum.inr ⟨g * basePoleFlip, hg⟩, Subtype.ext ?_⟩
      simp [mul_assoc]

instance instFiniteDihedralAxisSubgroup (n : ℕ) [NeZero n] : Finite (dihedralAxisSubgroup n) :=
  Finite.of_equiv _ (dihedralAxisSubgroupEquivSum n)

@[simp]
theorem natCard_dihedralAxisSubgroup (n : ℕ) [NeZero n] :
    Nat.card (dihedralAxisSubgroup n) = 2 * n := by
  let _ : Fintype (cyclicAxisSubgroup n) := Fintype.ofFinite _
  let _ : Fintype (dihedralAxisSubgroup n) := Fintype.ofFinite _
  rw [← Nat.card_congr (dihedralAxisSubgroupEquivSum n), Nat.card_eq_fintype_card,
    Fintype.card_sum, ← Nat.card_eq_fintype_card, natCard_cyclicAxisSubgroup, two_mul]

/-- **For `2 ≤ n`, the concrete dihedral subgroup `dihedralAxisSubgroup n` has `3` pole orbits on
`S²`**, witnessing the `(2, 2, n)` branch of `poleOrbitOrder_classification_of_three_orbits`. -/
theorem natCard_orbitRelQuotient_poles_dihedralAxisSubgroup {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Nat.card (MulAction.orbitRel.Quotient (dihedralAxisSubgroup n)
      (poles (dihedralAxisSubgroup n))) = 3 := by
  have hne_bot : dihedralAxisSubgroup n ≠ ⊥ := by
    rw [Ne, Subgroup.eq_bot_iff_card, natCard_dihedralAxisSubgroup]
    omega
  rcases natCard_orbitRelQuotient_poles_eq_two_or_three hne_bot with h2 | h3
  · exfalso
    obtain ⟨_, p, hle⟩ := (natCard_orbitRelQuotient_poles_eq_two_iff _).mp h2
    have hex : ∃ g ∈ cyclicAxisSubgroup n, g ≠ 1 := by
      by_contra! hall
      exact (cyclicAxisSubgroup_ne_bot_iff n).mpr hn ((Subgroup.eq_bot_iff_forall _).mpr hall)
    obtain ⟨g, hgC, hg1⟩ := hex
    have hgp : g • p = p := hle (cyclicAxisSubgroup_le_dihedralAxisSubgroup n hgC)
    have hgbase : g • basePole = basePole := cyclicAxisSubgroup_le_stabilizer_basePole n hgC
    have hp_pair := (smul_eq_self_unitSphere_iff_of_ne_one hg1 hgbase p).mp hgp
    have hflip_p : basePoleFlip • p = p := hle (basePoleFlip_mem_dihedralAxisSubgroup n)
    rcases hp_pair with rfl | rfl
    · rw [basePoleFlip_smul_basePole] at hflip_p
      exact neg_ne_self_unitSphere basePole hflip_p
    · rw [specialUnitaryGroup.smul_neg_unitSphere, basePoleFlip_smul_basePole, neg_neg,
        eq_comm] at hflip_p
      exact neg_ne_self_unitSphere basePole hflip_p
  · exact h3

end DihedralModel

end TauCeti.Matrix.SpecialOrthogonalGroup
