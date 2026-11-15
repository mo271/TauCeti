/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.GroupTheory.DoubleCoset.Finite
public import TauCeti.GroupTheory.DoubleCoset.Inv
public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.GroupTheory.GroupAction.Orbit.CycleType
public import TauCeti.GroupTheory.GroupAction.Period

/-!
# Double cosets, left-coset orbits, and right-coset fiber counts

For subgroups `H` and `K` of a group `G`, `TauCeti.GroupTheory.DoubleCoset.Orbits` identifies the
double cosets `K \ G / H` with the `K`-orbits on `G ⧸ H` via `x ∈ K s H ↔ (x : G ⧸ H) ∈ orbit K s`.
Combining that description with the inversion bijection `H \ G / K ≃ K \ G / H`
(`DoubleCoset.quotientInvEquiv`, sending `H g K` to `K g⁻¹ H`) gives the companion dictionary on the
opposite side, where `H` sits on the left and `K` sits on the right:

* **Inversion and quotient bijections (`DoubleCoset.quotientInvEquiv`,
  `TauCeti.orbitRelQuotientQuotientEquivDoubleCosetLeft`,
  `TauCeti.orbitRelQuotientQuotientEquivDoubleCoset`).** `K`-orbits on `G ⧸ H` are in canonical
  bijection both with `K \ G / H` (sending `orbit K (g H)` to `K g H`) and with `H \ G / K`
  (sending `orbit K (g H)` to `H g⁻¹ K`), so `H \ G / K` is finite whenever `H` has finite index
  (`TauCeti.finite_doubleCosetQuotient_left`).
* **Right-coset fibers inside a double coset (`DoubleCoset.rightCosetToDoubleCoset`,
  `TauCeti.rightCosetFiberEquivOrbit`, `TauCeti.natCard_rightCosetFiber_mk`,
  `TauCeti.natCard_rightCosetFiber_zpowers_mk`).** Each double coset `H g K` is a union of right
  cosets `H x`, and `H x ↦ x⁻¹ H` carries the right-coset fiber over `H g K` bijectively onto
  `MulAction.orbit K (g⁻¹ : G ⧸ H)`. For `K = Subgroup.zpowers t`, the number of right cosets of
  `H` inside `H g ⟨t⟩` equals `MulAction.period t (g⁻¹ : G ⧸ H)`, with no finiteness assumption on
  `G` or `H`.
* **Full cycle type via double cosets
  (`TauCeti.fullCycleType_permutationRepresentation_eq_map_doubleCoset`).** For an enumeration
  `e : G ⧸ H ≃ β` of a finite coset space, the full cycle type of `e.permutationRepresentation t`
  is the multiset of right-coset fiber sizes over `H \ G / ⟨t⟩`.
-/

open MulAction

public section

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- Inversion `g ↦ g⁻¹` induces a canonical bijection `H \ G / K ≃ K \ G / H` exchanging the two
flanking subgroups: `H g K` maps to `K g⁻¹ H`. -/
def quotientInvEquiv (H K : Subgroup G) :
    Quotient (H : Set G) K ≃ Quotient (K : Set G) H where
  toFun := _root_.Quotient.lift (fun g ↦ mk K H g⁻¹) fun _ _ hab ↦
    eq.mpr <| mem_doubleCoset.mp <| inv_mem_doubleCoset_inv_iff.mpr <|
      mem_doubleCoset.mpr (eq.mp (_root_.Quotient.sound hab))
  invFun := _root_.Quotient.lift (fun g ↦ mk H K g⁻¹) fun _ _ hab ↦
    eq.mpr <| mem_doubleCoset.mp <| inv_mem_doubleCoset_inv_iff.mpr <|
      mem_doubleCoset.mpr (eq.mp (_root_.Quotient.sound hab))
  left_inv q := _root_.Quotient.inductionOn q fun g ↦ by
    -- Unfold the lifted inversion maps on representatives to expose `(g⁻¹)⁻¹ = g`.
    change mk H K (g⁻¹)⁻¹ = mk H K g
    rw [inv_inv]
  right_inv q := _root_.Quotient.inductionOn q fun g ↦ by
    -- Unfold the lifted inversion maps on representatives to expose `(g⁻¹)⁻¹ = g`.
    change mk K H (g⁻¹)⁻¹ = mk K H g
    rw [inv_inv]

/-- `DoubleCoset.quotientInvEquiv` sends `DoubleCoset.mk H K g` to `DoubleCoset.mk K H g⁻¹`. -/
@[simp]
theorem quotientInvEquiv_apply_mk (H K : Subgroup G) (g : G) :
    quotientInvEquiv H K (mk H K g) = mk K H g⁻¹ := (rfl)

/-- The inverse of `DoubleCoset.quotientInvEquiv H K` is `DoubleCoset.quotientInvEquiv K H`. -/
@[simp]
theorem quotientInvEquiv_symm (H K : Subgroup G) :
    (quotientInvEquiv H K).symm = quotientInvEquiv K H := (rfl)

/-- Projection from the right coset space `Quotient (QuotientGroup.rightRel H)` to the double coset
space `H \ G / K`, sending the right coset `H x` to `H x K`. -/
def rightCosetToDoubleCoset (H K : Subgroup G) :
    _root_.Quotient (QuotientGroup.rightRel H) → Quotient (H : Set G) K :=
  _root_.Quotient.lift (mk H K) fun a b hab ↦ by
    have hh : b * a⁻¹ ∈ H := by simpa [QuotientGroup.rightRel_apply] using hab
    simpa [inv_mul_cancel_right] using (mk_mem_mul (H := H) (K := K) ⟨b * a⁻¹, hh⟩ a).symm

/-- `DoubleCoset.rightCosetToDoubleCoset` sends the right coset of `x` to `DoubleCoset.mk H K x`. -/
@[simp]
theorem rightCosetToDoubleCoset_mk (H K : Subgroup G) (x : G) :
    rightCosetToDoubleCoset H K (_root_.Quotient.mk'' x) = mk H K x := (rfl)

/-- Every double coset `H g K` contains at least one right coset `H g`. -/
theorem rightCosetToDoubleCoset_surjective (H K : Subgroup G) :
    Function.Surjective (rightCosetToDoubleCoset H K) :=
  fun d ↦ _root_.Quotient.inductionOn d fun g ↦ ⟨_root_.Quotient.mk'' g, rfl⟩

end DoubleCoset

namespace TauCeti

variable {G : Type*} [Group G]

/-- **The double cosets `H \ G / K` are finite when `H` has finite index**: dual to
`TauCeti.finite_doubleCosetQuotient` via `DoubleCoset.quotientInvEquiv`. -/
instance finite_doubleCosetQuotient_left (H K : Subgroup G) [H.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
  Finite.of_equiv _ (DoubleCoset.quotientInvEquiv H K).symm

/-- Projection from the left coset space `G ⧸ H` to the double coset space `K \ G / H`, sending
`g H` to `K g H`. -/
private def quotientToDoubleCosetLeft (H K : Subgroup G) :
    G ⧸ H → DoubleCoset.Quotient (K : Set G) H :=
  fun q ↦ Quotient.liftOn' q (DoubleCoset.mk K H) fun a b hab ↦
    DoubleCoset.eq.mpr ⟨1, K.one_mem, a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab,
      by rw [one_mul, mul_inv_cancel_left]⟩

/-- **Left-coset `K`-orbits are `K \ G / H` double cosets.** Sending the `K`-orbit of `g H` to
`K g H` is a bijection `MulAction.orbitRel.Quotient K (G ⧸ H) ≃ DoubleCoset.Quotient K H`. -/
def orbitRelQuotientQuotientEquivDoubleCosetLeft (H K : Subgroup G) :
    orbitRel.Quotient K (G ⧸ H) ≃ DoubleCoset.Quotient (K : Set G) H where
  toFun ω := Quotient.liftOn' ω (quotientToDoubleCosetLeft H K) fun a b ↦
    QuotientGroup.induction_on a fun _ ↦ QuotientGroup.induction_on b fun y hab ↦
      (DoubleCoset.eq.mpr <| DoubleCoset.mem_doubleCoset.mp <|
        (mem_doubleCoset_iff_mk_mem_orbit y H K).mpr (orbitRel_apply.mp hab)).symm
  invFun := Quotient.lift (fun g ↦ (Quotient.mk'' (g : G ⧸ H) : orbitRel.Quotient K (G ⧸ H)))
    fun _ b hab ↦ Quotient.sound' <| orbitRel_apply.mpr <|
      (mem_doubleCoset_iff_mk_mem_orbit b H K).mp <|
        DoubleCoset.mem_doubleCoset.mpr (DoubleCoset.eq.mp (Quotient.sound hab).symm)
  left_inv ω := Quotient.inductionOn' ω fun q ↦ QuotientGroup.induction_on q fun _ ↦ rfl
  right_inv d := Quotient.inductionOn d fun _ ↦ rfl

/-- `orbitRelQuotientQuotientEquivDoubleCosetLeft` sends the `K`-orbit of `g H` to `K g H`. -/
@[simp]
theorem orbitRelQuotientQuotientEquivDoubleCosetLeft_mk (H K : Subgroup G) (g : G) :
    orbitRelQuotientQuotientEquivDoubleCosetLeft H K (Quotient.mk'' (g : G ⧸ H)) =
      DoubleCoset.mk K H g := (rfl)

/-- The inverse of `orbitRelQuotientQuotientEquivDoubleCosetLeft` sends `K g H` to the `K`-orbit of
`g H`. -/
@[simp]
theorem orbitRelQuotientQuotientEquivDoubleCosetLeft_symm_mk (H K : Subgroup G) (g : G) :
    (orbitRelQuotientQuotientEquivDoubleCosetLeft H K).symm (DoubleCoset.mk K H g) =
      Quotient.mk'' (g : G ⧸ H) := (rfl)

/-- **Left-coset `K`-orbits are `H \ G / K` double cosets.** Composing
`orbitRelQuotientQuotientEquivDoubleCosetLeft` with `DoubleCoset.quotientInvEquiv` identifies
`MulAction.orbitRel.Quotient K (G ⧸ H)` with `DoubleCoset.Quotient H K` via
`orbit K (g H) ↦ H g⁻¹ K`. -/
def orbitRelQuotientQuotientEquivDoubleCoset (H K : Subgroup G) :
    orbitRel.Quotient K (G ⧸ H) ≃ DoubleCoset.Quotient (H : Set G) K :=
  (orbitRelQuotientQuotientEquivDoubleCosetLeft H K).trans (DoubleCoset.quotientInvEquiv K H)

/-- `orbitRelQuotientQuotientEquivDoubleCoset` sends the `K`-orbit of `g H` to `H g⁻¹ K`. -/
@[simp]
theorem orbitRelQuotientQuotientEquivDoubleCoset_mk (H K : Subgroup G) (g : G) :
    orbitRelQuotientQuotientEquivDoubleCoset H K (Quotient.mk'' (g : G ⧸ H)) =
      DoubleCoset.mk H K g⁻¹ := by
  rw [orbitRelQuotientQuotientEquivDoubleCoset, Equiv.trans_apply,
    orbitRelQuotientQuotientEquivDoubleCosetLeft_mk, DoubleCoset.quotientInvEquiv_apply_mk]

/-- The inverse of `orbitRelQuotientQuotientEquivDoubleCoset` sends `H g K` to the `K`-orbit of
`g⁻¹ H`. -/
@[simp]
theorem orbitRelQuotientQuotientEquivDoubleCoset_symm_mk (H K : Subgroup G) (g : G) :
    (orbitRelQuotientQuotientEquivDoubleCoset H K).symm (DoubleCoset.mk H K g) =
      Quotient.mk'' ((g⁻¹ : G) : G ⧸ H) := by
  rw [orbitRelQuotientQuotientEquivDoubleCoset, Equiv.symm_trans_apply,
    DoubleCoset.quotientInvEquiv_symm, DoubleCoset.quotientInvEquiv_apply_mk,
    orbitRelQuotientQuotientEquivDoubleCosetLeft_symm_mk]

/-- Under `QuotientGroup.quotientRightRelEquivQuotientLeftRel H` (`H x ↦ x⁻¹ H`), the right cosets
of `H` lying inside a double coset `d : H \ G / K` correspond bijectively to the corresponding
`K`-orbit on `G ⧸ H`. -/
def rightCosetFiberEquivOrbit (H K : Subgroup G) (d : DoubleCoset.Quotient (H : Set G) K) :
    {r : Quotient (QuotientGroup.rightRel H) // DoubleCoset.rightCosetToDoubleCoset H K r = d} ≃
      ((orbitRelQuotientQuotientEquivDoubleCoset H K).symm d).orbit :=
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).subtypeEquiv fun r ↦
    Quotient.inductionOn' r fun x ↦ by
      rw [QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk,
        DoubleCoset.rightCosetToDoubleCoset_mk, orbitRel.Quotient.mem_orbit,
        (orbitRelQuotientQuotientEquivDoubleCoset H K).eq_symm_apply,
        orbitRelQuotientQuotientEquivDoubleCoset_mk, inv_inv]

/-- The number of right cosets of `H` inside a double coset `d : H \ G / K` equals the `Nat.card`
of the corresponding `K`-orbit on `G ⧸ H`, without finiteness hypotheses on `G` or `H`. -/
theorem natCard_rightCosetFiber_eq_natCard_orbit (H K : Subgroup G)
    (d : DoubleCoset.Quotient (H : Set G) K) :
    Nat.card {r : Quotient (QuotientGroup.rightRel H) //
        DoubleCoset.rightCosetToDoubleCoset H K r = d} =
      Nat.card ((orbitRelQuotientQuotientEquivDoubleCoset H K).symm d).orbit :=
  Nat.card_congr (rightCosetFiberEquivOrbit H K d)

/-- The number of right cosets of `H` inside `H g K` equals `Nat.card (orbit K (g⁻¹ H))`. -/
theorem natCard_rightCosetFiber_mk (H K : Subgroup G) (g : G) :
    Nat.card {r : Quotient (QuotientGroup.rightRel H) //
        DoubleCoset.rightCosetToDoubleCoset H K r = DoubleCoset.mk H K g} =
      Nat.card (orbit K ((g⁻¹ : G) : G ⧸ H)) := by
  rw [natCard_rightCosetFiber_eq_natCard_orbit,
    orbitRelQuotientQuotientEquivDoubleCoset_symm_mk, orbitRel.Quotient.orbit_mk]

/-- For a cyclic right subgroup `⟨t⟩`, the number of right cosets of `H` inside `H g ⟨t⟩` equals
`MulAction.period t ((g⁻¹ : G) : G ⧸ H)`. Unlike `|H g ⟨t⟩| / |H|`, this holds for infinite `H`
and `G`. -/
theorem natCard_rightCosetFiber_zpowers_mk (H : Subgroup G) (t g : G) :
    Nat.card {r : Quotient (QuotientGroup.rightRel H) //
        DoubleCoset.rightCosetToDoubleCoset H (Subgroup.zpowers t) r =
          DoubleCoset.mk H (Subgroup.zpowers t) g} =
      MulAction.period t ((g⁻¹ : G) : G ⧸ H) := by
  rw [natCard_rightCosetFiber_mk, MulAction.natCard_orbit_zpowers]

open scoped Classical in
/-- For an enumeration `e : G ⧸ H ≃ β` of a finite coset space, the full cycle type of
`e.permutationRepresentation t` is the multiset of right-coset fiber sizes over the double cosets
`H \ G / ⟨t⟩`. -/
theorem fullCycleType_permutationRepresentation_eq_map_doubleCoset {β : Type*} [Fintype β]
    [DecidableEq β] {H : Subgroup G} (e : G ⧸ H ≃ β) (t : G) :
    let : Fintype (DoubleCoset.Quotient (H : Set G) (Subgroup.zpowers t)) :=
      have : H.FiniteIndex := H.finiteIndex_of_equiv e
      Fintype.ofFinite _
    (e.permutationRepresentation t).fullCycleType =
      (Finset.univ : Finset (DoubleCoset.Quotient (H : Set G) (Subgroup.zpowers t))).val.map
        fun d ↦ Nat.card {r : Quotient (QuotientGroup.rightRel H) //
          DoubleCoset.rightCosetToDoubleCoset H (Subgroup.zpowers t) r = d} := by
  intro _
  let : Fintype (G ⧸ H) := Fintype.ofEquiv β e.symm
  let e' := (orbitRelQuotientQuotientEquivDoubleCoset H (Subgroup.zpowers t)).symm
  have hperm : e.permutationRepresentation t = e.permCongr (toPerm t) :=
    Equiv.ext fun i ↦ by simp [Equiv.permutationRepresentation_apply, Equiv.permCongr_apply]
  rw [hperm, Equiv.Perm.fullCycleType_permCongr, fullCycleType_toPerm_eq_map_card_orbit,
    ← Multiset.map_univ_val_equiv e', Multiset.map_map]
  refine Multiset.map_congr rfl fun d _ ↦ ?_
  rw [Function.comp_apply, ← natCard_rightCosetFiber_eq_natCard_orbit]

end TauCeti
