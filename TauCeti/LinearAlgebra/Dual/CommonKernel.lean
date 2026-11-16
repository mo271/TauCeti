/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Common kernels of families of linear functionals

Let `S` be a submodule of a vector space `V` and `ℓ : ι → Module.Dual K V` a family of linear
functionals whose common kernel `⨅ i, LinearMap.ker (ℓ i)` is contained in `S` (in particular, when
the common kernel equals `S`). Assembling the functionals into `LinearMap.pi ℓ : V →ₗ[K] (ι → K)`
identifies `V ⧸ ⨅ i, LinearMap.ker (ℓ i)` with a subspace of `ι → K`, which surjects onto `V ⧸ S`.

* Over any division ring `K`, if `ι` is finite then `V ⧸ S` is finite-dimensional of dimension at
  most `Fintype.card ι` (`Submodule.finrank_quotient_le_card_of_iInf_ker_le`).
* For an arbitrary index type `ι`, if `V ⧸ S` is finite-dimensional then its cardinal rank is at
  most `#ι` (`Submodule.lift_rank_quotient_le_lift_mk_of_iInf_ker_le`), and `(finrank K (V ⧸ S) :
  Cardinal) ≤ #ι` unconditionally (`Submodule.finrank_quotient_le_mk_of_iInf_ker_le`).
* When `Fintype.card ι` attains `finrank K (V ⧸ S)`, the common kernel equals `S` and
  `LinearMap.pi ℓ` is surjective (`Submodule.iInf_ker_eq_of_le_of_card_le_finrank`,
  `LinearMap.surjective_pi_of_iInf_ker_le_of_card_le_finrank`).
* Over a field `K`, a finite family of linear functionals has surjective evaluation map
  `LinearMap.pi ℓ` if and only if it is linearly independent
  (`LinearMap.surjective_pi_iff_linearIndependent`). Consequently a finite family cutting out `S`
  is linearly independent if and only if its cardinality equals `finrank K (V ⧸ S)`
  (`Submodule.linearIndependent_iff_card_eq_finrank_quotient_of_iInf_ker_eq`), and every subspace
  of finite codimension is cut out by `finrank K (V ⧸ S)` linearly independent functionals
  (`Submodule.exists_linearIndependent_dual_iInf_ker_eq`).

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Lemma 3.9 and Chapter 4.
-/

public section

namespace Submodule

open Module Cardinal

section DivisionRing

universe u₀ u w

variable {K : Type u₀} {V : Type u} {ι : Type w} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If a finite family of linear functionals has common kernel contained in `S`, then `V ⧸ S` is
finite-dimensional: `V ⧸ ⨅ i, ker (ℓ i)` embeds into `ι → K` and surjects onto `V ⧸ S`. -/
theorem finiteDimensional_quotient_of_iInf_ker_le [Finite ι] {S : Submodule K V}
    {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S) :
    FiniteDimensional K (V ⧸ S) := by
  let _ := Fintype.ofFinite ι
  have hker : LinearMap.ker (LinearMap.pi ℓ) ≤ S := by rwa [LinearMap.ker_pi]
  have : FiniteDimensional K (V ⧸ LinearMap.ker (LinearMap.pi ℓ)) :=
    Module.Finite.equiv (LinearMap.pi ℓ).quotKerEquivRange.symm
  exact Module.Finite.of_surjective (Submodule.factor hker) (Submodule.factor_surjective hker)

/-- Every finite family of linear functionals whose common kernel is contained in `S` has at least
`finrank K (V ⧸ S)` members. -/
theorem finrank_quotient_le_card_of_iInf_ker_le [Fintype ι] {S : Submodule K V}
    {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S) :
    finrank K (V ⧸ S) ≤ Fintype.card ι := by
  have hker : LinearMap.ker (LinearMap.pi ℓ) ≤ S := by rwa [LinearMap.ker_pi]
  have : FiniteDimensional K (V ⧸ LinearMap.ker (LinearMap.pi ℓ)) :=
    Module.Finite.equiv (LinearMap.pi ℓ).quotKerEquivRange.symm
  calc finrank K (V ⧸ S)
      ≤ finrank K (V ⧸ LinearMap.ker (LinearMap.pi ℓ)) :=
        LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hker)
    _ = finrank K (LinearMap.range (LinearMap.pi ℓ)) :=
        (LinearMap.pi ℓ).quotKerEquivRange.finrank_eq
    _ ≤ finrank K (ι → K) := Submodule.finrank_le _
    _ = Fintype.card ι := by simp

/-- Every finite family of linear functionals whose common kernel equals `S` has at least
`finrank K (V ⧸ S)` members. -/
theorem finrank_quotient_le_card_of_iInf_ker_eq [Fintype ι] {S : Submodule K V}
    {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) = S) :
    finrank K (V ⧸ S) ≤ Fintype.card ι :=
  finrank_quotient_le_card_of_iInf_ker_le hS.le

/-- For an arbitrary family of linear functionals whose common kernel is contained in `S`, the
`finrank` of `V ⧸ S` (viewed in `Cardinal`) is at most `#ι`. -/
theorem finrank_quotient_le_mk_of_iInf_ker_le {S : Submodule K V} {ℓ : ι → Module.Dual K V}
    (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S) :
    (finrank K (V ⧸ S) : Cardinal.{w}) ≤ #ι := by
  rcases finite_or_infinite ι with hfin | hinf
  · let _ := Fintype.ofFinite ι
    simpa only [mk_fintype, Nat.cast_le] using finrank_quotient_le_card_of_iInf_ker_le hS
  · exact natCast_lt_aleph0.le.trans (aleph0_le_mk ι)

/-- For an arbitrary family of linear functionals whose common kernel equals `S`, the `finrank` of
`V ⧸ S` (viewed in `Cardinal`) is at most `#ι`. -/
theorem finrank_quotient_le_mk_of_iInf_ker_eq {S : Submodule K V} {ℓ : ι → Module.Dual K V}
    (hS : (⨅ i, LinearMap.ker (ℓ i)) = S) :
    (finrank K (V ⧸ S) : Cardinal.{w}) ≤ #ι :=
  finrank_quotient_le_mk_of_iInf_ker_le hS.le

/-- **Cardinal bound for common kernels.** If `V ⧸ S` is finite-dimensional and an arbitrary family
`ℓ : ι → Module.Dual K V` has common kernel contained in `S`, then the cardinal rank of `V ⧸ S` is
at most `#ι` (up to universe lift). Finite-dimensionality of `V ⧸ S` cannot be dropped: on `ℕ → K`,
the coordinate projections have trivial common kernel, `#ℕ = ℵ₀`, and `rank K (ℕ → K) > ℵ₀`. -/
theorem lift_rank_quotient_le_lift_mk_of_iInf_ker_le {S : Submodule K V}
    [FiniteDimensional K (V ⧸ S)] {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S) :
    Cardinal.lift.{w} (Module.rank K (V ⧸ S)) ≤ Cardinal.lift.{u} #ι := by
  rw [← finrank_eq_rank K (V ⧸ S), lift_natCast]
  simpa only [lift_natCast] using lift_le.{u}.2 (finrank_quotient_le_mk_of_iInf_ker_le hS)

/-- If `V ⧸ S` is finite-dimensional and `⨅ i, ker (ℓ i) = S`, then
`Cardinal.lift (Module.rank K (V ⧸ S)) ≤ Cardinal.lift #ι`. -/
theorem lift_rank_quotient_le_lift_mk_of_iInf_ker_eq {S : Submodule K V}
    [FiniteDimensional K (V ⧸ S)] {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) = S) :
    Cardinal.lift.{w} (Module.rank K (V ⧸ S)) ≤ Cardinal.lift.{u} #ι :=
  lift_rank_quotient_le_lift_mk_of_iInf_ker_le hS.le

/-- Same-universe form of `Submodule.lift_rank_quotient_le_lift_mk_of_iInf_ker_le`. -/
theorem rank_quotient_le_mk_of_iInf_ker_le {ι : Type u} {S : Submodule K V}
    [FiniteDimensional K (V ⧸ S)] {ℓ : ι → Module.Dual K V}
    (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S) :
    Module.rank K (V ⧸ S) ≤ #ι := by
  simpa only [lift_id] using lift_rank_quotient_le_lift_mk_of_iInf_ker_le hS

/-- Same-universe form of `Submodule.lift_rank_quotient_le_lift_mk_of_iInf_ker_eq`. -/
theorem rank_quotient_le_mk_of_iInf_ker_eq {ι : Type u} {S : Submodule K V}
    [FiniteDimensional K (V ⧸ S)] {ℓ : ι → Module.Dual K V}
    (hS : (⨅ i, LinearMap.ker (ℓ i)) = S) :
    Module.rank K (V ⧸ S) ≤ #ι :=
  rank_quotient_le_mk_of_iInf_ker_le hS.le

/-- If `⨅ i, ker (ℓ i) ≤ S` and `Fintype.card ι ≤ finrank K (V ⧸ S)`, then equality holds: the
common kernel of `ℓ` is `S`. -/
theorem iInf_ker_eq_of_le_of_card_le_finrank [Fintype ι] {S : Submodule K V}
    {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S)
    (hcard : Fintype.card ι ≤ finrank K (V ⧸ S)) :
    (⨅ i, LinearMap.ker (ℓ i)) = S := by
  have hker : LinearMap.ker (LinearMap.pi ℓ) ≤ S := by rwa [LinearMap.ker_pi]
  have : FiniteDimensional K (V ⧸ LinearMap.ker (LinearMap.pi ℓ)) :=
    Module.Finite.equiv (LinearMap.pi ℓ).quotKerEquivRange.symm
  have : FiniteDimensional K (V ⧸ S) := finiteDimensional_quotient_of_iInf_ker_le hS
  have hle₁ : finrank K (V ⧸ S) ≤ finrank K (V ⧸ LinearMap.ker (LinearMap.pi ℓ)) :=
    LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hker)
  have hle₂ : finrank K (V ⧸ LinearMap.ker (LinearMap.pi ℓ)) ≤ Fintype.card ι := by
    calc finrank K (V ⧸ LinearMap.ker (LinearMap.pi ℓ))
        = finrank K (LinearMap.range (LinearMap.pi ℓ)) :=
          (LinearMap.pi ℓ).quotKerEquivRange.finrank_eq
      _ ≤ finrank K (ι → K) := Submodule.finrank_le _
      _ = Fintype.card ι := by simp
  -- Equal `finrank` makes the surjection `V ⧸ ker (pi ℓ) → V ⧸ S` injective, so `S ≤ ker (pi ℓ)`.
  have hinj : Function.Injective (Submodule.factor hker) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (le_antisymm hle₁ (hle₂.trans hcard)).symm).mpr (Submodule.factor_surjective hker)
  refine le_antisymm hS fun x hx ↦ ?_
  have hx0 : Submodule.factor hker (Submodule.Quotient.mk x) = 0 := by
    simp [(Submodule.Quotient.mk_eq_zero S).mpr hx]
  rw [← LinearMap.ker_pi, ← Submodule.Quotient.mk_eq_zero]
  exact hinj (hx0.trans (map_zero _).symm)

end DivisionRing

end Submodule

namespace LinearMap

open Module

section DivisionRing

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If `⨅ i, ker (ℓ i) ≤ S` and `Fintype.card ι ≤ finrank K (V ⧸ S)`, then the combined evaluation
map `LinearMap.pi ℓ : V →ₗ[K] (ι → K)` is surjective. -/
theorem surjective_pi_of_iInf_ker_le_of_card_le_finrank [Fintype ι] {S : Submodule K V}
    {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S)
    (hcard : Fintype.card ι ≤ finrank K (V ⧸ S)) :
    Function.Surjective (LinearMap.pi ℓ) := by
  have heq : LinearMap.ker (LinearMap.pi ℓ) = S := by
    rw [LinearMap.ker_pi]
    exact Submodule.iInf_ker_eq_of_le_of_card_le_finrank hS hcard
  have hle : finrank K (range (LinearMap.pi ℓ)) ≤ finrank K (ι → K) := Submodule.finrank_le _
  have hpi : finrank K (ι → K) = Fintype.card ι := by simp
  have hquot : finrank K (range (LinearMap.pi ℓ)) = finrank K (V ⧸ S) :=
    (LinearMap.pi ℓ).quotKerEquivRange.symm.finrank_eq.trans
      (Submodule.quotEquivOfEq _ _ heq).finrank_eq
  exact range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by omega))

end DivisionRing

section Field

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Duality for finite families of functionals.** Over a field, a finite family
`ℓ : ι → Module.Dual K V` is linearly independent if and only if the evaluation map
`LinearMap.pi ℓ : V →ₗ[K] (ι → K)` is surjective. The ambient space `V` need not be
finite-dimensional. -/
theorem surjective_pi_iff_linearIndependent [Finite ι] {ℓ : ι → Module.Dual K V} :
    Function.Surjective (LinearMap.pi ℓ) ↔ LinearIndependent K ℓ := by
  classical
  let _ := Fintype.ofFinite ι
  constructor
  · intro hsurj
    refine Fintype.linearIndependent_iff.mpr fun c hc j ↦ ?_
    obtain ⟨v, hv⟩ := hsurj (Pi.single j 1)
    have h := LinearMap.congr_fun hc v
    have hj (i : ι) : ℓ i v = (Pi.single j (1 : K) : ι → K) i := by
      simpa only [pi_apply] using congr_fun hv i
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, hj, Pi.single_apply]
      using h
  · intro hli
    by_contra hnsurj
    have hlt : range (LinearMap.pi ℓ) < ⊤ := lt_top_iff_ne_top.mpr (range_eq_top.not.mpr hnsurj)
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    -- Expand `φ : Dual K (ι → K)` in the standard basis `Pi.single i 1`; vanishing on
    -- `range (pi ℓ)` yields a linear relation among the `ℓ i`.
    let c : ι → K := fun i ↦ φ (Pi.single i 1)
    have hφ_eq (x : ι → K) : φ x = ∑ i, c i * x i := by
      conv_lhs => rw [← (Pi.basisFun K ι).sum_repr x, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Pi.basisFun_repr, Pi.basisFun_apply, map_smul, smul_eq_mul, mul_comm]
    have hc : ∑ i, c i • ℓ i = 0 := by
      ext v
      have hmem : φ (LinearMap.pi ℓ v) ∈ (range (LinearMap.pi ℓ)).map φ := ⟨_, ⟨v, rfl⟩, rfl⟩
      rw [hφ, Submodule.mem_bot, hφ_eq] at hmem
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply,
        pi_apply] using hmem
    have hc0 : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp hli c hc
    exact hφ0 <| ext fun x ↦ by simp [hφ_eq, hc0]

end Field

end LinearMap

namespace Submodule

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A finite family of linear functionals with `⨅ i, ker (ℓ i) ≤ S` and
`Fintype.card ι ≤ finrank K (V ⧸ S)` is linearly independent. -/
theorem linearIndependent_of_iInf_ker_le_of_card_le_finrank [Fintype ι] {S : Submodule K V}
    {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) ≤ S)
    (hcard : Fintype.card ι ≤ finrank K (V ⧸ S)) :
    LinearIndependent K ℓ :=
  LinearMap.surjective_pi_iff_linearIndependent.mp
    (LinearMap.surjective_pi_of_iInf_ker_le_of_card_le_finrank hS hcard)

/-- A finite family of linear functionals cutting out `S` and attaining the minimal size
`finrank K (V ⧸ S)` is linearly independent. -/
theorem linearIndependent_of_iInf_ker_eq_of_card_eq_finrank [Fintype ι] {S : Submodule K V}
    {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) = S)
    (hcard : Fintype.card ι = finrank K (V ⧸ S)) :
    LinearIndependent K ℓ :=
  linearIndependent_of_iInf_ker_le_of_card_le_finrank hS.le hcard.le

/-- If a linearly independent finite family of functionals has common kernel `S`, then `V ⧸ S` has
dimension `Fintype.card ι`. -/
theorem finrank_quotient_eq_card_of_iInf_ker_eq_of_linearIndependent [Fintype ι]
    {S : Submodule K V} {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) = S)
    (hli : LinearIndependent K ℓ) :
    finrank K (V ⧸ S) = Fintype.card ι := by
  have hsurj := LinearMap.surjective_pi_iff_linearIndependent.mpr hli
  have hker : LinearMap.ker (LinearMap.pi ℓ) = S := by rwa [LinearMap.ker_pi]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((LinearMap.pi ℓ).quotKerEquivOfSurjective hsurj)).finrank_eq.trans (by simp)

/-- A finite family of linear functionals with common kernel `S` is linearly independent if and
only if its cardinality equals `finrank K (V ⧸ S)`. -/
theorem linearIndependent_iff_card_eq_finrank_quotient_of_iInf_ker_eq [Fintype ι]
    {S : Submodule K V} {ℓ : ι → Module.Dual K V} (hS : (⨅ i, LinearMap.ker (ℓ i)) = S) :
    LinearIndependent K ℓ ↔ Fintype.card ι = finrank K (V ⧸ S) :=
  ⟨fun hli ↦ (finrank_quotient_eq_card_of_iInf_ker_eq_of_linearIndependent hS hli).symm,
    linearIndependent_of_iInf_ker_eq_of_card_eq_finrank hS⟩

/-- Every subspace `S` of finite codimension is the common kernel of `finrank K (V ⧸ S)` linearly
independent linear functionals, obtained by pulling back a dual basis of `V ⧸ S`. -/
theorem exists_linearIndependent_dual_iInf_ker_eq (S : Submodule K V)
    [FiniteDimensional K (V ⧸ S)] :
    ∃ ℓ : Fin (finrank K (V ⧸ S)) → Module.Dual K V,
      LinearIndependent K ℓ ∧ (⨅ i, LinearMap.ker (ℓ i)) = S := by
  let b := finBasis K (V ⧸ S)
  let ℓ : Fin (finrank K (V ⧸ S)) → Module.Dual K V := fun i ↦ b.dualBasis i ∘ₗ S.mkQ
  have hS : (⨅ i, LinearMap.ker (ℓ i)) = S := by
    ext x
    simp only [mem_iInf, LinearMap.mem_ker, ℓ, LinearMap.comp_apply, mkQ_apply]
    refine ⟨fun hx ↦ ?_, fun hx i ↦ by simp [(Submodule.Quotient.mk_eq_zero S).mpr hx]⟩
    rw [← Submodule.Quotient.mk_eq_zero S, ← b.sum_repr (Submodule.Quotient.mk x)]
    simp_rw [← Basis.dualBasis_apply, hx, zero_smul, Finset.sum_const_zero]
  exact ⟨ℓ, linearIndependent_of_iInf_ker_eq_of_card_eq_finrank hS (Fintype.card_fin _), hS⟩

end Submodule

end
