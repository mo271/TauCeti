/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.Analysis.Normed.Group.Seminorm

/-!
# Kernels, quotient descent, and sublinear quotient estimates for module seminorms

For a seminorm `p : Seminorm 𝕜 E` on a module `E` over a seminormed ring `𝕜`, the vectors on which
`p` vanishes form a submodule `p.ker : Submodule 𝕜 E`. On a seminormed space over a normed field,
`(normSeminorm 𝕜 E).ker` is Mathlib's `nullSubmodule 𝕜 E`, and `p.ker` is closed whenever `p` is
continuous.

Descending a seminorm to a quotient `E ⧸ S` takes two forms, with genuinely different scalar
assumptions:

* When `S ≤ p.ker`, `p` is constant on the cosets of `S` and descends directly to
  `p.liftQ S hS : Seminorm 𝕜 (E ⧸ S)` over any `SeminormedRing 𝕜`. Its kernel is
  `p.ker.map S.mkQ`, so descending across `p.ker` itself yields a separated seminorm with trivial
  kernel (`Seminorm.ker_liftQ_self`).
* For an arbitrary submodule `S : Submodule 𝕜 E`, the coset infimum defines a module seminorm
  `p.quotient S : Seminorm 𝕜 (E ⧸ S)` when `𝕜` is a `NormedField`. Over a general normed ring,
  coset infima need not be homogeneous: for `𝕜 = E = ℤ`, `S = 2ℤ`, and `p n = |(n : ℝ)|`, the odd
  coset `1 + 2ℤ` has infimum `1` while `2 • (1 + 2ℤ) = 2ℤ` has infimum `0 ≠ |2| * 1`. Over a
  normed field, invertibility of nonzero scalars gives homogeneity; `p.quotient S` agrees with
  `p.liftQ S hS` when `S ≤ p.ker` and recovers `normSeminorm 𝕜 (E ⧸ S)` for `normSeminorm 𝕜 E`.

Finally, any norm-bounded subadditive functional `ℓ : E → ℝ` that is nonpositive on `S` satisfies
`ℓ x ≤ M * ‖S.mkQ x‖`, and hence `ℓ x ≤ M * B` whenever `x` is approximated within norm `B` in
`E` by an element of `S` (assuming `0 ≤ M`). Specializing to `Seminorm` (or bundling an absolutely
homogeneous subadditive functional via `Seminorm.of`) gives the abstract sublinear Bramble–Hilbert
functional estimate, while a reverse approximation bound `∃ q ∈ S, ‖x - q‖ ≤ C * p x` gives the
quotient-norm upper bound `‖z‖ ≤ C * p.liftQ S hS z` of Deny–Lions type.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966], Chapter I, §2 and Chapter II, §4.
* J. H. Bramble, S. R. Hilbert, *Estimation of linear functionals on Sobolev spaces with
  application to Fourier transforms and spline interpolation*, SIAM J. Numer. Anal. 7 (1970),
  Theorem 2.
* J. Deny, J.-L. Lions, *Les espaces du type de Beppo Levi*, Ann. Inst. Fourier 5 (1954),
  Chapter III, §2.
-/

public section

open Set
open scoped NNReal

namespace Seminorm

section Ker

variable {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The submodule of vectors on which a module seminorm vanishes. -/
def ker (p : Seminorm 𝕜 E) : Submodule 𝕜 E where
  carrier := {x : E | p x = 0}
  add_mem' {x y} (hx : p x = 0) (hy : p y = 0) :=
    le_antisymm ((map_add_le_add p x y).trans_eq (by rw [hx, hy, add_zero])) (apply_nonneg p _)
  zero_mem' := map_zero p
  smul_mem' c x (hx : p x = 0) := (map_smul_eq_mul p c x).trans (by rw [hx, mul_zero])

@[simp]
theorem mem_ker {p : Seminorm 𝕜 E} {x : E} : x ∈ p.ker ↔ p x = 0 :=
  (Iff.rfl)

@[simp]
theorem coe_ker (p : Seminorm 𝕜 E) : (p.ker : Set E) = {x : E | p x = 0} :=
  (rfl)

@[simp]
theorem toAddSubgroup_ker (p : Seminorm 𝕜 E) :
    p.ker.toAddSubgroup = p.toAddGroupSeminorm.ker := by
  ext x
  exact AddGroupSeminorm.mem_ker.symm

@[simp]
theorem ker_zero : (0 : Seminorm 𝕜 E).ker = ⊤ := by
  ext x
  simp

@[simp]
theorem ker_add (p q : Seminorm 𝕜 E) : (p + q).ker = p.ker ⊓ q.ker := by
  ext x
  simp only [mem_ker, add_apply, Submodule.mem_inf]
  exact add_eq_zero_iff_of_nonneg (apply_nonneg p x) (apply_nonneg q x)

@[simp]
theorem ker_sup (p q : Seminorm 𝕜 E) : (p ⊔ q).ker = p.ker ⊓ q.ker := by
  ext x
  simp only [mem_ker, sup_apply, Submodule.mem_inf]
  exact ⟨fun h ↦ ⟨le_antisymm (le_sup_left.trans_eq h) (apply_nonneg p x),
    le_antisymm (le_sup_right.trans_eq h) (apply_nonneg q x)⟩,
    fun ⟨hp, hq⟩ ↦ by rw [hp, hq, sup_idem]⟩

theorem ker_smul_of_ne_zero {r : ℝ≥0} (hr : r ≠ 0) (p : Seminorm 𝕜 E) :
    (r • p).ker = p.ker := by
  ext x
  simp [NNReal.smul_def, hr]

theorem antitone_ker : Antitone (ker : Seminorm 𝕜 E → Submodule 𝕜 E) :=
  fun p _ hpq _ hx ↦
    mem_ker.mpr <| le_antisymm ((hpq _).trans_eq (mem_ker.mp hx)) (apply_nonneg p _)

/-- Adding a vector in `p.ker` on the right leaves `p` unchanged. -/
theorem map_add_eq_left_of_mem_ker {p : Seminorm 𝕜 E} (x : E) {k : E} (hk : k ∈ p.ker) :
    p (x + k) = p x :=
  p.toAddGroupSeminorm.map_add_eq_left_of_mem_ker x (AddGroupSeminorm.mem_ker.mpr hk)

/-- Adding a vector in `p.ker` on the left leaves `p` unchanged. -/
theorem map_add_eq_right_of_mem_ker {p : Seminorm 𝕜 E} {k : E} (hk : k ∈ p.ker) (x : E) :
    p (k + x) = p x :=
  p.toAddGroupSeminorm.map_add_eq_right_of_mem_ker (AddGroupSeminorm.mem_ker.mpr hk) x

/-- Subtracting a vector in `p.ker` leaves `p` unchanged. -/
theorem map_sub_eq_left_of_mem_ker {p : Seminorm 𝕜 E} (x : E) {k : E} (hk : k ∈ p.ker) :
    p (x - k) = p x :=
  p.toAddGroupSeminorm.map_sub_eq_left_of_mem_ker x (AddGroupSeminorm.mem_ker.mpr hk)

/-- A submodule `S` lies in `p.ker` if and only if `p` is invariant under adding vectors in `S`. -/
theorem le_ker_iff_forall_map_add_eq {p : Seminorm 𝕜 E} {S : Submodule 𝕜 E} :
    S ≤ p.ker ↔ ∀ x : E, ∀ s ∈ S, p (x + s) = p x := by
  rw [← Submodule.toAddSubgroup_le, toAddSubgroup_ker]
  exact p.toAddGroupSeminorm.le_ker_iff_forall_map_add_eq

/-- A submodule `S` lies in `p.ker` if and only if `p` is invariant under subtracting vectors in
`S`. -/
theorem le_ker_iff_forall_map_sub_eq {p : Seminorm 𝕜 E} {S : Submodule 𝕜 E} :
    S ≤ p.ker ↔ ∀ x : E, ∀ s ∈ S, p (x - s) = p x := by
  rw [← Submodule.toAddSubgroup_le, toAddSubgroup_ker]
  exact p.toAddGroupSeminorm.le_ker_iff_forall_map_sub_eq

/-- The kernel of a continuous seminorm is a closed subspace. -/
theorem isClosed_ker [TopologicalSpace E] {p : Seminorm 𝕜 E} (hp : Continuous p) :
    IsClosed (p.ker : Set E) := by
  rw [coe_ker]
  exact isClosed_singleton.preimage hp

end Ker

section KerComp

variable {𝕜 𝕜₂ E F : Type*} [SeminormedRing 𝕜] [SeminormedRing 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜₂ F]

@[simp]
theorem ker_comp (p : Seminorm 𝕜₂ F) (f : E →ₛₗ[σ] F) :
    (p.comp f).ker = p.ker.comap f :=
  (rfl)

end KerComp

section KerNorm

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On a seminormed space, the kernel of `normSeminorm 𝕜 E` is Mathlib's `nullSubmodule 𝕜 E`. -/
@[simp]
theorem ker_normSeminorm : (normSeminorm 𝕜 E).ker = nullSubmodule 𝕜 E := by
  ext x
  simp [mem_nullSubmodule_iff]

end KerNorm

section LiftQ

variable {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

private theorem toAddSubgroup_le_ker {p : Seminorm 𝕜 E} {S : Submodule 𝕜 E} (hS : S ≤ p.ker) :
    S.toAddSubgroup ≤ p.toAddGroupSeminorm.ker :=
  fun _ hx ↦ AddGroupSeminorm.mem_ker.mpr (hS hx)

/-- Descend a module seminorm `p` across a submodule `S` contained in its kernel. -/
def liftQ (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker) : Seminorm 𝕜 (E ⧸ S) where
  toFun z := Quotient.liftOn' z p fun x y hxy ↦ by
    have hmem : -x + y ∈ p.ker := hS (QuotientAddGroup.leftRel_apply.mp hxy)
    simpa only [add_neg_cancel_left] using (map_add_eq_left_of_mem_ker x hmem).symm
  map_zero' := map_zero p
  add_le' z w := by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective z
    obtain ⟨y, rfl⟩ := S.mkQ_surjective w
    exact map_add_le_add p x y
  neg' z := by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective z
    exact map_neg_eq_map p x
  smul' a z := by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective z
    exact map_smul_eq_mul p a x

@[simp]
theorem liftQ_mk (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker) (x : E) :
    p.liftQ S hS (Submodule.Quotient.mk x) = p x :=
  (rfl)

theorem liftQ_mkQ (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker) (x : E) :
    p.liftQ S hS (S.mkQ x) = p x :=
  (rfl)

@[simp]
theorem toAddGroupSeminorm_liftQ (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker) :
    (p.liftQ S hS).toAddGroupSeminorm = p.toAddGroupSeminorm.liftQ S.toAddSubgroup
      (fun _ hx ↦ AddGroupSeminorm.mem_ker.mpr (mem_ker.mp (hS hx))) := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact (p.liftQ_mk S hS x).trans (AddGroupSeminorm.liftQ_mk _ S.toAddSubgroup _ x).symm

@[simp]
theorem comp_mkQ_liftQ (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker) :
    (p.liftQ S hS).comp S.mkQ = p :=
  ext fun _ ↦ rfl

@[simp]
theorem liftQ_comp_mkQ (S : Submodule 𝕜 E) (q : Seminorm 𝕜 (E ⧸ S))
    (hS : S ≤ (q.comp S.mkQ).ker := fun x hx ↦ by
      simp [(Submodule.Quotient.mk_eq_zero S).mpr hx]) :
    (q.comp S.mkQ).liftQ S hS = q := by
  ext z
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  exact liftQ_mkQ _ S hS x

theorem eq_liftQ_iff {p : Seminorm 𝕜 E} {S : Submodule 𝕜 E} {hS : S ≤ p.ker}
    {q : Seminorm 𝕜 (E ⧸ S)} :
    q = p.liftQ S hS ↔ q.comp S.mkQ = p := by
  refine ⟨fun h ↦ h ▸ comp_mkQ_liftQ p S hS, fun h ↦ ?_⟩
  subst h
  exact (liftQ_comp_mkQ S q hS).symm

theorem liftQ_mono {p q : Seminorm 𝕜 E} {S : Submodule 𝕜 E} {hp : S ≤ p.ker} {hq : S ≤ q.ker}
    (hpq : p ≤ q) :
    p.liftQ S hp ≤ q.liftQ S hq := by
  intro z
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  exact hpq x

@[simp]
theorem liftQ_zero (S : Submodule 𝕜 E) (hS : S ≤ (0 : Seminorm 𝕜 E).ker := by simp) :
    (0 : Seminorm 𝕜 E).liftQ S hS = 0 := by
  ext z
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  simp

theorem liftQ_add (p q : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hp : S ≤ p.ker) (hq : S ≤ q.ker) :
    (p + q).liftQ S (ker_add p q ▸ le_inf hp hq) = p.liftQ S hp + q.liftQ S hq := by
  ext z
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  simp

theorem liftQ_sup (p q : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hp : S ≤ p.ker) (hq : S ≤ q.ker) :
    (p ⊔ q).liftQ S (ker_sup p q ▸ le_inf hp hq) = p.liftQ S hp ⊔ q.liftQ S hq := by
  ext z
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  simp

theorem liftQ_smul (r : ℝ≥0) (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hp : S ≤ p.ker)
    (hrp : S ≤ (r • p).ker := fun x hx ↦ by
      simp [mem_ker.mp (hp hx)]) :
    (r • p).liftQ S hrp = r • p.liftQ S hp := by
  ext z
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  simp

theorem ker_liftQ (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker) :
    (p.liftQ S hS).ker = p.ker.map S.mkQ := by
  ext z
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  simp only [mem_ker, liftQ_mkQ, Submodule.mem_map]
  refine ⟨fun hx ↦ ⟨x, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, hyx⟩
  have hsub : y - x ∈ p.ker := hS ((Submodule.Quotient.eq S).mp hyx)
  simpa only [sub_sub_cancel, mem_ker.mp hy] using map_sub_eq_left_of_mem_ker y hsub

@[simp]
theorem ker_liftQ_self (p : Seminorm 𝕜 E) :
    (p.liftQ p.ker le_rfl).ker = ⊥ := by
  ext z
  obtain ⟨x, rfl⟩ := p.ker.mkQ_surjective z
  simp [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]

/-- Descending `p` across its full kernel `p.ker` yields a separated seminorm on `E ⧸ p.ker`. -/
@[simp]
theorem liftQ_self_eq_zero_iff (p : Seminorm 𝕜 E) (z : E ⧸ p.ker) :
    p.liftQ p.ker le_rfl z = 0 ↔ z = 0 := by
  rw [← mem_ker, ker_liftQ_self, Submodule.mem_bot]

end LiftQ

section Quotient

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

private theorem quotient_smul_le (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (a : 𝕜) (z : E ⧸ S) :
    p.toAddGroupSeminorm.quotient S.toAddSubgroup (a • z) ≤
      ‖a‖ * p.toAddGroupSeminorm.quotient S.toAddSubgroup z := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_smul, norm_zero, zero_mul]
    exact (map_zero (p.toAddGroupSeminorm.quotient S.toAddSubgroup)).le
  · have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    refine (div_le_iff₀' hpos).mp (AddGroupSeminorm.le_quotient_iff.mpr fun m hm ↦ ?_)
    rw [div_le_iff₀' hpos]
    have hsmul : ‖a‖ * p.toAddGroupSeminorm m = p.toAddGroupSeminorm (a • m) :=
      (map_smul_eq_mul p a m).symm
    rw [hsmul]
    have hmk : ((a • m : E) : E ⧸ S.toAddSubgroup) = a • z := by
      rw [← hm]
      exact Submodule.Quotient.mk_smul S a m
    exact hmk ▸ p.toAddGroupSeminorm.quotient_mk_le S.toAddSubgroup (a • m)

private theorem quotient_smul_eq (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (a : 𝕜) (z : E ⧸ S) :
    p.toAddGroupSeminorm.quotient S.toAddSubgroup (a • z) =
      ‖a‖ * p.toAddGroupSeminorm.quotient S.toAddSubgroup z := by
  refine le_antisymm (quotient_smul_le p S a z) ?_
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_smul, norm_zero, zero_mul]
    exact apply_nonneg (p.toAddGroupSeminorm.quotient S.toAddSubgroup) _
  · have hle := mul_le_mul_of_nonneg_left (quotient_smul_le p S a⁻¹ (a • z)) (norm_nonneg a)
    have heq : p.toAddGroupSeminorm.quotient S.toAddSubgroup (a⁻¹ • (a • z)) =
        p.toAddGroupSeminorm.quotient S.toAddSubgroup z :=
      congrArg (p.toAddGroupSeminorm.quotient S.toAddSubgroup) (inv_smul_smul₀ ha z)
    exact ((congrArg (‖a‖ * ·) heq).symm.trans_le hle).trans_eq (by
      rw [← mul_assoc, ← norm_mul, mul_inv_cancel₀ ha, norm_one, one_mul])

/-- The quotient seminorm on `E ⧸ S` induced by a seminorm `p` and an arbitrary submodule `S` over
a normed field `𝕜`, defined on each class as the infimum of `p` over its representatives in `E`. -/
noncomputable def quotient (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) : Seminorm 𝕜 (E ⧸ S) where
  __ := p.toAddGroupSeminorm.quotient S.toAddSubgroup
  smul' := quotient_smul_eq p S

@[simp]
theorem toAddGroupSeminorm_quotient (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) :
    (p.quotient S).toAddGroupSeminorm = p.toAddGroupSeminorm.quotient S.toAddSubgroup :=
  (rfl)

theorem le_quotient_iff {p : Seminorm 𝕜 E} {S : Submodule 𝕜 E} {z : E ⧸ S} {r : ℝ} :
    r ≤ p.quotient S z ↔ ∀ m : E, S.mkQ m = z → r ≤ p m :=
  AddGroupSeminorm.le_quotient_iff

theorem quotient_lt_iff {p : Seminorm 𝕜 E} {S : Submodule 𝕜 E} {z : E ⧸ S} {r : ℝ} :
    p.quotient S z < r ↔ ∃ m : E, S.mkQ m = z ∧ p m < r :=
  AddGroupSeminorm.quotient_lt_iff

theorem quotient_mk_le (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (x : E) :
    p.quotient S (Submodule.Quotient.mk x) ≤ p x :=
  p.toAddGroupSeminorm.quotient_mk_le S.toAddSubgroup x

theorem quotient_mkQ_le (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (x : E) :
    p.quotient S (S.mkQ x) ≤ p x :=
  p.toAddGroupSeminorm.quotient_mk_le S.toAddSubgroup x

theorem exists_mk_eq_and_lt (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (z : E ⧸ S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : E, S.mkQ m = z ∧ p m < p.quotient S z + ε :=
  p.toAddGroupSeminorm.exists_mk_eq_and_lt S.toAddSubgroup z hε

theorem quotient_mkQ_eq_iInf_add (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (x : E) :
    p.quotient S (S.mkQ x) = ⨅ s : S, p (x + s) :=
  p.toAddGroupSeminorm.quotient_mk_eq_iInf_add S.toAddSubgroup x

theorem quotient_mkQ_eq_iInf_sub (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (x : E) :
    p.quotient S (S.mkQ x) = ⨅ s : S, p (x - s) :=
  p.toAddGroupSeminorm.quotient_mk_eq_iInf_sub S.toAddSubgroup x

theorem quotient_mono {p q : Seminorm 𝕜 E} (S : Submodule 𝕜 E) (hpq : p ≤ q) :
    p.quotient S ≤ q.quotient S :=
  p.toAddGroupSeminorm.quotient_mono S.toAddSubgroup hpq

theorem quotient_anti (p : Seminorm 𝕜 E) {S₁ S₂ : Submodule 𝕜 E} (hS : S₁ ≤ S₂) (x : E) :
    p.quotient S₂ (S₂.mkQ x) ≤ p.quotient S₁ (S₁.mkQ x) :=
  p.toAddGroupSeminorm.quotient_anti hS x

theorem quotient_eq_liftQ (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker) :
    p.quotient S = p.liftQ S hS := by
  ext z
  have h := DFunLike.congr_fun
    (p.toAddGroupSeminorm.quotient_eq_liftQ S.toAddSubgroup (toAddSubgroup_le_ker hS)) z
  exact h.trans (DFunLike.congr_fun (p.toAddGroupSeminorm_liftQ S hS).symm z)

@[simp]
theorem quotient_bot (p : Seminorm 𝕜 E) (x : E) :
    p.quotient ⊥ (Submodule.Quotient.mk x) = p x := by
  rw [quotient_eq_liftQ p ⊥ bot_le, liftQ_mk]

@[simp]
theorem quotient_top (p : Seminorm 𝕜 E) : p.quotient ⊤ = 0 := by
  ext z
  refine le_antisymm ?_ (apply_nonneg _ _)
  have hmk : (⊤ : Submodule 𝕜 E).mkQ 0 = z := Subsingleton.elim _ _
  exact (hmk ▸ p.quotient_mkQ_le ⊤ 0).trans_eq (map_zero p)

end Quotient

section QuotientNorm

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On a seminormed space, the quotient seminorm of `normSeminorm 𝕜 E` is
`normSeminorm 𝕜 (E ⧸ S)`. -/
@[simp]
theorem quotient_normSeminorm (S : Submodule 𝕜 E) :
    (normSeminorm 𝕜 E).quotient S = normSeminorm 𝕜 (E ⧸ S) := by
  ext z
  exact DFunLike.congr_fun (AddGroupSeminorm.quotient_normAddGroupSeminorm S.toAddSubgroup) z

end QuotientNorm

section NormBounds

variable {𝕜 E : Type*} [SeminormedRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- When `S ≤ p.ker`, a norm bound `p x ≤ M * ‖x‖` descends to `(p.liftQ S hS) z ≤ M * ‖z‖` on
`E ⧸ S` without requiring `0 ≤ M`. -/
theorem liftQ_le_mul_norm (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker)
    {M : ℝ} (hM : ∀ x : E, p x ≤ M * ‖x‖) (z : E ⧸ S) :
    p.liftQ S hS z ≤ M * ‖z‖ := by
  have heq := DFunLike.congr_fun (p.toAddGroupSeminorm_liftQ S hS) z
  exact (p.toAddGroupSeminorm.liftQ_le_mul_norm S.toAddSubgroup (toAddSubgroup_le_ker hS) hM
    z).trans_eq' heq.symm

/-- A seminorm vanishing on `S` and bounded by `M * ‖·‖` is bounded at every `x` by `M` times the
quotient norm `‖S.mkQ x‖`, without requiring `0 ≤ M`. -/
theorem apply_le_mul_norm_mkQ (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker)
    {M : ℝ} (hM : ∀ y : E, p y ≤ M * ‖y‖) (x : E) :
    p x ≤ M * ‖S.mkQ x‖ := by
  simpa only [liftQ_mkQ] using p.liftQ_le_mul_norm S hS hM (S.mkQ x)

/-- Distance-to-subspace form of `Seminorm.apply_le_mul_norm_mkQ`. -/
theorem apply_le_mul_infDist (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker)
    {M : ℝ} (hM : ∀ y : E, p y ≤ M * ‖y‖) (x : E) :
    p x ≤ M * Metric.infDist x (S : Set E) := by
  rw [← S.coe_toAddSubgroup, ← QuotientAddGroup.norm_mk]
  exact p.apply_le_mul_norm_mkQ S hS hM x

/-- **Sublinear Bramble–Hilbert estimate (quotient-norm form).** If `p` vanishes on `S` and
satisfies `p y ≤ M * ‖y‖` with `0 ≤ M`, then any bound `‖S.mkQ x‖ ≤ B` implies `p x ≤ M * B`. -/
theorem apply_le_mul_of_norm_mkQ_le (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≤ p.ker)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y : E, p y ≤ M * ‖y‖) {x : E} {B : ℝ} (hx : ‖S.mkQ x‖ ≤ B) :
    p x ≤ M * B :=
  (p.apply_le_mul_norm_mkQ S hS hM x).trans (mul_le_mul_of_nonneg_left hx hM0)

/-- **Sublinear Bramble–Hilbert estimate (approximation form).** If `p` vanishes on `S` and
satisfies `p y ≤ M * ‖y‖` with `0 ≤ M`, and `x` is approximated within norm `B` by an element of
`S`, then `p x ≤ M * B`. -/
theorem apply_le_mul_of_exists_mem_norm_sub_le (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E)
    (hS : S ≤ p.ker) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y : E, p y ≤ M * ‖y‖)
    {x : E} {B : ℝ} (hx : ∃ q ∈ S, ‖x - q‖ ≤ B) :
    p x ≤ M * B := by
  obtain ⟨q, hq, hxq⟩ := hx
  have hmk : ‖S.mkQ x‖ ≤ B := by
    have heq : S.mkQ (x - q) = S.mkQ x := by
      rw [map_sub, S.mkQ_apply q, (Submodule.Quotient.mk_eq_zero S).mpr hq, sub_zero]
    rw [← heq]
    exact (Submodule.Quotient.norm_mk_le S (x - q)).trans hxq
  exact p.apply_le_mul_of_norm_mkQ_le S hS hM0 hM hmk

/-- If every `x : E` admits an approximant `q ∈ S` with `‖x - q‖ ≤ C * p x` and `S ≤ p.ker`, then
the quotient norm on `E ⧸ S` is bounded by `C` times the descended seminorm `p.liftQ S hS`,
without requiring `0 ≤ C`. -/
theorem norm_le_mul_liftQ_of_exists_mem_norm_sub_le (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E)
    (hS : S ≤ p.ker) {C : ℝ} (hC : ∀ x : E, ∃ q ∈ S, ‖x - q‖ ≤ C * p x) (z : E ⧸ S) :
    ‖z‖ ≤ C * p.liftQ S hS z := by
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  obtain ⟨q, hq, hxq⟩ := hC x
  have heq : S.mkQ (x - q) = S.mkQ x := by
    rw [map_sub, S.mkQ_apply q, (Submodule.Quotient.mk_eq_zero S).mpr hq, sub_zero]
  rw [liftQ_mkQ, ← heq]
  exact (Submodule.Quotient.norm_mk_le S (x - q)).trans hxq

end NormBounds

section QuotientNormBounds

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- Over a normed field, a norm bound `p x ≤ M * ‖x‖` passes to the quotient seminorm
`(p.quotient S) z ≤ M * ‖z‖` for any submodule `S`, without requiring `0 ≤ M`. -/
theorem quotient_le_mul_norm (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E)
    {M : ℝ} (hM : ∀ x : E, p x ≤ M * ‖x‖) (z : E ⧸ S) :
    p.quotient S z ≤ M * ‖z‖ :=
  p.toAddGroupSeminorm.quotient_le_mul_norm S.toAddSubgroup hM z

end QuotientNormBounds

end Seminorm

namespace Submodule

variable {R E : Type*} [Ring R] [SeminormedAddCommGroup E] [Module R E]

/-- **Unbundled subadditive quotient estimate.** A subadditive functional `ℓ : E → ℝ` that is
nonpositive on `S` and satisfies `ℓ y ≤ M * ‖y‖` satisfies `ℓ x ≤ M * ‖S.mkQ x‖`, without
requiring `0 ≤ M` or scalar homogeneity of `ℓ`. This simultaneously covers sublinear functionals
and bounded real-linear functionals annihilating `S`. -/
theorem apply_le_mul_norm_mkQ_of_add_le (S : Submodule R E) {ℓ : E → ℝ}
    (hadd : ∀ x y : E, ℓ (x + y) ≤ ℓ x + ℓ y) (hS : ∀ q ∈ S, ℓ q ≤ 0)
    {M : ℝ} (hM : ∀ y : E, ℓ y ≤ M * ‖y‖) (x : E) :
    ℓ x ≤ M * ‖S.mkQ x‖ := by
  have h00 : ℓ 0 ≤ ℓ 0 + ℓ 0 := by simpa only [add_zero] using hadd 0 0
  have h0 : ℓ 0 = 0 := le_antisymm (hS 0 S.zero_mem) (by linarith)
  rcases le_or_gt 0 M with hM0 | hMneg
  · rcases eq_or_lt_of_le hM0 with rfl | hMpos
    · simpa using hM x
    · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      obtain ⟨m, hm, hmnorm⟩ := QuotientAddGroup.exists_norm_mk_lt (S.mkQ x) (div_pos hε hMpos)
      have hsub : x - m ∈ S := (Submodule.Quotient.eq S).mp hm.symm
      calc ℓ x = ℓ (m + (x - m)) := by rw [add_sub_cancel]
        _ ≤ ℓ m + ℓ (x - m) := hadd m (x - m)
        _ ≤ M * ‖m‖ + 0 := add_le_add (hM m) (hS _ hsub)
        _ ≤ M * (‖S.mkQ x‖ + ε / M) := by
          rw [add_zero]
          exact mul_le_mul_of_nonneg_left hmnorm.le hM0
        _ = M * ‖S.mkQ x‖ + ε := by rw [mul_add, mul_div_cancel₀ _ hMpos.ne']
  · have hnorm0 (y : E) : ‖y‖ = 0 := by
      by_contra hy
      have hypos : 0 < ‖y‖ := (norm_nonneg y).lt_of_ne' hy
      have hsum : 0 ≤ ℓ y + ℓ (-y) := by
        simpa only [add_neg_cancel, h0] using hadd y (-y)
      have hneg : M * ‖y‖ + M * ‖-y‖ < 0 := by
        rw [norm_neg, ← two_mul, ← mul_assoc]
        exact mul_neg_of_neg_of_pos (by linarith) hypos
      linarith [hM y, hM (-y)]
    have hz0 : ‖S.mkQ x‖ = 0 :=
      le_antisymm ((QuotientAddGroup.norm_mk_le_norm (S := S.toAddSubgroup) (m := x)).trans_eq
        (hnorm0 x)) (norm_nonneg _)
    simpa only [hz0, mul_zero, hnorm0 x] using hM x

/-- **Unbundled subadditive Bramble–Hilbert estimate.** If `ℓ : E → ℝ` is subadditive, nonpositive
on `S`, and bounded by `M * ‖·‖` with `0 ≤ M`, then `∃ q ∈ S, ‖x - q‖ ≤ B` implies
`ℓ x ≤ M * B`. -/
theorem apply_le_mul_of_add_le_of_exists_mem_norm_sub_le (S : Submodule R E) {ℓ : E → ℝ}
    (hadd : ∀ x y : E, ℓ (x + y) ≤ ℓ x + ℓ y) (hS : ∀ q ∈ S, ℓ q ≤ 0)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y : E, ℓ y ≤ M * ‖y‖)
    {x : E} {B : ℝ} (hx : ∃ q ∈ S, ‖x - q‖ ≤ B) :
    ℓ x ≤ M * B := by
  obtain ⟨q, hq, hxq⟩ := hx
  calc ℓ x = ℓ ((x - q) + q) := by rw [sub_add_cancel]
    _ ≤ ℓ (x - q) + ℓ q := hadd (x - q) q
    _ ≤ M * ‖x - q‖ + 0 := add_le_add (hM (x - q)) (hS q hq)
    _ ≤ M * B := by
      rw [add_zero]
      exact mul_le_mul_of_nonneg_left hxq hM0

end Submodule
