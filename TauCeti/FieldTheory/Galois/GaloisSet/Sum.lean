/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Basic
public import Mathlib.Algebra.Group.Action.Sum
import Mathlib.GroupTheory.Perm.Finite
import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Disjoint unions of labelled Galois sets

Given a bijection `e : Fin m ⊕ Fin n ≃ Fin k`, two labelled Galois sets `ρ : GaloisSet K m` and
`τ : GaloisSet K n` combine into a labelled Galois set `TauCeti.GaloisSet.sumCongr e ρ τ` of size
`k` whose kernel is `ρ.val.ker ⊓ τ.val.ker`.

Conversely, a labelled Galois set of size `k` arises in this way from a unique pair `(ρ, τ)`
precisely when every Galois automorphism preserves the image `Set.range (e ∘ Sum.inl)` of the left
summand (`TauCeti.GaloisSet.sumCongrEquiv`). When `i : Fin m` is fixed, the actions for which the
orbit of `e (Sum.inl i)` equals `Set.range (e ∘ Sum.inl)` correspond to pairs `(ρ, τ)` with `ρ`
transitive (`TauCeti.GaloisSet.sumCongrTransitiveEquiv`). Splitting off the orbit of a chosen label
along this equivalence is the inductive step that reduces mass sums over arbitrary labelled Galois
sets to transitive ones.

## Main definitions and results

* `TauCeti.GaloisSet.sumCongr`: disjoint union of two labelled Galois sets along a bijection
  `Fin m ⊕ Fin n ≃ Fin k`.
* `TauCeti.GaloisSet.sumCongrEquiv`: Galois sets preserving `Set.range (e ∘ Sum.inl)` correspond to
  pairs `(ρ, τ)` of Galois sets on the summands.
* `TauCeti.GaloisSet.stabilizer_sumCongr_inl`, `TauCeti.GaloisSet.stabilizer_sumCongr_inr`, and
  `TauCeti.GaloisSet.orbit_sumCongr_inl`: stabilizers and orbits in `sumCongr e ρ τ`.
* `TauCeti.GaloisSet.sumCongrTransitiveEquiv`: Galois sets in which the orbit of `e (Sum.inl i)` is
  `Set.range (e ∘ Sum.inl)` correspond to pairs `(ρ, τ)` with `ρ` transitive.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

variable {K : Type*} [Field K] {m n k : ℕ}

/-- The disjoint union of two labelled Galois sets of sizes `m` and `n`, transported to `Fin k`
along a bijection `e : Fin m ⊕ Fin n ≃ Fin k`. -/
def sumCongr (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n) : GaloisSet K k :=
  ⟨e.permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin m) (Fin n)).comp (ρ.val.prod τ.val)), by
    rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
      MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
      MonoidHom.ker_prod, Subgroup.coe_inf]
    exact ρ.property.inter τ.property⟩

/-- `sumCongr e ρ τ` acts by transporting `Equiv.sumCongr (ρ.val σ) (τ.val σ)` along `e`. -/
@[simp]
theorem sumCongr_val_apply (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n)
    (σ : Gal(SeparableClosure K/K)) (l : Fin k) :
    (sumCongr e ρ τ).val σ l = e (Equiv.sumCongr (ρ.val σ) (τ.val σ) (e.symm l)) :=
  (rfl)

/-- On the left summand `e (Sum.inl i)`, `sumCongr e ρ τ` acts through `ρ`. -/
theorem sumCongr_val_apply_inl (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n)
    (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (sumCongr e ρ τ).val σ (e (Sum.inl i)) = e (Sum.inl (ρ.val σ i)) := by
  simp

/-- On the right summand `e (Sum.inr j)`, `sumCongr e ρ τ` acts through `τ`. -/
theorem sumCongr_val_apply_inr (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n)
    (σ : Gal(SeparableClosure K/K)) (j : Fin n) :
    (sumCongr e ρ τ).val σ (e (Sum.inr j)) = e (Sum.inr (τ.val σ j)) := by
  simp

/-- The kernel of `sumCongr e ρ τ` is the intersection of the kernels of `ρ` and `τ`. -/
@[simp]
theorem ker_sumCongr (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n) :
    (sumCongr e ρ τ).val.ker = ρ.val.ker ⊓ τ.val.ker := by
  dsimp [sumCongr]
  rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
    MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
    MonoidHom.ker_prod]

/-- The bijection `e : Fin m ⊕ Fin n ≃ Fin k` intertwines the action of `sumCongr e ρ τ` with the
sum of the actions of `ρ` and `τ`. -/
theorem sumCongr_smul_apply (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n)
    (σ : Gal(SeparableClosure K/K)) (x : Fin m ⊕ Fin n) :
    letI := ρ.mulAction
    letI := τ.mulAction
    letI := (sumCongr e ρ τ).mulAction
    σ • e x = e (σ • x) := by
  let := ρ.mulAction
  let := τ.mulAction
  let := (sumCongr e ρ τ).mulAction
  rcases x with i | j <;> simp

/-- A pair of labelled Galois sets is determined by its disjoint union along `e`. -/
theorem sumCongr_injective (e : Fin m ⊕ Fin n ≃ Fin k) :
    Function.Injective (fun p : GaloisSet K m × GaloisSet K n ↦ sumCongr e p.1 p.2) := by
  rintro ⟨ρ₁, τ₁⟩ ⟨ρ₂, τ₂⟩ h
  refine Prod.ext (ext fun σ i ↦ ?_) (ext fun σ j ↦ ?_)
  · have hi := congrArg (fun μ : GaloisSet K k ↦ μ.val σ (e (Sum.inl i))) h
    exact Sum.inl_injective (e.injective (by simpa using hi))
  · have hj := congrArg (fun μ : GaloisSet K k ↦ μ.val σ (e (Sum.inr j))) h
    exact Sum.inr_injective (e.injective (by simpa using hj))

/-- Every Galois automorphism preserves the left summand `Set.range (e ∘ Sum.inl)` under
`sumCongr e ρ τ`. -/
theorem mapsTo_range_inl_sumCongr (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m)
    (τ : GaloisSet K n) (σ : Gal(SeparableClosure K/K)) :
    Set.MapsTo ((sumCongr e ρ τ).val σ) (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl)) := by
  rintro _ ⟨i, rfl⟩
  exact ⟨ρ.val σ i, by simp⟩

/-- A labelled Galois set preserving `Set.range (e ∘ Sum.inl)` splits along `e` into a pair of
labelled Galois sets on `Fin m` and `Fin n`. -/
theorem exists_sumCongr_eq (e : Fin m ⊕ Fin n ≃ Fin k) {μ : GaloisSet K k}
    (hμ : ∀ σ, Set.MapsTo (μ.val σ) (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl))) :
    ∃ (ρ : GaloisSet K m) (τ : GaloisSet K n), sumCongr e ρ τ = μ := by
  let φ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin m ⊕ Fin n) :=
    e.symm.permCongrHom.toMonoidHom.comp μ.val
  have hφ (σ : Gal(SeparableClosure K/K)) :
      σ ∈ φ ⁻¹' (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range := by
    refine Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hμ σ ⟨i, rfl⟩
    simp only [Function.comp_apply] at hj
    exact ⟨j, by simp [φ, Equiv.permCongr_apply, ← hj]⟩
  let ψ := (MonoidHom.ofInjective (f := Equiv.Perm.sumCongrHom (Fin m) (Fin n))
    Equiv.Perm.sumCongrHom_injective).symm.toMonoidHom.comp
    (φ.codRestrict (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range hφ)
  have hker : μ.val.ker ≤ ψ.ker := fun σ hσ ↦ by
    rw [MonoidHom.mem_ker] at hσ ⊢
    have hφσ : φ σ = 1 := by rw [MonoidHom.comp_apply, hσ, map_one]
    have hcod : φ.codRestrict (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range hφ σ = 1 :=
      Subtype.ext hφσ
    rw [MonoidHom.comp_apply, hcod, map_one]
  let ρ : GaloisSet K m := ⟨(MonoidHom.fst _ _).comp ψ, Subgroup.isOpen_mono
    (hker.trans fun σ hσ ↦ by simp [MonoidHom.mem_ker.1 hσ]) μ.property⟩
  let τ : GaloisSet K n := ⟨(MonoidHom.snd _ _).comp ψ, Subgroup.isOpen_mono
    (hker.trans fun σ hσ ↦ by simp [MonoidHom.mem_ker.1 hσ]) μ.property⟩
  refine ⟨ρ, τ, ext fun σ l ↦ ?_⟩
  have hψ : Equiv.Perm.sumCongrHom (Fin m) (Fin n) (ψ σ) = φ σ :=
    MonoidHom.apply_ofInjective_symm Equiv.Perm.sumCongrHom_injective _
  have hl := congrArg (fun p : Equiv.Perm (Fin m ⊕ Fin n) ↦ e (p (e.symm l))) hψ
  simpa [ρ, τ, φ, Equiv.permCongr_apply] using hl

/-- Labelled Galois sets of size `k` preserving `Set.range (e ∘ Sum.inl)` correspond bijectively to
pairs of labelled Galois sets of sizes `m` and `n`. -/
def sumCongrEquiv (e : Fin m ⊕ Fin n ≃ Fin k) :
    GaloisSet K m × GaloisSet K n ≃
      {μ : GaloisSet K k //
        ∀ σ, Set.MapsTo (μ.val σ) (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl))} :=
  Equiv.ofBijective (fun p ↦ ⟨sumCongr e p.1 p.2, mapsTo_range_inl_sumCongr e p.1 p.2⟩)
    ⟨fun _ _ h ↦ sumCongr_injective e (Subtype.mk.inj h), fun ⟨_, hμ⟩ ↦
      let ⟨ρ, τ, h⟩ := exists_sumCongr_eq e hμ
      ⟨(ρ, τ), Subtype.ext h⟩⟩

/-- `sumCongrEquiv e` sends `(ρ, τ)` to `sumCongr e ρ τ`. -/
@[simp]
theorem coe_sumCongrEquiv_apply (e : Fin m ⊕ Fin n ≃ Fin k) (p : GaloisSet K m × GaloisSet K n) :
    (sumCongrEquiv e p : GaloisSet K k) = sumCongr e p.1 p.2 :=
  (rfl)

/-- A label in the left summand has the same stabilizer in `sumCongr e ρ τ` as in `ρ`. -/
@[simp]
theorem stabilizer_sumCongr_inl (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n)
    (i : Fin m) :
    letI := (sumCongr e ρ τ).mulAction
    letI := ρ.mulAction
    MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inl i)) =
      MulAction.stabilizer Gal(SeparableClosure K/K) i := by
  let := (sumCongr e ρ τ).mulAction
  let := ρ.mulAction
  exact TauCeti.MulAction.stabilizer_eq_of_injective (e ∘ Sum.inl)
    (e.injective.comp Sum.inl_injective) (fun σ j ↦ (sumCongr_val_apply_inl e ρ τ σ j).symm) i

/-- A label in the right summand has the same stabilizer in `sumCongr e ρ τ` as in `τ`. -/
@[simp]
theorem stabilizer_sumCongr_inr (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n)
    (j : Fin n) :
    letI := (sumCongr e ρ τ).mulAction
    letI := τ.mulAction
    MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inr j)) =
      MulAction.stabilizer Gal(SeparableClosure K/K) j := by
  let := (sumCongr e ρ τ).mulAction
  let := τ.mulAction
  exact TauCeti.MulAction.stabilizer_eq_of_injective (e ∘ Sum.inr)
    (e.injective.comp Sum.inr_injective) (fun σ j' ↦ (sumCongr_val_apply_inr e ρ τ σ j').symm) j

/-- The orbit of `e (Sum.inl i)` in `sumCongr e ρ τ` is the image under `e ∘ Sum.inl` of the orbit
of `i` in `ρ`. -/
theorem orbit_sumCongr_inl (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m) (τ : GaloisSet K n)
    (i : Fin m) :
    letI := (sumCongr e ρ τ).mulAction
    letI := ρ.mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i)) =
      (e ∘ Sum.inl) '' MulAction.orbit Gal(SeparableClosure K/K) i := by
  let := (sumCongr e ρ τ).mulAction
  let := ρ.mulAction
  ext l
  simp only [MulAction.mem_orbit_iff, smul_def, Set.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ.val σ i, ⟨σ, rfl⟩, by simp⟩
  · rintro ⟨j, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, by simp⟩

/-- The orbit of `e (Sum.inl i)` in `sumCongr e ρ τ` fills `Set.range (e ∘ Sum.inl)` precisely when
`ρ` is transitive. -/
@[simp]
theorem orbit_sumCongr_inl_eq_range_iff (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m)
    (τ : GaloisSet K n) (i : Fin m) :
    (letI := (sumCongr e ρ τ).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i)) = Set.range (e ∘ Sum.inl)) ↔
      ρ.IsTransitive := by
  let := ρ.mulAction
  rw [orbit_sumCongr_inl, ← Set.image_univ,
    Set.image_eq_image (e.injective.comp Sum.inl_injective), isTransitive_def,
    MulAction.isPretransitive_iff_orbit_eq_univ i]

/-- Labelled Galois sets of size `k` in which the orbit of `e (Sum.inl i)` is
`Set.range (e ∘ Sum.inl)` correspond bijectively to pairs `(ρ, τ)` with `ρ` transitive on `Fin m`
and `τ` arbitrary on `Fin n`. -/
def sumCongrTransitiveEquiv (e : Fin m ⊕ Fin n ≃ Fin k) (i : Fin m) :
    {ρ : GaloisSet K m // ρ.IsTransitive} × GaloisSet K n ≃
      {μ : GaloisSet K k //
        letI := μ.mulAction
        MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i)) = Set.range (e ∘ Sum.inl)} :=
  ({ toFun := fun p ↦ ⟨(p.1.1, p.2), p.1.2⟩
     invFun := fun p ↦ (⟨p.1.1, p.2⟩, p.1.2)
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl } :
    {ρ : GaloisSet K m // ρ.IsTransitive} × GaloisSet K n ≃
      {p : GaloisSet K m × GaloisSet K n // p.1.IsTransitive}).trans <|
    (Equiv.subtypeEquiv (sumCongrEquiv e) fun p ↦
      (orbit_sumCongr_inl_eq_range_iff e p.1 p.2 i).symm).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans <|
        Equiv.subtypeEquivRight fun μ ↦ and_iff_right_of_imp fun hμ σ l hl ↦ by
          let := μ.mulAction
          rw [← hμ, MulAction.mem_orbit_iff] at hl ⊢
          obtain ⟨τ, rfl⟩ := hl
          exact ⟨σ * τ, mul_smul σ τ _⟩

/-- `sumCongrTransitiveEquiv e i` sends `(ρ, τ)` to `sumCongr e ρ.1 τ`. -/
@[simp]
theorem coe_sumCongrTransitiveEquiv_apply (e : Fin m ⊕ Fin n ≃ Fin k) (i : Fin m)
    (p : {ρ : GaloisSet K m // ρ.IsTransitive} × GaloisSet K n) :
    (sumCongrTransitiveEquiv e i p : GaloisSet K k) = sumCongr e p.1.1 p.2 :=
  (rfl)

end TauCeti.GaloisSet
