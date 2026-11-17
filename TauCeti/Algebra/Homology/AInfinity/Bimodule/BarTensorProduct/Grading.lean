/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Basic

/-!
# Grading, reassociations, and sign twist for the bar tensor product

This module supplies the graded carrier infrastructure for the two-sided bar tensor product
`M ⊗_{B∞} N` on `(M ⊗ Tᶜ(sB)) ⊗ N`:

* `TauCeti.AInfinityBimodule.barTensorGrading`: the total internal grading combining `M`, the
  suspended tensor coalgebra `Tᶜ(sB)`, and `N`.
* `TauCeti.AInfinityBimodule.barTensorAssocLeft`, `barTensorAssocMid`, `barTensorAssocRight`:
  the three canonical `R`-linear equivalences reassociating the bar bicomodule
  `(Tᶜ(sA) ⊗ ((M ⊗ Tᶜ(sB)) ⊗ N)) ⊗ Tᶜ(sC)` to isolate the left bimodule, the middle coalgebra,
  and the right bimodule.
* `TauCeti.AInfinityBimodule.barTensorSignTwist`: the degree-zero Koszul involution `Φ` acting
  as `(-1)^{|n| + |w_C|}` on `N` and `Tᶜ(sC)`. Conjugating the raw differential by `Φ` reconciles
  the single suspension of `(M ⊗ Tᶜ(sB)) ⊗ N` with the double suspension of `M` and `N`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped BigOperators TensorProduct

namespace TauCeti.AInfinityBimodule

universe uR uA uB uC uM uN

/-! ### Grading of the bar tensor product -/

section Grading

variable {R : Type uR}

/-- Shifting a tensor-product grading is equivalent to shifting its left factor. -/
private theorem shift_tensorProduct_left [CommSemiring R] {X Y : Type*}
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (G : InternalGrading R X ℤ) (H : InternalGrading R Y ℤ) (c : ℤ) :
    (G.tensorProduct H).shift c = (G.shift c).tensorProduct H := by
  refine InternalGrading.ext fun n ↦ ?_
  rw [InternalGrading.shift_piece, InternalGrading.tensorProduct_piece_eq_iSup,
    InternalGrading.tensorProduct_piece_eq_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun p ↦ ?_
    have h1 : p - c + c = p := sub_add_cancel p c
    have h2 : n - (p - c) = n + c - p := by omega
    refine le_trans ?_ (le_iSup (fun q : ℤ ↦
      Submodule.map₂ (TensorProduct.mk R X Y) ((G.shift c).piece q) (H.piece (n - q))) (p - c))
    rw [InternalGrading.shift_piece, h1, h2]
  · refine iSup_le fun p ↦ ?_
    have h : n + c - (p + c) = n - p := by omega
    refine le_trans ?_ (le_iSup (fun q : ℤ ↦
      Submodule.map₂ (TensorProduct.mk R X Y) (G.piece q) (H.piece (n + c - q))) (p + c))
    rw [InternalGrading.shift_piece, h]

/-- Shifting a tensor-product grading is equivalent to shifting its right factor. -/
private theorem shift_tensorProduct_right [CommSemiring R] {X Y : Type*}
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (G : InternalGrading R X ℤ) (H : InternalGrading R Y ℤ) (c : ℤ) :
    (G.tensorProduct H).shift c = G.tensorProduct (H.shift c) := by
  refine InternalGrading.ext fun n ↦ ?_
  rw [InternalGrading.shift_piece, InternalGrading.tensorProduct_piece_eq_iSup,
    InternalGrading.tensorProduct_piece_eq_iSup]
  refine iSup_congr fun p ↦ ?_
  have h : n - p + c = n + c - p := by omega
  rw [InternalGrading.shift_piece, h]

variable {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup B] [Module R B] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The total internal grading on the bar tensor carrier `(M ⊗ Tᶜ(sB)) ⊗ N`, combining the
unsuspended gradings of `M` and `N` with the total suspended grading of `Tᶜ(sB)`. -/
noncomputable def barTensorGrading (GB : InternalGrading R B ℤ)
    (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) :
    InternalGrading R ((M ⊗[R] TensorWords R B) ⊗[R] N) ℤ :=
  (GM.tensorProduct (TensorWords.grading (GB.shift 1))).tensorProduct GN

/-- The bar tensor grading is the total grading of `M`, `Tᶜ(sB)`, and `N`. -/
theorem barTensorGrading_def (GB : InternalGrading R B ℤ)
    (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) :
    barTensorGrading GB GM GN =
      (GM.tensorProduct (TensorWords.grading (GB.shift 1))).tensorProduct GN :=
  (rfl)

/-- The degree-`p` piece of the bar tensor grading. -/
@[simp]
theorem barTensorGrading_piece (GB : InternalGrading R B ℤ)
    (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) (p : ℤ) :
    (barTensorGrading GB GM GN).piece p =
      ((GM.tensorProduct (TensorWords.grading (GB.shift 1))).tensorProduct GN).piece p :=
  (rfl)

/-- Shifting `barTensorGrading` is equivalent to shifting its left module grading `GM`. -/
theorem shift_barTensorGrading_left (GB : InternalGrading R B ℤ)
    (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) (c : ℤ) :
    (barTensorGrading GB GM GN).shift c = barTensorGrading GB (GM.shift c) GN := by
  rw [barTensorGrading_def, barTensorGrading_def, shift_tensorProduct_left,
    shift_tensorProduct_left]

/-- Shifting `barTensorGrading` is equivalent to shifting its right module grading `GN`. -/
theorem shift_barTensorGrading_right (GB : InternalGrading R B ℤ)
    (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) (c : ℤ) :
    (barTensorGrading GB GM GN).shift c = barTensorGrading GB GM (GN.shift c) := by
  rw [barTensorGrading_def, barTensorGrading_def, shift_tensorProduct_right]

/-- A pure tensor of homogeneous elements in `M`, `Tᶜ(sB)`, and `N` has the sum of their degrees
in `barTensorGrading`. -/
theorem tmul_mem_barTensorGrading (GB : InternalGrading R B ℤ)
    {GM : InternalGrading R M ℤ} {GN : InternalGrading R N ℤ}
    {m : M} {w : TensorWords R B} {n : N} {p q r : ℤ}
    (hm : m ∈ GM.piece p) (hw : w ∈ (TensorWords.grading (GB.shift 1)).piece q)
    (hn : n ∈ GN.piece r) :
    (m ⊗ₜ[R] w) ⊗ₜ[R] n ∈ (barTensorGrading GB GM GN).piece (p + q + r) :=
  InternalGrading.tmul_mem_tensorProduct _ _ (InternalGrading.tmul_mem_tensorProduct _ _ hm hw) hn

/-- With the empty word in the middle, `(m ⊗ 1) ⊗ n` has degree `|m| + |n|`. -/
theorem tmul_one_mem_barTensorGrading (GB : InternalGrading R B ℤ)
    {GM : InternalGrading R M ℤ} {GN : InternalGrading R N ℤ}
    {m : M} {n : N} {p r : ℤ} (hm : m ∈ GM.piece p) (hn : n ∈ GN.piece r) :
    (m ⊗ₜ[R] (1 : TensorWords R B)) ⊗ₜ[R] n ∈ (barTensorGrading GB GM GN).piece (p + r) := by
  have h1 : (1 : TensorWords R B) ∈ (TensorWords.grading (GB.shift 1)).piece 0 := by
    simpa only [TensorWords.grading_piece] using TensorWords.one_mem_gradedPiece (GB.shift 1)
  have h := tmul_mem_barTensorGrading GB hm h1 hn
  rwa [add_zero] at h

end Grading

/-! ### Reassociation equivalences -/

section Reassociation

variable (R : Type uR) (A : Type uA) (B : Type uB) (C : Type uC)
  (M : Type uM) (N : Type uN)
  [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Reassociate the bar bicomodule of `(M ⊗ Tᶜ(sB)) ⊗ N` to isolate the left bimodule bar carrier
`(Tᶜ(sA) ⊗ M) ⊗ Tᶜ(sB)`. -/
noncomputable def barTensorAssocLeft :
    ((TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C) ≃ₗ[R]
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ⊗[R] (N ⊗[R] TensorWords R C) :=
  ((TensorProduct.assoc R (TensorWords R A) (M ⊗[R] TensorWords R B) N).symm.rTensor
      (TensorWords R C)).trans <|
    (((TensorProduct.assoc R (TensorWords R A) M (TensorWords R B)).symm.rTensor N).rTensor
        (TensorWords R C)).trans <|
      TensorProduct.assoc R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) N (TensorWords R C)

@[simp]
theorem barTensorAssocLeft_tmul (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    barTensorAssocLeft R A B C M N ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) =
      ((wA ⊗ₜ m) ⊗ₜ wB) ⊗ₜ (n ⊗ₜ wC) := by
  simp [barTensorAssocLeft]

@[simp]
theorem barTensorAssocLeft_symm_tmul (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    (barTensorAssocLeft R A B C M N).symm (((wA ⊗ₜ m) ⊗ₜ wB) ⊗ₜ (n ⊗ₜ wC)) =
      (wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC := by
  simp [barTensorAssocLeft]

/-- Reassociate the bar bicomodule of `(M ⊗ Tᶜ(sB)) ⊗ N` to isolate the middle tensor coalgebra
`Tᶜ(sB)`. -/
noncomputable def barTensorAssocMid :
    ((TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C) ≃ₗ[R]
      (TensorWords R A ⊗[R] M) ⊗[R] (TensorWords R B ⊗[R] (N ⊗[R] TensorWords R C)) :=
  (barTensorAssocLeft R A B C M N).trans
    (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B) (N ⊗[R] TensorWords R C))

@[simp]
theorem barTensorAssocMid_tmul (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    barTensorAssocMid R A B C M N ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) =
      (wA ⊗ₜ m) ⊗ₜ (wB ⊗ₜ (n ⊗ₜ wC)) := by
  simp [barTensorAssocMid]

@[simp]
theorem barTensorAssocMid_symm_tmul (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    (barTensorAssocMid R A B C M N).symm ((wA ⊗ₜ m) ⊗ₜ (wB ⊗ₜ (n ⊗ₜ wC))) =
      (wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC := by
  simp [barTensorAssocMid]

/-- Reassociate the bar bicomodule of `(M ⊗ Tᶜ(sB)) ⊗ N` to isolate the right bimodule bar carrier
`(Tᶜ(sB) ⊗ N) ⊗ Tᶜ(sC)`. -/
noncomputable def barTensorAssocRight :
    ((TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C) ≃ₗ[R]
      (TensorWords R A ⊗[R] M) ⊗[R] ((TensorWords R B ⊗[R] N) ⊗[R] TensorWords R C) :=
  (barTensorAssocMid R A B C M N).trans
    ((TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.lTensor
      (TensorWords R A ⊗[R] M))

@[simp]
theorem barTensorAssocRight_tmul (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    barTensorAssocRight R A B C M N ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) =
      (wA ⊗ₜ m) ⊗ₜ ((wB ⊗ₜ n) ⊗ₜ wC) := by
  simp [barTensorAssocRight]

@[simp]
theorem barTensorAssocRight_symm_tmul (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N)
    (wC : TensorWords R C) :
    (barTensorAssocRight R A B C M N).symm ((wA ⊗ₜ m) ⊗ₜ ((wB ⊗ₜ n) ⊗ₜ wC)) =
      (wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC := by
  simp [barTensorAssocRight]

variable {R A B C M N}

/-- Extensionality for linear maps out of the fivefold bar tensor bicomodule. -/
theorem barTensor_ext {X : Type*} [AddCommMonoid X] [Module R X]
    {f g : (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R] X}
    (h : ∀ wA m wB n wC,
      f ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) = g ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC)) :
    f = g := by
  refine TensorProduct.ext' fun x wC ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [TensorProduct.add_tmul, map_add, hx₁, hx₂]
  | tmul wA p =>
    induction p using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hy₁, hy₂]
    | tmul mb n =>
      induction mb using TensorProduct.inductionOn with
      | add z₁ z₂ hz₁ hz₂ =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hz₁, hz₂]
      | tmul m wB => exact h wA m wB n wC

end Reassociation

/-! ### The sign-fixing involution -/

section SignTwist

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The degree-zero Koszul involution `Φ` on `(Tᶜ(sA) ⊗ ((M ⊗ Tᶜ(sB)) ⊗ N)) ⊗ Tᶜ(sC)` that scales
`n` by `(-1)^{|n|}` and `w_C` by `(-1)^{|w_C|}`. Conjugating the raw differential by `Φ` turns its
right co-Leibniz sign into the one required by `barGrading AA CC (barTensorGrading GB GM GN)`. -/
noncomputable def barTensorSignTwist (GC : InternalGrading R C ℤ) (GN : InternalGrading R N ℤ) :
    (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C →ₗ[R]
      (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ⊗[R] TensorWords R C :=
  TensorProduct.map
    (((GN.koszulTwist 1).lTensor (M ⊗[R] TensorWords R B)).lTensor (TensorWords R A))
    ((TensorWords.grading (GC.shift 1)).koszulTwist 1)

@[simp]
theorem barTensorSignTwist_tmul (GC : InternalGrading R C ℤ) (GN : InternalGrading R N ℤ)
    (wA : TensorWords R A) (m : M) (wB : TensorWords R B) (n : N) (wC : TensorWords R C) :
    barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN ((wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ n)) ⊗ₜ wC) =
      (wA ⊗ₜ ((m ⊗ₜ wB) ⊗ₜ GN.koszulTwist 1 n)) ⊗ₜ
        (TensorWords.grading (GC.shift 1)).koszulTwist 1 wC := by
  simp [barTensorSignTwist]

/-- The sign-fixing twist is an involution. -/
@[simp]
theorem barTensorSignTwist_comp_self (GC : InternalGrading R C ℤ) (GN : InternalGrading R N ℤ) :
    barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN ∘ₗ
      barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN = LinearMap.id := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply, barTensorSignTwist_tmul,
    InternalGrading.koszulTwist_koszulTwist]

/-- Conjugating a map acting on the left bimodule factor by `barTensorSignTwist` leaves it
unchanged. -/
theorem barTensorSignTwist_conj_assocLeft (GC : InternalGrading R C ℤ)
    (GN : InternalGrading R N ℤ) {M' : Type*} [AddCommMonoid M'] [Module R M']
    (F : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] M') ⊗[R] TensorWords R B) :
    barTensorSignTwist (R := R) (A := A) (B := B) (M := M') GC GN ∘ₗ
      ((barTensorAssocLeft R A B C M' N).symm.toLinearMap ∘ₗ
        F.rTensor (N ⊗[R] TensorWords R C) ∘ₗ
        (barTensorAssocLeft R A B C M N).toLinearMap) ∘ₗ
      barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN =
      (barTensorAssocLeft R A B C M' N).symm.toLinearMap ∘ₗ
        F.rTensor (N ⊗[R] TensorWords R C) ∘ₗ
        (barTensorAssocLeft R A B C M N).toLinearMap := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.comp_apply, barTensorSignTwist_tmul, LinearEquiv.coe_coe,
    barTensorAssocLeft_tmul, LinearMap.rTensor_tmul]
  induction F ((wA ⊗ₜ m) ⊗ₜ wB) using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul u v =>
    induction u using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul wA' m' =>
      simp only [barTensorAssocLeft_symm_tmul, barTensorSignTwist_tmul,
        InternalGrading.koszulTwist_koszulTwist]

/-- `barTensorSignTwist` intertwines the left coaction of `Tᶜ(sA)`. -/
theorem leftCoactRTensor_comp_barTensorSignTwist (GC : InternalGrading R C ℤ)
    (GN : InternalGrading R N ℤ) :
    Comodule.leftCoactRTensor (TensorWords R C)
        (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N)) ∘ₗ
      barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN =
      (barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN).lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R C)
          (Comodule.leftCofreeCoact R (TensorWords R A) ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  simp only [LinearMap.comp_apply, barTensorSignTwist_tmul, Comodule.leftCoactRTensor_tmul,
    Comodule.leftCofreeCoact_tmul]
  induction Coalgebra.comul (R := R) wA using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul u v => simp

/-- `barTensorSignTwist` transforms under the right coaction of `Tᶜ(sC)` by twisting the split-off
right coalgebra factor. -/
theorem cofreeCoact_comp_barTensorSignTwist (GC : InternalGrading R C ℤ)
    (GN : InternalGrading R N ℤ) :
    Comodule.cofreeCoact R (TensorWords R C)
        (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) ∘ₗ
      barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN =
      TensorProduct.map (barTensorSignTwist (R := R) (A := A) (B := B) (M := M) GC GN)
        ((TensorWords.grading (GC.shift 1)).koszulTwist 1) ∘ₗ
        Comodule.cofreeCoact R (TensorWords R C)
          (TensorWords R A ⊗[R] ((M ⊗[R] TensorWords R B) ⊗[R] N)) := by
  have hτ : Coalgebra.comul ∘ₗ (TensorWords.grading (GC.shift 1)).koszulTwist 1 =
      TensorProduct.map ((TensorWords.grading (GC.shift 1)).koszulTwist 1)
        ((TensorWords.grading (GC.shift 1)).koszulTwist 1) ∘ₗ
        (Coalgebra.comul : TensorWords R C →ₗ[R] TensorWords R C ⊗[R] TensorWords R C) := by
    rw [TensorWords.koszulTwist_grading, TensorWords.comul_eq_deconcatenation,
      TensorWords.deconcatenation_natural]
  refine barTensor_ext fun wA m wB n wC ↦ ?_
  have hc := LinearMap.congr_fun hτ wC
  simp only [LinearMap.comp_apply] at hc
  simp only [LinearMap.comp_apply, barTensorSignTwist_tmul, Comodule.cofreeCoact_tmul, hc]
  induction Coalgebra.comul (R := R) wC using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul u v => simp

end SignTwist

/-! ### Homogeneity of the reassociations and sign twist -/

section Homogeneity

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The sign-fixing twist preserves total suspended degree. -/
theorem isHomogeneous_barTensorSignTwist (AA : AInfinityAlgebra R A) (GB : InternalGrading R B ℤ)
    (CC : AInfinityAlgebra R C) (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous
      (barTensorSignTwist (R := R) (A := A) (B := B) (M := M) CC.grading GN)
      (barGrading AA CC (barTensorGrading GB GM GN)).piece
      (barGrading AA CC (barTensorGrading GB GM GN)).piece 0 := by
  have hN : LinearMap.IsHomogeneous (GN.koszulTwist 1) (GN.shift 1).piece (GN.shift 1).piece 0 :=
    LinearMap.isHomogeneous_shift_piece_iff.2 <| LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using GN.koszulTwist_mem_piece hx 1
  have hC : LinearMap.IsHomogeneous ((TensorWords.grading (CC.grading.shift 1)).koszulTwist 1)
      (TensorWords.grading (CC.grading.shift 1)).piece
      (TensorWords.grading (CC.grading.shift 1)).piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using (TensorWords.grading (CC.grading.shift 1)).koszulTwist_mem_piece
        hx 1
  have hP := shift_barTensorGrading_right GB GM GN 1
  rw [barGrading_def, hP, barTensorGrading_def, barTensorSignTwist]
  have h1 := (LinearMap.isHomogeneous_id
    (GM.tensorProduct (TensorWords.grading (GB.shift 1))).piece).tensorProduct hN
  have h2 := (LinearMap.isHomogeneous_id
    (TensorWords.grading (AA.grading.shift 1)).piece).tensorProduct h1
  simpa only [LinearMap.lTensor_def, zero_add] using h2.tensorProduct hC

/-- Reassociation to the left bimodule preserves total suspended degree. -/
theorem isHomogeneous_barTensorAssocLeft (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B)
    (CC : AInfinityAlgebra R C) (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorAssocLeft R A B C M N).toLinearMap
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece
      ((barGrading AA BB GM).tensorProduct
        (GN.tensorProduct (TensorWords.grading (CC.grading.shift 1)))).piece 0 := by
  let GA := TensorWords.grading (AA.grading.shift 1)
  let GB := TensorWords.grading (BB.grading.shift 1)
  let GC := TensorWords.grading (CC.grading.shift 1)
  have hP := shift_barTensorGrading_left BB.grading GM GN 1
  have heq : (barTensorAssocLeft R A B C M N).toLinearMap =
      (TensorProduct.assoc R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) N
          (TensorWords R C)).toLinearMap ∘ₗ
        (((TensorProduct.assoc R (TensorWords R A) M (TensorWords R B)).symm.toLinearMap.rTensor
          N).rTensor (TensorWords R C) ∘ₗ
        (TensorProduct.assoc R (TensorWords R A) (M ⊗[R] TensorWords R B)
          N).symm.toLinearMap.rTensor (TensorWords R C)) :=
    rfl
  rw [barGrading_def, hP, barTensorGrading_def, barGrading_def, heq]
  have h1 := (InternalGrading.isHomogeneous_assoc_symm GA
    ((GM.shift 1).tensorProduct GB) GN).rTensor GC
  have h2 := ((InternalGrading.isHomogeneous_assoc_symm GA (GM.shift 1) GB).rTensor GN).rTensor GC
  have h3 := InternalGrading.isHomogeneous_assoc ((GA.tensorProduct (GM.shift 1)).tensorProduct GB)
    GN GC
  simpa only [add_zero] using h3.comp (h2.comp h1)

/-- The inverse of `barTensorAssocLeft` preserves total suspended degree. -/
theorem isHomogeneous_barTensorAssocLeft_symm (AA : AInfinityAlgebra R A)
    (BB : AInfinityAlgebra R B) (CC : AInfinityAlgebra R C) (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorAssocLeft R A B C M N).symm.toLinearMap
      ((barGrading AA BB GM).tensorProduct
        (GN.tensorProduct (TensorWords.grading (CC.grading.shift 1)))).piece
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece 0 :=
  (isHomogeneous_barTensorAssocLeft AA BB CC GM GN).linearEquiv_symm

/-- Reassociation to the middle coalgebra preserves total suspended degree, with the suspension
placed on `M`. -/
theorem isHomogeneous_barTensorAssocMid (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B)
    (CC : AInfinityAlgebra R C) (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorAssocMid R A B C M N).toLinearMap
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).tensorProduct
        ((TensorWords.grading (BB.grading.shift 1)).tensorProduct
          (GN.tensorProduct (TensorWords.grading (CC.grading.shift 1))))).piece 0 := by
  have h1 := isHomogeneous_barTensorAssocLeft AA BB CC GM GN
  rw [barGrading_def AA BB GM] at h1
  have h2 := InternalGrading.isHomogeneous_assoc
    ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1))
    (TensorWords.grading (BB.grading.shift 1))
    (GN.tensorProduct (TensorWords.grading (CC.grading.shift 1)))
  have heq : (barTensorAssocMid R A B C M N).toLinearMap =
      (TensorProduct.assoc R (TensorWords R A ⊗[R] M) (TensorWords R B)
        (N ⊗[R] TensorWords R C)).toLinearMap ∘ₗ
      (barTensorAssocLeft R A B C M N).toLinearMap :=
    rfl
  rw [heq]
  simpa only [add_zero] using h2.comp h1

/-- The inverse of `barTensorAssocMid` preserves total suspended degree. -/
theorem isHomogeneous_barTensorAssocMid_symm (AA : AInfinityAlgebra R A)
    (BB : AInfinityAlgebra R B) (CC : AInfinityAlgebra R C) (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorAssocMid R A B C M N).symm.toLinearMap
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (GM.shift 1)).tensorProduct
        ((TensorWords.grading (BB.grading.shift 1)).tensorProduct
          (GN.tensorProduct (TensorWords.grading (CC.grading.shift 1))))).piece
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece 0 :=
  (isHomogeneous_barTensorAssocMid AA BB CC GM GN).linearEquiv_symm

/-- Reassociation to the right bimodule preserves total suspended degree, with the suspension
placed on `N`. -/
theorem isHomogeneous_barTensorAssocRight (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B)
    (CC : AInfinityAlgebra R C) (GM : InternalGrading R M ℤ) (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorAssocRight R A B C M N).toLinearMap
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct GM).tensorProduct
        (barGrading BB CC GN)).piece 0 := by
  let GA := TensorWords.grading (AA.grading.shift 1)
  let GB := TensorWords.grading (BB.grading.shift 1)
  let GC := TensorWords.grading (CC.grading.shift 1)
  have hshift :
      (GA.tensorProduct (GM.shift 1)).tensorProduct (GB.tensorProduct (GN.tensorProduct GC)) =
      (GA.tensorProduct GM).tensorProduct (GB.tensorProduct ((GN.shift 1).tensorProduct GC)) := by
    rw [← shift_tensorProduct_right GA GM 1, ← shift_tensorProduct_left _ _ 1,
      shift_tensorProduct_right (GA.tensorProduct GM) _ 1,
      shift_tensorProduct_right GB _ 1, shift_tensorProduct_left GN GC 1]
  have h1 := isHomogeneous_barTensorAssocMid AA BB CC GM GN
  rw [hshift] at h1
  have h2 := (LinearMap.isHomogeneous_id (GA.tensorProduct GM).piece).tensorProduct
    (InternalGrading.isHomogeneous_assoc_symm GB (GN.shift 1) GC)
  have heq : (barTensorAssocRight R A B C M N).toLinearMap =
      TensorProduct.map LinearMap.id
        (TensorProduct.assoc R (TensorWords R B) N (TensorWords R C)).symm.toLinearMap ∘ₗ
      (barTensorAssocMid R A B C M N).toLinearMap :=
    rfl
  rw [heq, barGrading_def BB CC GN]
  simpa only [add_zero] using h2.comp h1

/-- The inverse of `barTensorAssocRight` preserves total suspended degree. -/
theorem isHomogeneous_barTensorAssocRight_symm (AA : AInfinityAlgebra R A)
    (BB : AInfinityAlgebra R B) (CC : AInfinityAlgebra R C) (GM : InternalGrading R M ℤ)
    (GN : InternalGrading R N ℤ) :
    LinearMap.IsHomogeneous (barTensorAssocRight R A B C M N).symm.toLinearMap
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct GM).tensorProduct
        (barGrading BB CC GN)).piece
      (barGrading AA CC (barTensorGrading BB.grading GM GN)).piece 0 :=
  (isHomogeneous_barTensorAssocRight AA BB CC GM GN).linearEquiv_symm

end Homogeneity

end TauCeti.AInfinityBimodule
