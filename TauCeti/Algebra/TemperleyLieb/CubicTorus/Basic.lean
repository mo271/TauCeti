/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Star
public import TauCeti.Algebra.TemperleyLieb.Star

/-!
# The cubic quantum torus representation of the Temperley–Lieb algebra at `δ = √3`

At `δ = √3 = 2 cos (π / 6)` (`δ² = 3`), `TemperleyLieb ℂ (√3 : ℂ) m` surjects via `cubicFixedHom m`
onto the inversion-fixed star subalgebra `cubicFixed (m - 1)` of `CubicTorus (m - 1)`
(`finrank_cubicTorus` = `3 ^ N`, `finrank_cubicFixed` = `(3 ^ N + 1) / 2`,
`cubicFixedHom_surjective`). The alternating `chainForm N` on `Fin N → ZMod 3` defines
`cubicFactor N` (`α(a, b) = ω ^ (2 B(a, b))`), site unitaries `cubicSite N j`, and projections
`cubicProjection N j = 3⁻¹ • (1 + U_j + U_j ^ 2)`.
-/

public section

namespace TauCeti.TemperleyLieb

open TwistedMonoidAlgebra (basis scalarTrace mapStarAlgHom algHom_ext)

instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) := ⟨Complex.conj_ofReal _⟩
private theorem sqrt_three_coe_mul_self : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
private theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by decide +revert
/-- The alternating chain form `B(a, b) = ∑_{j < N - 1} (a_j b_{j + 1} - b_j a_{j + 1})` on
`Fin N → ZMod 3`. -/
def chainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin (N - 1),
    (a ⟨i.1, by omega⟩ * b ⟨i.1 + 1, by omega⟩ - b ⟨i.1, by omega⟩ * a ⟨i.1 + 1, by omega⟩)
theorem chainForm_def (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b = ∑ i : Fin (N - 1),
      (a ⟨i.1, by omega⟩ * b ⟨i.1 + 1, by omega⟩ -
        b ⟨i.1, by omega⟩ * a ⟨i.1 + 1, by omega⟩) := (rfl)
theorem chainForm_add_left (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N (a + b) c = chainForm N a c + chainForm N b c := by
  rw [chainForm_def, chainForm_def, chainForm_def, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [Pi.add_apply]; ring
theorem chainForm_add_right (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N a (b + c) = chainForm N a b + chainForm N a c := by
  rw [chainForm_def, chainForm_def, chainForm_def, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [Pi.add_apply]; ring
theorem chainForm_smul_left (N : ℕ) (r : ZMod 3) (a b : Fin N → ZMod 3) :
    chainForm N (r • a) b = r * chainForm N a b := by
  rw [chainForm_def, chainForm_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring
theorem chainForm_smul_right (N : ℕ) (r : ZMod 3) (a b : Fin N → ZMod 3) :
    chainForm N a (r • b) = r * chainForm N a b := by
  rw [chainForm_def, chainForm_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring
@[simp] theorem chainForm_zero_left (N : ℕ) (b : Fin N → ZMod 3) : chainForm N 0 b = 0 := by
  simp [chainForm_def]
@[simp] theorem chainForm_zero_right (N : ℕ) (a : Fin N → ZMod 3) : chainForm N a 0 = 0 := by
  simp [chainForm_def]
@[simp] theorem chainForm_self (N : ℕ) (a : Fin N → ZMod 3) : chainForm N a a = 0 := by
  simp [chainForm_def]
theorem chainForm_swap (N : ℕ) (a b : Fin N → ZMod 3) : chainForm N b a = -chainForm N a b := by
  rw [chainForm_def, chainForm_def, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring
@[simp] theorem chainForm_neg_left (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) b = -chainForm N a b := by simpa using chainForm_smul_left N (-1) a b
@[simp] theorem chainForm_neg_right (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a (-b) = -chainForm N a b := by simpa using chainForm_smul_right N (-1) a b
theorem chainForm_neg_neg (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) (-b) = chainForm N a b := by simp
theorem chainForm_single_right {N : ℕ} (a : Fin N → ZMod 3) (k : Fin N) :
    chainForm N a (Pi.single k 1) =
      (if h : 0 < k.val then a ⟨k.val - 1, by omega⟩ else 0) -
        (if h : k.val + 1 < N then a ⟨k.val + 1, h⟩ else 0) := by
  simp only [chainForm_def, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, ite_mul,
    mul_one, one_mul, mul_zero, zero_mul]
  congr 1
  · split_ifs with hk
    · refine Finset.sum_eq_single ⟨k.val - 1, by omega⟩ (fun i _ hi ↦ ?_) (by simp) |>.trans ?_
      · have : i.1 ≠ k.1 - 1 := fun h ↦ hi (Fin.ext h)
        simp [Fin.ext_iff]; omega
      · simp [Nat.sub_add_cancel hk]
    · exact Finset.sum_eq_zero fun i _ ↦ by simp [Fin.ext_iff]; omega
  · split_ifs with hk
    · refine Finset.sum_eq_single ⟨k.val, by omega⟩ (fun i _ hi ↦ ?_) (by simp) |>.trans (by simp)
      simp [Fin.ext_iff, show i.1 ≠ k.1 from fun h ↦ hi (Fin.ext h)]
    · exact Finset.sum_eq_zero fun i _ ↦ by simp [Fin.ext_iff]; omega
theorem chainForm_single_single_succ {N : ℕ} {i j : Fin N} (hij : (i : ℕ) + 1 = j) :
    chainForm N (Pi.single i 1) (Pi.single j 1) = 1 := by
  rw [chainForm_single_right]
  have hi : (⟨j.val - 1, by omega⟩ : Fin N) = i := Fin.ext (by dsimp; omega)
  simp only [show 0 < j.val by omega, ↓reduceDIte, hi, Pi.single_eq_same]
  split_ifs with hlt
  · simp [Pi.single_eq_of_ne (show (⟨j.val + 1, hlt⟩ : Fin N) ≠ i from fun h ↦ by
      have := congrArg Fin.val h; dsimp at this; omega)]
  · simp
theorem chainForm_single_single_of_dist_ge_two {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    chainForm N (Pi.single i 1) (Pi.single j 1) = 0 := by
  rw [chainForm_single_right]
  have hne (n : ℕ) (hn : n < N) (hd : n ≠ i.val) : (⟨n, hn⟩ : Fin N) ≠ i :=
    fun h ↦ hd (congrArg Fin.val h)
  split_ifs <;> simp [Pi.single_eq_of_ne, hne _ _ (by omega : j.val - 1 ≠ i.val),
    hne _ _ (by omega : j.val + 1 ≠ i.val)]
/-- The primitive cube root of unity `ω = exp (2 π i / 3)`, as a unit of `ℂ`. -/
noncomputable def cubeRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi / 3 * Complex.I)) (Complex.exp_ne_zero _)
theorem cubeRootOfUnity_val :
    (cubeRootOfUnity : ℂ) = Complex.exp (2 * Real.pi / 3 * Complex.I) := (rfl)
theorem cubeRootOfUnity_val_eq :
    (cubeRootOfUnity : ℂ) = (-1 + Real.sqrt 3 * Complex.I) / 2 := by
  have harg : (2 * Real.pi / 3 * Complex.I : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [cubeRootOfUnity_val, harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast; ring
@[simp] theorem cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, cubeRootOfUnity_val, Units.val_one, ← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2; push_cast; ring
@[simp] theorem cubeRootOfUnity_val_pow_three : (cubeRootOfUnity : ℂ) ^ 3 = 1 := by
  rw [← Units.val_pow_eq_pow_val, cubeRootOfUnity_pow_three, Units.val_one]
theorem cubeRootOfUnity_ne_one : cubeRootOfUnity ≠ 1 := fun h ↦ by
  have hre := congrArg Complex.re ((congrArg Units.val h).symm.trans cubeRootOfUnity_val_eq)
  simp at hre; linarith
theorem cubeRootOfUnity_val_ne_one : (cubeRootOfUnity : ℂ) ≠ 1 :=
  fun h ↦ cubeRootOfUnity_ne_one (Units.ext h)
theorem one_add_cubeRootOfUnity_add_sq :
    1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 :=
  (mul_eq_zero.mp (by linear_combination cubeRootOfUnity_val_pow_three :
    ((cubeRootOfUnity : ℂ) - 1) * (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) = 0)
  ).resolve_left (sub_ne_zero.mpr cubeRootOfUnity_val_ne_one)
@[simp] theorem star_cubeRootOfUnity_val :
    star (cubeRootOfUnity : ℂ) = ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  have hmul : star (cubeRootOfUnity : ℂ) * (cubeRootOfUnity : ℂ) = 1 := by
    rw [cubeRootOfUnity_val, Complex.star_def, ← Complex.exp_conj,
      show (starRingEnd ℂ) (2 * Real.pi / 3 * Complex.I) = -(2 * Real.pi / 3 * Complex.I) by
        simp [map_div₀, map_mul, map_ofNat], ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  simpa [mul_assoc] using congrArg (· * ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ)) hmul
/-- The character `x ↦ ω ^ x.val` on `ZMod 3`. -/
noncomputable def cubeRootPow (x : ZMod 3) : ℂˣ := cubeRootOfUnity ^ x.val
@[simp] theorem cubeRootPow_zero : cubeRootPow 0 = 1 := by simp [cubeRootPow]
@[simp] theorem cubeRootPow_one : cubeRootPow 1 = cubeRootOfUnity := by
  rw [cubeRootPow, show (1 : ZMod 3).val = 1 from rfl, pow_one]
@[simp] theorem cubeRootPow_two : cubeRootPow 2 = cubeRootOfUnity ^ 2 := by
  rw [cubeRootPow, show (2 : ZMod 3).val = 2 from rfl]
theorem cubeRootPow_add (x y : ZMod 3) : cubeRootPow (x + y) = cubeRootPow x * cubeRootPow y := by
  simp only [cubeRootPow, ZMod.val_add]
  rw [← pow_add, ← pow_eq_pow_mod _ cubeRootOfUnity_pow_three]
@[simp] theorem cubeRootPow_neg (x : ZMod 3) : cubeRootPow (-x) = (cubeRootPow x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← cubeRootPow_add, neg_add_cancel, cubeRootPow_zero])
@[simp] theorem cubeRootPow_eq_one_iff {x : ZMod 3} : cubeRootPow x = 1 ↔ x = 0 := by
  rcases zmod3_cases x with rfl | rfl | rfl
  · simp
  · simp [cubeRootOfUnity_ne_one]
  · refine ⟨fun h ↦ False.elim (cubeRootOfUnity_ne_one ?_), fun h ↦ absurd h (by decide)⟩
    rw [cubeRootPow_two] at h; simpa [pow_succ, h] using cubeRootOfUnity_pow_three
@[simp] theorem star_cubeRootPow_val (x : ZMod 3) :
    star (cubeRootPow x : ℂ) = ((cubeRootPow x)⁻¹ : ℂˣ) := by
  rw [cubeRootPow, Units.val_pow_eq_pow_val, star_pow, star_cubeRootOfUnity_val,
    ← Units.val_pow_eq_pow_val, inv_pow]

/-! ### The cubic factor set and cubic quantum torus -/

/-- The factor set `α(a, b) = ω ^ (2 * B(a, b))` of the cubic quantum torus on
`Multiplicative (Fin N → ZMod 3)`. -/
noncomputable def cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  cubeRootPow (2 * chainForm N a.toAdd b.toAdd)
theorem cubicFactor_def (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) := (rfl)
instance cubicFactor_isFactorSet (N : ℕ) : IsFactorSet (cubicFactor N) where
  cocycle g h j := by
    simp only [cubicFactor_def, toAdd_mul, ← cubeRootPow_add]
    congr 1; rw [chainForm_add_left, chainForm_add_right]; ring
  one_left g := by simp [cubicFactor_def]
instance cubicFactor_unitary (N : ℕ) :
    Fact (∀ g h : Multiplicative (Fin N → ZMod 3),
      star (cubicFactor N g h : ℂ) = ((cubicFactor N g h)⁻¹ : ℂˣ)) :=
  ⟨fun _ _ ↦ star_cubeRootPow_val _⟩
@[simp] theorem cubicFactor_self (N : ℕ) (g : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g g = 1 := by simp [cubicFactor_def]
@[simp] theorem cubicFactor_inv_self (N : ℕ) (g : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g g⁻¹ = 1 := by simp [cubicFactor_def]
@[simp] theorem cubicFactor_inv_self_left (N : ℕ) (g : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g⁻¹ g = 1 := by simp [cubicFactor_def]
@[simp] theorem cubicFactor_inv_inv (N : ℕ) (g h : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g⁻¹ h⁻¹ = cubicFactor N g h := by simp [cubicFactor_def]
theorem cubicFactor_swap (N : ℕ) (g h : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N h g = (cubicFactor N g h)⁻¹ := by
  rw [cubicFactor_def, cubicFactor_def, chainForm_swap, mul_neg, cubeRootPow_neg]
theorem cubicFactor_mul_inv_swap (N : ℕ) (g h : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g h * (cubicFactor N h g)⁻¹ = cubeRootPow (chainForm N g.toAdd h.toAdd) := by
  rw [cubicFactor_swap N g h, inv_inv, cubicFactor_def, ← cubeRootPow_add]
  congr 1; rw [← add_mul, show (2 : ZMod 3) + 2 = 1 by decide, one_mul]
/-- **The cubic quantum torus** `G_N`: the twisted group algebra of `(ZMod 3)^N` for
`cubicFactor N`, of complex dimension `3 ^ N`. -/
noncomputable abbrev CubicTorus (N : ℕ) :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
/-- The Weyl basis element `W(a) = TwistedMonoidAlgebra.of a` of `CubicTorus N`. -/
noncomputable def weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  TwistedMonoidAlgebra.of a
theorem weyl_def (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a = TwistedMonoidAlgebra.of a := (rfl)
@[simp] theorem weyl_one (N : ℕ) : weyl N 1 = 1 := TwistedMonoidAlgebra.of_one
@[simp] theorem weyl_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b = (cubicFactor N a b : ℂ) • weyl N (a * b) :=
  TwistedMonoidAlgebra.of_mul_of a b
@[simp] theorem star_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    star (weyl N a) = weyl N a⁻¹ := by
  rw [weyl_def, TwistedMonoidAlgebra.star_of_of_apply_inv_eq_one (cubicFactor_inv_self N a),
    ← weyl_def]
theorem weyl_mul_weyl_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N a⁻¹ = 1 := by simp
theorem weyl_inv_mul_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a⁻¹ * weyl N a = 1 := by simp
@[simp] theorem weyl_sq (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 2 = weyl N a⁻¹ := by
  rw [sq, weyl_mul, cubicFactor_self, Units.val_one, one_smul]
  congr 1; apply Multiplicative.toAdd.injective; ext i
  exact (by decide : ∀ z : ZMod 3, z + z = -z) (a.toAdd i)
@[simp] theorem weyl_pow_three (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 3 = 1 := by rw [pow_succ, weyl_sq, weyl_inv_mul_weyl]
/-- Commutation relation: `W(a) * W(b) = ω ^ B(a, b) • (W(b) * W(a))`. -/
theorem weyl_mul_comm_factor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b =
      (cubeRootPow (chainForm N a.toAdd b.toAdd) : ℂ) • (weyl N b * weyl N a) := by
  rw [weyl_mul, weyl_mul, smul_smul, mul_comm b a, ← Units.val_mul,
    ← cubicFactor_mul_inv_swap N a b, mul_assoc, inv_mul_cancel, mul_one]
/-- The cubic quantum torus `CubicTorus N` has complex dimension `3 ^ N`. -/
@[simp] theorem finrank_cubicTorus (N : ℕ) : Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [TwistedMonoidAlgebra.finrank_eq_natCard, Nat.card_eq_fintype_card,
    Fintype.card_congr Multiplicative.toAdd, Fintype.card_pi]; simp [ZMod.card]

/-! ### The inversion automorphism and fixed-point star subalgebra -/

/-- The inversion `⋆`-automorphism `θ_N : CubicTorus N →⋆ₐ[ℂ] CubicTorus N` (`W(a) ↦ W(a⁻¹)`). -/
noncomputable def cubicInversion (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus N :=
  mapStarAlgHom (MulEquiv.inv (Multiplicative (Fin N → ZMod 3))).toMonoidHom
    (fun g h ↦ cubicFactor_inv_inv N g h)
@[simp] theorem cubicInversion_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicInversion N (weyl N a) = weyl N a⁻¹ := TwistedMonoidAlgebra.mapStarAlgHom_of _ _ a
@[simp] theorem cubicInversion_involutive (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x :=
  AlgHom.congr_fun (algHom_ext fun g ↦ by simp [← weyl_def] :
    (cubicInversion N).toAlgHom.comp (cubicInversion N).toAlgHom = AlgHom.id ℂ (CubicTorus N)) x
@[simp] theorem scalarTrace_cubicInversion (N : ℕ) (x : CubicTorus N) :
    scalarTrace (cubicFactor N) (cubicInversion N x) = scalarTrace (cubicFactor N) x :=
  LinearMap.congr_fun ((basis ℂ _ (cubicFactor N)).ext fun g ↦ by
    classical
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
      TwistedMonoidAlgebra.basis_apply, ← weyl_def, cubicInversion_weyl]
    simp [weyl_def, TwistedMonoidAlgebra.scalarTrace_of] :
    (scalarTrace (cubicFactor N)).comp (cubicInversion N).toAlgHom.toLinearMap =
      scalarTrace (cubicFactor N)) x
/-- **The inversion-fixed star subalgebra** `C_N = {x ∈ G_N : θ_N x = x}` of complex dimension
`(3 ^ N + 1) / 2`. -/
noncomputable def cubicFixed (N : ℕ) : StarSubalgebra ℂ (CubicTorus N) :=
  StarAlgHom.equalizer (cubicInversion N) (StarAlgHom.id ℂ (CubicTorus N))
@[simp] theorem mem_cubicFixed {N : ℕ} {x : CubicTorus N} :
    x ∈ cubicFixed N ↔ cubicInversion N x = x := Iff.rfl
/-- The inversion-fixed subalgebra `cubicFixed N` has complex dimension `(3 ^ N + 1) / 2`. -/
@[simp] theorem finrank_cubicFixed (N : ℕ) :
    Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  classical
  let G := Multiplicative (Fin N → ZMod 3)
  let b := basis ℂ G (cubicFactor N)
  let eV : CubicTorus N ≃ₗ[ℂ] (G → ℂ) := b.equivFun
  have hinv_repr (x : CubicTorus N) (g : G) : eV (cubicInversion N x) g = eV x g⁻¹ :=
    LinearMap.congr_fun (b.ext fun h ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
        Module.Basis.coord_apply]
      conv_lhs =>
        rw [show b h = weyl N h from TwistedMonoidAlgebra.basis_apply .., cubicInversion_weyl,
          show weyl N h⁻¹ = b h⁻¹ from (TwistedMonoidAlgebra.basis_apply ..).symm]
      simp only [Module.Basis.repr_self, Finsupp.single_apply, inv_eq_iff_eq_inv] :
      (b.coord g).comp (cubicInversion N).toAlgHom.toLinearMap = b.coord g⁻¹) x
  have hinv_eq (g : G) : g⁻¹ = g ↔ g = 1 :=
    ⟨fun h ↦ Multiplicative.toAdd.injective (funext fun i ↦
      (by decide : ∀ z : ZMod 3, -z = z → z = 0) _
        (by simpa [G, toAdd_inv] using congrFun (congrArg Multiplicative.toAdd h) i)),
      fun h ↦ by simp [h]⟩
  let σ := Fintype.equivFin G
  let I : Finset G := Finset.univ.filter fun g ↦ σ g ≤ σ g⁻¹
  have h1I : (1 : G) ∈ I := by simp [I]
  have hI_iff {g : G} (hg : g ≠ 1) : g⁻¹ ∈ I ↔ g ∉ I := by
    have hne : σ g ≠ σ g⁻¹ := fun h ↦ hg ((hinv_eq g).mp (σ.injective h).symm)
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, inv_inv, not_le]
    exact ⟨fun h ↦ lt_of_le_of_ne h hne.symm, le_of_lt⟩
  have hmem_or (g : G) (hg : g ∉ I) : g⁻¹ ∈ I :=
    (hI_iff fun h ↦ hg (by simpa [h] using h1I)).mpr hg
  let eFixed : cubicFixed N ≃ₗ[ℂ] (I → ℂ) :=
    { toFun := fun x i ↦ eV x.1 i.1
      invFun := fun f ↦ ⟨eV.symm fun g ↦ if h : g ∈ I then f ⟨g, h⟩ else f ⟨g⁻¹, hmem_or g h⟩,
        mem_cubicFixed.mpr <| eV.injective <| funext fun g ↦ by
          rw [hinv_repr, eV.apply_symm_apply]
          by_cases hg : g = 1; · subst hg; simp [h1I]
          split_ifs with h1 h2 h3
          · exact absurd h2 ((hI_iff hg).mp h1)
          · rfl
          · exact congrArg f (Subtype.ext (inv_inv g))
          · exact absurd ((hI_iff hg).mpr h3) h1⟩
      map_add' := fun _ _ ↦ funext fun _ ↦ congrFun (eV.map_add _ _) _
      map_smul' := fun _ _ ↦ funext fun _ ↦ congrFun (eV.map_smul _ _) _
      left_inv := fun x ↦ Subtype.ext <| eV.injective <| funext fun g ↦ by
        dsimp only; rw [eV.apply_symm_apply]; split_ifs
        · rfl
        · simpa [hinv_repr] using congrFun (congrArg eV (mem_cubicFixed.mp x.2)) g
      right_inv := fun f ↦ funext fun i ↦ by dsimp only; rw [eV.apply_symm_apply]; simp [i.2] }
  have hcard_G : Fintype.card G = 3 ^ N := by
    rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_pi]; simp [ZMod.card]
  have hbij : (I.erase 1).card = (Finset.univ \ I).card :=
    Finset.card_bij (fun g _ ↦ g⁻¹)
      (fun g hg ↦ by
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and] at hg ⊢
        exact (hI_iff hg.1).not.mpr (not_not.mpr hg.2))
      (fun _ _ _ _ h ↦ inv_injective h)
      (fun g hg ↦ by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hg
        exact ⟨g⁻¹, Finset.mem_erase.mpr ⟨inv_ne_one.mpr fun h ↦ hg (by simpa [h] using h1I),
          hmem_or g hg⟩, inv_inv g⟩)
  have htot : (Finset.univ \ I).card + I.card = Fintype.card G :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
  have herase : (I.erase 1).card + 1 = I.card := Finset.card_erase_add_one h1I
  have hfin : Module.finrank ℂ (cubicFixed N) = I.card := by
    rw [eFixed.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  omega

/-! ### Site unitaries and Jones projections -/

/-- The site unitary `U_j = W(e_j)` at site `j : Fin N`. -/
noncomputable def cubicSite (N : ℕ) (j : Fin N) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd (Pi.single j 1))
theorem cubicSite_def (N : ℕ) (j : Fin N) :
    cubicSite N j = weyl N (Multiplicative.ofAdd (Pi.single j 1)) := (rfl)
@[simp] theorem cubicSite_pow_three (N : ℕ) (j : Fin N) : cubicSite N j ^ 3 = 1 :=
  weyl_pow_three N _
@[simp] theorem star_cubicSite (N : ℕ) (j : Fin N) : star (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_def, star_weyl, weyl_sq]
@[simp] theorem cubicInversion_cubicSite (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_def, cubicInversion_weyl, weyl_sq]
theorem cubicSite_mul_cubicSite_succ {N : ℕ} {i j : Fin N} (hij : (i : ℕ) + 1 = j) :
    cubicSite N i * cubicSite N j = (cubeRootOfUnity : ℂ) • (cubicSite N j * cubicSite N i) := by
  rw [cubicSite_def, cubicSite_def, weyl_mul_comm_factor]; simp [chainForm_single_single_succ hij]
theorem cubicSite_mul_cubicSite_pred {N : ℕ} {i j : Fin N} (hij : (i : ℕ) + 1 = j) :
    cubicSite N j * cubicSite N i =
      ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N i * cubicSite N j) := by
  rw [cubicSite_mul_cubicSite_succ hij, smul_smul, ← pow_succ, cubeRootOfUnity_val_pow_three,
    one_smul]
theorem cubicSite_mul_cubicSite_comm {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    cubicSite N i * cubicSite N j = cubicSite N j * cubicSite N i := by
  rw [cubicSite_def, cubicSite_def, weyl_mul_comm_factor]
  simp [chainForm_single_single_of_dist_ge_two hij]
/-- The Jones projection `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)` at site `j : Fin N`. -/
noncomputable def cubicProjection (N : ℕ) (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)
theorem cubicProjection_def (N : ℕ) (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) := (rfl)
theorem cubicProjection_mem_cubicFixed (N : ℕ) (j : Fin N) :
    cubicProjection N j ∈ cubicFixed N := by
  have h4 : cubicSite N j ^ 4 = cubicSite N j := by rw [pow_succ, cubicSite_pow_three, one_mul]
  rw [mem_cubicFixed, cubicProjection_def, map_smul, map_add, map_add, map_one, map_pow,
    cubicInversion_cubicSite, ← pow_mul, h4]; abel_nf
@[simp] theorem star_cubicProjection (N : ℕ) (j : Fin N) :
    star (cubicProjection N j) = cubicProjection N j := by
  have h4 : cubicSite N j ^ 4 = cubicSite N j := by rw [pow_succ, cubicSite_pow_three, one_mul]
  rw [cubicProjection_def, star_smul, star_add, star_add, star_one, star_pow, star_cubicSite,
    ← pow_mul, h4, show star ((3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ by simp]; abel_nf
theorem isSelfAdjoint_cubicProjection (N : ℕ) (j : Fin N) :
    IsSelfAdjoint (cubicProjection N j) := star_cubicProjection N j
@[simp] theorem cubicSite_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j * cubicProjection N j = cubicProjection N j := by
  rw [cubicProjection_def, mul_smul_comm]
  congr 1; rw [mul_add, mul_add, mul_one, ← sq, ← pow_succ', cubicSite_pow_three]; abel
@[simp] theorem cubicSite_sq_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 * cubicProjection N j = cubicProjection N j := by
  rw [sq, mul_assoc, cubicSite_mul_cubicProjection, cubicSite_mul_cubicProjection]
/-- Each `cubicProjection N j` is idempotent: `p_j * p_j = p_j`. -/
@[simp] theorem cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  conv_lhs => arg 1; rw [cubicProjection_def]
  rw [smul_mul_assoc, add_mul, add_mul, one_mul, cubicSite_mul_cubicProjection,
    cubicSite_sq_mul_cubicProjection, show cubicProjection N j + cubicProjection N j +
      cubicProjection N j = (3 : ℂ) • cubicProjection N j by module, smul_smul]; norm_num
private theorem cubicProjection_mul_weyl_mul_cubicProjection_eq_zero {N : ℕ} (i : Fin N)
    {a : Multiplicative (Fin N → ZMod 3)} (hB : chainForm N (Pi.single i 1) a.toAdd ≠ 0) :
    cubicProjection N i * weyl N a * cubicProjection N i = 0 := by
  set ζ : ℂ := (cubeRootPow (chainForm N (Pi.single i 1) a.toAdd) : ℂ)
  have hζ3 : ζ ^ 3 = 1 := by
    simpa [ζ] using congrArg Units.val (by
      rw [cubeRootPow, ← pow_mul, mul_comm, pow_mul, cubeRootOfUnity_pow_three, one_pow] :
      cubeRootPow (chainForm N (Pi.single i 1) a.toAdd) ^ 3 = 1)
  have hsum : 1 + ζ + ζ ^ 2 = 0 :=
    (mul_eq_zero.mp (by linear_combination hζ3 : (ζ - 1) * (1 + ζ + ζ ^ 2) = 0)).resolve_left
      (sub_ne_zero.mpr fun h ↦ hB (cubeRootPow_eq_one_iff.mp (Units.ext h)))
  have hcomm : cubicSite N i * weyl N a = ζ • (weyl N a * cubicSite N i) := by
    simpa [cubicSite_def, ζ] using weyl_mul_comm_factor N (Multiplicative.ofAdd (Pi.single i 1)) a
  have hcomm2 : cubicSite N i ^ 2 * weyl N a = (ζ ^ 2) • (weyl N a * cubicSite N i ^ 2) := by
    rw [sq, mul_assoc, hcomm, mul_smul_comm, ← mul_assoc, hcomm, smul_mul_assoc, smul_smul,
      ← sq, mul_assoc, ← sq]
  conv_lhs => arg 1; arg 1; rw [cubicProjection_def N i]
  rw [smul_mul_assoc, smul_mul_assoc]
  simp only [add_mul, one_mul, hcomm, hcomm2, smul_mul_assoc, mul_assoc,
    cubicSite_mul_cubicProjection, cubicSite_sq_mul_cubicProjection]
  rw [show weyl N a * cubicProjection N i + ζ • (weyl N a * cubicProjection N i) +
      (ζ ^ 2) • (weyl N a * cubicProjection N i) =
      (1 + ζ + ζ ^ 2) • (weyl N a * cubicProjection N i) by module, hsum, zero_smul, smul_zero]
/-- Adjacent Jones projections satisfy `p_i * p_j * p_i = 3⁻¹ • p_i`. -/
theorem cubicProjection_mul_cubicProjection_mul_cubicProjection {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cubicProjection N i * cubicProjection N j * cubicProjection N i =
      (3 : ℂ)⁻¹ • cubicProjection N i := by
  have hB : chainForm N (Pi.single i 1) (Pi.single j 1) ≠ 0 := by
    rcases hij with h | h
    · rw [chainForm_single_single_succ h]; decide
    · rw [chainForm_swap, chainForm_single_single_succ h]; decide
  have hU := cubicProjection_mul_weyl_mul_cubicProjection_eq_zero i
    (a := Multiplicative.ofAdd (Pi.single j 1)) (by simpa using hB)
  have hU2 := cubicProjection_mul_weyl_mul_cubicProjection_eq_zero i
    (a := (Multiplicative.ofAdd (Pi.single j 1))⁻¹)
    (by simpa [chainForm_neg_right] using neg_ne_zero.mpr hB)
  rw [cubicProjection_def N j, cubicSite_def, weyl_sq, mul_smul_comm, smul_mul_assoc]
  simp only [mul_add, mul_one, add_mul, cubicProjection_mul_self, hU, hU2, add_zero]
/-- Distant Jones projections commute when `|i - j| ≥ 2`. -/
theorem cubicProjection_mul_cubicProjection_comm {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    cubicProjection N i * cubicProjection N j = cubicProjection N j * cubicProjection N i := by
  have hc : Commute (cubicSite N i) (cubicSite N j) := cubicSite_mul_cubicSite_comm hij
  simp only [cubicProjection_def, smul_mul_assoc, mul_smul_comm]; congr 1
  simp only [add_mul, mul_add, one_mul, mul_one, hc.eq, (hc.pow_right 2).eq, (hc.pow_left 2).eq,
    ((hc.pow_left 2).pow_right 2).eq]; abel_nf
@[simp] theorem scalarTrace_cubicProjection (N : ℕ) (j : Fin N) :
    scalarTrace (cubicFactor N) (cubicProjection N j) = (3 : ℂ)⁻¹ := by
  have h1 : Multiplicative.ofAdd (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) ≠ 1 := fun h ↦ by
    have := congrFun (congrArg Multiplicative.toAdd h) j; simp at this
  rw [cubicProjection_def, map_smul, map_add, map_add, TwistedMonoidAlgebra.scalarTrace_one,
    cubicSite_def, weyl_sq, weyl_def, weyl_def, TwistedMonoidAlgebra.scalarTrace_of_ne_one _ h1,
    TwistedMonoidAlgebra.scalarTrace_of_ne_one _ (inv_ne_one.mpr h1)]; simp

/-! ### The Temperley–Lieb comparison homomorphism and its surjectivity -/

/-- The `⋆`-algebra comparison map `F_m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)`
sending `e (√3 : ℂ) j` to `(√3 : ℂ) • cubicProjection (m - 1) j`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1) :=
  let f : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
    TemperleyLieb.lift
      (fun j ↦ ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
        StarSubalgebra.smul_mem _ (cubicProjection_mem_cubicFixed (m - 1) j) _⟩)
      (fun j ↦ Subtype.ext <| by
        simp only [MulMemClass.coe_mul, SetLike.val_smul, smul_mul_smul_comm,
          cubicProjection_mul_self, sqrt_three_coe_mul_self, smul_smul])
      (fun {i j} hij ↦ Subtype.ext <| by
        simp only [MulMemClass.coe_mul, smul_mul_smul_comm,
          cubicProjection_mul_cubicProjection_mul_cubicProjection hij, smul_smul]
        congr 1; linear_combination ((Real.sqrt 3 : ℂ) * (3 : ℂ)⁻¹) * sqrt_three_coe_mul_self)
      (fun {i j} hij ↦ Subtype.ext <| by
        simp only [MulMemClass.coe_mul, smul_mul_smul_comm,
          cubicProjection_mul_cubicProjection_comm hij])
  { f with
    map_star' := TemperleyLieb.map_star_iff.mpr fun j ↦ Subtype.ext <| by
      simp only [f, TemperleyLieb.lift_e, StarMemClass.coe_star, star_smul,
        Complex.star_def, Complex.conj_ofReal, star_cubicProjection] }
@[simp] theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by simp [cubicFixedHom]
@[simp] theorem cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedHom m (star x) = star (cubicFixedHom m x) := map_star (cubicFixedHom m) x
private noncomputable def symWeyl (N : ℕ) (a : Fin N → ZMod 3) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd a) + weyl N (Multiplicative.ofAdd (-a))
private theorem symWeyl_mul_symWeyl (N : ℕ) (u v : Fin N → ZMod 3) :
    symWeyl N u * symWeyl N v =
      (cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v) : ℂ) • symWeyl N (u + v) +
        (((cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))⁻¹ : ℂˣ) : ℂ) •
          symWeyl N (u - v) := by
  have h1 : cubicFactor N (Multiplicative.ofAdd (-u)) (Multiplicative.ofAdd (-v)) =
      cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v) := by simp [cubicFactor_def]
  have h2 : cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd (-v)) =
      (cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))⁻¹ := by
    simp [cubicFactor_def, mul_neg]
  have h3 : cubicFactor N (Multiplicative.ofAdd (-u)) (Multiplicative.ofAdd v) =
      (cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))⁻¹ := by
    simp [cubicFactor_def, mul_neg]
  simp only [symWeyl, add_mul, mul_add, weyl_mul, h1, h2, h3, ← ofAdd_add]
  rw [show -u + -v = -(u + v) by abel, show u + -v = u - v from (sub_eq_add_neg u v).symm,
    show -u + v = -(u - v) by abel, smul_add, smul_add]; abel
private theorem symWeyl_add_and_sub_mem {N : ℕ} {S : Subalgebra ℂ (CubicTorus N)}
    {u v : Fin N → ZMod 3} (hu : symWeyl N u ∈ S) (hv : symWeyl N v ∈ S)
    (hB : chainForm N u v ≠ 0) : symWeyl N (u + v) ∈ S ∧ symWeyl N (u - v) ∈ S := by
  set β : ℂˣ := cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v)
  have hmul1 := symWeyl_mul_symWeyl N u v
  have hmul2 : symWeyl N v * symWeyl N u =
      ((β⁻¹ : ℂˣ) : ℂ) • symWeyl N (u + v) + (β : ℂ) • symWeyl N (u - v) := by
    rw [symWeyl_mul_symWeyl N v u, cubicFactor_swap N (Multiplicative.ofAdd u), inv_inv,
      add_comm v u, show v - u = -(u - v) by abel,
      show symWeyl N (-(u - v)) = symWeyl N (u - v) by simp [symWeyl, add_comm]]
  have hβ_ne : (β : ℂ) ≠ 1 := fun h ↦ hB <| by
    have h2 : 2 * chainForm N u v = 0 := cubeRootPow_eq_one_iff.mp (Units.ext h)
    simpa [← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide] using congrArg ((2 : ZMod 3) * ·) h2
  have hβ3 : (β : ℂ) ^ 3 = 1 := by
    simpa [β, cubicFactor_def] using congrArg Units.val (by
      rw [cubeRootPow, ← pow_mul, mul_comm, pow_mul, cubeRootOfUnity_pow_three, one_pow] :
      cubeRootPow (2 * chainForm N u v) ^ 3 = 1)
  have hdet : (β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2 ≠ 0 := fun h0 ↦ hβ_ne <| by
    have hmul : ((β : ℂ) * ((β⁻¹ : ℂˣ) : ℂ)) ^ 2 = 1 := by simp
    linear_combination hmul + (β : ℂ) ^ 2 * sub_eq_zero.mp h0 - (β : ℂ) * hβ3
  have solve (w x y : CubicTorus N) (hx : x ∈ S) (hy : y ∈ S)
      (heq : ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2) • w = (β : ℂ) • x - ((β⁻¹ : ℂˣ) : ℂ) • y) :
      w ∈ S := by
    have hm := S.smul_mem (heq ▸ sub_mem (S.smul_mem hx _) (S.smul_mem hy _))
      ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at hm
  exact ⟨solve _ _ _ (S.mul_mem hu hv) (S.mul_mem hv hu) (by rw [hmul1, hmul2]; module),
    solve _ _ _ (S.mul_mem hv hu) (S.mul_mem hu hv) (by rw [hmul1, hmul2]; module)⟩
/-- **Surjectivity of `cubicFixedHom m`** for every `m : ℕ`. -/
theorem cubicFixedHom_surjective (m : ℕ) : Function.Surjective (cubicFixedHom m) := by
  set N := m - 1
  set S : Subalgebra ℂ (CubicTorus N) :=
    ((cubicFixed N).val.comp (cubicFixedHom m).toAlgHom).range
  have hsingle (j : Fin N) : symWeyl N (Pi.single j 1) ∈ S := by
    have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hp : cubicProjection N j ∈ S := by
      have hm := S.smul_mem (⟨e (Real.sqrt 3 : ℂ) j, coe_cubicFixedHom_e m j⟩ :
        (Real.sqrt 3 : ℂ) • cubicProjection N j ∈ S) (Real.sqrt 3 : ℂ)⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hsqrt, one_smul] at hm
    have h : symWeyl N (Pi.single j 1) = (3 : ℂ) • cubicProjection N j - 1 := by
      rw [cubicProjection_def, smul_smul]; norm_num
      rw [symWeyl, ofAdd_neg, ← weyl_sq, ← cubicSite_def]; abel
    exact h ▸ sub_mem (S.smul_mem hp _) S.one_mem
  have hsingle_smul (j : Fin N) (c : ZMod 3) (hc : c ≠ 0) :
      symWeyl N (c • Pi.single j 1) ∈ S := by
    rcases zmod3_cases c with rfl | rfl | rfl
    · exact absurd rfl hc
    · rw [one_smul]; exact hsingle j
    · rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul,
        show symWeyl N (-(Pi.single j 1)) = symWeyl N (Pi.single j 1) by simp [symWeyl, add_comm]]
      exact hsingle j
  have hchain_lt {k : ℕ} (hk : k + 1 < N) {a' : Fin N → ZMod 3}
      (ha' : ∀ i : Fin N, k + 1 ≤ i.val → a' i = 0) :
      chainForm N a' (Pi.single ⟨k + 1, hk⟩ 1) = a' ⟨k, by omega⟩ := by
    rw [chainForm_single_right]; simp only [Nat.succ_pos', ↓reduceDIte, Nat.add_sub_cancel]
    split_ifs with hlt
    · rw [ha' ⟨k + 2, hlt⟩ (by dsimp; omega), sub_zero]
    · simp
  have hind : ∀ k ≤ N, ∀ a : Fin N → ZMod 3,
      (∀ i : Fin N, k ≤ i.val → a i = 0) → symWeyl N a ∈ S := by
    intro k; induction k with
    | zero =>
      intro _ a ha
      rw [show a = 0 from funext fun i ↦ ha i (Nat.zero_le _),
        show symWeyl N 0 = (2 : ℂ) • (1 : CubicTorus N) by simp [symWeyl, two_smul]]
      exact S.smul_mem S.one_mem _
    | succ k ih =>
      intro hk a ha; have hkN : k < N := by omega
      set ek : Fin N → ZMod 3 := Pi.single ⟨k, hkN⟩ 1
      set c : ZMod 3 := a ⟨k, hkN⟩; set a' : Fin N → ZMod 3 := a - c • ek
      have ha'supp : ∀ i : Fin N, k ≤ i.val → a' i = 0 := fun i hi ↦ by
        by_cases hik : i.val = k
        · obtain rfl : i = ⟨k, hkN⟩ := Fin.ext hik; simp [a', ek, c]
        · simp [a', ek, ha i (by omega),
            Pi.single_eq_of_ne (show i ≠ ⟨k, hkN⟩ from fun h ↦ hik (congrArg Fin.val h))]
      have ha'mem : symWeyl N a' ∈ S := ih (by omega) a' ha'supp
      have ha_eq : a = a' + c • ek := by simp [a']
      by_cases hc : c = 0; · rwa [ha_eq, hc, zero_smul, add_zero]
      have hcek : symWeyl N (c • ek) ∈ S := hsingle_smul ⟨k, hkN⟩ c hc
      cases k with
      | zero => rwa [ha_eq, show a' = 0 from funext fun i ↦ ha'supp i (Nat.zero_le _), zero_add]
      | succ p =>
        set ep : Fin N → ZMod 3 := Pi.single ⟨p, by omega⟩ 1
        have hB_a' : chainForm N a' ek = a' ⟨p, by omega⟩ := hchain_lt hkN ha'supp
        by_cases hap : a' ⟨p, by omega⟩ ≠ 0
        · exact ha_eq ▸ (symWeyl_add_and_sub_mem ha'mem hcek (by
            rw [chainForm_smul_right, hB_a']
            exact (by decide : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → x * y ≠ 0) _ _ hc hap)).1
        · push Not at hap; set v : Fin N → ZMod 3 := a' + ep
          have hvsupp : ∀ i : Fin N, p + 1 ≤ i.val → v i = 0 := fun i hi ↦ by
            simp [v, ep, Pi.single_eq_of_ne (show i ≠ ⟨p, by omega⟩ from fun h ↦ by
              have := congrArg Fin.val h; dsimp at this; omega), ha'supp i hi]
          have hB_v : chainForm N v ek = 1 := by rw [hchain_lt hkN hvsupp]; simp [v, ep, hap]
          have hstep (d : ZMod 3) (hd : d ≠ 0) : symWeyl N (v + d • ek) ∈ S :=
            (symWeyl_add_and_sub_mem (ih (by omega) v hvsupp) (hsingle_smul ⟨p + 1, hkN⟩ d hd)
              (by rwa [chainForm_smul_right, hB_v, mul_one])).1
          have hB_step (d : ZMod 3) : chainForm N (v + d • ek) ep = chainForm N a' ep - d := by
            rw [chainForm_add_left, chainForm_add_left, chainForm_self, add_zero,
              chainForm_smul_left, chainForm_swap N ep ek,
              show chainForm N ep ek = 1 from chainForm_single_single_succ rfl]; ring
          by_cases hcase : chainForm N a' ep ≠ c
          · rw [show a = v + c • ek - ep by rw [ha_eq]; simp only [v]; abel]
            exact (symWeyl_add_and_sub_mem (hstep c hc) (hsingle ⟨p, by omega⟩)
              (by rw [hB_step]; exact sub_ne_zero.mpr hcase)).2
          · push Not at hcase
            have hminus : symWeyl N (a' - c • ek) ∈ S := by
              rw [show a' - c • ek = v + (-c) • ek - ep by simp only [v, neg_smul]; abel]
              exact (symWeyl_add_and_sub_mem (hstep (-c) (neg_ne_zero.mpr hc))
                (hsingle ⟨p, by omega⟩) (by
                  rw [hB_step, hcase, sub_neg_eq_add]
                  exact (by decide : ∀ x : ZMod 3, x ≠ 0 → x + x ≠ 0) c hc)).2
            have hprod : symWeyl N a' * symWeyl N (c • ek) =
                symWeyl N (a' + c • ek) + symWeyl N (a' - c • ek) := by
              rw [symWeyl_mul_symWeyl]; simp [cubicFactor_def, chainForm_smul_right, hB_a', hap]
            rw [show symWeyl N a = symWeyl N a' * symWeyl N (c • ek) - symWeyl N (a' - c • ek) by
              rw [ha_eq, hprod]; abel]
            exact sub_mem (S.mul_mem ha'mem hcek) hminus
  intro y
  have hy_mem : y.1 ∈ S := by
    let b := basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
    rw [show y.1 = (2 : ℂ)⁻¹ • (y.1 + cubicInversion N y.1) by
      rw [show cubicInversion N y.1 = y.1 from y.2, ← two_smul ℂ, smul_smul]; norm_num]
    refine S.smul_mem ?_ _
    have hsum : y.1 + cubicInversion N y.1 = (b.repr y.1).sum fun g z ↦ z • symWeyl N g.toAdd := by
      conv_lhs => rw [← b.linearCombination_repr y.1]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, map_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ ↦ by
        simp only [b, TwistedMonoidAlgebra.basis_apply, ← weyl_def, map_smul, cubicInversion_weyl,
          symWeyl, ← smul_add]; rfl
    rw [hsum, Finsupp.sum]
    exact S.sum_mem fun g _ ↦ S.smul_mem (hind N le_rfl g.toAdd fun i hi ↦
      absurd i.2 (not_lt.mpr hi)) _
  exact let ⟨x, hx⟩ := hy_mem; ⟨x, Subtype.ext hx⟩

end TauCeti.TemperleyLieb
