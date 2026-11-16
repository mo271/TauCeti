/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.SelfAdjoint
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Cartan involutions and the Cartan decomposition of a Lie algebra

Let `θ` be an automorphism of a Lie algebra `L` over a commutative ring `R`. Its `+1`-eigenspace is
the fixed Lie subalgebra `𝔨 = θ.toLieHom.fixedSubalgebra`, and its `-1`-eigenspace is the submodule
`𝔭 = θ.cartanP = ker (θ + id)`. Because `θ` preserves Lie brackets, the eigenspaces satisfy the
parity relations `[𝔨, 𝔭] ⊆ 𝔭`, `[𝔭, 𝔭] ⊆ 𝔨`, and `[𝔭, [𝔭, 𝔭]] ⊆ 𝔭`, making `𝔭` both a Lie
submodule over `𝔨` (`LieEquiv.cartanPLieSubmodule`) and a Lie triple system. Whenever `2` is
invertible in `R`, `𝔨` and `𝔭` are orthogonal for the Killing form `B`, and if `θ` is involutive
then `L = 𝔨 ⊕ 𝔭` (`LieEquiv.isCompl_fixedSubalgebra_cartanP`).

Twisting the Killing form by `θ` defines the bilinear form `B_θ (x, y) = -B (x, θ y)`
(`LieEquiv.cartanBilinForm`). When `θ` is involutive, `B_θ` is symmetric, `θ`-invariant, makes `𝔨`
and `𝔭` orthogonal, and satisfies the adjoint identity `B_θ ⁅x, y⁆ z = -B_θ y ⁅θ x, z⁆`. Thus
`ad x` is `B_θ`-skew-adjoint for `x ∈ 𝔨` and `B_θ`-self-adjoint for `x ∈ 𝔭`.

Over an ordered ring, `θ` is a **Cartan involution** (`LieEquiv.IsCartanInvolution`) when it is
involutive and `0 < -B (x, θ x)` for every nonzero `x : L`, equivalently when `B_θ` is positive
definite. Over an ordered field `K`, the existence of a Cartan involution forces `B_θ` and hence
`B` to be nondegenerate, so `L` is automatically Killing, finite-dimensional, semisimple, and
centreless, with no separate finiteness or semisimplicity hypotheses needed. Moreover:

* `B` is negative definite on `𝔨` and positive definite on `𝔭`;
* restricting `B_θ` to `𝔨` equips `𝔨` with a positive definite `𝔨`-invariant symmetric form, so `𝔨`
  is compact reductive (`𝔨 = Z(𝔨) ⊕ [𝔨, 𝔨]` with `[𝔨, 𝔨]` semisimple and negative-definite
  intrinsic Killing form); and
* over `ℝ`, `B_θ` packages as `InnerProductSpace.Core ℝ L` and `ad x` is diagonalizable over `ℝ`
  (hence semisimple) for every `x ∈ 𝔭`.

## Main definitions

* `LieEquiv.cartanP`: the `-1`-eigenspace `ker (θ + id)` of `θ : L ≃ₗ⁅R⁆ L`.
* `LieEquiv.cartanPLieSubmodule`: `θ.cartanP` as a `LieSubmodule` over `θ.toLieHom.fixedSubalgebra`.
* `LieEquiv.cartanBilinForm`: the twisted Killing form `B_θ (x, y) = -killingForm R L x (θ y)`.
* `LieEquiv.IsCartanInvolution`: involutive `θ` with strictly positive `-B (x, θ x)` for `x ≠ 0`.
* `LieEquiv.IsCartanInvolution.innerProductCore`: `B_θ` packaged as `InnerProductSpace.Core ℝ L`.

## Main statements

* `LieEquiv.isCompl_fixedSubalgebra_cartanP`: the Cartan decomposition `L = 𝔨 ⊕ 𝔭` when `2` is
  invertible and `θ` is involutive.
* `LieEquiv.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP` and
  `LieEquiv.cartanBilinForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP`: orthogonality of `𝔨`
  and `𝔭` for both `B` and `B_θ`.
* `LieEquiv.ad_mem_skewAdjointSubmodule_cartanBilinForm` and
  `LieEquiv.ad_mem_selfAdjointSubmodule_cartanBilinForm`: `ad x` is `B_θ`-skew-adjoint on `𝔨` and
  `B_θ`-self-adjoint on `𝔭`.
* `LieEquiv.IsCartanInvolution.isKilling`, `LieEquiv.IsCartanInvolution.finiteDimensional`,
  `LieEquiv.IsCartanInvolution.isSemisimple`, and `LieEquiv.IsCartanInvolution.center_eq_bot`: a Lie
  algebra admitting a Cartan involution over an ordered field is finite-dimensional and semisimple.
* `LieEquiv.IsCartanInvolution.hasCentralRadical_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`, and
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg`: compact
  reductive structure of `𝔨`.
* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top_of_mem_cartanP` and
  `LieEquiv.IsCartanInvolution.isSemisimple_ad_of_mem_cartanP`: real diagonalizability and
  semisimplicity of `ad x` for `x ∈ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–§2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, §7.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer, 2012, §12.1 and
  §13.1.
-/

public section

open LieAlgebra

namespace LieEquiv

section CommRing

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-! ### The `-1`-eigenspace `cartanP` and bracket parity -/

/-- The `-1`-eigenspace `𝔭 = {x ∈ L | θ x = -x}` of a Lie algebra automorphism `θ : L ≃ₗ⁅R⁆ L`,
defined as `ker (θ + id)`. -/
def cartanP (θ : L ≃ₗ⁅R⁆ L) : Submodule R L :=
  LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id)

/-- Definitional characterization of `LieEquiv.cartanP` as `ker (θ + id)`. -/
theorem cartanP_def (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanP = LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id) :=
  (rfl)

/-- A vector lies in `θ.cartanP` if and only if `θ` negates it. -/
@[simp]
theorem mem_cartanP_iff {θ : L ≃ₗ⁅R⁆ L} {x : L} :
    x ∈ θ.cartanP ↔ θ x = -x := by
  rw [cartanP_def, LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe,
    coe_toLinearEquiv, LinearMap.id_apply, add_eq_zero_iff_eq_neg]

@[simp]
theorem apply_coe_cartanP (θ : L ≃ₗ⁅R⁆ L) (x : θ.cartanP) :
    θ (x : L) = -x :=
  mem_cartanP_iff.mp x.2

/-- The `-1`-eigenspace of `θ⁻¹` coincides with that of `θ`. -/
@[simp]
theorem cartanP_symm (θ : L ≃ₗ⁅R⁆ L) : θ.symm.cartanP = θ.cartanP := by
  ext x
  rw [mem_cartanP_iff, mem_cartanP_iff, symm_apply_eq, map_neg, eq_neg_iff_add_eq_zero, add_comm,
    ← eq_neg_iff_add_eq_zero]

/-- The `+1`-eigenspace `θ.toLieHom.fixedSubalgebra` has underlying submodule `ker (θ - id)`. -/
theorem fixedSubalgebra_toSubmodule_eq_ker (θ : L ≃ₗ⁅R⁆ L) :
    θ.toLieHom.fixedSubalgebra.toSubmodule = LinearMap.ker ((θ : L →ₗ[R] L) - LinearMap.id) := by
  rw [LieHom.fixedSubalgebra_toSubmodule]
  exact LinearMap.fixedSubmodule_eq_ker (θ : L →ₗ[R] L)

/-- An intertwining Lie homomorphism carries `cartanP` into `cartanP`. -/
theorem _root_.LieHom.apply_mem_cartanP {θ₁ : L ≃ₗ⁅R⁆ L} {θ₂ : M ≃ₗ⁅R⁆ M} (u : L →ₗ⁅R⁆ M)
    (h : θ₂.toLieHom.comp u = u.comp θ₁.toLieHom) {x : L} (hx : x ∈ θ₁.cartanP) :
    u x ∈ θ₂.cartanP := by
  rw [mem_cartanP_iff] at hx ⊢
  calc θ₂ (u x) = u (θ₁ x) := LieHom.congr_fun h x
    _ = u (-x) := congrArg u hx
    _ = -u x := map_neg u x

/-- An intertwining Lie equivalence maps `cartanP` onto `cartanP`. -/
theorem map_cartanP {θ₁ : L ≃ₗ⁅R⁆ L} {θ₂ : M ≃ₗ⁅R⁆ M} (e : L ≃ₗ⁅R⁆ M)
    (h : θ₂.toLieHom.comp e.toLieHom = e.toLieHom.comp θ₁.toLieHom) :
    θ₁.cartanP.map (e : L →ₗ[R] M) = θ₂.cartanP := by
  ext y
  rw [Submodule.mem_map]
  refine ⟨?_, fun hy ↦ ⟨e.symm y, ?_, e.apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact e.toLieHom.apply_mem_cartanP h hx
  · exact e.symm.toLieHom.apply_mem_cartanP (e.symm_intertwines h) hy

/-- **`[𝔨, 𝔭] ⊆ 𝔭`.** Bracketing a `θ`-fixed element with a `θ`-negated element produces a
`θ`-negated element. -/
theorem lie_mem_cartanP_left {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  rw [mem_cartanP_iff, θ.map_lie, hx', mem_cartanP_iff.mp hy, lie_neg]

/-- **`[𝔭, 𝔨] ⊆ 𝔭`.** Bracketing a `θ`-negated element with a `θ`-fixed element produces a
`θ`-negated element. -/
theorem lie_mem_cartanP_right {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  have hy' : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [mem_cartanP_iff, θ.map_lie, mem_cartanP_iff.mp hx, hy', neg_lie]

/-- **`[𝔭, 𝔭] ⊆ 𝔨`.** The bracket of two `θ`-negated elements is fixed by `θ`. -/
theorem lie_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.toLieHom.fixedSubalgebra := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, θ.map_lie, mem_cartanP_iff.mp hx,
    mem_cartanP_iff.mp hy, neg_lie, lie_neg, neg_neg]

/-- **`[𝔭, [𝔭, 𝔭]] ⊆ 𝔭`.** The `-1`-eigenspace `θ.cartanP` is closed under double brackets, so it
forms a Lie triple system inside `L`. -/
theorem lie_lie_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y z : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.cartanP) (hz : z ∈ θ.cartanP) :
    ⁅x, ⁅y, z⁆⁆ ∈ θ.cartanP :=
  lie_mem_cartanP_right hx (lie_mem_fixedSubalgebra_of_mem_cartanP hy hz)

/-- The `-1`-eigenspace `θ.cartanP` packaged as a Lie submodule of `L` over the fixed Lie
subalgebra `θ.toLieHom.fixedSubalgebra`, recording the isotropy representation of `𝔨` on `𝔭`. -/
def cartanPLieSubmodule (θ : L ≃ₗ⁅R⁆ L) : LieSubmodule R θ.toLieHom.fixedSubalgebra L where
  __ := θ.cartanP
  lie_mem {x _} hy := lie_mem_cartanP_left x.2 hy

@[simp]
theorem cartanPLieSubmodule_toSubmodule (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanPLieSubmodule.toSubmodule = θ.cartanP :=
  (rfl)

@[simp]
theorem mem_cartanPLieSubmodule_iff {θ : L ≃ₗ⁅R⁆ L} {x : L} :
    x ∈ θ.cartanPLieSubmodule ↔ x ∈ θ.cartanP :=
  Iff.rfl

/-! ### Direct-sum decomposition and Killing orthogonality -/

section InvertibleTwo

variable [Invertible (2 : R)]

@[simp]
theorem cartanP_refl : (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  rw [mem_cartanP_iff, refl_apply] at hx
  have h2 : (2 : R) • x = 0 := by rw [two_smul, ← eq_neg_iff_add_eq_zero]; exact hx
  simpa [← mul_smul, invOf_mul_self] using congrArg (⅟(2 : R) • ·) h2

/-- Away from characteristic `2`, the `+1`- and `-1`-eigenspaces of `θ` meet trivially. -/
theorem disjoint_fixedSubalgebra_cartanP (θ : L ≃ₗ⁅R⁆ L) :
    Disjoint θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  have h1 : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  have h2 : θ x = -x := mem_cartanP_iff.mp hy
  have hsum : (2 : R) • x = 0 := by
    rw [two_smul, ← eq_neg_iff_add_eq_zero]
    exact h1.symm.trans h2
  simpa [← mul_smul, invOf_mul_self] using congrArg (⅟(2 : R) • ·) hsum

/-- **Cartan decomposition `L = 𝔨 ⊕ 𝔭`.** For an involutive Lie algebra automorphism `θ` over a
commutative ring in which `2` is invertible, the fixed subalgebra `𝔨` and the `-1`-eigenspace `𝔭`
are complementary submodules. -/
theorem isCompl_fixedSubalgebra_cartanP {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP := by
  refine ⟨θ.disjoint_fixedSubalgebra_cartanP, codisjoint_iff.mpr (eq_top_iff.mpr fun x _ ↦ ?_)⟩
  refine Submodule.mem_sup.mpr ⟨⅟(2 : R) • (x + θ x), ?_, ⅟(2 : R) • (x - θ x), ?_, ?_⟩
  · rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_fixedSubalgebra, coe_toLieHom, map_smul,
      map_add, hθ x, add_comm]
  · rw [mem_cartanP_iff, map_smul, map_sub, hθ x, ← smul_neg, neg_sub]
  · rw [← smul_add, add_add_sub_cancel, ← two_smul R x, ← mul_smul, invOf_mul_self, one_smul]

/-- Away from characteristic `2`, `𝔨` and `𝔭` are orthogonal with respect to the Killing form. -/
theorem killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    killingForm R L x y = 0 := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  have hinv := killingForm_of_equiv_apply θ x y
  rw [hx', mem_cartanP_iff.mp hy, map_neg] at hinv
  have h2 : (2 : R) * killingForm R L x y = 0 := by
    rw [two_mul, ← eq_neg_iff_add_eq_zero]
    exact hinv.symm
  simpa [← mul_assoc, invOf_mul_self] using congrArg (⅟(2 : R) * ·) h2

/-- Symmetric companion to `killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP`. -/
theorem killingForm_eq_zero_of_mem_cartanP_of_mem_fixedSubalgebra (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    killingForm R L x y = 0 := by
  rw [LieModule.traceForm_comm]
  exact θ.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hy hx

end InvertibleTwo

/-! ### The twisted Killing form `B_θ (x, y) = -B (x, θ y)` -/

/-- The bilinear form `B_θ (x, y) = -killingForm R L x (θ y)` obtained by twisting the Killing
form by `θ : L ≃ₗ⁅R⁆ L`. -/
noncomputable def cartanBilinForm (θ : L ≃ₗ⁅R⁆ L) : LinearMap.BilinForm R L :=
  -(killingForm R L).compl₁₂ LinearMap.id (θ : L →ₗ[R] L)

@[simp]
theorem cartanBilinForm_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanBilinForm x y = -killingForm R L x (θ y) :=
  (rfl)

/-- On the fixed subalgebra `𝔨` in the right slot, `B_θ` agrees with `-B`. -/
theorem cartanBilinForm_eq_neg_killingForm_of_mem_fixedSubalgebra (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    θ.cartanBilinForm x y = -killingForm R L x y := by
  rw [cartanBilinForm_apply, ← coe_toLieHom, LieHom.mem_fixedSubalgebra.mp hy]

/-- On `θ.cartanP` in the right slot, `B_θ` agrees with `B`. -/
theorem cartanBilinForm_eq_killingForm_of_mem_cartanP (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hy : y ∈ θ.cartanP) :
    θ.cartanBilinForm x y = killingForm R L x y := by
  rw [cartanBilinForm_apply, mem_cartanP_iff.mp hy, map_neg, neg_neg]

/-- Away from characteristic `2`, `𝔨` and `𝔭` are orthogonal with respect to `B_θ`. -/
theorem cartanBilinForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [Invertible (2 : R)]
    (θ : L ≃ₗ⁅R⁆ L) {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    θ.cartanBilinForm x y = 0 := by
  rw [θ.cartanBilinForm_eq_killingForm_of_mem_cartanP hy,
    θ.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy]

/-- For an involutive automorphism `θ`, the twisted Killing form `B_θ` is symmetric. -/
theorem isSymm_cartanBilinForm_of_involutive {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    θ.cartanBilinForm.IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ by
    rw [cartanBilinForm_apply, cartanBilinForm_apply, neg_inj,
      ← killingForm_of_equiv_apply θ x (θ y), hθ y, LieModule.traceForm_comm]

/-- Every Lie algebra automorphism `θ` preserves its own twisted Killing form `B_θ`. -/
theorem cartanBilinForm_apply_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanBilinForm (θ x) (θ y) = θ.cartanBilinForm x y := by
  rw [cartanBilinForm_apply, cartanBilinForm_apply, killingForm_of_equiv_apply θ x (θ y)]

/-- Intertwining Lie equivalences preserve the twisted Killing form `B_θ`; in particular every
automorphism commuting with `θ` is `B_θ`-orthogonal. -/
theorem cartanBilinForm_equiv_apply {θ₁ : L ≃ₗ⁅R⁆ L} {θ₂ : M ≃ₗ⁅R⁆ M} (e : L ≃ₗ⁅R⁆ M)
    (h : θ₂.toLieHom.comp e.toLieHom = e.toLieHom.comp θ₁.toLieHom) (x y : L) :
    θ₂.cartanBilinForm (e x) (e y) = θ₁.cartanBilinForm x y := by
  have hey : θ₂ (e y) = e (θ₁ y) := LieHom.congr_fun h y
  rw [cartanBilinForm_apply, cartanBilinForm_apply, hey, killingForm_of_equiv_apply]

/-- **Twisted adjoint invariance.** For involutive `θ`, the adjoint of `ad x` with respect to
`B_θ` is `-ad (θ x)`: `B_θ ⁅x, y⁆ z = -B_θ y ⁅θ x, z⁆`. -/
theorem cartanBilinForm_ad_left {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) (x y z : L) :
    θ.cartanBilinForm ⁅x, y⁆ z = -θ.cartanBilinForm y ⁅θ x, z⁆ := by
  have hθlie : θ ⁅θ x, z⁆ = ⁅x, θ z⁆ := by rw [θ.map_lie, hθ x]
  rw [cartanBilinForm_apply, cartanBilinForm_apply, neg_neg, hθlie, ← lie_skew x y,
    LinearMap.map_neg₂, neg_neg, LieModule.traceForm_apply_lie_apply]

/-- For involutive `θ` and `x ∈ 𝔨`, `ad x` is skew-adjoint with respect to `B_θ`. -/
theorem ad_mem_skewAdjointSubmodule_cartanBilinForm {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ)
    {x : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) :
    ad R L x ∈ θ.cartanBilinForm.skewAdjointSubmodule := by
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro y z
  simp only [Pi.neg_apply, ad_apply, map_neg]
  rw [cartanBilinForm_ad_left hθ, ← coe_toLieHom, LieHom.mem_fixedSubalgebra.mp hx]

/-- For involutive `θ` and `x ∈ 𝔭`, `ad x` is self-adjoint with respect to `B_θ`. -/
theorem ad_mem_selfAdjointSubmodule_cartanBilinForm {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ)
    {x : L} (hx : x ∈ θ.cartanP) :
    ad R L x ∈ θ.cartanBilinForm.selfAdjointSubmodule := by
  rw [LinearMap.mem_selfAdjointSubmodule]
  intro y z
  simp only [ad_apply]
  rw [cartanBilinForm_ad_left hθ, mem_cartanP_iff.mp hx, neg_lie, map_neg, neg_neg]

/-- Restricting `B_θ` to the fixed subalgebra `𝔨` coincides with pulling back `-killingForm R L`
along the inclusion of `𝔨`, hence is a `𝔨`-invariant bilinear form on `𝔨`. -/
theorem lieInvariant_restrict_cartanBilinForm_fixedSubalgebra (θ : L ≃ₗ⁅R⁆ L) :
    (θ.cartanBilinForm.restrict θ.toLieHom.fixedSubalgebra.toSubmodule).lieInvariant
      θ.toLieHom.fixedSubalgebra := by
  have heq : θ.cartanBilinForm.restrict θ.toLieHom.fixedSubalgebra.toSubmodule =
      (-(killingForm R L)).compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap := by
    ext x y
    exact θ.cartanBilinForm_eq_neg_killingForm_of_mem_fixedSubalgebra y.2
  have hneg : (-(killingForm R L)).lieInvariant L := fun x y z ↦ by
    simp [LieModule.traceForm_lieInvariant R L L x y z]
  rw [heq]
  exact hneg.compl₁₂ θ.toLieHom.fixedSubalgebra.incl

end CommRing

/-! ### The Cartan involution predicate -/

section Preorder

variable {R L M : Type*} [CommRing R] [Preorder R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- A Lie algebra automorphism `θ : L ≃ₗ⁅R⁆ L` is a **Cartan involution** when it is involutive
(`θ (θ x) = x`) and the twisted Killing form `-B (x, θ x)` is strictly positive for every nonzero
`x : L`. -/
def IsCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop :=
  Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → 0 < -(killingForm R L x (θ x))

/-- Unfolded definition of `LieEquiv.IsCartanInvolution`. -/
theorem isCartanInvolution_def (θ : L ≃ₗ⁅R⁆ L) :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → 0 < -(killingForm R L x (θ x)) :=
  Iff.rfl

/-- `θ` is a Cartan involution if and only if `θ` is involutive and `θ.cartanBilinForm` has
positive-definite quadratic map. -/
theorem isCartanInvolution_iff_posDef {R L : Type*} [CommRing R] [PartialOrder R] [LieRing L]
    [LieAlgebra R L] (θ : L ≃ₗ⁅R⁆ L) :
    θ.IsCartanInvolution ↔ Function.Involutive θ ∧ θ.cartanBilinForm.toQuadraticMap.PosDef := by
  rw [isCartanInvolution_def, θ.cartanBilinForm.posDef_toQuadraticMap_iff]
  rfl

/-- Intertwining Lie equivalences preserve and reflect Cartan involutions. -/
theorem isCartanInvolution_iff_of_intertwines {θ₁ : L ≃ₗ⁅R⁆ L} {θ₂ : M ≃ₗ⁅R⁆ M} (e : L ≃ₗ⁅R⁆ M)
    (h : θ₂.toLieHom.comp e.toLieHom = e.toLieHom.comp θ₁.toLieHom) :
    θ₁.IsCartanInvolution ↔ θ₂.IsCartanInvolution := by
  have hfun (z : L) : θ₂ (e z) = e (θ₁ z) := LieHom.congr_fun h z
  refine ⟨fun ⟨hinv, hpos⟩ ↦ ⟨fun y ↦ ?_, fun y hy ↦ ?_⟩,
    fun ⟨hinv, hpos⟩ ↦ ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩⟩
  · rw [← e.apply_symm_apply y, hfun, hfun, hinv]
  · have hx : e.symm y ≠ 0 := fun hx0 ↦ hy (by rw [← e.apply_symm_apply y, hx0, map_zero])
    have heq := cartanBilinForm_equiv_apply e h (e.symm y) (e.symm y)
    rw [cartanBilinForm_apply, cartanBilinForm_apply, e.apply_symm_apply] at heq
    exact heq ▸ hpos (e.symm y) hx
  · calc θ₁ (θ₁ x) = e.symm (e (θ₁ (θ₁ x))) := (e.symm_apply_apply _).symm
      _ = e.symm (θ₂ (θ₂ (e x))) := by rw [← hfun (θ₁ x), ← hfun x]
      _ = x := by rw [hinv (e x), e.symm_apply_apply]
  · have hex : e x ≠ 0 := fun h0 ↦ hx (e.injective (h0.trans (map_zero e).symm))
    have heq := cartanBilinForm_equiv_apply e h x x
    rw [cartanBilinForm_apply, cartanBilinForm_apply] at heq
    exact heq ▸ hpos (e x) hex

/-- A nontrivial abelian Lie algebra admits no Cartan involution, since its Killing form vanishes
identically. -/
theorem not_isCartanInvolution_of_isLieAbelian [Nontrivial L] [IsLieAbelian L] (θ : L ≃ₗ⁅R⁆ L) :
    ¬ θ.IsCartanInvolution := by
  rintro ⟨-, hpos⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have had : ad R L x = 0 := LinearMap.ext fun y ↦ trivial_lie_zero L L x y
  have h0 : killingForm R L x (θ x) = 0 := by simp [killingForm_apply_apply, had]
  exact lt_irrefl (0 : R) (by simpa [h0] using hpos x hx)

end Preorder

namespace IsCartanInvolution

section PartialOrder

variable {R L : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]
  {θ : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution)
include hθ

/-- A Cartan involution is involutive. -/
theorem involutive : Function.Involutive θ :=
  hθ.1

/-- A Cartan involution equals its own inverse. -/
theorem symm_eq : θ.symm = θ :=
  LieEquiv.ext fun x ↦ θ.symm_apply_eq.mpr (hθ.involutive x).symm

/-- `B_θ (x, x) > 0` for every nonzero `x : L`. -/
theorem cartanBilinForm_self_pos {x : L} (hx : x ≠ 0) :
    0 < θ.cartanBilinForm x x :=
  hθ.2 x hx

/-- The quadratic map of `θ.cartanBilinForm` is positive definite. -/
theorem posDef_cartanBilinForm : θ.cartanBilinForm.toQuadraticMap.PosDef :=
  (θ.cartanBilinForm.posDef_toQuadraticMap_iff).mpr fun _ hx ↦ hθ.cartanBilinForm_self_pos hx

/-- `θ.cartanBilinForm` is symmetric. -/
theorem isSymm_cartanBilinForm : θ.cartanBilinForm.IsSymm :=
  isSymm_cartanBilinForm_of_involutive hθ.involutive

/-- On the fixed subalgebra `𝔨`, the ambient Killing form is strictly negative on nonzero
vectors. -/
theorem killingForm_self_neg_of_mem_fixedSubalgebra [IsOrderedAddMonoid R] {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hx0 : x ≠ 0) :
    killingForm R L x x < 0 := by
  have h := hθ.cartanBilinForm_self_pos hx0
  rwa [θ.cartanBilinForm_eq_neg_killingForm_of_mem_fixedSubalgebra hx, Left.neg_pos_iff] at h

/-- On the `-1`-eigenspace `𝔭`, the ambient Killing form is strictly positive on nonzero
vectors. -/
theorem killingForm_self_pos_of_mem_cartanP {x : L} (hx : x ∈ θ.cartanP) (hx0 : x ≠ 0) :
    0 < killingForm R L x x := by
  have h := hθ.cartanBilinForm_self_pos hx0
  rwa [θ.cartanBilinForm_eq_killingForm_of_mem_cartanP hx] at h

/-- The restriction of `-killingForm R L` to `𝔨` is positive definite. -/
theorem posDef_neg_killingForm_fixedSubalgebra :
    ((-(killingForm R L)).restrict θ.toLieHom.fixedSubalgebra.toSubmodule).toQuadraticMap.PosDef :=
  by
  rw [LinearMap.BilinForm.posDef_toQuadraticMap_iff]
  intro x hx
  have hx0 : (x : L) ≠ 0 := fun h0 ↦ hx (Subtype.ext h0)
  have h := hθ.cartanBilinForm_self_pos hx0
  rwa [θ.cartanBilinForm_eq_neg_killingForm_of_mem_fixedSubalgebra x.2] at h

/-- The restriction of `killingForm R L` to `𝔭` is positive definite. -/
theorem posDef_killingForm_cartanP :
    ((killingForm R L).restrict θ.cartanP).toQuadraticMap.PosDef := by
  rw [LinearMap.BilinForm.posDef_toQuadraticMap_iff]
  intro x hx
  exact hθ.killingForm_self_pos_of_mem_cartanP x.2 fun h0 ↦ hx (Subtype.ext h0)

/-- For a Cartan involution `θ`, the restriction of `B_θ` to `𝔨` is symmetric. -/
theorem isSymm_restrict_cartanBilinForm_fixedSubalgebra :
    (θ.cartanBilinForm.restrict θ.toLieHom.fixedSubalgebra.toSubmodule).IsSymm := by
  rw [LinearMap.BilinForm.restrict_eq_compl₁₂]
  exact hθ.isSymm_cartanBilinForm.compl₁₂ _

/-- For a Cartan involution `θ`, the restriction of `B_θ` to `𝔨` is positive definite. -/
theorem posDef_restrict_cartanBilinForm_fixedSubalgebra :
    (θ.cartanBilinForm.restrict θ.toLieHom.fixedSubalgebra.toSubmodule).toQuadraticMap.PosDef := by
  rw [LinearMap.BilinForm.restrict_eq_compl₁₂]
  exact θ.cartanBilinForm.posDef_toQuadraticMap_compl₁₂ hθ.posDef_cartanBilinForm _
    θ.toLieHom.fixedSubalgebra.toSubmodule.injective_subtype

end PartialOrder

section LinearOrderRing

variable {R L : Type*} [CommRing R] [LinearOrder R] [LieRing L] [LieAlgebra R L]
  {θ : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution)
include hθ

/-- `θ.cartanBilinForm` is nondegenerate. -/
theorem nondegenerate_cartanBilinForm : θ.cartanBilinForm.Nondegenerate :=
  θ.cartanBilinForm.nondegenerate_of_anisotropic hθ.posDef_cartanBilinForm.anisotropic

/-- **Nondegeneracy of the Killing form.** Every Lie algebra admitting a Cartan involution has
nondegenerate Killing form. -/
theorem nondegenerate_killingForm : (killingForm R L).Nondegenerate := by
  have hnd := hθ.nondegenerate_cartanBilinForm
  refine ⟨fun x hx ↦ hnd.1 x fun y ↦ ?_, fun y hy ↦ ?_⟩
  · simp [cartanBilinForm_apply, hx (θ y)]
  · have hsymm : θ.symm y = 0 := hnd.2 (θ.symm y) fun x ↦ by simp [cartanBilinForm_apply, hy x]
    exact θ.symm.injective (hsymm.trans (map_zero θ.symm).symm)

/-- Every Lie algebra admitting a Cartan involution is Killing (`IsKilling R L`). -/
theorem isKilling : IsKilling R L :=
  TauCeti.isKilling_of_killingForm_nondegenerate R L hθ.nondegenerate_killingForm

/-- Every Lie algebra admitting a Cartan involution is finite as an `R`-module. -/
theorem finite : Module.Finite R L :=
  have := hθ.isKilling
  TauCeti.finite_of_isKilling

/-- Every Lie algebra admitting a Cartan involution has trivial centre. -/
theorem center_eq_bot : center R L = ⊥ := by
  refine eq_bot_iff.mpr fun z hz ↦ hθ.nondegenerate_killingForm.1 z fun y ↦ ?_
  have had : ad R L z = 0 := LinearMap.ext fun w ↦ by
    rw [ad_apply, LinearMap.zero_apply, ← lie_skew z w,
      (LieModule.mem_maxTrivSubmodule R L L z).mp hz w, neg_zero]
  simp [killingForm_apply_apply, had]

end LinearOrderRing

section LinearOrderField

variable {K L : Type*} [Field K] [LinearOrder K] [LieRing L] [LieAlgebra K L]

/-- **Automatic finite-dimensionality.** Over a linearly ordered field, a Lie algebra admitting a
Cartan involution is automatically finite-dimensional. -/
theorem finiteDimensional {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    FiniteDimensional K L :=
  hθ.finite

/-- **Automatic semisimplicity.** Over a linearly ordered field, a Lie algebra admitting a Cartan
involution is automatically semisimple (`IsSemisimple K L`), because `B_θ` forces the Killing form
to be nondegenerate. -/
theorem isSemisimple {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    IsSemisimple K L :=
  have := hθ.isKilling
  have := hθ.finiteDimensional
  inferInstance

/-- Over a linearly ordered field, a Lie algebra admitting a Cartan involution has trivial
radical. -/
theorem hasTrivialRadical {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    HasTrivialRadical K L :=
  have := hθ.isSemisimple
  inferInstance

/-- **The fixed subalgebra `𝔨` is reductive** (`HasCentralRadical K 𝔨`), since `B_θ|_𝔨` is a
symmetric positive-definite `𝔨`-invariant form on `𝔨`. -/
theorem hasCentralRadical_fixedSubalgebra {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    HasCentralRadical K θ.toLieHom.fixedSubalgebra := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.hasCentralRadical_of_anisotropic _
    hθ.isSymm_restrict_cartanBilinForm_fixedSubalgebra.isRefl
    hθ.posDef_restrict_cartanBilinForm_fixedSubalgebra.anisotropic
    θ.lieInvariant_restrict_cartanBilinForm_fixedSubalgebra

/-- **The fixed subalgebra `𝔨` splits as `Z(𝔨) ⊕ [𝔨, 𝔨]`.** -/
theorem isCompl_center_derivedSeries_fixedSubalgebra {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    IsCompl (center K θ.toLieHom.fixedSubalgebra)
      (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.isCompl_center_derivedSeries_one_of_anisotropic _
    hθ.isSymm_restrict_cartanBilinForm_fixedSubalgebra.isRefl
    hθ.posDef_restrict_cartanBilinForm_fixedSubalgebra.anisotropic
    θ.lieInvariant_restrict_cartanBilinForm_fixedSubalgebra

/-- **The derived ideal `[𝔨, 𝔨]` of the fixed subalgebra is semisimple.** -/
theorem isSemisimple_derivedSeries_fixedSubalgebra {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    IsSemisimple K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.isSemisimple_derivedSeries_one_of_anisotropic _
    hθ.isSymm_restrict_cartanBilinForm_fixedSubalgebra.isRefl
    hθ.posDef_restrict_cartanBilinForm_fixedSubalgebra.anisotropic
    θ.lieInvariant_restrict_cartanBilinForm_fixedSubalgebra

end LinearOrderField

section OrderedField

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [LieRing L] [LieAlgebra K L]

/-- Over an ordered field, a Cartan involution splits `L` as `𝔨 ⊕ 𝔭`. -/
theorem isCompl_fixedSubalgebra_cartanP {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP :=
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  LieEquiv.isCompl_fixedSubalgebra_cartanP hθ.involutive

/-! ### Compactness of the intrinsic Killing form of `𝔨` -/

/-- The intrinsic Killing form of `𝔨` is nonpositive on the diagonal. -/
theorem killingForm_fixedSubalgebra_self_nonpos {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution)
    (x : θ.toLieHom.fixedSubalgebra) :
    killingForm K θ.toLieHom.fixedSubalgebra x x ≤ 0 := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.killingForm_self_nonpos_of_posDef _
    hθ.isSymm_restrict_cartanBilinForm_fixedSubalgebra
    hθ.posDef_restrict_cartanBilinForm_fixedSubalgebra
    θ.lieInvariant_restrict_cartanBilinForm_fixedSubalgebra x

/-- The intrinsic Killing form of `𝔨` vanishes at `x` if and only if `x ∈ Z(𝔨)`. -/
theorem killingForm_fixedSubalgebra_self_eq_zero_iff {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution)
    (x : θ.toLieHom.fixedSubalgebra) :
    killingForm K θ.toLieHom.fixedSubalgebra x x = 0 ↔
      x ∈ center K θ.toLieHom.fixedSubalgebra := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.killingForm_self_eq_zero_iff_of_posDef _
    hθ.isSymm_restrict_cartanBilinForm_fixedSubalgebra
    hθ.posDef_restrict_cartanBilinForm_fixedSubalgebra
    θ.lieInvariant_restrict_cartanBilinForm_fixedSubalgebra x

/-- **Compactness of `[𝔨, 𝔨]`.** The intrinsic Killing form of `[𝔨, 𝔨]` is strictly negative on
every nonzero element. -/
theorem killingForm_derivedSeries_fixedSubalgebra_self_neg {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) {x : derivedSeries K θ.toLieHom.fixedSubalgebra 1} (hx : x ≠ 0) :
    killingForm K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) x x < 0 := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero _
    hθ.isSymm_restrict_cartanBilinForm_fixedSubalgebra
    hθ.posDef_restrict_cartanBilinForm_fixedSubalgebra
    θ.lieInvariant_restrict_cartanBilinForm_fixedSubalgebra x hx

end OrderedField

/-! ### Real inner product and diagonalizability of `ad x` for `x ∈ 𝔭` -/

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
include hθ

/-- Package the twisted Killing form `B_θ` of a real Cartan involution as `InnerProductSpace.Core`,
without installing a global `Norm` or `InnerProductSpace` instance on `L`. -/
@[implicit_reducible]
noncomputable def innerProductCore : InnerProductSpace.Core ℝ L :=
  θ.cartanBilinForm.toInnerProductCore hθ.isSymm_cartanBilinForm hθ.posDef_cartanBilinForm

/-- The inner product induced by `LieEquiv.IsCartanInvolution.innerProductCore` evaluates as
`-killingForm ℝ L x (θ y)`. -/
theorem innerProductCore_inner (x y : L) :
    @inner ℝ L hθ.innerProductCore.toInner x y = -killingForm ℝ L x (θ y) :=
  θ.cartanBilinForm.toInnerProductCore_inner hθ.isSymm_cartanBilinForm hθ.posDef_cartanBilinForm x y

/-- **Real diagonalizability of `ad x` for `x ∈ 𝔭`.** For a Cartan involution `θ` of a real Lie
algebra `L` (automatically finite-dimensional) and every `x ∈ θ.cartanP`, the real eigenspaces of
`ad ℝ L x` span `L`. -/
theorem iSup_eigenspace_ad_eq_top_of_mem_cartanP {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, (ad ℝ L x).eigenspace μ = ⊤ := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.iSup_eigenspace_eq_top_of_isSelfAdjoint hθ.isSymm_cartanBilinForm
    hθ.posDef_cartanBilinForm (ad_mem_selfAdjointSubmodule_cartanBilinForm hθ.involutive hx)

/-- **Semisimplicity of `ad x` for `x ∈ 𝔭`.** For a Cartan involution `θ` of a real Lie algebra
`L` and every `x ∈ θ.cartanP`, the adjoint endomorphism `ad ℝ L x` is semisimple. -/
theorem isSemisimple_ad_of_mem_cartanP {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple := by
  have _f := hθ.finiteDimensional
  exact LinearMap.BilinForm.isSemisimple_of_isSelfAdjoint hθ.isSymm_cartanBilinForm
    hθ.posDef_cartanBilinForm (ad_mem_selfAdjointSubmodule_cartanBilinForm hθ.involutive hx)

end Real

end IsCartanInvolution

end LieEquiv
