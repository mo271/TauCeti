/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Normed.Module.Quotient

/-!
# Pulling back, pairing adjoints, and quotient descent of continuous bilinear maps

A continuous linear map `u : W →L[𝕜] V` pulls a continuous bilinear map `B` on `V` back to the
bilinear map `B (u ·) (u ·)` on `W`. This operation is itself continuous and linear in `B`
(`ContinuousLinearMap.pullbackBilinL`), so that it commutes with derivatives of families of
bilinear maps, such as the coordinate expressions of metrics. In particular, pulling back each
value of a continuous family of multilinear maps valued in bilinear maps, along `u` in every
argument, gives a continuous family
(`Continuous.pullbackBilinL_compContinuousMultilinearMap`). Pulling back along a bijection preserves
nondegeneracy (`ContinuousLinearMap.injective_bilinearComp`).

The quadratic map `x ↦ B x x` of a continuous bilinear map is Lipschitz on every ball, with a
constant proportional to the radius: `‖B x x - B y y‖ ≤ ‖B‖ (‖x‖ + ‖y‖) ‖x - y‖`
(`ContinuousLinearMap.norm_apply_apply_sub_apply_apply_le`). This is the quadratic estimate on the
nonlinear terms of an equation that is quadratic in its unknown.

Pulling back along continuous linear equivalences keeps a bilinear map `B₀ : V →L V' →L G`
invertible as a map to the dual (`ContinuousLinearMap.IsInvertible.bilinearComp`), and it
conjugates the comparison operator `B₀⁻¹ ∘ B` of two such maps by the equivalence in the first
slot (`ContinuousLinearMap.inverse_bilinearComp_comp_bilinearComp`). This is how operators built
from a pair of bilinear forms, such as the Morse congruence of a form with a reference form,
transform under a linear change of coordinates.

An invertible bilinear map `B₀ : V →L V →L G` determines adjoints of operators on `V`: the
adjoint `ContinuousLinearMap.pairingAdjoint B₀ X` is characterized by
`B₀ (adj X w) w' = B₀ w (X w')` (`ContinuousLinearMap.IsInvertible.pairingAdjoint_apply`). It
reverses products, fixes the identity, and tends to the identity as `B₀` stays near an
invertible map and `X` tends to the identity. On Banach spaces the comparison operator
`B₀⁻¹ ∘ B` also tends to the identity as both maps tend to the same invertible map
(`ContinuousLinearMap.IsInvertible.tendsto_inverse_comp`).

Dually to pullback, a continuous bilinear (or sesquilinear) map `b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G`
vanishing on `S₁` in its first argument and on `S₂` in its second descends to a continuous
bilinear map `b.liftQ₂ S₁ S₂ h₁ h₂ : E₁ ⧸ S₁ →SL[σ₁₃] E₂ ⧸ S₂ →SL[σ₂₃] G` by alternating
`Submodule.liftQL` with `ContinuousLinearMap.flip`. Both operations are isometric, so descending
through quotients in both arguments preserves the operator norm (`ContinuousLinearMap.norm_liftQ₂`),
and precomposing a quotient bilinear map with both quotient projections likewise preserves its
norm (`ContinuousLinearMap.norm_bilinearComp_mkQL`). Evaluating on quotient classes yields the
two-sided quotient-norm bound `‖b x y‖ ≤ ‖b‖ * ‖S₁.mkQ x‖ * ‖S₂.mkQ y‖` and the bilinear
Bramble–Hilbert estimate (`ContinuousLinearMap.norm_apply_le_of_exists_mem_norm_sub_le`; compare
Bramble–Hilbert, *SIAM J. Numer. Anal.* 7 (1970), Theorem 2, and Ciarlet, *The Finite Element
Method for Elliptic Problems*, §3.1).
-/

public section

noncomputable section

namespace ContinuousLinearMap

section Pullback

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V W G : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pulling a continuous bilinear map back along a continuous linear map `u`,
`B ↦ B (u ·) (u ·)`, as a continuous linear map in `B`. -/
def pullbackBilinL (u : W →L[𝕜] V) : (V →L[𝕜] V →L[𝕜] G) →L[𝕜] W →L[𝕜] W →L[𝕜] G :=
  (compL 𝕜 W (V →L[𝕜] G) (W →L[𝕜] G) ((compL 𝕜 W V G).flip u)).comp
    ((compL 𝕜 W V (V →L[𝕜] G)).flip u)

@[simp]
theorem pullbackBilinL_apply (u : W →L[𝕜] V) (B : V →L[𝕜] V →L[𝕜] G) (v w : W) :
    pullbackBilinL u B v w = B (u v) (u w) :=
  (rfl)

/-- `pullbackBilinL u` precomposes a bilinear map with `u`, and then each of its values with `u`.
In this form it is visibly built from `u` by continuous linear operations, so that, for instance,
its regularity in `u` follows from that of the precomposition maps `compL`. -/
theorem pullbackBilinL_eq_comp (u : W →L[𝕜] V) :
    pullbackBilinL (G := G) u =
      (compL 𝕜 W (V →L[𝕜] G) (W →L[𝕜] G) ((compL 𝕜 W V G).flip u)).comp
        ((compL 𝕜 W V (V →L[𝕜] G)).flip u) :=
  (rfl)

/-- The quadratic map `x ↦ B x x` of a continuous bilinear map `B` satisfies
`‖B x x - B y y‖ ≤ ‖B‖ (‖x‖ + ‖y‖) ‖x - y‖`. -/
theorem norm_apply_apply_sub_apply_apply_le (B : V →L[𝕜] V →L[𝕜] G) (x y : V) :
    ‖B x x - B y y‖ ≤ ‖B‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have h : B x x - B y y = B x (x - y) + B (x - y) y := by
    simp only [map_sub, sub_apply]
    abel
  rw [h]
  calc ‖B x (x - y) + B (x - y) y‖ ≤ ‖B‖ * ‖x‖ * ‖x - y‖ + ‖B‖ * ‖x - y‖ * ‖y‖ :=
        (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))
    _ = ‖B‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

/-- Pulling a nondegenerate bilinear map back along a bijective continuous linear map keeps it
nondegenerate. -/
theorem injective_bilinearComp {B : V →L[𝕜] V →L[𝕜] G} (hB : Function.Injective B)
    {u : W →L[𝕜] V} (hu : Function.Bijective u) : Function.Injective (B.bilinearComp u u) := by
  intro w w' hww'
  refine hu.1 (hB ?_)
  ext v
  obtain ⟨v, rfl⟩ := hu.2 v
  exact congrArg (fun φ ↦ φ v) hww'

section Invertible

variable {V' W' : Type*} [SeminormedAddCommGroup V'] [NormedSpace 𝕜 V']
  [SeminormedAddCommGroup W'] [NormedSpace 𝕜 W']

/-- Pulling a bilinear map that is invertible, as a map to the space of linear maps on its
second argument, back along continuous linear equivalences in both arguments keeps it
invertible. -/
theorem IsInvertible.bilinearComp {B₀ : V →L[𝕜] V' →L[𝕜] G} (hB₀ : B₀.IsInvertible)
    (e₁ : W ≃L[𝕜] V) (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).IsInvertible := by
  refine .of_inverse (g := (e₁.symm : V →L[𝕜] W) ∘L B₀.inverse ∘L
    (compL 𝕜 V' W' G).flip (e₂.symm : V' →L[𝕜] W')) ?_ ?_
  · ext φ x
    simp [hB₀.self_apply_inverse]
  · ext x
    have h : (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V') x).comp
        (e₂.symm : V' →L[𝕜] W') = B₀ (e₁ x) := by
      ext y
      simp
    simp [h, hB₀.inverse_apply_self]

/-- Pulling two bilinear maps back along continuous linear equivalences conjugates their
comparison operator `B₀⁻¹ ∘ B` by the equivalence `e₁` in the first argument. -/
theorem inverse_bilinearComp_comp_bilinearComp {B₀ : V →L[𝕜] V' →L[𝕜] G}
    (hB₀ : B₀.IsInvertible) (B : V →L[𝕜] V' →L[𝕜] G) (e₁ : W ≃L[𝕜] V) (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).inverse ∘L
        B.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V') =
      (e₁.symm : V →L[𝕜] W) ∘L (B₀.inverse ∘L B) ∘L (e₁ : W →L[𝕜] V) := by
  ext w
  rw [comp_apply, (hB₀.bilinearComp e₁ e₂).inverse_apply_eq]
  ext w'
  simp [hB₀.self_apply_inverse]

end Invertible

section PairingAdjoint

open Filter Topology

/-- The adjoint of an operator `X` on `V` for the pairing `B₀`, `B₀⁻¹ ∘ (· ∘ X) ∘ B₀`. When
`B₀` is invertible it is characterized by `B₀ (adj X w) w' = B₀ w (X w')`
(`ContinuousLinearMap.IsInvertible.pairingAdjoint_apply`). -/
def pairingAdjoint (B₀ : V →L[𝕜] V →L[𝕜] G) (X : V →L[𝕜] V) : V →L[𝕜] V :=
  B₀.inverse ∘L ((compL 𝕜 V V G).flip X ∘L B₀)

/-- The adjoint for the pairing `B₀` is `B₀⁻¹ ∘ (· ∘ X) ∘ B₀`. -/
theorem pairingAdjoint_def (B₀ : V →L[𝕜] V →L[𝕜] G) (X : V →L[𝕜] V) :
    pairingAdjoint B₀ X = B₀.inverse ∘L ((compL 𝕜 V V G).flip X ∘L B₀) := by
  rw [pairingAdjoint]

variable {B₀ : V →L[𝕜] V →L[𝕜] G}

/-- The defining property of the adjoint for an invertible pairing. -/
@[simp] theorem IsInvertible.pairingAdjoint_apply (hB₀ : B₀.IsInvertible) (X : V →L[𝕜] V)
    (w w' : V) :
    B₀ (pairingAdjoint B₀ X w) w' = B₀ w (X w') := by
  simp [pairingAdjoint, hB₀.self_apply_inverse]

/-- Operators are determined by their pairings against an invertible bilinear map. -/
theorem IsInvertible.ext_of_pairing (hB₀ : B₀.IsInvertible) {X Y : V →L[𝕜] V}
    (h : ∀ w w', B₀ (X w) w' = B₀ (Y w) w') : X = Y :=
  ext fun w ↦ hB₀.bijective.injective (ext (h w))

/-- The adjoint for an invertible pairing reverses products. -/
theorem IsInvertible.pairingAdjoint_mul (hB₀ : B₀.IsInvertible) (X Y : V →L[𝕜] V) :
    pairingAdjoint B₀ (X * Y) = pairingAdjoint B₀ Y * pairingAdjoint B₀ X :=
  hB₀.ext_of_pairing fun w w' ↦ by
    simp only [hB₀.pairingAdjoint_apply, mul_apply_eq_comp]

/-- The adjoint of the identity for an invertible pairing is the identity. -/
@[simp] theorem IsInvertible.pairingAdjoint_one (hB₀ : B₀.IsInvertible) :
    pairingAdjoint B₀ (1 : V →L[𝕜] V) = 1 :=
  hB₀.ext_of_pairing fun w w' ↦ by simp [hB₀.pairingAdjoint_apply]

end PairingAdjoint

section Tendsto

open Filter Topology

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The comparison operator `e₀⁻¹ ∘ e` tends to the identity as both maps tend to the same
invertible map. -/
theorem IsInvertible.tendsto_inverse_comp {e : E →L[𝕜] F} (he : e.IsInvertible) :
    Tendsto (fun p : (E →L[𝕜] F) × (E →L[𝕜] F) ↦ p.1.inverse ∘L p.2) (𝓝 (e, e)) (𝓝 1) := by
  have h₁ : ContinuousAt (fun p : (E →L[𝕜] F) × (E →L[𝕜] F) ↦ p.1.inverse) (e, e) :=
    ContinuousAt.comp (f := Prod.fst) (x := (e, e))
      (he.contDiffAt_map_inverse (n := 0)).continuousAt continuousAt_fst
  have h := h₁.clm_comp continuousAt_snd
  simpa only [he.inverse_comp_self, ← one_def] using h.tendsto

/-- The adjoint of `X` for the pairing `B₀` tends to the identity as `B₀` tends to an
invertible pairing and `X` tends to the identity. -/
theorem IsInvertible.tendsto_pairingAdjoint {B₀ : E →L[𝕜] E →L[𝕜] H} (hB₀ : B₀.IsInvertible) :
    Tendsto (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦ pairingAdjoint q.1 q.2)
      (𝓝 (B₀, 1)) (𝓝 1) := by
  have h₁ : ContinuousAt (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦ q.1.inverse) (B₀, 1) :=
    ContinuousAt.comp (f := Prod.fst) (x := (B₀, 1))
      (hB₀.contDiffAt_map_inverse (n := 0)).continuousAt continuousAt_fst
  have h₂ : ContinuousAt (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦
      (compL 𝕜 E E H).flip q.2) (B₀, 1) :=
    ((compL 𝕜 E E H).flip).continuous.continuousAt.comp continuousAt_snd
  have h : ContinuousAt (fun q : (E →L[𝕜] E →L[𝕜] H) × (E →L[𝕜] E) ↦
      pairingAdjoint q.1 q.2) (B₀, 1) :=
    h₁.clm_comp (h₂.clm_comp continuousAt_fst)
  simpa only [hB₀.pairingAdjoint_one] using h.tendsto

end Tendsto

end Pullback

section QuotientSemilinear

variable {𝕜₁ 𝕜₂ 𝕜₃ E₁ E₂ G : Type*}
  [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜₁ E₁]
  [SeminormedAddCommGroup E₂] [NormedSpace 𝕜₂ E₂]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜₃ G]
  {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}
  [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]

private theorem le_ker_flip_liftQL (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker) :
    S₂ ≤ (S₁.liftQL b h₁).flip.ker := by
  intro y hy
  rw [LinearMap.mem_ker]
  ext z
  obtain ⟨x, rfl⟩ := S₁.mkQ_surjective z
  have hy0 : b.flip y = 0 := h₂ hy
  simpa only [coe_coe, flip_apply, Submodule.liftQL_apply, Submodule.mkQ_apply,
    Submodule.liftQ_apply, zero_apply] using congrArg (fun f : E₁ →SL[σ₁₃] G ↦ f x) hy0

/-- Lift a continuous bilinear (or sesquilinear) map `E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G` to the
quotient modules `(E₁ ⧸ S₁) →SL[σ₁₃] (E₂ ⧸ S₂) →SL[σ₂₃] G` across submodules annihilated in the
first and second arguments respectively. -/
def liftQ₂ (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker) :
    E₁ ⧸ S₁ →SL[σ₁₃] E₂ ⧸ S₂ →SL[σ₂₃] G :=
  (S₂.liftQL (S₁.liftQL b h₁).flip (le_ker_flip_liftQL S₁ S₂ b h₁ h₂)).flip

@[simp]
theorem liftQ₂_mk (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker)
    (x : E₁) (y : E₂) :
    b.liftQ₂ S₁ S₂ h₁ h₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = b x y :=
  (rfl)

theorem liftQ₂_mkQ (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker)
    (x : E₁) (y : E₂) :
    b.liftQ₂ S₁ S₂ h₁ h₂ (S₁.mkQ x) (S₂.mkQ y) = b x y :=
  (rfl)

/-- Forgetting continuity on `ContinuousLinearMap.liftQ₂` recovers the algebraic quotient lift
`LinearMap.liftQ₂`. -/
@[simp]
theorem toLinearMap₁₂_liftQ₂ (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker) :
    (b.liftQ₂ S₁ S₂ h₁ h₂).toLinearMap₁₂ = b.toLinearMap₁₂.liftQ₂ S₁ S₂
      (fun x hx ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun y ↦
        (toLinearMap₁₂_apply_apply_apply b x y).trans <|
          (DFunLike.congr_fun (LinearMap.mem_ker.mp (h₁ hx)) y).trans (zero_apply y))
      (fun y hy ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun x ↦
        (LinearMap.flip_apply b.toLinearMap₁₂ x y).trans <|
          (toLinearMap₁₂_apply_apply_apply b x y).trans <| (flip_apply b x y).symm.trans <|
            (DFunLike.congr_fun (LinearMap.mem_ker.mp (h₂ hy)) x).trans (zero_apply x)) := by
  ext x y
  simp

/-- Universal property of `ContinuousLinearMap.liftQ₂`: a continuous bilinear map on
`(E₁ ⧸ S₁) × (E₂ ⧸ S₂)` equals `b.liftQ₂ S₁ S₂ h₁ h₂` if and only if it agrees with `b` on pairs
of quotient classes. -/
theorem eq_liftQ₂_iff {S₁ : Submodule 𝕜₁ E₁} {S₂ : Submodule 𝕜₂ E₂}
    {b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G} {h₁ : S₁ ≤ b.ker} {h₂ : S₂ ≤ b.flip.ker}
    {c : E₁ ⧸ S₁ →SL[σ₁₃] E₂ ⧸ S₂ →SL[σ₂₃] G} :
    c = b.liftQ₂ S₁ S₂ h₁ h₂ ↔
      ∀ x y, c (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = b x y := by
  refine ⟨fun hc x y ↦ hc ▸ liftQ₂_mk S₁ S₂ b h₁ h₂ x y, fun hc ↦ ?_⟩
  ext z w
  obtain ⟨x, rfl⟩ := S₁.mkQ_surjective z
  obtain ⟨y, rfl⟩ := S₂.mkQ_surjective w
  exact hc x y

/-- Flipping `liftQ₂` lifts `b.flip` with the two quotient submodules exchanged. -/
@[simp]
theorem flip_liftQ₂ (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker) :
    (b.liftQ₂ S₁ S₂ h₁ h₂).flip = b.flip.liftQ₂ S₂ S₁ h₂ ((flip_flip b).symm ▸ h₁) := by
  rw [eq_liftQ₂_iff]
  intro y x
  simp

@[simp]
theorem liftQ₂_zero (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (h₁ : S₁ ≤ (0 : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G).ker := by simp)
    (h₂ : S₂ ≤ (0 : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G).flip.ker := by simp) :
    (0 : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G).liftQ₂ S₁ S₂ h₁ h₂ = 0 := by
  symm
  rw [eq_liftQ₂_iff]
  intro x y
  simp

theorem liftQ₂_add (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b₁ b₂ : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G)
    (h₁₁ : S₁ ≤ b₁.ker) (h₁₂ : S₂ ≤ b₁.flip.ker)
    (h₂₁ : S₁ ≤ b₂.ker) (h₂₂ : S₂ ≤ b₂.flip.ker)
    (h₁ : S₁ ≤ (b₁ + b₂).ker := fun x hx ↦ by
      simp [LinearMap.mem_ker.mp (h₁₁ hx), LinearMap.mem_ker.mp (h₂₁ hx)])
    (h₂ : S₂ ≤ (b₁ + b₂).flip.ker := fun y hy ↦ by
      simp [LinearMap.mem_ker.mp (h₁₂ hy), LinearMap.mem_ker.mp (h₂₂ hy)]) :
    (b₁ + b₂).liftQ₂ S₁ S₂ h₁ h₂ = b₁.liftQ₂ S₁ S₂ h₁₁ h₁₂ + b₂.liftQ₂ S₁ S₂ h₂₁ h₂₂ := by
  symm
  rw [eq_liftQ₂_iff]
  intro x y
  simp

theorem liftQ₂_smul (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (c : 𝕜₃) (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker)
    (hc₁ : S₁ ≤ (c • b).ker := h₁.trans (LinearMap.ker_le_ker_smul _ _))
    (hc₂ : S₂ ≤ (c • b).flip.ker := by
      rw [flip_smul]
      exact h₂.trans (LinearMap.ker_le_ker_smul _ _)) :
    (c • b).liftQ₂ S₁ S₂ hc₁ hc₂ = c • b.liftQ₂ S₁ S₂ h₁ h₂ := by
  symm
  rw [eq_liftQ₂_iff]
  intro x y
  simp

/-- Descending a continuous bilinear map through quotients in both arguments preserves its operator
norm. -/
@[simp]
theorem norm_liftQ₂ (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker) :
    ‖b.liftQ₂ S₁ S₂ h₁ h₂‖ = ‖b‖ := by
  rw [liftQ₂, opNorm_flip, S₂.norm_liftQL, opNorm_flip, S₁.norm_liftQL]

/-- Descending a continuous bilinear map through quotients in both arguments preserves its
nonnegative operator norm. -/
@[simp]
theorem nnnorm_liftQ₂ (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker) :
    ‖b.liftQ₂ S₁ S₂ h₁ h₂‖₊ = ‖b‖₊ :=
  Subtype.ext (norm_liftQ₂ S₁ S₂ b h₁ h₂)

/-- **Two-sided quotient-norm bound for continuous bilinear maps.** If `b` vanishes on `S₁` on the
left and `S₂` on the right, then `‖b x y‖ ≤ ‖b‖ * ‖S₁.mkQ x‖ * ‖S₂.mkQ y‖`. -/
theorem norm_apply_le_mul_norm_mkQ (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker)
    (x : E₁) (y : E₂) :
    ‖b x y‖ ≤ ‖b‖ * ‖S₁.mkQ x‖ * ‖S₂.mkQ y‖ := by
  simpa only [liftQ₂_mkQ, norm_liftQ₂] using
    (b.liftQ₂ S₁ S₂ h₁ h₂).le_opNorm₂ (S₁.mkQ x) (S₂.mkQ y)

/-- Distance-to-subspace form of `ContinuousLinearMap.norm_apply_le_mul_norm_mkQ`. -/
theorem norm_apply_le_mul_infDist (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker)
    (x : E₁) (y : E₂) :
    ‖b x y‖ ≤ ‖b‖ * Metric.infDist x (S₁ : Set E₁) * Metric.infDist y (S₂ : Set E₂) := by
  rw [← S₁.norm_mkQL_apply, ← S₂.norm_mkQL_apply]
  exact norm_apply_le_mul_norm_mkQ S₁ S₂ b h₁ h₂ x y

/-- **Bilinear Bramble–Hilbert estimate (quotient-norm form).** Bounds `‖S₁.mkQ x‖ ≤ B₁` and
`‖S₂.mkQ y‖ ≤ B₂` yield `‖b x y‖ ≤ ‖b‖ * B₁ * B₂` without sign assumptions on `B₁` or `B₂`. -/
theorem norm_apply_le_of_norm_mkQ_le (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker)
    {x : E₁} {y : E₂} {B₁ B₂ : ℝ} (hx : ‖S₁.mkQ x‖ ≤ B₁) (hy : ‖S₂.mkQ y‖ ≤ B₂) :
    ‖b x y‖ ≤ ‖b‖ * B₁ * B₂ := by
  simpa only [liftQ₂_mkQ] using
    (b.liftQ₂ S₁ S₂ h₁ h₂).le_of_opNorm₂_le_of_le (norm_liftQ₂ S₁ S₂ b h₁ h₂).le hx hy

/-- **Bilinear Bramble–Hilbert estimate (approximation form).** If `b` vanishes on `S₁` in its
first argument and on `S₂` in its second, and `x` and `y` admit approximants in `S₁` and `S₂`
within norms `B₁` and `B₂`, then `‖b x y‖ ≤ ‖b‖ * B₁ * B₂` without sign assumptions on `B₁` or
`B₂`. -/
theorem norm_apply_le_of_exists_mem_norm_sub_le (S₁ : Submodule 𝕜₁ E₁) (S₂ : Submodule 𝕜₂ E₂)
    (b : E₁ →SL[σ₁₃] E₂ →SL[σ₂₃] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker)
    {x : E₁} {y : E₂} {B₁ B₂ : ℝ}
    (hx : ∃ p ∈ S₁, ‖x - p‖ ≤ B₁) (hy : ∃ q ∈ S₂, ‖y - q‖ ≤ B₂) :
    ‖b x y‖ ≤ ‖b‖ * B₁ * B₂ := by
  obtain ⟨p, hp, hxp⟩ := hx
  obtain ⟨q, hq, hyq⟩ := hy
  have hmk₁ : ‖S₁.mkQ x‖ ≤ B₁ := by
    have heq : S₁.mkQ (x - p) = S₁.mkQ x := by
      rw [map_sub, S₁.mkQ_apply p, (Submodule.Quotient.mk_eq_zero S₁).mpr hp, sub_zero]
    rw [← heq]
    exact (Submodule.Quotient.norm_mk_le S₁ (x - p)).trans hxp
  have hmk₂ : ‖S₂.mkQ y‖ ≤ B₂ := by
    have heq : S₂.mkQ (y - q) = S₂.mkQ y := by
      rw [map_sub, S₂.mkQ_apply q, (Submodule.Quotient.mk_eq_zero S₂).mpr hq, sub_zero]
    rw [← heq]
    exact (Submodule.Quotient.norm_mk_le S₂ (y - q)).trans hyq
  exact norm_apply_le_of_norm_mkQ_le S₁ S₂ b h₁ h₂ hmk₁ hmk₂

end QuotientSemilinear

section QuotientLinear

variable {𝕜 E₁ E₂ G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Precomposing a continuous bilinear map out of quotient modules with both quotient projections
preserves its operator norm. -/
@[simp]
theorem norm_bilinearComp_mkQL (S₁ : Submodule 𝕜 E₁) (S₂ : Submodule 𝕜 E₂)
    (c : E₁ ⧸ S₁ →L[𝕜] E₂ ⧸ S₂ →L[𝕜] G) :
    ‖c.bilinearComp S₁.mkQL S₂.mkQL‖ = ‖c‖ := by
  have h₁ : S₁ ≤ (c.bilinearComp S₁.mkQL S₂.mkQL).ker := by
    intro x hx
    ext y
    simp [(Submodule.Quotient.mk_eq_zero S₁).mpr hx]
  have h₂ : S₂ ≤ (c.bilinearComp S₁.mkQL S₂.mkQL).flip.ker := by
    intro y hy
    ext x
    simp [(Submodule.Quotient.mk_eq_zero S₂).mpr hy]
  have heq : c = (c.bilinearComp S₁.mkQL S₂.mkQL).liftQ₂ S₁ S₂ h₁ h₂ := by
    rw [eq_liftQ₂_iff]
    intro x y
    rfl
  conv_rhs => rw [heq]
  exact (norm_liftQ₂ S₁ S₂ _ h₁ h₂).symm

@[simp]
theorem bilinearComp_mkQL_liftQ₂ (S₁ : Submodule 𝕜 E₁) (S₂ : Submodule 𝕜 E₂)
    (b : E₁ →L[𝕜] E₂ →L[𝕜] G) (h₁ : S₁ ≤ b.ker) (h₂ : S₂ ≤ b.flip.ker) :
    (b.liftQ₂ S₁ S₂ h₁ h₂).bilinearComp S₁.mkQL S₂.mkQL = b := by
  ext x y
  exact liftQ₂_mk S₁ S₂ b h₁ h₂ x y

end QuotientLinear

end ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V W G : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pulling back each value of a continuous family `f` of multilinear maps valued in bilinear
maps, both in its arguments and in its values, along a continuous linear map `u` gives a
continuous family. Applied to iterated derivatives of a family of bilinear forms, this is the
pullback of all their coordinate derivatives along `u`. -/
theorem Continuous.pullbackBilinL_compContinuousMultilinearMap {X ι : Type*} [TopologicalSpace X]
    {f : X → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V) (V →L[𝕜] V →L[𝕜] G)} (hf : Continuous f)
    (u : W →L[𝕜] V) :
    Continuous fun x ↦ (ContinuousLinearMap.pullbackBilinL u).compContinuousMultilinearMap
      ((f x).compContinuousLinearMap fun _ ↦ u) :=
  ((ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ W) _ _
    (ContinuousLinearMap.pullbackBilinL u)).continuous.comp
    ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ u).continuous.comp hf) :)
