/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Reductive.Decomposition
import TauCeti.Algebra.Lie.Killing.Perfect

/-!
# Cartan involutions of reductive Lie algebras

For a reductive Lie algebra `L` with nontrivial centre, the Killing form vanishes on `center R L`,
so no automorphism can make `-B (x, θ x)` strictly positive on all of `L`. Following Knapp, an
automorphism `θ : L ≃ₗ⁅R⁆ L` is a **reductive Cartan involution**
(`LieEquiv.IsReductiveCartanInvolution`) when `θ` is involutive on `L` and its restriction
`θ.restrictDerivedSeries 1` to the derived ideal `⁅L, L⁆ = derivedSeries R L 1` is a Cartan
involution in the semisimple sense (`LieEquiv.IsCartanInvolution`).

Over a linearly ordered field `K`, the existence of a reductive Cartan involution `θ` forces
`derivedSeries K L 1` to be Killing, finite-dimensional, and semisimple, and hence forces `L`
itself to split as `L = center K L ⊕ derivedSeries K L 1` with central radical
(`TauCeti.isCompl_center_derivedSeries_of_isKilling_derivedSeries`) — with no separate
reductivity or finite-dimensionality hypothesis on `L`. Moreover:

* `θ` preserves both `center K L` and `derivedSeries K L 1`, acting as an involutive automorphism
  on the centre and as a Cartan involution on the derived ideal;
* the `-1`-eigenspace `𝔭 = θ.cartanP` splits directly as
  `(𝔭 ⊓ center K L) ⊕ (𝔭 ⊓ derivedSeries K L 1)` (`LieEquiv.cartanPCenterDerivedEquiv`);
* every semisimple Cartan involution is a reductive Cartan involution, and the two predicates
  coincide whenever `center K L = ⊥` (in particular when `HasTrivialRadical K L`);
* on an abelian Lie algebra, `IsReductiveCartanInvolution` reduces to `Function.Involutive`; and
* along any decomposition `L = center R L ⊕ derivedSeries R L 1`, pairing an arbitrary involutive
  automorphism of the centre with a Cartan involution of the derived ideal via
  `LieEquiv.ofCenterDerived` yields a reductive Cartan involution of `L`.

## Main definitions

* `LieEquiv.cartanPCenterDerivedEquiv`: linear equivalence
  `(↥(θ.cartanP ⊓ center R L) × ↥(θ.cartanP ⊓ derivedSeries R L 1)) ≃ₗ[R] θ.cartanP` associated
  with `IsCompl (center R L) (derivedSeries R L 1)`.
* `LieEquiv.IsReductiveCartanInvolution`: `θ` is involutive and `(θ.restrictDerivedSeries 1)` is a
  Cartan involution of `derivedSeries R L 1`.

## Main statements

* `LieEquiv.cartanP_eq_sup_inf_center_inf_derivedSeries` and
  `LieEquiv.disjoint_cartanP_inf_center_inf_derivedSeries`: `𝔭 = (𝔭 ∩ 𝔷) ⊕ (𝔭 ∩ [L, L])`.
* `LieEquiv.IsCartanInvolution.isReductiveCartanInvolution` and
  `LieEquiv.isReductiveCartanInvolution_iff_isCartanInvolution_of_center_eq_bot`: comparison with
  the semisimple predicate.
* `LieEquiv.isReductiveCartanInvolution_iff_involutive`: abelian specialization.
* `LieEquiv.isReductiveCartanInvolution_ofCenterDerived_iff`: characterization of assembled
  automorphisms on `center R L ⊕ derivedSeries R L 1`.
* `LieEquiv.IsReductiveCartanInvolution.isCompl_center_derivedSeries` and
  `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical`: automatic reductive splitting.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VII, §2.
-/

public section

open LieAlgebra

namespace LieEquiv

section CommRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The `-1`-eigenspace of `θ.restrictCenter` embeds into `L` as `θ.cartanP ⊓ center R L`. -/
theorem map_cartanP_restrictCenter (θ : L ≃ₗ⁅R⁆ L) :
    θ.restrictCenter.cartanP.map (center R L).toSubmodule.subtype =
      θ.cartanP ⊓ (center R L).toSubmodule := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_inf, mem_cartanP_iff, Submodule.coe_subtype,
    LieSubmodule.mem_toSubmodule]
  refine ⟨?_, fun ⟨hx, hxz⟩ ↦ ⟨⟨x, hxz⟩, Subtype.ext ?_, rfl⟩⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, z.2⟩
    simpa only [← θ.coe_restrictCenter z, NegMemClass.coe_neg] using
      congrArg (fun u : center R L ↦ (u : L)) hz
  · simpa only [θ.coe_restrictCenter ⟨x, hxz⟩, NegMemClass.coe_neg] using hx

/-- The `-1`-eigenspace of `θ.restrictDerivedSeries k` embeds into `L` as
`θ.cartanP ⊓ derivedSeries R L k`. -/
theorem map_cartanP_restrictDerivedSeries (θ : L ≃ₗ⁅R⁆ L) (k : ℕ) :
    (θ.restrictDerivedSeries k).cartanP.map (derivedSeries R L k).toSubmodule.subtype =
      θ.cartanP ⊓ (derivedSeries R L k).toSubmodule := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_inf, mem_cartanP_iff, Submodule.coe_subtype,
    LieSubmodule.mem_toSubmodule]
  refine ⟨?_, fun ⟨hx, hxd⟩ ↦ ⟨⟨x, hxd⟩, Subtype.ext ?_, rfl⟩⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨?_, d.2⟩
    simpa only [← θ.coe_restrictDerivedSeries k d, NegMemClass.coe_neg] using
      congrArg (fun u : derivedSeries R L k ↦ (u : L)) hd
  · simpa only [θ.coe_restrictDerivedSeries k ⟨x, hxd⟩, NegMemClass.coe_neg] using hx

/-- Along a direct-sum decomposition `L = center R L ⊕ derivedSeries R L 1`, every vector in
`θ.cartanP` decomposes uniquely into negated central and derived components. -/
theorem existsUnique_cartanP_center_add_cartanP_derivedSeries (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) (x : θ.cartanP) :
    ∃! p : center R L × derivedSeries R L 1,
      θ p.1 = -p.1 ∧ θ p.2 = -p.2 ∧ (p.1 : L) + p.2 = x := by
  let a := (center R L).toSubmodule.prodEquivOfIsCompl (derivedSeries R L 1).toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr h)
  obtain ⟨p, hp⟩ := a.surjective (x : L)
  have hsum : (p.1 : L) + p.2 = x := by
    simpa only [a, Submodule.coe_prodEquivOfIsCompl'] using hp
  have hz : -θ p.1 ∈ center R L := (center R L).neg_mem (θ.apply_mem_center p.1.2)
  have hd : -θ p.2 ∈ derivedSeries R L 1 :=
    (derivedSeries R L 1).neg_mem (θ.apply_mem_derivedSeries 1 p.2.2)
  have hneg : ((⟨-θ p.1, hz⟩ : center R L), (⟨-θ p.2, hd⟩ : derivedSeries R L 1)) = p := by
    apply a.injective
    calc a (⟨-θ p.1, hz⟩, ⟨-θ p.2, hd⟩) = -θ p.1 + -θ p.2 :=
          Submodule.coe_prodEquivOfIsCompl' _ _ _ _
      _ = -θ ((p.1 : L) + p.2) := by rw [map_add, neg_add]
      _ = x := by rw [hsum, mem_cartanP_iff.mp x.2, neg_neg]
      _ = a p := hp.symm
  have hp1 : θ p.1 = -p.1 := neg_eq_iff_eq_neg.mp (congrArg (fun q ↦ (q.1 : L)) hneg)
  have hp2 : θ p.2 = -p.2 := neg_eq_iff_eq_neg.mp (congrArg (fun q ↦ (q.2 : L)) hneg)
  refine ⟨p, ⟨hp1, hp2, hsum⟩, fun q hq ↦ a.injective ?_⟩
  simpa only [a, Submodule.coe_prodEquivOfIsCompl'] using hq.2.2.trans hsum.symm

/-- Addition identifies `(θ.cartanP ⊓ center R L) × (θ.cartanP ⊓ derivedSeries R L 1)` linearly
with `θ.cartanP` whenever `center R L` and `derivedSeries R L 1` are complementary. -/
noncomputable def cartanPCenterDerivedEquiv (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    (↥(θ.cartanP ⊓ (center R L).toSubmodule) ×
      ↥(θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule)) ≃ₗ[R] θ.cartanP :=
  LinearEquiv.ofBijective
    { toFun := fun p ↦ ⟨(p.1 : L) + p.2, θ.cartanP.add_mem p.1.2.1 p.2.2.1⟩
      map_add' := fun _ _ ↦ Subtype.ext (by simp; abel)
      map_smul' := fun _ _ ↦ Subtype.ext (by simp [smul_add]) }
    ⟨fun p q hpq ↦ by
      let a := (center R L).toSubmodule.prodEquivOfIsCompl (derivedSeries R L 1).toSubmodule
        (LieSubmodule.isCompl_toSubmodule.mpr h)
      have hpair : ((⟨(p.1 : L), p.1.2.2⟩ : center R L),
          (⟨(p.2 : L), p.2.2.2⟩ : derivedSeries R L 1)) =
          (⟨(q.1 : L), q.1.2.2⟩, ⟨(q.2 : L), q.2.2.2⟩) := by
        apply a.injective
        simpa only [a, Submodule.coe_prodEquivOfIsCompl', LinearMap.coe_mk, AddHom.coe_mk] using
          congrArg Subtype.val hpq
      exact Prod.ext (Subtype.ext (congrArg (fun r ↦ (r.1 : L)) hpair))
        (Subtype.ext (congrArg (fun r ↦ (r.2 : L)) hpair)),
    fun x ↦ by
      obtain ⟨p, hp, -⟩ := θ.existsUnique_cartanP_center_add_cartanP_derivedSeries h x
      exact ⟨(⟨p.1, mem_cartanP_iff.mpr hp.1, p.1.2⟩,
        ⟨p.2, mem_cartanP_iff.mpr hp.2.1, p.2.2⟩), Subtype.ext hp.2.2⟩⟩

@[simp]
theorem cartanPCenterDerivedEquiv_apply (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (p : ↥(θ.cartanP ⊓ (center R L).toSubmodule) ×
      ↥(θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule)) :
    (θ.cartanPCenterDerivedEquiv h p : L) = (p.1 : L) + p.2 :=
  (rfl)

@[simp]
theorem cartanPCenterDerivedEquiv_symm_add (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) (x : θ.cartanP) :
    (((θ.cartanPCenterDerivedEquiv h).symm x).1 : L) +
      ((θ.cartanPCenterDerivedEquiv h).symm x).2 = x := by
  rw [← θ.cartanPCenterDerivedEquiv_apply h, LinearEquiv.apply_symm_apply]

/-- The central and derived parts of `θ.cartanP` are disjoint when `center R L` and
`derivedSeries R L 1` are complementary. -/
theorem disjoint_cartanP_inf_center_inf_derivedSeries (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    Disjoint (θ.cartanP ⊓ (center R L).toSubmodule)
      (θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule) :=
  (LieSubmodule.isCompl_toSubmodule.mpr h).disjoint.mono inf_le_right inf_le_right

/-- **`𝔭 = (𝔭 ∩ 𝔷) ⊕ (𝔭 ∩ [L, L])`.** When `center R L` and `derivedSeries R L 1` are
complementary, `θ.cartanP` is the sum of its intersections with the centre and the derived ideal. -/
theorem cartanP_eq_sup_inf_center_inf_derivedSeries (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    θ.cartanP =
      (θ.cartanP ⊓ (center R L).toSubmodule) ⊔ (θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule) := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨p, hp, -⟩ := θ.existsUnique_cartanP_center_add_cartanP_derivedSeries h ⟨x, hx⟩
  exact Submodule.mem_sup.mpr ⟨p.1, ⟨mem_cartanP_iff.mpr hp.1, p.1.2⟩,
    p.2, ⟨mem_cartanP_iff.mpr hp.2.1, p.2.2⟩, hp.2.2⟩

end CommRing

/-! ### The reductive Cartan involution predicate -/

section Preorder

variable {R L M : Type*} [CommRing R] [Preorder R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- An automorphism `θ : L ≃ₗ⁅R⁆ L` is a **reductive Cartan involution** when `θ` is involutive on
`L` and its restriction `θ.restrictDerivedSeries 1` to the derived ideal `derivedSeries R L 1` is a
Cartan involution. -/
def IsReductiveCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop :=
  Function.Involutive θ ∧ (θ.restrictDerivedSeries 1).IsCartanInvolution

/-- Unfolded definition of `LieEquiv.IsReductiveCartanInvolution`. -/
theorem isReductiveCartanInvolution_def (θ : L ≃ₗ⁅R⁆ L) :
    θ.IsReductiveCartanInvolution ↔
      Function.Involutive θ ∧ (θ.restrictDerivedSeries 1).IsCartanInvolution :=
  Iff.rfl

/-- Intertwining Lie equivalences preserve and reflect reductive Cartan involutions. -/
theorem isReductiveCartanInvolution_iff_of_intertwines {θ₁ : L ≃ₗ⁅R⁆ L} {θ₂ : M ≃ₗ⁅R⁆ M}
    (e : L ≃ₗ⁅R⁆ M) (h : θ₂.toLieHom.comp e.toLieHom = e.toLieHom.comp θ₁.toLieHom) :
    θ₁.IsReductiveCartanInvolution ↔ θ₂.IsReductiveCartanInvolution := by
  have hfun (z : L) : θ₂ (e z) = e (θ₁ z) := LieHom.congr_fun h z
  have hd : (θ₂.restrictDerivedSeries 1).toLieHom.comp (e.restrictDerivedSeries 1).toLieHom =
      (e.restrictDerivedSeries 1).toLieHom.comp (θ₁.restrictDerivedSeries 1).toLieHom :=
    LieHom.ext fun x ↦ Subtype.ext (by
      simp only [LieHom.comp_apply, coe_toLieHom, coe_restrictDerivedSeries]
      exact hfun x)
  refine ⟨fun ⟨hinv, hc⟩ ↦ ⟨fun y ↦ ?_, (isCartanInvolution_iff_of_intertwines _ hd).mp hc⟩,
    fun ⟨hinv, hc⟩ ↦ ⟨fun x ↦ ?_, (isCartanInvolution_iff_of_intertwines _ hd).mpr hc⟩⟩
  · rw [← e.apply_symm_apply y, hfun, hfun, hinv]
  · calc θ₁ (θ₁ x) = e.symm (e (θ₁ (θ₁ x))) := (e.symm_apply_apply _).symm
      _ = e.symm (θ₂ (θ₂ (e x))) := by rw [← hfun (θ₁ x), ← hfun x]
      _ = x := by rw [hinv (e x), e.symm_apply_apply]

/-- When `L` is perfect (`derivedSeries R L 1 = ⊤`), `θ.restrictDerivedSeries 1` is a Cartan
involution if and only if `θ` is. -/
theorem isCartanInvolution_restrictDerivedSeries_one_iff_of_eq_top (θ : L ≃ₗ⁅R⁆ L)
    (htop : derivedSeries R L 1 = ⊤) :
    (θ.restrictDerivedSeries 1).IsCartanInvolution ↔ θ.IsCartanInvolution := by
  let e : derivedSeries R L 1 ≃ₗ⁅R⁆ L :=
    ofBijective (derivedSeries R L 1).incl
      ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, htop ▸ LieSubmodule.mem_top x⟩, rfl⟩⟩
  have he : θ.toLieHom.comp e.toLieHom = e.toLieHom.comp (θ.restrictDerivedSeries 1).toLieHom :=
    LieHom.ext fun x ↦ (θ.coe_restrictDerivedSeries 1 x).symm
  exact isCartanInvolution_iff_of_intertwines e he

/-- On an abelian Lie algebra, `derivedSeries R L 1` is trivial, so `IsReductiveCartanInvolution`
is equivalent to `Function.Involutive`. -/
theorem isReductiveCartanInvolution_iff_involutive [IsLieAbelian L] (θ : L ≃ₗ⁅R⁆ L) :
    θ.IsReductiveCartanInvolution ↔ Function.Involutive θ := by
  refine ⟨And.left, fun hθ ↦ ⟨hθ, (isCartanInvolution_def _).mpr
    ⟨θ.involutive_restrictDerivedSeries hθ 1, fun x hx ↦ ?_⟩⟩⟩
  have hbot : (derivedSeries R L 1).toSubmodule = ⊥ := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule, coe_derivedSeries_one_eq, Submodule.span_eq_bot]
    rintro _ ⟨a, b, rfl⟩
    exact trivial_lie_zero L L a b
  have hx0 : (x : L) = 0 := by
    have hmem : (x : L) ∈ (derivedSeries R L 1).toSubmodule := x.2
    rwa [hbot, Submodule.mem_bot] at hmem
  exact False.elim (hx (Subtype.ext hx0))

/-- Along a decomposition `L = center R L ⊕ derivedSeries R L 1`, the assembled automorphism
`ofCenterDerived h e_z e_d` is a reductive Cartan involution if and only if `e_z` is involutive and
`e_d` is a Cartan involution. -/
@[simp]
theorem isReductiveCartanInvolution_ofCenterDerived_iff
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (e_z : center R L ≃ₗ⁅R⁆ center R L)
    (e_d : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived h e_z e_d).IsReductiveCartanInvolution ↔
      Function.Involutive e_z ∧ e_d.IsCartanInvolution := by
  rw [isReductiveCartanInvolution_def, involutive_ofCenterDerived_iff,
    restrictDerivedSeries_one_ofCenterDerived]
  exact ⟨fun ⟨⟨hz, _⟩, hd⟩ ↦ ⟨hz, hd⟩, fun ⟨hz, hd⟩ ↦ ⟨⟨hz, (isCartanInvolution_def _).mp hd |>.1⟩,
    hd⟩⟩

end Preorder

section LinearOrderField

variable {K L : Type*} [Field K] [LinearOrder K] [LieRing L] [LieAlgebra K L]

/-- Every semisimple Cartan involution over a linearly ordered field is also a reductive Cartan
involution, since a Killing Lie algebra over a field is perfect. -/
theorem IsCartanInvolution.isReductiveCartanInvolution {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) : θ.IsReductiveCartanInvolution := by
  have := hθ.isKilling
  have htop := TauCeti.derivedSeries_one_eq_top_of_isKilling K L
  exact ⟨hθ.involutive, (θ.isCartanInvolution_restrictDerivedSeries_one_iff_of_eq_top htop).mpr hθ⟩

/-- When `center K L = ⊥`, reductive and semisimple Cartan involutions coincide. -/
theorem isReductiveCartanInvolution_iff_isCartanInvolution_of_center_eq_bot
    (θ : L ≃ₗ⁅K⁆ L) (hc : center K L = ⊥) :
    θ.IsReductiveCartanInvolution ↔ θ.IsCartanInvolution := by
  refine ⟨fun hθ ↦ ?_, IsCartanInvolution.isReductiveCartanInvolution⟩
  have := hθ.2.isKilling
  have hcompl := TauCeti.isCompl_center_derivedSeries_of_isKilling_derivedSeries (K := K) (L := L)
  have htop : derivedSeries K L 1 = ⊤ := by
    have hsup := hcompl.codisjoint.eq_top
    rwa [hc, bot_sup_eq] at hsup
  exact (θ.isCartanInvolution_restrictDerivedSeries_one_iff_of_eq_top htop).mp hθ.2

/-- On a Lie algebra with trivial radical, reductive and semisimple Cartan involutions coincide. -/
theorem isReductiveCartanInvolution_iff_isCartanInvolution [HasTrivialRadical K L]
    (θ : L ≃ₗ⁅K⁆ L) :
    θ.IsReductiveCartanInvolution ↔ θ.IsCartanInvolution :=
  θ.isReductiveCartanInvolution_iff_isCartanInvolution_of_center_eq_bot
    (LieAlgebra.center_eq_bot K L)

end LinearOrderField

namespace IsReductiveCartanInvolution

section PartialOrder

variable {R L : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]
  {θ : L ≃ₗ⁅R⁆ L} (hθ : θ.IsReductiveCartanInvolution)
include hθ

/-- A reductive Cartan involution is involutive on `L`. -/
theorem involutive : Function.Involutive θ :=
  hθ.1

/-- A reductive Cartan involution equals its own inverse. -/
theorem symm_eq : θ.symm = θ :=
  LieEquiv.ext fun x ↦ θ.symm_apply_eq.mpr (hθ.involutive x).symm

/-- The restriction of a reductive Cartan involution to `derivedSeries R L 1` is a Cartan
involution. -/
theorem isCartanInvolution_restrictDerivedSeries :
    (θ.restrictDerivedSeries 1).IsCartanInvolution :=
  hθ.2

/-- The restriction of a reductive Cartan involution to `center R L` is involutive. -/
theorem involutive_restrictCenter : Function.Involutive θ.restrictCenter :=
  θ.involutive_restrictCenter hθ.involutive

end PartialOrder

section LinearOrderField

variable {K L : Type*} [Field K] [LinearOrder K] [LieRing L] [LieAlgebra K L]
  {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsReductiveCartanInvolution)
include hθ

/-- The derived ideal of a Lie algebra admitting a reductive Cartan involution is Killing. -/
theorem isKilling_derivedSeries : IsKilling K (derivedSeries K L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.isKilling

/-- The derived ideal of a Lie algebra admitting a reductive Cartan involution is
finite-dimensional. -/
theorem finiteDimensional_derivedSeries : FiniteDimensional K (derivedSeries K L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.finiteDimensional

/-- The derived ideal of a Lie algebra admitting a reductive Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries : IsSemisimple K (derivedSeries K L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.isSemisimple

/-- **Automatic reductivity.** Over a linearly ordered field, a Lie algebra admitting a reductive
Cartan involution has central radical. -/
theorem hasCentralRadical : HasCentralRadical K L :=
  have := hθ.isKilling_derivedSeries
  TauCeti.hasCentralRadical_of_isKilling_derivedSeries

/-- **Automatic centre/derived splitting.** Over a linearly ordered field, a Lie algebra admitting a
reductive Cartan involution splits as `center K L ⊕ derivedSeries K L 1`. -/
theorem isCompl_center_derivedSeries : IsCompl (center K L) (derivedSeries K L 1) :=
  have := hθ.isKilling_derivedSeries
  TauCeti.isCompl_center_derivedSeries_of_isKilling_derivedSeries

/-- For a reductive Cartan involution over a linearly ordered field, `𝔭 ∩ 𝔷` and `𝔭 ∩ [L, L]` are
disjoint. -/
theorem disjoint_cartanP_inf_center_inf_derivedSeries :
    Disjoint (θ.cartanP ⊓ (center K L).toSubmodule)
      (θ.cartanP ⊓ (derivedSeries K L 1).toSubmodule) :=
  θ.disjoint_cartanP_inf_center_inf_derivedSeries hθ.isCompl_center_derivedSeries

/-- For a reductive Cartan involution over a linearly ordered field,
`𝔭 = (𝔭 ∩ 𝔷) ⊕ (𝔭 ∩ [L, L])`. -/
theorem cartanP_eq_sup_inf_center_inf_derivedSeries :
    θ.cartanP =
      (θ.cartanP ⊓ (center K L).toSubmodule) ⊔ (θ.cartanP ⊓ (derivedSeries K L 1).toSubmodule) :=
  θ.cartanP_eq_sup_inf_center_inf_derivedSeries hθ.isCompl_center_derivedSeries

/-- Linear equivalence `(𝔭 ∩ 𝔷) × (𝔭 ∩ [L, L]) ≃ₗ[K] 𝔭` for a reductive Cartan involution. -/
noncomputable def cartanPCenterDerivedEquiv :
    (↥(θ.cartanP ⊓ (center K L).toSubmodule) ×
      ↥(θ.cartanP ⊓ (derivedSeries K L 1).toSubmodule)) ≃ₗ[K] θ.cartanP :=
  θ.cartanPCenterDerivedEquiv hθ.isCompl_center_derivedSeries

end LinearOrderField

section OrderedField

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [LieRing L] [LieAlgebra K L]

/-- Over an ordered field, a reductive Cartan involution splits `L` as `𝔨 ⊕ 𝔭`. -/
theorem isCompl_fixedSubalgebra_cartanP {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsReductiveCartanInvolution) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP :=
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  LieEquiv.isCompl_fixedSubalgebra_cartanP hθ.involutive

end OrderedField

end IsReductiveCartanInvolution

end LieEquiv
