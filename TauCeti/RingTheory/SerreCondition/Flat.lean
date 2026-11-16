/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import TauCeti.RingTheory.SerreCondition.Normal
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.Algebra.DualNumber.Basic
import TauCeti.RingTheory.Depth.Flat
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.Localization.Reduced
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Serre's conditions, reducedness, and normality along flat homomorphisms

Let `R → S` be a flat homomorphism of rings with `S` Noetherian. For a prime `q` of `S` lying over
`p = q ∩ R` and corresponding to the prime `Q` of the fibre `κ(p) ⊗[R] S`, the local map
`R_p → S_q` is faithfully flat with closed fibre `S_q ⧸ 𝔪_{R_p} S_q ≃ (κ(p) ⊗[R] S)_Q`. Both
dimension and depth are additive along `R_p → S_q`:
`dim S_q = dim R_p + dim (S_q ⧸ 𝔪_{R_p} S_q)` and
`depth S_q = depth R_p + depth (S_q ⧸ 𝔪_{R_p} S_q)`.

From these two formulas follow ascent and descent of Serre's conditions `(R_n)` and `(S_n)`:

* **Ascent from base and fibres:** If `R` and every fibre `κ(p) ⊗[R] S` satisfy `(R_n)`, so does
  `S`: when `ht q ≤ n`, the dimension formula gives `ht p + ht Q = ht q ≤ n`, so both `R_p` and
  `(κ(p) ⊗[R] S)_Q` are regular local rings, and regularity ascends along `R_p → S_q`. Likewise,
  since `min(n, a) + min(n, b) ≥ min(n, a + b)`, if `R` and every fibre satisfy `(S_n)` then `S`
  satisfies `(S_n)`.
* **Descent along faithfully flat maps:** When `R → S` is faithfully flat, every fibre
  `κ(p) ⊗[R] S` is nonzero and therefore has a minimal prime `Q`. At the corresponding prime `q`
  of `S`, the closed fibre `(κ(p) ⊗[R] S)_Q` has dimension zero and depth zero, so `ht q = ht p`,
  `dim S_q = dim R_p`, and `depth S_q = depth R_p`. Both `(R_n)` and `(S_n)` therefore descend
  from `S` to `R`.

Unlike Cohen–Macaulayness (`Module.isCohenMacaulay_self_iff_of_flat`), `(R_n)` and normality do
not descend from `S` to the fibres: `k[t, x, y] ⧸ (y² - x³ - t)` is regular and flat over `k[t]`,
while its fibre `k[x, y] ⧸ (y² - x³)` over `(t)` fails `(R_1)` at the cusp.

Combining `(R_0) + (S_1)` and `(R_1) + (S_2)` gives ascent of reducedness along flat maps with
reduced fibres, and ascent and faithful-flatness descent of normality (every localization at a
prime an integrally closed domain). None of the ascent results assume `R` or its fibres to be
globally Noetherian: at each prime `q` of `S`, faithful flatness of `R_p → S_q` makes `R_p`
Noetherian, and `(κ(p) ⊗[R] S)_Q` is a quotient of `S_q`.

## Main results

* `IsLocalRing.min_ringKrullDim_le_depth_of_flat` and
  `IsLocalRing.min_ringKrullDim_le_depth_iff_of_flat_of_ringKrullDim_quotient_eq_zero`: the local
  `(S_n)` bound ascends along flat local homomorphisms and is invariant when the closed fibre has
  dimension zero.
* `Ring.SatisfiesSerreR.isRegularLocalRing`, `Module.SatisfiesSerreS.min_ringKrullDim_le_depth`,
  and `Module.SatisfiesSerreS.of_krullDimLE_zero`: evaluate `(R_n)` and `(S_n)` directly on a local
  ring, and discharge `(S_n)` on rings of Krull dimension at most zero.
* `Ring.SatisfiesSerreR.of_flat` and `Ring.SatisfiesSerreR.of_faithfullyFlat`: ascent of `(R_n)`
  from base and fibres along flat maps, and descent along faithfully flat maps.
* `Module.SatisfiesSerreS.of_flat` and `Module.SatisfiesSerreS.of_faithfullyFlat`: ascent of
  `(S_n)` from base and fibres along flat maps, and descent along faithfully flat maps.
* `TauCeti.isReduced_of_flat_of_isReduced_fiber`: a flat Noetherian algebra with reduced fibres
  over a reduced ring is reduced.
* `TauCeti.isDomain_localization_atPrime_of_flat`,
  `TauCeti.isIntegrallyClosed_localization_atPrime_of_flat`, and
  `TauCeti.isIntegrallyClosed_of_flat`: normality ascends along flat maps with normal fibres.
* `TauCeti.isDomain_localization_atPrime_of_faithfullyFlat` and
  `TauCeti.isIntegrallyClosed_localization_atPrime_of_faithfullyFlat`: normality descends along
  faithfully flat maps with Noetherian target.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.9 and its Corollary.
* [Stacks Project, Lemma 10.163.4](https://stacks.math.columbia.edu/tag/0339) and
  [Lemma 10.164.3](https://stacks.math.columbia.edu/tag/033G).
-/

public section

universe u v

open IsLocalRing Algebra.TensorProduct

namespace IsLocalRing

section Local

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [IsLocalRing S] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S] {n : ℕ}

/-- **The local `(S_n)` bound along a flat local homomorphism.** For a flat local homomorphism
`R → S` of local rings with `S` Noetherian, if `depth R ≥ min (n, dim R)` and
`depth (S ⧸ 𝔪_R S) ≥ min (n, dim (S ⧸ 𝔪_R S))`, then `depth S ≥ min (n, dim S)`. -/
theorem min_ringKrullDim_le_depth_of_flat
    (hR : min (n : WithBot ℕ∞) (ringKrullDim R) ≤ (depth (ModuleCat.of R R) : WithBot ℕ∞))
    (hF : min (n : WithBot ℕ∞) (ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S))) ≤
      (depth (ModuleCat.of S (S ⧸ (maximalIdeal R).map (algebraMap R S))) : WithBot ℕ∞)) :
    min (n : WithBot ℕ∞) (ringKrullDim S) ≤ (depth (ModuleCat.of S S) : WithBot ℕ∞) := by
  have : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  have : IsNoetherianRing R := .of_faithfullyFlat S
  set I := (maximalIdeal R).map (algebraMap R S)
  have : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top (algebraMap R S)).ne
  have hnat {x : ℕ∞} {m : ℕ} (h : (x : WithBot ℕ∞) ≤ m) : ∃ c : ℕ, x = c := by
    obtain ⟨c, hc, -⟩ := ENat.le_natCast_iff.mp (WithBot.coe_le_coe.mp h)
    exact ⟨c, hc⟩
  obtain ⟨a, ha⟩ := Module.exists_supportDim_eq_natCast (R := R) (M := R)
  obtain ⟨b, hb⟩ := Module.exists_supportDim_eq_natCast (R := S) (M := S ⧸ I)
  obtain ⟨c, hc⟩ := hnat (ha ▸ depth_le_supportDim (R := R) (M := R))
  obtain ⟨d, hd⟩ := hnat (hb ▸ depth_le_supportDim (R := S) (M := S ⧸ I))
  rw [Module.supportDim_self_eq_ringKrullDim] at ha
  rw [Module.supportDim_quotient_eq_ringKrullDim] at hb
  have hcast (x y : ℕ) :
      min (x : WithBot ℕ∞) (y : WithBot ℕ∞) = ((min x y : ℕ) : WithBot ℕ∞) := by
    rcases le_total x y with hxy | hxy
    · rw [min_eq_left (by exact_mod_cast hxy), min_eq_left hxy]
    · rw [min_eq_right (by exact_mod_cast hxy), min_eq_right hxy]
  rw [ha, hc, hcast] at hR
  rw [hb, hd, hcast] at hF
  rw [TauCeti.ringKrullDim_eq_ringKrullDim_add_ringKrullDim_quotient_map_maximalIdeal R (S := S),
    depth_eq_add_of_flat (R := R) (S := S), ha, hb, hc, hd,
    show (a : WithBot ℕ∞) + b = ((a + b : ℕ) : WithBot ℕ∞) by norm_cast, hcast]
  norm_cast at hR hF ⊢
  omega

/-- Along a flat local homomorphism `R → S` with `S` Noetherian whose closed fibre `S ⧸ 𝔪_R S` has
Krull dimension zero, the `(S_n)` depth bound holds for `S` if and only if it holds for `R`. -/
theorem min_ringKrullDim_le_depth_iff_of_flat_of_ringKrullDim_quotient_eq_zero
    (hdim : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0) :
    min (n : WithBot ℕ∞) (ringKrullDim S) ≤ (depth (ModuleCat.of S S) : WithBot ℕ∞) ↔
      min (n : WithBot ℕ∞) (ringKrullDim R) ≤ (depth (ModuleCat.of R R) : WithBot ℕ∞) := by
  have : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  have : IsNoetherianRing R := .of_faithfullyFlat S
  rw [TauCeti.ringKrullDim_eq_ringKrullDim_add_ringKrullDim_quotient_map_maximalIdeal R (S := S),
    hdim, add_zero, depth_eq_of_flat_of_ringKrullDim_quotient_eq_zero hdim]

end Local

end IsLocalRing

section FiberHelpers

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Identifies the closed fibre `S_q ⧸ 𝔪_{R_p} S_q` of `R_p → S_q` with the local ring
`(κ(p) ⊗[R] S)_Q` of the fibre at the prime `Q` corresponding to `q`, using the `Mul` and `Add`
projections of `CommRing` rather than `OreLocalization`'s unexposed instances. -/
private noncomputable def closedFiberEquiv (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S))
    [Q.IsPrime] :
    letI q := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
    letI := Localization.AtPrime.algebraOfLiesOver p q
    @RingEquiv (Localization.AtPrime q ⧸
        (maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)))
      (Localization.AtPrime Q)
      (@Distrib.toMul _ (@instDistribOfSemiring _ CommRing.toCommSemiring.toSemiring))
      (@Distrib.toMul _ (@instDistribOfSemiring _ CommRing.toCommSemiring.toSemiring))
      (@Distrib.toAdd _ (@instDistribOfSemiring _ CommRing.toCommSemiring.toSemiring))
      (@Distrib.toAdd _ (@instDistribOfSemiring _ CommRing.toCommSemiring.toSemiring)) :=
  let q := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hI : p.map (algebraMap R (Localization.AtPrime q)) =
      (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e₀ := (Ideal.quotEquivOfEq hI.symm).trans
    (Ideal.Fiber.localizationAlgEquivQuotient p Q).toRingEquiv.symm
  { toEquiv := e₀.toEquiv, map_mul' := e₀.map_mul, map_add' := e₀.map_add }

/-- For a flat `R`-algebra `S` with `S` Noetherian and a prime `Q` of the fibre `κ(p) ⊗[R] S`
contracting to `q`, the height of `q` is `ht p + ht Q` and the closed fibre of `R_p → S_q` has
Krull dimension `ht Q`. -/
private theorem height_comap_includeRight_eq_add [IsNoetherianRing S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime] :
    letI q := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
    letI := Localization.AtPrime.algebraOfLiesOver p q
    q.height = p.height + Q.height ∧
      ringKrullDim (Localization.AtPrime q ⧸
        (maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))) = Q.height := by
  set q := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_flat_of_isLocalHom
  have : IsNoetherianRing (Localization.AtPrime p) := .of_faithfullyFlat (Localization.AtPrime q)
  have hfib : ringKrullDim (Localization.AtPrime q ⧸
      (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))) = Q.height :=
    (ringKrullDim_eq_of_ringEquiv (closedFiberEquiv p Q)).trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q))
  have hdim := TauCeti.ringKrullDim_eq_ringKrullDim_add_ringKrullDim_quotient_map_maximalIdeal
    (Localization.AtPrime p) (S := Localization.AtPrime q)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q,
    IsLocalization.AtPrime.ringKrullDim_eq_height p, hfib, ← WithBot.coe_add] at hdim
  exact ⟨WithBot.coe_inj.mp hdim, hfib⟩

/-- Over every prime `p` of the base of a faithfully flat Noetherian algebra `S`, there is a prime
`q` of `S` minimal in the fibre over `p`, so that `ht q = ht p` and the closed fibre of
`R_p → S_q` has dimension zero. -/
private theorem exists_liesOver_ringKrullDim_quotient_eq_zero [IsNoetherianRing S]
    [Module.FaithfullyFlat R S] (p : Ideal R) [p.IsPrime] :
    ∃ (q : Ideal S) (_ : q.IsPrime) (_ : q.LiesOver p),
      letI := Localization.AtPrime.algebraOfLiesOver p q
      q.height = p.height ∧
        ringKrullDim (Localization.AtPrime q ⧸
          (maximalIdeal (Localization.AtPrime p)).map
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))) = 0 := by
  obtain ⟨q₀, hq₀, hlies₀⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) p
  let Q₀ := (PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q₀, hq₀, hlies₀⟩).asIdeal
  obtain ⟨Q, hQmin, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (p.Fiber S)) ≤ Q₀)
  have : Q.IsPrime := hQmin.isPrime
  obtain ⟨hh, hfib⟩ := height_comap_includeRight_eq_add (S := S) p Q
  have hQ0 : Q.height = 0 := Ideal.height_eq_zero_iff.2 hQmin
  refine ⟨Q.comap (includeRight : S →ₐ[R] p.Fiber S), inferInstance, inferInstance, ?_, ?_⟩
  · rw [hh, hQ0, add_zero]
  · rw [hfib, hQ0, WithBot.coe_zero]

end FiberHelpers

namespace Ring.SatisfiesSerreR

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

/-- A local ring of dimension at most `n` satisfying `(R_n)` is a regular local ring. -/
theorem isRegularLocalRing [IsLocalRing R] (h : SatisfiesSerreR n R)
    (hdim : ringKrullDim R ≤ n) : IsRegularLocalRing R := by
  let e : R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl fun _ hx ↦ notMem_maximalIdeal.mp hx
  have hm : (maximalIdeal R).height ≤ n := by
    rw [← WithBot.coe_le_coe, maximalIdeal_height_eq_ringKrullDim]
    exact hdim
  have := satisfiesSerreR_iff.1 h (maximalIdeal R) hm
  exact .of_ringEquiv e.symm.toRingEquiv

/-- **Serre's condition `(R_n)` ascends along flat homomorphisms.** Let `S` be a flat Noetherian
`R`-algebra. If `R` and every fibre `κ(p) ⊗[R] S` satisfy `(R_n)`, then `S` satisfies `(R_n)`.
H. Matsumura, *Commutative Ring Theory*, Theorem 23.9 (i). -/
theorem of_flat [IsNoetherianRing S] [Module.Flat R S] (hR : SatisfiesSerreR n R)
    (hf : ∀ (p : Ideal R) [p.IsPrime], SatisfiesSerreR n (p.Fiber S)) :
    SatisfiesSerreR n S := by
  rw [satisfiesSerreR_iff] at hR ⊢
  intro q _ hq
  obtain ⟨p, _, _⟩ : ∃ p : Ideal R, p.IsPrime ∧ q.LiesOver p := ⟨q.under R, inferInstance, ⟨rfl⟩⟩
  obtain ⟨Q, _, rfl⟩ : ∃ Q : Ideal (p.Fiber S), Q.IsPrime ∧ Q.comap includeRight = q :=
    ⟨_, ((PrimeSpectrum.primesOverOrderIsoFiber R S p) ⟨q, ‹_›, ‹_›⟩).isPrime,
      congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply _)⟩
  set r := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
  let := Localization.AtPrime.algebraOfLiesOver p r
  obtain ⟨hh, -⟩ := height_comap_includeRight_eq_add (S := S) p Q
  have := hR p (le_self_add.trans (hh ▸ hq))
  have := (satisfiesSerreR_iff.1 (hf p)) Q (le_add_self.trans (hh ▸ hq))
  have := IsRegularLocalRing.of_ringEquiv (closedFiberEquiv p Q).symm
  exact TauCeti.IsRegularLocalRing.of_hasGoingDown_of_quotient_map_maximalIdeal
    (R := Localization.AtPrime p)

/-- **Serre's condition `(R_n)` descends along faithfully flat homomorphisms.** If `S` is a
Noetherian faithfully flat `R`-algebra satisfying `(R_n)`, then `R` satisfies `(R_n)`. -/
theorem of_faithfullyFlat [IsNoetherianRing S] [Module.FaithfullyFlat R S]
    (hS : SatisfiesSerreR n S) : SatisfiesSerreR n R := by
  rw [satisfiesSerreR_iff] at hS ⊢
  intro p _ hp
  obtain ⟨q, _, _, hq, -⟩ := exists_liesOver_ringKrullDim_quotient_eq_zero (S := S) p
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have := hS q (hq ▸ hp)
  exact TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom (S := Localization.AtPrime q)

end Ring.SatisfiesSerreR

namespace Module

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

/-- Every ring of Krull dimension at most zero satisfies `(S_n)` over itself for all `n`. -/
theorem SatisfiesSerreS.of_krullDimLE_zero [Ring.KrullDimLE 0 R] : SatisfiesSerreS n R R :=
  satisfiesSerreS_self_iff.2 fun p _ ↦ (min_le_right _ _).trans <| by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
      Ideal.height_eq_zero_iff.2 (Ideal.mem_minimalPrimes_iff_isPrime.2 ‹p.IsPrime›)]
    exact_mod_cast zero_le

/-- A local ring satisfying `(S_n)` over itself satisfies `depth R ≥ min (n, dim R)`. -/
theorem SatisfiesSerreS.min_ringKrullDim_le_depth [IsLocalRing R] (h : SatisfiesSerreS n R R) :
    min (n : WithBot ℕ∞) (ringKrullDim R) ≤ (depth (ModuleCat.of R R) : WithBot ℕ∞) := by
  let e : R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl fun _ hx ↦ notMem_maximalIdeal.mp hx
  have hm := satisfiesSerreS_self_iff.1 h (maximalIdeal R)
  rwa [ringKrullDim_eq_of_ringEquiv e.symm.toRingEquiv, e.symm.toRingEquiv.depth_self_eq] at hm

/-- **Pointwise `(S_n)` ascent along a flat algebra.** Let `S` be a flat Noetherian `R`-algebra
and `q` a prime of `S` lying over `p`. If `R_p` satisfies `depth R_p ≥ min (n, dim R_p)` and so
does the local ring of `κ(p) ⊗[R] S` at the prime corresponding to `q`, then
`depth S_q ≥ min (n, dim S_q)`. -/
theorem min_ringKrullDim_le_depth_localization_atPrime_of_flat [IsNoetherianRing S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hp : min (n : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p)) ≤
      (depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) : WithBot ℕ∞))
    (hq : ∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime], Q.comap includeRight = q →
      min (n : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime Q)) ≤
        (depth (R := Localization.AtPrime Q) (ModuleCat.of _ (Localization.AtPrime Q)) :
          WithBot ℕ∞)) :
    min (n : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q)) ≤
      (depth (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q)) : WithBot ℕ∞) := by
  obtain ⟨Q, _, rfl⟩ : ∃ Q : Ideal (p.Fiber S), Q.IsPrime ∧ Q.comap includeRight = q :=
    ⟨_, ((PrimeSpectrum.primesOverOrderIsoFiber R S p) ⟨q, ‹_›, ‹_›⟩).isPrime,
      congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply _)⟩
  set r := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
  let := Localization.AtPrime.algebraOfLiesOver p r
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime r)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  set I := (maximalIdeal (Localization.AtPrime p)).map
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime r))
  have : Nontrivial (Localization.AtPrime r ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (map_maximalIdeal_lt_top (algebraMap (Localization.AtPrime p) (Localization.AtPrime r))).ne
  have : IsLocalRing (Localization.AtPrime r ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let e := closedFiberEquiv p Q
  refine min_ringKrullDim_le_depth_of_flat (R := Localization.AtPrime p) hp ?_
  rw [ringKrullDim_eq_of_ringEquiv e,
    depth_eq_depth_of_surjective (R := Localization.AtPrime r) (T := Localization.AtPrime r ⧸ I)
      Ideal.Quotient.mk_surjective,
    e.depth_self_eq]
  exact hq Q rfl

/-- **Serre's condition `(S_n)` ascends along flat homomorphisms.** Let `S` be a flat Noetherian
`R`-algebra. If `R` and every fibre `κ(p) ⊗[R] S` satisfy `(S_n)`, then `S` satisfies `(S_n)`.
Stacks, Lemma 10.163.4 (0339); H. Matsumura, *Commutative Ring Theory*, Theorem 23.9 (ii). -/
@[stacks 0339]
theorem SatisfiesSerreS.of_flat [IsNoetherianRing S] [Module.Flat R S]
    (hR : SatisfiesSerreS n R R)
    (hf : ∀ (p : Ideal R) [p.IsPrime], SatisfiesSerreS n (p.Fiber S) (p.Fiber S)) :
    SatisfiesSerreS n S S :=
  satisfiesSerreS_self_iff.2 fun q _ ↦
    min_ringKrullDim_le_depth_localization_atPrime_of_flat (q.under R) q
      (satisfiesSerreS_self_iff.1 hR _) fun Q _ _ ↦ satisfiesSerreS_self_iff.1 (hf (q.under R)) Q

/-- **Serre's condition `(S_n)` descends along faithfully flat homomorphisms.** If `S` is a
Noetherian faithfully flat `R`-algebra satisfying `(S_n)`, then `R` satisfies `(S_n)`. -/
theorem SatisfiesSerreS.of_faithfullyFlat [IsNoetherianRing S] [Module.FaithfullyFlat R S]
    (hS : SatisfiesSerreS n S S) : SatisfiesSerreS n R R := by
  refine satisfiesSerreS_self_iff.2 fun p _ ↦ ?_
  obtain ⟨q, _, _, -, hdim⟩ := exists_liesOver_ringKrullDim_quotient_eq_zero (S := S) p
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  exact (min_ringKrullDim_le_depth_iff_of_flat_of_ringKrullDim_quotient_eq_zero hdim).mp
    (satisfiesSerreS_self_iff.1 hS q)

end Module

namespace TauCeti

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- **Reducedness ascends along flat homomorphisms with reduced fibres.** If `S` is a flat
Noetherian algebra over a reduced ring `R` and every fibre `κ(p) ⊗[R] S` is reduced, then `S` is
reduced. H. Matsumura, *Commutative Ring Theory*, Corollary of Theorem 23.9. -/
theorem isReduced_of_flat_of_isReduced_fiber [IsReduced R] [IsNoetherianRing S] [Module.Flat R S]
    (hf : ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber S)) : IsReduced S := by
  refine isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one.2
    ⟨IsReduced.satisfiesSerreR_zero.of_flat fun p _ ↦ @IsReduced.satisfiesSerreR_zero _ _ (hf p),
      Module.satisfiesSerreS_self_iff.2 fun q _ ↦ ?_⟩
  obtain ⟨p, _, _⟩ : ∃ p : Ideal R, p.IsPrime ∧ q.LiesOver p := ⟨q.under R, inferInstance, ⟨rfl⟩⟩
  refine Module.min_ringKrullDim_le_depth_localization_atPrime_of_flat p q ?_ fun Q _ hQ ↦ ?_
  · let := Localization.AtPrime.algebraOfLiesOver p q
    have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
      Localization.isLocalHom_localRingHom _ _ _ _
    have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
      .of_flat_of_isLocalHom
    have : IsNoetherianRing (Localization.AtPrime p) := .of_faithfullyFlat (Localization.AtPrime q)
    have : IsReduced (Localization.AtPrime p) := IsLocalization.isReduced p.primeCompl _
    exact (isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one.1
      ‹IsReduced (Localization.AtPrime p)›).2.min_ringKrullDim_le_depth
  · subst hQ
    let r := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
    let := Localization.AtPrime.algebraOfLiesOver p r
    have : IsNoetherianRing (Localization.AtPrime Q) :=
      isNoetherianRing_of_ringEquiv _ (closedFiberEquiv p Q)
    have := hf p
    have := IsLocalization.isReduced Q.primeCompl (Localization.AtPrime Q)
    exact ((isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one
      (R := Localization.AtPrime Q)).1 ‹_›).2.min_ringKrullDim_le_depth

/-- A Noetherian integrally closed domain satisfies `(R_1)` and `(S_2)`. -/
private theorem satisfiesSerreR_one_and_satisfiesSerreS_two_of_isIntegrallyClosed (A : Type*)
    [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A] :
    Ring.SatisfiesSerreR 1 A ∧ Module.SatisfiesSerreS 2 A A :=
  forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.1
    fun P _ ↦ ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors⟩

/-- Under normal local rings on `R` and on the fibres of `S`, `S` satisfies `(R_1)` and `(S_2)`. -/
private theorem satisfiesSerreR_one_and_satisfiesSerreS_two_of_flat [IsNoetherianRing S]
    [Module.Flat R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hf : ∀ (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime],
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    Ring.SatisfiesSerreR 1 S ∧ Module.SatisfiesSerreS 2 S S := by
  refine ⟨Ring.satisfiesSerreR_iff.2 fun q _ hq ↦ ?_,
    Module.satisfiesSerreS_self_iff.2 fun q _ ↦ ?_⟩
  · obtain ⟨p, _, _⟩ : ∃ p : Ideal R, p.IsPrime ∧ q.LiesOver p := ⟨q.under R, inferInstance, ⟨rfl⟩⟩
    obtain ⟨Q, _, rfl⟩ : ∃ Q : Ideal (p.Fiber S), Q.IsPrime ∧ Q.comap includeRight = q :=
      ⟨_, ((PrimeSpectrum.primesOverOrderIsoFiber R S p) ⟨q, ‹_›, ‹_›⟩).isPrime,
        congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply _)⟩
    set r := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
    let := Localization.AtPrime.algebraOfLiesOver p r
    have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime r)) :=
      Localization.isLocalHom_localRingHom _ _ _ _
    have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime r) :=
      .of_flat_of_isLocalHom
    have : IsNoetherianRing (Localization.AtPrime p) := .of_faithfullyFlat (Localization.AtPrime r)
    have : IsNoetherianRing (Localization.AtPrime Q) :=
      isNoetherianRing_of_ringEquiv _ (closedFiberEquiv p Q)
    obtain ⟨_, _⟩ := hR p
    obtain ⟨_, _⟩ := hf p Q
    obtain ⟨hh, -⟩ := height_comap_includeRight_eq_add (S := S) p Q
    have := (satisfiesSerreR_one_and_satisfiesSerreS_two_of_isIntegrallyClosed
        (Localization.AtPrime p)).1.isRegularLocalRing <| by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
      exact_mod_cast le_self_add.trans (hh ▸ hq)
    have := (satisfiesSerreR_one_and_satisfiesSerreS_two_of_isIntegrallyClosed
        (Localization.AtPrime Q)).1.isRegularLocalRing <| by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
      exact_mod_cast le_add_self.trans (hh ▸ hq)
    have := IsRegularLocalRing.of_ringEquiv (closedFiberEquiv p Q).symm
    exact IsRegularLocalRing.of_hasGoingDown_of_quotient_map_maximalIdeal
      (R := Localization.AtPrime p)
  · obtain ⟨p, _, _⟩ : ∃ p : Ideal R, p.IsPrime ∧ q.LiesOver p := ⟨q.under R, inferInstance, ⟨rfl⟩⟩
    refine Module.min_ringKrullDim_le_depth_localization_atPrime_of_flat p q ?_ fun Q _ hQ ↦ ?_
    · let := Localization.AtPrime.algebraOfLiesOver p q
      have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
        Localization.isLocalHom_localRingHom _ _ _ _
      have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
        .of_flat_of_isLocalHom
      have : IsNoetherianRing (Localization.AtPrime p) :=
        .of_faithfullyFlat (Localization.AtPrime q)
      obtain ⟨_, _⟩ := hR p
      exact (satisfiesSerreR_one_and_satisfiesSerreS_two_of_isIntegrallyClosed
        (Localization.AtPrime p)).2.min_ringKrullDim_le_depth
    · subst hQ
      let r := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
      let := Localization.AtPrime.algebraOfLiesOver p r
      have : IsNoetherianRing (Localization.AtPrime Q) :=
        isNoetherianRing_of_ringEquiv _ (closedFiberEquiv p Q)
      obtain ⟨_, _⟩ := hf p Q
      exact (satisfiesSerreR_one_and_satisfiesSerreS_two_of_isIntegrallyClosed
        (Localization.AtPrime Q)).2.min_ringKrullDim_le_depth

/-- **Normal local rings ascend along flat homomorphisms (domain part).** If `S` is a flat
Noetherian `R`-algebra and all localizations at primes of `R` and of the fibres `κ(p) ⊗[R] S` are
integrally closed domains, then every localization `S_q` at a prime is a domain.
H. Matsumura, *Commutative Ring Theory*, Corollary of Theorem 23.9. -/
theorem isDomain_localization_atPrime_of_flat [IsNoetherianRing S] [Module.Flat R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hf : ∀ (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime],
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q))
    (q : Ideal S) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  (forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.2
    (satisfiesSerreR_one_and_satisfiesSerreS_two_of_flat hR hf) q).1

/-- **Normal local rings ascend along flat homomorphisms (integral closedness part).** If `S` is a
flat Noetherian `R`-algebra and all localizations at primes of `R` and of the fibres `κ(p) ⊗[R] S`
are integrally closed domains, then every localization `S_q` at a prime is integrally closed.
H. Matsumura, *Commutative Ring Theory*, Corollary of Theorem 23.9. -/
theorem isIntegrallyClosed_localization_atPrime_of_flat [IsNoetherianRing S] [Module.Flat R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hf : ∀ (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime],
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q))
    (q : Ideal S) [q.IsPrime] : IsIntegrallyClosed (Localization.AtPrime q) :=
  (forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.2
    (satisfiesSerreR_one_and_satisfiesSerreS_two_of_flat hR hf) q).2

/-- **Integral closedness ascends along flat homomorphisms with normal fibres.** If `S` is a flat
Noetherian `R`-algebra and all localizations at primes of `R` and of the fibres `κ(p) ⊗[R] S` are
integrally closed domains, then `S` is integrally closed in its total ring of fractions. -/
theorem isIntegrallyClosed_of_flat [IsNoetherianRing S] [Module.Flat R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hf : ∀ (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime],
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    IsIntegrallyClosed S :=
  let ⟨hR₁, hS₂⟩ := satisfiesSerreR_one_and_satisfiesSerreS_two_of_flat hR hf
  isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two hR₁ hS₂

/-- **Normality descends along faithfully flat homomorphisms (domain part).** If `S` is a
Noetherian faithfully flat `R`-algebra whose localizations at primes are integrally closed domains,
then every localization `R_p` at a prime is a domain. Stacks, Lemma 10.164.3 (033G). -/
@[stacks 033G "domain part"]
theorem isDomain_localization_atPrime_of_faithfullyFlat [IsNoetherianRing S]
    [Module.FaithfullyFlat R S]
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal R) [p.IsPrime] : IsDomain (Localization.AtPrime p) := by
  have : IsNoetherianRing R := .of_faithfullyFlat S
  obtain ⟨hR₁, hS₂⟩ :=
    forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.1 hS
  exact (forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.2
    ⟨hR₁.of_faithfullyFlat, hS₂.of_faithfullyFlat⟩ p).1

/-- **Normality descends along faithfully flat homomorphisms (integral closedness part).** If `S`
is a Noetherian faithfully flat `R`-algebra whose localizations at primes are integrally closed
domains, then every localization `R_p` at a prime is integrally closed. Stacks, Lemma 10.164.3
(033G). -/
@[stacks 033G "integrally closed part"]
theorem isIntegrallyClosed_localization_atPrime_of_faithfullyFlat [IsNoetherianRing S]
    [Module.FaithfullyFlat R S]
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal R) [p.IsPrime] : IsIntegrallyClosed (Localization.AtPrime p) := by
  have : IsNoetherianRing R := .of_faithfullyFlat S
  obtain ⟨hR₁, hS₂⟩ :=
    forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.1 hS
  exact (forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.2
    ⟨hR₁.of_faithfullyFlat, hS₂.of_faithfullyFlat⟩ p).2

/-! ### Checks -/

/-- The dual numbers `k[ε]` over a field are flat and Artinian, so they satisfy `(S_n)` for every
`n` even though they are not reduced. -/
example (k : Type u) [Field k] (n : ℕ) : Module.SatisfiesSerreS n (DualNumber k) (DualNumber k) :=
  have : Module.Flat k (DualNumber k) := Module.Flat.of_free
  (IsRegularRing.satisfiesSerreS (R := k) n).of_flat fun p _ ↦ by
    have : IsArtinianRing (p.Fiber (DualNumber k)) :=
      isArtinian_of_tower p.ResidueField inferInstance
    exact .of_krullDimLE_zero

/-- Flatness over a reduced base does not preserve `(R_0)` or reducedness without reduced fibres:
`k[ε]` is flat and finite over the field `k`, yet fails `(R_0)`. -/
example (k : Type u) [Field k] : ¬ Ring.SatisfiesSerreR 0 (DualNumber k) := fun hR₀ ↦
  DualNumber.not_isReduced (R := k) <|
    isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one.2 ⟨hR₀, .of_krullDimLE_zero⟩

end TauCeti
