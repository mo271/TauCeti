/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Herbrand function and the upper numbering on a local ring

Let a group `G` act by ring automorphisms on a local ring `S`, with lower ramification groups
`G_i = ramificationGroup G S i` and real-indexed filtration `G_u = ramificationGroupReal G S u =
G_⌈u⌉`. The **Herbrand function** is

`φ(u) = ∫_0^u (#G_t / #G_0) dt`.

Its **inverse Herbrand function** is `ψ(v) = sInf {u : ℝ | v ≤ φ(u)}`, and the **upper
ramification filtration** is `G^v = G_{ψ(v)}`.

Because the integrand `#G_t / #G_0` is locally constant on each `(i - 1, i]` and nonnegative,
`φ` is continuous, monotone, piecewise affine on every `[i - 1, i]`, and given by the finite-sum
formula `φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0` on `[m, m + 1]` for every group `G`,
without finiteness assumptions. Likewise `G^v` is antitone, satisfies `G^0 = G_0` and
`G^n = G_{ψℕ(n)}`, and obeys the subgroup trace identity `(G^u).subgroupOf H = H^{φ_H(ψ_G(u))}`
for every group `G` and subgroup `H ≤ G`.

When `G_0` is finite, `φ` is the identity on `[-1, 0]` and restricts to an order automorphism
`herbrandOrderIso` of `[-1, ∞)`, so at every natural number `n`, `ψ(n)` is the natural number
`psiNat G S n` characterized by `#G_1 + ⋯ + #G_m = n · #G_0`. When `G` itself is finite, the
integrand is antitone and bounded below by `1 / #G_0` on all of `ℝ`, so `φ` is a continuous,
strictly increasing, concave bijection of `ℝ` onto itself with `ψ` its two-sided inverse on all of
`ℝ`.

The finiteness assumption on `G` for global properties below `-1` cannot be relaxed to finiteness of
`G_0`: if `G = ℤ` acts on `S = ℚ(t)` by translation `n • f(t) = f(t + n)`, then `G_0 = ⊥` is finite
while `G_t = ⊤` for `t ≤ -1` has `Nat.card ⊤ = 0`, so `φ(u) = -1` for all `u ≤ -1` and
`ψ(-1) = sInf Set.univ = 0`.

This generalizes the local-field construction in
`TauCeti/NumberTheory/LocalField/Herbrand/Basic.lean` to an arbitrary group acting on a local ring:
neither a valuation, nor discreteness, nor a finite residue field is used.

## Main definitions

* `TauCeti.IsLocalRing.herbrandFun`: the Herbrand function `φ(u) = ∫_0^u (#G_t / #G_0) dt`.
* `TauCeti.IsLocalRing.inverseHerbrandFun`: the inverse Herbrand function `ψ(v)`.
* `TauCeti.IsLocalRing.upperRamificationGroup`: the upper ramification group `G^v = G_{ψ(v)}`.
* `TauCeti.IsLocalRing.herbrandOrderIso`: `φ` restricted to an order automorphism of `[-1, ∞)`.
* `TauCeti.IsLocalRing.psiNat`: the integral inverse Herbrand function `ψℕ : ℕ → ℕ`.
* `TauCeti.IsLocalRing.UpperJump`: strict drops of the upper ramification filtration.

## Main results

* `TauCeti.IsLocalRing.continuous_herbrandFun`, `TauCeti.IsLocalRing.herbrandFun_monotone`,
  `TauCeti.IsLocalRing.herbrandFun_of_mem_Icc`, and `TauCeti.IsLocalRing.herbrandFun_natCast`:
  continuity, monotonicity, and the finite-sum formula for any group `G`.
* `TauCeti.IsLocalRing.herbrandFun_strictMono`, `TauCeti.IsLocalRing.herbrandFun_bijective`, and
  `TauCeti.IsLocalRing.herbrandFun_slope_anti_adjacent`: for finite `G`, `φ` is a strictly
  increasing concave bijection of `ℝ`.
* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun` and
  `TauCeti.IsLocalRing.inverseHerbrandFun_herbrandFun`: `φ(ψ(v)) = v` and `ψ(φ(u)) = u`.
* `TauCeti.IsLocalRing.upperRamificationGroup_herbrandFun`: `G^{φ(u)} = G_u`.
* `TauCeti.IsLocalRing.upperRamificationGroup_antitone` and
  `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup`: antitonicity and the trace identity
  `(G^u).subgroupOf H = H^{φ_H(ψ_G(u))}` for any group `G` and subgroup `H ≤ G`.
* `TauCeti.IsLocalRing.coe_psiNat` and `TauCeti.IsLocalRing.psiNat_eq_iff`: integrality and
  arithmetic characterization of `ψ(n)`.
* `TauCeti.IsLocalRing.upperJump_herbrandFun_iff`: `φ` carries lower jumps to upper jumps.
* `TauCeti.IsLocalRing.herbrandFun_eq_of_ramificationGroup_eq_comap`,
  `TauCeti.IsLocalRing.herbrandFun_eq_of_ringEquiv`, and
  `TauCeti.IsLocalRing.map_upperRamificationGroup_of_ringEquiv`: invariance and transport along
  filtration-preserving morphisms and equivariant ring isomorphisms.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1.
-/

public section
noncomputable section

open MeasureTheory Set intervalIntegral

namespace TauCeti.IsLocalRing

section Defs

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The **Herbrand function** `φ(u) = ∫_0^u (#G_t / #G_0) dt` of a group `G` acting on a local
ring `S`, where `G_t = ramificationGroupReal G S t`. For finite `G`, this is a continuous strictly
increasing bijection of `ℝ`, equal to the identity on `[-1, 0]`, with
`φ(m) = (#G_1 + ⋯ + #G_m) / #G_0` at every natural number `m`. -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

/-- The integral formula defining `herbrandFun`. -/
theorem herbrandFun_def (u : ℝ) :
    herbrandFun G S u = ∫ t in (0 : ℝ)..u,
      (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) :=
  (rfl)

/-- The **inverse Herbrand function** `ψ(v)`, defined as the least `u : ℝ` with `v ≤ φ(u)`. For
finite `G`, `φ` is a continuous strictly increasing bijection of `ℝ`, so `ψ` is the two-sided
inverse of `φ` on all of `ℝ` and satisfies `ψ(-1) = -1`. -/
def inverseHerbrandFun (v : ℝ) : ℝ :=
  sInf {u : ℝ | v ≤ herbrandFun G S u}

/-- The defining formula of `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_def (v : ℝ) :
    inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u} :=
  (rfl)

/-- The **upper ramification group** `G^v = G_{ψ(v)}` of a group `G` acting on a local ring `S`.
For finite `G`, this reindexes the lower filtration so that `G^{φ(u)} = G_u`. -/
def upperRamificationGroup (v : ℝ) : Subgroup G :=
  ramificationGroupReal G S (inverseHerbrandFun G S v)

/-- The upper ramification group at `v` is the lower ramification group at `ψ(v)`. -/
theorem upperRamificationGroup_def (v : ℝ) :
    upperRamificationGroup G S v = ramificationGroupReal G S (inverseHerbrandFun G S v) :=
  (rfl)

variable {G S} in
/-- Membership in the upper ramification group: `σ ∈ G^v ↔ σ ∈ G_{ψ(v)}`. -/
@[simp]
theorem mem_upperRamificationGroup_iff {v : ℝ} {σ : G} :
    σ ∈ upperRamificationGroup G S v ↔ σ ∈ ramificationGroupReal G S (inverseHerbrandFun G S v) :=
  Iff.rfl

/-- Every upper ramification group is normal in `G`. -/
instance instNormalUpperRamificationGroup (v : ℝ) : (upperRamificationGroup G S v).Normal := by
  rw [upperRamificationGroup_def]
  infer_instance

/-- The **integral inverse Herbrand function** `ψℕ : ℕ → ℕ`: the floor `⌊ψ(n)⌋₊`, which equals
`ψ(n)` (`coe_psiNat`) and is characterized by `#G_1 + ⋯ + #G_m = n · #G_0` whenever `G_0` is
finite. -/
def psiNat (n : ℕ) : ℕ :=
  ⌊inverseHerbrandFun G S n⌋₊

/-- An **upper jump** (or upper break) of `(G, S)`: a real index `v` at which `G^v` strictly
contains `G^w` for every `w > v`. -/
def UpperJump (v : ℝ) : Prop :=
  ∀ w : ℝ, v < w → upperRamificationGroup G S w < upperRamificationGroup G S v

/-- Characterization of upper jumps. -/
theorem upperJump_iff (v : ℝ) :
    UpperJump G S v ↔
      ∀ w : ℝ, v < w → upperRamificationGroup G S w < upperRamificationGroup G S v :=
  Iff.rfl

/-- The integrand `#G_t / #G_0` of the Herbrand function. -/
private def herbrandDensity (t : ℝ) : ℝ :=
  (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

private theorem intervalIntegrable_herbrandDensity_intCast_add (k : ℤ) (n : ℕ) :
    IntervalIntegrable (herbrandDensity G S) volume (k : ℝ) ((k + n : ℤ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : IntervalIntegrable (herbrandDensity G S) volume ((k + n : ℤ) : ℝ)
        ((k + (n + 1 : ℕ) : ℤ) : ℝ) := by
      refine (intervalIntegrable_const (c :=
        (Nat.card (ramificationGroup G S (k + n + 1)) : ℝ) /
          Nat.card (ramificationGroup G S 0))).congr fun t ht ↦ ?_
      rw [uIoc_of_le (by push_cast; linarith)] at ht
      have hG := ramificationGroupReal_eq_of_sub_one_lt_of_le G S (i := k + n + 1) (u := t)
        (by push_cast at ht ⊢; linarith [ht.1]) (by push_cast at ht ⊢; linarith [ht.2])
      simp only [herbrandDensity, hG]
    exact ih.trans hstep

private theorem intervalIntegrable_herbrandDensity (a b : ℝ) :
    IntervalIntegrable (herbrandDensity G S) volume a b := by
  set k : ℤ := min ⌊a⌋ ⌊b⌋
  set m : ℤ := max ⌈a⌉ ⌈b⌉
  have hkm : k ≤ m :=
    (min_le_left _ _).trans ((Int.floor_le_ceil a).trans (le_max_left _ _))
  have hint : IntervalIntegrable (herbrandDensity G S) volume (k : ℝ) (m : ℝ) := by
    have h := intervalIntegrable_herbrandDensity_intCast_add G S k (m - k).toNat
    rwa [Int.toNat_of_nonneg (sub_nonneg.2 hkm), add_sub_cancel] at h
  have hsub : uIcc a b ⊆ uIcc (k : ℝ) m := by
    rw [uIcc_of_le (a := (k : ℝ)) (b := m) (by exact_mod_cast hkm)]
    exact uIcc_subset_Icc
      ⟨(Int.cast_le.2 (min_le_left _ _)).trans (Int.floor_le a),
        (Int.le_ceil a).trans (Int.cast_le.2 (le_max_left _ _))⟩
      ⟨(Int.cast_le.2 (min_le_right _ _)).trans (Int.floor_le b),
        (Int.le_ceil b).trans (Int.cast_le.2 (le_max_right _ _))⟩
  exact hint.mono_set hsub

/-- `φ(0) = 0`. -/
@[simp]
theorem herbrandFun_zero : herbrandFun G S 0 = 0 :=
  integral_same

/-- Difference of two values of the Herbrand function as an interval integral. -/
theorem herbrandFun_sub (a b : ℝ) :
    herbrandFun G S b - herbrandFun G S a =
      ∫ t in a..b,
        (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity G S 0 b)
    (intervalIntegrable_herbrandDensity G S 0 a)

/-- On an interval `[a, b]` over which the lower filtration is constantly `H`, meaning `G_t = H`
for all `a < t ≤ b`, the Herbrand function is affine of slope `#H / #G_0`. -/
theorem herbrandFun_sub_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G S t = H) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card H / Nat.card (ramificationGroup G S 0)) := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht
  rw [h t ht.1 ht.2]

/-- On an interval `[a, b] ⊆ [i - 1, i]`, the Herbrand function is affine of slope `#G_i / #G_0`. -/
theorem herbrandFun_sub_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ i) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card (ramificationGroup G S i) / Nat.card (ramificationGroup G S 0)) :=
  herbrandFun_sub_of_forall_eq G S hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le G S (ha.trans_lt ht₁) (ht₂.trans hb)

/-- The Herbrand function is nondecreasing on `ℝ`. -/
theorem herbrandFun_monotone : Monotone (herbrandFun G S) := fun a b hab ↦
  sub_nonneg.1 <| herbrandFun_sub G S a b ▸ integral_nonneg hab fun _ _ ↦ by positivity

/-- The Herbrand function is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_herbrandFun : Continuous (herbrandFun G S) :=
  continuous_primitive (intervalIntegrable_herbrandDensity G S) 0

/-- The **finite-sum formula** for the Herbrand function: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem herbrandFun_of_mem_Icc (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1) :
    herbrandFun G S u =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ) +
        (u - m) * Nat.card (ramificationGroup G S (m + 1 : ℕ))) /
        Nat.card (ramificationGroup G S 0) := by
  have hstep := herbrandFun_sub_of_le G S (i := (m + 1 : ℕ)) (by push_cast; linarith) h₁
    (by push_cast; linarith)
  induction m generalizing u with
  | zero =>
    rw [Nat.cast_zero, herbrandFun_zero] at hstep
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    linear_combination hstep
  | succ k ih =>
    have hk := ih (u := (k + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)
      (herbrandFun_sub_of_le G S (i := (k + 1 : ℕ)) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith))
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hk] at hstep
    push_cast at hstep ⊢
    linear_combination hstep

/-- The Herbrand function at a natural number `m`: `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem herbrandFun_natCast (m : ℕ) :
    herbrandFun G S m =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ)) /
        Nat.card (ramificationGroup G S 0) := by
  rw [herbrandFun_of_mem_Icc G S m le_rfl (by linarith), sub_self, zero_mul, add_zero]

private theorem herbrandFun_eq_zero_of_infinite_zero [Infinite (ramificationGroup G S 0)]
    (u : ℝ) : herbrandFun G S u = 0 := by
  rw [herbrandFun_def, Nat.card_eq_zero_of_infinite (α := ramificationGroup G S 0)]
  simp

private theorem inverseHerbrandFun_eq_zero_of_infinite_zero [Infinite (ramificationGroup G S 0)]
    (v : ℝ) : inverseHerbrandFun G S v = 0 := by
  simp_rw [inverseHerbrandFun_def, herbrandFun_eq_zero_of_infinite_zero G S]
  by_cases hv : v ≤ 0
  · rw [Set.eq_univ_of_forall (s := { _u : ℝ | v ≤ 0 }) fun _ ↦ hv]
    exact Real.sInf_of_not_bddBelow not_bddBelow_univ
  · rw [Set.eq_empty_of_forall_notMem (s := { _u : ℝ | v ≤ 0 }) fun _ ↦ hv]
    exact Real.sInf_empty

end Defs

section FiniteZero

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  [Finite (ramificationGroup G S 0)]

/-- The Herbrand function is the identity on `[-1, 0]`. -/
theorem herbrandFun_of_le_zero {u : ℝ} (h₁ : -1 ≤ u) (h₀ : u ≤ 0) :
    herbrandFun G S u = u := by
  have h := herbrandFun_sub_of_le G S (i := 0) (by simpa using h₁) h₀ (by simp)
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [div_self h0, herbrandFun_zero] at h
  linarith

/-- `φ(-1) = -1`. -/
@[simp]
theorem herbrandFun_neg_one : herbrandFun G S (-1) = -1 :=
  herbrandFun_of_le_zero G S le_rfl (by norm_num)

/-- For `u ≤ -1`, `φ(u) = -1 + (u + 1) · (#G / #G_0)`. -/
theorem herbrandFun_of_le_neg_one {u : ℝ} (hu : u ≤ -1) :
    herbrandFun G S u =
      -1 + (u + 1) * (Nat.card G / Nat.card (ramificationGroup G S 0)) := by
  have h := herbrandFun_sub_of_forall_eq G S hu (H := ⊤) fun t _ ht ↦ by
    rw [ramificationGroupReal_def]
    exact ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by exact_mod_cast ht))
  rw [herbrandFun_neg_one, Subgroup.card_top] at h
  linarith

/-- The Herbrand function is the identity as long as the lower filtration is constant from `0`
through `u`. For `-1 ≤ u ≤ 0` the hypothesis is vacuous and the conclusion is
`herbrandFun_of_le_zero`. -/
theorem herbrandFun_eq_self_of_forall_eq {u : ℝ} (hu₁ : -1 ≤ u)
    (h : ∀ t : ℝ, 0 < t → t ≤ u → ramificationGroupReal G S t = ramificationGroup G S 0) :
    herbrandFun G S u = u := by
  rcases le_or_gt u 0 with hu | hu
  · exact herbrandFun_of_le_zero G S hu₁ hu
  have hsub := herbrandFun_sub_of_forall_eq G S hu.le h
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [herbrandFun_zero, sub_zero, sub_zero, div_self h0, mul_one] at hsub
  exact hsub

private theorem div_sub_le_herbrandFun_sub_of_neg_one_le {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) :
    (b - a) / Nat.card (ramificationGroup G S 0) ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, div_eq_mul_inv, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_mono_on_of_le_Ioo hab intervalIntegrable_const
    (intervalIntegrable_herbrandDensity G S a b) fun t ht ↦ ?_
  have hle : ramificationGroupReal G S t ≤ ramificationGroup G S 0 := by
    rw [ramificationGroupReal_def]
    exact ramificationGroup_antitone G S (Int.le_ceil_iff.2 (by push_cast; linarith [ht.1]))
  have : Finite (ramificationGroupReal G S t) := Finite.Set.subset _ hle
  rw [div_eq_mul_inv]
  refine le_mul_of_one_le_left (by positivity) ?_
  exact_mod_cast (Nat.card_pos (α := ramificationGroupReal G S t))

private theorem herbrandFun_strictMonoOn_Ici : StrictMonoOn (herbrandFun G S) (Set.Ici (-1)) :=
  fun a ha b _ hab ↦ by
    have h := div_sub_le_herbrandFun_sub_of_neg_one_le G S ha hab.le
    have : 0 < (b - a) / Nat.card (ramificationGroup G S 0) :=
      div_pos (sub_pos.2 hab) (Nat.cast_pos.2 Nat.card_pos)
    linarith

private theorem exists_herbrandFun_eq_of_neg_one_lt {v : ℝ} (hv : -1 < v) :
    ∃ u : ℝ, -1 < u ∧ herbrandFun G S u = v := by
  set g : ℝ := (Nat.card (ramificationGroup G S 0) : ℝ)
  have hg : 0 < g := Nat.cast_pos.2 Nat.card_pos
  set b := max 0 (v * g)
  have hφb : v ≤ herbrandFun G S b := by
    have h := div_sub_le_herbrandFun_sub_of_neg_one_le G S (a := 0) (by norm_num)
      (le_max_left 0 (v * g))
    rw [herbrandFun_zero, sub_zero, sub_zero] at h
    linarith [(le_div_iff₀ hg).2 (le_max_right 0 (v * g))]
  obtain ⟨u, hu, hφu⟩ := intermediate_value_Icc (by linarith [le_max_left 0 (v * g)] : (-1 : ℝ) ≤ b)
    (continuous_herbrandFun G S).continuousOn ⟨by rw [herbrandFun_neg_one]; exact hv.le, hφb⟩
  exact ⟨u, lt_of_le_of_ne hu.1 fun heq ↦ by
    subst heq; rw [herbrandFun_neg_one] at hφu; linarith, hφu⟩

/-- The Herbrand function restricted to an order automorphism of `[-1, ∞)`. -/
def herbrandOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) :=
  StrictMono.orderIsoOfSurjective
    (fun u ↦ ⟨herbrandFun G S u,
      Set.mem_Ici.2 ((herbrandFun_neg_one G S).ge.trans (herbrandFun_monotone G S u.2))⟩)
    (fun a b h ↦ herbrandFun_strictMonoOn_Ici G S a.2 b.2 h)
    fun v ↦ by
      rcases eq_or_lt_of_le (Set.mem_Ici.1 v.2) with h | h
      · exact ⟨⟨-1, le_rfl⟩, Subtype.ext ((herbrandFun_neg_one G S).trans h)⟩
      · obtain ⟨u, hu, hφ⟩ := exists_herbrandFun_eq_of_neg_one_lt G S h
        exact ⟨⟨u, hu.le⟩, Subtype.ext hφ⟩

/-- The forward map of `herbrandOrderIso` is `herbrandFun`. -/
@[simp]
theorem coe_herbrandOrderIso (u : Set.Ici (-1 : ℝ)) :
    (herbrandOrderIso G S u : ℝ) = herbrandFun G S u :=
  (rfl)

private theorem inverseHerbrandFun_herbrandFun_of_neg_one_lt {u : ℝ} (hu : -1 < u) :
    inverseHerbrandFun G S (herbrandFun G S u) = u := by
  have hset : {x : ℝ | herbrandFun G S u ≤ herbrandFun G S x} = Set.Ici u := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    refine ⟨fun h ↦ by_contra fun hlt ↦ ?_, fun h ↦ herbrandFun_monotone G S h⟩
    push Not at hlt
    rcases le_or_gt (-1) x with hx1 | hx1
    · exact (herbrandFun_strictMonoOn_Ici G S hx1 hu.le hlt).not_ge h
    · exact ((herbrandFun_monotone G S hx1.le).trans_lt
        (herbrandFun_strictMonoOn_Ici G S le_rfl hu.le hu)).not_ge h
  rw [inverseHerbrandFun_def, hset, csInf_Ici]

private theorem herbrandFun_inverseHerbrandFun_of_neg_one_lt {v : ℝ} (hv : -1 < v) :
    herbrandFun G S (inverseHerbrandFun G S v) = v := by
  obtain ⟨u₀, hu₀, rfl⟩ := exists_herbrandFun_eq_of_neg_one_lt G S hv
  rw [inverseHerbrandFun_herbrandFun_of_neg_one_lt G S hu₀]

private theorem neg_one_lt_inverseHerbrandFun_of_neg_one_lt {v : ℝ} (hv : -1 < v) :
    -1 < inverseHerbrandFun G S v := by
  obtain ⟨u₀, hu₀, rfl⟩ := exists_herbrandFun_eq_of_neg_one_lt G S hv
  rwa [inverseHerbrandFun_herbrandFun_of_neg_one_lt G S hu₀]

private theorem inverseHerbrandFun_strictMonoOn_Ioi :
    StrictMonoOn (inverseHerbrandFun G S) (Set.Ioi (-1)) := fun v₁ hv₁ v₂ hv₂ hlt ↦ by
  by_contra hge
  push Not at hge
  have hle := herbrandFun_monotone G S hge
  rw [herbrandFun_inverseHerbrandFun_of_neg_one_lt G S hv₁,
    herbrandFun_inverseHerbrandFun_of_neg_one_lt G S hv₂] at hle
  exact hlt.not_ge hle

private theorem inverseHerbrandFun_le_iff_of_neg_one_lt {u v : ℝ} (hu : -1 ≤ u) (hv : -1 < v) :
    inverseHerbrandFun G S v ≤ u ↔ v ≤ herbrandFun G S u := by
  rw [← (herbrandFun_strictMonoOn_Ici G S).le_iff_le
      (neg_one_lt_inverseHerbrandFun_of_neg_one_lt G S hv).le hu,
    herbrandFun_inverseHerbrandFun_of_neg_one_lt G S hv]

private theorem le_inverseHerbrandFun_iff_of_neg_one_lt {u v : ℝ} (hu : -1 ≤ u) (hv : -1 < v) :
    u ≤ inverseHerbrandFun G S v ↔ herbrandFun G S u ≤ v := by
  rw [← (herbrandFun_strictMonoOn_Ici G S).le_iff_le hu
      (neg_one_lt_inverseHerbrandFun_of_neg_one_lt G S hv).le,
    herbrandFun_inverseHerbrandFun_of_neg_one_lt G S hv]

private theorem inverseHerbrandFun_eq_zero_of_infinite_of_le_neg_one [Infinite G] {v : ℝ}
    (hv : v ≤ -1) : inverseHerbrandFun G S v = 0 := by
  have hset : {u : ℝ | v ≤ herbrandFun G S u} = Set.univ :=
    Set.eq_univ_of_forall fun u ↦ hv.trans <| by
      rcases le_or_gt u (-1) with hu | hu
      · rw [herbrandFun_of_le_neg_one G S hu, Nat.card_eq_zero_of_infinite]; norm_num
      · rw [← herbrandFun_neg_one G S]; exact herbrandFun_monotone G S hu.le
  rw [inverseHerbrandFun_def, hset]
  exact Real.sInf_of_not_bddBelow not_bddBelow_univ

private theorem inverseHerbrandFun_natCast_eq_floor (n : ℕ) :
    inverseHerbrandFun G S n = ⌊inverseHerbrandFun G S n⌋₊ := by
  have hn1 : (-1 : ℝ) < n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  set u := inverseHerbrandFun G S n
  set m := ⌊u⌋₊
  have hu : 0 ≤ u := (le_inverseHerbrandFun_iff_of_neg_one_lt G S (by norm_num) hn1).2 (by simp)
  have hm₁ : (m : ℝ) ≤ u := Nat.floor_le hu
  have hm₂ : u < m + 1 := Nat.lt_floor_add_one u
  have hφ := herbrandFun_of_mem_Icc G S m hm₁ hm₂.le
  rw [herbrandFun_inverseHerbrandFun_of_neg_one_lt G S hn1,
    eq_div_iff (Nat.cast_ne_zero.2 Nat.card_pos.ne')] at hφ
  set g : ℤ → ℕ := fun i ↦ Nat.card (ramificationGroup G S i)
  have hfin : ∀ i : ℕ, Finite (ramificationGroup G S i) := fun i ↦
    Finite.Set.subset _ (ramificationGroup_antitone G S (Int.natCast_nonneg i))
  have hdvd : ∀ i : ℕ, i ≤ m + 1 → g (m + 1 : ℕ) ∣ g i := fun i hi ↦
    Subgroup.card_dvd_of_le (ramificationGroup_antitone G S (by exact_mod_cast hi))
  have h₁ : g (m + 1 : ℕ) ∣ n * g 0 := dvd_mul_of_dvd_right (hdvd 0 (Nat.zero_le _)) _
  have h₂ : g (m + 1 : ℕ) ∣ ∑ i ∈ Finset.Icc 1 m, g i := Finset.dvd_sum fun i hi ↦
    hdvd i (by have := (Finset.mem_Icc.1 hi).2; omega)
  obtain ⟨c, hc⟩ := (Int.natCast_dvd_natCast.2 h₁).sub (Int.natCast_dvd_natCast.2 h₂)
  have hcR : (n : ℝ) * g 0 - ∑ i ∈ Finset.Icc 1 m, (g i : ℝ) = g (m + 1 : ℕ) * c := by
    exact_mod_cast hc
  have hgm1 : (g (m + 1 : ℕ) : ℝ) ≠ 0 := by
    have := hfin (m + 1); exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hcu : u - m = c := mul_right_cancel₀ hgm1 <|
    (by rw [← hcR]; linarith : (u - m) * g (m + 1 : ℕ) = g (m + 1 : ℕ) * c).trans (mul_comm _ _)
  have hc0 : 0 ≤ c := by exact_mod_cast (hcu ▸ sub_nonneg.2 hm₁ : (0 : ℝ) ≤ c)
  have hc1 : c < 1 := by exact_mod_cast (hcu ▸ by linarith : (c : ℝ) < 1)
  have hc_zero : c = 0 := by omega
  rw [hc_zero, Int.cast_zero, sub_eq_zero] at hcu
  exact hcu

/-- `ψℕ(n) = m` exactly when `#G_1 + ⋯ + #G_m = n · #G_0`, that is when `φ(m) = n`. -/
theorem psiNat_eq_iff {n m : ℕ} :
    psiNat G S n = m ↔
      ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
        n * Nat.card (ramificationGroup G S 0) := by
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn1 : (-1 : ℝ) < n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm1 : (-1 : ℝ) < m := by linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [← Nat.cast_inj (R := ℝ), psiNat, ← inverseHerbrandFun_natCast_eq_floor G S n]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hφ : herbrandFun G S m = n := by
      rw [← h, herbrandFun_inverseHerbrandFun_of_neg_one_lt G S hn1]
    rw [herbrandFun_natCast, div_eq_iff h0] at hφ
    exact_mod_cast hφ
  · have hφ : herbrandFun G S m = n := by rw [herbrandFun_natCast, div_eq_iff h0]; exact_mod_cast h
    rw [← hφ, inverseHerbrandFun_herbrandFun_of_neg_one_lt G S hm1]

/-- The integral inverse Herbrand function is strictly increasing. -/
theorem psiNat_strictMono : StrictMono (psiNat G S) := fun a b h ↦ by
  have hlt := inverseHerbrandFun_strictMonoOn_Ioi G S
    (Set.mem_Ioi.2 (by linarith [Nat.cast_nonneg (α := ℝ) a]))
    (Set.mem_Ioi.2 (by linarith [Nat.cast_nonneg (α := ℝ) b])) (Nat.cast_lt.2 h)
  rw [inverseHerbrandFun_natCast_eq_floor G S a, inverseHerbrandFun_natCast_eq_floor G S b] at hlt
  exact Nat.cast_lt.1 hlt

/-- `n ≤ ψℕ(n)`. -/
theorem self_le_psiNat (n : ℕ) : n ≤ psiNat G S n :=
  (psiNat_strictMono G S).id_le n

/-- `ψℕ(n) ≤ i ↔ n ≤ ⌊φ(i)⌋₊`. -/
@[simp]
theorem psiNat_le_iff_le_floor_herbrandFun {n i : ℕ} :
    psiNat G S n ≤ i ↔ n ≤ ⌊herbrandFun G S i⌋₊ := by
  have h0 : (0 : ℝ) ≤ herbrandFun G S i := by
    rw [← herbrandFun_zero G S]
    exact herbrandFun_monotone G S (Nat.cast_nonneg i)
  rw [Nat.le_floor_iff h0, ← Nat.cast_le (α := ℝ), psiNat,
    ← inverseHerbrandFun_natCast_eq_floor G S n,
    inverseHerbrandFun_le_iff_of_neg_one_lt G S
      (by linarith [Nat.cast_nonneg (α := ℝ) i]) (by linarith [Nat.cast_nonneg (α := ℝ) n])]

/-- `ψℕ(v) = v` exactly when `G_v = G_0`. -/
@[simp]
theorem psiNat_eq_self_iff {v : ℕ} :
    psiNat G S v = v ↔ ramificationGroup G S v = ramificationGroup G S 0 := by
  have hle : ∀ i : ℕ, ramificationGroup G S i ≤ ramificationGroup G S 0 := fun i ↦
    ramificationGroup_antitone G S (Int.natCast_nonneg i)
  rw [psiNat_eq_iff]
  constructor
  · intro h
    rcases v with _ | k
    · simp
    have hk := Finset.sum_le_card_nsmul (Finset.Icc 1 k)
      (fun i : ℕ ↦ Nat.card (ramificationGroup G S i)) _
      fun i _ ↦ Subgroup.card_le_of_le (hle i)
    rw [Finset.sum_Icc_succ_top (by omega)] at h
    simp only [Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul] at hk
    exact Subgroup.eq_of_le_of_card_ge (hle _) (by rw [add_mul, one_mul] at h; omega)
  · intro hv
    calc ∑ i ∈ Finset.Icc 1 v, Nat.card (ramificationGroup G S i)
        = ∑ _i ∈ Finset.Icc 1 v, Nat.card (ramificationGroup G S 0) := by
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          have hi' : (i : ℤ) ≤ v := by have := (Finset.mem_Icc.1 hi).2; omega
          rw [le_antisymm (hle i) (hv.symm.le.trans (ramificationGroup_antitone G S hi'))]
      _ = v * Nat.card (ramificationGroup G S 0) := by simp

/-- If `G_t = G_0` and `G_{t+1} = ⊥`, then `ψℕ(v) = t + #G_0 · (v - t)` for every `v ≥ t`. -/
theorem psiNat_eq_add_card_mul_sub {t v : ℕ}
    (ht : ramificationGroup G S t = ramificationGroup G S 0)
    (ht' : ramificationGroup G S (t + 1 : ℕ) = ⊥) (hv : t ≤ v) :
    psiNat G S v = t + Nat.card (ramificationGroup G S 0) * (v - t) := by
  set g₀ := Nat.card (ramificationGroup G S 0)
  have hsum : ∀ m, t ≤ m →
      ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) = t * g₀ + (m - t) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rw [(psiNat_eq_iff G S).1 ((psiNat_eq_self_iff G S).2 ht), Nat.sub_self, add_zero]
    | succ m hm ih =>
      have hbot : ramificationGroup G S (m + 1 : ℕ) = ⊥ := le_bot_iff.1 <|
        (ramificationGroup_antitone G S (by push_cast; omega)).trans ht'.le
      rw [Finset.sum_Icc_succ_top (by omega), ih, hbot, Subgroup.card_bot]
      omega
  refine (psiNat_eq_iff G S).2 ((hsum _ (by omega)).trans ?_)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
  simp only [Nat.add_sub_cancel_left]
  ring

/-- Over a Noetherian local ring, the upper ramification filtration of a faithful action with
finite zeroth ramification group vanishes from some index on. -/
theorem exists_forall_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ∃ N : ℝ, ∀ v : ℝ, N ≤ v → upperRamificationGroup G S v = ⊥ := by
  obtain ⟨N₀, hN₀⟩ := exists_forall_ramificationGroup_eq_bot G S
  set M : ℤ := max N₀ 0
  have hM0 : (0 : ℝ) ≤ M := by exact_mod_cast le_max_right N₀ 0
  have hφM : (0 : ℝ) ≤ herbrandFun G S M := herbrandFun_zero G S ▸ herbrandFun_monotone G S hM0
  refine ⟨herbrandFun G S M, fun v hv ↦ ?_⟩
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  exact hN₀ _ ((le_max_left N₀ 0).trans (Int.le_ceil_iff.2 (by
    linarith [(le_inverseHerbrandFun_iff_of_neg_one_lt G S (by linarith) (by linarith)).2 hv])))

end FiniteZero

section Finite

variable (G : Type*) [Group G] [Finite G] (S : Type*) [CommRing S] [IsLocalRing S]
  [MulSemiringAction G S]

private theorem herbrandDensity_antitone : Antitone (herbrandDensity G S) := fun _ _ hst ↦ by
  unfold herbrandDensity
  gcongr
  exact Subgroup.card_le_of_le (ramificationGroupReal_antitone G S hst)

private theorem inv_le_herbrandDensity (t : ℝ) :
    (Nat.card (ramificationGroup G S 0) : ℝ)⁻¹ ≤ herbrandDensity G S t := by
  rw [herbrandDensity, div_eq_mul_inv]
  refine le_mul_of_one_le_left (by positivity) ?_
  exact_mod_cast (Nat.card_pos (α := ramificationGroupReal G S t))

private theorem div_sub_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) / Nat.card (ramificationGroup G S 0) ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, div_eq_mul_inv, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun t _ ↦ inv_le_herbrandDensity G S t

private theorem herbrandFun_sub_le_mul {a b : ℝ} (hab : a ≤ b) :
    herbrandFun G S b - herbrandFun G S a ≤ (b - a) * herbrandDensity G S a := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab (intervalIntegrable_herbrandDensity G S a b) intervalIntegrable_const
    fun t ht ↦ herbrandDensity_antitone G S ht.1

private theorem mul_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) * herbrandDensity G S b ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun t ht ↦ herbrandDensity_antitone G S ht.2

/-- The Herbrand function is strictly increasing on `ℝ`. -/
theorem herbrandFun_strictMono : StrictMono (herbrandFun G S) := fun a b hab ↦ by
  have h := div_sub_le_herbrandFun_sub G S hab.le
  have : 0 < (b - a) / Nat.card (ramificationGroup G S 0) :=
    div_pos (sub_pos.2 hab) (Nat.cast_pos.2 Nat.card_pos)
  linarith

/-- The Herbrand function is surjective onto `ℝ`. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) := fun y ↦ by
  set g : ℝ := (Nat.card (ramificationGroup G S 0) : ℝ)
  have hg : 0 < g := Nat.cast_pos.2 Nat.card_pos
  set a := min 0 (y * g)
  set b := max 0 (y * g)
  have hφa : herbrandFun G S a ≤ y := by
    have h := div_sub_le_herbrandFun_sub G S (min_le_left 0 (y * g))
    rw [herbrandFun_zero, zero_sub, zero_sub] at h
    linarith [(le_div_iff₀ hg).2 (by linarith [min_le_right 0 (y * g)] : -y * g ≤ -a)]
  have hφb : y ≤ herbrandFun G S b := by
    have h := div_sub_le_herbrandFun_sub G S (le_max_left 0 (y * g))
    rw [herbrandFun_zero, sub_zero, sub_zero] at h
    linarith [(le_div_iff₀ hg).2 (le_max_right 0 (y * g))]
  obtain ⟨u, _, hu⟩ := intermediate_value_Icc ((min_le_left _ _).trans (le_max_left _ _))
    (continuous_herbrandFun G S).continuousOn ⟨hφa, hφb⟩
  exact ⟨u, hu⟩

/-- The Herbrand function is a bijection of `ℝ` onto itself. -/
theorem herbrandFun_bijective : Function.Bijective (herbrandFun G S) :=
  ⟨(herbrandFun_strictMono G S).injective, herbrandFun_surjective G S⟩

/-- `-1 ≤ φ(u) ↔ -1 ≤ u`. -/
@[simp]
theorem neg_one_le_herbrandFun_iff {u : ℝ} : -1 ≤ herbrandFun G S u ↔ -1 ≤ u := by
  conv_lhs => rw [← herbrandFun_neg_one G S]
  exact (herbrandFun_strictMono G S).le_iff_le

/-- The Herbrand function is **concave**: its slopes over two adjacent intervals decrease. -/
theorem herbrandFun_slope_anti_adjacent {u v w : ℝ} (huv : u < v) (hvw : v < w) :
    (herbrandFun G S w - herbrandFun G S v) / (w - v) ≤
      (herbrandFun G S v - herbrandFun G S u) / (v - u) :=
  calc (herbrandFun G S w - herbrandFun G S v) / (w - v)
      ≤ herbrandDensity G S v :=
        (div_le_iff₀' (sub_pos.2 hvw)).2 (herbrandFun_sub_le_mul G S hvw.le)
    _ ≤ (herbrandFun G S v - herbrandFun G S u) / (v - u) :=
        (le_div_iff₀' (sub_pos.2 huv)).2 (mul_le_herbrandFun_sub G S huv.le)

/-! ### The inverse Herbrand function and order isomorphism -/

/-- `φ(ψ(v)) = v` for every real `v`. -/
@[simp]
theorem herbrandFun_inverseHerbrandFun (v : ℝ) :
    herbrandFun G S (inverseHerbrandFun G S v) = v := by
  obtain ⟨u₀, rfl⟩ := herbrandFun_surjective G S v
  have hset : {u : ℝ | herbrandFun G S u₀ ≤ herbrandFun G S u} = Set.Ici u₀ := by
    ext u
    exact (herbrandFun_strictMono G S).le_iff_le
  rw [inverseHerbrandFun_def, hset, csInf_Ici]

/-- `ψ(φ(u)) = u` for every real `u`. -/
@[simp]
theorem inverseHerbrandFun_herbrandFun (u : ℝ) :
    inverseHerbrandFun G S (herbrandFun G S u) = u :=
  (herbrandFun_strictMono G S).injective (herbrandFun_inverseHerbrandFun G S _)

/-- The Herbrand function as an order automorphism of `ℝ`. -/
private def herbrandRealOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (herbrandFun G S) (herbrandFun_strictMono G S)
    (herbrandFun_surjective G S)

private theorem herbrandRealOrderIso_symm_apply (v : ℝ) :
    (herbrandRealOrderIso G S).symm v = inverseHerbrandFun G S v :=
  (herbrandFun_strictMono G S).injective <| by
    rw [herbrandFun_inverseHerbrandFun]
    exact (herbrandRealOrderIso G S).apply_symm_apply v

/-- The inverse Herbrand function is strictly increasing on `ℝ`. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) := by
  simpa only [funext (herbrandRealOrderIso_symm_apply G S)] using
    (herbrandRealOrderIso G S).symm.strictMono

/-- The inverse Herbrand function is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) := by
  simpa only [funext (herbrandRealOrderIso_symm_apply G S)] using
    (herbrandRealOrderIso G S).symm.continuous

/-- `ψ(v) ≤ u ↔ v ≤ φ(u)`. -/
theorem inverseHerbrandFun_le_iff {u v : ℝ} :
    inverseHerbrandFun G S v ≤ u ↔ v ≤ herbrandFun G S u := by
  rw [← (herbrandFun_strictMono G S).le_iff_le, herbrandFun_inverseHerbrandFun]

/-- `u ≤ ψ(v) ↔ φ(u) ≤ v`. -/
theorem le_inverseHerbrandFun_iff {u v : ℝ} :
    u ≤ inverseHerbrandFun G S v ↔ herbrandFun G S u ≤ v := by
  rw [← (herbrandFun_strictMono G S).le_iff_le, herbrandFun_inverseHerbrandFun]

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
theorem inverseHerbrandFun_of_le_zero {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_of_le_zero G S h₁ h₀]
  exact inverseHerbrandFun_herbrandFun G S v

/-- `ψ(-1) = -1`. -/
@[simp]
theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 :=
  inverseHerbrandFun_of_le_zero G S le_rfl (by norm_num)

/-- `-1 ≤ ψ(v) ↔ -1 ≤ v`. -/
@[simp]
theorem neg_one_le_inverseHerbrandFun_iff {v : ℝ} : -1 ≤ inverseHerbrandFun G S v ↔ -1 ≤ v := by
  rw [le_inverseHerbrandFun_iff, herbrandFun_neg_one]

/-- The inverse map of `herbrandOrderIso` is `inverseHerbrandFun`. -/
@[simp]
theorem coe_herbrandOrderIso_symm (v : Set.Ici (-1 : ℝ)) :
    ((herbrandOrderIso G S).symm v : ℝ) = inverseHerbrandFun G S v :=
  (herbrandFun_strictMono G S).injective <| by
    rw [herbrandFun_inverseHerbrandFun, ← coe_herbrandOrderIso, OrderIso.apply_symm_apply]

/-! ### Properties of the upper ramification filtration for finite `G` -/

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]

/-- For `v ≤ -1`, `G^v = ⊤`. -/
theorem upperRamificationGroup_eq_top_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    upperRamificationGroup G S v = ⊤ := by
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  apply ramificationGroup_eq_top_of_le_neg_one
  have hle : inverseHerbrandFun G S v ≤ -1 := by
    rw [inverseHerbrandFun_le_iff, herbrandFun_neg_one]
    exact hv
  exact Int.ceil_le.2 (by exact_mod_cast hle)

/-- For `v ≤ 0`, the upper and lower numberings agree. -/
theorem upperRamificationGroup_of_le_zero {v : ℝ} (hv : v ≤ 0) :
    upperRamificationGroup G S v = ramificationGroupReal G S v := by
  rcases le_or_gt v (-1) with h | h
  · rw [upperRamificationGroup_eq_top_of_le_neg_one G S h, ramificationGroupReal_def]
    exact (ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by exact_mod_cast h))).symm
  · rw [upperRamificationGroup_def, inverseHerbrandFun_of_le_zero G S h.le hv]

/-! ### Jumps for finite `G` -/

/-- `φ` carries lower jumps precisely to upper jumps. -/
@[simp]
theorem upperJump_herbrandFun_iff (u : ℝ) :
    UpperJump G S (herbrandFun G S u) ↔ LowerJump G S u := by
  rw [upperJump_iff, lowerJump_iff]
  constructor
  · intro h v huv
    simpa only [upperRamificationGroup_herbrandFun] using
      h (herbrandFun G S v) (herbrandFun_strictMono G S huv)
  · intro h w hvw
    have hlt : u < inverseHerbrandFun G S w := by
      simpa only [inverseHerbrandFun_herbrandFun] using inverseHerbrandFun_strictMono G S hvw
    simpa only [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun] using
      h (inverseHerbrandFun G S w) hlt

/-- `ψ` carries upper jumps precisely to lower jumps. -/
@[simp]
theorem lowerJump_inverseHerbrandFun_iff (v : ℝ) :
    LowerJump G S (inverseHerbrandFun G S v) ↔ UpperJump G S v := by
  simpa only [herbrandFun_inverseHerbrandFun] using
    (upperJump_herbrandFun_iff G S (inverseHerbrandFun G S v)).symm

end Finite

section GeneralInverse

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- `ψ(0) = 0`. -/
@[simp]
theorem inverseHerbrandFun_zero : inverseHerbrandFun G S 0 = 0 := by
  rcases finite_or_infinite (ramificationGroup G S 0) with _ | _
  · simpa only [herbrandFun_zero] using
      inverseHerbrandFun_herbrandFun_of_neg_one_lt G S (u := 0) (by norm_num)
  · exact inverseHerbrandFun_eq_zero_of_infinite_zero G S 0

/-- `G^0 = G_0`. -/
@[simp]
theorem upperRamificationGroup_zero :
    upperRamificationGroup G S 0 = ramificationGroup G S 0 := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_zero, ← Int.cast_zero,
    ramificationGroupReal_intCast]

/-- `ψℕ(0) = 0`. -/
@[simp]
theorem psiNat_zero : psiNat G S 0 = 0 := by
  rw [psiNat, Nat.cast_zero, inverseHerbrandFun_zero, Nat.floor_zero]

/-- The integral inverse Herbrand function computes `inverseHerbrandFun` at natural numbers. -/
@[simp]
theorem coe_psiNat (n : ℕ) : (psiNat G S n : ℝ) = inverseHerbrandFun G S n := by
  rcases finite_or_infinite (ramificationGroup G S 0) with _ | _
  · exact (inverseHerbrandFun_natCast_eq_floor G S n).symm
  · rw [psiNat, inverseHerbrandFun_eq_zero_of_infinite_zero G S n, Nat.floor_zero, Nat.cast_zero]

/-- At a natural number `n`, `G^n = G_{ψℕ(n)}`. -/
@[simp]
theorem upperRamificationGroup_natCast (n : ℕ) :
    upperRamificationGroup G S n = ramificationGroup G S (psiNat G S n) := by
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast, ramificationGroupReal_intCast]

/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) := fun v w hvw ↦ by
  rcases finite_or_infinite (ramificationGroup G S 0) with _ | _
  · rcases finite_or_infinite G with _ | _
    · exact ramificationGroupReal_antitone G S ((inverseHerbrandFun_strictMono G S).monotone hvw)
    · rcases le_or_gt v (-1) with hv | hv
      · rw [upperRamificationGroup_def, upperRamificationGroup_def,
          inverseHerbrandFun_eq_zero_of_infinite_of_le_neg_one G S hv, ← Int.cast_zero,
          ramificationGroupReal_intCast]
        rcases le_or_gt w (-1) with hw | hw
        · rw [inverseHerbrandFun_eq_zero_of_infinite_of_le_neg_one G S hw, ← Int.cast_zero,
            ramificationGroupReal_intCast]
        · rw [ramificationGroupReal_def]
          exact ramificationGroup_antitone G S (Int.le_ceil_iff.2 (by
            push_cast; linarith [neg_one_lt_inverseHerbrandFun_of_neg_one_lt G S hw]))
      · exact ramificationGroupReal_antitone G S
          ((inverseHerbrandFun_strictMonoOn_Ioi G S).monotoneOn hv (hv.trans_le hvw) hvw)
  · simp [upperRamificationGroup_def, inverseHerbrandFun_eq_zero_of_infinite_zero]

/-- Every upper jump is at least `-1`. -/
theorem neg_one_le_of_upperJump {v : ℝ} (hv : UpperJump G S v) : -1 ≤ v := by
  rcases finite_or_infinite (ramificationGroup G S 0) with _ | _
  · rcases finite_or_infinite G with _ | _
    · exact (neg_one_le_inverseHerbrandFun_iff G S).1
        (neg_one_le_of_lowerJump G S ((lowerJump_inverseHerbrandFun_iff G S v).2 hv))
    · by_contra h
      push Not at h
      have hlt := (upperJump_iff G S v).1 hv (-1) h
      simp [upperRamificationGroup_def,
        inverseHerbrandFun_eq_zero_of_infinite_of_le_neg_one G S le_rfl,
        inverseHerbrandFun_eq_zero_of_infinite_of_le_neg_one G S h.le] at hlt
  · have hlt := (upperJump_iff G S v).1 hv (v + 1) (by linarith)
    simp [upperRamificationGroup_def, inverseHerbrandFun_eq_zero_of_infinite_zero] at hlt

private theorem neg_one_lt_inverseHerbrandFun_of_infinite [Infinite G] (u : ℝ) :
    -1 < inverseHerbrandFun G S u := by
  rcases finite_or_infinite (ramificationGroup G S 0) with _ | _
  · rcases le_or_gt u (-1) with hu | hu
    · rw [inverseHerbrandFun_eq_zero_of_infinite_of_le_neg_one G S hu]; norm_num
    · exact neg_one_lt_inverseHerbrandFun_of_neg_one_lt G S hu
  · rw [inverseHerbrandFun_eq_zero_of_infinite_zero G S u]; norm_num

/-- **The finite-level subgroup identity.** For any subgroup `H ≤ G` acting by restriction, the
trace on `H` of the upper ramification group `G^u` is `H^{φ_H(ψ_G(u))}`. Neither finiteness of
`G`, nor normality of `H`, nor discreteness of `S`, nor any residue hypothesis is needed. -/
theorem subgroupOf_upperRamificationGroup (H : Subgroup G) (u : ℝ) :
    (upperRamificationGroup G S u).subgroupOf H =
      upperRamificationGroup H S (herbrandFun H S (inverseHerbrandFun G S u)) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def, subgroupOf_ramificationGroupReal]
  congr 1
  rcases finite_or_infinite H with _ | _
  · exact (inverseHerbrandFun_herbrandFun H S _).symm
  · have : Infinite G := Infinite.of_injective H.subtype H.subtype_injective
    rcases finite_or_infinite (ramificationGroup H S 0) with _ | _
    · exact (inverseHerbrandFun_herbrandFun_of_neg_one_lt H S
        (neg_one_lt_inverseHerbrandFun_of_infinite G S u)).symm
    · have : Infinite (ramificationGroup G S 0) := Infinite.of_injective
        (fun x : ramificationGroup H S 0 ↦
          (⟨(x.1 : G), Subgroup.mem_subgroupOf.1
            ((SetLike.ext_iff.1 (subgroupOf_ramificationGroup G S H 0) x.1).2 x.2)⟩ :
            ramificationGroup G S 0))
        fun _ _ h ↦
          Subtype.ext (Subtype.ext (congrArg (fun z : ramificationGroup G S 0 ↦ (z : G)) h))
      rw [inverseHerbrandFun_eq_zero_of_infinite_zero G S u,
        inverseHerbrandFun_eq_zero_of_infinite_zero H S]

end GeneralInverse

section Transport

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  {H : Type*} [Group H] {T : Type*} [CommRing T] [IsLocalRing T] [MulSemiringAction H T]

/-- A surjective group homomorphism with finite kernel pulling back every lower ramification group
preserves the Herbrand function: the kernel lies in every ramification group and its cardinality
cancels from the ratio `#G_t / #G_0`. -/
theorem herbrandFun_eq_of_ramificationGroup_eq_comap (φ : G →* H) [Finite φ.ker]
    (hφ : Function.Surjective φ)
    (h : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ) (u : ℝ) :
    herbrandFun G S u = herbrandFun H T u := by
  have hcard (i : ℤ) :
      Nat.card (ramificationGroup G S i) = Nat.card φ.ker * Nat.card (ramificationGroup H T i) := by
    set K := ramificationGroup G S i
    have hK : K = (ramificationGroup H T i).comap φ := h i
    have hker : (φ.domRestrict K).ker.map K.subtype = φ.ker := by
      ext g
      simp only [Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.domRestrict_apply,
        Subgroup.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun ⟨_, hg⟩ ↦ hg, fun hg ↦ ⟨by rw [hK, Subgroup.mem_comap, hg]; exact one_mem _, hg⟩⟩
    have hrange : (φ.domRestrict K).range = ramificationGroup H T i := by
      rw [MonoidHom.domRestrict_range, hK, Subgroup.map_comap_eq_self_of_surjective hφ]
    rw [← Subgroup.card_ker_mul_card_range (φ.domRestrict K), hrange,
      ← Subgroup.card_map_of_injective (K := (φ.domRestrict K).ker) K.subtype_injective, hker]
  have hker0 : (Nat.card φ.ker : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [herbrandFun_def, herbrandFun_def]
  congr 1 with t
  rw [ramificationGroupReal_def, ramificationGroupReal_def, hcard, hcard]
  push_cast
  exact mul_div_mul_left _ _ hker0

/-- A surjective group homomorphism with finite kernel pulling back every lower ramification group
preserves the inverse Herbrand function. -/
theorem inverseHerbrandFun_eq_of_ramificationGroup_eq_comap (φ : G →* H) [Finite φ.ker]
    (hφ : Function.Surjective φ)
    (h : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ) (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun H T v := by
  simp_rw [inverseHerbrandFun_def, herbrandFun_eq_of_ramificationGroup_eq_comap φ hφ h]

/-- A surjective group homomorphism with finite kernel pulling back every lower ramification group
pulls back every upper ramification group. -/
theorem upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap (φ : G →* H) [Finite φ.ker]
    (hφ : Function.Surjective φ)
    (h : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ) (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup H T v).comap φ := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    inverseHerbrandFun_eq_of_ramificationGroup_eq_comap φ hφ h,
    ramificationGroupReal_def, ramificationGroupReal_def, h]

/-- A surjective group homomorphism with finite kernel pulling back every lower ramification group
maps every upper ramification group onto the target upper ramification group. -/
theorem map_upperRamificationGroup_of_ramificationGroup_eq_comap (φ : G →* H) [Finite φ.ker]
    (hφ : Function.Surjective φ)
    (h : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ) (v : ℝ) :
    (upperRamificationGroup G S v).map φ = upperRamificationGroup H T v := by
  rw [upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap φ hφ h v,
    Subgroup.map_comap_eq_self_of_surjective hφ]

/-- An equivariant ring isomorphism along a surjective group homomorphism with finite kernel
preserves the Herbrand function. -/
theorem herbrandFun_eq_of_ringEquiv (φ : G →* H) [Finite φ.ker] (hφ : Function.Surjective φ)
    (f : S ≃+* T) (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x) (u : ℝ) :
    herbrandFun G S u = herbrandFun H T u :=
  herbrandFun_eq_of_ramificationGroup_eq_comap φ hφ
    (ramificationGroup_eq_comap_of_ringEquiv φ f hf) u

/-- An equivariant ring isomorphism along a surjective group homomorphism with finite kernel
preserves the inverse Herbrand function. -/
theorem inverseHerbrandFun_eq_of_ringEquiv (φ : G →* H) [Finite φ.ker]
    (hφ : Function.Surjective φ) (f : S ≃+* T) (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x)
    (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun H T v :=
  inverseHerbrandFun_eq_of_ramificationGroup_eq_comap φ hφ
    (ramificationGroup_eq_comap_of_ringEquiv φ f hf) v

/-- An equivariant ring isomorphism along a surjective group homomorphism with finite kernel
identifies the upper ramification groups via preimage. -/
theorem upperRamificationGroup_eq_comap_of_ringEquiv (φ : G →* H) [Finite φ.ker]
    (hφ : Function.Surjective φ) (f : S ≃+* T) (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x)
    (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup H T v).comap φ :=
  upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap φ hφ
    (ramificationGroup_eq_comap_of_ringEquiv φ f hf) v

/-- An equivariant ring isomorphism along a surjective group homomorphism with finite kernel
carries the upper ramification groups to each other. -/
theorem map_upperRamificationGroup_of_ringEquiv (φ : G →* H) [Finite φ.ker]
    (hφ : Function.Surjective φ) (f : S ≃+* T) (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x)
    (v : ℝ) :
    (upperRamificationGroup G S v).map φ = upperRamificationGroup H T v :=
  map_upperRamificationGroup_of_ramificationGroup_eq_comap φ hφ
    (ramificationGroup_eq_comap_of_ringEquiv φ f hf) v

end Transport

end TauCeti.IsLocalRing
