/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.Divisors
public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import TauCeti.NumberTheory.ModularForms.QExpansion.LevelRaise

/-!
# The all-divisor newform decomposition and newspace dimension formulas

This file completes the Atkin–Lehner–Miyake–Li theorem (Diamond–Shurman, Theorem 5.8.3; Miyake,
Theorem 4.6.19) on the decomposition of the cusp-form space `S_k(Γ₁(N))` and its nebentypus
subspaces `S_k(N, χ)` into level-raised newspaces from all divisor levels `M ∣ N`, and derives the
divisor-sum and Möbius-inverted dimension formulas in all integral weights `k : ℤ`.

*Linear independence and bases.* `Newform.span_levelRaise_eq_top` already shows that the
level-raised newforms `(V_d g)(τ) = g(dτ)`, indexed by `M ∈ N.divisors`, `d ∈ (N / M).divisors`
and `g : Newform M k`, span `S_k(Γ₁(N))`. To prove that this family is linearly independent
(`HeckeRing.GL2.Newform.linearIndependent_levelRaise_toCuspForm`), any linear relation is split
first by nebentypus modulo `N` (`iSupIndep_cuspFormCharSpace`) and then by simultaneous
eigenvalues for the good Hecke operators `Tₚ`, `p ∤ N` (`TauCeti.iSupIndep_iInf_eigenspace`).
Strong multiplicity one across divisor levels (`Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq`)
forces all active terms sharing both invariants to arise from a single divisor level `M` and a
single newform `g` of level `M`, after which `TauCeti.CuspForm.linearIndependent_levelRaise`
eliminates the remaining sum over `d ∣ N / M`. Together with spanning this gives the explicit
bases `HeckeRing.GL2.Newform.levelRaiseBasis` of `S_k(Γ₁(N))` and
`HeckeRing.GL2.Newform.levelRaiseBasisCharSpace` of `S_k(N, χ)`, as well as the internal
direct-sum decomposition `TauCeti.isInternal_map_levelRaiseₗ_cuspFormsNew`:

```text
S_k(Γ₁(N)) = ⨁_{M ∣ N} ⨁_{d ∣ N/M} V_d(S_k(Γ₁(M))ⁿᵉʷ).
```

*Dimension formulas and double-Möbius inversion.* Counting basis elements (or summing the ranks of
the injective images `V_d(S_k(Γ₁(M))ⁿᵉʷ)`) yields

```text
dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors · dim S_k(Γ₁(M))ⁿᵉʷ,
```

and at a fixed nebentypus `χ` modulo `N` the analogous sum over the multiples `M = cond(χ) · m` of
the conductor dividing `N`. Inverting the divisor-count convolution via `(μ * μ) * σ₀ = 1`
(`ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_mem_divisors`) gives the integer
newspace dimension formulas for `Γ₁(N)` (`TauCeti.finrank_cuspFormsNew_eq_sum_divisors`), for a
fixed character `χ` (`TauCeti.finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors`), and
for `Γ₀(N)` (`TauCeti.finrank_cuspFormsNew_inf_cuspFormCharSpace_one_eq_sum_divisors`), valid in
every integral weight `k : ℤ`.

## Main definitions

* `HeckeRing.GL2.Newform.levelRaiseBasis`: the level-raised newforms `(M, d, g) ↦ V_d g`, as a
  `ℂ`-basis of `S_k(Γ₁(N))`.
* `HeckeRing.GL2.Newform.levelRaiseBasisCharSpace`: the level-raised newforms whose nebentypus
  pulls back to `χ`, as a `ℂ`-basis of `S_k(N, χ)`.

## Main results

* `HeckeRing.GL2.Newform.linearIndependent_levelRaise_toCuspForm`: the family `(M, d, g) ↦ V_d g`
  over `M ∈ N.divisors`, `d ∈ (N / M).divisors`, `g : Newform M k` is `ℂ`-linearly independent.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_eq_top`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew`,
  `TauCeti.isInternal_map_levelRaiseₗ_cuspFormsNew`: the internal direct-sum decomposition of
  `S_k(Γ₁(N))` into the subspaces `V_d(S_k(Γ₁(M))ⁿᵉʷ)`.
* `TauCeti.finrank_cuspForm_Gamma1_eq_sum_divisors`,
  `TauCeti.finrank_cuspFormCharSpace_eq_sum_conductor_dvd`,
  `TauCeti.finrank_cuspFormCharSpace_changeLevel_isPrimitive`,
  `TauCeti.finrank_cuspForm_Gamma0_eq_sum_divisors`: the forward divisor-sum dimension formulas.
* `TauCeti.finrank_cuspFormsNew_eq_sum_divisors`: `(dim S_k(Γ₁(N))ⁿᵉʷ : ℤ)` as the `(μ * μ)`-sum
  of `dim S_k(Γ₁(M))` over `M ∈ N.divisors`.
* `TauCeti.finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors`,
  `TauCeti.finrank_cuspFormsNew_comap_cuspFormCharSpace_eq_sum_divisors`: the fixed-character
  `(μ * μ)`-formula over the multiples of `cond(χ)` dividing `N`.
* `TauCeti.finrank_cuspFormsNew_inf_cuspFormCharSpace_one_eq_sum_divisors`: the `Γ₀(N)` newspace
  dimension formula.
* `HeckeRing.GL2.Newform.natCast_card`, `HeckeRing.GL2.Newform.natCast_card_subtype_χ_eq`: the
  number of newforms of level `N` (and with fixed nebentypus `χ`) via `(μ * μ)`-inversion.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.19.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Finset

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2.Newform

open TauCeti _root_.CuspForm

variable {N : ℕ} {k : ℤ}

/-! ### Linear independence and bases of level-raised newforms -/

/-- Index set for the Atkin–Lehner–Miyake–Li basis of `S_k(Γ₁(N))`: triples `(M, d, g)` with
`M ∈ N.divisors`, `d ∈ (N / M).divisors` and `g : Newform M k`. -/
abbrev LevelRaiseIndex (N : ℕ) (k : ℤ) : Type :=
  Σ (M : N.divisors) (_ : (N / (M : ℕ)).divisors), Newform M k

/-- The level-raised cusp form `V_d g` in `S_k(Γ₁(N))` attached to `(M, d, g)`. -/
noncomputable def levelRaiseToCuspForm (x : LevelRaiseIndex N k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  CuspForm.levelRaise (x.2.1 : ℕ)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd (Nat.mul_dvd_of_mem_divisors x.1.2 x.2.1.2))
    x.2.2.toCuspForm

/-- The nebentypus character modulo `N` of `V_d g`, obtained by pulling `g.χ` back along
`M ∣ N`. -/
noncomputable def inducedChar (x : LevelRaiseIndex N k) : (ZMod N)ˣ →* ℂˣ :=
  x.2.2.χ.comp (ZMod.unitsMap (Nat.dvd_of_mem_divisors x.1.2))

private theorem levelRaiseToCuspForm_mem_charSpace (x : LevelRaiseIndex N k) :
    levelRaiseToCuspForm x ∈ cuspFormCharSpace k (inducedChar x) :=
  CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd
    (Nat.mul_dvd_of_mem_divisors x.1.2 x.2.1.2) x.2.2.χ x.2.2.mem_charSpace

variable [NeZero N]

/-- Two indices sharing the same induced nebentypus modulo `N` and the same eigenvalues at all
primes `p ∤ N` arise from the same divisor level `M` and the same newform `g`, so their
level-raised forms are level-raises of a single nonzero cusp form along distinct multipliers. -/
private theorem sum_eq_zero_of_same_char_and_eigenvalues {s : Finset (LevelRaiseIndex N k)}
    {c : LevelRaiseIndex N k → ℂ} (hc : ∑ x ∈ s, c x • levelRaiseToCuspForm x = 0)
    {x₀ : LevelRaiseIndex N k} (hx₀ : x₀ ∈ s)
    (hchar : ∀ x ∈ s, inducedChar x = inducedChar x₀)
    (heig : ∀ x ∈ s, ∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N),
      x.2.2.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right (Nat.dvd_of_mem_divisors x.1.2)) =
        x₀.2.2.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right (Nat.dvd_of_mem_divisors x₀.1.2))) :
    c x₀ = 0 := by
  -- Strong multiplicity one identifies `(x.1, x.2.2)` with `(x₀.1, x₀.2.2)` for every `x ∈ s`.
  have hM_eq (x : s) : x.1.1 = x₀.1 := by
    obtain ⟨hM, -⟩ := level_eq_and_coe_eq_of_comp_unitsMap_eq x.1.2.2 x₀.2.2
      (Nat.dvd_of_mem_divisors x.1.1.2) (Nat.dvd_of_mem_divisors x₀.1.2) (hchar x.1 x.2) rfl
      (S := ∅) fun p hp hpN _ ↦ heig x.1 x.2 p hp hpN
    exact Subtype.ext hM
  have hdvd (x : s) : (x.1.2.1 : ℕ) * (x₀.1 : ℕ) ∣ N := by
    rw [← hM_eq x]
    exact Nat.mul_dvd_of_mem_divisors x.1.1.2 x.1.2.1.2
  have hinj : Function.Injective (fun x : s ↦ (x.1.2.1 : ℕ)) := by
    rintro ⟨⟨M₁, d₁, g₁⟩, hx₁⟩ ⟨⟨M₂, d₂, g₂⟩, hx₂⟩ hd
    obtain rfl : M₁ = M₂ := (hM_eq ⟨_, hx₁⟩).trans (hM_eq ⟨_, hx₂⟩).symm
    obtain ⟨-, hcoe⟩ := level_eq_and_coe_eq_of_comp_unitsMap_eq g₁ g₂
      (Nat.dvd_of_mem_divisors M₁.2) (Nat.dvd_of_mem_divisors M₁.2)
      ((hchar _ hx₁).trans (hchar _ hx₂).symm) rfl (S := ∅) fun p hp hpN _ ↦
        (heig _ hx₁ p hp hpN).trans (heig _ hx₂ p hp hpN).symm
    obtain rfl : g₁ = g₂ := Newform.ext (DFunLike.coe_injective hcoe)
    obtain rfl : d₁ = d₂ := Subtype.ext hd
    rfl
  have hform_eq (x : s) :
      levelRaiseToCuspForm x.1 =
        CuspForm.levelRaise (x.1.2.1 : ℕ)
          (Gamma1_map_le_conjAct_scaleGL_of_dvd (hdvd x)) x₀.2.2.toCuspForm := by
    rcases x with ⟨⟨M, d, g⟩, hx⟩
    rcases x₀ with ⟨M₀, d₀, g₀⟩
    have hMeq : M = M₀ := hM_eq ⟨⟨M, d, g⟩, hx⟩
    subst hMeq
    obtain ⟨-, hcoe⟩ := level_eq_and_coe_eq_of_comp_unitsMap_eq g g₀
      (Nat.dvd_of_mem_divisors M.2) (Nat.dvd_of_mem_divisors M.2) (hchar _ hx) rfl
      (S := ∅) fun p hp hpN _ ↦ heig _ hx p hp hpN
    obtain rfl : g = g₀ := Newform.ext (DFunLike.coe_injective hcoe)
    rfl
  have hli := TauCeti.CuspForm.linearIndependent_levelRaise
    (one_mem_strictPeriods_Gamma1_map (x₀.1 : ℕ)) hinj
    (fun x : s ↦ Gamma1_map_le_conjAct_scaleGL_of_dvd (hdvd x)) x₀.2.2.ne_zero
  rw [linearIndependent_iff'] at hli
  refine hli s.attach (fun x ↦ c x.1) ?_ ⟨x₀, hx₀⟩ (Finset.mem_attach _ _)
  rw [← hc, ← Finset.sum_attach s]
  exact Finset.sum_congr rfl fun x _ ↦ congrArg (c x.1 • ·) (hform_eq x).symm

/-- **All level-raised newforms across divisor levels of `N` are linearly independent**
(Diamond–Shurman, Theorem 5.8.3; Miyake, Theorem 4.6.19). -/
theorem linearIndependent_levelRaise_toCuspForm :
    LinearIndependent ℂ (levelRaiseToCuspForm (N := N) (k := k)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc x₀ hx₀
  -- Step 1: project the relation onto the nebentypus component `inducedChar x₀`.
  let s₁ := {x ∈ s | inducedChar x = inducedChar x₀}
  have hs₁_sum : ∑ x ∈ s₁, c x • levelRaiseToCuspForm x = 0 := by
    have hsplit : ∑ x ∈ s₁, c x • levelRaiseToCuspForm x +
        ∑ x ∈ s with ¬ inducedChar x = inducedChar x₀, c x • levelRaiseToCuspForm x = 0 := by
      simpa only [s₁] using (Finset.sum_filter_add_sum_filter_not s
        (fun x ↦ inducedChar x = inducedChar x₀) fun x ↦ c x • levelRaiseToCuspForm x).trans hc
    refine (Submodule.disjoint_def.mp (iSupIndep_cuspFormCharSpace k (inducedChar x₀))) _
      (Submodule.sum_mem _ fun x hx ↦ ?_) ?_
    · dsimp only
      rw [← (Finset.mem_filter.mp hx).2]
      exact Submodule.smul_mem _ _ (levelRaiseToCuspForm_mem_charSpace x)
    · rw [eq_neg_of_add_eq_zero_left hsplit]
      refine neg_mem (Submodule.sum_mem _ fun x hx ↦ Submodule.mem_iSup_of_mem (inducedChar x) <|
        Submodule.mem_iSup_of_mem (Finset.mem_filter.mp hx).2 <|
          Submodule.smul_mem _ _ (levelRaiseToCuspForm_mem_charSpace x))
  -- Step 2: project onto the joint eigenspace of the good Hecke operators `Tₚ`, `p ∤ N`.
  let ιP := {p : ℕ // p.Prime ∧ p.Coprime N}
  let T : ιP → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    fun p ↦ heckeTCuspNat k p.1 (_hn := ⟨p.2.1.ne_zero⟩)
  let eig (x : LevelRaiseIndex N k) : ιP → ℂ := fun p ↦
    x.2.2.eigenvalue ⟨p.1, p.2.1.pos⟩
      (p.2.2.coprime_dvd_right (Nat.dvd_of_mem_divisors x.1.2))
  have hmem_eig (x : LevelRaiseIndex N k) :
      levelRaiseToCuspForm x ∈ ⨅ p, (T p).eigenspace (eig x p) :=
    (Submodule.mem_iInf _).mpr fun p ↦ Module.End.mem_eigenspace_iff.mpr <|
      x.2.2.heckeTCuspNat_levelRaise_eq_eigenvalue_smul
        (Nat.mul_dvd_of_mem_divisors x.1.2 x.2.1.2) p.2.1 p.2.2
  let s₂ := {x ∈ s₁ | eig x = eig x₀}
  have hs₂_sum : ∑ x ∈ s₂, c x • levelRaiseToCuspForm x = 0 := by
    have hsplit : ∑ x ∈ s₂, c x • levelRaiseToCuspForm x +
        ∑ x ∈ s₁ with ¬ eig x = eig x₀, c x • levelRaiseToCuspForm x = 0 := by
      simpa only [s₂] using (Finset.sum_filter_add_sum_filter_not s₁
        (fun x ↦ eig x = eig x₀) fun x ↦ c x • levelRaiseToCuspForm x).trans hs₁_sum
    refine (Submodule.disjoint_def.mp (iSupIndep_iInf_eigenspace T (eig x₀))) _
      (Submodule.sum_mem _ fun x hx ↦ ?_) ?_
    · dsimp only
      rw [← (Finset.mem_filter.mp hx).2]
      exact Submodule.smul_mem _ _ (hmem_eig x)
    · rw [eq_neg_of_add_eq_zero_left hsplit]
      refine neg_mem (Submodule.sum_mem _ fun x hx ↦ Submodule.mem_iSup_of_mem (eig x) <|
        Submodule.mem_iSup_of_mem (Finset.mem_filter.mp hx).2 <|
          Submodule.smul_mem _ _ (hmem_eig x))
  -- Step 3: apply strong multiplicity one and single-form level-raise independence on `s₂`.
  refine sum_eq_zero_of_same_char_and_eigenvalues hs₂_sum
    (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hx₀, rfl⟩, rfl⟩)
    (fun x hx ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2) fun x hx p hp hpN ↦ ?_
  exact congrFun (Finset.mem_filter.mp hx).2 ⟨p, hp, hpN⟩

private theorem top_le_span_range_levelRaiseToCuspForm :
    ⊤ ≤ Submodule.span ℂ (Set.range (levelRaiseToCuspForm (N := N) (k := k))) := by
  rw [← span_levelRaise_eq_top N k]
  refine Submodule.span_mono ?_
  rintro _ ⟨M, d, _, _, hdM, g, rfl⟩
  have hMN : M ∈ N.divisors := Nat.mem_divisors.mpr ⟨dvd_of_mul_left_dvd hdM, NeZero.ne N⟩
  have hd : d ∈ (N / M).divisors := by
    refine Nat.mem_divisors.mpr ⟨Nat.dvd_div_of_mul_dvd (mul_comm d M ▸ hdM), ?_⟩
    exact Nat.div_ne_zero_iff.mpr ⟨NeZero.ne M, Nat.le_of_dvd (NeZero.pos N)
      (dvd_of_mul_left_dvd hdM)⟩
  exact ⟨⟨⟨M, hMN⟩, ⟨d, hd⟩, g⟩, rfl⟩

variable (N k) in
/-- **The Atkin–Lehner–Miyake–Li basis of `S_k(Γ₁(N))`** (Diamond–Shurman, Theorem 5.8.3;
Miyake, Theorem 4.6.19): the level-raised newforms `V_d g` indexed by `M ∈ N.divisors`,
`d ∈ (N / M).divisors` and `g : Newform M k`. -/
noncomputable def levelRaiseBasis :
    Module.Basis (LevelRaiseIndex N k) ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Module.Basis.mk linearIndependent_levelRaise_toCuspForm top_le_span_range_levelRaiseToCuspForm

/-- Evaluating `levelRaiseBasis` at `(M, d, g)` gives `V_d g`. -/
@[simp]
theorem levelRaiseBasis_apply (x : LevelRaiseIndex N k) :
    levelRaiseBasis N k x = levelRaiseToCuspForm x := by
  simp [levelRaiseBasis]

/-- Because `S_k(Γ₁(N))` is finite-dimensional, `LevelRaiseIndex N k` is finite. -/
instance : Finite (LevelRaiseIndex N k) :=
  Module.Finite.finite_basis (levelRaiseBasis N k)

/-- A level-raised newform whose nebentypus pulls back to `χ`, bundled in `S_k(N, χ)`. -/
private noncomputable def levelRaiseToCharSpace (χ : (ZMod N)ˣ →* ℂˣ)
    (x : {x : LevelRaiseIndex N k // inducedChar x = χ}) : cuspFormCharSpace k χ :=
  ⟨levelRaiseToCuspForm x.1, by
    have hx := x.2
    let x₁ := x.1
    change levelRaiseToCuspForm x₁ ∈ cuspFormCharSpace k χ
    rw [← hx]
    exact levelRaiseToCuspForm_mem_charSpace x₁⟩

private theorem linearIndependent_levelRaiseToCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ (levelRaiseToCharSpace (N := N) (k := k) χ) :=
  LinearIndependent.of_comp (cuspFormCharSpace k χ).subtype
    (linearIndependent_levelRaise_toCuspForm.comp Subtype.val Subtype.val_injective)

private theorem top_le_span_range_levelRaiseToCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (levelRaiseToCharSpace (N := N) (k := k) χ)) := by
  classical
  cases nonempty_fintype (LevelRaiseIndex N k)
  rintro ⟨F, hFχ⟩ -
  set b := levelRaiseBasis N k
  -- Split `F = ∑ x, b.repr F x • b x` according to whether `inducedChar x = χ`.
  have hsum : ∑ x : LevelRaiseIndex N k, b.repr F x • b x = F := b.sum_repr F
  have hother : ∑ x : LevelRaiseIndex N k with ¬ inducedChar x = χ, b.repr F x • b x = 0 := by
    have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun x ↦ inducedChar x = χ)
      fun x ↦ b.repr F x • b x).trans hsum
    refine (Submodule.disjoint_def.mp (iSupIndep_cuspFormCharSpace k χ).symm) _
      (Submodule.sum_mem _ fun x hx ↦ Submodule.mem_iSup_of_mem (inducedChar x) <|
        Submodule.mem_iSup_of_mem (Finset.mem_filter.mp hx).2 ?_) ?_
    · rw [levelRaiseBasis_apply]
      exact Submodule.smul_mem _ _ (levelRaiseToCuspForm_mem_charSpace x)
    · rw [eq_sub_of_add_eq' hsplit]
      refine sub_mem hFχ (Submodule.sum_mem _ fun x hx ↦ ?_)
      rw [← (Finset.mem_filter.mp hx).2, levelRaiseBasis_apply]
      exact Submodule.smul_mem _ _ (levelRaiseToCuspForm_mem_charSpace x)
  have hkeep : ∑ x : LevelRaiseIndex N k with inducedChar x = χ, b.repr F x • b x = F := by
    have := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun x ↦ inducedChar x = χ)
      fun x ↦ b.repr F x • b x).trans hsum
    rwa [hother, add_zero] at this
  have hF_eq : (⟨F, hFχ⟩ : cuspFormCharSpace k χ) =
      ∑ x ∈ (Finset.univ.filter fun x : LevelRaiseIndex N k ↦ inducedChar x = χ).attach,
        b.repr F x.1 • levelRaiseToCharSpace χ ⟨x.1, (Finset.mem_filter.mp x.2).2⟩ := by
    apply Subtype.ext
    dsimp only
    rw [Submodule.coe_sum]
    conv_lhs => rw [← hkeep, ← Finset.sum_attach]
    exact Finset.sum_congr rfl fun x _ ↦ by simp [b, levelRaiseToCharSpace]
  rw [hF_eq]
  exact Submodule.sum_mem _ fun x _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x.1, (Finset.mem_filter.mp x.2).2⟩, rfl⟩)

variable (N k) in
/-- **The level-raised newform basis of `S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3; Miyake,
Theorem 4.6.19): the triples `(M, d, g)` whose newform `g` has nebentypus pulling back to `χ`
form a `ℂ`-basis of `cuspFormCharSpace k χ`. -/
noncomputable def levelRaiseBasisCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.Basis {x : LevelRaiseIndex N k // inducedChar x = χ} ℂ (cuspFormCharSpace k χ) :=
  Module.Basis.mk (linearIndependent_levelRaiseToCharSpace χ)
    (top_le_span_range_levelRaiseToCharSpace χ)

/-- Coercing `levelRaiseBasisCharSpace` back to `S_k(Γ₁(N))` gives `V_d g`. -/
@[simp]
theorem coe_levelRaiseBasisCharSpace_apply (χ : (ZMod N)ˣ →* ℂˣ)
    (x : {x : LevelRaiseIndex N k // inducedChar x = χ}) :
    (levelRaiseBasisCharSpace N k χ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      levelRaiseToCuspForm x.1 := by
  simp [levelRaiseBasisCharSpace, levelRaiseToCharSpace]

end HeckeRing.GL2.Newform

namespace TauCeti

open HeckeRing.GL2 HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### Internal direct-sum decomposition of `S_k(Γ₁(N))` into level-raised newspaces -/

/-- The family of level-raised newspaces `V_d(S_k(Γ₁(M))ⁿᵉʷ)` inside `S_k(Γ₁(N))`, indexed by
pairs `(M, d)` with `M ∈ N.divisors` and `d ∈ (N / M).divisors`. -/
private noncomputable abbrev levelRaiseNewSubmodule (N : ℕ) (k : ℤ)
    (p : Σ M : N.divisors, (N / (M : ℕ)).divisors) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (cuspFormsNew p.1 k).map
    (CuspForm.levelRaiseₗ (p.2 : ℕ)
      (Gamma1_map_le_conjAct_scaleGL_of_dvd (Nat.mul_dvd_of_mem_divisors p.1.2 p.2.2)))

private theorem repr_levelRaiseBasis_eq_zero_of_mem_map
    {p : Σ M : N.divisors, (N / (M : ℕ)).divisors}
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hF : F ∈ levelRaiseNewSubmodule N k p)
    {x : LevelRaiseIndex N k} (hx : (⟨x.1, x.2.1⟩ : Σ M : N.divisors, (N / (M : ℕ)).divisors) ≠ p) :
    (levelRaiseBasis N k).repr F x = 0 := by
  have hspan : levelRaiseNewSubmodule N k p =
      Submodule.span ℂ (Set.range fun g : Newform p.1 k ↦
        levelRaiseBasis N k ⟨p.1, p.2, g⟩) := by
    rw [levelRaiseNewSubmodule, ← Newform.span_range_toCuspForm_eq_cuspFormsNew,
      Submodule.map_span, ← Set.range_comp]
    congr 2
    ext g
    simp [CuspForm.levelRaiseₗ_apply, levelRaiseToCuspForm]
  rw [hspan] at hF
  induction hF using Submodule.span_induction with
  | mem _ hg =>
    obtain ⟨g, rfl⟩ := hg
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne]
    intro heq
    rcases p with ⟨M, d⟩
    subst heq
    exact hx rfl
  | zero => simp
  | add _ _ _ _ ha hb => simp [ha, hb]
  | smul a _ _ ha => simp [ha]

/-- **The level-raised newspaces `V_d(S_k(Γ₁(M))ⁿᵉʷ)` span `S_k(Γ₁(N))`.** -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ p : Σ M : N.divisors, (N / (M : ℕ)).divisors,
      (cuspFormsNew p.1 k).map
        (CuspForm.levelRaiseₗ (p.2 : ℕ)
          (Gamma1_map_le_conjAct_scaleGL_of_dvd (Nat.mul_dvd_of_mem_divisors p.1.2 p.2.2)))) =
      ⊤ := by
  refine eq_top_iff.mpr ((levelRaiseBasis N k).span_eq.ge.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨⟨M, d, g⟩, rfl⟩
  rw [levelRaiseBasis_apply, levelRaiseToCuspForm, ← CuspForm.levelRaiseₗ_apply]
  exact Submodule.mem_iSup_of_mem ⟨M, d⟩ (Submodule.mem_map_of_mem g.isNew)

/-- **The level-raised newspaces `V_d(S_k(Γ₁(M))ⁿᵉʷ)` are independent.** -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    iSupIndep fun p : Σ M : N.divisors, (N / (M : ℕ)).divisors ↦
      (cuspFormsNew p.1 k).map
        (CuspForm.levelRaiseₗ (p.2 : ℕ)
          (Gamma1_map_le_conjAct_scaleGL_of_dvd (Nat.mul_dvd_of_mem_divisors p.1.2 p.2.2))) := by
  intro p
  rw [Submodule.disjoint_def]
  intro F hFp hFrest
  refine (levelRaiseBasis N k).repr.injective (map_zero (levelRaiseBasis N k).repr ▸ ?_)
  ext x
  by_cases hx : (⟨x.1, x.2.1⟩ : Σ M : N.divisors, (N / (M : ℕ)).divisors) = p
  · refine Submodule.iSup_induction _ (motive := fun G ↦ (levelRaiseBasis N k).repr G x = 0)
      hFrest (fun q G hGq ↦ ?_) (by simp) fun _ _ ha hb ↦ by simp [ha, hb]
    exact Submodule.iSup_induction _ (motive := fun G ↦ (levelRaiseBasis N k).repr G x = 0)
      hGq (fun hqp H hHq ↦ repr_levelRaiseBasis_eq_zero_of_mem_map hHq (hx ▸ hqp.symm))
      (by simp) fun _ _ ha hb ↦ by simp [ha, hb]
  · exact repr_levelRaiseBasis_eq_zero_of_mem_map hFp hx

/-- **Internal direct-sum decomposition of `S_k(Γ₁(N))` into level-raised newspaces**
(Diamond–Shurman, Theorem 5.8.3; Miyake, Theorem 4.6.19):

```text
S_k(Γ₁(N)) = ⨁_{M ∣ N} ⨁_{d ∣ N/M} V_d(S_k(Γ₁(M))ⁿᵉʷ).
```
-/
theorem isInternal_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    DirectSum.IsInternal fun p : Σ M : N.divisors, (N / (M : ℕ)).divisors ↦
      (cuspFormsNew p.1 k).map
        (CuspForm.levelRaiseₗ (p.2 : ℕ)
          (Gamma1_map_le_conjAct_scaleGL_of_dvd (Nat.mul_dvd_of_mem_divisors p.1.2 p.2.2))) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew N k) (iSup_map_levelRaiseₗ_cuspFormsNew_eq_top N k)

/-! ### Forward divisor-sum dimension formulas -/

/-- The `⊓` and `comap` presentations of `S_k(N, χ)ⁿᵉʷ` have the same dimension, equal to the
number of newforms of level `N` and nebentypus `χ`. -/
theorem finrank_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) =
      Nat.card {f : Newform N k // f.χ = χ} := by
  have hcomap : (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype =
      (cuspFormsNew N k ⊓ cuspFormCharSpace k χ).comap (cuspFormCharSpace k χ).subtype := by
    ext x
    simp
  rw [← Newform.finrank_cuspFormsNew_comap_cuspFormCharSpace χ, hcomap,
    (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq]

/-- **Divisor-sum dimension formula for `S_k(Γ₁(N))`**:
`dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors · dim S_k(Γ₁(M))ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma1_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ M : N.divisors, #(N / (M : ℕ)).divisors * Module.finrank ℂ (cuspFormsNew M k) := by
  rw [Module.finrank_eq_nat_card_basis (levelRaiseBasis N k), Nat.card_sigma]
  refine Fintype.sum_congr _ _ fun M ↦ ?_
  rw [Nat.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul,
    ← Module.finrank_eq_nat_card_basis (Newform.basis M k)]

private theorem card_levelRaiseIndex_inducedChar_eq (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Nat.card {x : LevelRaiseIndex N k // inducedChar x = χ} =
      ∑ M : {M : N.divisors //
          DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ (M : ℕ)},
        #(N / (M.1 : ℕ)).divisors *
          Nat.card {g : Newform M.1 k //
            g.χ = (DirichletCharacter.changeLevel M.2
              (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom} := by
  let χ' : DirichletCharacter ℂ N := MulChar.ofUnitHom χ
  have hχ'_to : χ'.toUnitHom = χ := by
    dsimp only [χ']
    rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
  have hcond_of_eq {x : LevelRaiseIndex N k} (hx : inducedChar x = χ) :
      χ'.conductor ∣ (x.1 : ℕ) := by
    have hMN := Nat.dvd_of_mem_divisors x.1.2
    refine (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ' hMN).mp
      ⟨hMN, MulChar.ofUnitHom x.2.2.χ, ?_⟩
    apply MulChar.equivToUnitHom.injective
    rw [← MulChar.toUnitHom_eq, ← MulChar.toUnitHom_eq, hχ'_to,
      DirichletCharacter.changeLevel_toUnitHom, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
      Equiv.apply_symm_apply, ← hx, inducedChar]
  have hχ_iff {M : N.divisors} (hm : χ'.conductor ∣ (M : ℕ)) {g : Newform M k} :
      g.χ.comp (ZMod.unitsMap (Nat.dvd_of_mem_divisors M.2)) = χ ↔
        g.χ = (DirichletCharacter.changeLevel hm χ'.primitiveCharacter).toUnitHom := by
    have hMN := Nat.dvd_of_mem_divisors M.2
    have hpull :
        ((DirichletCharacter.changeLevel hm χ'.primitiveCharacter).toUnitHom).comp
          (ZMod.unitsMap hMN) = χ := by
      rw [← DirichletCharacter.changeLevel_toUnitHom, ← DirichletCharacter.changeLevel_trans,
        DirichletCharacter.changeLevel_primitiveCharacter, hχ'_to]
    exact ⟨fun hgχ ↦ (MonoidHom.cancel_right (ZMod.unitsMap_surjective hMN)).mp
      (hgχ.trans hpull.symm), fun hg ↦ by rw [hg, hpull]⟩
  let e : {x : LevelRaiseIndex N k // inducedChar x = χ} ≃
      Σ (M : {M : N.divisors // χ'.conductor ∣ (M : ℕ)}) (_ : (N / (M.1 : ℕ)).divisors),
        {g : Newform M.1 k //
          g.χ = (DirichletCharacter.changeLevel M.2 χ'.primitiveCharacter).toUnitHom} :=
    { toFun := fun ⟨x, hx⟩ ↦
        ⟨⟨x.1, hcond_of_eq hx⟩, x.2.1, ⟨x.2.2, (hχ_iff (hcond_of_eq hx)).mp hx⟩⟩
      invFun := fun ⟨⟨M, hm⟩, d, ⟨g, hg⟩⟩ ↦ ⟨⟨M, d, g⟩, (hχ_iff hm).mpr hg⟩
      left_inv := fun ⟨⟨_, _, _⟩, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, _, ⟨_, _⟩⟩ ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  refine Fintype.sum_congr _ _ fun M ↦ ?_
  rw [Nat.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]

/-- **Divisor-sum dimension formula for `S_k(N, χ)`** over the divisor levels `M ∣ N` divisible
by the conductor of `χ`. -/
theorem finrank_cuspFormCharSpace_eq_sum_conductor_dvd (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank ℂ (cuspFormCharSpace k χ) =
      ∑ M : {M : N.divisors //
          DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ (M : ℕ)},
        #(N / (M.1 : ℕ)).divisors *
          Module.finrank ℂ ↥(cuspFormsNew M.1 k ⊓
            cuspFormCharSpace k
              (DirichletCharacter.changeLevel M.2
                (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) := by
  rw [Module.finrank_eq_nat_card_basis (levelRaiseBasisCharSpace N k χ),
    card_levelRaiseIndex_inducedChar_eq]
  refine Fintype.sum_congr _ _ fun M ↦ ?_
  rw [finrank_cuspFormsNew_inf_cuspFormCharSpace]

/-- **Divisor-sum dimension formula for `S_k(c · m, χ₀)`** when `χ₀` is a primitive Dirichlet
character of conductor `c`: the contributing divisor levels are `M = c · d` for `d ∣ m`. -/
theorem finrank_cuspFormCharSpace_changeLevel_isPrimitive {c m : ℕ} [NeZero c] [NeZero m]
    (k : ℤ) {χ₀ : DirichletCharacter ℂ c} (hχ₀ : χ₀.IsPrimitive) :
    Module.finrank ℂ
        (cuspFormCharSpace k
          (DirichletCharacter.changeLevel (dvd_mul_right c m) χ₀).toUnitHom) =
      ∑ d : m.divisors, #(m / (d : ℕ)).divisors *
        Module.finrank ℂ ↥(cuspFormsNew (c * (d : ℕ)) k ⊓
          cuspFormCharSpace k
            (DirichletCharacter.changeLevel (dvd_mul_right c (d : ℕ)) χ₀).toUnitHom) := by
  let χm : DirichletCharacter ℂ (c * m) :=
    DirichletCharacter.changeLevel (dvd_mul_right c m) χ₀
  have hmul_eq : (MulChar.ofUnitHom χm.toUnitHom : DirichletCharacter ℂ (c * m)) = χm := by
    rw [MulChar.ofUnitHom_eq, MulChar.toUnitHom_eq, Equiv.symm_apply_apply]
  have hcond : DirichletCharacter.conductor (MulChar.ofUnitHom χm.toUnitHom) = c := by
    rw [hmul_eq, DirichletCharacter.conductor_changeLevel χ₀ (dvd_mul_right c m), hχ₀]
  rw [finrank_cuspFormCharSpace_eq_sum_conductor_dvd]
  let bij : m.divisors ≃
      {M : (c * m).divisors //
        DirichletCharacter.conductor (MulChar.ofUnitHom χm.toUnitHom) ∣ (M : ℕ)} :=
    { toFun := fun d ↦
        have hcd : c * (d : ℕ) ∣ c * m := mul_dvd_mul_left c (Nat.dvd_of_mem_divisors d.2)
        ⟨⟨c * (d : ℕ), Nat.mem_divisors.mpr ⟨hcd, NeZero.ne (c * m)⟩⟩, by
          dsimp only
          rw [hcond]
          exact dvd_mul_right c d⟩
      invFun := fun ⟨M, hm⟩ ↦
        have hcM : c ∣ (M : ℕ) := by rwa [hcond] at hm
        have hdvd : (M : ℕ) / c ∣ m := (mul_dvd_mul_iff_left (NeZero.ne c)).mp
          ((Nat.mul_div_cancel' hcM).symm ▸ Nat.dvd_of_mem_divisors M.2)
        ⟨(M : ℕ) / c, Nat.mem_divisors.mpr ⟨hdvd, NeZero.ne m⟩⟩
      left_inv := fun d ↦ Subtype.ext (Nat.mul_div_cancel_left (d : ℕ) (NeZero.pos c))
      right_inv := fun ⟨M, hm⟩ ↦ Subtype.ext <| Subtype.ext <| by
        rw [hcond] at hm
        exact Nat.mul_div_cancel' hm }
  rw [← Equiv.sum_comp bij]
  refine Fintype.sum_congr _ _ fun d ↦ ?_
  have hchar : DirichletCharacter.changeLevel (bij d).2
      (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χm.toUnitHom)) =
        DirichletCharacter.changeLevel (dvd_mul_right c (d : ℕ)) χ₀ := by
    apply DirichletCharacter.changeLevel_injective
      (mul_dvd_mul_left c (Nat.dvd_of_mem_divisors d.2))
    rw [← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter,
      hmul_eq, ← DirichletCharacter.changeLevel_trans]
  rw [hchar]
  have hval : ((bij d).1 : ℕ) = c * (d : ℕ) := rfl
  congr 1
  rw [hval, Nat.mul_div_mul_left m (d : ℕ) (NeZero.pos c)]

/-- **Divisor-sum dimension formula for `S_k(Γ₀(N))`.** -/
theorem finrank_cuspForm_Gamma0_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) =
      ∑ M : N.divisors, #(N / (M : ℕ)).divisors *
        Module.finrank ℂ ↥(cuspFormsNew M k ⊓ cuspFormCharSpace k (1 : (ZMod M)ˣ →* ℂˣ)) := by
  rw [← (cuspFormCharSpaceOneEquiv N k).finrank_eq,
    finrank_cuspFormCharSpace_eq_sum_conductor_dvd]
  have h1 : (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ) : DirichletCharacter ℂ N) = 1 := by
    apply MulChar.equivToUnitHom.injective
    rw [MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, ← MulChar.toUnitHom_eq]
    ext
    simp
  have hcond1 :
      DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) = 1 := by
    rw [h1, DirichletCharacter.conductor_one]
  let bij : N.divisors ≃
      {M : N.divisors //
        DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ (M : ℕ)} :=
    { toFun := fun M ↦ ⟨M, by rw [hcond1]; exact one_dvd (M : ℕ)⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun ⟨_, _⟩ ↦ rfl }
  rw [← Equiv.sum_comp bij]
  refine Fintype.sum_congr _ _ fun M ↦ ?_
  have hchar : (DirichletCharacter.changeLevel (bij M).2
      (DirichletCharacter.primitiveCharacter
        (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)))).toUnitHom = 1 := by
    have hch : DirichletCharacter.changeLevel (bij M).2
        (DirichletCharacter.primitiveCharacter
          (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ))) = 1 := by
      apply (DirichletCharacter.changeLevel_eq_one_iff (Nat.dvd_of_mem_divisors M.2)).mp
      rw [← DirichletCharacter.changeLevel_trans,
        DirichletCharacter.changeLevel_primitiveCharacter]
      exact h1
    rw [hch]
    ext
    simp
  rw [hchar]
  rfl

/-! ### Möbius-inverted newspace dimension formulas -/

/-- **Möbius-inverted dimension formula for `S_k(Γ₁(N))ⁿᵉʷ`** (Diamond–Shurman, Theorem 5.8.3),
valid in all integral weights `k : ℤ`:

```text
dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M)).
```
-/
theorem finrank_cuspFormsNew_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ) :
    (Module.finrank ℂ (cuspFormsNew N k) : ℤ) =
      ∑ M ∈ N.divisors, (ArithmeticFunction.moebius * ArithmeticFunction.moebius) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) : ℤ) := by
  let g : ℕ → ℤ := fun M ↦
    if hM : M ≠ 0 then
      have : NeZero M := ⟨hM⟩
      (Module.finrank ℂ (cuspFormsNew M k) : ℤ)
    else 0
  have hgN : g N = (Module.finrank ℂ (cuspFormsNew N k) : ℤ) := by simp [g, NeZero.ne N]
  rw [← hgN]
  refine ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_mem_divisors (NeZero.ne N)
    (f := fun M ↦ (Module.finrank ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) : ℤ))
    (g := g) fun M hMN ↦ ?_
  have : NeZero M := ⟨(Nat.pos_of_mem_divisors hMN).ne'⟩
  rw [finrank_cuspForm_Gamma1_eq_sum_divisors M k, Nat.cast_sum, ← Finset.sum_coe_sort M.divisors]
  refine Fintype.sum_congr _ _ fun d ↦ ?_
  simp [g, (Nat.pos_of_mem_divisors d.2).ne']

private theorem finrank_cuspFormsNew_inf_cuspFormCharSpace_congr {M₁ M₂ : ℕ} [NeZero M₁]
    [NeZero M₂] (h : M₁ = M₂) {χ₁ : (ZMod M₁)ˣ →* ℂˣ} {χ₂ : (ZMod M₂)ˣ →* ℂˣ}
    (hχ : χ₁.comp (ZMod.unitsMap (dvd_of_eq h)) = χ₂) :
    Module.finrank ℂ ↥(cuspFormsNew M₁ k ⊓ cuspFormCharSpace k χ₁) =
      Module.finrank ℂ ↥(cuspFormsNew M₂ k ⊓ cuspFormCharSpace k χ₂) := by
  subst h
  rw [ZMod.unitsMap_self, MonoidHom.comp_id] at hχ
  subst hχ
  rfl

/-- **Möbius-inverted dimension formula for `S_k(N, χ)ⁿᵉʷ`** (Diamond–Shurman, Theorem 5.8.3),
summing over the divisors `m` of `N / cond(χ)` (that is, the levels `M = cond(χ) · m` with
`cond(χ) ∣ M ∣ N`), in all integral weights `k : ℤ`. -/
theorem finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) : ℤ) =
      ∑ m ∈ (N / DirichletCharacter.conductor (MulChar.ofUnitHom χ)).divisors,
        (ArithmeticFunction.moebius * ArithmeticFunction.moebius)
          (N / (DirichletCharacter.conductor (MulChar.ofUnitHom χ) * m)) *
          (Module.finrank ℂ
            (cuspFormCharSpace k
              (DirichletCharacter.changeLevel
                (dvd_mul_right (DirichletCharacter.conductor (MulChar.ofUnitHom χ)) m)
                (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) :
            ℤ) := by
  let χ' : DirichletCharacter ℂ N := MulChar.ofUnitHom χ
  let c := χ'.conductor
  have hcN : c ∣ N := χ'.conductor_dvd_level
  have hc0 : c ≠ 0 := χ'.conductor_ne_zero
  have : NeZero c := ⟨hc0⟩
  have hNc0 : N / c ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hc0, Nat.le_of_dvd (NeZero.pos N) hcN⟩
  let ψ : ∀ m : ℕ, (ZMod (c * m))ˣ →* ℂˣ := fun m ↦
    (DirichletCharacter.changeLevel (dvd_mul_right c m) χ'.primitiveCharacter).toUnitHom
  let g : ℕ → ℤ := fun m ↦
    if hm : m ≠ 0 then
      have : NeZero (c * m) := ⟨mul_ne_zero hc0 hm⟩
      (Module.finrank ℂ ↥(cuspFormsNew (c * m) k ⊓ cuspFormCharSpace k (ψ m)) : ℤ)
    else 0
  have hcmN : c * (N / c) = N := Nat.mul_div_cancel' hcN
  have hψN : (ψ (N / c)).comp (ZMod.unitsMap (dvd_of_eq hcmN)) = χ := by
    have hch : DirichletCharacter.changeLevel (dvd_of_eq hcmN)
        (DirichletCharacter.changeLevel (dvd_mul_right c (N / c)) χ'.primitiveCharacter) = χ' := by
      rw [← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]
    have h1 : (ψ (N / c)).comp (ZMod.unitsMap (dvd_of_eq hcmN)) = χ'.toUnitHom := by
      rw [← DirichletCharacter.changeLevel_toUnitHom]
      exact congrArg MulChar.toUnitHom hch
    rw [h1]
    dsimp only [χ']
    rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
  have : NeZero (c * (N / c)) := ⟨mul_ne_zero hc0 hNc0⟩
  have hgNc : g (N / c) = (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) : ℤ) := by
    change (if hm : N / c ≠ 0 then _ else 0) = _
    rw [dite_eq_left_of_eq_true (eq_true hNc0)]
    exact congrArg Nat.cast (finrank_cuspFormsNew_inf_cuspFormCharSpace_congr hcmN hψN)
  rw [← hgNc]
  have hinv := ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_mem_divisors hNc0
    (f := fun m ↦ (Module.finrank ℂ (cuspFormCharSpace k (ψ m)) : ℤ)) (g := g) fun m hm ↦ by
      have : NeZero m := ⟨(Nat.pos_of_mem_divisors hm).ne'⟩
      rw [finrank_cuspFormCharSpace_changeLevel_isPrimitive k χ'.primitiveCharacter_isPrimitive,
        Nat.cast_sum, ← Finset.sum_coe_sort m.divisors]
      refine Fintype.sum_congr _ _ fun d ↦ ?_
      simp [g, ψ, c, (Nat.pos_of_mem_divisors d.2).ne']
  rw [hinv]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Nat.div_div_eq_div_mul, Int.cast_id]

/-- `comap`-form of `TauCeti.finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors`, matching
`HeckeRing.GL2.Newform.finrank_cuspFormsNew_comap_cuspFormCharSpace`. -/
theorem finrank_cuspFormsNew_comap_cuspFormCharSpace_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    (Module.finrank ℂ ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) : ℤ) =
      ∑ m ∈ (N / DirichletCharacter.conductor (MulChar.ofUnitHom χ)).divisors,
        (ArithmeticFunction.moebius * ArithmeticFunction.moebius)
          (N / (DirichletCharacter.conductor (MulChar.ofUnitHom χ) * m)) *
          (Module.finrank ℂ
            (cuspFormCharSpace k
              (DirichletCharacter.changeLevel
                (dvd_mul_right (DirichletCharacter.conductor (MulChar.ofUnitHom χ)) m)
                (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) :
            ℤ) := by
  rw [Newform.finrank_cuspFormsNew_comap_cuspFormCharSpace,
    ← finrank_cuspFormsNew_inf_cuspFormCharSpace,
    finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors]

/-- **Möbius-inverted dimension formula for the `Γ₀(N)` newspace** (Diamond–Shurman,
Theorem 5.8.3, trivial character), valid in all integral weights `k : ℤ`:

```text
dim S_k(Γ₀(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M)).
```
-/
theorem finrank_cuspFormsNew_inf_cuspFormCharSpace_one_eq_sum_divisors (N : ℕ) [NeZero N]
    (k : ℤ) :
    (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) : ℤ) =
      ∑ M ∈ N.divisors, (ArithmeticFunction.moebius * ArithmeticFunction.moebius) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma0 M).map (mapGL ℝ)) k) : ℤ) := by
  let g : ℕ → ℤ := fun M ↦
    if hM : M ≠ 0 then
      have : NeZero M := ⟨hM⟩
      (Module.finrank ℂ ↥(cuspFormsNew M k ⊓ cuspFormCharSpace k (1 : (ZMod M)ˣ →* ℂˣ)) : ℤ)
    else 0
  have hgN : g N =
      (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) : ℤ) := by
    simp [g, NeZero.ne N]
  rw [← hgN]
  refine ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_mem_divisors (NeZero.ne N)
    (f := fun M ↦ (Module.finrank ℂ (CuspForm ((Gamma0 M).map (mapGL ℝ)) k) : ℤ))
    (g := g) fun M hMN ↦ ?_
  have : NeZero M := ⟨(Nat.pos_of_mem_divisors hMN).ne'⟩
  rw [finrank_cuspForm_Gamma0_eq_sum_divisors M k, Nat.cast_sum, ← Finset.sum_coe_sort M.divisors]
  refine Fintype.sum_congr _ _ fun d ↦ ?_
  simp [g, (Nat.pos_of_mem_divisors d.2).ne']

end TauCeti

namespace HeckeRing.GL2.Newform

open TauCeti

/-- **The number of newforms of level `N` and weight `k`** via double-Möbius inversion of the
`Γ₁` cusp-form dimensions. -/
theorem natCast_card (N : ℕ) [NeZero N] (k : ℤ) :
    (Nat.card (Newform N k) : ℤ) =
      ∑ M ∈ N.divisors, (ArithmeticFunction.moebius * ArithmeticFunction.moebius) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) : ℤ) := by
  rw [← Module.finrank_eq_nat_card_basis (basis N k), finrank_cuspFormsNew_eq_sum_divisors]

/-- **The number of newforms of level `N`, weight `k`, and nebentypus `χ`** via double-Möbius
inversion over the multiples of `cond(χ)` dividing `N`. -/
theorem natCast_card_subtype_χ_eq (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (Nat.card {f : Newform N k // f.χ = χ} : ℤ) =
      ∑ m ∈ (N / DirichletCharacter.conductor (MulChar.ofUnitHom χ)).divisors,
        (ArithmeticFunction.moebius * ArithmeticFunction.moebius)
          (N / (DirichletCharacter.conductor (MulChar.ofUnitHom χ) * m)) *
          (Module.finrank ℂ
            (cuspFormCharSpace k
              (DirichletCharacter.changeLevel
                (dvd_mul_right (DirichletCharacter.conductor (MulChar.ofUnitHom χ)) m)
                (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) :
            ℤ) := by
  rw [← finrank_cuspFormsNew_inf_cuspFormCharSpace,
    finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors]

end HeckeRing.GL2.Newform
