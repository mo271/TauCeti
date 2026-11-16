/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.ExtendScalars
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# Automorphism and isomorphism-class counts over the unramified part

Let `K` be a nonarchimedean local field with `q` residue classes, and let `L` be a finite
subextension of `SeparableClosure K` of residue degree `f = L.inertiaDegree`. By
`IntermediateField.unramifiedExtension_inertiaDegree_le`, `L` contains the canonical unramified
extension `K_f = unramifiedExtension K (SeparableClosure K) f`, which is finite and Galois of
degree `f` over `K`.

Restriction of `K`-automorphisms from `L` to `K_f` sits in a short exact sequence with kernel the
`K_f`-automorphism group of `L` (viewed over `K_f` via `IntermediateField.extendScalars`) and image
the subgroup of `Gal(K_f / K)` consisting of automorphisms that extend to `L`. Applying
`IntermediateField.natCard_algEquiv_eq_mul_of_le` yields the automorphism factorization
`#Aut_K(L) = #Aut_{K_f}(L) · #{τ ∈ Gal(K_f / K) | τ extends to L}`
(`IntermediateField.natCard_algEquiv_eq_mul`).

For fixed degree `n` and residue degree `f`, this file also packages the carrier
`TauCeti.subextensionsOfDegreeInertia K n f` of subextensions of `SeparableClosure K` of degree `n`
and residue degree `f`, proves its closure under `K`-isomorphism and its orbit-count identity
`#{M ∈ subextensionsOfDegreeInertia K n f | L ≃ₐ[K] M} · #Aut_K(L) = n`, characterizes its members
as intermediate fields over `K_f` of degree `e` and residue degree `f` over `K` (and transports
them to `totallyRamifiedOfDegree F e` over an unramified base `F`), and establishes both the
weighted `1 / #Aut` class-sum reduction from `K`-isomorphism classes to `K_f`-isomorphism classes
and the refined Serre mass formula over `K`-isomorphism classes:
`∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ d(M / K)) = 1 / (f · q ^ (f(e - 1)))`.

## Main definitions

* `TauCeti.subextensionsOfDegreeInertia`: the subextensions of `SeparableClosure K` of degree
  `n` and residue degree `f` over `K`.
* `TauCeti.IsDegreeInertiaRepresentativeSet`: `R` is a set of representatives of the
  `K`-isomorphism classes in `subextensionsOfDegreeInertia K n f`.
* `TauCeti.subextensionsOfDegreeInertiaEquiv`: equivalence between
  `subextensionsOfDegreeInertia K (f * e) f` and intermediate fields of
  `SeparableClosure K / K_f` of degree `e` over `K_f` and residue degree `f` over `K`.
* `TauCeti.restrictScalarsEquivTotallyRamifiedOfDegree`: equivalence with
  `totallyRamifiedOfDegree F e` over an unramified base `F`.

## Main results

* `IntermediateField.natCard_algEquiv_eq_mul`: for a finite subextension `L` of
  `SeparableClosure K`, `#Aut_K(L)` equals `#Aut_{K_f}(L)` times the number of automorphisms of
  `K_f / K` extending to `L`, where `K_f = unramifiedExtension K (SeparableClosure K) f(L / K)`.
* `TauCeti.ncard_isomorphic_mul_natCard_algEquiv_of_mem_subextensionsOfDegreeInertia`: the orbit
  count `#{M ∈ subextensionsOfDegreeInertia K n f | L ≃ₐ[K] M} · #Aut_K(L) = n`.
* `TauCeti.ncard_isomorphic_restrictScalars_unramifiedExtension_mul_natCard`: orbit count on
  `K_f`-isomorphism classes under `Gal(K_f / K)`.
* `TauCeti.tsum_div_natCard_algEquiv_unramifiedExtension`: weighted `1 / #Aut` class-sum reduction
  from `K`-isomorphism classes to `K_f`-isomorphism classes, dividing by `f`.

In the namespace `TauCeti.IsDegreeInertiaRepresentativeSet`:

* `tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent`:
  refined Serre mass formula over `K`-isomorphism classes of degree `f * e` and residue degree `f`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Théorèmes 1–2 and
  Remarque 3°.
-/

public section
noncomputable section

open ValuativeRel IntermediateField
open scoped ENNReal

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Automorphism count over the unramified part**: for a finite subextension `L` of
`SeparableClosure K` with residue degree `f = L.inertiaDegree` and canonical unramified part
`K_f = TauCeti.unramifiedExtension K (SeparableClosure K) f ≤ L`, the cardinality of `L ≃ₐ[K] L`
equals the cardinality of the `K_f`-automorphism group of `extendScalars` of `L` multiplied by the
number of `K`-automorphisms of `K_f` that extend to `L`. -/
theorem natCard_algEquiv_eq_mul (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
          TauCeti.unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
          extendScalars L.unramifiedExtension_inertiaDegree_le) *
        Nat.card {τ : TauCeti.unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≃ₐ[K]
            TauCeti.unramifiedExtension K (SeparableClosure K) L.inertiaDegree //
          ∃ σ : L ≃ₐ[K] L, ∀ x,
            (σ ⟨x.1, L.unramifiedExtension_inertiaDegree_le x.2⟩ : SeparableClosure K) = τ x} :=
  natCard_algEquiv_eq_mul_of_le L.unramifiedExtension_inertiaDegree_le

/-- The order of the automorphism group of a finite subextension `L` over its unramified part
divides `#Aut_K(L)`. -/
theorem natCard_extendScalars_unramifiedExtension_algEquiv_dvd
    (L : IntermediateField K (SeparableClosure K)) [Module.Finite K L] :
    Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
        TauCeti.unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
        extendScalars L.unramifiedExtension_inertiaDegree_le) ∣
      Nat.card (L ≃ₐ[K] L) :=
  natCard_extendScalars_algEquiv_dvd L.unramifiedExtension_inertiaDegree_le

/-- The number of `K`-automorphisms of the unramified part of `L` that extend to `L` divides the
residue degree `L.inertiaDegree`. -/
theorem natCard_subtype_extend_unramifiedExtension_dvd_inertiaDegree
    (L : IntermediateField K (SeparableClosure K)) [Module.Finite K L] :
    Nat.card {τ : TauCeti.unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≃ₐ[K]
        TauCeti.unramifiedExtension K (SeparableClosure K) L.inertiaDegree //
      ∃ σ : L ≃ₐ[K] L, ∀ x,
        (σ ⟨x.1, L.unramifiedExtension_inertiaDegree_le x.2⟩ : SeparableClosure K) = τ x} ∣
      L.inertiaDegree := by
  have hdvd := natCard_subtype_extend_dvd_natCard_algEquiv L.unramifiedExtension_inertiaDegree_le
  rwa [IsGalois.card_aut_eq_finrank,
    TauCeti.finrank_unramifiedExtension L.inertiaDegree_pos.ne'] at hdvd

end IntermediateField

namespace TauCeti

section Carrier

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The set of subextensions of `SeparableClosure K` having degree `n` and residue degree `f` over
`K`. When `f ≥ 1` and `n = f * e`, these are the subextensions containing the canonical unramified
extension `K_f` that are totally ramified of degree `e` over `K_f`. -/
def subextensionsOfDegreeInertia (n f : ℕ) : Set (IntermediateField K (SeparableClosure K)) :=
  {L | Module.finrank K L = n ∧ L.inertiaDegree = f}

/-- Explicit set-builder description of `subextensionsOfDegreeInertia K n f`. -/
theorem subextensionsOfDegreeInertia_def (n f : ℕ) :
    subextensionsOfDegreeInertia K n f =
      {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = n ∧ L.inertiaDegree = f} :=
  (rfl)

variable {K}

/-- Membership in `subextensionsOfDegreeInertia K n f`: degree `n` and residue degree `f`. -/
@[simp]
theorem mem_subextensionsOfDegreeInertia_iff {n f : ℕ}
    {L : IntermediateField K (SeparableClosure K)} :
    L ∈ subextensionsOfDegreeInertia K n f ↔ Module.finrank K L = n ∧ L.inertiaDegree = f :=
  Iff.rfl

/-- Any member of `subextensionsOfDegreeInertia K n f` with `n ≠ 0` or `f ≠ 0` is finite over
`K`. -/
theorem finite_of_mem_subextensionsOfDegreeInertia {n f : ℕ}
    {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ subextensionsOfDegreeInertia K n f) (h : n ≠ 0 ∨ f ≠ 0) :
    Module.Finite K L := by
  rw [mem_subextensionsOfDegreeInertia_iff] at hL
  rcases h with hn | hf
  · exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero (hL.1 ▸ hn))
  · by_contra hfin
    exact hf (hL.2.symm.trans (L.inertiaDegree_of_not_finite hfin))

/-- For `f ≠ 0`, there is no subextension of `finrank` `0` and residue degree `f`: positive residue
degree forces finiteness over `K`, hence positive `finrank`. -/
@[simp]
theorem subextensionsOfDegreeInertia_zero_left {f : ℕ} (hf : f ≠ 0) :
    subextensionsOfDegreeInertia K 0 f = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun L hL ↦ ?_
  have := finite_of_mem_subextensionsOfDegreeInertia hL (.inr hf)
  exact Module.finrank_pos.ne' hL.1

/-- For `n ≠ 0`, there is no subextension of `finrank` `n` and residue degree `0`: positive
`finrank` forces finiteness over `K`, hence positive residue degree. -/
@[simp]
theorem subextensionsOfDegreeInertia_zero_right {n : ℕ} (hn : n ≠ 0) :
    subextensionsOfDegreeInertia K n 0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun L hL ↦ ?_
  have := finite_of_mem_subextensionsOfDegreeInertia hL (.inl hn)
  exact L.inertiaDegree_pos.ne' hL.2

/-- Subextensions of residue degree `1` and degree `n` are precisely the totally ramified
subextensions `totallyRamifiedOfDegree K n`. -/
@[simp]
theorem subextensionsOfDegreeInertia_one_right (n : ℕ) :
    subextensionsOfDegreeInertia K n 1 = totallyRamifiedOfDegree K n := by
  ext L
  rw [mem_subextensionsOfDegreeInertia_iff, mem_totallyRamifiedOfDegree_iff,
    IntermediateField.isTotallyRamified_iff_inertiaDegree_eq_one]

/-- For `f ≠ 0`, the unique subextension of `SeparableClosure K` of degree `f` and residue degree
`f` is `unramifiedExtension K (SeparableClosure K) f`. -/
theorem subextensionsOfDegreeInertia_self {f : ℕ} (hf : f ≠ 0) :
    subextensionsOfDegreeInertia K f f = {unramifiedExtension K (SeparableClosure K) f} := by
  set U := unramifiedExtension K (SeparableClosure K) f
  ext L
  rw [mem_subextensionsOfDegreeInertia_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hdeg, hiner⟩
    have : Module.Finite K L :=
      finite_of_mem_subextensionsOfDegreeInertia ⟨hdeg, hiner⟩ (.inr hf)
    have hUL : U ≤ L := by simpa [U, hiner] using L.unramifiedExtension_inertiaDegree_le
    exact (eq_of_le_of_finrank_eq hUL ((finrank_unramifiedExtension hf).trans hdeg.symm)).symm
  · rintro rfl
    refine ⟨finrank_unramifiedExtension hf, ?_⟩
    rw [U.inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) U
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) U
    have : IsUnramified K U := isUnramified_unramifiedExtension
    rw [IsUnramified.inertiaDegree_eq_finrank, finrank_unramifiedExtension hf]

/-- `subextensionsOfDegreeInertia K n f` is closed under `K`-algebra isomorphism, including the
degenerate case `n = 0, f = 0`. -/
theorem mem_subextensionsOfDegreeInertia_of_algEquiv {n f : ℕ}
    {L M : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ subextensionsOfDegreeInertia K n f) (e : L ≃ₐ[K] M) :
    M ∈ subextensionsOfDegreeInertia K n f :=
  ⟨e.symm.toLinearEquiv.finrank_eq.trans hL.1,
    (IntermediateField.inertiaDegree_eq_of_algEquiv e).symm.trans hL.2⟩

/-- Ambient `K`-automorphisms of `SeparableClosure K` preserve
`subextensionsOfDegreeInertia K n f`. -/
theorem map_mem_subextensionsOfDegreeInertia_iff {n f : ℕ}
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    {L : IntermediateField K (SeparableClosure K)} :
    L.map (σ : SeparableClosure K →ₐ[K] SeparableClosure K) ∈
        subextensionsOfDegreeInertia K n f ↔
      L ∈ subextensionsOfDegreeInertia K n f :=
  ⟨fun h ↦ mem_subextensionsOfDegreeInertia_of_algEquiv h (intermediateFieldMap σ L).symm,
    fun h ↦ mem_subextensionsOfDegreeInertia_of_algEquiv h (intermediateFieldMap σ L)⟩

/-! ### Orbit count on `subextensionsOfDegreeInertia` -/

/-- The members of `subextensionsOfDegreeInertia K n f` that are `K`-isomorphic to a member `L`
coincide with all subextensions of `SeparableClosure K` that are `K`-isomorphic to `L`. -/
theorem setOf_mem_subextensionsOfDegreeInertia_isomorphic {n f : ℕ}
    {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ subextensionsOfDegreeInertia K n f) :
    {M ∈ subextensionsOfDegreeInertia K n f | Nonempty (L ≃ₐ[K] M)} =
      {M : IntermediateField K (SeparableClosure K) | Nonempty (L ≃ₐ[K] M)} :=
  Set.ext fun _ ↦ and_iff_right_of_imp fun ⟨e⟩ ↦ mem_subextensionsOfDegreeInertia_of_algEquiv hL e

/-- **Orbit count by degree and residue degree**: for `L ∈ subextensionsOfDegreeInertia K n f`
with `n ≠ 0` or `f ≠ 0`, the number of members of `subextensionsOfDegreeInertia K n f` that are
`K`-isomorphic to `L`, multiplied by `#Aut_K(L)`, equals `n`. -/
theorem ncard_isomorphic_mul_natCard_algEquiv_of_mem_subextensionsOfDegreeInertia {n f : ℕ}
    {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ subextensionsOfDegreeInertia K n f) (h : n ≠ 0 ∨ f ≠ 0) :
    {M ∈ subextensionsOfDegreeInertia K n f | Nonempty (L ≃ₐ[K] M)}.ncard *
      Nat.card (L ≃ₐ[K] L) = n := by
  have := finite_of_mem_subextensionsOfDegreeInertia hL h
  rw [setOf_mem_subextensionsOfDegreeInertia_isomorphic hL,
    IntermediateField.ncard_isomorphic_mul_natCard_algEquiv_of_isSepClosed, hL.1]

/-- A Galois member `L` of `subextensionsOfDegreeInertia K n f` is the sole member of its
`K`-isomorphism class. -/
theorem setOf_mem_subextensionsOfDegreeInertia_isomorphic_eq_singleton_of_normal {n f : ℕ}
    {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ subextensionsOfDegreeInertia K n f) [Normal K L] :
    {M ∈ subextensionsOfDegreeInertia K n f | Nonempty (L ≃ₐ[K] M)} = {L} := by
  rw [setOf_mem_subextensionsOfDegreeInertia_isomorphic hL,
    IntermediateField.setOf_isomorphic_eq_singleton_of_normal]

/-- A Galois member `L` of `subextensionsOfDegreeInertia K n f` (with `n ≠ 0` or `f ≠ 0`) has
exactly `n` automorphisms over `K`. -/
theorem natCard_algEquiv_of_mem_subextensionsOfDegreeInertia_of_normal {n f : ℕ}
    {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ subextensionsOfDegreeInertia K n f) (h : n ≠ 0 ∨ f ≠ 0) [Normal K L] :
    Nat.card (L ≃ₐ[K] L) = n := by
  have hcard := ncard_isomorphic_mul_natCard_algEquiv_of_mem_subextensionsOfDegreeInertia hL h
  rwa [setOf_mem_subextensionsOfDegreeInertia_isomorphic_eq_singleton_of_normal hL,
    Set.ncard_singleton, one_mul] at hcard

/-! ### Representative sets of `K`-isomorphism classes by degree and residue degree -/

/-- A set `R` of subextensions of `SeparableClosure K` is a *set of representatives* of the
`K`-isomorphism classes in `subextensionsOfDegreeInertia K n f` when `R` is contained in
`subextensionsOfDegreeInertia K n f` and every member of `subextensionsOfDegreeInertia K n f` is
`K`-isomorphic to a unique member of `R`. -/
def IsDegreeInertiaRepresentativeSet (n f : ℕ)
    (R : Set (IntermediateField K (SeparableClosure K))) : Prop :=
  R ⊆ subextensionsOfDegreeInertia K n f ∧
    ∀ L ∈ subextensionsOfDegreeInertia K n f, ∃! M, M ∈ R ∧ Nonempty (L ≃ₐ[K] M)

/-- Unfolds `IsDegreeInertiaRepresentativeSet n f R`. -/
theorem isDegreeInertiaRepresentativeSet_iff {n f : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} :
    IsDegreeInertiaRepresentativeSet n f R ↔
      R ⊆ subextensionsOfDegreeInertia K n f ∧
        ∀ L ∈ subextensionsOfDegreeInertia K n f, ∃! M, M ∈ R ∧ Nonempty (L ≃ₐ[K] M) :=
  Iff.rfl

/-- For residue degree `1`, `IsDegreeInertiaRepresentativeSet n 1 R` is Serre's
`IsRepresentativeSet n R`. -/
@[simp]
theorem isDegreeInertiaRepresentativeSet_one_right {n : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} :
    IsDegreeInertiaRepresentativeSet n 1 R ↔ IsRepresentativeSet n R := by
  rw [isDegreeInertiaRepresentativeSet_iff, isRepresentativeSet_iff,
    subextensionsOfDegreeInertia_one_right]

variable (K) in
/-- Every `subextensionsOfDegreeInertia K n f` admits a set of representatives of its
`K`-isomorphism classes. -/
theorem exists_isDegreeInertiaRepresentativeSet (n f : ℕ) :
    ∃ R : Set (IntermediateField K (SeparableClosure K)),
      IsDegreeInertiaRepresentativeSet n f R :=
  exists_subset_forall_existsUnique_nonempty_algEquiv (subextensionsOfDegreeInertia K n f)

namespace IsDegreeInertiaRepresentativeSet

variable {n f : ℕ} {R : Set (IntermediateField K (SeparableClosure K))}

/-- Every representative set for `subextensionsOfDegreeInertia K n f` is contained in it. -/
theorem subset (hR : IsDegreeInertiaRepresentativeSet n f R) :
    R ⊆ subextensionsOfDegreeInertia K n f :=
  hR.1

/-- Every member of `subextensionsOfDegreeInertia K n f` is `K`-isomorphic to a unique member of a
representative set `R`. -/
theorem existsUnique {L : IntermediateField K (SeparableClosure K)}
    (hR : IsDegreeInertiaRepresentativeSet n f R)
    (hL : L ∈ subextensionsOfDegreeInertia K n f) :
    ∃! M, M ∈ R ∧ Nonempty (L ≃ₐ[K] M) :=
  hR.2 L hL

/-- Regroups a sum over `subextensionsOfDegreeInertia K n f` of a `K`-isomorphism-invariant weight
along `K`-isomorphism classes: when `n ≠ 0` or `f ≠ 0`, every member is finite over `K` and the
class of `M ∈ R` has `n / #Aut_K(M)` members. -/
theorem tsum_eq_tsum_div_natCard_algEquiv_mul
    (hR : IsDegreeInertiaRepresentativeSet n f R) (h : n ≠ 0 ∨ f ≠ 0)
    (w : IntermediateField K (SeparableClosure K) → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K (SeparableClosure K)}, (L ≃ₐ[K] M) → w L = w M) :
    ∑' L : subextensionsOfDegreeInertia K n f, w L =
      ∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) * w M := by
  classical
  let C (M : IntermediateField K (SeparableClosure K)) :
      Set (IntermediateField K (SeparableClosure K)) :=
    {L | L ∈ subextensionsOfDegreeInertia K n f ∧ Nonempty (M ≃ₐ[K] L)}
  have hU : subextensionsOfDegreeInertia K n f = ⋃ M ∈ R, C M := by
    ext L
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨fun hL ↦ ?_, fun ⟨_, _, hL, _⟩ ↦ hL⟩
    obtain ⟨M, ⟨hM, ⟨e⟩⟩, -⟩ := hR.existsUnique hL
    exact ⟨M, hM, hL, ⟨e.symm⟩⟩
  have hdisj : R.PairwiseDisjoint C := by
    rintro M hM M' hM' hne
    refine Set.disjoint_left.2 ?_
    rintro L ⟨hL, ⟨e⟩⟩ ⟨-, ⟨e'⟩⟩
    obtain ⟨_, -, huniq⟩ := hR.existsUnique hL
    exact hne ((huniq M ⟨hM, ⟨e.symm⟩⟩).trans (huniq M' ⟨hM', ⟨e'.symm⟩⟩).symm)
  rw [hU, tsum_biUnion hdisj]
  refine tsum_congr fun M ↦ ?_
  have hM := hR.subset M.2
  have := finite_of_mem_subextensionsOfDegreeInertia hM h
  have hcard := ncard_isomorphic_mul_natCard_algEquiv_of_mem_subextensionsOfDegreeInertia hM h
  have hAut : Nat.card (M ≃ₐ[K] M) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨.refl⟩, inferInstance⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Module.finrank_pos.ne' hM.1
  have hfin : (C M).Finite := Set.finite_of_ncard_ne_zero fun hncard ↦
    hn0 (hcard ▸ mul_eq_zero_of_left hncard _)
  rw [tsum_congr fun L : C M ↦ hw (Classical.choice L.2.2).symm, ENNReal.tsum_set_const,
    ← hfin.cast_ncard_eq]
  congr 1
  exact (ENNReal.eq_div_iff (by exact_mod_cast hAut) (ENNReal.natCast_ne_top _)).2
    (by exact_mod_cast (mul_comm _ _).trans hcard)

/-- Relates the discriminant-weighted class sum over `R` to the subextension sum over
`subextensionsOfDegreeInertia K n f`:
`n · ∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ d(M / K)) = ∑_L q ^ (-d(L / K))`. -/
theorem mul_tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent
    (hR : IsDegreeInertiaRepresentativeSet n f R) (h : n ≠ 0 ∨ f ≠ 0) :
    (n : ℝ≥0∞) * ∑' M : R, 1 / ((Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) *
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.discriminantExponent) =
      ∑' L : subextensionsOfDegreeInertia K n f,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent := by
  rw [hR.tsum_eq_tsum_div_natCard_algEquiv_mul h
    (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent) fun e ↦ by
      rw [IntermediateField.discriminantExponent_eq_of_algEquiv e], ← ENNReal.tsum_mul_left]
  refine tsum_congr fun M ↦ ?_
  rw [one_div, ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
    (.inl (ENNReal.natCast_ne_top _)), ← mul_assoc]
  simp only [div_eq_mul_inv, one_mul]

/-- **Refined Serre mass formula over `K`-isomorphism classes by residue degree**: for `f ≠ 0`,
`e ≠ 0`, and any representative set `R` of the `K`-isomorphism classes of extensions of degree
`f * e` and residue degree `f`,
`∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ d(M / K)) = 1 / (f · q ^ (f(e - 1)))`. -/
theorem tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent
    {e : ℕ} (hR : IsDegreeInertiaRepresentativeSet (f * e) f R) (hf : f ≠ 0) (he : e ≠ 0) :
    ∑' M : R, 1 / ((Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) *
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.discriminantExponent) =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  have hfe : f * e ≠ 0 := mul_ne_zero hf he
  apply (ENNReal.mul_right_inj (a := ((f * e : ℕ) : ℝ≥0∞)) (by exact_mod_cast hfe)
    (ENNReal.natCast_ne_top _)).1
  have htsum : (∑' L : subextensionsOfDegreeInertia K (f * e) f,
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent) =
      e / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) :=
    tsum_inertiaDegree_eq hf e
  rw [hR.mul_tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_discriminantExponent
    (.inr hf), htsum]
  set P : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))
  have hf0 : (f : ℝ≥0∞) ≠ 0 := by exact_mod_cast hf
  have hftop : (f : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top f
  have hPtop : P ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [Nat.cast_mul, mul_comm (f : ℝ≥0∞) (e : ℝ≥0∞), one_div,
    ENNReal.mul_inv (.inr hPtop) (.inl hftop), ← mul_assoc, mul_assoc (e : ℝ≥0∞),
    ENNReal.mul_inv_cancel hf0 hftop, mul_one, div_eq_mul_inv]

end IsDegreeInertiaRepresentativeSet

end Carrier

/-! ### Subfield factorization and class-sum reduction over `K_f` -/

section UnramifiedExtensionBase

private theorem finrank_restrictScalars_eq_mul (F : Type*) {L' L : Type*} [Field F] [Field L']
    [Field L] [Algebra F L'] [Algebra F L] [Algebra L' L] [IsScalarTower F L' L]
    (E : IntermediateField L' L) :
    Module.finrank F (E.restrictScalars F) = Module.finrank F L' * Module.finrank L' E := by
  rw [(restrictScalarsAlgEquiv F E).toLinearEquiv.finrank_eq, ← Module.finrank_mul_finrank F L' E]

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every subextension of `SeparableClosure K` with positive residue degree `f` contains the
canonical unramified extension `unramifiedExtension K (SeparableClosure K) f`. -/
theorem unramifiedExtension_le_of_mem_subextensionsOfDegreeInertia {n f : ℕ} (hf : f ≠ 0)
    {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ subextensionsOfDegreeInertia K n f) :
    unramifiedExtension K (SeparableClosure K) f ≤ L := by
  have : Module.Finite K L := finite_of_mem_subextensionsOfDegreeInertia hL (.inr hf)
  simpa [hL.2] using L.unramifiedExtension_inertiaDegree_le

/-- For `f ≠ 0`, an intermediate field `E` of `SeparableClosure K` over
`unramifiedExtension K (SeparableClosure K) f` restricts to
`subextensionsOfDegreeInertia K (f * e) f` if and only if `[E : K_f] = e` and
`(E.restrictScalars K).inertiaDegree = f`. -/
theorem restrictScalars_mem_subextensionsOfDegreeInertia_iff {f e : ℕ} (hf : f ≠ 0)
    (E : IntermediateField (unramifiedExtension K (SeparableClosure K) f) (SeparableClosure K)) :
    E.restrictScalars K ∈ subextensionsOfDegreeInertia K (f * e) f ↔
      Module.finrank (unramifiedExtension K (SeparableClosure K) f) E = e ∧
        (E.restrictScalars K).inertiaDegree = f := by
  have hrank : Module.finrank K (E.restrictScalars K) =
      f * Module.finrank (unramifiedExtension K (SeparableClosure K) f) E := by
    rw [finrank_restrictScalars_eq_mul K E, finrank_unramifiedExtension hf]
  rw [mem_subextensionsOfDegreeInertia_iff, hrank]
  exact and_congr_left' ⟨Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf), congrArg (f * ·)⟩

variable (K) in
/-- **Subfield characterization over `K_f`**: for `f ≠ 0`,
`subextensionsOfDegreeInertia K (f * e) f` corresponds bijectively via `extendScalars` and
`restrictScalars` to the intermediate fields of `SeparableClosure K` over
`K_f = unramifiedExtension K (SeparableClosure K) f` having degree `e` over `K_f` and residue
degree `f` over `K`. -/
def subextensionsOfDegreeInertiaEquiv {f : ℕ} (hf : f ≠ 0) (e : ℕ) :
    subextensionsOfDegreeInertia K (f * e) f ≃
      {E : IntermediateField (unramifiedExtension K (SeparableClosure K) f) (SeparableClosure K) |
        Module.finrank (unramifiedExtension K (SeparableClosure K) f) E = e ∧
          (E.restrictScalars K).inertiaDegree = f} where
  toFun L := ⟨extendScalars (unramifiedExtension_le_of_mem_subextensionsOfDegreeInertia hf L.2), by
    rw [Set.mem_ofPred_eq, ← restrictScalars_mem_subextensionsOfDegreeInertia_iff hf,
      extendScalars_restrictScalars]
    exact L.2⟩
  invFun E := ⟨E.1.restrictScalars K,
    (restrictScalars_mem_subextensionsOfDegreeInertia_iff hf E.1).2 E.2⟩
  left_inv L := Subtype.ext <| extendScalars_restrictScalars
    (unramifiedExtension_le_of_mem_subextensionsOfDegreeInertia hf L.2)
  right_inv E := Subtype.ext <| extendScalars_of_restrictScalars E.1
    (h := unramifiedExtension_le_of_mem_subextensionsOfDegreeInertia hf
      ((restrictScalars_mem_subextensionsOfDegreeInertia_iff hf E.1).2 E.2))

/-- Applying `subextensionsOfDegreeInertiaEquiv` extends scalars of `L` to
`unramifiedExtension K (SeparableClosure K) f`. -/
@[simp]
theorem coe_subextensionsOfDegreeInertiaEquiv_apply {f : ℕ} (hf : f ≠ 0) (e : ℕ)
    (L : subextensionsOfDegreeInertia K (f * e) f) :
    (subextensionsOfDegreeInertiaEquiv K hf e L :
        IntermediateField (unramifiedExtension K (SeparableClosure K) f) (SeparableClosure K)) =
      extendScalars (unramifiedExtension_le_of_mem_subextensionsOfDegreeInertia hf L.2) :=
  (rfl)

/-- Applying `(subextensionsOfDegreeInertiaEquiv K hf e).symm` restricts scalars down to `K`. -/
@[simp]
theorem coe_subextensionsOfDegreeInertiaEquiv_symm_apply {f : ℕ} (hf : f ≠ 0) (e : ℕ)
    (E : {E : IntermediateField (unramifiedExtension K (SeparableClosure K) f)
        (SeparableClosure K) |
      Module.finrank (unramifiedExtension K (SeparableClosure K) f) E = e ∧
        (E.restrictScalars K).inertiaDegree = f}) :
    ((subextensionsOfDegreeInertiaEquiv K hf e).symm E :
        IntermediateField K (SeparableClosure K)) =
      E.1.restrictScalars K :=
  (rfl)

private theorem mapNormalBase_restrictScalars_mem_subextensionsOfDegreeInertia {n f : ℕ}
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    {E : IntermediateField (unramifiedExtension K (SeparableClosure K) f) (SeparableClosure K)}
    (hE : E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f) :
    (mapNormalBase (σ : SeparableClosure K →ₐ[K] SeparableClosure K) E).restrictScalars K ∈
      subextensionsOfDegreeInertia K n f := by
  rw [mapNormalBase_restrictScalars, map_mem_subextensionsOfDegreeInertia_iff]
  exact hE

/-- **Orbit count on `K_f`-isomorphism classes under `Gal(K_f / K)`**: for `f ≠ 0`, let `R_U` be a
set of `K_f`-isomorphism representatives for the intermediate fields of `SeparableClosure K / K_f`
whose scalar restriction lies in `subextensionsOfDegreeInertia K n f`. For any `M ∈ R_U`, the number
of `M' ∈ R_U` with `M.restrictScalars K ≃ₐ[K] M'.restrictScalars K`, multiplied by the number of
automorphisms of `K_f / K` extending to `M.restrictScalars K`, equals `f`. -/
theorem ncard_isomorphic_restrictScalars_unramifiedExtension_mul_natCard {n f : ℕ} (hf : f ≠ 0)
    {R_U : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K))}
    (hRS : ∀ E ∈ R_U, E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f)
    (hR_U : ∀ E : IntermediateField (unramifiedExtension K (SeparableClosure K) f)
        (SeparableClosure K),
      E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f →
        ∃! M, M ∈ R_U ∧ Nonempty (E ≃ₐ[unramifiedExtension K (SeparableClosure K) f] M))
    {M : IntermediateField (unramifiedExtension K (SeparableClosure K) f) (SeparableClosure K)}
    (hM : M ∈ R_U) :
    {M' ∈ R_U | Nonempty (M.restrictScalars K ≃ₐ[K] M'.restrictScalars K)}.ncard *
      Nat.card {τ : unramifiedExtension K (SeparableClosure K) f ≃ₐ[K]
          unramifiedExtension K (SeparableClosure K) f //
        ∃ σ : M.restrictScalars K ≃ₐ[K] M.restrictScalars K,
          ∀ x, (σ ⟨x.1, le_restrictScalars M x.2⟩ : SeparableClosure K) = τ x} = f := by
  let S : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K)) :=
    {E | E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f}
  have hcard := IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard_eq_finrank
    (S := S)
    (fun σ _ hE ↦ mapNormalBase_restrictScalars_mem_subextensionsOfDegreeInertia σ hE)
    hRS hR_U hM
  rwa [finrank_unramifiedExtension hf] at hcard

/-- **Weighted `1 / #Aut` class-sum reduction over `K_f`**: for `f ≠ 0`, any `K_f`-isomorphism
representative set `R_U` of `{E : IntermediateField K_f (SeparableClosure K) |
E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f}`, any `K`-isomorphism representative set
`R` of `subextensionsOfDegreeInertia K n f`, and any `K`-isomorphism-invariant weight `w`,
`∑_{N ∈ R} w(N) / #Aut_K(N) = f⁻¹ · ∑_{M ∈ R_U} w(M.restrictScalars K) / #Aut_{K_f}(M)`. -/
theorem tsum_div_natCard_algEquiv_unramifiedExtension {n f : ℕ} (hf : f ≠ 0)
    {R_U : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K))}
    {R : Set (IntermediateField K (SeparableClosure K))}
    (hRS : ∀ E ∈ R_U, E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f)
    (hR_U : ∀ E : IntermediateField (unramifiedExtension K (SeparableClosure K) f)
        (SeparableClosure K),
      E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f →
        ∃! M, M ∈ R_U ∧ Nonempty (E ≃ₐ[unramifiedExtension K (SeparableClosure K) f] M))
    (hR : IsDegreeInertiaRepresentativeSet n f R)
    (w : IntermediateField K (SeparableClosure K) → ℝ≥0∞)
    (hw : ∀ {L₁ L₂ : IntermediateField K (SeparableClosure K)}, (L₁ ≃ₐ[K] L₂) → w L₁ = w L₂) :
    ∑' N : R, w N.1 / (Nat.card (N.1 ≃ₐ[K] N.1) : ℝ≥0∞) =
      (f : ℝ≥0∞)⁻¹ *
        ∑' M : R_U,
          w (M.1.restrictScalars K) /
            (Nat.card (M.1 ≃ₐ[unramifiedExtension K (SeparableClosure K) f] M.1) : ℝ≥0∞) := by
  let S : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K)) :=
    {E | E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f}
  have hST : IntermediateField.restrictScalars K '' S = subextensionsOfDegreeInertia K n f := by
    ext L
    simp only [Set.mem_image, Set.mem_ofPred_eq, S]
    refine ⟨?_, fun hL ↦ ⟨extendScalars
      (unramifiedExtension_le_of_mem_subextensionsOfDegreeInertia hf hL), ?_,
      extendScalars_restrictScalars _⟩⟩
    · rintro ⟨E, hE, rfl⟩
      exact hE
    · rwa [extendScalars_restrictScalars]
  have hsum := IntermediateField.tsum_div_natCard_algEquiv_eq_inv_finrank_mul_tsum
    (S := S)
    (fun σ _ hE ↦ mapNormalBase_restrictScalars_mem_subextensionsOfDegreeInertia σ hE)
    hRS hR_U hST hR.subset hR.2 w hw
  rwa [finrank_unramifiedExtension hf] at hsum

/-- **Unweighted `1 / #Aut` class-sum reduction over `K_f`**:
`∑_{N ∈ R} 1 / #Aut_K(N) = f⁻¹ · ∑_{M ∈ R_U} 1 / #Aut_{K_f}(M)`. -/
theorem tsum_one_div_natCard_algEquiv_unramifiedExtension {n f : ℕ} (hf : f ≠ 0)
    {R_U : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) f)
      (SeparableClosure K))}
    {R : Set (IntermediateField K (SeparableClosure K))}
    (hRS : ∀ E ∈ R_U, E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f)
    (hR_U : ∀ E : IntermediateField (unramifiedExtension K (SeparableClosure K) f)
        (SeparableClosure K),
      E.restrictScalars K ∈ subextensionsOfDegreeInertia K n f →
        ∃! M, M ∈ R_U ∧ Nonempty (E ≃ₐ[unramifiedExtension K (SeparableClosure K) f] M))
    (hR : IsDegreeInertiaRepresentativeSet n f R) :
    ∑' N : R, 1 / (Nat.card (N.1 ≃ₐ[K] N.1) : ℝ≥0∞) =
      (f : ℝ≥0∞)⁻¹ *
        ∑' M : R_U,
          1 / (Nat.card (M.1 ≃ₐ[unramifiedExtension K (SeparableClosure K) f] M.1) : ℝ≥0∞) :=
  tsum_div_natCard_algEquiv_unramifiedExtension hf hRS hR_U hR (fun _ ↦ 1) (fun _ ↦ rfl)

end UnramifiedExtensionBase

/-! ### Transport to `totallyRamifiedOfDegree F e` over an unramified local field `F` -/

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [IsUnramified K F] [Algebra F (SeparableClosure K)]
  [IsScalarTower K F (SeparableClosure K)] (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)

/-- Transport along `Φ.symm : SeparableClosure K ≃ₐ[F] SeparableClosure F` identifies the
intermediate fields `E` of `SeparableClosure K / F` with
`E.restrictScalars K ∈ subextensionsOfDegreeInertia K (f(F / K) * e) (f(F / K))` and the totally
ramified subextensions `totallyRamifiedOfDegree F e`. -/
def restrictScalarsEquivTotallyRamifiedOfDegree (e : ℕ) :
    {E : IntermediateField F (SeparableClosure K) |
      E.restrictScalars K ∈
        subextensionsOfDegreeInertia K (inertiaDegree K F * e) (inertiaDegree K F)} ≃
      totallyRamifiedOfDegree F e where
  toFun E := ⟨E.1.map Φ.symm.toAlgHom, by
    have : Module.Finite K F := finite_of_valuativeExtension K F
    rw [map_mem_totallyRamifiedOfDegree_iff F Φ E.1 e,
      (IsUnramified.inertiaDegree_eq_finrank (K := K) (L := F)).symm]
    exact E.2⟩
  invFun M := ⟨M.1.map Φ.toAlgHom, by
    have : Module.Finite K F := finite_of_valuativeExtension K F
    have hmap : (M.1.map Φ.toAlgHom).map Φ.symm.toAlgHom = M.1 := by
      simp [IntermediateField.map_map, IntermediateField.map_id]
    have hmem := (map_mem_totallyRamifiedOfDegree_iff F Φ (M.1.map Φ.toAlgHom) e).1
      (hmap.symm ▸ M.2)
    rw [Set.mem_ofPred_eq, mem_subextensionsOfDegreeInertia_iff]
    rwa [← IsUnramified.inertiaDegree_eq_finrank (K := K) (L := F)] at hmem⟩
  left_inv E := Subtype.ext <| by
    simp [IntermediateField.map_map, IntermediateField.map_id]
  right_inv M := Subtype.ext <| by
    simp [IntermediateField.map_map, IntermediateField.map_id]

@[simp]
theorem coe_restrictScalarsEquivTotallyRamifiedOfDegree_apply (e : ℕ)
    (E : {E : IntermediateField F (SeparableClosure K) |
      E.restrictScalars K ∈
        subextensionsOfDegreeInertia K (inertiaDegree K F * e) (inertiaDegree K F)}) :
    (restrictScalarsEquivTotallyRamifiedOfDegree F Φ e E :
        IntermediateField F (SeparableClosure F)) =
      E.1.map Φ.symm.toAlgHom :=
  (rfl)

@[simp]
theorem coe_restrictScalarsEquivTotallyRamifiedOfDegree_symm_apply (e : ℕ)
    (M : totallyRamifiedOfDegree F e) :
    ((restrictScalarsEquivTotallyRamifiedOfDegree F Φ e).symm M :
        IntermediateField F (SeparableClosure K)) =
      M.1.map Φ.toAlgHom :=
  (rfl)

end Transport

end TauCeti

end
