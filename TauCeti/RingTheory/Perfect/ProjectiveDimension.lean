/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import TauCeti.Algebra.Category.ModuleCat.Projective.SequentialColimit
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Tor
import TauCeti.RingTheory.RegularLocalRing.Frobenius

/-!
# Projective dimension over the perfection of a ring with flat Frobenius

Let `K` be a ring of exponential characteristic `p` whose Frobenius endomorphism is flat, and
suppose that every `K`-module has projective dimension at most `d`. Then every module over a
perfect closure `i : K →+* L`, for instance Mathlib's colimit perfection `PerfectClosure K p`, has
projective dimension at most `d + 1`. By Kunz's theorem this applies to a regular ring `K` of
Krull dimension at most `d`, whose Frobenius is flat and whose modules have projective dimension
at most `d`: the perfection of a regular ring of finite Krull dimension has finite global
dimension.

The perfect closure `L` is the union of the increasing sequence of subrings `i(K) ^ (1 / p ^ n)`,
the images of `x ↦ i(x) ^ (1 / p ^ n)`. Each of them is isomorphic to `K` because `i` is
injective: its kernel is the `p`-nilradical of `K`, which vanishes because flat Frobenius is
injective. The perfect closure is flat over each of them because it is flat over `K`
(`RingHom.Flat.of_isPerfectClosure`). Every module over `L` is then the colimit of its base
changes from these subrings, which have projective dimension at most `d`, and the telescope
sequence adds one (`ModuleCat.hasProjectiveDimensionLT_succ_of_iSup_eq_top`).

When `p` is prime and `g : A →+* B` is a surjection from a perfect ring `A` onto a reduced ring `B`
(in particular any perfect ring of characteristic `p`), `Tor_{n+1}^A(B, M) = 0` for every
`B`-module `M` (`TauCeti.isZero_Tor_succ_restrictScalars_of_surjective`), so `B ⊗[A] —` sends a
projective resolution of `M` over `A` of length `d` to a projective resolution of `M` over `B` of
length `d` (`TauCeti.hasProjectiveDimensionLE_of_surjective_of_perfectRing`). Applied to a
surjection from a perfect closure of `K`, this bounds the global dimension of any reduced quotient
of `L` by `d + 1`, and in particular bounds the global dimension of any perfectly finitely
presented algebra over the perfection of a regular ring `K` of Krull dimension at most `d` in `n`
perfect variables by `d + n + 1` (Bhatt and Scholze, Proposition 11.31 and Remark 11.32).

## Main results

* `IsPerfectClosure.hasProjectiveDimensionLE_succ`: if Frobenius of `K` is flat and every
  `K`-module has projective dimension at most `d`, then every module over a perfect closure of
  `K` has projective dimension at most `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing`: over a perfect closure of a
  regular ring of Krull dimension at most `d`, every module has projective dimension at most
  `d + 1`.
* `TauCeti.hasProjectiveDimensionLE_of_surjective_of_perfectRing`: along a surjection `g : A →+* B`
  from a perfect ring of prime characteristic onto a reduced ring, `pd_B M ≤ d` whenever
  `pd_A M ≤ d`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_surjective` and
  `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`: every module
  over a reduced quotient of a perfect closure of a ring of prime characteristic with flat
  Frobenius and global dimension at most `d` (in particular a regular ring of Krull dimension at
  most `d`) has projective dimension at most `d + 1`.
* `TauCeti.hasProjectiveDimensionLE_of_surjective_isPerfectClosure_mvPolynomial` and
  `TauCeti.hasProjectiveDimensionLE_of_surjective_perfectClosure_mvPolynomial`: every module over a
  reduced quotient of a perfect closure of `MvPolynomial σ K` for a regular ring `K` of prime
  characteristic `p` and Krull dimension at most `d` and finite `σ` has projective dimension at
  most `d + Nat.card σ + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Proposition 11.31, Remark 11.32, and their proofs.
* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

/-- **Projective dimension along a surjection from a perfect ring onto a reduced ring.** Let `A` be
a perfect ring of prime characteristic `p`, `B` a reduced ring (in particular any perfect ring of
characteristic `p`), and `g : A →+* B` a surjective ring homomorphism. Because
`Tor_{n+1}^A(B, M) = 0` for every `B`-module `M` and `n ≥ 0`, extending scalars along `g` carries
a projective resolution of `M` over `A` to a projective resolution of `M` over `B`, so
`pd_B M ≤ d` whenever `pd_A M ≤ d`. -/
theorem hasProjectiveDimensionLE_of_surjective_of_perfectRing {A B : Type u} [CommRing A]
    [CommRing B] [IsReduced B] {p : ℕ} [ExpChar A p] [PerfectRing A p] [Fact p.Prime]
    {g : A →+* B} (hg : Function.Surjective g) (M : ModuleCat.{u} B) (d : ℕ)
    [HasProjectiveDimensionLE ((ModuleCat.restrictScalars g).obj M) d] :
    HasProjectiveDimensionLE M d :=
  ModuleCat.hasProjectiveDimensionLE_of_surjective_of_isZero_Tor hg M d fun n _ ↦
    isZero_Tor_succ_restrictScalars_of_surjective (p := p) hg M n

end TauCeti

namespace IsPerfectClosure

variable {K L : Type u} [CommRing K] [CommRing L] (i : K →+* L) (p : ℕ) [ExpChar L p]
  [PerfectRing L p]

/-- The `n`-th stage `x ↦ i(x) ^ (1 / p ^ n)` of the perfect closure `i`. -/
private noncomputable def stage (n : ℕ) : K →+* L :=
  (iterateFrobeniusEquiv L p n).symm.toRingHom.comp i

/-- The images of the stages increase: `i(x) ^ (1 / p ^ n) = i(x ^ p) ^ (1 / p ^ (n + 1))`. -/
private theorem monotone_range_stage : Monotone fun n ↦ (stage i p n).range :=
  monotone_nat_of_le_succ fun n ↦ by
    rintro _ ⟨x, rfl⟩
    refine ⟨x ^ p, (iterateFrobeniusEquiv L p (n + 1)).injective ?_⟩
    simp only [stage, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply, map_pow]
    rw [add_comm n 1, iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply,
      iterateFrobeniusEquiv_one_apply]

variable [IsPerfectClosure i p]

/-- Every element of a perfect closure is `i(x) ^ (1 / p ^ n)` for some `x` and `n`. -/
private theorem iSup_range_stage : ⨆ n, (stage i p n).range = ⊤ :=
  eq_top_iff.2 fun x _ ↦ by
    obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem i p x
    refine le_iSup (fun n ↦ (stage i p n).range) n ⟨y, ?_⟩
    rw [stage, RingHom.comp_apply, hy, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_eq, iterateFrobeniusEquiv_def]

variable [ExpChar K p]

/-- The stages are injective when Frobenius is flat: the kernel of `i` is the `p`-nilradical,
which vanishes because flat Frobenius is injective. -/
private theorem stage_injective (hF : (frobenius K p).Flat) (n : ℕ) :
    Function.Injective (stage i p n) :=
  (iterateFrobeniusEquiv L p n).symm.injective.comp (injective_of_flat_frobenius i p hF)

/-- When Frobenius is flat, the `n`-th stage identifies `K` with its image. -/
private noncomputable def stageEquiv (hF : (frobenius K p).Flat) (n : ℕ) :
    K ≃+* (stage i p n).range :=
  RingEquiv.ofBijective (stage i p n).rangeRestrict
    ⟨fun _ _ h ↦ stage_injective i p hF n congr($h.1), (stage i p n).rangeRestrict_surjective⟩

/-- A perfect closure is flat over the image of each stage. -/
private theorem flat_range_stage (hF : (frobenius K p).Flat) (n : ℕ) :
    Module.Flat (stage i p n).range L := by
  rw [← RingHom.flat_algebraMap_iff, ← RingHom.Flat.comp_iff_of_bijective_right
    (g := (stage i p n).rangeRestrict) (stageEquiv i p hF n).bijective]
  have hσ : (iterateFrobeniusEquiv L p n).symm.toRingHom.Flat :=
    .of_bijective (RingEquiv.bijective _)
  exact (RingHom.Flat.of_isPerfectClosure i p hF).comp hσ

include i in
/-- If the Frobenius endomorphism of `K` is flat and every `K`-module has projective dimension at
most `d`, then every module over a perfect closure `i : K →+* L` has projective dimension at most
`d + 1`. -/
theorem hasProjectiveDimensionLE_succ (hF : (frobenius K p).Flat) {d : ℕ}
    (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d) (M : ModuleCat.{u} L) :
    HasProjectiveDimensionLE M (d + 1) := by
  have := flat_range_stage i p hF
  refine ModuleCat.hasProjectiveDimensionLT_succ_of_iSup_eq_top (monotone_range_stage i p)
    (iSup_range_stage i p) M fun n ↦ ?_
  -- A module over the `n`-th stage is a `K`-module along `stageEquiv`, with the same projective
  -- dimension.
  let e := stageEquiv i p hF n
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : K →+* (stage i p n).range) e.symm
  let N := ModuleCat.of (stage i p n).range M
  have := h ((ModuleCat.restrictScalars (e : K →+* (stage i p n).range)).obj N)
  let e' : (ModuleCat.restrictScalars (e : K →+* (stage i p n).range)).obj N
      ≃ₛₗ[(e : K →+* (stage i p n).range)] N :=
    { (e : K →+* (stage i p n).range).restrictScalarsSemilinearMap N with
      invFun := fun m ↦ m
      left_inv := RingHom.restrictScalarsSemilinearMap_apply _ N
      right_inv := RingHom.restrictScalarsSemilinearMap_apply _ N }
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e e' d

include i p in
/-- Over a perfect closure of a regular ring of Krull dimension at most `d`, every module has
projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) (M : ModuleCat.{u} L) : HasProjectiveDimensionLE M (d + 1) :=
  hasProjectiveDimensionLE_succ i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) M

include i in
/-- **Global dimension of reduced quotients of a perfect closure.** Let `i : K →+* L` be a perfect
closure in prime characteristic `p` such that `(frobenius K p).Flat` and every `K`-module has
projective dimension at most `d`. For any surjective ring homomorphism `g : L →+* B` onto a reduced
ring `B` (in particular any perfect ring of characteristic `p`), every `B`-module has projective
dimension at most `d + 1` (Bhatt and Scholze, Remark 11.32). -/
theorem hasProjectiveDimensionLE_succ_of_surjective [Fact p.Prime] {B : Type u} [CommRing B]
    [IsReduced B] (hF : (frobenius K p).Flat) {d : ℕ}
    (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d) {g : L →+* B}
    (hg : Function.Surjective g) (M : ModuleCat.{u} B) :
    HasProjectiveDimensionLE M (d + 1) := by
  have := hasProjectiveDimensionLE_succ i p hF h ((ModuleCat.restrictScalars g).obj M)
  exact TauCeti.hasProjectiveDimensionLE_of_surjective_of_perfectRing (p := p) hg M (d + 1)

include i p in
/-- Over any reduced quotient of a perfect closure of a regular ring of prime characteristic `p` and
Krull dimension at most `d`, every module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective [Fact p.Prime]
    [IsRegularRing K] {B : Type u} [CommRing B] [IsReduced B] {d : ℕ} (hd : ringKrullDim K ≤ d)
    {g : L →+* B} (hg : Function.Surjective g) (M : ModuleCat.{u} B) :
    HasProjectiveDimensionLE M (d + 1) :=
  hasProjectiveDimensionLE_succ_of_surjective i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) hg M

end IsPerfectClosure

namespace TauCeti

/-- **Global dimension of perfectly finitely presented algebras over the perfection of a regular
ring (Bhatt–Scholze, Proposition 11.31).** Let `K` be a regular ring of prime characteristic `p`
and Krull dimension at most `d`, let `σ` be a finite indexing type, and let `g` be a surjective
ring homomorphism from a perfect closure `L` of `MvPolynomial σ K` onto a reduced ring `B` (in
particular any perfect ring of characteristic `p`). Then every `B`-module has projective dimension
at most `d + Nat.card σ + 1`. -/
theorem hasProjectiveDimensionLE_of_surjective_isPerfectClosure_mvPolynomial
    {K : Type u} {σ : Type v} {L B : Type (max u v)} [CommRing K] [CommRing L] [CommRing B]
    [Finite σ] [IsReduced B] (i : MvPolynomial σ K →+* L) (p : ℕ) [Fact p.Prime] [ExpChar K p]
    [ExpChar L p] [PerfectRing L p] [IsPerfectClosure i p] [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) {g : L →+* B} (hg : Function.Surjective g)
    (M : ModuleCat.{max u v} B) :
    HasProjectiveDimensionLE M (d + Nat.card σ + 1) := by
  have hd' : ringKrullDim (MvPolynomial σ K) ≤ (d + Nat.card σ : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.cast_add]
    gcongr
  exact IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective i p hd' hg M

/-- Specialization of `TauCeti.hasProjectiveDimensionLE_of_surjective_isPerfectClosure_mvPolynomial`
to the colimit perfection `PerfectClosure (MvPolynomial σ K) p`. -/
theorem hasProjectiveDimensionLE_of_surjective_perfectClosure_mvPolynomial
    {K : Type u} {σ : Type v} {B : Type (max u v)} [CommRing K] [CommRing B] [Finite σ]
    [IsReduced B] (p : ℕ) [hp : Fact p.Prime] [CharP K p] [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) {g : PerfectClosure (MvPolynomial σ K) p →+* B}
    (hg : Function.Surjective g) (M : ModuleCat.{max u v} B) :
    HasProjectiveDimensionLE M (d + Nat.card σ + 1) := by
  have : ExpChar K p := .prime hp.out
  have : ExpChar (PerfectClosure (MvPolynomial σ K) p) p := .prime hp.out
  exact hasProjectiveDimensionLE_of_surjective_isPerfectClosure_mvPolynomial
    (PerfectClosure.of (MvPolynomial σ K) p) p hd hg M

end TauCeti
