/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.RingTheory.Dagger.WeakCompletion.Aeval
public import TauCeti.RingTheory.Dagger.WeakCompletion.Jacobson
public import TauCeti.RingTheory.Dagger.WeakCompletion.Presentation
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.Nilpotent
import TauCeti.RingTheory.AdicCompletion.Nilpotent
import TauCeti.RingTheory.Ideal.Maps

/-!
# The universal property of the Monsky–Washnitzer weak completion

Let `O` be a commutative ring and `π : O` a parameter. Monsky and Washnitzer (§1–§2) study two
classes of `O`-algebras in which overconvergent power series in `π` can be evaluated:

1. An `O`-algebra `B` is *weakly complete* with respect to `π` (`IsWeaklyComplete π B`,
   Monsky–Washnitzer §1, Definition 1.1) if `B` is `π`-adically separated and every finite tuple
   `b : Fin m → B` extends along `O[X₁, …, Xₘ] → (O[X₁, …, Xₘ])†` to an `O`-algebra homomorphism
   `(O[X₁, …, Xₘ])† →ₐ[O] B`. Without any noetherianity, valuation, or completeness assumption,
   every weak completion `S†` of a finitely generated `O`-algebra `S` is weakly complete
   (`weakCompletion.isWeaklyComplete`) and `of π S : S →ₐ[O] S†` is initial among `O`-algebra
   homomorphisms from `S` into weakly complete `O`-algebras
   (`weakCompletion.existsUnique_lift_of_isWeaklyComplete`,
   `weakCompletion.liftEquivOfIsWeaklyComplete`).
2. An `O`-algebra `B` is *weakly complete and finitely generated* (w.c.f.g.,
   `IsWeaklyCompleteFG π B`, Monsky–Washnitzer §2; van der Put §2, (2.1)) if `B` is isomorphic as
   an `O`-algebra to `(O[X₁, …, Xₘ])† ⧸ J` for some `m : ℕ` and ideal `J`. Every w.c.f.g. algebra
   has `π` in its Jacobson radical (`IsWeaklyCompleteFG.algebraMap_mem_jacobson`) and admits
   overconvergent polynomial evaluations (`IsWeaklyCompleteFG.exists_lift_mvPolynomial`). Whenever
   `B` is `π`-adically separated — in particular whenever `B` is noetherian (by Krull's
   intersection theorem), and hence whenever all `(O[X₁, …, Xₘ])†` are noetherian — `B` is weakly
   complete (`IsWeaklyCompleteFG.isWeaklyComplete`) and receives a unique extension along
   `S → S†` of every `O`-algebra homomorphism `S →ₐ[O] B` (`weakCompletion.existsUnique_lift`,
   `weakCompletion.liftEquiv`).

Over the closed unit ball `O = K°` of a complete ultrametric field `K` with a nonzero topologically
nilpotent parameter `π ∈ O`, `IsWeaklyCompleteFG π B` is equivalent to being a quotient of an
integral Monsky–Washnitzer algebra `K°⟨X₁, …, Xₘ⟩†`
(`isWeaklyCompleteFG_iff_exists_intWashnitzerAlgebra`), `O` itself is w.c.f.g. if and only if
`‖(π : K)‖ < 1` (`isWeaklyCompleteFG_unitClosedBall_iff`), `O ⧸ (π)` is w.c.f.g. yet not flat over
`O` (`not_flat_quotient_span_unitClosedBall`), and positive-dimensional polynomial algebras over `O`
are neither weakly complete nor w.c.f.g. (`not_isWeaklyComplete_mvPolynomial_unitClosedBall`,
`not_isWeaklyCompleteFG_mvPolynomial_unitClosedBall`).

## Main definitions and results

* `TauCeti.Dagger.IsWeaklyComplete`: weakly complete `O`-algebras (Monsky–Washnitzer §1, Def. 1.1).
* `TauCeti.Dagger.IsWeaklyCompleteFG`: weakly complete finitely generated `O`-algebras (van der Put
  §2, (2.1)).
* `TauCeti.Dagger.weakCompletion.isWeaklyComplete` and
  `TauCeti.Dagger.weakCompletion.isWeaklyCompleteFG`: `S†` is both weakly complete and w.c.f.g. for
  every finitely generated `O`-algebra `S`.
* `TauCeti.Dagger.weakCompletion.existsUnique_lift_of_isWeaklyComplete` and
  `TauCeti.Dagger.weakCompletion.liftEquivOfIsWeaklyComplete`: universal property of `S → S†` with
  respect to arbitrary weakly complete `O`-algebras, without noetherianity.
* `TauCeti.Dagger.IsWeaklyCompleteFG.isWeaklyComplete_of_isNoetherianRing`,
  `TauCeti.Dagger.IsWeaklyCompleteFG.isWeaklyComplete`,
  `TauCeti.Dagger.weakCompletion.existsUnique_lift`, and
  `TauCeti.Dagger.weakCompletion.liftEquiv`: universal property of `S → S†` with respect to
  w.c.f.g. `O`-algebras.
* `TauCeti.Dagger.isWeaklyCompleteFG_iff_exists_intWashnitzerAlgebra`,
  `TauCeti.Dagger.isWeaklyCompleteFG_unitClosedBall_iff`, and
  `TauCeti.Dagger.weakCompletion.aevalIntWashnitzerAlgebra`: specialization to `O = K°` of a
  complete ultrametric field `K`.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §1–§2, Theorem 2.1.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2, (2.1)–(2.2).
-/

public section

namespace TauCeti.Dagger

open MvPolynomial

section General

variable {O : Type*} [CommRing O]

/-- An `O`-algebra `B` is *weakly complete* with respect to `π : O` (Monsky–Washnitzer §1,
Definition 1.1) if `B` is `π`-adically separated and every finite tuple `b : Fin m → B` extends
along `O[X₁, …, Xₘ] → (O[X₁, …, Xₘ])†` to an `O`-algebra homomorphism
`(O[X₁, …, Xₘ])† →ₐ[O] B`. -/
structure IsWeaklyComplete (π : O) (B : Type*) [CommRing B] [Algebra O B] : Prop where
  isHausdorff : IsHausdorff (Ideal.span {algebraMap O B π}) B
  exists_lift_fin (m : ℕ) (b : Fin m → B) :
    ∃ ψ : weakCompletion π (MvPolynomial (Fin m) O) →ₐ[O] B,
      ∀ i, ψ (weakCompletion.of π (MvPolynomial (Fin m) O) (MvPolynomial.X i)) = b i

/-- Explicit characterization of `IsWeaklyComplete π B`. -/
theorem isWeaklyComplete_iff (π : O) (B : Type*) [CommRing B] [Algebra O B] :
    IsWeaklyComplete π B ↔
      IsHausdorff (Ideal.span {algebraMap O B π}) B ∧
        ∀ (m : ℕ) (b : Fin m → B),
          ∃ ψ : weakCompletion π (MvPolynomial (Fin m) O) →ₐ[O] B,
            ∀ i, ψ (weakCompletion.of π (MvPolynomial (Fin m) O) (MvPolynomial.X i)) = b i :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An `O`-algebra `B` is *weakly complete and finitely generated* (w.c.f.g.) with respect to
`π : O` (Monsky–Washnitzer §2; van der Put §2, (2.1)) if `B` is isomorphic as an `O`-algebra to a
quotient `(O[X₁, …, Xₘ])† ⧸ J` of the weak completion of a polynomial algebra in finitely many
variables. -/
def IsWeaklyCompleteFG (π : O) (B : Type*) [CommRing B] [Algebra O B] : Prop :=
  ∃ (m : ℕ) (J : Ideal (weakCompletion π (MvPolynomial (Fin m) O))),
    Nonempty (B ≃ₐ[O] (weakCompletion π (MvPolynomial (Fin m) O) ⧸ J))

/-- Definitional unfolding of `IsWeaklyCompleteFG π B`. -/
theorem isWeaklyCompleteFG_def (π : O) (B : Type*) [CommRing B] [Algebra O B] :
    IsWeaklyCompleteFG π B ↔
      ∃ (m : ℕ) (J : Ideal (weakCompletion π (MvPolynomial (Fin m) O))),
        Nonempty (B ≃ₐ[O] (weakCompletion π (MvPolynomial (Fin m) O) ⧸ J)) :=
  Iff.rfl

/-- An `O`-algebra `B` is w.c.f.g. if and only if it receives a surjective `O`-algebra homomorphism
from `(O[X₁, …, Xₘ])†` for some `m : ℕ`. -/
theorem isWeaklyCompleteFG_iff_exists_surjective (π : O) (B : Type*) [CommRing B] [Algebra O B] :
    IsWeaklyCompleteFG π B ↔
      ∃ (m : ℕ) (ψ : weakCompletion π (MvPolynomial (Fin m) O) →ₐ[O] B),
        Function.Surjective ψ := by
  refine ⟨fun ⟨m, J, ⟨e⟩⟩ ↦ ⟨m, e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ O J),
      e.symm.surjective.comp Ideal.Quotient.mk_surjective⟩,
    fun ⟨m, ψ, hψ⟩ ↦ ⟨m, RingHom.ker ψ, ⟨(Ideal.quotientKerAlgEquivOfSurjective hψ).symm⟩⟩⟩

namespace IsWeaklyComplete

variable {π : O} {B B' : Type*} [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B']

/-- Weak completeness transfers along `O`-algebra equivalences. -/
theorem of_algEquiv (hB : IsWeaklyComplete π B) (e : B ≃ₐ[O] B') : IsWeaklyComplete π B' where
  isHausdorff := by
    have hmap : (Ideal.span {algebraMap O B π}).map e.toRingEquiv =
        Ideal.span {algebraMap O B' π} := by
      rw [Ideal.map_span, Set.image_singleton]
      simp
    exact hmap ▸ (IsHausdorff.congr_ringEquiv _ e.toRingEquiv).mpr hB.isHausdorff
  exists_lift_fin m b := by
    obtain ⟨ψ, hψ⟩ := hB.exists_lift_fin m (e.symm ∘ b)
    exact ⟨e.toAlgHom.comp ψ, fun i ↦ by simp [hψ i]⟩

/-- Two `O`-equivalent algebras are simultaneously weakly complete. -/
theorem algEquiv_iff (e : B ≃ₐ[O] B') : IsWeaklyComplete π B ↔ IsWeaklyComplete π B' :=
  ⟨fun h ↦ h.of_algEquiv e, fun h ↦ h.of_algEquiv e.symm⟩

/-- In a weakly complete `O`-algebra `B`, every tuple `b : σ → B` indexed by an arbitrary finite
type `σ` extends uniquely along `O[X_σ] → (O[X_σ])†` to `(O[X_σ])† →ₐ[O] B`. -/
theorem existsUnique_lift_mvPolynomial {σ : Type*} [Finite σ] (hB : IsWeaklyComplete π B)
    (b : σ → B) :
    ∃! ψ : weakCompletion π (MvPolynomial σ O) →ₐ[O] B,
      ∀ i, ψ (weakCompletion.of π (MvPolynomial σ O) (MvPolynomial.X i)) = b i := by
  have := hB.isHausdorff
  cases nonempty_fintype σ
  let e := Fintype.equivFin σ
  obtain ⟨ψ₀, hψ₀⟩ := hB.exists_lift_fin (Fintype.card σ) (b ∘ e.symm)
  refine ⟨ψ₀.comp (weakCompletion.map π (MvPolynomial.renameEquiv O e).toAlgHom), fun i ↦ ?_,
    fun ψ hψ ↦ weakCompletion.algHom_ext_mvPolynomial π fun i ↦ ?_⟩
  · simp [hψ₀ (e i)]
  · simp [hψ i, hψ₀ (e i)]

/-- In a weakly complete `O`-algebra `B`, `1 - π b` is a unit for every `b : B`. -/
theorem isUnit_one_sub_algebraMap_mul (hB : IsWeaklyComplete π B) (b : B) :
    IsUnit (1 - algebraMap O B π * b) := by
  obtain ⟨ψ, hψ⟩ := hB.exists_lift_fin 1 (fun _ ↦ b)
  have hu := (weakCompletion.isUnit_one_sub_algebraMap_mul π
    (weakCompletion.of π (MvPolynomial (Fin 1) O) (MvPolynomial.X 0))).map ψ
  simpa [map_sub, map_mul, AlgHom.commutes, hψ 0] using hu

/-- In a weakly complete `O`-algebra `B`, `1 + π b` is a unit for every `b : B`. -/
theorem isUnit_one_add_algebraMap_mul (hB : IsWeaklyComplete π B) (b : B) :
    IsUnit (1 + algebraMap O B π * b) := by
  simpa [sub_neg_eq_add] using hB.isUnit_one_sub_algebraMap_mul (-b)

/-- The image of `π` in any weakly complete `O`-algebra `B` lies in the Jacobson radical of `B`. -/
theorem algebraMap_mem_jacobson (hB : IsWeaklyComplete π B) :
    algebraMap O B π ∈ Ring.jacobson B :=
  Ring.mem_jacobson_iff.mpr fun b ↦ by
    simpa [add_comm] using hB.isUnit_one_add_algebraMap_mul b

/-- The ideal generated by `π` in a weakly complete `O`-algebra `B` lies in `Ring.jacobson B`. -/
theorem span_algebraMap_le_jacobson (hB : IsWeaklyComplete π B) :
    Ideal.span {algebraMap O B π} ≤ Ring.jacobson B :=
  (Ring.jacobson B).span_singleton_le_iff_mem.mpr hB.algebraMap_mem_jacobson

/-- Every `π`-adically complete `O`-algebra (finitely generated or not) is weakly complete with
respect to `π`. -/
theorem of_isAdicComplete (π : O) (B : Type*) [CommRing B] [Algebra O B]
    [IsAdicComplete (Ideal.span {algebraMap O B π}) B] :
    IsWeaklyComplete π B where
  isHausdorff := inferInstance
  exists_lift_fin m b := by
    let fB : B →ₐ[O] piAdicCompletion π B := IsScalarTower.toAlgHom O B (piAdicCompletion π B)
    have hfB : Function.Bijective fB := by
      convert AdicCompletion.of_bijective (Ideal.span {algebraMap O B π}) B using 1
      ext x
      simp [fB, AdicCompletion.algebraMap_apply]
    let eB : B ≃ₐ[O] piAdicCompletion π B := AlgEquiv.ofBijective fB hfB
    have hspan : Ideal.span {algebraMap O (MvPolynomial (Fin m) O) π} ≤
        (Ideal.span {algebraMap O B π}).comap (MvPolynomial.aeval b) := by
      simp [← Ideal.map_le_iff_le_comap, Ideal.map_span]
    let ψ : weakCompletion π (MvPolynomial (Fin m) O) →ₐ[O] B :=
      eB.symm.toAlgHom.comp
        ((AdicCompletion.mapₐ (MvPolynomial.aeval b) hspan).comp
          (weakCompletion π (MvPolynomial (Fin m) O)).val)
    refine ⟨ψ, fun i ↦ eB.injective ?_⟩
    dsimp only [ψ]
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, AlgHom.comp_apply,
      Subalgebra.val_apply, weakCompletion.coe_of, AdicCompletion.mapₐ_of, MvPolynomial.aeval_X]
    simp [eB, fB, AdicCompletion.algebraMap_apply]

/-- Every `O`-algebra in which the image of `π` is nilpotent is weakly complete with respect to
`π`. -/
theorem of_isNilpotent {π : O} {B : Type*} [CommRing B] [Algebra O B]
    (hπ : IsNilpotent (algebraMap O B π)) :
    IsWeaklyComplete π B := by
  obtain ⟨n, hn⟩ := hπ
  have hpow : Ideal.span {algebraMap O B π} ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, hn, Ideal.span_singleton_eq_bot]
  have : IsAdicComplete (Ideal.span {algebraMap O B π}) B :=
    TauCeti.isAdicComplete_of_pow_smul_eq_bot (by rw [hpow, Submodule.bot_smul])
  exact of_isAdicComplete π B

end IsWeaklyComplete

namespace weakCompletion

variable (π : O) (S : Type*) [CommRing S] [Algebra O S] [Algebra.FiniteType O S]

/-- For every finitely generated `O`-algebra `S`, the weak completion `S†` is weakly complete with
respect to `π`. -/
theorem isWeaklyComplete : IsWeaklyComplete π (weakCompletion π S) :=
  ⟨inferInstance, fun _ y ↦ ⟨aeval π y, aeval_of_X π y⟩⟩

variable {S}

/-- **Universal property of the Monsky–Washnitzer weak completion** for weakly complete target
algebras: without any noetherianity hypothesis, every `O`-algebra homomorphism `φ : S →ₐ[O] B` from
a finitely generated `O`-algebra `S` into a weakly complete `O`-algebra `B` extends uniquely along
`of π S : S →ₐ[O] S†`. -/
theorem existsUnique_lift_of_isWeaklyComplete {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) (φ : S →ₐ[O] B) :
    ∃! φ' : weakCompletion π S →ₐ[O] B, φ'.comp (of π S) = φ := by
  have := hB.isHausdorff
  obtain ⟨g, hg⟩ := Algebra.FiniteType.out (R := O) (A := S)
  let x : g → S := (↑)
  have hx : Algebra.adjoin O (Set.range x) = ⊤ := by
    simpa only [x, Subtype.range_coe_subtype, Finset.setOfPred_mem] using hg
  have hf : Function.Surjective (MvPolynomial.aeval (R := O) x) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hx
  obtain ⟨Ψ, hΨ, -⟩ := hB.existsUnique_lift_mvPolynomial (φ ∘ x)
  have hΨ_poly : Ψ.comp (of π (MvPolynomial g O)) = φ.comp (MvPolynomial.aeval x) :=
    MvPolynomial.algHom_ext fun i ↦ by simp [hΨ i]
  have hker_base : (RingHom.ker (MvPolynomial.aeval x)).map (of π (MvPolynomial g O)) ≤
      RingHom.ker Ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro P hP
    rw [RingHom.mem_ker] at hP
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hP' := DFunLike.congr_fun hΨ_poly P
    simpa [hP] using hP'
  have hker_le : ∀ z ∈ RingHom.ker (map π (MvPolynomial.aeval x)), Ψ z = 0 := by
    intro z hz
    rw [ker_map_eq_iInf_of_surjective π hf] at hz
    refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {algebraMap O B π})).mpr fun n ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (Ideal.mem_iInf.mp hz n)
    rw [map_add, RingHom.mem_ker.mp (hker_base hu), zero_add]
    exact Ideal.apply_mem_span_algebraMap_pow Ψ hv
  let eS := Ideal.quotientKerAlgEquivOfSurjective (map_surjective π _ hf)
  let φ' : weakCompletion π S →ₐ[O] B :=
    (Ideal.Quotient.liftₐ (RingHom.ker (map π (MvPolynomial.aeval x))) Ψ hker_le).comp
      eS.symm.toAlgHom
  have hφ'_map (z : weakCompletion π (MvPolynomial g O)) :
      φ' (map π (MvPolynomial.aeval x) z) = Ψ z := by
    have hmk : eS.symm (map π (MvPolynomial.aeval x) z) = Ideal.Quotient.mk _ z :=
      eS.injective (by simp [eS])
    dsimp only [φ']
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hmk, Ideal.Quotient.liftₐ_apply]
    exact Ideal.Quotient.lift_mk _ _ _
  refine ⟨φ', AlgHom.ext fun s ↦ ?_, fun ψ hψ ↦ algHom_ext π fun s ↦ ?_⟩
  · obtain ⟨P, rfl⟩ := hf s
    calc φ' (of π S (MvPolynomial.aeval x P))
        = φ' (map π (MvPolynomial.aeval x) (of π (MvPolynomial g O) P)) := by rw [map_of]
      _ = Ψ (of π (MvPolynomial g O) P) := hφ'_map _
      _ = φ (MvPolynomial.aeval x P) := DFunLike.congr_fun hΨ_poly P
  · exact (DFunLike.congr_fun hψ s).trans (by
      obtain ⟨P, rfl⟩ := hf s
      simpa [← map_of, hφ'_map] using (DFunLike.congr_fun hΨ_poly P).symm)

/-- The unique extension `S† →ₐ[O] B` of `φ : S →ₐ[O] B` into a weakly complete `O`-algebra `B`. -/
noncomputable def liftOfIsWeaklyComplete {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) (φ : S →ₐ[O] B) :
    weakCompletion π S →ₐ[O] B :=
  (existsUnique_lift_of_isWeaklyComplete π hB φ).choose

@[simp]
theorem liftOfIsWeaklyComplete_comp_of {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) (φ : S →ₐ[O] B) :
    (liftOfIsWeaklyComplete π hB φ).comp (of π S) = φ :=
  (existsUnique_lift_of_isWeaklyComplete π hB φ).choose_spec.1

@[simp]
theorem liftOfIsWeaklyComplete_of {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) (φ : S →ₐ[O] B) (s : S) :
    liftOfIsWeaklyComplete π hB φ (of π S s) = φ s :=
  DFunLike.congr_fun (liftOfIsWeaklyComplete_comp_of π hB φ) s

/-- Uniqueness characterization of `liftOfIsWeaklyComplete π hB φ`. -/
theorem eq_liftOfIsWeaklyComplete_iff {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) (φ : S →ₐ[O] B) (ψ : weakCompletion π S →ₐ[O] B) :
    ψ = liftOfIsWeaklyComplete π hB φ ↔ ψ.comp (of π S) = φ :=
  ⟨fun h ↦ h ▸ liftOfIsWeaklyComplete_comp_of π hB φ,
    (existsUnique_lift_of_isWeaklyComplete π hB φ).choose_spec.2 ψ⟩

/-- Naturality of `liftOfIsWeaklyComplete` along `weakCompletion.map`. -/
@[simp]
theorem liftOfIsWeaklyComplete_comp_map {R B : Type*} [CommRing R] [Algebra O R]
    [Algebra.FiniteType O R] [CommRing B] [Algebra O B] (hB : IsWeaklyComplete π B)
    (φ : S →ₐ[O] B) (f : R →ₐ[O] S) :
    (liftOfIsWeaklyComplete π hB φ).comp (map π f) =
      liftOfIsWeaklyComplete π hB (φ.comp f) := by
  rw [eq_liftOfIsWeaklyComplete_iff]
  ext r
  simp

variable (S) in
/-- Restriction along `of π S : S →ₐ[O] S†` identifies `(S† →ₐ[O] B)` with `(S →ₐ[O] B)` for every
weakly complete `O`-algebra `B`. -/
noncomputable def liftEquivOfIsWeaklyComplete {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) :
    (weakCompletion π S →ₐ[O] B) ≃ (S →ₐ[O] B) where
  toFun ψ := ψ.comp (of π S)
  invFun φ := liftOfIsWeaklyComplete π hB φ
  left_inv ψ := ((eq_liftOfIsWeaklyComplete_iff π hB _ ψ).mpr rfl).symm
  right_inv φ := liftOfIsWeaklyComplete_comp_of π hB φ

@[simp]
theorem liftEquivOfIsWeaklyComplete_apply {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) (ψ : weakCompletion π S →ₐ[O] B) :
    liftEquivOfIsWeaklyComplete π S hB ψ = ψ.comp (of π S) :=
  (rfl)

@[simp]
theorem liftEquivOfIsWeaklyComplete_symm_apply {B : Type*} [CommRing B] [Algebra O B]
    (hB : IsWeaklyComplete π B) (φ : S →ₐ[O] B) :
    (liftEquivOfIsWeaklyComplete π S hB).symm φ = liftOfIsWeaklyComplete π hB φ :=
  (rfl)

end weakCompletion

namespace IsWeaklyCompleteFG

variable {π : O} {B B' : Type*} [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B']

/-- Weakly complete finite generation transfers along `O`-algebra equivalences. -/
theorem of_algEquiv (hB : IsWeaklyCompleteFG π B) (e : B ≃ₐ[O] B') : IsWeaklyCompleteFG π B' := by
  obtain ⟨m, J, ⟨e₀⟩⟩ := hB
  exact ⟨m, J, ⟨e.symm.trans e₀⟩⟩

/-- Two `O`-equivalent algebras are simultaneously w.c.f.g. -/
theorem algEquiv_iff (e : B ≃ₐ[O] B') : IsWeaklyCompleteFG π B ↔ IsWeaklyCompleteFG π B' :=
  ⟨fun h ↦ h.of_algEquiv e, fun h ↦ h.of_algEquiv e.symm⟩

/-- Every surjective `O`-algebra image of a w.c.f.g. algebra is w.c.f.g. -/
theorem of_surjective (hB : IsWeaklyCompleteFG π B) {f : B →ₐ[O] B'}
    (hf : Function.Surjective f) :
    IsWeaklyCompleteFG π B' := by
  rw [isWeaklyCompleteFG_iff_exists_surjective] at hB ⊢
  obtain ⟨m, ψ, hψ⟩ := hB
  exact ⟨m, f.comp ψ, hf.comp hψ⟩

/-- Every quotient of a w.c.f.g. algebra by an ideal is w.c.f.g. -/
theorem quotient (hB : IsWeaklyCompleteFG π B) (I : Ideal B) : IsWeaklyCompleteFG π (B ⧸ I) :=
  hB.of_surjective (f := Ideal.Quotient.mkₐ O I) Ideal.Quotient.mk_surjective

/-- Overconvergent polynomial evaluation into any w.c.f.g. `O`-algebra `B`: every finite tuple
`b : σ → B` extends to an `O`-algebra homomorphism `(O[X_σ])† →ₐ[O] B`. -/
theorem exists_lift_mvPolynomial {σ : Type*} [Finite σ] (hB : IsWeaklyCompleteFG π B)
    (b : σ → B) :
    ∃ ψ : weakCompletion π (MvPolynomial σ O) →ₐ[O] B,
      ∀ i, ψ (weakCompletion.of π (MvPolynomial σ O) (MvPolynomial.X i)) = b i := by
  obtain ⟨m, q, hq⟩ := (isWeaklyCompleteFG_iff_exists_surjective π B).mp hB
  choose y hy using fun i ↦ hq (b i)
  refine ⟨q.comp (weakCompletion.aeval π y), fun i ↦ ?_⟩
  simp [hy i]

/-- In a w.c.f.g. `O`-algebra `B`, `1 - π b` is a unit for every `b : B`. -/
theorem isUnit_one_sub_algebraMap_mul (hB : IsWeaklyCompleteFG π B) (b : B) :
    IsUnit (1 - algebraMap O B π * b) := by
  obtain ⟨ψ, hψ⟩ := hB.exists_lift_mvPolynomial (fun _ : Fin 1 ↦ b)
  have hu := (weakCompletion.isUnit_one_sub_algebraMap_mul π
    (weakCompletion.of π (MvPolynomial (Fin 1) O) (MvPolynomial.X 0))).map ψ
  simpa [map_sub, map_mul, AlgHom.commutes, hψ 0] using hu

/-- In a w.c.f.g. `O`-algebra `B`, `1 + π b` is a unit for every `b : B`. -/
theorem isUnit_one_add_algebraMap_mul (hB : IsWeaklyCompleteFG π B) (b : B) :
    IsUnit (1 + algebraMap O B π * b) := by
  simpa [sub_neg_eq_add] using hB.isUnit_one_sub_algebraMap_mul (-b)

/-- The image of `π` in any w.c.f.g. `O`-algebra `B` lies in the Jacobson radical of `B`. -/
theorem algebraMap_mem_jacobson (hB : IsWeaklyCompleteFG π B) :
    algebraMap O B π ∈ Ring.jacobson B :=
  Ring.mem_jacobson_iff.mpr fun b ↦ by
    simpa [add_comm] using hB.isUnit_one_add_algebraMap_mul b

/-- The ideal generated by `π` in a w.c.f.g. `O`-algebra `B` lies in `Ring.jacobson B`. -/
theorem span_algebraMap_le_jacobson (hB : IsWeaklyCompleteFG π B) :
    Ideal.span {algebraMap O B π} ≤ Ring.jacobson B :=
  (Ring.jacobson B).span_singleton_le_iff_mem.mpr hB.algebraMap_mem_jacobson

/-- Every `π`-adically separated w.c.f.g. `O`-algebra is weakly complete. -/
theorem isWeaklyComplete_of_isHausdorff (hB : IsWeaklyCompleteFG π B)
    [IsHausdorff (Ideal.span {algebraMap O B π}) B] :
    IsWeaklyComplete π B :=
  ⟨inferInstance, fun _ b ↦ hB.exists_lift_mvPolynomial b⟩

/-- Every noetherian w.c.f.g. `O`-algebra is `π`-adically separated. -/
theorem isHausdorff_of_isNoetherianRing (hB : IsWeaklyCompleteFG π B) [IsNoetherianRing B] :
    IsHausdorff (Ideal.span {algebraMap O B π}) B :=
  IsHausdorff.of_le_jacobson _ B hB.span_algebraMap_le_jacobson

/-- Every noetherian w.c.f.g. `O`-algebra is weakly complete. -/
theorem isWeaklyComplete_of_isNoetherianRing (hB : IsWeaklyCompleteFG π B) [IsNoetherianRing B] :
    IsWeaklyComplete π B := by
  have := hB.isHausdorff_of_isNoetherianRing
  exact hB.isWeaklyComplete_of_isHausdorff

/-- When `(O[X₁, …, Xₘ])†` is noetherian for every `m : ℕ`, every w.c.f.g. `O`-algebra is
noetherian. -/
theorem isNoetherianRing
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) :
    IsNoetherianRing B := by
  obtain ⟨m, ψ, hψ⟩ := (isWeaklyCompleteFG_iff_exists_surjective π B).mp hB
  exact isNoetherianRing_of_surjective _ _ ψ.toRingHom hψ

/-- When `(O[X₁, …, Xₘ])†` is noetherian for every `m : ℕ`, every w.c.f.g. `O`-algebra is weakly
complete (Monsky–Washnitzer, Theorem 2.1). -/
theorem isWeaklyComplete
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) :
    IsWeaklyComplete π B := by
  have := hB.isNoetherianRing
  exact hB.isWeaklyComplete_of_isNoetherianRing

end IsWeaklyCompleteFG

/-- For every finitely generated `O`-algebra `S`, the weak completion `S†` is weakly complete and
finitely generated (`IsWeaklyCompleteFG π S†`). No noetherianity hypothesis is needed. -/
theorem weakCompletion.isWeaklyCompleteFG (π : O) (S : Type*) [CommRing S] [Algebra O S]
    [Algebra.FiniteType O S] :
    IsWeaklyCompleteFG π (weakCompletion π S) := by
  obtain ⟨g, hg⟩ := Algebra.FiniteType.out (R := O) (A := S)
  cases nonempty_fintype g
  let e := Fintype.equivFin g
  let x : Fin (Fintype.card g) → S := fun i ↦ (e.symm i : S)
  have hx : Algebra.adjoin O (Set.range x) = ⊤ := by
    have hrange : Set.range x = (g : Set S) := by
      ext s
      simp only [x, Set.mem_range]
      exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (e.symm i).property,
        fun hs ↦ ⟨e ⟨s, hs⟩, by simp⟩⟩
    rwa [hrange]
  exact (isWeaklyCompleteFG_iff_exists_surjective π _).mpr
    ⟨Fintype.card g, weakCompletion.map π (MvPolynomial.aeval x),
      weakCompletion.map_aeval_surjective π x hx⟩

namespace IsWeaklyCompleteFG

/-- Every finitely generated `π`-adically complete `O`-algebra is w.c.f.g. with respect to `π`. -/
theorem of_isAdicComplete (π : O) (S : Type*) [CommRing S] [Algebra O S]
    [Algebra.FiniteType O S] [IsAdicComplete (Ideal.span {algebraMap O S π}) S] :
    IsWeaklyCompleteFG π S :=
  (weakCompletion.isWeaklyCompleteFG π S).of_algEquiv
    (AlgEquiv.ofBijective (weakCompletion.of π S)
      (weakCompletion.of_bijective_of_isAdicComplete π)).symm

/-- Every finitely generated `O`-algebra in which the image of `π` is nilpotent is w.c.f.g. with
respect to `π`. -/
theorem of_isNilpotent {π : O} {S : Type*} [CommRing S] [Algebra O S]
    [Algebra.FiniteType O S] (hπ : IsNilpotent (algebraMap O S π)) :
    IsWeaklyCompleteFG π S :=
  (weakCompletion.isWeaklyCompleteFG π S).of_algEquiv
    (AlgEquiv.ofBijective (weakCompletion.of π S)
      (weakCompletion.of_bijective_of_isNilpotent hπ)).symm

/-- Whenever the base ring `O` is `π`-adically complete, `O` itself is w.c.f.g. over `O`. -/
theorem self_of_isAdicComplete (π : O) [IsAdicComplete (Ideal.span {π}) O] :
    IsWeaklyCompleteFG π O := by
  have : IsAdicComplete (Ideal.span {algebraMap O O π}) O := by simpa
  exact of_isAdicComplete π O

/-- The residue ring `O ⧸ Ideal.span {π}` is w.c.f.g. over `O` for every `π : O`. -/
theorem quotient_span_self (π : O) : IsWeaklyCompleteFG π (O ⧸ Ideal.span {π}) :=
  of_isNilpotent ⟨1, by
    rw [pow_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl⟩

end IsWeaklyCompleteFG

namespace weakCompletion

variable (π : O) {S B : Type*} [CommRing S] [Algebra O S] [Algebra.FiniteType O S]
  [CommRing B] [Algebra O B]

/-- Every `O`-algebra homomorphism `φ : S →ₐ[O] B` into a noetherian w.c.f.g. `O`-algebra `B`
extends uniquely along `of π S : S →ₐ[O] S†`. -/
theorem existsUnique_lift_of_isNoetherianRing [IsNoetherianRing B] (hB : IsWeaklyCompleteFG π B)
    (φ : S →ₐ[O] B) :
    ∃! φ' : weakCompletion π S →ₐ[O] B, φ'.comp (of π S) = φ :=
  existsUnique_lift_of_isWeaklyComplete π hB.isWeaklyComplete_of_isNoetherianRing φ

/-- **Universal property of the Monsky–Washnitzer weak completion** for w.c.f.g. target algebras:
when `(O[X₁, …, Xₘ])†` is noetherian for every `m : ℕ`, every `O`-algebra homomorphism
`φ : S →ₐ[O] B` from a finitely generated `O`-algebra `S` into a w.c.f.g. `O`-algebra `B` extends
uniquely along `of π S : S →ₐ[O] S†`. -/
theorem existsUnique_lift
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) (φ : S →ₐ[O] B) :
    ∃! φ' : weakCompletion π S →ₐ[O] B, φ'.comp (of π S) = φ :=
  existsUnique_lift_of_isWeaklyComplete π hB.isWeaklyComplete φ

/-- The unique extension `S† →ₐ[O] B` of `φ : S →ₐ[O] B` into a w.c.f.g. `O`-algebra `B` when
polynomial weak completions over `O` are noetherian. -/
noncomputable def lift
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) (φ : S →ₐ[O] B) :
    weakCompletion π S →ₐ[O] B :=
  liftOfIsWeaklyComplete π hB.isWeaklyComplete φ

@[simp]
theorem lift_comp_of
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) (φ : S →ₐ[O] B) :
    (lift π hB φ).comp (of π S) = φ :=
  liftOfIsWeaklyComplete_comp_of π hB.isWeaklyComplete φ

@[simp]
theorem lift_of
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) (φ : S →ₐ[O] B) (s : S) :
    lift π hB φ (of π S s) = φ s :=
  liftOfIsWeaklyComplete_of π hB.isWeaklyComplete φ s

/-- Uniqueness characterization of `lift π hB φ`. -/
theorem eq_lift_iff
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) (φ : S →ₐ[O] B) (ψ : weakCompletion π S →ₐ[O] B) :
    ψ = lift π hB φ ↔ ψ.comp (of π S) = φ :=
  eq_liftOfIsWeaklyComplete_iff π hB.isWeaklyComplete φ ψ

variable (S) in
/-- Restriction along `of π S : S →ₐ[O] S†` identifies `(S† →ₐ[O] B)` with `(S →ₐ[O] B)` for every
w.c.f.g. `O`-algebra `B` when polynomial weak completions over `O` are noetherian. -/
noncomputable def liftEquiv
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) :
    (weakCompletion π S →ₐ[O] B) ≃ (S →ₐ[O] B) :=
  liftEquivOfIsWeaklyComplete π S hB.isWeaklyComplete

@[simp]
theorem liftEquiv_apply
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) (ψ : weakCompletion π S →ₐ[O] B) :
    liftEquiv π S hB ψ = ψ.comp (of π S) :=
  (rfl)

@[simp]
theorem liftEquiv_symm_apply
    [∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O))]
    (hB : IsWeaklyCompleteFG π B) (φ : S →ₐ[O] B) :
    (liftEquiv π S hB).symm φ = lift π hB φ :=
  (rfl)

end weakCompletion

section NonExamples

/-- Although `O ⧸ Ideal.span {π}` is w.c.f.g. over `O`, it is not flat over `O` whenever `π` is a
non-unit nonzerodivisor of `O`. -/
theorem not_flat_quotient_span {π : O} (hπ : π ∈ nonZeroDivisors O) (hπu : ¬ IsUnit π) :
    ¬ Module.Flat O (O ⧸ Ideal.span {π}) := by
  intro hflat
  have hreg : IsSMulRegular (O ⧸ Ideal.span {π}) π :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hπ
  have h10 : (1 : O ⧸ Ideal.span {π}) = 0 := hreg <| by
    dsimp only
    rw [Algebra.smul_def, mul_one, smul_zero, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h10
  exact hπu (isUnit_of_dvd_one h10)

/-- For a nonempty variable set `σ` and an `O`-algebra `R` in which `π` is not nilpotent, the
polynomial algebra `R[X_σ]` is not weakly complete with respect to `π`. -/
theorem not_isWeaklyComplete_mvPolynomial {R σ : Type*} [CommRing R] [Algebra O R] [Nonempty σ]
    {π : O} (hπ : ¬ IsNilpotent (algebraMap O R π)) :
    ¬ IsWeaklyComplete π (MvPolynomial σ R) := by
  obtain ⟨i⟩ := ‹Nonempty σ›
  refine fun h ↦ hπ ?_
  let ev : MvPolynomial σ R →ₐ[R] Polynomial R := MvPolynomial.aeval fun _ ↦ Polynomial.X
  have hev : ev (1 + algebraMap O (MvPolynomial σ R) π * MvPolynomial.X i) =
      Polynomial.C (1 : R) + Polynomial.X * Polynomial.C (algebraMap O R π) := by
    rw [IsScalarTower.algebraMap_apply O R (MvPolynomial σ R), map_add, map_one, map_mul,
      AlgHom.commutes, Polynomial.algebraMap_eq, MvPolynomial.aeval_X, Polynomial.C_1, mul_comm]
  have hu := hev ▸ (h.isUnit_one_add_algebraMap_mul (MvPolynomial.X i)).map ev
  exact Polynomial.isNilpotent_C_iff.mp (Polynomial.isUnit_C_add_X_mul_iff.mp hu).2

/-- For a nonempty variable set `σ` and an `O`-algebra `R` in which `π` is not nilpotent, the
polynomial algebra `R[X_σ]` is not w.c.f.g. with respect to `π`. -/
theorem not_isWeaklyCompleteFG_mvPolynomial {R σ : Type*} [CommRing R] [Algebra O R] [Nonempty σ]
    {π : O} (hπ : ¬ IsNilpotent (algebraMap O R π)) :
    ¬ IsWeaklyCompleteFG π (MvPolynomial σ R) := by
  obtain ⟨i⟩ := ‹Nonempty σ›
  refine fun h ↦ hπ ?_
  let ev : MvPolynomial σ R →ₐ[R] Polynomial R := MvPolynomial.aeval fun _ ↦ Polynomial.X
  have hev : ev (1 + algebraMap O (MvPolynomial σ R) π * MvPolynomial.X i) =
      Polynomial.C (1 : R) + Polynomial.X * Polynomial.C (algebraMap O R π) := by
    rw [IsScalarTower.algebraMap_apply O R (MvPolynomial σ R), map_add, map_one, map_mul,
      AlgHom.commutes, Polynomial.algebraMap_eq, MvPolynomial.aeval_X, Polynomial.C_1, mul_comm]
  have hu := hev ▸ (h.isUnit_one_add_algebraMap_mul (MvPolynomial.X i)).map ev
  exact Polynomial.isNilpotent_C_iff.mp (Polynomial.isUnit_C_add_X_mul_iff.mp hu).2

/-! Concrete universal-property lift: in `(O[T])†`, `1 + π T` is invertible, so the Laurent
polynomial algebra `O[X, Y] ⧸ (X Y - 1)` maps to `(O[T])†` via `X ↦ 1 + π T`, `Y ↦ (1 + π T)⁻¹`,
and this map extends uniquely to `(O[X, Y] ⧸ (X Y - 1))† →ₐ[O] (O[T])†`. -/

example (π : O) :
    let B := weakCompletion π (MvPolynomial (Fin 1) O)
    let u : Bˣ :=
      (weakCompletion.isUnit_one_add_algebraMap_mul π
        (weakCompletion.of π (MvPolynomial (Fin 1) O) (MvPolynomial.X 0))).unit
    let I : Ideal (MvPolynomial (Fin 2) O) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - 1}
    ∃ φ' : weakCompletion π (MvPolynomial (Fin 2) O ⧸ I) →ₐ[O] B,
      φ' (weakCompletion.of π _ (Ideal.Quotient.mk I (MvPolynomial.X 0))) = (u : B) ∧
        φ' (weakCompletion.of π _ (Ideal.Quotient.mk I (MvPolynomial.X 1))) = ((u⁻¹ : Bˣ) : B) := by
  intro B u I
  let φ₀ : MvPolynomial (Fin 2) O →ₐ[O] B :=
    MvPolynomial.aeval fun i : Fin 2 ↦ if i = 0 then (u : B) else ((u⁻¹ : Bˣ) : B)
  have hI : I ≤ RingHom.ker φ₀ := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp [φ₀, Units.mul_inv]
  let φ : (MvPolynomial (Fin 2) O ⧸ I) →ₐ[O] B :=
    Ideal.Quotient.liftₐ I φ₀ fun a ha ↦ RingHom.mem_ker.mp (hI ha)
  refine ⟨weakCompletion.liftOfIsWeaklyComplete π (weakCompletion.isWeaklyComplete π _) φ, ?_, ?_⟩
  · rw [weakCompletion.liftOfIsWeaklyComplete_of, Ideal.Quotient.liftₐ_apply]
    exact (Ideal.Quotient.lift_mk I φ₀.toRingHom _).trans (by simp [φ₀])
  · rw [weakCompletion.liftOfIsWeaklyComplete_of, Ideal.Quotient.liftₐ_apply]
    exact (Ideal.Quotient.lift_mk I φ₀.toRingHom _).trans (by simp [φ₀])

end NonExamples

end General

section UnitClosedBall

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "O" => Subring.unitClosedBall K

/-- Over the valuation unit ball `O = K°` of a complete ultrametric field `K` with a parameter
`π ∈ O` satisfying `0 < ‖(π : K)‖ < 1`, an `O`-algebra `B` is w.c.f.g. with respect to `π` if and
only if it is `O`-isomorphic to a quotient of an integral Monsky–Washnitzer algebra
`O⟨X₁, …, Xₘ⟩†`. -/
theorem isWeaklyCompleteFG_iff_exists_intWashnitzerAlgebra [CompleteSpace K] {π : O}
    (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) (B : Type*) [CommRing B] [Algebra O B] :
    IsWeaklyCompleteFG π B ↔
      ∃ (m : ℕ) (J : Ideal (intWashnitzerAlgebra (Fin m) K)),
        Nonempty (B ≃ₐ[O] (intWashnitzerAlgebra (Fin m) K ⧸ J)) := by
  refine ⟨fun ⟨m, J, ⟨e⟩⟩ ↦ ?_, fun ⟨m, J, ⟨e⟩⟩ ↦ ?_⟩
  · let em := weakCompletion.polynomialEquiv (σ := Fin m) hπ hπ1
    exact ⟨m, J.map em.toRingHom, ⟨e.trans (Ideal.quotientEquivAlg _ _ em rfl)⟩⟩
  · let em := (weakCompletion.polynomialEquiv (σ := Fin m) hπ hπ1).symm
    exact ⟨m, J.map em.toRingHom, ⟨e.trans (Ideal.quotientEquivAlg _ _ em rfl)⟩⟩

/-- Over a complete ultrametric field `K`, the unit ball `O = K°` is w.c.f.g. over itself with
respect to `π : O` if and only if `‖(π : K)‖ < 1`. -/
theorem isWeaklyCompleteFG_unitClosedBall_iff [CompleteSpace K] (π : O) :
    IsWeaklyCompleteFG π O ↔ ‖(π : K)‖ < 1 := by
  refine ⟨fun hO ↦ lt_of_le_of_ne (Subring.mem_unitClosedBall.mp π.property) fun hnorm ↦ ?_,
    fun hπ1 ↦ ?_⟩
  · have hπK : (π : K) ≠ 0 := fun h0 ↦ by simp [h0] at hnorm
    have hinv_mem : (π : K)⁻¹ ∈ O := by
      rw [Subring.mem_unitClosedBall, norm_inv, hnorm, inv_one]
    let u : O := ⟨(π : K)⁻¹, hinv_mem⟩
    have hmul : π * u = 1 := Subtype.ext (mul_inv_cancel₀ hπK)
    have hu0 : IsUnit (0 : O) := by
      simpa [Algebra.algebraMap_self, hmul] using hO.isUnit_one_sub_algebraMap_mul u
    exact not_isUnit_zero hu0
  · by_cases hπ : π = 0
    · subst hπ
      exact IsWeaklyCompleteFG.of_isNilpotent ⟨1, by simp⟩
    · have hπK : (π : K) ≠ 0 := by simpa using hπ
      let ϖ : NormedRing.PseudoUniformizer K := .ofAlgebraMap (c := (π : K)) hπK hπ1
      have hϖ : ϖ.toUnitClosedBall = π := by
        apply Subtype.ext
        simp [NormedRing.PseudoUniformizer.coe_toUnitClosedBall, ϖ]
      have : IsAdicComplete (Ideal.span {π}) O :=
        hϖ ▸ ϖ.isAdicComplete_span_toUnitClosedBall
      exact IsWeaklyCompleteFG.self_of_isAdicComplete π

/-- Over `O = K°`, for any nonzero parameter `π : O` with `‖(π : K)‖ < 1`, the quotient `O ⧸ (π)` is
not flat over `O`. -/
theorem not_flat_quotient_span_unitClosedBall {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    ¬ Module.Flat O (O ⧸ Ideal.span {π}) := by
  refine not_flat_quotient_span (mem_nonZeroDivisors_of_ne_zero hπ) fun ⟨u, hu⟩ ↦ hπ1.not_ge ?_
  have h1 : (u : K) * ((u⁻¹ : Oˣ) : K) = 1 := by
    exact_mod_cast congrArg Subtype.val u.mul_inv
  have hu_inv : ‖((u⁻¹ : Oˣ) : K)‖ ≤ 1 := Subring.mem_unitClosedBall.mp (u⁻¹ : Oˣ).val.property
  have hprod : ‖(π : K)‖ * ‖((u⁻¹ : Oˣ) : K)‖ = 1 := by
    rw [← norm_mul, ← hu, h1, norm_one]
  nlinarith [norm_nonneg (π : K)]

/-- Over `O = K°`, for any nonzero `π : O` and nonempty variable set `σ`, `O[X_σ]` is not weakly
complete with respect to `π`. -/
theorem not_isWeaklyComplete_mvPolynomial_unitClosedBall {σ : Type*} [Nonempty σ] {π : O}
    (hπ : π ≠ 0) :
    ¬ IsWeaklyComplete π (MvPolynomial σ O) :=
  not_isWeaklyComplete_mvPolynomial (R := O) (by simpa using hπ)

/-- Over `O = K°`, for any nonzero `π : O` and nonempty variable set `σ`, `O[X_σ]` is not w.c.f.g.
with respect to `π`. -/
theorem not_isWeaklyCompleteFG_mvPolynomial_unitClosedBall {σ : Type*} [Nonempty σ] {π : O}
    (hπ : π ≠ 0) :
    ¬ IsWeaklyCompleteFG π (MvPolynomial σ O) :=
  not_isWeaklyCompleteFG_mvPolynomial (R := O) (by simpa using hπ)

namespace weakCompletion

variable [CompleteSpace K] {S σ : Type*} [CommRing S] [Algebra (Subring.unitClosedBall K) S]
  [Algebra.FiniteType (Subring.unitClosedBall K) S] [Finite σ]

local notation "O'" => Subring.unitClosedBall K

/-- Evaluation of integral Monsky–Washnitzer series `O⟨X_σ⟩† →ₐ[O] S†` at an arbitrary finite
family `y : σ → S†` in the weak completion of `S`, extending `evalIntWashnitzerAlgebra`. -/
noncomputable def aevalIntWashnitzerAlgebra {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (y : σ → weakCompletion π S) :
    intWashnitzerAlgebra σ K →ₐ[O'] weakCompletion π S :=
  (aeval π y).comp (polynomialEquiv hπ hπ1).symm.toAlgHom

theorem aevalIntWashnitzerAlgebra_def {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (y : σ → weakCompletion π S) :
    aevalIntWashnitzerAlgebra hπ hπ1 y =
      (aeval π y).comp (polynomialEquiv hπ hπ1).symm.toAlgHom :=
  (rfl)

@[simp]
theorem aevalIntWashnitzerAlgebra_polynomialEquiv {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (y : σ → weakCompletion π S) (z : weakCompletion π (MvPolynomial σ O')) :
    aevalIntWashnitzerAlgebra hπ hπ1 y (polynomialEquiv hπ hπ1 z) = aeval π y z := by
  simp [aevalIntWashnitzerAlgebra_def]

@[simp]
theorem aevalIntWashnitzerAlgebra_ofMvPolynomial {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (y : σ → weakCompletion π S) (p : MvPolynomial σ O') :
    aevalIntWashnitzerAlgebra hπ hπ1 y (intWashnitzerAlgebra.ofMvPolynomial σ K p) =
      MvPolynomial.aeval y p := by
  simp [aevalIntWashnitzerAlgebra_def]

/-- Evaluating integral Monsky–Washnitzer series at elements coming from `S` recovers
`evalIntWashnitzerAlgebra`. -/
@[simp]
theorem aevalIntWashnitzerAlgebra_of_comp {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (x : σ → S) :
    aevalIntWashnitzerAlgebra hπ hπ1 (of π S ∘ x) = evalIntWashnitzerAlgebra hπ hπ1 x := by
  rw [aevalIntWashnitzerAlgebra_def, aeval_of_comp, evalIntWashnitzerAlgebra_def]

/-- Universal characterization of `aevalIntWashnitzerAlgebra hπ hπ1 y` among `O`-algebra
homomorphisms `O⟨X_σ⟩† →ₐ[O] S†`. -/
theorem eq_aevalIntWashnitzerAlgebra_iff {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (y : σ → weakCompletion π S) (ψ : intWashnitzerAlgebra σ K →ₐ[O'] weakCompletion π S) :
    ψ = aevalIntWashnitzerAlgebra hπ hπ1 y ↔
      ∀ i, ψ (intWashnitzerAlgebra.ofMvPolynomial σ K (MvPolynomial.X i)) = y i := by
  refine ⟨fun h i ↦ by simp [h], fun h ↦ ?_⟩
  have hcomp : ψ.comp (polynomialEquiv hπ hπ1).toAlgHom = aeval π y :=
    (eq_aeval_iff π y _).mpr fun i ↦ by simpa using h i
  apply AlgHom.ext
  intro f
  simpa [aevalIntWashnitzerAlgebra_def] using
    DFunLike.congr_fun hcomp ((polynomialEquiv hπ hπ1).symm f)

/-! Over a noetherian valuation unit ball `O = K°` of a complete ultrametric field `K` (for
instance any complete discretely valued field) with `0 < ‖(π : K)‖ < 1`, `isNoetherianRing`
supplies the typeclass hypothesis of `existsUnique_lift` and `liftEquiv` for all w.c.f.g. target
algebras. -/

example [IsNoetherianRing O'] {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (B : Type*) [CommRing B] [Algebra O' B] (hB : IsWeaklyCompleteFG π B) (φ : S →ₐ[O'] B) :
    ∃! φ' : weakCompletion π S →ₐ[O'] B, φ'.comp (of π S) = φ := by
  have : ∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O')) :=
    fun _ ↦ isNoetherianRing hπ hπ1
  exact existsUnique_lift π hB φ

noncomputable example [IsNoetherianRing O'] {π : O'} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (B : Type*) [CommRing B] [Algebra O' B] (hB : IsWeaklyCompleteFG π B) :
    (weakCompletion π S →ₐ[O'] B) ≃ (S →ₐ[O'] B) :=
  letI : ∀ m : ℕ, IsNoetherianRing (weakCompletion π (MvPolynomial (Fin m) O')) :=
    fun _ ↦ isNoetherianRing hπ hπ1
  liftEquiv π S hB

end weakCompletion

end UnitClosedBall

end TauCeti.Dagger
