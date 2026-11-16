/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
public import TauCeti.Algebra.Coalgebra.Subcomodule.Convolution
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Schur's lemma for simple comodules

A comodule `M` over a projective coalgebra `C` is simple (`IsSimpleOrder (Subcomodule R C M)`)
precisely when it is simple as a module over the convolution dual `WithConv (C →ₗ[R] R)`. This
file records the resulting Schur properties for native comodule morphisms and their scalar
matrices:

* Every simple comodule has a nontrivial carrier, and over a projective coalgebra it is finitely
  generated as a module over the base ring.
* A nonzero comodule morphism between simple comodules over a projective coalgebra is bijective.
* Over an algebraically closed field, every comodule endomorphism of a simple comodule is a scalar
  multiple of the identity, and every scalar matrix intertwining the coefficient matrix of a simple
  comodule with itself is a scalar multiple of the identity matrix.

No finite-dimensionality assumption on the comodule is imposed in the field statements: over a
field every coalgebra is projective, so simplicity already implies finite dimensionality.

## Main results

* `TauCeti.Subcomodule.nontrivial_of_isSimpleOrder`: a simple comodule is nontrivial.
* `TauCeti.Subcomodule.finite_of_isSimpleOrder`: a simple comodule over a projective coalgebra is
  finitely generated.
* `TauCeti.Comodule.Hom.bijective_of_ne_zero` and `TauCeti.Comodule.Hom.eq_zero_or_bijective`:
  Schur's lemma for morphisms between simple comodules.
* `TauCeti.Comodule.Hom.exists_eq_smul_id`: over an algebraically closed field, every endomorphism
  of a simple comodule is scalar.
* `Module.Basis.exists_eq_smul_one_of_coefficientMatrix_mul_eq`: the matrix form of Schur's lemma
  for a finite basis of a simple comodule over an algebraically closed field.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open Module

namespace TauCeti.Subcomodule

section CommSemiring

variable {R C M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A simple comodule has a nontrivial underlying module. -/
theorem nontrivial_of_isSimpleOrder [IsSimpleOrder (Subcomodule R C M)] : Nontrivial M := by
  rcases subsingleton_or_nontrivial M with h | h
  · refine False.elim (bot_ne_top (α := Subcomodule R C M) ?_)
    ext m
    simp [Subsingleton.elim m (0 : M)]
  · exact h

end CommSemiring

section CommRing

variable {R C M : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]

/-- Over a projective coalgebra, every simple comodule is finitely generated over the base ring. -/
theorem finite_of_isSimpleOrder [IsSimpleOrder (Subcomodule R C M)] : Module.Finite R M := by
  have hfin : Module.Finite R (⊤ : Subcomodule R C M).toSubmodule :=
    finite_of_isAtom isAtom_top
  rw [top_toSubmodule] at hfin
  exact Module.Finite.equiv (Submodule.topEquiv (R := R) (M := M))

end CommRing

end TauCeti.Subcomodule

namespace TauCeti.Comodule.Hom

section CommRing

variable {R C M N : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]
  [AddCommGroup N] [Module R N] [Comodule R C N]

attribute [local instance] Comodule.convolutionModule

/-- **Schur's lemma.** A nonzero comodule morphism between simple comodules over a projective
coalgebra is bijective. -/
theorem bijective_of_ne_zero [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] {f : Hom R C M N} (hf : f ≠ 0) :
    Function.Bijective f := by
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C M)›
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C N)›
  have hf' : f.toConvolutionLinearMap ≠ 0 := fun h ↦ hf <| by
    ext m
    simpa using LinearMap.congr_fun h m
  have hcoe : (f.toConvolutionLinearMap : M → N) = f := funext fun m ↦ by simp
  exact hcoe ▸ LinearMap.bijective_of_ne_zero (f := f.toConvolutionLinearMap) hf'

/-- Every comodule morphism between simple comodules over a projective coalgebra is either zero or
bijective. -/
theorem eq_zero_or_bijective [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] (f : Hom R C M N) :
    f = 0 ∨ Function.Bijective f :=
  (eq_or_ne f 0).imp_right bijective_of_ne_zero

end CommRing

section IsAlgClosed

variable {k C M : Type*} [Field k] [IsAlgClosed k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]

/-- **Schur's lemma over an algebraically closed field.** Every comodule endomorphism of a simple
comodule is a scalar multiple of the identity morphism. Simplicity over a field already forces
`M` to be finite dimensional. -/
theorem exists_eq_smul_id [IsSimpleOrder (Subcomodule k C M)] (f : Hom k C M M) :
    ∃ c : k, f = c • Hom.id k C M := by
  have : FiniteDimensional k M := Subcomodule.finite_of_isSimpleOrder (C := C)
  let ρ : Representation k (WithConv (Module.Dual k C)) M :=
    (convolutionAction (R := k) (C := C) (M := M)).toMonoidHom
  have : ρ.IsIrreducible := isIrreducible_convolutionAction
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_forall_apply_eq_smul (ρ := ρ)
    f.toLinearMap fun g m ↦ f.map_convolutionAction g m
  refine ⟨c, ?_⟩
  ext m
  exact hc m

end IsAlgClosed

end TauCeti.Comodule.Hom

namespace Module.Basis

open TauCeti TauCeti.Comodule

variable {k A M ι : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [Coalgebra k A]
  [AddCommGroup M] [Module k M] [Comodule k A M] [IsSimpleOrder (Subcomodule k A M)]
  [Fintype ι] [DecidableEq ι]

/-- **Matrix Schur's lemma.** Over an algebraically closed field, any scalar matrix intertwining
the coefficient matrix of a simple comodule with itself is a scalar multiple of the identity
matrix. -/
theorem exists_eq_smul_one_of_coefficientMatrix_mul_eq (b : Basis ι k M) {X : Matrix ι ι k}
    (hX : coefficientMatrix (C := A) b * X.map (algebraMap k A) =
      X.map (algebraMap k A) * coefficientMatrix (C := A) b) :
    ∃ c : k, X = c • 1 := by
  let f : Hom k A M M :=
    ⟨Matrix.toLin b b X, (b.map_coact_iff_coefficientMatrix b (Matrix.toLin b b X)).mpr
      (by simpa only [LinearMap.toMatrix_toLin] using hX)⟩
  obtain ⟨c, hc⟩ := f.exists_eq_smul_id
  refine ⟨c, ?_⟩
  have hlin : Matrix.toLin b b X = c • LinearMap.id := by
    simpa only [Hom.smul_toLinearMap, Hom.id_toLinearMap] using congrArg Hom.toLinearMap hc
  simpa only [LinearMap.toMatrix_toLin, map_smul, LinearMap.toMatrix_id] using
    congrArg (LinearMap.toMatrix b b) hlin

end Module.Basis
