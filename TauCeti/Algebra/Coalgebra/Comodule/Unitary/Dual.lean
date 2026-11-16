/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Basic
public import TauCeti.Algebra.Coalgebra.Star

/-!
# Duals and entrywise conjugates of unitary comodules

When a finite free comodule `M` over a Hopf algebra `A` with a star structure has a unitary
coefficient matrix `u` in a basis `b`, its antipode transform `u.map S` coincides with the
conjugate transpose `uᴴ`. Combining this with the general dual-basis formula `(u.map S)ᵀ` shows
that Tau Ceti's explicit dual comodule `Module.Dual R M` has coefficient matrix `u.map star` — the
entrywise star `ū`, distinct from the conjugate transpose `uᴴ` — in the dual basis `b.dualBasis`.

Over a star coalgebra (`TauCeti.StarCoalgebra`), the entrywise star `u.map star` of any coefficient
matrix again satisfies the comultiplication and counit equations of a multiplicative matrix.

## Main declarations

* `Module.Basis.map_antipode_coefficientMatrix_of_mem_unitary`: for a unitary coefficient matrix,
  the entrywise antipode equals the conjugate transpose.
* `Module.Basis.coefficientMatrix_dualBasis_of_mem_unitary`: in the dual basis, the dual comodule
  has the entrywise star `u.map star` as its coefficient matrix.
* `TauCeti.Comodule.IsUnitary.coefficientMatrix_dualBasis`: the orthonormal-basis specialization
  for a unitary comodule.
* `TauCeti.Comodule.comul_star_coefficientMatrix_eq_sum` and
  `TauCeti.Comodule.counit_star_coefficientMatrix`: the coalgebra laws for `u.map star`.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Section 1.3.
-/

public section

open Module TauCeti TauCeti.Comodule
open scoped Matrix TensorProduct

namespace Module.Basis

section Hopf

variable {R A M ι : Type*} [CommSemiring R] [Semiring A] [StarRing A]
  [HopfAlgebra R A] [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι]

/-- If the coefficient matrix of a finite basis of a Hopf comodule is unitary, its entrywise
antipode image is its conjugate transpose. No inner product on `M` or star-coalgebra assumption on
`A` is required. -/
theorem map_antipode_coefficientMatrix_of_mem_unitary [DecidableEq ι] (b : Basis ι R M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R) =
      (coefficientMatrix (C := A) b)ᴴ := by
  have hu' : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  exact left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) hu'

attribute [local instance] TauCeti.Comodule.dual

/-- If the coefficient matrix `u` of a finite basis `b` is unitary, then the dual comodule has the
entrywise star `u.map star` as its coefficient matrix in the dual basis `b.dualBasis`. -/
theorem coefficientMatrix_dualBasis_of_mem_unitary [Module.Finite R M] [Module.Projective R M]
    [DecidableEq ι] (b : Basis ι R M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    coefficientMatrix (C := A) b.dualBasis = (coefficientMatrix (C := A) b).map star := by
  rw [b.coefficientMatrix_dualBasis, b.map_antipode_coefficientMatrix_of_mem_unitary hu]
  ext i j
  rfl

end Hopf

end Module.Basis

namespace TauCeti.Comodule

section UnitaryDual

variable {𝕜 A M ι : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [HopfAlgebra 𝕜 A]
  [StarModule 𝕜 A] [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [Comodule 𝕜 A M]
  [FiniteDimensional 𝕜 M] [Fintype ι]

attribute [local instance] Comodule.dual

/-- In the dual basis of any orthonormal basis, the linear dual of a finite unitary Hopf comodule
has the entrywise star of the original coefficient matrix as its coefficient matrix. -/
theorem IsUnitary.coefficientMatrix_dualBasis [DecidableEq ι] (hM : IsUnitary 𝕜 A M)
    (b : OrthonormalBasis ι 𝕜 M) :
    coefficientMatrix (C := A) b.toBasis.dualBasis =
      (coefficientMatrix (C := A) b.toBasis).map star :=
  b.toBasis.coefficientMatrix_dualBasis_of_mem_unitary (hM.coefficientMatrix_mem_unitary b)

end UnitaryDual

section StarCoalgebra

variable {R A M ι : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
  [Module R A] [StarModule R A] [Coalgebra R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M]

/-- In a star coalgebra, the entrywise star of a coefficient matrix satisfies the matrix
comultiplication identity. -/
theorem comul_star_coefficientMatrix_eq_sum [Fintype ι] (b : Basis ι R M) (i j : ι) :
    Coalgebra.comul (R := R) (star (coefficientMatrix (C := A) b i j)) =
      ∑ k, star (coefficientMatrix (C := A) b i k) ⊗ₜ[R]
        star (coefficientMatrix (C := A) b k j) := by
  rw [StarCoalgebra.comul_star, comul_coefficientMatrix_eq_sum, star_sum]
  rfl

/-- In a star coalgebra, the entrywise star of a coefficient matrix satisfies the matrix counit
identity. -/
theorem counit_star_coefficientMatrix [DecidableEq ι] (b : Basis ι R M) (i j : ι) :
    Coalgebra.counit (R := R) (star (coefficientMatrix (C := A) b i j)) =
      if i = j then 1 else 0 := by
  rw [StarCoalgebra.counit_star, counit_coefficientMatrix]
  split_ifs <;> simp

end StarCoalgebra

end TauCeti.Comodule
