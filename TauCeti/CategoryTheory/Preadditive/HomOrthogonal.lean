/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
public import TauCeti.CategoryTheory.Linear.Biproduct
public import TauCeti.CategoryTheory.Simple.Endomorphism
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Abelian structure from Hom-orthogonal biproduct decompositions

Let `C` be a preadditive category with finite biproducts and `X : ι → C` a Hom-orthogonal family
(`CategoryTheory.HomOrthogonal X`) such that every object of `C` is isomorphic to a finite
biproduct of members of `X`. By `CategoryTheory.HomOrthogonal.matrixDecomposition`, morphisms
between two such biproducts correspond to `ι`-indexed families of matrices with entries in the
endomorphism rings `End (X i)`.

When each `End (X i)` is a division ring (nontrivial, with every nonzero element a unit), each
matrix block represents a linear map between finite-dimensional vector spaces over `End (X i)`.
Kernels and cokernels of morphisms in `C` are realized as finite biproducts of the `X i` by
choosing bases of the blockwise cokernels and kernels, every monomorphism and epimorphism splits,
and `C` is therefore abelian (`CategoryTheory.HomOrthogonal.abelian`) and idempotent complete
(`CategoryTheory.HomOrthogonal.isIdempotentComplete`), with every `X i` simple
(`CategoryTheory.HomOrthogonal.simple`).

When `C` is `K`-linear over a semiring `K` and each `End (X i)` is module-finite over `K`, every
Hom module `Y ⟶ Z` in `C` is module-finite over `K`
(`CategoryTheory.HomOrthogonal.moduleFinite_hom`). In particular, when `K` is a field and each
endomorphism algebra satisfies `End (X i) ≃ₐ[K] K`, the category `C` is abelian with
finite-dimensional Hom spaces (`CategoryTheory.HomOrthogonal.abelianOfAlgEquiv`,
`CategoryTheory.HomOrthogonal.finiteDimensional_hom_of_algEquiv`).

## Main declarations

* `CategoryTheory.HomOrthogonal.hasCokernels` and `CategoryTheory.HomOrthogonal.hasKernels`:
  existence of cokernels and kernels from division-ring endomorphisms and finite biproduct
  decompositions.
* `CategoryTheory.HomOrthogonal.splitMonoCategory` and
  `CategoryTheory.HomOrthogonal.splitEpiCategory`: every monomorphism and epimorphism splits.
* `CategoryTheory.HomOrthogonal.abelian`: the resulting `Abelian C` structure.
* `CategoryTheory.HomOrthogonal.isIdempotentComplete` and `CategoryTheory.HomOrthogonal.simple`:
  idempotent completeness of `C` and simplicity of each `X i`.
* `CategoryTheory.HomOrthogonal.moduleFinite_hom`: module-finiteness of `Y ⟶ Z` when each
  `End (X i)` is module-finite over `K`.
* `CategoryTheory.HomOrthogonal.abelianOfAlgEquiv` and
  `CategoryTheory.HomOrthogonal.finiteDimensional_hom_of_algEquiv`: specializations to `K`-linear
  categories with scalar endomorphism algebras `End (X i) ≃ₐ[K] K`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §1.8.
* X.-W. Chen, *A note on standardly stratified algebras*, arXiv:1502.06845 (for recognizing
  semisimple abelian categories from additive generators with division endomorphism rings).
-/

public section

universe t w v u

namespace CategoryTheory.HomOrthogonal

open Limits Matrix

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι : Type w} {X : ι → C}

section BlockLinear

open scoped Classical in
/-- Reinterprets `HomOrthogonal.matrixDecompositionAddEquiv` via right matrix multiplication as a
blockwise family of left `End (X i)`-linear maps. -/
private noncomputable def homEquivBlockLinear (o : HomOrthogonal X) {α β : Type}
    [Fintype α] [Fintype β] {a : α → ι} {b : β → ι} :
    ((⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q)) ≃+
      ∀ i : ι, (b ⁻¹' {i} → End (X i)) →ₗ[End (X i)] (a ⁻¹' {i} → End (X i)) :=
  o.matrixDecompositionAddEquiv.trans
    (AddEquiv.piCongrRight fun _ ↦ Matrix.toLinearMapRight'.toAddEquiv)

open scoped Classical in
private theorem homEquivBlockLinear_id (o : HomOrthogonal X) {α : Type} [Fintype α]
    {a : α → ι} (i : ι) :
    homEquivBlockLinear o (𝟙 (⨁ fun p ↦ X (a p))) i = LinearMap.id := by
  change (o.matrixDecomposition (𝟙 (⨁ fun p ↦ X (a p))) i).toLinearMapRight' = LinearMap.id
  rw [o.matrixDecomposition_id]
  simp

open scoped Classical in
private theorem homEquivBlockLinear_comp (o : HomOrthogonal X) {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] {a : α → ι} {b : β → ι} {c : γ → ι}
    (f : (⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q))
    (g : (⨁ fun q ↦ X (b q)) ⟶ ⨁ fun r ↦ X (c r)) (i : ι) :
    homEquivBlockLinear o (f ≫ g) i =
      homEquivBlockLinear o f i ∘ₗ homEquivBlockLinear o g i := by
  change (o.matrixDecomposition (f ≫ g) i).toLinearMapRight' =
    (o.matrixDecomposition f i).toLinearMapRight' ∘ₗ (o.matrixDecomposition g i).toLinearMapRight'
  rw [o.matrixDecomposition_comp]
  simp

omit [HasFiniteBiproducts C] in
open scoped Classical in
/-- Realizes a finitely supported family of finite-dimensional left `End (X i)`-vector spaces as
the coordinate family `(c ⁻¹' {i} → End (X i))` of a finite `Type`-indexed map `c : γ → ι`. -/
private theorem exists_blockLinearEquiv [∀ i, Nontrivial (End (X i))]
    (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (W : ι → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module (End (X i)) (W i)]
    [∀ i, Module.Finite (End (X i)) (W i)]
    {μ : Type} [Finite μ] (m : μ → ι) (hsupp : ∀ i, i ∉ Set.range m → Subsingleton (W i)) :
    ∃ (γ : Type) (_ : Fintype γ) (c : γ → ι),
      Nonempty (∀ i : ι, W i ≃ₗ[End (X i)] (c ⁻¹' {i} → End (X i))) := by
  let _ := Fintype.ofFinite μ
  let divInst (i : ι) : DivisionRing (End (X i)) :=
    DivisionRing.ofIsUnitOrEqZero fun f ↦ or_iff_not_imp_right.mpr (hunit i f)
  let Q : Type := Quotient (Setoid.ker m)
  let m' : Q → ι := Quotient.lift m fun _ _ h ↦ h
  have hm' : Function.Injective m' := fun q₁ q₂ h ↦
    Quotient.inductionOn₂ q₁ q₂ (fun _ _ hxy ↦ Quotient.sound hxy) h
  have hrange : Set.range m' = Set.range m := by
    ext i
    exact ⟨fun ⟨q, hq⟩ ↦ by obtain ⟨x, rfl⟩ := Quotient.exists_rep q; exact ⟨x, hq⟩,
      fun ⟨x, hx⟩ ↦ ⟨⟦x⟧, hx⟩⟩
  let γ : Type := Σ q : Q, Fin (@Module.finrank (End (X (m' q))) (W (m' q))
    (divInst (m' q)).toSemiring _ _)
  let c : γ → ι := fun p ↦ m' p.1
  have hex (i : ι) : Nonempty (W i ≃ₗ[End (X i)] (c ⁻¹' {i} → End (X i))) := by
    by_cases hi : i ∈ Set.range m'
    · obtain ⟨q, rfl⟩ := hi
      let _ : DivisionRing (End (X (m' q))) := divInst (m' q)
      let eIdx : Fin (Module.finrank (End (X (m' q))) (W (m' q))) ≃ ↥(c ⁻¹' {m' q}) :=
        Equiv.ofBijective (fun k ↦ ⟨⟨q, k⟩, rfl⟩)
          ⟨fun _ _ h ↦ eq_of_heq (Sigma.mk.inj (Subtype.mk.inj h)).2,
            fun ⟨⟨q', k⟩, hq'⟩ ↦ by obtain rfl := hm' hq'; exact ⟨k, rfl⟩⟩
      exact ⟨(Module.finBasis (End (X (m' q))) (W (m' q))).equivFun.trans
        (LinearEquiv.funCongrLeft (End (X (m' q))) (End (X (m' q))) eIdx.symm)⟩
    · have : Subsingleton (W i) := hsupp i (hrange ▸ hi)
      have : IsEmpty ↥(c ⁻¹' {i}) := ⟨fun ⟨p, hp⟩ ↦ hi ⟨p.1, hp⟩⟩
      exact ⟨{ toFun := 0, invFun := 0,
               map_add' := fun _ _ ↦ Subsingleton.elim _ _,
               map_smul' := fun _ _ ↦ Subsingleton.elim _ _,
               left_inv := fun _ ↦ Subsingleton.elim _ _,
               right_inv := fun _ ↦ Subsingleton.elim _ _ }⟩
  exact ⟨γ, inferInstance, c, ⟨fun i ↦ (hex i).some⟩⟩

end BlockLinear

section DivisionEnd

variable [∀ i, Nontrivial (End (X i))]

open scoped Classical in
/-- Between two finite biproducts of `X`, blockwise kernels of the associated linear maps give a
categorical cokernel together with its coordinate description. -/
private theorem exists_cokernel_biproduct (o : HomOrthogonal X)
    (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    {α β : Type} [Fintype α] [Fintype β] {a : α → ι} {b : β → ι}
    (f : (⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q)) :
    ∃ (γ : Type) (_ : Fintype γ) (c : γ → ι)
      (e : ∀ i, ↥(LinearMap.ker (homEquivBlockLinear o f i)) ≃ₗ[End (X i)]
        (c ⁻¹' {i} → End (X i)))
      (π : (⨁ fun q ↦ X (b q)) ⟶ ⨁ fun r ↦ X (c r)) (_ : f ≫ π = 0),
      (∀ i, homEquivBlockLinear o π i =
        (LinearMap.ker (homEquivBlockLinear o f i)).subtype ∘ₗ (e i).symm.toLinearMap) ∧
      (∀ {δ : Type} [Fintype δ] {d : δ → ι}
        (h : (⨁ fun q ↦ X (b q)) ⟶ ⨁ fun s ↦ X (d s)), f ≫ h = 0 →
        ∃! u : (⨁ fun r ↦ X (c r)) ⟶ ⨁ fun s ↦ X (d s), π ≫ u = h) := by
  let divInst (i : ι) : DivisionRing (End (X i)) :=
    DivisionRing.ofIsUnitOrEqZero fun g ↦ or_iff_not_imp_right.mpr (hunit i g)
  have hfin (i : ι) : Module.Finite (End (X i)) ↥(LinearMap.ker (homEquivBlockLinear o f i)) :=
    let _ : DivisionRing (End (X i)) := divInst i
    inferInstance
  have hsupp (i : ι) (hi : i ∉ Set.range b) :
      Subsingleton ↥(LinearMap.ker (homEquivBlockLinear o f i)) := by
    have : IsEmpty ↥(b ⁻¹' {i}) := ⟨fun ⟨q, hq⟩ ↦ hi ⟨q, hq⟩⟩
    infer_instance
  obtain ⟨γ, hγ, c, ⟨e⟩⟩ := exists_blockLinearEquiv hunit
    (fun i ↦ ↥(LinearMap.ker (homEquivBlockLinear o f i))) b hsupp
  let π : (⨁ fun q ↦ X (b q)) ⟶ ⨁ fun r ↦ X (c r) :=
    (homEquivBlockLinear o).symm fun i ↦
      (LinearMap.ker (homEquivBlockLinear o f i)).subtype ∘ₗ (e i).symm.toLinearMap
  have hπ_coord (i : ι) : homEquivBlockLinear o π i =
      (LinearMap.ker (homEquivBlockLinear o f i)).subtype ∘ₗ (e i).symm.toLinearMap :=
    congrFun ((homEquivBlockLinear o).apply_symm_apply _) i
  have hπ : f ≫ π = 0 := (homEquivBlockLinear o).injective <|
    funext fun i ↦ LinearMap.ext fun v ↦ by
      simp [homEquivBlockLinear_comp, hπ_coord]
  refine ⟨γ, hγ, c, e, π, hπ, hπ_coord, fun {δ} _ {d} h fh ↦ ?_⟩
  have hmem (i : ι) (v : d ⁻¹' {i} → End (X i)) :
      homEquivBlockLinear o h i v ∈ LinearMap.ker (homEquivBlockLinear o f i) := by
    have h0 := congrFun (congrArg DFunLike.coe
      (congrFun (congrArg (homEquivBlockLinear o) fh) i)) v
    simpa [homEquivBlockLinear_comp] using h0
  let u : (⨁ fun r ↦ X (c r)) ⟶ ⨁ fun s ↦ X (d s) :=
    (homEquivBlockLinear o).symm fun i ↦
      (e i).toLinearMap ∘ₗ (homEquivBlockLinear o h i).codRestrict _ (hmem i)
  have hu_eq : π ≫ u = h := (homEquivBlockLinear o).injective <|
    funext fun i ↦ LinearMap.ext fun v ↦ by
      have hu_coord : homEquivBlockLinear o u i =
          (e i).toLinearMap ∘ₗ (homEquivBlockLinear o h i).codRestrict _ (hmem i) :=
        congrFun ((homEquivBlockLinear o).apply_symm_apply _) i
      simp [homEquivBlockLinear_comp, hπ_coord, hu_coord]
  refine ⟨u, hu_eq, fun u' hu' ↦ (homEquivBlockLinear o).injective ?_⟩
  refine funext fun i ↦ LinearMap.ext fun v ↦ ?_
  have hcomp := congrFun (congrArg DFunLike.coe
    (congrFun (congrArg (homEquivBlockLinear o) (hu'.trans hu_eq.symm)) i)) v
  simp only [homEquivBlockLinear_comp, hπ_coord, LinearMap.comp_apply,
    Submodule.coe_subtype] at hcomp
  exact (e i).symm.injective (Subtype.ext hcomp)

open scoped Classical in
/-- Between two finite biproducts of `X`, blockwise quotients by the ranges of the associated
linear maps give a categorical kernel together with its coordinate description. -/
private theorem exists_kernel_biproduct (o : HomOrthogonal X)
    (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    {α β : Type} [Fintype α] [Fintype β] {a : α → ι} {b : β → ι}
    (f : (⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q)) :
    ∃ (γ : Type) (_ : Fintype γ) (c : γ → ι)
      (e : ∀ i,
        ((a ⁻¹' {i} → End (X i)) ⧸ LinearMap.range (homEquivBlockLinear o f i)) ≃ₗ[End (X i)]
          (c ⁻¹' {i} → End (X i)))
      (ιf : (⨁ fun r ↦ X (c r)) ⟶ ⨁ fun p ↦ X (a p)) (_ : ιf ≫ f = 0),
      (∀ i, homEquivBlockLinear o ιf i =
        (e i).toLinearMap ∘ₗ (LinearMap.range (homEquivBlockLinear o f i)).mkQ) ∧
      (∀ {δ : Type} [Fintype δ] {d : δ → ι}
        (k : (⨁ fun s ↦ X (d s)) ⟶ ⨁ fun p ↦ X (a p)), k ≫ f = 0 →
        ∃! u : (⨁ fun s ↦ X (d s)) ⟶ ⨁ fun r ↦ X (c r), u ≫ ιf = k) := by
  have hsupp (i : ι) (hi : i ∉ Set.range a) :
      Subsingleton ((a ⁻¹' {i} → End (X i)) ⧸ LinearMap.range (homEquivBlockLinear o f i)) := by
    have : IsEmpty ↥(a ⁻¹' {i}) := ⟨fun ⟨p, hp⟩ ↦ hi ⟨p, hp⟩⟩
    infer_instance
  obtain ⟨γ, hγ, c, ⟨e⟩⟩ := exists_blockLinearEquiv hunit
    (fun i ↦ (a ⁻¹' {i} → End (X i)) ⧸ LinearMap.range (homEquivBlockLinear o f i)) a hsupp
  let ιf : (⨁ fun r ↦ X (c r)) ⟶ ⨁ fun p ↦ X (a p) :=
    (homEquivBlockLinear o).symm fun i ↦
      (e i).toLinearMap ∘ₗ (LinearMap.range (homEquivBlockLinear o f i)).mkQ
  have hι_coord (i : ι) : homEquivBlockLinear o ιf i =
      (e i).toLinearMap ∘ₗ (LinearMap.range (homEquivBlockLinear o f i)).mkQ :=
    congrFun ((homEquivBlockLinear o).apply_symm_apply _) i
  have hι : ιf ≫ f = 0 := (homEquivBlockLinear o).injective <|
    funext fun i ↦ LinearMap.ext fun v ↦ by
      simp [homEquivBlockLinear_comp, hι_coord]
  refine ⟨γ, hγ, c, e, ιf, hι, hι_coord, fun {δ} _ {d} k kf ↦ ?_⟩
  have hle (i : ι) : LinearMap.range (homEquivBlockLinear o f i) ≤
      LinearMap.ker (homEquivBlockLinear o k i) := by
    rintro _ ⟨v, rfl⟩
    have h0 := congrFun (congrArg DFunLike.coe
      (congrFun (congrArg (homEquivBlockLinear o) kf) i)) v
    simpa [homEquivBlockLinear_comp] using h0
  let u : (⨁ fun s ↦ X (d s)) ⟶ ⨁ fun r ↦ X (c r) :=
    (homEquivBlockLinear o).symm fun i ↦
      (LinearMap.range (homEquivBlockLinear o f i)).liftQ (homEquivBlockLinear o k i) (hle i) ∘ₗ
        (e i).symm.toLinearMap
  have hu_eq : u ≫ ιf = k := (homEquivBlockLinear o).injective <|
    funext fun i ↦ LinearMap.ext fun v ↦ by
      have hu_coord : homEquivBlockLinear o u i =
          (LinearMap.range (homEquivBlockLinear o f i)).liftQ (homEquivBlockLinear o k i) (hle i) ∘ₗ
            (e i).symm.toLinearMap :=
        congrFun ((homEquivBlockLinear o).apply_symm_apply _) i
      simp [homEquivBlockLinear_comp, hι_coord, hu_coord]
  refine ⟨u, hu_eq, fun u' hu' ↦ (homEquivBlockLinear o).injective ?_⟩
  refine funext fun i ↦ LinearMap.ext fun w ↦ ?_
  obtain ⟨v, rfl⟩ := (e i).surjective w
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ v
  have hcomp := congrFun (congrArg DFunLike.coe
    (congrFun (congrArg (homEquivBlockLinear o) (hu'.trans hu_eq.symm)) i)) x
  simpa [homEquivBlockLinear_comp, hι_coord] using hcomp

/-- A category in which every object is a finite biproduct of a Hom-orthogonal family with
division endomorphism rings has cokernels. -/
theorem hasCokernels (o : HomOrthogonal X) (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    HasCokernels C := by
  classical
  refine ⟨fun {Y Z} g ↦ ?_⟩
  obtain ⟨α, _, a, ⟨eY⟩⟩ := hgen Y
  obtain ⟨β, _, b, ⟨eZ⟩⟩ := hgen Z
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  let f : (⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q) := eY.inv ≫ g ≫ eZ.hom
  obtain ⟨γ, _, c, _, π, hπ, _, huniv⟩ := exists_cokernel_biproduct o hunit f
  have hf : HasCokernel f := ⟨⟨⟨CokernelCofork.ofπ π hπ,
    Cofork.IsColimit.mk' _ fun s ↦ Classical.choice <| by
      obtain ⟨δ, _, d, ⟨eW⟩⟩ := hgen s.pt
      let _ := Fintype.ofFinite δ
      obtain ⟨u, hu, huniq⟩ := huniv (s.π ≫ eW.hom) (by simp [reassoc_of% s.condition])
      refine ⟨⟨u ≫ eW.inv, ?_, fun {m} hm ↦ ?_⟩⟩
      · simp [reassoc_of% hu]
      · have hm' : π ≫ (m ≫ eW.hom) = s.π ≫ eW.hom := by
          rw [← Category.assoc]; exact congrArg (· ≫ eW.hom) hm
        simpa using huniq (m ≫ eW.hom) hm' =≫ eW.inv⟩⟩⟩
  have h1 : HasCokernel (eY.hom ≫ f) := hasCokernel_epi_comp f eY.hom
  have h2 : HasCokernel ((eY.hom ≫ f) ≫ eZ.inv) := hasCokernel_comp_iso (eY.hom ≫ f) eZ.inv
  have hg : (eY.hom ≫ f) ≫ eZ.inv = g := by simp [f]
  exact hg ▸ h2

/-- A category in which every object is a finite biproduct of a Hom-orthogonal family with
division endomorphism rings has kernels. -/
theorem hasKernels (o : HomOrthogonal X) (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    HasKernels C := by
  classical
  refine ⟨fun {Y Z} g ↦ ?_⟩
  obtain ⟨α, _, a, ⟨eY⟩⟩ := hgen Y
  obtain ⟨β, _, b, ⟨eZ⟩⟩ := hgen Z
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  let f : (⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q) := eY.inv ≫ g ≫ eZ.hom
  obtain ⟨γ, _, c, _, ιf, hι, _, huniv⟩ := exists_kernel_biproduct o hunit f
  have hf : HasKernel f := ⟨⟨⟨KernelFork.ofι ιf hι,
    Fork.IsLimit.mk' _ fun s ↦ Classical.choice <| by
      obtain ⟨δ, _, d, ⟨eW⟩⟩ := hgen s.pt
      let _ := Fintype.ofFinite δ
      obtain ⟨u, hu, huniq⟩ := huniv (eW.inv ≫ s.ι) (by simp [s.condition])
      refine ⟨⟨eW.hom ≫ u, ?_, fun {m} hm ↦ ?_⟩⟩
      · simp [hu]
      · have hm' : (eW.inv ≫ m) ≫ ιf = eW.inv ≫ s.ι := by
          rw [Category.assoc]; exact congrArg (eW.inv ≫ ·) hm
        simpa using eW.hom ≫= huniq (eW.inv ≫ m) hm'⟩⟩⟩
  have h1 : HasKernel (f ≫ eZ.inv) := hasKernel_comp_mono f eZ.inv
  have h2 : HasKernel (eY.hom ≫ (f ≫ eZ.inv)) := hasKernel_iso_comp eY.hom (f ≫ eZ.inv)
  have hg : eY.hom ≫ (f ≫ eZ.inv) = g := by simp [f]
  exact hg ▸ h2

/-- Every monomorphism splits in a category where every object is a finite biproduct of a
Hom-orthogonal family with division endomorphism rings. -/
theorem splitMonoCategory (o : HomOrthogonal X) (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    SplitMonoCategory C := by
  classical
  refine ⟨fun {Y Z} g _ ↦ ?_⟩
  obtain ⟨α, _, a, ⟨eY⟩⟩ := hgen Y
  obtain ⟨β, _, b, ⟨eZ⟩⟩ := hgen Z
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  let f : (⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q) := eY.inv ≫ g ≫ eZ.hom
  have : Mono f := mono_comp _ _
  obtain ⟨γ, _, c, e, ιf, hι, hι_coord, _⟩ := exists_kernel_biproduct o hunit f
  have hι0 : ιf = 0 := (cancel_mono f).1 (by simp [hι])
  have hsurj (i : ι) : LinearMap.range (homEquivBlockLinear o f i) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    apply (e i).injective
    have h0 := congrFun (congrArg DFunLike.coe
      (congrFun (congrArg (homEquivBlockLinear o) hι0) i)) v
    simpa [hι_coord] using h0
  let divInst (i : ι) : DivisionRing (End (X i)) :=
    DivisionRing.ofIsUnitOrEqZero fun h ↦ or_iff_not_imp_right.mpr (hunit i h)
  have hrinv (i : ι) :
      ∃ r : (a ⁻¹' {i} → End (X i)) →ₗ[End (X i)] (b ⁻¹' {i} → End (X i)),
        homEquivBlockLinear o f i ∘ₗ r = LinearMap.id := by
    let _ : DivisionRing (End (X i)) := divInst i
    exact (homEquivBlockLinear o f i).exists_rightInverse_of_surjective (hsurj i)
  let r₀ : (⨁ fun q ↦ X (b q)) ⟶ ⨁ fun p ↦ X (a p) :=
    (homEquivBlockLinear o).symm fun i ↦ (hrinv i).choose
  have hfr₀ : f ≫ r₀ = 𝟙 _ := (homEquivBlockLinear o).injective <|
    funext fun i ↦ LinearMap.ext fun v ↦ by
      have hr_coord : homEquivBlockLinear o r₀ i = (hrinv i).choose :=
        congrFun ((homEquivBlockLinear o).apply_symm_apply _) i
      have hspec := congrFun (congrArg DFunLike.coe (hrinv i).choose_spec) v
      simpa [homEquivBlockLinear_comp, homEquivBlockLinear_id, hr_coord] using hspec
  refine IsSplitMono.mk' ⟨eZ.hom ≫ r₀ ≫ eY.inv, ?_⟩
  calc
    g ≫ eZ.hom ≫ r₀ ≫ eY.inv = eY.hom ≫ (f ≫ r₀) ≫ eY.inv := by simp [f]
    _ = 𝟙 Y := by simp [hfr₀]

/-- Every epimorphism splits in a category where every object is a finite biproduct of a
Hom-orthogonal family with division endomorphism rings. -/
theorem splitEpiCategory (o : HomOrthogonal X) (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    SplitEpiCategory C := by
  classical
  refine ⟨fun {Y Z} g _ ↦ ?_⟩
  obtain ⟨α, _, a, ⟨eY⟩⟩ := hgen Y
  obtain ⟨β, _, b, ⟨eZ⟩⟩ := hgen Z
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  let f : (⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q) := eY.inv ≫ g ≫ eZ.hom
  have : Epi f := epi_comp _ _
  obtain ⟨γ, _, c, e, π, hπ, hπ_coord, _⟩ := exists_cokernel_biproduct o hunit f
  have hπ0 : π = 0 := (cancel_epi f).1 (by simp [hπ])
  have hinj (i : ι) : LinearMap.ker (homEquivBlockLinear o f i) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h0 := congrFun (congrArg DFunLike.coe
      (congrFun (congrArg (homEquivBlockLinear o) hπ0) i)) (e i ⟨x, hx⟩)
    simpa [hπ_coord] using h0
  let divInst (i : ι) : DivisionRing (End (X i)) :=
    DivisionRing.ofIsUnitOrEqZero fun h ↦ or_iff_not_imp_right.mpr (hunit i h)
  have hlinv (i : ι) :
      ∃ s : (a ⁻¹' {i} → End (X i)) →ₗ[End (X i)] (b ⁻¹' {i} → End (X i)),
        s ∘ₗ homEquivBlockLinear o f i = LinearMap.id := by
    let _ : DivisionRing (End (X i)) := divInst i
    exact (homEquivBlockLinear o f i).exists_leftInverse_of_injective (hinj i)
  let s₀ : (⨁ fun q ↦ X (b q)) ⟶ ⨁ fun p ↦ X (a p) :=
    (homEquivBlockLinear o).symm fun i ↦ (hlinv i).choose
  have hs₀f : s₀ ≫ f = 𝟙 _ := (homEquivBlockLinear o).injective <|
    funext fun i ↦ LinearMap.ext fun v ↦ by
      have hs_coord : homEquivBlockLinear o s₀ i = (hlinv i).choose :=
        congrFun ((homEquivBlockLinear o).apply_symm_apply _) i
      have hspec := congrFun (congrArg DFunLike.coe (hlinv i).choose_spec) v
      simpa [homEquivBlockLinear_comp, homEquivBlockLinear_id, hs_coord] using hspec
  refine IsSplitEpi.mk' ⟨eZ.hom ≫ s₀ ≫ eY.inv, ?_⟩
  calc
    (eZ.hom ≫ s₀ ≫ eY.inv) ≫ g = eZ.hom ≫ (s₀ ≫ f) ≫ eZ.inv := by simp [f]
    _ = 𝟙 Z := by simp [hs₀f]

/-- A preadditive category with finite biproducts in which every object is a finite biproduct of a
Hom-orthogonal family with division endomorphism rings is abelian. -/
@[instance_reducible]
noncomputable def abelian (o : HomOrthogonal X) (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    Abelian C :=
  let _ : HasKernels C := o.hasKernels hunit hgen
  let _ : HasCokernels C := o.hasCokernels hunit hgen
  let _ : SplitMonoCategory C := o.splitMonoCategory hunit hgen
  let _ : SplitEpiCategory C := o.splitEpiCategory hunit hgen
  let _ : IsNormalMonoCategory C :=
    ⟨fun {Y Z} f _ ↦
      have := isSplitMono_of_mono f
      ⟨{ Z := Z
         g := 𝟙 Z - retraction f ≫ f
         w := by simp
         isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι ≫ retraction f)
           (fun s ↦ by
             have hs := s.condition
             rw [Preadditive.comp_sub, Category.comp_id, comp_zero, sub_eq_zero,
               ← Category.assoc] at hs
             simpa using hs.symm)
           (fun s m hm ↦ by simpa using hm =≫ retraction f) }⟩⟩
  let _ : IsNormalEpiCategory C :=
    ⟨fun {Y Z} f _ ↦
      have := isSplitEpi_of_epi f
      ⟨{ W := Y
         g := 𝟙 Y - f ≫ section_ f
         w := by simp
         isColimit := Cofork.IsColimit.mk _ (fun s ↦ section_ f ≫ s.π)
           (fun s ↦ by
             have hs := s.condition
             rw [Preadditive.sub_comp, Category.id_comp, zero_comp, sub_eq_zero,
               Category.assoc] at hs
             simpa using hs.symm)
           (fun s m hm ↦ by simpa [← Category.assoc] using section_ f ≫= hm) }⟩⟩
  let _ : HasFiniteProducts C := hasFiniteProducts_of_hasFiniteBiproducts C
  { }

/-- Under the hypotheses of `CategoryTheory.HomOrthogonal.abelian`, the category `C` is idempotent
complete. -/
theorem isIdempotentComplete (o : HomOrthogonal X) (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    IsIdempotentComplete C := by
  let _ : Abelian C := o.abelian hunit hgen
  exact Idempotents.isIdempotentComplete_of_abelian C

/-- Under the hypotheses of `CategoryTheory.HomOrthogonal.abelian`, every member `X i` of the
generating Hom-orthogonal family is simple. -/
theorem simple (o : HomOrthogonal X) (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) (i : ι) :
    Simple (X i) := by
  have := o.splitMonoCategory hunit hgen
  have : ∀ Y : C, Injective Y := fun _ ↦
    ⟨fun g f _ ↦
      have := isSplitMono_of_mono f
      ⟨retraction f ≫ g, by rw [← Category.assoc, IsSplitMono.id, Category.id_comp]⟩⟩
  exact simple_of_nontrivial_end_of_isUnit (X i) (hunit i)

end DivisionEnd

section Linear

/-- If every object is a finite biproduct of a Hom-orthogonal family `X` whose endomorphism modules
are finite over `K`, then every Hom module `Y ⟶ Z` is finite over `K`. -/
theorem moduleFinite_hom (o : HomOrthogonal X) (K : Type t) [Semiring K] [Linear K C]
    [∀ i, Module.Finite K (End (X i))]
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p)))
    (Y Z : C) :
    Module.Finite K (Y ⟶ Z) := by
  have hXX (i j : ι) : Module.Finite K (X i ⟶ X j) := by
    by_cases hij : i = j
    · subst hij
      exact Module.Finite.equiv (End.linearEquiv (R := K) (X := X i))
    · have : Subsingleton (X i ⟶ X j) := o hij
      infer_instance
  obtain ⟨α, _, a, ⟨eY⟩⟩ := hgen Y
  obtain ⟨β, _, b, ⟨eZ⟩⟩ := hgen Z
  have h1 (p : α) : Module.Finite K (X (a p) ⟶ ⨁ fun q ↦ X (b q)) :=
    TauCeti.moduleFinite_homTo_biproduct K (fun q ↦ X (b q)) (X (a p))
  have h2 : Module.Finite K ((⨁ fun p ↦ X (a p)) ⟶ ⨁ fun q ↦ X (b q)) :=
    TauCeti.moduleFinite_hom_biproduct K (fun p ↦ X (a p)) (⨁ fun q ↦ X (b q))
  exact Module.Finite.equiv (CategoryTheory.Linear.homCongr K eY eZ).symm

/-- A `K`-linear preadditive category with finite biproducts in which every object is a finite
biproduct of a Hom-orthogonal family `X` with `End (X i) ≃ₐ[K] K` over a field `K` is abelian. -/
@[instance_reducible]
noncomputable def abelianOfAlgEquiv (o : HomOrthogonal X) (K : Type t) [Field K] [Linear K C]
    (hend : ∀ i, Nonempty (End (X i) ≃ₐ[K] K))
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    Abelian C :=
  let _ (i : ι) : Nontrivial (End (X i)) := (hend i).some.toEquiv.nontrivial
  o.abelian
    (fun i f hf ↦ by
      let e := (hend i).some
      have hne : e f ≠ 0 := by simpa using hf
      simpa using (isUnit_iff_ne_zero.mpr hne).map e.symm.toMonoidHom)
    hgen

/-- Under the hypotheses of `CategoryTheory.HomOrthogonal.abelianOfAlgEquiv`, the category `C` is
idempotent complete. -/
theorem isIdempotentComplete_of_algEquiv (o : HomOrthogonal X) (K : Type t) [Field K] [Linear K C]
    (hend : ∀ i, Nonempty (End (X i) ≃ₐ[K] K))
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    IsIdempotentComplete C := by
  let _ : Abelian C := o.abelianOfAlgEquiv K hend hgen
  exact Idempotents.isIdempotentComplete_of_abelian C

/-- Under the hypotheses of `CategoryTheory.HomOrthogonal.abelianOfAlgEquiv`, each member `X i` of
the generating Hom-orthogonal family is simple. -/
theorem simple_of_algEquiv (o : HomOrthogonal X) (K : Type t) [Field K] [Linear K C]
    (hend : ∀ i, Nonempty (End (X i) ≃ₐ[K] K))
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) (i : ι) :
    Simple (X i) := by
  let _ (j : ι) : Nontrivial (End (X j)) := (hend j).some.toEquiv.nontrivial
  exact o.simple
    (fun j f hf ↦ by
      let e := (hend j).some
      have hne : e f ≠ 0 := by simpa using hf
      simpa using (isUnit_iff_ne_zero.mpr hne).map e.symm.toMonoidHom)
    hgen i

/-- Under the hypotheses of `CategoryTheory.HomOrthogonal.abelianOfAlgEquiv`, every Hom space
`Y ⟶ Z` is finite-dimensional over `K`. -/
theorem finiteDimensional_hom_of_algEquiv (o : HomOrthogonal X) (K : Type t) [Field K]
    [Linear K C] (hend : ∀ i, Nonempty (End (X i) ≃ₐ[K] K))
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p)))
    (Y Z : C) :
    FiniteDimensional K (Y ⟶ Z) := by
  have _ (i : ι) : Module.Finite K (End (X i)) :=
    Module.Finite.equiv (hend i).some.symm.toLinearEquiv
  exact o.moduleFinite_hom K hgen Y Z

end Linear

end CategoryTheory.HomOrthogonal
