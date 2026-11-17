/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Basic
public import TauCeti.RepresentationTheory.Continuous.TopRep.Subquotients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.Basic
import TauCeti.Topology.Discrete

/-!
# Inverse limits of inhomogeneous continuous cochains

For a tower `T : ℕᵒᵖ ⥤ TopRep R G` of topological `G`-representations with jointly continuous
actions, the inhomogeneous continuous cochain complexes `inhomogeneousCochains (T.obj n)` assemble
into a tower of cochain complexes `inhomogeneousCochainsTower T hT : ComplexTower R (.up ℕ)`.
Whenever `c : Limits.Cone T` is a limit cone in `TopRep R G`, the induced action on `c.pt` is
jointly continuous (`continuous_ρ_of_isLimit`) and the inhomogeneous cochain complex of the limit
is canonically isomorphic to the limit complex of the cochain tower (`inhomogeneousCochainsLimIso`):

`C•(G, lim Tₙ) ≅ lim C•(G, Tₙ)`.

When every level `Tₙ` carries the discrete topology and every transition map `Tₙ₊₁ → Tₙ` is
surjective, `TauCeti.exists_continuous_lift` implies that every transition on continuous cochains
`Cⁱ(G, Tₙ₊₁) → Cⁱ(G, Tₙ)` is surjective (`inhomogeneousCochainsTower_transition_surjective`), for an
arbitrary topological group `G`. Consequently `lim¹` vanishes on cochains in every degree, the
product-complex sequence `0 → lim C• → ∏ C• → ∏ C• → 0` is short exact
(`inhomogeneousCochainsTower_shortComplex_shortExact`), and the Milnor exact sequence holds on the
cohomology of inhomogeneous continuous cochains:

`0 → lim¹ Hⁿ(C•(G, Tₖ)) → Hⁿ⁺¹(C•(G, lim Tₖ)) → lim Hⁿ⁺¹(C•(G, Tₖ)) → 0`.

## Main definitions

* `TauCeti.ContinuousCohomology.limTopRep`, `TauCeti.ContinuousCohomology.limTopRepCone`: the
  explicit subspace-of-product limit of a tower in `TopRep R G`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsTower`: the `ComplexTower` of inhomogeneous
  continuous cochains attached to a tower in `TopRep R G`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsLimIso`: the canonical isomorphism
  `inhomogeneousCochains c.pt _ ≅ (inhomogeneousCochainsTower T hT).limComplex` for any limit cone
  `c` of `T`.
* `TauCeti.ContinuousCohomology.inhomogeneousHomologyToLim`,
  `TauCeti.ContinuousCohomology.inhomogeneousLimOneToHomology`: the two maps of the Milnor exact
  sequence on inhomogeneous cohomology.

## Main results

* `TauCeti.ContinuousCohomology.isLimitOfIsEmbeddingRange`,
  `TauCeti.ContinuousCohomology.isEmbedding_of_isLimit`,
  `TauCeti.ContinuousCohomology.range_of_isLimit`: characterization of sequential limit cones in
  `TopRep R G` via topological embeddings onto the compatible-tuple locus.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsTower_transition_surjective` and
  `TauCeti.ContinuousCohomology.inhomogeneousCochainsTower_shortComplex_shortExact`: surjective
  transitions on discrete coefficients induce surjective cochain transitions and short exactness of
  the Milnor product-complex sequence.
* `TauCeti.ContinuousCohomology.inhomogeneousLimOneToHomology_injective`,
  `TauCeti.ContinuousCohomology.exact_inhomogeneousLimOneToHomology_inhomogeneousHomologyToLim`,
  `TauCeti.ContinuousCohomology.inhomogeneousHomologyToLim_surjective`,
  `TauCeti.ContinuousCohomology.inhomogeneousHomologyToLim_bijective_zero`,
  `TauCeti.ContinuousCohomology.inhomogeneousHomologyToLim_bijective_succ`: the Milnor short exact
  sequence and `lim¹ = 0` isomorphism criterion for inhomogeneous continuous cochains.
* `TauCeti.ContinuousCohomology.isZero_limComplex_homology_succ_of_subsingleton` and
  `TauCeti.ContinuousCohomology.isZero_limComplex_of_transition_eq_zero`: vanishing checks for a
  trivial group and for towers with zero transition maps.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.ContinuousCohomology

universe u v w

/-! ### Sequential limits in `TopRep R G` -/

section TopRepLimits

variable {R : Type u} [Ring R] [TopologicalSpace R] {G : Type v} [Monoid G]

/-- The compatible-tuple locus of a tower `T : ℕᵒᵖ ⥤ TopRep R G` inside `∀ n, (T.obj (op n)).V`. -/
@[expose]
def limTopRepSubmodule (T : ℕᵒᵖ ⥤ TopRep.{w} R G) :
    Submodule R (∀ n : ℕ, (T.obj (op n)).V) where
  carrier := {y | ∀ n : ℕ, (T.map (homOfLE (Nat.le_succ n)).op).hom (y (n + 1)) = y n}
  add_mem' {x y} hx hy n := by simp [hx n, hy n]
  zero_mem' n := by simp
  smul_mem' r {x} hx n := by simp [hx n]

/-- A cone `c : Limits.Cone T` in `TopRep R G` whose evaluation map into the product is a
topological embedding onto the compatible-tuple locus is a limit cone. -/
noncomputable def isLimitOfIsEmbeddingRange (T : ℕᵒᵖ ⥤ TopRep.{w} R G) (c : Limits.Cone T)
    (hEmb : Topology.IsEmbedding fun x : c.pt.V ↦ fun n : ℕ ↦ (c.π.app (op n)).hom x)
    (hRange : Set.range (fun x : c.pt.V ↦ fun n : ℕ ↦ (c.π.app (op n)).hom x) =
      (limTopRepSubmodule T : Set (∀ n : ℕ, (T.obj (op n)).V))) :
    Limits.IsLimit c := by
  let φ : c.pt.V → ∀ n : ℕ, (T.obj (op n)).V := fun x n ↦ (c.π.app (op n)).hom x
  have hmem (s : Limits.Cone T) (a : s.pt.V) :
      (fun n : ℕ ↦ (s.π.app (op n)).hom a) ∈ Set.range φ := by
    rw [hRange]
    intro n
    exact congrArg (fun q : s.pt ⟶ T.obj (op n) ↦ q.hom a) (s.w (homOfLE (Nat.le_succ n)).op)
  let liftFun (s : Limits.Cone T) (a : s.pt.V) : c.pt.V := Classical.choose (hmem s a)
  have hlift (s : Limits.Cone T) (a : s.pt.V) (n : ℕ) :
      (c.π.app (op n)).hom (liftFun s a) = (s.π.app (op n)).hom a :=
    congrFun (Classical.choose_spec (hmem s a)) n
  refine
    { lift := fun s ↦ TopRep.ofHom
        { toFun := liftFun s
          map_add' := fun a b ↦ hEmb.injective <| funext fun n ↦ by
            simp only [hlift, map_add]
          map_smul' := fun r a ↦ hEmb.injective <| funext fun n ↦ by
            simp only [hlift, map_smul, RingHom.id_apply]
          cont := hEmb.continuous_iff.mpr <|
            (continuous_pi fun n ↦ (s.π.app (op n)).hom.continuous).congr fun a ↦
              funext fun n ↦ (hlift s a n).symm
          isIntertwining' := fun g ↦ by
            ext a
            apply hEmb.injective
            funext n
            change (c.π.app (op n)).hom (liftFun s (s.pt.ρ g a)) =
              (c.π.app (op n)).hom (c.pt.ρ g (liftFun s a))
            rw [hlift]
            exact (TopRep.hom_comm_apply (s.π.app (op n)) g a).trans
              ((congrArg ((T.obj (op n)).ρ g) (hlift s a n).symm).trans
                (TopRep.hom_comm_apply (c.π.app (op n)) g (liftFun s a)).symm) }
      fac := fun s j ↦ by
        ext a
        exact hlift s a (unop j)
      uniq := fun s m hm ↦ by
        ext a
        apply hEmb.injective
        funext n
        have hmn := congrArg (fun q : s.pt ⟶ T.obj (op n) ↦ q.hom a) (hm (op n))
        exact hmn.trans (hlift s a n).symm }

/-- The explicit inverse limit of a tower `T : ℕᵒᵖ ⥤ TopRep R G`, realised as the invariant
subrepresentation of compatible tuples inside `∀ n, (T.obj (op n)).V`. -/
@[expose]
def limTopRep (T : ℕᵒᵖ ⥤ TopRep.{w} R G) : TopRep.{w} R G :=
  TopRep.subrepresentation
    (TopRep.of (k := R) (G := G)
      { toMonoidHom :=
          { toFun := fun g ↦ ContinuousLinearMap.pi fun n : ℕ ↦
              (T.obj (op n)).ρ g ∘L ContinuousLinearMap.proj n
            map_one' := by ext x n; simp
            map_mul' := fun g h ↦ by ext x n; simp } })
    (limTopRepSubmodule T) fun g x hx n ↦ by
      change (T.map (homOfLE (Nat.le_succ n)).op).hom ((T.obj (op (n + 1))).ρ g (x (n + 1))) =
        (T.obj (op n)).ρ g (x n)
      rw [TopRep.hom_comm_apply, hx n]

/-- The projection from `limTopRep T` onto level `n`. -/
def limTopRepπ (T : ℕᵒᵖ ⥤ TopRep.{w} R G) (n : ℕ) : limTopRep T ⟶ T.obj (op n) :=
  TopRep.ofHom
    { toFun := fun x ↦ x.1 n
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := (continuous_apply n).comp continuous_subtype_val
      isIntertwining' := fun g ↦ by
        ext x
        exact congrArg (fun y : ∀ k : ℕ, (T.obj (op k)).V ↦ y n)
          (ContRepresentation.coe_subrepresentation_apply g x) }

@[simp]
theorem limTopRepπ_hom_apply (T : ℕᵒᵖ ⥤ TopRep.{w} R G) (n : ℕ) (x : (limTopRep T).V) :
    (limTopRepπ T n).hom x = x.1 n := by
  rfl

/-- The canonical cone with vertex `limTopRep T` over `T`. -/
noncomputable def limTopRepCone (T : ℕᵒᵖ ⥤ TopRep.{w} R G) : Limits.Cone T where
  pt := limTopRep T
  π := NatTrans.ofOpSequence (limTopRepπ T) fun n ↦ by
    ext x
    change (limTopRepπ T n).hom x =
      (T.map (homOfLE (Nat.le_succ n)).op).hom ((limTopRepπ T (n + 1)).hom x)
    rw [limTopRepπ_hom_apply, limTopRepπ_hom_apply]
    exact (x.2 n).symm

/-- `limTopRepCone T` is a limit cone in `TopRep R G`. -/
noncomputable def isLimitLimTopRepCone (T : ℕᵒᵖ ⥤ TopRep.{w} R G) :
    Limits.IsLimit (limTopRepCone T) :=
  isLimitOfIsEmbeddingRange T (limTopRepCone T)
    Topology.IsEmbedding.subtypeVal
    (by ext y; exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ x.2, fun hy ↦ ⟨⟨y, hy⟩, rfl⟩⟩)

/-- For any limit cone `c` of `T : ℕᵒᵖ ⥤ TopRep R G`, the coordinate map into the product is a
topological embedding. -/
theorem isEmbedding_of_isLimit (T : ℕᵒᵖ ⥤ TopRep.{w} R G) (c : Limits.Cone T)
    (hc : Limits.IsLimit c) :
    Topology.IsEmbedding fun x : c.pt.V ↦ fun n : ℕ ↦ (c.π.app (op n)).hom x := by
  let e : c.pt ≅ limTopRep T := hc.conePointUniqueUpToIso (isLimitLimTopRepCone T)
  let hHomeo : c.pt.V ≃ₜ (limTopRep T).V :=
    { toFun := e.hom.hom
      invFun := e.inv.hom
      left_inv := fun x ↦ congrArg (fun q : c.pt ⟶ c.pt ↦ q.hom x) e.hom_inv_id
      right_inv := fun x ↦ congrArg (fun q : limTopRep T ⟶ limTopRep T ↦ q.hom x) e.inv_hom_id
      continuous_toFun := e.hom.hom.continuous
      continuous_invFun := e.inv.hom.continuous }
  have hfun : (fun x : c.pt.V ↦ fun n : ℕ ↦ (c.π.app (op n)).hom x) =
      Subtype.val ∘ hHomeo := funext fun x ↦ funext fun n ↦ by
    have hw := congrArg (fun q : c.pt ⟶ T.obj (op n) ↦ q.hom x)
      (hc.conePointUniqueUpToIso_hom_comp (isLimitLimTopRepCone T) (op n))
    exact hw.symm.trans (limTopRepπ_hom_apply T n (e.hom.hom x))
  rw [hfun]
  exact Topology.IsEmbedding.subtypeVal.comp hHomeo.isEmbedding

/-- For any limit cone `c` of `T : ℕᵒᵖ ⥤ TopRep R G`, the range of the coordinate map into the
product is precisely the compatible-tuple locus `limTopRepSubmodule T`. -/
theorem range_of_isLimit (T : ℕᵒᵖ ⥤ TopRep.{w} R G) (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    Set.range (fun x : c.pt.V ↦ fun n : ℕ ↦ (c.π.app (op n)).hom x) =
      (limTopRepSubmodule T : Set (∀ n : ℕ, (T.obj (op n)).V)) := by
  let e : c.pt ≅ limTopRep T := hc.conePointUniqueUpToIso (isLimitLimTopRepCone T)
  have hcomp (x : c.pt.V) : (fun n : ℕ ↦ (c.π.app (op n)).hom x) = (e.hom.hom x).1 := by
    funext n
    have hw := congrArg (fun q : c.pt ⟶ T.obj (op n) ↦ q.hom x)
      (hc.conePointUniqueUpToIso_hom_comp (isLimitLimTopRepCone T) (op n))
    exact hw.symm.trans (limTopRepπ_hom_apply T n (e.hom.hom x))
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp only
    rw [hcomp]
    exact (e.hom.hom x).2
  · intro hy
    refine ⟨e.inv.hom ⟨y, hy⟩, ?_⟩
    dsimp only
    rw [hcomp]
    exact congrArg Subtype.val
      (congrArg (fun q : limTopRep T ⟶ limTopRep T ↦ q.hom ⟨y, hy⟩) e.inv_hom_id)

/-- If every level of a tower `T : ℕᵒᵖ ⥤ TopRep R G` has a jointly continuous `G`-action, then
every limit cone vertex of `T` also has a jointly continuous `G`-action. -/
theorem continuous_ρ_of_isLimit [TopologicalSpace G] (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    Continuous fun p : G × c.pt.V ↦ c.pt.ρ p.1 p.2 := by
  rw [(isEmbedding_of_isLimit T c hc).continuous_iff]
  refine continuous_pi fun n ↦ ?_
  exact ((hT n).comp
    (continuous_fst.prodMk ((c.π.app (op n)).hom.continuous.comp continuous_snd))).congr fun p ↦
    (TopRep.hom_comm_apply (c.π.app (op n)) p.1 p.2).symm

/-- A tower in `TopRep R G` whose consecutive transition maps all vanish has subsingleton limit. -/
theorem subsingleton_of_isLimit_of_transition_eq_zero (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hzero : ∀ n, T.map (homOfLE (Nat.le_succ n)).op = 0)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    Subsingleton c.pt.V := by
  refine ⟨fun x y ↦ (isEmbedding_of_isLimit T c hc).injective (funext fun n ↦ ?_)⟩
  have h0 (a : c.pt.V) : (c.π.app (op n)).hom a = 0 := by
    have hw := congrArg (fun q : c.pt ⟶ T.obj (op n) ↦ q.hom a) (c.w (homOfLE (Nat.le_succ n)).op)
    rw [hzero n] at hw
    exact hw.symm
  rw [h0 x, h0 y]

end TopRepLimits

/-! ### The tower of inhomogeneous continuous cochains and its inverse limit -/

section CochainsTower

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- The tower of inhomogeneous continuous cochain complexes attached to a tower `T` in `TopRep R G`
whose levels have jointly continuous `G`-actions. -/
@[expose]
noncomputable def inhomogeneousCochainsTower (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2) :
    ComplexTower.{max v w} R (ComplexShape.up ℕ) where
  obj n := inhomogeneousCochains (T.obj n) (hT (unop n))
  map f := inhomogeneousCochainsCoeffMap (T.map f) (hT _) (hT _)
  map_id n := by
    rw [T.map_id]
    exact inhomogeneousCochainsCoeffMap_id (T.obj n) (hT (unop n))
  map_comp f g := by
    rw [T.map_comp]
    exact inhomogeneousCochainsCoeffMap_comp (T.map f) (T.map g) (hT _) (hT _) (hT _)

@[simp]
theorem inhomogeneousCochainsTower_obj (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2) (n : ℕᵒᵖ) :
    (inhomogeneousCochainsTower T hT).obj n = inhomogeneousCochains (T.obj n) (hT (unop n)) :=
  rfl

@[simp]
theorem inhomogeneousCochainsTower_map (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (inhomogeneousCochainsTower T hT).map f =
      inhomogeneousCochainsCoeffMap (T.map f) (hT (unop m)) (hT (unop n)) :=
  rfl

/-- A transition map in degree `i` of `inhomogeneousCochainsTower` acts by postcomposition with the
transition morphism of `T`. -/
theorem inhomogeneousCochainsTower_term_transition (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (i n : ℕ) (f : C(Fin i → G, (T.obj (op (n + 1))).V)) :
    ((inhomogeneousCochainsTower T hT).term i).transition n f =
      (inhomogeneousCochainsMapF (.id G) (T.map (homOfLE (Nat.le_succ n)).op) i).hom f := by
  rw [ModuleTower.transition_def]
  change ((inhomogeneousCochainsCoeffMap (T.map (homOfLE (Nat.le_succ n)).op)
    (hT (n + 1)) (hT n)).f i).hom f = _
  rw [inhomogeneousCochainsCoeffMap_f]

/-- Degree-`i` linear equivalence `C(Fin i → G, c.pt.V) ≃ₗ[R] lim_n C(Fin i → G, Tₙ.V)` for any
limit cone `c` of `T`. -/
private noncomputable def inhomogeneousCochainsLimDegreeEquiv (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) (i : ℕ) :
    C(Fin i → G, c.pt.V) ≃ₗ[R] ((inhomogeneousCochainsTower T hT).term i).lim := by
  have hEmb := isEmbedding_of_isLimit T c hc
  have hRange := range_of_isLimit T c hc
  let evalAt (y : ((inhomogeneousCochainsTower T hT).term i).lim) (n : ℕ) :
      C(Fin i → G, (T.obj (op n)).V) := y.1 n
  have hmem (y : ((inhomogeneousCochainsTower T hT).term i).lim) (g : Fin i → G) :
      (fun n : ℕ ↦ evalAt y n g) ∈
        Set.range (fun x : c.pt.V ↦ fun n : ℕ ↦ (c.π.app (op n)).hom x) := by
    rw [hRange]
    intro n
    have hy := congrArg (fun f : C(Fin i → G, (T.obj (op n)).V) ↦ f g)
      (((inhomogeneousCochainsTower T hT).term i).transition_coe_lim_succ y n)
    have ht := congrArg (fun f : C(Fin i → G, (T.obj (op n)).V) ↦ f g)
      (inhomogeneousCochainsTower_term_transition T hT i n (evalAt y (n + 1)))
    exact (inhomogeneousCochainsMapF_apply (.id G) (T.map (homOfLE (Nat.le_succ n)).op) i
      (evalAt y (n + 1)) g).symm.trans (ht.symm.trans hy)
  let invVal (y : ((inhomogeneousCochainsTower T hT).term i).lim) (g : Fin i → G) : c.pt.V :=
    Classical.choose (hmem y g)
  have hinvVal (y : ((inhomogeneousCochainsTower T hT).term i).lim) (g : Fin i → G) (n : ℕ) :
      (c.π.app (op n)).hom (invVal y g) = evalAt y n g :=
    congrFun (Classical.choose_spec (hmem y g)) n
  refine
    { toFun := fun f ↦
        ⟨fun n ↦ (inhomogeneousCochainsMapF (.id G) (c.π.app (op n)) i).hom f,
          ((inhomogeneousCochainsTower T hT).term i).mem_lim.2 fun n ↦ by
            rw [inhomogeneousCochainsTower_term_transition]
            refine ContinuousMap.ext fun g ↦ ?_
            exact (inhomogeneousCochainsMapF_apply (.id G)
                (T.map (homOfLE (Nat.le_succ n)).op) i _ g).trans <|
              (congrArg (T.map (homOfLE (Nat.le_succ n)).op).hom
                (inhomogeneousCochainsMapF_apply (.id G) (c.π.app (op (n + 1))) i f g)).trans <|
              (congrArg (fun q : c.pt ⟶ T.obj (op n) ↦ q.hom (f g))
                (c.w (homOfLE (Nat.le_succ n)).op)).trans
              (inhomogeneousCochainsMapF_apply (.id G) (c.π.app (op n)) i f g).symm⟩
      invFun := fun y ↦
        ⟨invVal y, hEmb.continuous_iff.mpr <|
          (continuous_pi fun n ↦ (evalAt y n).continuous).congr fun g ↦
            funext fun n ↦ (hinvVal y g n).symm⟩
      map_add' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ map_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ map_smul _ _ _)
      left_inv := fun f ↦ ContinuousMap.ext fun g ↦ hEmb.injective <| funext fun n ↦
        (hinvVal _ g n).trans (inhomogeneousCochainsMapF_apply _ _ _ _ g)
      right_inv := fun y ↦ Subtype.ext <| funext fun n ↦ ContinuousMap.ext fun g ↦
        (inhomogeneousCochainsMapF_apply _ _ _ _ g).trans (hinvVal y g n) }

private theorem inhomogeneousCochainsLimDegreeEquiv_coe (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) (i : ℕ) (f : C(Fin i → G, c.pt.V)) (n : ℕ) :
    ((inhomogeneousCochainsLimDegreeEquiv T hT c hc i f :
        ((inhomogeneousCochainsTower T hT).term i).Product) n) =
      (inhomogeneousCochainsMapF (.id G) (c.π.app (op n)) i).hom f :=
  rfl

/-- **Inverse limits commute with inhomogeneous continuous cochains.** For any limit cone `c` of a
tower `T : ℕᵒᵖ ⥤ TopRep R G` with jointly continuous level actions, the inhomogeneous cochain
complex of `c.pt` is canonically isomorphic to the limit complex of the cochain tower. -/
noncomputable def inhomogeneousCochainsLimIso (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    inhomogeneousCochains c.pt (continuous_ρ_of_isLimit T hT c hc) ≅
      (inhomogeneousCochainsTower T hT).limComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (inhomogeneousCochainsLimDegreeEquiv T hT c hc i).toModuleIso)
    fun i j hij ↦ by
      have hji : i + 1 = j := hij
      subst hji
      apply ModuleCat.hom_ext
      ext f
      change (ModuleTower.limMap ((inhomogeneousCochainsTower T hT).dTower i (i + 1)))
          (inhomogeneousCochainsLimDegreeEquiv T hT c hc i f) =
        inhomogeneousCochainsLimDegreeEquiv T hT c hc (i + 1)
          (((inhomogeneousCochains c.pt _).d i (i + 1)).hom f)
      apply ModuleTower.lim_ext
      intro n
      rw [ModuleTower.limπ_apply, ModuleTower.limπ_apply, ModuleTower.coe_limMap_apply,
        ModuleTower.productMap_apply, ComplexTower.dTower_app,
        inhomogeneousCochainsLimDegreeEquiv_coe, inhomogeneousCochainsLimDegreeEquiv_coe]
      have hcomm := congrArg (fun q : (inhomogeneousCochains c.pt _).X i ⟶
          (inhomogeneousCochains (T.obj (op n)) (hT n)).X (i + 1) ↦ q.hom f)
        ((inhomogeneousCochainsCoeffMap (c.π.app (op n))
          (continuous_ρ_of_isLimit T hT c hc) (hT n)).comm i (i + 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, inhomogeneousCochainsCoeffMap_f] at hcomm
      exact hcomm

/-- Composing `inhomogeneousCochainsLimIso` with the `n`-th projection of the limit complex
recovers the coefficient map induced by `c.π.app (op n)`. -/
@[reassoc (attr := simp)]
theorem inhomogeneousCochainsLimIso_hom_comp_limComplexπ (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) (n : ℕ) :
    (inhomogeneousCochainsLimIso T hT c hc).hom ≫
        (inhomogeneousCochainsTower T hT).limComplexπ n =
      inhomogeneousCochainsCoeffMap (c.π.app (op n))
        (continuous_ρ_of_isLimit T hT c hc) (hT n) := by
  ext i : 1
  apply ModuleCat.hom_ext
  ext f
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, ComplexTower.limComplexπ_f_hom,
    inhomogeneousCochainsCoeffMap_f]
  change ((inhomogeneousCochainsTower T hT).term i).limπ n
    (inhomogeneousCochainsLimDegreeEquiv T hT c hc i f) = _
  rw [ModuleTower.limπ_apply, inhomogeneousCochainsLimDegreeEquiv_coe]
  rfl

end CochainsTower

/-! ### Discrete surjective transitions and the Milnor sequence on inhomogeneous cochains -/

section InhomogeneousMilnor

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- **Surjective transitions on discrete coefficients lift to continuous cochains.** If level `n`
of a tower `T` is discrete and `Tₙ₊₁ → Tₙ` is surjective, then the induced transition on degree-`i`
inhomogeneous continuous cochains is surjective, for any topological group `G`. -/
theorem inhomogeneousCochainsTower_transition_surjective (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ k, Continuous fun p : G × (T.obj (op k)).V ↦ (T.obj (op k)).ρ p.1 p.2)
    (i n : ℕ) [DiscreteTopology (T.obj (op n)).V]
    (hsurj : Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) :
    Function.Surjective (((inhomogeneousCochainsTower T hT).term i).transition n) := by
  intro f
  let f' : C(Fin i → G, (T.obj (op n)).V) := f
  obtain ⟨e, hecont, he⟩ := TauCeti.exists_continuous_lift hsurj f'.continuous
  refine ⟨⟨e, hecont⟩, ?_⟩
  rw [inhomogeneousCochainsTower_term_transition]
  exact ContinuousMap.ext fun g ↦ (inhomogeneousCochainsMapF_apply _ _ _ _ g).trans (he g)

/-- If every level of `T` is discrete and every transition `Tₙ₊₁ → Tₙ` is surjective, then the
shift map on every degree of `inhomogeneousCochainsTower T hT` is surjective (equivalently
`lim¹` of cochains vanishes in every degree). -/
theorem inhomogeneousCochainsTower_shift_surjective (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (i : ℕ) :
    Function.Surjective (((inhomogeneousCochainsTower T hT).term i).shift) :=
  ModuleTower.shift_surjective ((inhomogeneousCochainsTower T hT).term i) fun n ↦
    inhomogeneousCochainsTower_transition_surjective T hT i n (hsurj n)

/-- When every level of `T` is discrete and every transition is surjective, the Milnor
product-complex sequence `0 → lim C• → ∏ C• → ∏ C• → 0` is short exact. -/
theorem inhomogeneousCochainsTower_shortComplex_shortExact (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) :
    (inhomogeneousCochainsTower T hT).shortComplex.ShortExact :=
  ComplexTower.shortComplex_shortExact
    (inhomogeneousCochainsTower_shift_surjective T hT hsurj)

/-- The canonical map `Hʲ(C•(G, c.pt)) → lim Hʲ(C•(G, Tₙ))` induced by the cone projections of a
limit cone `c`. -/
noncomputable def inhomogeneousHomologyToLim (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) (j : ℕ) :
    (inhomogeneousCochains c.pt (continuous_ρ_of_isLimit T hT c hc)).homology j →ₗ[R]
      ((inhomogeneousCochainsTower T hT).homology j).lim :=
  (inhomogeneousCochainsTower T hT).homologyToLim j ∘ₗ
    (HomologicalComplex.homologyMap (inhomogeneousCochainsLimIso T hT c hc).hom j).hom

@[simp]
theorem coe_inhomogeneousHomologyToLim_apply (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) (j : ℕ)
    (x : (inhomogeneousCochains c.pt (continuous_ρ_of_isLimit T hT c hc)).homology j) (n : ℕ) :
    (inhomogeneousHomologyToLim T hT c hc j x :
        ((inhomogeneousCochainsTower T hT).homology j).Product) n =
      HomologicalComplex.homologyMap
        (inhomogeneousCochainsCoeffMap (c.π.app (op n)) (continuous_ρ_of_isLimit T hT c hc) (hT n))
        j x := by
  rw [inhomogeneousHomologyToLim, LinearMap.comp_apply, ComplexTower.coe_homologyToLim_apply,
    ← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    inhomogeneousCochainsLimIso_hom_comp_limComplexπ]
  rfl

/-- The connecting map `lim¹ Hⁿ(C•(G, Tₖ)) → Hⁿ⁺¹(C•(G, c.pt))` of the Milnor exact sequence for
inhomogeneous cochains. -/
noncomputable def inhomogeneousLimOneToHomology (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    ((inhomogeneousCochainsTower T hT).homology n).limOne →ₗ[R]
      (inhomogeneousCochains c.pt (continuous_ρ_of_isLimit T hT c hc)).homology (n + 1) :=
  (HomologicalComplex.homologyMap (inhomogeneousCochainsLimIso T hT c hc).inv (n + 1)).hom ∘ₗ
    (inhomogeneousCochainsTower T hT).limOneToHomology
      (inhomogeneousCochainsTower_shift_surjective T hT hsurj)
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)

/-- In degree `0`, `H⁰(C•(G, lim Tₙ)) → lim H⁰(C•(G, Tₙ))` is bijective for every tower `T` with
jointly continuous level actions, with no discreteness or surjectivity assumption. -/
theorem inhomogeneousHomologyToLim_bijective_zero (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    Function.Bijective (inhomogeneousHomologyToLim T hT c hc 0) := by
  let C := inhomogeneousCochainsTower T hT
  have hlim : Function.Bijective (C.homologyToLim 0) := by
    refine ⟨C.homologyToLim_injective_of_forall_not_rel
      fun i (hi : i + 1 = 0) ↦ Nat.succ_ne_zero i hi, fun y ↦ ?_⟩
    let yn (k : ℕ) : (C.obj (op k)).homology 0 := y.1 k
    let cy (n : ℕ) : (C.obj (op n)).cycles 0 :=
      (CochainComplex.isoHomologyπ₀ (C.obj (op n))).inv (yn n)
    let z (n : ℕ) : (C.obj (op n)).X 0 := (C.obj (op n)).iCycles 0 (cy n)
    have hzMem : z ∈ (C.term 0).lim := ((C.term 0).mem_lim).2 fun n ↦ by
      rw [ModuleTower.transition_def]
      change ((C.map (homOfLE (Nat.le_succ n)).op).f 0) ((C.obj (op (n + 1))).iCycles 0
        (cy (n + 1))) = (C.obj (op n)).iCycles 0 (cy n)
      have hi := ConcreteCategory.congr_hom
        (HomologicalComplex.cyclesMap_i (C.map (homOfLE (Nat.le_succ n)).op) 0) (cy (n + 1))
      have hnat := ConcreteCategory.congr_hom
        (CochainComplex.isoHomologyπ₀_inv_naturality
          (C.map (homOfLE (Nat.le_succ n)).op)) (yn (n + 1))
      have hy : HomologicalComplex.homologyMap (C.map (homOfLE (Nat.le_succ n)).op) 0
          (yn (n + 1)) = yn n := by
        have h := (C.homology 0).transition_coe_lim_succ y n
        rwa [ComplexTower.homology_transition] at h
      simp only [ConcreteCategory.comp_apply] at hi hnat
      rw [← hi, ← hnat, hy]
    let z0 : (C.term 0).lim := ⟨z, hzMem⟩
    let z' : C.limComplex.X 0 := z0
    have hπ0 (n : ℕ) : ((C.limComplexπ n).f 0).hom z' = z n := by
      have h := LinearMap.congr_fun (C.limComplexπ_f_hom n 0) z0
      exact h.trans (ModuleTower.limπ_apply (C.term 0) n z0)
    have hd0 : (C.limComplex.d 0 1).hom z' = 0 := by
      apply (C.term 1).lim_ext
      intro n
      have hcomm := ConcreteCategory.congr_hom ((C.limComplexπ n).comm 0 1) z'
      simp only [ConcreteCategory.comp_apply] at hcomm
      have hπ1 : ((C.limComplexπ n).f 1).hom ((C.limComplex.d 0 1).hom z') =
          ((C.term 1).limπ n) ((C.limComplex.d 0 1).hom z') :=
        LinearMap.congr_fun (C.limComplexπ_f_hom n 1) ((C.limComplex.d 0 1).hom z')
      change ((C.term 1).limπ n) ((C.limComplex.d 0 1).hom z') = ((C.term 1).limπ n) 0
      rw [← hπ1, ← hcomm, hπ0 n, map_zero]
      have hd := ConcreteCategory.congr_hom ((C.obj (op n)).iCycles_d 0 1) (cy n)
      simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hd
    let cLim : C.limComplex.cycles 0 :=
      (C.limComplex.cyclesIsoSc' 0 0 1 (by simp) (by simp)).inv
        ((C.limComplex.sc' 0 0 1).moduleCatCyclesIso.inv ⟨z', hd0⟩)
    have hcLim : C.limComplex.iCycles 0 cLim = z' := by
      have h1 := ConcreteCategory.congr_hom
        (C.limComplex.cyclesIsoSc'_inv_iCycles 0 0 1 (by simp) (by simp))
        ((C.limComplex.sc' 0 0 1).moduleCatCyclesIso.inv ⟨z', hd0⟩)
      have h2 := ConcreteCategory.congr_hom
        (C.limComplex.sc' 0 0 1).moduleCatCyclesIso_inv_iCycles ⟨z', hd0⟩
      simp only [ConcreteCategory.comp_apply] at h1
      exact h1.trans h2
    refine ⟨C.limComplex.homologyπ 0 cLim, (C.homology 0).lim_ext fun n ↦ ?_⟩
    rw [ModuleTower.limπ_apply, ModuleTower.limπ_apply, ComplexTower.coe_homologyToLim_apply]
    have hnat := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (C.limComplexπ n) 0) cLim
    simp only [ConcreteCategory.comp_apply] at hnat
    rw [hnat]
    have hcy : HomologicalComplex.cyclesMap (C.limComplexπ n) 0 cLim = cy n := by
      apply (ModuleCat.mono_iff_injective ((C.obj (op n)).iCycles 0)).mp inferInstance
      have hi := ConcreteCategory.congr_hom
        (HomologicalComplex.cyclesMap_i (C.limComplexπ n) 0) cLim
      simp only [ConcreteCategory.comp_apply] at hi
      rw [hi, hcLim]
      exact hπ0 n
    rw [hcy]
    have hinv := ConcreteCategory.congr_hom
      (CochainComplex.isoHomologyπ₀ (C.obj (op n))).inv_hom_id (yn n)
    simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hinv
    have hhom : (CochainComplex.isoHomologyπ₀ (C.obj (op n))).hom = (C.obj (op n)).homologyπ 0 :=
      (C.obj (op n)).isoHomologyπ_hom _ 0 rfl (by simp)
    rw [← hhom]
    exact hinv
  have hiso : Function.Bijective
      (HomologicalComplex.homologyMap (inhomogeneousCochainsLimIso T hT c hc).hom 0).hom :=
    (HomologicalComplex.homologyMapIso (inhomogeneousCochainsLimIso T hT c hc) 0
      ).toLinearEquiv.bijective
  exact hlim.comp hiso

/-- In every degree `j`, `Hʲ(C•(G, lim Tₙ)) → lim Hʲ(C•(G, Tₙ))` is surjective for a tower of
discrete representations with surjective transitions. -/
theorem inhomogeneousHomologyToLim_surjective (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (j : ℕ) :
    Function.Surjective (inhomogeneousHomologyToLim T hT c hc j) :=
  (ComplexTower.homologyToLim_surjective
      (inhomogeneousCochainsTower_shift_surjective T hT hsurj) j).comp
    (HomologicalComplex.homologyMapIso (inhomogeneousCochainsLimIso T hT c hc) j
      ).toLinearEquiv.surjective

/-- The Milnor connecting map `lim¹ Hⁿ → Hⁿ⁺¹(C•(G, lim Tₖ))` is injective. -/
theorem inhomogeneousLimOneToHomology_injective (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    Function.Injective (inhomogeneousLimOneToHomology T hT c hc hsurj n) :=
  (HomologicalComplex.homologyMapIso (inhomogeneousCochainsLimIso T hT c hc) (n + 1)
      ).symm.toLinearEquiv.injective.comp
    (ComplexTower.limOneToHomology_injective
      (inhomogeneousCochainsTower_shift_surjective T hT hsurj)
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))

/-- Exactness of the Milnor sequence `lim¹ Hⁿ → Hⁿ⁺¹(C•(G, lim Tₖ)) → lim Hⁿ⁺¹`. -/
theorem exact_inhomogeneousLimOneToHomology_inhomogeneousHomologyToLim (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    Function.Exact (inhomogeneousLimOneToHomology T hT c hc hsurj n)
      (inhomogeneousHomologyToLim T hT c hc (n + 1)) := by
  let e := (HomologicalComplex.homologyMapIso (inhomogeneousCochainsLimIso T hT c hc) (n + 1)
    ).toLinearEquiv
  intro x
  have hex := ComplexTower.exact_limOneToHomology_homologyToLim
    (inhomogeneousCochainsTower_shift_surjective T hT hsurj)
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl) (e x)
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hex.1 hx
    refine ⟨y, ?_⟩
    change e.symm _ = x
    rw [hy, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, rfl⟩
    exact hex.2 ⟨y, (e.apply_symm_apply _).symm⟩

/-- When `lim¹ Hⁿ` vanishes, `Hⁿ⁺¹(C•(G, lim Tₖ)) → lim Hⁿ⁺¹` is bijective. -/
theorem inhomogeneousHomologyToLim_bijective_succ (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ)
    [Subsingleton ((inhomogeneousCochainsTower T hT).homology n).limOne] :
    Function.Bijective (inhomogeneousHomologyToLim T hT c hc (n + 1)) :=
  (ComplexTower.homologyToLim_bijective
      (inhomogeneousCochainsTower_shift_surjective T hT hsurj)
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)).comp
    (HomologicalComplex.homologyMapIso (inhomogeneousCochainsLimIso T hT c hc) (n + 1)
      ).toLinearEquiv.bijective

end InhomogeneousMilnor

/-! ### Vanishing checks: trivial group and zero transitions -/

section DegenerateChecks

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- When `G` is a subsingleton, the limit complex of `inhomogeneousCochainsTower T hT` has zero
cohomology in every positive degree. -/
theorem isZero_limComplex_homology_succ_of_subsingleton [Subsingleton G]
    (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2) (n : ℕ) :
    Limits.IsZero ((inhomogeneousCochainsTower T hT).limComplex.homology (n + 1)) :=
  (isZero_inhomogeneousCochains_homology_succ_of_subsingleton (limTopRep T)
      (continuous_ρ_of_isLimit T hT (limTopRepCone T) (isLimitLimTopRepCone T)) n).of_iso
    (HomologicalComplex.homologyMapIso
      (inhomogeneousCochainsLimIso T hT (limTopRepCone T) (isLimitLimTopRepCone T)) (n + 1)).symm

/-- A tower with zero consecutive transition maps has zero inhomogeneous cochain complex on its
limit. -/
theorem isZero_inhomogeneousCochains_of_transition_eq_zero (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (hzero : ∀ n, T.map (homOfLE (Nat.le_succ n)).op = 0)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    Limits.IsZero (inhomogeneousCochains c.pt (continuous_ρ_of_isLimit T hT c hc)) := by
  have : Subsingleton c.pt.V := subsingleton_of_isLimit_of_transition_eq_zero T hzero c hc
  rw [Limits.IsZero.iff_id_eq_zero]
  ext i f g
  exact Subsingleton.elim _ _

/-- A tower with zero consecutive transition maps has zero limit complex `lim C•(G, Tₙ)`. -/
theorem isZero_limComplex_of_transition_eq_zero (T : ℕᵒᵖ ⥤ TopRep.{w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (hzero : ∀ n, T.map (homOfLE (Nat.le_succ n)).op = 0) :
    Limits.IsZero (inhomogeneousCochainsTower T hT).limComplex :=
  (isZero_inhomogeneousCochains_of_transition_eq_zero T hT hzero
      (limTopRepCone T) (isLimitLimTopRepCone T)).of_iso
    (inhomogeneousCochainsLimIso T hT (limTopRepCone T) (isLimitLimTopRepCone T)).symm

end DegenerateChecks

end TauCeti.ContinuousCohomology
