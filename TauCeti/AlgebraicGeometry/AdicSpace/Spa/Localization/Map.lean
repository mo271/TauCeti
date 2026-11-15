/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison
public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
import TauCeti.RingTheory.Huber.AdicHom.Localization

/-!
# Functoriality and adicness of completed rational localisation along morphisms

Let `φ : A →+* B` be continuous at `0`, and let `R(T/s) ⊆ Spa (A, A⁺)` and `R(T'/s') ⊆ Spa (B, B⁺)`
be rational subsets such that pullback along `φ` maps `R(T'/s')` into `R(T/s)`. Instantiating
Wedhorn's Lemma 8.1 at `(B⟨T'/s'⟩, B_U'⁺)` yields a unique continuous ring homomorphism
`ringHomOfMapsToRationalSubset : A⟨T/s⟩ →+* B⟨T'/s'⟩` commuting with `toCompletionLoc`, carrying
`A_U⁺` into `B_U'⁺` (`pairHomOfMapsToRationalSubset`), and inheriting adicness when `φ` is adic.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.46, Lemma 8.1, and
  Proposition 8.2.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

/-- Install the localization topological-ring instances for `S` in a term. -/
local macro "withLocRing1 " P:term:arg T:term:arg s:term:arg S:term:arg h:term:arg
    " => " body:term : term =>
  `(letI := locUniformSpace $P $T $s $S $h
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $h
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $h
    $body)

/-- Install the localization topological-ring instances for `S` and `S'` in a term. -/
local macro "withLocRing2 " P:term:arg T:term:arg s:term:arg S:term:arg h:term:arg
    P':term:arg T':term:arg s':term:arg S':term:arg h':term:arg " => " body:term : term =>
  `(withLocRing1 $P $T $s $S $h => withLocRing1 $P' $T' $s' $S' $h' => $body)

/-- Install the localization Huber-ring instances for `S` in a term. -/
local macro "withLocHuber1 " P:term:arg T:term:arg s:term:arg S:term:arg h:term:arg
    " => " body:term : term =>
  `(withLocRing1 $P $T $s $S $h => letI := isHuberRing_completion_locTopology $P $T $s $S $h; $body)

/-- Install the localization Huber-ring instances for `S` and `S'` in a term. -/
local macro "withLocHuber2 " P:term:arg T:term:arg s:term:arg S:term:arg h:term:arg
    P':term:arg T':term:arg s':term:arg S':term:arg h':term:arg " => " body:term : term =>
  `(withLocHuber1 $P $T $s $S $h => withLocHuber1 $P' $T' $s' $S' $h' => $body)

/-- Register localization topological-ring and Huber-ring instances in tactic mode. -/
local macro "map_loc_huber " P:term:arg T:term:arg s:term:arg S:term:arg h:term:arg : tactic =>
  `(tactic| (
    let _ := locUniformSpace $P $T $s $S $h
    have _ := isUniformAddGroup_locUniformSpace $P $T $s $S $h
    have _ := isTopologicalRing_locUniformSpace $P $T $s $S $h
    have _ := isHuberRing_completion_locTopology $P $T $s $S $h))

section RingHom

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]

section TwoRings

variable (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*)
  [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition B) (Bplus : Subring B)

/-- If `φ : A →+* B` is continuous at `0` and pullback along `φ` carries `R(T'/s')` into `R(T/s)`,
`(toCompletionLoc P' T' s' S' hden').comp φ` extends uniquely to `A⟨T/s⟩ →+* B⟨T'/s'⟩`. -/
theorem existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b) (T' : Finset B) (s' : B) (S' : Type*)
    [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S') {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      ∃! σ : Completion S →+* Completion S', Continuous σ ∧
        σ.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' s' S' hden').comp φ := by
  map_loc_huber P' T' s' S' hden'
  refine existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    P Aplus T s S hden (powerBoundedSubring (Completion S'))
    ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
    ((continuous_toCompletionLoc P' T' s' S' hden').continuousAt.comp_of_eq hφ (map_zero φ))
    fun w hw ↦ ?_
  have hle := completedPlusSubring_le_powerBoundedSubring P' Bplus hBplus T' s' S' hden'
  rw [comap_comp, Function.comp_apply]
  exact hsub (by simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P' Bplus T' s' S' hden' ⟨w, spa_antitone hle hw⟩)

section WithBplus

variable (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b) (T' : Finset B) (s' : B) (S' : Type*)
  [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
  (hden' : HasDenominatorPower P' T' s' S')

section BasicRingHom

variable {φ : A →+* B} (hφ : ContinuousAt φ 0)
  (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s))

/-- The continuous ring homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩` induced by `φ : A →+* B` continuous at
`0` whose valuation pullback maps `R(T'/s')` into `R(T/s)`. -/
noncomputable def ringHomOfMapsToRationalSubset :
    withLocRing2 P T s S hden P' T' s' S' hden' => Completion S →+* Completion S' :=
  (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
    P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub).choose

/-- Apply `f` to the `BasicRingHom` section variables. -/
local macro:max "mapAppR " f:term:max : term =>
  let i := Lean.mkIdent
  `($f $(i `P) $(i `Aplus) $(i `T) $(i `s) $(i `S) $(i `hden) $(i `P') $(i `Bplus) $(i `hBplus)
      $(i `T') $(i `s') $(i `S') $(i `hden') $(i `hφ) $(i `hsub))

/-- `ringHomOfMapsToRationalSubset` is continuous. -/
@[fun_prop] theorem continuous_ringHomOfMapsToRationalSubset :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      Continuous (mapAppR ringHomOfMapsToRationalSubset) :=
  (mapAppR existsUnique_continuous_ringHom_of_mapsTo_rationalSubset).choose_spec.1.1

/-- `ringHomOfMapsToRationalSubset` commutes with the structure maps from `A` and `B`. -/
@[simp] theorem ringHomOfMapsToRationalSubset_comp_toCompletionLoc :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      (mapAppR ringHomOfMapsToRationalSubset).comp (toCompletionLoc P T s S hden) =
        (toCompletionLoc P' T' s' S' hden').comp φ :=
  (mapAppR existsUnique_continuous_ringHom_of_mapsTo_rationalSubset).choose_spec.1.2

/-- Pointwise action of `ringHomOfMapsToRationalSubset` on elements coming from `A`. -/
@[simp] theorem ringHomOfMapsToRationalSubset_algebraMap_coe (a : A) :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      mapAppR ringHomOfMapsToRationalSubset (algebraMap A S a : Completion S) =
        (algebraMap B S' (φ a) : Completion S') := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'
  rw [← toCompletionLoc_apply P T s S hden, ← toCompletionLoc_apply P' T' s' S' hden']
  exact RingHom.congr_fun (mapAppR ringHomOfMapsToRationalSubset_comp_toCompletionLoc) a

/-- Any continuous ring homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩` extending `ρ' ∘ φ` across `ρ` equals
`ringHomOfMapsToRationalSubset`. -/
theorem eq_ringHomOfMapsToRationalSubset :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      ∀ (τ : Completion S →+* Completion S'), Continuous τ →
        τ.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' s' S' hden').comp φ →
        τ = mapAppR ringHomOfMapsToRationalSubset :=
  fun _ hτ hc ↦
    (mapAppR existsUnique_continuous_ringHom_of_mapsTo_rationalSubset).choose_spec.2 _ ⟨hτ, hc⟩

/-- Pullback along `ringHomOfMapsToRationalSubset` sends `Spa (B⟨T'/s'⟩, B_U'⁺)` into
`Spa (A⟨T/s⟩, A_U⁺)`. -/
theorem comap_ringHomOfMapsToRationalSubset_mem_spa :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      ∀ w ∈ spa (completedPlusSubring P' Bplus T' s' S' hden'),
        comap (mapAppR ringHomOfMapsToRationalSubset) w ∈
          spa (completedPlusSubring P Aplus T s S hden) := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'
  refine fun w hw ↦ comap_mem_spa_completedPlusSubring P Aplus T s S hden _
    (mapAppR continuous_ringHomOfMapsToRationalSubset) ((mem_spa_iff _ _).mp hw).1 ?_
  rw [ringHomOfMapsToRationalSubset_comp_toCompletionLoc, comap_comp, Function.comp_apply]
  exact hsub (by simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P' Bplus T' s' S' hden' ⟨w, hw⟩)

end BasicRingHom

/-- Functoriality of `ringHomOfMapsToRationalSubset` with respect to composition. -/
@[simp] theorem ringHomOfMapsToRationalSubset_comp
    (P'' : PairOfDefinition C) (Cplus : Subring C) (hCplus : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c)
    (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
    [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower P'' T'' s'' S'')
    {φ : A →+* B} (hφ : ContinuousAt φ 0) {ψ : B →+* C} (hψ : ContinuousAt ψ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s))
    (hsub' : Set.MapsTo (comap ψ) (rationalSubset Cplus T'' s'') (rationalSubset Bplus T' s')) :
    withLocRing2 P T s S hden P' T' s' S' hden' => withLocRing1 P'' T'' s'' S'' hden'' =>
      (ringHomOfMapsToRationalSubset
          P' Bplus T' s' S' hden' P'' Cplus hCplus T'' s'' S'' hden'' hψ hsub').comp
        (ringHomOfMapsToRationalSubset
          P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub) =
      ringHomOfMapsToRationalSubset P Aplus T s S hden P'' Cplus hCplus T'' s'' S'' hden''
        (φ := ψ.comp φ) (hψ.comp_of_eq hφ (map_zero φ))
        (by rw [comap_comp]; exact hsub.comp hsub') := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'; map_loc_huber P'' T'' s'' S'' hden''
  refine eq_ringHomOfMapsToRationalSubset P Aplus T s S hden P'' Cplus hCplus T'' s'' S'' hden''
    (φ := ψ.comp φ) (hψ.comp_of_eq hφ (map_zero φ)) _ _
    ((continuous_ringHomOfMapsToRationalSubset
      P' Bplus T' s' S' hden' P'' Cplus hCplus T'' s'' S'' hden'' hψ hsub').comp
      (continuous_ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub)) ?_
  rw [RingHom.comp_assoc, ringHomOfMapsToRationalSubset_comp_toCompletionLoc, ← RingHom.comp_assoc,
    ringHomOfMapsToRationalSubset_comp_toCompletionLoc, RingHom.comp_assoc]

/-- If `φ : A →+* B` is adic, the induced map `A⟨T/s⟩ →+* B⟨T'/s'⟩` is adic. -/
theorem isAdicHom_ringHomOfMapsToRationalSubset {φ : A →+* B} (hφ : IsAdicHom φ)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      IsAdicHom (ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ.continuous.continuousAt hsub) := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'
  refine IsAdicHom.of_comp (f := toCompletionLoc P T s S hden) ?_
    (continuous_toCompletionLoc P T s S hden)
    (continuous_ringHomOfMapsToRationalSubset
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ.continuous.continuousAt hsub)
  rw [ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
  exact (isAdicHom_toCompletionLoc P' T' s' S' hden').comp hφ

end WithBplus

/-- `ringHomOfMapsToRationalSubset` carries `A_U⁺` into `B_U'⁺`. -/
theorem ringHomOfMapsToRationalSubset_mem_completedPlusSubring
    (hIplus' : ∀ j : P'.ringOfDefinition, j ∈ P'.idealOfDefinition → (j : B) ∈ Bplus)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b) (T' : Finset B) (s' : B) (S' : Type*)
    [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S') {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    withLocRing2 P T s S hden P' T' s' S' hden' =>
      ∀ f ∈ completedPlusSubring P Aplus T s S hden,
        ringHomOfMapsToRationalSubset P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub f ∈
          completedPlusSubring P' Bplus T' s' S' hden' := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'
  have hint := isRingOfIntegralElements_completedPlusSubring P' Bplus hIplus' hBplus T' s' S' hden'
  refine fun f hf ↦ hint.mem_of_forall_vle_one fun w hw ↦ ?_
  simpa only [comap_vle, map_one] using
    ((mem_spa_iff _ _).mp
      (comap_ringHomOfMapsToRationalSubset_mem_spa
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub w hw)).2 f hf

end TwoRings

section SameRing

variable (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)
  (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
  (hden' : HasDenominatorPower P T' s' S')

/-- Along `RingHom.id A`, `ringHomOfMapsToRationalSubset` agrees with
`ringHomOfRationalSubsetSubset`. -/
@[simp] theorem ringHomOfMapsToRationalSubset_id (hId : ContinuousAt (RingHom.id A) 0)
    (hsub : Set.MapsTo (comap (RingHom.id A))
      (rationalSubset Aplus T' s') (rationalSubset Aplus T s)) :
    withLocRing2 P T s S hden P T' s' S' hden' =>
      ringHomOfMapsToRationalSubset P Aplus T s S hden P Aplus hAplus T' s' S' hden' hId hsub =
        ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden'
          (fun v hv ↦ by simpa only [comap_id, id_eq] using hsub hv) := by
  map_loc_huber P T s S hden; map_loc_huber P T' s' S' hden'
  have hsub' : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s :=
    fun v hv ↦ by simpa only [comap_id, id_eq] using hsub hv
  refine (eq_ringHomOfMapsToRationalSubset P Aplus T s S hden P Aplus hAplus T' s' S' hden'
    hId hsub (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub')
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub')
    ?_).symm
  rw [ringHomOfRationalSubsetSubset_comp_toCompletionLoc, RingHom.comp_id]

/-- The restriction map `A⟨T/s⟩ →+* A⟨T'/s'⟩` of a containment `R(T'/s') ⊆ R(T/s)` is adic. -/
theorem isAdicHom_ringHomOfRationalSubsetSubset
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    withLocRing2 P T s S hden P T' s' S' hden' =>
      IsAdicHom (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub) := by
  map_loc_huber P T s S hden; map_loc_huber P T' s' S' hden'
  have : IsHuberRing A := ⟨⟨P⟩⟩
  have hsub_id : Set.MapsTo (comap (RingHom.id A))
      (rationalSubset Aplus T' s') (rationalSubset Aplus T s) :=
    fun v hv ↦ by simpa only [comap_id, id_eq] using hsub hv
  simpa only [ringHomOfMapsToRationalSubset_id] using
    isAdicHom_ringHomOfMapsToRationalSubset
      P Aplus T s S hden P Aplus hAplus T' s' S' hden' IsAdicHom.id hsub_id

end SameRing

end RingHom

section PairHom

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

section ExplicitSA

variable (P : PairOfDefinition A) (SA : Pair A) (hP : P.ringOfDefinition ≤ SA.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

section BasicPairHom

variable (P' : PairOfDefinition B) (SB : Pair B) (hP' : P'.ringOfDefinition ≤ SB.plus)
  (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
  (hden' : HasDenominatorPower P' T' s' S') {φ : A →+* B} (hφ : ContinuousAt φ 0)
  (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s))

/-- `ringHomOfMapsToRationalSubset` bundled as a morphism of completed rational localisation Huber
pairs `(A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_U'⁺)`. -/
noncomputable def pairHomOfMapsToRationalSubset :
    withLocHuber2 P T s S hden P' T' s' S' hden' =>
      Pair.Hom (P.rationalLocalizationPair SA hP T s S hden)
        (P'.rationalLocalizationPair SB hP' T' s' S' hden') :=
  withLocHuber2 P T s S hden P' T' s' S' hden' =>
  let hpb := SB.isRingOfIntegralElements.isPowerBounded_of_mem
  { toRingHom := ringHomOfMapsToRationalSubset
      P SA.plus T s S hden P' SB.plus hpb T' s' S' hden' hφ hsub
    continuous_toRingHom := continuous_ringHomOfMapsToRationalSubset
      P SA.plus T s S hden P' SB.plus hpb T' s' S' hden' hφ hsub
    map_mem_plus := fun f hf ↦ by
      rw [rationalLocalizationPair_plus] at hf ⊢
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring
        P SA.plus T s S hden P' SB.plus (fun j _ ↦ hP' j.2) hpb T' s' S' hden' hφ hsub f hf }

/-- The underlying ring homomorphism of `pairHomOfMapsToRationalSubset` is
`ringHomOfMapsToRationalSubset`. -/
@[simp] theorem pairHomOfMapsToRationalSubset_toRingHom :
    withLocHuber2 P T s S hden P' T' s' S' hden' =>
      (pairHomOfMapsToRationalSubset
        P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub).toRingHom =
        ringHomOfMapsToRationalSubset
          P SA.plus T s S hden P' SB.plus SB.isRingOfIntegralElements.isPowerBounded_of_mem
          T' s' S' hden' hφ hsub := (rfl)

/-- Pulling back along `pairHomOfMapsToRationalSubset` and `toCompletionLocHom` computes `comap φ`
on `Spv`. -/
theorem spaComap_toCompletionLocHom_spaComap_pairHomOfMapsToRationalSubset :
    withLocHuber2 P T s S hden P' T' s' S' hden' =>
      ∀ w : spa (P'.rationalLocalizationPair SB hP' T' s' S' hden').plus,
        (((P.toCompletionLocHom SA hP T s S hden).spaComap
          ((pairHomOfMapsToRationalSubset
            P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub).spaComap w)).1 : Spv A) =
          comap φ (((P'.toCompletionLocHom SB hP' T' s' S' hden').spaComap w).1 : Spv B) := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'; intro w
  simp only [Pair.Hom.spaComap_val, toRingHom_toCompletionLocHom,
    pairHomOfMapsToRationalSubset_toRingHom]
  rw [← Function.comp_apply (f := comap (toCompletionLoc P T s S hden)), ← comap_comp,
    ringHomOfMapsToRationalSubset_comp_toCompletionLoc, comap_comp, Function.comp_apply]

end BasicPairHom

/-- On the same presentation along `RingHom.id A`, `pairHomOfMapsToRationalSubset` is `id`. -/
@[simp] theorem pairHomOfMapsToRationalSubset_self (hId : ContinuousAt (RingHom.id A) 0)
    (hsub : Set.MapsTo (comap (RingHom.id A))
      (rationalSubset SA.plus T s) (rationalSubset SA.plus T s)) :
    withLocHuber1 P T s S hden =>
      pairHomOfMapsToRationalSubset P SA hP T s S hden P SA hP T s S hden hId hsub =
        Pair.Hom.id (P.rationalLocalizationPair SA hP T s S hden) := by
  map_loc_huber P T s S hden; apply Pair.Hom.ext
  simp only [pairHomOfMapsToRationalSubset_toRingHom, Pair.Hom.toRingHom_id]
  exact (eq_ringHomOfMapsToRationalSubset P SA.plus T s S hden P SA.plus
    SA.isRingOfIntegralElements.isPowerBounded_of_mem T s S hden hId hsub
    (RingHom.id _) continuous_id (by rw [RingHom.id_comp, RingHom.comp_id])).symm

/-- Functoriality of `pairHomOfMapsToRationalSubset` with respect to composition. -/
@[simp] theorem pairHomOfMapsToRationalSubset_comp
    (P' : PairOfDefinition B) (SB : Pair B) (hP' : P'.ringOfDefinition ≤ SB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    (P'' : PairOfDefinition C) (SC : Pair C) (hP'' : P''.ringOfDefinition ≤ SC.plus)
    (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
    [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower P'' T'' s'' S'')
    {φ : A →+* B} (hφ : ContinuousAt φ 0) {ψ : B →+* C} (hψ : ContinuousAt ψ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s))
    (hsub' : Set.MapsTo (comap ψ) (rationalSubset SC.plus T'' s'') (rationalSubset SB.plus T' s')) :
    withLocHuber2 P T s S hden P' T' s' S' hden' => withLocHuber1 P'' T'' s'' S'' hden'' =>
      (pairHomOfMapsToRationalSubset
          P' SB hP' T' s' S' hden' P'' SC hP'' T'' s'' S'' hden'' hψ hsub').comp
        (pairHomOfMapsToRationalSubset P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub) =
      pairHomOfMapsToRationalSubset P SA hP T s S hden P'' SC hP'' T'' s'' S'' hden''
        (φ := ψ.comp φ) (hψ.comp_of_eq hφ (map_zero φ))
        (by rw [comap_comp]; exact hsub.comp hsub') := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'; map_loc_huber P'' T'' s'' S'' hden''
  apply Pair.Hom.ext; simp

end ExplicitSA

/-- When `φ = f.toRingHom`, `pairHomOfMapsToRationalSubset` commutes with `toCompletionLocHom`. -/
theorem pairHomOfMapsToRationalSubset_comp_toCompletionLocHom
    (P : PairOfDefinition A) {SA : Pair A} (hP : P.ringOfDefinition ≤ SA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) {SB : Pair B} (hP' : P'.ringOfDefinition ≤ SB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    (f : Pair.Hom SA SB) {φ : A →+* B} (hfφ : f.toRingHom = φ) (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s)) :
    withLocHuber2 P T s S hden P' T' s' S' hden' =>
      (pairHomOfMapsToRationalSubset P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub).comp
        (P.toCompletionLocHom SA hP T s S hden) =
        (P'.toCompletionLocHom SB hP' T' s' S' hden').comp f := by
  map_loc_huber P T s S hden; map_loc_huber P' T' s' S' hden'
  apply Pair.Hom.ext; simp [hfφ]

end PairHom

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.Pair.Hom

open TauCeti.ValuationSpectrum

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {SA : Pair A} {SB : Pair B}

/-- `f.spaComap` maps `Subtype.val ⁻¹' R(T'/s')` into `Subtype.val ⁻¹' R(T/s)` iff
`comap f.toRingHom` maps `R(T'/s')` into `R(T/s)`. -/
theorem mapsTo_spaComap_rationalSubset_iff (f : Hom SA SB)
    (T : Finset A) (s : A) (T' : Finset B) (s' : B) :
    Set.MapsTo f.spaComap
      (Subtype.val ⁻¹' rationalSubset SB.plus T' s')
      (Subtype.val ⁻¹' rationalSubset SA.plus T s) ↔
    Set.MapsTo (comap f.toRingHom) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s) :=
  ⟨fun h v hv ↦ by
    simpa only [Set.mem_preimage, spaComap_val] using
      @h ⟨v, rationalSubset_subset_spa SB.plus T' s' hv⟩ hv,
   fun h v hv ↦ by simpa only [Set.mem_preimage, spaComap_val] using h hv⟩

end TauCeti.Huber.Pair.Hom

end
