/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Encodable.Basic
public import TauCeti.ModelTheory.RelationalConfiguration.Topology
public import TauCeti.SetTheory.Descriptive.Tree

/-!
# Query codes of relational configurations

When a language `L` and carrier `V` have countably many atoms `Atom L V`, an explicit enumeration
`e : Encodable (Atom L V)` embeds the configuration space `RelationalConfiguration L V` into Cantor
space `ℕ → Bool` by reading the truth value of the `n`-th atom when `n` decodes to an atom and
padding with `false` otherwise (`queryCodeWith e`). Fixing `Encodable.ofCountable (Atom L V)`
defines the canonical query code `queryCode`.

Because `RelationalConfiguration L V` is compact and `ℕ → Bool` is Hausdorff, the continuous
injection `queryCodeWith e` is a closed embedding (`isClosedEmbedding_queryCodeWith`). Pulling
back the tree representation of analytic sets (`MeasureTheory.AnalyticSet.exists_tree_eq`) along
`queryCodeWith e` represents every analytic class of relational configurations as the projection
of the body of a descriptive tree on `Bool × ℕ` (`exists_tree_of_analyticSet_with` and
`exists_tree_of_analyticSet`).

Nothing here assumes that `L` is relational or that `V` itself is countable: only `Countable
(Atom L V)` is needed for `queryCode` (which holds automatically when each `L.Relations n` and `V`
are countable, and also on uncountable `V` when `L` has only countably many nullary relations).

## Main definitions

* `TauCeti.RelationalConfiguration.queryCodeWith`: the embedding into Cantor space `ℕ → Bool`
  induced by an explicit `Encodable (Atom L V)`.
* `TauCeti.RelationalConfiguration.queryCode`: the canonical embedding using
  `Encodable.ofCountable (Atom L V)`.

## Main results

* `TauCeti.RelationalConfiguration.queryCodeWith_injective` and `queryCode_injective`: the query
  code is injective.
* `TauCeti.RelationalConfiguration.continuous_queryCodeWith` and `continuous_queryCode`: the query
  code is continuous.
* `TauCeti.RelationalConfiguration.measurable_queryCodeWith` and `measurable_queryCode`: the query
  code is measurable for the product σ-algebras.
* `TauCeti.RelationalConfiguration.isClosedEmbedding_queryCodeWith` and
  `isClosedEmbedding_queryCode`: the query code is a closed embedding into Cantor space.
* `TauCeti.RelationalConfiguration.exists_tree_of_analyticSet_with` and
  `exists_tree_of_analyticSet`: every analytic class of configurations is represented by a
  descriptive tree on `Bool × ℕ` through its query code.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, §16 (coding countable structures in Cantor space) and §25 (analytic sets as
  projections of trees).
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapter 4.
-/

public section

universe u v w

open Descriptive Descriptive.Tree MeasureTheory Topology

namespace TauCeti.RelationalConfiguration

variable {L : FirstOrder.Language.{u, v}} {V : Type w}

/-! ### Explicit-encoding query codes -/

/-- The **query code** of a relational configuration with respect to an explicit enumeration
`e : Encodable (Atom L V)`: coordinate `n` reads the truth value of the atom decoded from `n`, and
is padded with `false` when `n` decodes to `none`. -/
def queryCodeWith (e : Encodable (Atom L V)) (c : RelationalConfiguration L V) : ℕ → Bool :=
  fun n => (@Encodable.decode _ e n).elim false c.eval

/-- Unfolding lemma for `queryCodeWith`. -/
theorem queryCodeWith_apply (e : Encodable (Atom L V)) (c : RelationalConfiguration L V) (n : ℕ) :
    queryCodeWith e c n = (@Encodable.decode _ e n).elim false c.eval := (rfl)

/-- Reading the query code at the code of an atom recovers the atom's value. -/
@[simp]
theorem queryCodeWith_encode (e : Encodable (Atom L V)) (c : RelationalConfiguration L V)
    (a : Atom L V) : queryCodeWith e c (@Encodable.encode _ e a) = c.eval a := by
  let := e
  simp [queryCodeWith]

/-- An undecodable coordinate of `queryCodeWith` is padded with `false`. -/
theorem queryCodeWith_eq_false_of_decode_eq_none (e : Encodable (Atom L V))
    (c : RelationalConfiguration L V) {n : ℕ} (hn : @Encodable.decode _ e n = none) :
    queryCodeWith e c n = false := by
  simp [queryCodeWith, hn]

/-- At a coordinate decoding to an atom `a`, `queryCodeWith` reads `c.eval a`. -/
theorem queryCodeWith_eq_eval_of_decode_eq_some (e : Encodable (Atom L V))
    (c : RelationalConfiguration L V) {n : ℕ} {a : Atom L V}
    (hn : @Encodable.decode _ e n = some a) : queryCodeWith e c n = c.eval a := by
  simp [queryCodeWith, hn]

/-- The all-false configuration encodes to the all-false sequence. -/
@[simp]
theorem queryCodeWith_mk_false (e : Encodable (Atom L V)) :
    queryCodeWith e (mk fun _ => false) = fun _ => false := by
  funext n
  cases h : @Encodable.decode _ e n <;> simp [queryCodeWith, h]

/-- `queryCodeWith e` is injective: every atom appears at its encoded coordinate. -/
theorem queryCodeWith_injective (e : Encodable (Atom L V)) :
    Function.Injective (queryCodeWith e) := by
  intro c d h
  ext a
  have ha := congrFun h (@Encodable.encode _ e a)
  simpa using ha

/-- Two configurations have the same query code iff they are equal. -/
@[simp]
theorem queryCodeWith_eq_iff (e : Encodable (Atom L V)) {c d : RelationalConfiguration L V} :
    queryCodeWith e c = queryCodeWith e d ↔ c = d :=
  (queryCodeWith_injective e).eq_iff

/-- `queryCodeWith e` is continuous into Cantor space `ℕ → Bool`. -/
@[fun_prop]
theorem continuous_queryCodeWith (e : Encodable (Atom L V)) :
    Continuous (queryCodeWith e) := by
  refine continuous_pi fun n => ?_
  cases h : @Encodable.decode _ e n with
  | none => simpa [queryCodeWith, h] using continuous_const
  | some a => simpa [queryCodeWith, h] using continuous_eval a

/-- `queryCodeWith e` is measurable for the product σ-algebras. -/
@[fun_prop]
theorem measurable_queryCodeWith (e : Encodable (Atom L V)) :
    Measurable (queryCodeWith e) := by
  refine measurable_pi_iff.2 fun n => ?_
  cases h : @Encodable.decode _ e n with
  | none => simp [queryCodeWith, h]
  | some a => simpa [queryCodeWith, h] using measurable_eval a

/-- `queryCodeWith e` is a closed embedding of `RelationalConfiguration L V` into Cantor space. -/
theorem isClosedEmbedding_queryCodeWith (e : Encodable (Atom L V)) :
    IsClosedEmbedding (queryCodeWith e) :=
  (continuous_queryCodeWith e).isClosedEmbedding (queryCodeWith_injective e)

/-- **Tree representation of analytic classes of configurations** (explicit-encoding form).
Every analytic set `A` of relational configurations is represented by a descriptive tree `T` on
`Bool × ℕ` via `queryCodeWith e`. -/
theorem exists_tree_of_analyticSet_with (e : Encodable (Atom L V))
    {A : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) :
    ∃ T : tree (Bool × ℕ),
      A = {c | ∃ g : ℕ → ℕ, (fun n => (queryCodeWith e c n, g n)) ∈ body T} := by
  obtain ⟨T, hT⟩ := (hA.image_of_continuous (continuous_queryCodeWith e)).exists_tree_eq
  refine ⟨T, ?_⟩
  ext c
  rw [← (queryCodeWith_injective e).mem_set_image, hT]
  rfl

/-! ### Canonical query code -/

/-- The canonical **query code** of a relational configuration, obtained from
`Encodable.ofCountable (Atom L V)`. -/
noncomputable def queryCode [Countable (Atom L V)] (c : RelationalConfiguration L V) :
    ℕ → Bool :=
  queryCodeWith (Encodable.ofCountable (Atom L V)) c

/-- `queryCode` is `queryCodeWith` for `Encodable.ofCountable (Atom L V)`. -/
theorem queryCode_eq_queryCodeWith [Countable (Atom L V)] :
    queryCode (L := L) (V := V) = queryCodeWith (Encodable.ofCountable (Atom L V)) := (rfl)

/-- Reading `queryCode` at the `Encodable.ofCountable` code of an atom recovers its value. -/
@[simp]
theorem queryCode_encode [Countable (Atom L V)] (c : RelationalConfiguration L V)
    (a : Atom L V) :
    queryCode c (@Encodable.encode _ (Encodable.ofCountable (Atom L V)) a) = c.eval a :=
  queryCodeWith_encode (Encodable.ofCountable (Atom L V)) c a

/-- The all-false configuration has the all-false canonical query code. -/
@[simp]
theorem queryCode_mk_false [Countable (Atom L V)] :
    queryCode (L := L) (V := V) (mk fun _ => false) = fun _ => false :=
  queryCodeWith_mk_false (Encodable.ofCountable (Atom L V))

/-- The canonical query code is injective. -/
theorem queryCode_injective [Countable (Atom L V)] :
    Function.Injective (queryCode (L := L) (V := V)) :=
  queryCodeWith_injective (Encodable.ofCountable (Atom L V))

/-- Two configurations have the same canonical query code iff they are equal. -/
@[simp]
theorem queryCode_eq_iff [Countable (Atom L V)] {c d : RelationalConfiguration L V} :
    queryCode c = queryCode d ↔ c = d :=
  queryCodeWith_eq_iff (Encodable.ofCountable (Atom L V))

/-- The canonical query code is continuous. -/
@[fun_prop]
theorem continuous_queryCode [Countable (Atom L V)] :
    Continuous (queryCode (L := L) (V := V)) :=
  continuous_queryCodeWith (Encodable.ofCountable (Atom L V))

/-- The canonical query code is measurable for the product σ-algebras. -/
@[fun_prop]
theorem measurable_queryCode [Countable (Atom L V)] :
    Measurable (queryCode (L := L) (V := V)) :=
  measurable_queryCodeWith (Encodable.ofCountable (Atom L V))

/-- The canonical query code is a closed embedding into Cantor space `ℕ → Bool`. -/
theorem isClosedEmbedding_queryCode [Countable (Atom L V)] :
    IsClosedEmbedding (queryCode (L := L) (V := V)) :=
  isClosedEmbedding_queryCodeWith (Encodable.ofCountable (Atom L V))

/-- **Tree representation of analytic classes of configurations.** Every analytic set of
configurations over a countable atom set is the projection of the body of a descriptive tree on
`Bool × ℕ` along `queryCode`. -/
theorem exists_tree_of_analyticSet [Countable (Atom L V)]
    {A : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) :
    ∃ T : tree (Bool × ℕ),
      A = {c | ∃ g : ℕ → ℕ, (fun n => (queryCode c n, g n)) ∈ body T} :=
  exists_tree_of_analyticSet_with (Encodable.ofCountable (Atom L V)) hA

end TauCeti.RelationalConfiguration
