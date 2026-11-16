/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Average
public import TauCeti.MeasureTheory.Group.Foelner.Int
import TauCeti.GroupTheory.Amenable.Multiplicative

/-!
# Amenability of the integers

The intervals `{0, …, n}` form a counting-measure additive Følner sequence
(`TauCeti.isAddFoelner_int_Icc`), so `ℤ` has additive Følner sets and is additively amenable for
every additive group topology. Transporting through `Multiplicative.ofAdd` gives the corresponding
statements for `Multiplicative ℤ`.

Amenability of the integers is the starting example for proving amenability of commutative groups
using finite products and homomorphic images.

## Main results

* `TauCeti.hasAddFoelnerSets_int`, `TauCeti.hasFoelnerSets_multiplicative_int`: `ℤ` has additive
  Følner sets, and `Multiplicative ℤ` has Følner sets.
* `TauCeti.AddAmenable.int`, `TauCeti.Amenable.multiplicative_int`: `ℤ` is additively amenable for
  every additive group topology, and `Multiplicative ℤ` is amenable for every group topology.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

namespace TauCeti

/-- The integers have additive Følner sets, witnessed by the intervals `{0, …, n}`. -/
theorem hasAddFoelnerSets_int : HasAddFoelnerSets ℤ :=
  .of_isAddFoelner isAddFoelner_int_Icc

/-- The integers are amenable as an additive group, for every additive group topology. -/
instance AddAmenable.int
    {integerTopology : TopologicalSpace ℤ}
    [hTopology : letI := integerTopology; IsTopologicalAddGroup ℤ] :
    letI := integerTopology; AddAmenable ℤ := by
  let := integerTopology
  exact .of_hasAddFoelnerSets hasAddFoelnerSets_int

/-- The integer group has Følner sets, viewed multiplicatively through `Multiplicative.ofAdd`. -/
theorem hasFoelnerSets_multiplicative_int : HasFoelnerSets (Multiplicative ℤ) :=
  (hasFoelnerSets_multiplicative_iff ℤ).2 hasAddFoelnerSets_int

/-- The integer group is amenable for every group topology. -/
instance Amenable.multiplicative_int
    {integerTopology : TopologicalSpace (Multiplicative ℤ)}
    [hTopology : letI := integerTopology; IsTopologicalGroup (Multiplicative ℤ)] :
    letI := integerTopology; Amenable (Multiplicative ℤ) := by
  let := integerTopology
  exact .of_hasFoelnerSets hasFoelnerSets_multiplicative_int

end TauCeti
