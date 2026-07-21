/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.PartitionOfUnity

/-! # Positive partitions
In this file, we define "positive partitions" of a space `X` as families of functions `f i : X → ℝ`
with the property that all functions `f i` are nonnegative, that the family
`fun i ↦ Function.support (f i)` is locally finite, and that for every `x` there exists at least
one `i` with `0 < f i x`. These are essentially partitions of unity, just without the requirement
that at all the functions sum to `1`; every partition of unity is a positive partition, and every
positive partition can be turned into a partition of unity by dividing all functions by their sum.

The benefit of positive partitions is that they are easier to construct, and that generalise both
partitions of unity and bump coverings, so that parts of their API could be deduplicated by
generalising it to positive partitions in the future. Since we can't modify definitions from
mathlib in this fork though, we however don't let partitions of unity and bump coverings extend
positive partitions yet.

The term "positive partition" is borrowed from https://arxiv.org/abs/2203.03120, though we
require positive partitions to be locally finite while that paper does not.
-/

open Set Function

open scoped Topology

/-- A continuous positive partition on a set `s : Set X` is a collection of continuous functions
`f i` such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* the functions `f i` are nonnegative;
* at least one `f i x` is positive for each `x ∈ s`.

Every partition of unity is a positive partition, and every (global) positive partition can be
turned into a partition of unity by dividing all functions by their sum. The existence of
positive partitions and partitions of unity subordinate to any given cover is hence equivalent;
the utility of positive partitions is that they are easier to construct, and hence
allow you to obtain partitions of unity just by giving a positive partition.
-/
structure PositivePartition (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collection of continuous functions underlying this partition of unity -/
  toFun : ι → C(X, ℝ)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- at least one function is positive at every point in `s` -/
  exists_pos' : ∀ x ∈ s, ∃ i, 0 < toFun i x

namespace PositivePartition

variable {X ι : Type*} [TopologicalSpace X] {s : Set X} (f : PositivePartition ι X s)
    {u : ι → Set X}

instance : FunLike (PositivePartition ι X s) ι C(X, ℝ) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[simp]
lemma coe_mk (toFun : ι → C(X, ℝ)) (locallyFinite' : LocallyFinite fun i => support (toFun i))
    (nonneg' : 0 ≤ toFun) (exists_pos' : ∀ x ∈ s, ∃ i, 0 < toFun i x) {i : ι} :
  PositivePartition.mk toFun locallyFinite' nonneg' exists_pos' i = toFun i := rfl

protected lemma locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

lemma locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

lemma nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

/-- If `f` is a partition of unity on `s`, then for every `x ∈ s` there exists an index `i` such
that `0 < f i x`. -/
lemma exists_pos {x : X} (hx : x ∈ s) : ∃ i, 0 < f i x :=
  f.exists_pos' _ hx

lemma sum_pos {x : X} (hx : x ∈ s) : 0 < ∑ᶠ i, f i x :=
  finsum_pos (f.nonneg · x) (f.exists_pos hx) (f.locallyFinite.point_finite x)

lemma continuous_sum : Continuous fun x ↦ ∑ᶠ i, f i x :=
  continuous_finsum (fun i ↦ map_continuous (f i)) f.locallyFinite

/-- The partition of unity obtained from a positive partition by dividing all functions by their
sum. -/
noncomputable def toPartitionOfUnity (f : PositivePartition ι X) : PartitionOfUnity ι X where
  toFun i := ⟨_, (map_continuous (f i)).div f.continuous_sum fun x ↦ (f.sum_pos trivial).ne'⟩
  locallyFinite' := by
    suffices h : support (fun x ↦ ∑ᶠ (i : ι), f i x) = univ by simp [h, f.locallyFinite]
    exact eq_univ_of_forall fun x ↦ (f.sum_pos trivial).ne'
  nonneg' i x := by simpa using div_nonneg (f.nonneg i x) (f.sum_pos trivial).le
  sum_eq_one' := by
    simp [div_eq_mul_inv, ← finsum_mul, fun x ↦ (f.sum_pos (mem_univ x)).ne']
  sum_le_one' := by
    simp [div_eq_mul_inv, ← finsum_mul, fun x ↦ (f.sum_pos (mem_univ x)).ne']

-- TODO: move
@[simp]
lemma _root_.PartitionOfUnity.coe_mk (toFun : ι → C(X, ℝ))
    (locallyFinite' : LocallyFinite fun i => support (toFun i))
    (nonneg' : 0 ≤ toFun) (sum_eq_one' : ∀ x ∈ s, ∑ᶠ (i : ι), (toFun i) x = 1)
    (sum_le_one' : ∀ (x : X), ∑ᶠ (i : ι), (toFun i) x ≤ 1) {i : ι} :
  PartitionOfUnity.mk toFun locallyFinite' nonneg' sum_eq_one' sum_le_one' i = toFun i := rfl

@[simp]
lemma support_toPartitionOfUnity (f : PositivePartition ι X) {i : ι} :
    support (f.toPartitionOfUnity i) = support (f i) := by
  suffices h : support (fun x ↦ ∑ᶠ (i : ι), f i x) = univ by simp [toPartitionOfUnity, h]
  exact eq_univ_of_forall fun x ↦ (f.sum_pos trivial).ne'

@[simp]
lemma tsupport_toPartitionOfUnity (f : PositivePartition ι X) {i : ι} :
    tsupport (f.toPartitionOfUnity i) = tsupport (f i) := by
  simp [tsupport]

/-- The positive partition underlying a partition of unity.

TODO: when upstreaming positive partitions to mathlib, let `PartitionOfUnity` extend
`PositivePartition` instead of making this a definition. -/
def _root_.PartitionOfUnity.toPositivePartition (f : PartitionOfUnity ι X s) :
    PositivePartition ι X s where
  __ := f
  exists_pos' _ hx := f.exists_pos hx

@[simp]
lemma _root_.PartitionOfUnity.toPartitionOfUnity_toPositivePartition (f : PartitionOfUnity ι X) :
    f.toPositivePartition.toPartitionOfUnity = f := by
  cases f
  simp only [toPartitionOfUnity, PartitionOfUnity.toPositivePartition, coe_mk,
    PartitionOfUnity.mk.injEq]
  ext i x
  simp [*]

-- TODO: move
@[simp]
lemma _root_.PartitionOfUnity.toFun_eq_coe (f : PartitionOfUnity ι X s) : f.toFun = f := rfl

@[simp]
lemma _root_.PartitionOfUnity.support_toPositivePartition (f : PartitionOfUnity ι X s) {i : ι} :
    support (f.toPositivePartition i) = support (f i) := by
  simp [PartitionOfUnity.toPositivePartition]

@[simp]
lemma _root_.PartitionOfUnity.tsupport_toPositivePartition (f : PartitionOfUnity ι X s) {i : ι} :
    tsupport (f.toPositivePartition i) = tsupport (f i) := by
  simp [tsupport]

def IsSubordinate (u : ι → Set X) := ∀ i, tsupport (f i) ⊆ u i

lemma IsSubordinate.toPartitionOfUnity {f : PositivePartition ι X} (hf : f.IsSubordinate u) :
    f.toPartitionOfUnity.IsSubordinate u := by
  simpa [IsSubordinate, PartitionOfUnity.IsSubordinate] using hf

lemma _root_.PartitionOfUnity.IsSubordinate.toPositivePartition {f : PartitionOfUnity ι X s}
    (hf : f.IsSubordinate u) :
    f.toPositivePartition.IsSubordinate u := by
  simpa [IsSubordinate, PartitionOfUnity.IsSubordinate] using hf

end PositivePartition
