/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.ContinuousMulActionHom
import ClassifyingBundles.Equiv
import ClassifyingBundles.Join
import ClassifyingBundles.LocallyTrivialSMul
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Topology.Homotopy.Contractible

/-! # Joins of topological spaces
In this file we define joins of families of topological spaces.

## Main definitions & results
* `IJoin X`: the join of a family of topological spaces `X i`. We equip this with Milnor's coarse
  topology, i.e. the topology induced by all the projections `IJoin.weights i` and `IJoin.points i`.
* `IJoin.weights`: the projection `IJoin X → StdSimplex ℝ ι` of each point to its weights.
  While there is no canonical topology on `StdSimplex ℝ ι`, this is continuous at least in the sense
  that each component function `IJoin.weights i : IJoin X → ℝ` is.
* `IJoin.points i`: the projection `IJoin X → Option (X i)`. This is always continuous, and sends
  `x` to `none` if and only if `x.weights i` vanishes.
* `IJoin.of i`: the inclusion `X i → IJoin X`. This is always continuous.
* `IJoin.ofJoin h`: the inclusion `X i ⋆ X j → IJoin X` when `h : i ≠ j`. This is always continuous.
* `IJoin.map hf g`: the map `IJoin X → IJoin X'` induced by an injective map `f : ι → ι'` and a
  family of maps `g i : X i → X' (f i)`. This is always continuous.
* When `G` acts on each `X i`, it also acts on `IJoin X`. This action is effective / free /
  continuous whenever the actions on the `X i` are.
* Arbitrary joins `IJoin fun _ ↦ G` of copies of a single topological group `G` are locally trivial
* Any two equivariant maps into `IJoin fun _ : ℕ ↦ G` are equivariantly homotopic
* `IJoin fun _ : ℕ ↦ G` is contractible

## TODO
* Prove that `IJoin.of` and `IJoin.ofJoin` are closed embeddings
* Connect to iterated binary joins, use this to prove associativity of binary joins
* prove that joins of Hausdorff spaces are Hausdorff
* define Fσ sets, prove that Fσ sets in paracompact spaces are paracompact, use that to prove that
  infinite joins of compact Hausdorff spaces are paracompact
* prove that for every nonempty space `X` and infinite type `ι`, `IJoin fun _ : ι ↦ X` is
  contractible. We already obtained this for countable joins of groups as a corollary of the fact
  that any two equivariant maps into `IJoin fun _ : ℕ ↦ G` are equivariantly homotopic; the proof
  of contractibilit for general spaces will have to repeat part of the proof of that fact instead
  of building on top of it.
-/

namespace Topology

open Convexity

open scoped unitInterval

/-- The join of a family `X : ι → Type*` of topological spaces is defined as an element of
`StdSimplex ℝ ι`, i.e. a finitely supported function `weights : ι →₀ ℝ` of nonnegative numbers that
sum to `0`, together with an element of `X i` for each positive `weight i`. -/
structure IJoin {ι : Type*} (X : ι → Type*) extends StdSimplex ℝ ι where
  points (i : ι) : Option (X i)
  points_eq_none_iff {i : ι} : points i = none ↔ weights i = 0

namespace IJoin

variable {ι : Type*} {X : ι → Type*}

@[ext]
lemma ext {p p' : IJoin X} (h : p.weights = p'.weights)
    (h' : ∀ i, 0 < p.weights i → p.points i = p'.points i) : p = p' := by
  suffices p.points = p'.points by cases p; cases p'; simp_all
  ext1 i
  by_cases hi : 0 < p.weights i
  · exact h' i hi
  · rw [(p.weights_nonneg i).lt_iff_ne', not_not] at hi
    rw [p.points_eq_none_iff.2 hi, p'.points_eq_none_iff.2 <| h ▸ hi]

@[simp]
lemma points_isSome_iff {x : IJoin X} {i : ι} : (x.points i).isSome ↔ 0 < x.weights i := by
  simp [(x.weights_nonneg i).lt_iff_ne', ← x.points_eq_none_iff, Option.isSome_iff_ne_none]

/-- The canonical inclusion `X i → IJoin X`. -/
@[simps! points weights]
noncomputable def of [DecidableEq ι] (i : ι) (x : X i) : IJoin X where
  points := Function.update (fun _ ↦ none) i x
  toStdSimplex := .single i
  points_eq_none_iff := by grind [StdSimplex.weights_single]

lemma of_injective [DecidableEq ι] {i : ι} : Function.Injective (of (X := X) i) := by
  refine .of_comp (f := fun x ↦ x.points i) ?_
  convert Option.some_injective (X i)
  ext; simp

/-- The canonical inclusion `X i ⋆ X j → IJoin X` when `i ≠ j`. -/
@[simps!]
noncomputable def ofJoin [DecidableEq ι] {i j : ι} (h : i ≠ j) (x : X i ⋆ X j) : IJoin X where
  points := Function.update (Function.update (fun _ ↦ none) i x.fst) j x.snd
  toStdSimplex := .duple i j (σ x.t).2.1 x.t.2.1 (by simp)
  points_eq_none_iff := by
    intro k
    obtain rfl | _ := eq_or_ne k i
    · simp [h, -unitInterval.coe_symm_eq]
    · obtain rfl | _ := eq_or_ne k j
      · simp [h]
      · simp [‹k ≠ i›, ‹k ≠ j›]

/-- Any injection `ι → ι'` together with a family of maps `g i : X i → X' (f i)` induces a map
`IJoin X → IJoin X'`. The way this is defined is somewhat awkward to express formally:
`(map hf g x).points i` should be `x.points i'` for the unique `i'` with `f i' = i` when it exists
and `none` otherwise, but `g i'` is a map from `X i'` to `X' (f i')`, which is propositionally but
not definitionally equal to `X' i`, so a cast is needed. To not expose this too much,
we provide an API lemma applying `(map hf g x).points` to `f i` for some `i` instead of to a general
`i`. -/
@[simps! toStdSimplex weights]
noncomputable def map {ι' : Type*} {X' : ι' → Type*} {f : ι → ι'} [∀ i, Decidable (∃ i', f i' = i)]
    (hf : f.Injective) (g : ∀ i, X i → X' (f i)) (x : IJoin X) : IJoin X' where
  points i := if h : ∃ i', f i' = i then
    Option.map (Equiv.congrArg X' h.choose_spec ∘ g h.choose) (x.points h.choose) else none
  toStdSimplex := x.toStdSimplex.map f
  points_eq_none_iff := by
    intro i
    by_cases h : ∃ i', f i' = i
    · simp only [dite_eq_right_iff, h, forall_true_left, Option.map_eq_none_iff]
      rw [x.points_eq_none_iff, ← Finsupp.mapDomain_apply hf, h.choose_spec, StdSimplex.weights_map]
    · simpa [h] using Finsupp.mapDomain_notin_range _ _ h

@[simp]
lemma map_points_apply {ι' : Type*} {X' : ι' → Type*} {f : ι → ι'} [∀ i, Decidable (∃ i', f i' = i)]
    (hf : f.Injective) (g : ∀ i, X i → X' (f i)) {x : IJoin X} {i : ι} :
    (map hf g x).points (f i) = Option.map (g i) (x.points i) := by
  simp only [map, exists_apply_eq_apply, ↓reduceDIte]
  convert rfl using 2
  · rw [hf (exists_apply_eq_apply f i).choose_spec]
  · rw! [hf (exists_apply_eq_apply f i).choose_spec]
    simp
  · rw [hf (exists_apply_eq_apply f i).choose_spec]

@[simp]
lemma map_points_of_nonMem {ι' : Type*} {X' : ι' → Type*} {f : ι → ι'}
    [∀ i, Decidable (∃ i', f i' = i)] (hf : f.Injective) (g : ∀ i, X i → X' (f i)) {x : IJoin X}
    {i : ι'} (hi : i ∉ Set.range f) : (map hf g x).points i = none := by
  simp [map, show ¬ ∃ i', f i' = i from hi]

@[simp]
lemma map_of [DecidableEq ι] {ι' : Type*} [DecidableEq ι'] {X' : ι' → Type*} {f : ι → ι'}
    [∀ i, Decidable (∃ i', f i' = i)]
    (hf : f.Injective) (g : ∀ i, X i → X' (f i)) {i : ι} (x : X i) :
    map hf g (of i x) = of (f i) (g i x) := by
  ext i' hi' x'
  · simp
  · rw [map_weights, of_weights, Finsupp.mapDomain_single] at hi'
    replace hi' : i' = f i := by simpa using Finsupp.single_apply_ne_zero.1 hi'.ne'
    obtain rfl := hi'
    simp

@[simp]
lemma map_ofJoin [DecidableEq ι] {ι' : Type*} [DecidableEq ι'] {X' : ι' → Type*} {f : ι → ι'}
    [∀ i, Decidable (∃ i', f i' = i)]
    (hf : f.Injective) (g : ∀ i, X i → X' (f i)) {i j : ι} (h : i ≠ j) (x : X i ⋆ X j) :
    map hf g (ofJoin h x) = ofJoin (hf.ne h) (x.map (g i) (g j)) := by
  ext i' hi' x'
  · simp [ofJoin]
  · suffices h : i' = f i ∨ i' = f j by obtain rfl | rfl := h <;> simp [hf.ne h, h]
    obtain ⟨i'', rfl⟩ : ∃ i'', f i'' = i' := by
      by_contra h; exact hi'.ne' (Finsupp.mapDomain_notin_range _ _ h)
    by_contra h
    rw [not_or, ← ne_eq, ← ne_eq, hf.ne_iff, hf.ne_iff] at h
    simp [Finsupp.mapDomain_apply hf, h] at hi'

lemma map_map {ι' ι'' : Type*} {X' : ι' → Type*} {X'' : ι'' → Type*} {f : ι → ι'}
    [∀ i, Decidable (∃ i', f i' = i)] (hf : f.Injective) {g : ∀ i, X i → X' (f i)} {f' : ι' → ι''}
    [∀ i', Decidable (∃ i'', f' i'' = i')] (hf' : f'.Injective) {g' : ∀ i', X' i' → X'' (f' i')}
    [∀ i', Decidable (∃ i'', (f' ∘ f) i'' = i')] {x : IJoin X} :
    map hf' g' (map hf g x) = map (hf'.comp hf) (fun i ↦ g' (f i) ∘ g i) x := by
  ext i'' hi'' x''
  · simp [Finsupp.mapDomain_comp]
  · obtain ⟨i', rfl⟩ : ∃ i', f' i' = i'' := by
      by_contra h; exact hi''.ne' (Finsupp.mapDomain_notin_range _ _ h)
    rw [map_weights, Finsupp.mapDomain_apply hf'] at hi''
    obtain ⟨i, rfl⟩ : ∃ i, f i = i' := by
      by_contra h; exact hi''.ne' (Finsupp.mapDomain_notin_range _ _ h)
    rw [map_points_apply, map_points_apply]
    rw! (castMode := .all) [show f' (f i) = (f' ∘ f) i from rfl]
    rw [map_points_apply]
    simp

lemma map_injective {ι' : Type*} {X' : ι' → Type*} {f : ι → ι'} [∀ i, Decidable (∃ i', f i' = i)]
    (hf : f.Injective) {g : ∀ i, X i → X' (f i)} (hg : ∀ i, (g i).Injective) :
    (map hf g).Injective := by
  intro x x' h
  refine ext ?_ fun i hi ↦ ?_
  · exact Finsupp.mapDomain_injective hf <| congrArg (fun x : IJoin X' ↦ x.weights) h
  · have h' := congrArg (fun x ↦ x.points (f i)) h
    simp only [map_points_apply] at h'
    exact Option.map_injective (hg i) h'

lemma nonempty_iff : Nonempty (IJoin X) ↔ ∃ i, Nonempty (X i) := by
  classical
  refine ⟨fun ⟨x⟩ ↦ ?_, fun ⟨i, ⟨x⟩⟩ ↦ ⟨of i x⟩⟩
  have ⟨i, hi⟩ := x.support_weights_nonempty
  exact ⟨i, ⟨(Option.ne_none_iff_exists.1 <| x.points_eq_none_iff.not.2 <|
    Finsupp.mem_support_iff.1 hi).choose⟩⟩

instance [Nonempty ι] [∀ i, Nonempty (X i)] : Nonempty (IJoin X) :=
  nonempty_iff.2 ⟨Classical.arbitrary _, inferInstance⟩

attribute [local instance] Option.excludedPointTopology'

variable [∀ i, TopologicalSpace (X i)]

/-- The "strong topology" on `IJoin X` as defined by Milnor, i.e. the coarsest topology making all
the projections to `ℝ` and `X i` continuous where they are defined. -/
instance : TopologicalSpace (IJoin X) :=
  (⨅ i, .induced (fun x ↦ x.weights i) inferInstance) ⊓
    ⨅ i, Option.excludedPointTopology'.induced fun x ↦ x.points i

lemma continuous_iff {Y : Type*} [TopologicalSpace Y] {f : Y → IJoin X} :
    Continuous f ↔ (∀ i, Continuous (fun y ↦ (f y).weights i)) ∧
      ∀ i, Continuous (fun y ↦ (f y).points i) := by
  refine (continuous_inf_rng (f := f) (t₂ := ⨅ i, _) (t₃ := ⨅ i, _)).trans <| and_congr ?_ ?_
    <;> simp_rw [continuous_iInf_rng, continuous_induced_rng] <;> rfl

lemma continuousOn_iff {Y : Type*} [TopologicalSpace Y] {f : Y → IJoin X} {s : Set Y} :
    ContinuousOn f s ↔ (∀ i, ContinuousOn (fun y ↦ (f y).weights i) s) ∧
      ∀ i, ContinuousOn (fun y ↦ (f y).points i) s := by
  simp only [continuousOn_iff_continuous_restrict]
  exact continuous_iff

lemma nhds_eq_inf {x : IJoin X} :
    𝓝 x = (⨅ i, .comap (fun x ↦ x.weights i) (𝓝 (x.weights i))) ⊓
      (⨅ i, .comap (fun x ↦ x.points i) (𝓝 (x.points i))) := by
  rw [nhds_inf (t₁ := ⨅ i, .induced (fun x ↦ x.weights i) inferInstance)
    (t₂ := ⨅ i, Option.excludedPointTopology'.induced fun x ↦ x.points i) (a := x)]
  simp only [nhds_iInf, nhds_induced]

lemma tendsto_nhds_iff {α : Type*} {f : α → IJoin X} {l : Filter α} {x : IJoin X} :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ i,
      Filter.Tendsto ((fun x ↦ x.weights i) ∘ f) l (𝓝 (x.weights i)) ∧
        Filter.Tendsto ((fun x ↦ x.points i) ∘ f) l (𝓝 (x.points i)) := by
  simp [nhds_eq_inf, Filter.tendsto_inf, Filter.tendsto_iInf, forall_and]

@[fun_prop]
lemma continuous_weights {i : ι} : Continuous fun x : IJoin X ↦ x.weights i :=
  (continuous_iff.1 continuous_id).1 i

@[fun_prop]
lemma continuous_points {i : ι} : Continuous fun x : IJoin X ↦ x.points i :=
  (continuous_iff.1 continuous_id).2 i

lemma continuous_of [DecidableEq ι] {i : ι} : Continuous (of i : X i → IJoin X) :=
  continuous_iff.2 ⟨fun _ ↦ continuous_const, fun j ↦ (continuous_apply j).comp <|
    .update continuous_const i Option.continuous_some_excludedPointTopology'⟩

attribute [local fun_prop] Join.continuous_t in
lemma continuous_ofJoin [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    Continuous (ofJoin h : X i ⋆ X j → IJoin X) := by
  refine continuous_iff.2 ⟨fun i' ↦ ?_, fun i' ↦ ?_⟩
  · simp only [ofJoin_weights_apply]
    suffices ∀ i'', Continuous fun y : X i ⋆ X j ↦ Finsupp.single i'' (y.t : ℝ) i' by fun_prop
    -- note: the issue here is that `Finsupp.single` contains classical decidability instances
    refine fun i ↦ (continuous_apply _).comp <| (@continuous_single _ _ _ _ (_) _).comp ?_
    fun_prop
  · obtain rfl | h' := eq_or_ne i i'
    · simpa [h] using Join.continuous_fst
    · obtain rfl | h'' := eq_or_ne j i'
      · simpa [h] using Join.continuous_snd
      · simpa [h''.symm, h'.symm] using continuous_const

@[fun_prop]
lemma continuous_map {ι' : Type*} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)] {f : ι → ι'}
    [∀ i, Decidable (∃ i', f i' = i)] (hf : f.Injective) {g : ∀ i, X i → X' (f i)}
    (hg : ∀ i, Continuous (g i)) : Continuous (map hf g) := by
  refine continuous_iff.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · by_cases h : i ∈ Set.range f
    · obtain ⟨i', rfl⟩ := h
      simp [hf, continuous_weights]
    · simp [Finsupp.mapDomain_notin_range, h, continuous_const]
  · by_cases h : i ∈ Set.range f
    · obtain ⟨i', rfl⟩ := h
      simpa [Function.comp_def] using
        (hg i').optionMap_excludedPointTopology'.comp continuous_points
    · simp [h, continuous_const]

/-- The homeomorphism of joins given by a family of homeomorphisms of the factors along a
bijection between the index types. In particular, when the two index types are the same
this proves associativity of the join. -/
@[simps! apply symm_apply_weights]
noncomputable def _root_.Homeomorph.ijoinCongr {ι' : Type*} {X' : ι' → Type*}
    [∀ i, TopologicalSpace (X' i)] (e : ι ≃ ι') [∀ i, Decidable (∃ i', e i' = i)]
    [∀ i, Decidable (∃ i', e.symm i' = i)] (e' : ∀ i, X i ≃ₜ X' (e i)) : IJoin X ≃ₜ IJoin X' where
  toFun := map e.injective fun i ↦ e' i
  invFun := map e.symm.injective fun i x ↦ (e' (e.symm i)).symm <|
    Equiv.congrArg X' (e.apply_symm_apply i).symm x
  left_inv := by
    refine Function.RightInverse.leftInverse_of_injective (fun x ↦ ?_) <|
      map_injective e.injective fun i ↦ (e' i).injective
    classical
    simp only [map_map, Function.comp_def, Function.comp_apply, Homeomorph.apply_symm_apply]
    refine ext ?_ fun i _ ↦ ?_
    · simp [show (fun x : ι' ↦ x) = id from rfl]
    · obtain ⟨i', rfl⟩ : ∃ i', (e ∘ e.symm) i' = i := ⟨_, e.apply_symm_apply i⟩
      have : ∀ i j (h : i = j) (f : (i : _) → Option (X' i)),
          Option.map (fun x ↦ Equiv.congrArg X' h x) (f i) = f j := by
        rintro i j rfl; simp
      simpa using this _ _ (by simp) _
  right_inv x := by
    classical
    simp only [map_map, Function.comp_def, Function.comp_apply, Homeomorph.apply_symm_apply]
    refine ext ?_ fun i _ ↦ ?_
    · simp [show (fun x : ι' ↦ x) = id from rfl]
    · obtain ⟨i', rfl⟩ : ∃ i', (e ∘ e.symm) i' = i := ⟨_, e.apply_symm_apply i⟩
      have : ∀ i j (h : i = j) (f : (i : _) → Option (X' i)),
          Option.map (fun x ↦ Equiv.congrArg X' h x) (f i) = f j := by
        rintro i j rfl; simp
      simpa using this _ _ (by simp) _

@[simp]
lemma _root_.Homeomorph.ijoinCongr_symm_apply_points {ι' : Type*} {X' : ι' → Type*}
    [∀ i, TopologicalSpace (X' i)] (e : ι ≃ ι') [∀ i, Decidable (∃ i', e i' = i)]
    [∀ i, Decidable (∃ i', e.symm i' = i)] (e' : ∀ i, X i ≃ₜ X' (e i)) {x : IJoin X'} {i : ι} :
    ((Homeomorph.ijoinCongr e e').symm x).points i = Option.map (e' i).symm (x.points (e i)) := by
  obtain ⟨x', rfl⟩ : ∃ x', Homeomorph.ijoinCongr e e' x' = x :=
    ⟨_, (Homeomorph.ijoinCongr e e').apply_symm_apply x⟩
  rw [Homeomorph.symm_apply_apply]
  simp

section ConvexComb

lemma _root_.Finsupp.sum_eq_zero_iff_of_nonneg {α M N : Type*} [Zero M] [AddCommMonoid N]
    [PartialOrder N] [IsOrderedCancelAddMonoid N] {f : α →₀ M} {g : α → M → N}
    (hg : ∀ a ∈ f.support, 0 ≤ g a (f a)) :
    f.sum g = 0 ↔ ∀ a ∈ f.support, g a (f a) = 0 :=
  Finset.sum_eq_zero_iff_of_nonneg hg

lemma _root_.Finsupp.mapDomain_support_of_nonneg {α β M : Type*} [DecidableEq β] [AddCommMonoid M]
    [PartialOrder M] [IsOrderedCancelAddMonoid M] {f : α → β} {s : α →₀ M} (hs : ∀ a, 0 ≤ s a) :
    (s.mapDomain f).support = Finset.image f s.support := by
  ext a
  rw [← not_iff_not, Finsupp.notMem_support_iff, Finsupp.mapDomain, Finsupp.sum_apply,
    Finsupp.sum_eq_zero_iff_of_nonneg fun a' _ ↦ by
      simp [Finsupp.single_apply, ite_nonneg (hs a') le_rfl]]
  grind

lemma _root_.Convexity.StdSimplex.weights_pos_iff {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {x : StdSimplex R ι} {i : ι} :
    0 < x.weights i ↔ x.weights i ≠ 0 :=
  (x.nonneg i).lt_iff_ne'

lemma _root_.Convexity.StdSimplex.weights_sConvexComb_support [DecidableEq ι]
    {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [NoZeroDivisors R]
    {f : StdSimplex R (StdSimplex R ι)} :
    (Convexity.sConvexComb f).weights.support =
      f.weights.support.biUnion fun f' ↦ f'.weights.support := by
  ext i
  rw [← not_iff_not, StdSimplex.weights_sConvexComb, Finsupp.notMem_support_iff, Finsupp.sum_apply,
    Finsupp.sum_eq_zero_iff_of_nonneg fun f' ↦ by simp [mul_nonneg (f.nonneg f') (f'.nonneg i)]]
  simp only [Finset.mem_biUnion, not_exists, not_and, Finsupp.mem_support_iff]
  exact forall₂_congr fun f' hf' ↦ by simp [hf']

lemma _root_.Convexity.StdSimplex.weights_map_support {R : Type*} [PartialOrder R] [Semiring R]
    [IsStrictOrderedRing R] {M N : Type*} [DecidableEq N] {g : M → N} {f : StdSimplex R M} :
    (StdSimplex.map g f).weights.support = Finset.image g f.weights.support := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain_support_of_nonneg fun i ↦ f.nonneg i]

lemma _root_.Convexity.StdSimplex.weights_duple_support {R : Type*} [PartialOrder R] [Semiring R]
    {M : Type*} [DecidableEq M] [IsStrictOrderedRing R]
    {x y : M} {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) :
    (StdSimplex.duple x y hs ht h).weights.support ⊆ {x, y} :=
  Finsupp.support_add.trans <| by grind

/-- Take a convex combination of finitely many points in `IJoin X`, provided that for any two
points `x`, `x'` among them `x.points` and `x'.points` agree where both are defined.

Notably, restriction means that `IJoin X` is not a `ConvexSpace` in the sense of the convexity API -
we nonetheless try to keep the API here similar to the convexity API. -/
@[simps! toStdSimplex]
noncomputable def sConvexComb [DecidableEq ι] (f : StdSimplex ℝ (IJoin X))
    (_hf : ∀ x ∈ f.weights.support, ∀ x' ∈ f.weights.support,
      ∀ i ∈ (x.weights.support ∩ x'.weights.support), x.points i = x'.points i) : IJoin X where
  toStdSimplex := iConvexComb f (fun x ↦ x.toStdSimplex)
  points i :=
    if h : ∃ x ∈ f.weights.support, i ∈ x.weights.support then h.choose.points i else none
  points_eq_none_iff {i} := by
    classical
    rw [← Finsupp.notMem_support_iff, iConvexComb, StdSimplex.weights_sConvexComb_support,
      Finset.mem_biUnion, StdSimplex.weights_map_support]
    simp [points_eq_none_iff, show ∀ (h : ∃ a, (fun x ↦ ¬f.weights x = 0 ∧ ¬x.weights i = 0) a),
      h.choose.weights i ≠ 0 from fun h ↦ h.choose_spec.2]

omit [∀ i, TopologicalSpace (X i)] in
lemma sConvexComb_points_apply [DecidableEq ι] {f : StdSimplex ℝ (IJoin X)}
    {hf : ∀ x ∈ f.weights.support, ∀ x' ∈ f.weights.support,
      ∀ i ∈ (x.weights.support ∩ x'.weights.support), x.points i = x'.points i}
    {x : IJoin X} (hx : x ∈ f.weights.support) {i : ι} (hi : i ∈ x.weights.support) :
    (sConvexComb f hf).points i = x.points i := by
  dsimp [sConvexComb]
  have h : ∃ x ∈ f.weights.support, i ∈ x.weights.support := ⟨x, hx, hi⟩
  rw [dif_pos h]
  exact hf _ h.choose_spec.1 x hx _ <| Finset.mem_inter_of_mem h.choose_spec.2 hi

/-- Take a convex combination of two points `x`, `x'` in `IJoin X`, provided that
`x.points` and `x'.points` agree where both are defined. -/
noncomputable def convexCombPair [DecidableEq ι] (x x' : IJoin X) (t : unitInterval)
    (h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i) : IJoin X :=
  sConvexComb (.duple x x' (unitInterval.symm t).2.1 t.2.1 (by simp)) <| by
    intro x'' hx'' x''' hx'''
    classical
    replace hx'' : x'' = x ∨ x'' = x' := by simpa using StdSimplex.weights_duple_support _ _ _ hx''
    replace hx''' : x''' = x ∨ x''' = x' := by
      simpa using StdSimplex.weights_duple_support _ _ _ hx'''
    grind

omit [∀ i, TopologicalSpace (X i)] in
@[simp]
lemma convexCombPair_toStdSimplex [DecidableEq ι] {x x' : IJoin X} {t : unitInterval}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} :
    (convexCombPair x x' t h).toStdSimplex =
      Convexity.convexCombPair _ _ (unitInterval.symm t).2.1 t.2.1 (by simp)
        x.toStdSimplex x'.toStdSimplex := by
  simp [convexCombPair, iConvexComb, Convexity.convexCombPair]

omit [∀ i, TopologicalSpace (X i)] in
lemma convexCombPair_points_apply_left [DecidableEq ι] {x x' : IJoin X} {t : unitInterval}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} (ht : t ≠ 1)
    {i : ι} (hi : i ∈ x.weights.support) : (convexCombPair x x' t h).points i = x.points i := by
  refine sConvexComb_points_apply ?_ hi
  classical
  simp only [StdSimplex.weights_duple, Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply]
  grind [unitInterval.coe_ne_one.2 ht]

omit [∀ i, TopologicalSpace (X i)] in
lemma convexCombPair_points_apply_right [DecidableEq ι] {x x' : IJoin X} {t : unitInterval}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} (ht : t ≠ 0)
    {i : ι} (hi : i ∈ x'.weights.support) : (convexCombPair x x' t h).points i = x'.points i := by
  refine sConvexComb_points_apply ?_ hi
  classical
  simp only [StdSimplex.weights_duple, Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply]
  grind [unitInterval.coe_ne_zero.2 ht]

omit [∀ i, TopologicalSpace (X i)] in
lemma convexCombPair_points_apply_left' [DecidableEq ι] {x x' : IJoin X} {t : unitInterval}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} {i : ι}
    (hi : x.points i = x'.points i) : (convexCombPair x x' t h).points i = x.points i := by
  obtain hi' | hi' := or_not (p := i ∈ x.weights.support)
  · have hi'' : i ∈ x'.weights.support := by simpa [← points_eq_none_iff, hi] using hi'
    obtain ht | ht := show t ≠ 0 ∨ t ≠ 1 by grind [zero_ne_one]
    · rw [convexCombPair_points_apply_right ht hi'', hi]
    · rw [convexCombPair_points_apply_left ht hi']
  · rw [Finsupp.notMem_support_iff] at hi'
    rw [x.points_eq_none_iff.2 hi', Eq.comm, points_eq_none_iff] at hi
    simp [x.points_eq_none_iff.2 hi', points_eq_none_iff, hi, hi']

omit [∀ i, TopologicalSpace (X i)] in
lemma convexCombPair_points_apply_right' [DecidableEq ι] {x x' : IJoin X} {t : unitInterval}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} {i : ι}
    (hi : x.points i = x'.points i) : (convexCombPair x x' t h).points i = x'.points i := by
  rw [convexCombPair_points_apply_left' hi, hi]

omit [∀ i, TopologicalSpace (X i)] in
@[simp]
lemma convexCombPair_zero [DecidableEq ι] {x x' : IJoin X}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} :
    convexCombPair x x' 0 h = x := by
  refine ext (by simp) fun i hi ↦ convexCombPair_points_apply_left (by simp) ?_
  replace hi : 0 < x.weights i := by simpa [iConvexComb] using hi
  exact Finsupp.mem_support_iff.2 hi.ne'

omit [∀ i, TopologicalSpace (X i)] in
@[simp]
lemma convexCombPair_one [DecidableEq ι] {x x' : IJoin X}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} :
    convexCombPair x x' 1 h = x' := by
  refine ext (by simp) fun i hi ↦ convexCombPair_points_apply_right (by simp) ?_
  replace hi : 0 < x'.weights i := by simpa [iConvexComb] using hi
  exact Finsupp.mem_support_iff.2 hi.ne'

@[fun_prop]
lemma continuous_convexCombPair [DecidableEq ι] {Y : Type*} [TopologicalSpace Y]
    {f f' : Y → IJoin X} (hf : Continuous f) (hf' : Continuous f')
    {f'' : Y → unitInterval} (hf'' : Continuous f'')
    {h : ∀ y, ∀ i ∈ (f y).weights.support ∩ (f' y).weights.support,
      (f y).points i = (f' y).points i} :
    Continuous (fun y ↦ convexCombPair (f y) (f' y) (f'' y) (h y)) := by
  refine continuous_iff.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · simp only [convexCombPair_toStdSimplex, StdSimplex.weights_convexCombPair, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply]
    have : Continuous fun y ↦ (f y).weights i := continuous_weights.comp hf
    have : Continuous fun y ↦ (f' y).weights i := continuous_weights.comp hf'
    fun_prop
  · have h : (fun y ↦ ((f y).convexCombPair (f' y) (f'' y) (h y)).points i) ⁻¹' {none}ᶜ =
        ((fun y ↦ (f y).points i) ⁻¹' {none}ᶜ ∩ f'' ⁻¹' {1}ᶜ) ∪
          ((fun y ↦ (f' y).points i) ⁻¹' {none}ᶜ ∩ f'' ⁻¹' {0}ᶜ) := by
      ext y
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        points_eq_none_iff, convexCombPair_toStdSimplex, unitInterval.coe_symm_eq,
        StdSimplex.weights_convexCombPair, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, ← ne_eq, Set.mem_union, Set.mem_inter_iff,
        ← unitInterval.coe_ne_one, ← unitInterval.coe_ne_zero]
      refine ⟨by grind, fun h ↦ h.rec (fun _ ↦ LT.lt.ne' ?_) (fun _ ↦ LT.lt.ne' ?_)⟩
      · grind [add_pos_of_pos_of_nonneg, mul_pos, mul_nonneg, (f y).nonneg i, (f' y).nonneg i]
      · grind [add_pos_of_nonneg_of_pos, mul_pos, mul_nonneg, (f y).nonneg i, (f' y).nonneg i]
    refine Option.continuous_excludedPointTopology'_iff.2 ⟨?_, ?_⟩
    · rw [h]
      refine .union (.inter (Option.isClosed_none_excludedPointTopology'.isOpen_compl.preimage ?_)
          (isOpen_compl_singleton.preimage hf''))
        (.inter (Option.isClosed_none_excludedPointTopology'.isOpen_compl.preimage ?_)
          (isOpen_compl_singleton.preimage hf'')) <;> fun_prop
    · rw [h]
      refine .union_of_isOpen ?_ ?_
        (.inter (Option.isClosed_none_excludedPointTopology'.isOpen_compl.preimage (by fun_prop))
          (isOpen_compl_singleton.preimage hf''))
        (.inter (Option.isClosed_none_excludedPointTopology'.isOpen_compl.preimage (by fun_prop))
          (isOpen_compl_singleton.preimage hf''))
      · refine .congr (f := fun y ↦ (f y).points i) (by fun_prop) fun y hy ↦ by
          rw [convexCombPair_points_apply_left hy.2]
          simpa [points_eq_none_iff] using hy.1
      · refine .congr (f := fun y ↦ (f' y).points i) (by fun_prop) fun y hy ↦ by
          rw [convexCombPair_points_apply_right hy.2]
          simpa [points_eq_none_iff] using hy.1

/-- TODO: remove next time mathlib is bumped -/
lemma _root_.Finsupp.mem_range_of_mapDomain_ne_zero {α β M : Type*} [AddCommMonoid M] {f : α → β}
    {x : α →₀ M} {b : β} (h : Finsupp.mapDomain f x b ≠ 0) :
    b ∈ Set.range f := by contrapose! h; exact Finsupp.mapDomain_notin_range _ _ h

lemma _root_.Finsupp.exists_of_mapDomain_ne_zero {α β M : Type*} [AddCommMonoid M] {f : α → β}
    {x : α →₀ M} {b : β} (h : Finsupp.mapDomain f x b ≠ 0) : ∃ a, f a = b ∧ x a ≠ 0 := by
  classical
  simpa [and_comm] using Finsupp.mapDomain_support <| Finsupp.mem_support_iff.2 h

omit [∀ i, TopologicalSpace (X i)] in
lemma map_sConvexComb [DecidableEq ι] {ι' : Type*} [DecidableEq ι'] {X' : ι' → Type*}
    {f : ι → ι'} [∀ i, Decidable (∃ i', f i' = i)] (hf : f.Injective) {f' : ∀ i, X i → X' (f i)}
    {f'' : StdSimplex ℝ (IJoin X)} {hf'' : ∀ x ∈ f''.weights.support, ∀ x' ∈ f''.weights.support,
      ∀ i ∈ (x.weights.support ∩ x'.weights.support), x.points i = x'.points i} :
    map hf f' (sConvexComb f'' hf'') = sConvexComb (f''.map (map hf f')) fun x hx x' hx' i hi ↦ by
      classical
      obtain ⟨x, hx'', rfl⟩ := Finset.mem_image.1 <| Finsupp.mapDomain_support hx
      obtain ⟨x', hx''', rfl⟩ := Finset.mem_image.1 <| Finsupp.mapDomain_support hx'
      simp only [map_weights, Finset.mem_inter, Finsupp.mapDomain_support_of_injective hf,
        Finset.mem_image] at hi
      obtain ⟨⟨i, hi, rfl⟩, i', hi', hi''⟩ := hi
      obtain rfl := hf hi''
      simp only [map_points_apply]
      exact congrArg _ <| hf'' _ hx'' _ hx''' _ <| Finset.mem_inter.2 ⟨hi, hi'⟩ := by
  refine ext (by simp [-map_weights, map_iConvexComb]) fun i hi ↦ ?_
  replace hi := Finset.mem_image.1 <| Finsupp.mapDomain_support <| Finsupp.mem_support_iff.2 hi.ne'
  obtain ⟨i, hi, rfl⟩ := hi
  simp only [sConvexComb_toStdSimplex, ← sConvexComb_map, StdSimplex.weights_sConvexComb] at hi
  replace hi := Finset.mem_biUnion.1 <| Finsupp.support_sum hi
  obtain ⟨x, hx, hx'⟩ := hi
  classical
  replace hx := Finset.mem_image.1 <| Finsupp.mapDomain_support hx
  obtain ⟨x, hx, rfl⟩ := hx
  rw [map_points_apply, sConvexComb_points_apply hx (Finsupp.support_smul hx'),
    sConvexComb_points_apply (x := map hf f' x), map_points_apply]
  · rw [StdSimplex.weights_map_support, Finset.mem_image]
    refine ⟨x, hx, rfl⟩
  · simp only [map_weights, Finsupp.mapDomain_support_of_injective,
      Function.Injective.mem_finset_image, hf, Finsupp.support_smul hx']

omit [∀ i, TopologicalSpace (X i)] in
lemma map_convexCombPair [DecidableEq ι] {ι' : Type*} [DecidableEq ι'] {X' : ι' → Type*}
    {f : ι → ι'} [∀ i, Decidable (∃ i', f i' = i)] (hf : f.Injective) {f' : ∀ i, X i → X' (f i)}
    {x x' : IJoin X} {t : unitInterval}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} :
    map hf f' (convexCombPair x x' t h) = convexCombPair (map hf f' x) (map hf f' x') t (by
      intro i hi
      simp only [map_weights, Finset.mem_inter, Finsupp.mapDomain_support_of_injective hf,
        Finset.mem_image] at hi
      obtain ⟨⟨i, hi, rfl⟩, i', hi', hi''⟩ := hi
      obtain rfl := hf hi''
      simp only [map_points_apply]
      exact congrArg _ <| h _ <| Finset.mem_inter.2 ⟨hi, hi'⟩) := by
  simp [convexCombPair, map_sConvexComb]

end ConvexComb

section SMul

instance _root_.Option.smul {G X : Type*} [SMul G X] : SMul G (Option X) where
  smul g x := Option.map (g • ·) x

@[simp]
lemma _root_.Option.smul_none {G X : Type*} [SMul G X] {g : G} :
    g • (none : Option X) = none := rfl

@[simp]
lemma _root_.Option.smul_some {G X : Type*} [SMul G X] {g : G} {x : X} :
    g • some x = some (g • x) := rfl

lemma _root_.Option.smul_eq_map {G X : Type*} [SMul G X] {g : G} {x : Option X} :
    g • x = Option.map (g • ·) x := rfl

@[simp]
lemma _root_.Option.smul_eq_none {G X : Type*} [SMul G X] {g : G} {x : Option X} :
    g • x = none ↔ x = none := by
  cases x <;> simp

@[simp]
lemma _root_.Option.smul_getD {G X : Type*} [SMul G X] {g : G} {x : Option X} {x' : X}
    (hx : x.isSome) : (g • x).getD x' = g • x.getD x' := by
  cases x <;> simp at hx ⊢

instance _root_.Option.mulAction {G X : Type*} [Monoid G] [MulAction G X] :
    MulAction G (Option X) where
  mul_smul g g' x := by cases x <;> simp [mul_smul]
  one_smul x := by cases x <;> simp

/-- TODO: generalise `smul_left_cancel_iff` to this -/
@[simp]
lemma _root_.IsLeftCancelSMul.left_cancel_iff {G X : Type*} [SMul G X] [IsLeftCancelSMul G X]
    {g : G} {x x' : X} : g • x = g • x' ↔ x = x' :=
  ⟨fun h ↦ IsLeftCancelSMul.left_cancel _ _ _ h, fun h ↦ by rw [h]⟩

/-- TODO: generalise `smul_right_cancel_iff` to this -/
@[simp]
lemma _root_.IsCancelSMul.right_cancel_iff {G X : Type*} [SMul G X] [IsCancelSMul G X]
    {g g' : G} {x : X} : g • x = g' • x ↔ g = g' :=
  ⟨fun h ↦ IsCancelSMul.right_cancel _ _ _ h, fun h ↦ by rw [h]⟩

@[simp]
instance _root_.Option.isLeftCancelSMul {G X : Type*} [SMul G X] [IsLeftCancelSMul G X] :
    IsLeftCancelSMul G (Option X) where
  left_cancel' g x x' h := by
    cases x <;> cases x'
    · simp
    · simp at h
    · simp at h
    · simpa using h

instance {G : Type*} [∀ i, SMul G (X i)] : SMul G (IJoin X) where
  smul g x := ⟨x.toStdSimplex, fun i ↦ g • x.points i, by
    simp [x.points_eq_none_iff]⟩

omit [∀ i, TopologicalSpace (X i)] in
@[simp]
lemma smul_weights {G : Type*} [∀ i, SMul G (X i)] {g : G} {x : IJoin X} :
    (g • x).weights = x.weights := rfl

omit [∀ i, TopologicalSpace (X i)] in
@[simp]
lemma smul_points_apply {G : Type*} [∀ i, SMul G (X i)] {g : G} {x : IJoin X} {i : ι} :
    (g • x).points i = (g • x.points i) := rfl

omit [∀ i, TopologicalSpace (X i)] in
lemma smul_eq_map [∀ i : ι, Decidable (∃ i', id i' = i)] {G : Type*} [∀ i, SMul G (X i)]
    {g : G} {x : IJoin X} :
    g • x = map Function.injective_id (fun _ x ↦ g • x) x := by
  refine ext (by simp) fun i _ ↦ (map_points_apply Function.injective_id (fun i x ↦ g • x)).symm

omit [∀ i, TopologicalSpace (X i)] in
lemma smul_sConvexComb [DecidableEq ι] {G : Type*} [∀ i, SMul G (X i)]
    [∀ i, IsCancelSMul G (X i)] {f : StdSimplex ℝ (IJoin X)}
    {hf : ∀ x ∈ f.weights.support, ∀ x' ∈ f.weights.support,
      ∀ i ∈ (x.weights.support ∩ x'.weights.support), x.points i = x'.points i} {g : G} :
    g • sConvexComb f hf = sConvexComb (f.map (fun x ↦ g • x)) fun x hx x' hx' i hi ↦ by
      classical
      obtain ⟨x, hx'', rfl⟩ := Finset.mem_image.1 <| Finsupp.mapDomain_support hx
      obtain ⟨x', hx''', rfl⟩ := Finset.mem_image.1 <| Finsupp.mapDomain_support hx'
      simp only [smul_eq_map, map_weights, Finset.mem_inter,
        Finsupp.mapDomain_id] at hi
      simp [hf _ hx'' _ hx''' _ <| Finset.mem_inter.2 ⟨hi.1, hi.2⟩] := by
  classical
  simp only [smul_eq_map, map_sConvexComb]

omit [∀ i, TopologicalSpace (X i)] in
@[simp]
lemma smul_convexCombPair [DecidableEq ι] {G : Type*} [∀ i, SMul G (X i)]
    [∀ i, IsCancelSMul G (X i)] {x x' : IJoin X} {t : unitInterval}
    {h : ∀ i ∈ x.weights.support ∩ x'.weights.support, x.points i = x'.points i} {g : G} :
    g • convexCombPair x x' t h = convexCombPair (g • x) (g • x') t (by simpa using h) := by
  classical
  simp only [smul_eq_map, map_convexCombPair]

instance {G : Type*} [Monoid G] [∀ i, MulAction G (X i)] : MulAction G (IJoin X) where
  mul_smul _ _ _ := by ext <;> simp [mul_smul]
  one_smul _ := by ext <;> simp

instance [Nonempty ι] {G : Type*} [∀ i, SMul G (X i)] [∀ i, FaithfulSMul G (X i)] :
    FaithfulSMul G (IJoin X) := by
  classical
  refine .of_injective (f := MulActionHom.mk (of (Classical.arbitrary _)) ?_) of_injective
  intro g x
  simp [smul_eq_map]

instance [Nonempty ι] {G : Type*} [∀ i, SMul G (X i)] [∀ i, IsLeftCancelSMul G (X i)] :
    IsLeftCancelSMul G (IJoin X) where
  left_cancel' _ _ _ h := by
    refine ext (congrArg (fun x ↦ x.weights) h) fun i _ ↦ ?_
    simpa using (congrArg (fun x ↦ x.points i) h)

lemma _root_.Convexity.StdSimplex.exists_pos {R : Type*} [PartialOrder R] [Semiring R]
    [Nontrivial R] {M : Type*} (x : Convexity.StdSimplex R M) :
    ∃ i, 0 < x.weights i := by
  have ⟨i, hi⟩ := x.support_weights_nonempty
  exact ⟨i, (x.weights_nonneg i).lt_of_ne' <| by simpa using hi⟩

instance [Nonempty ι] {G : Type*} [∀ i, SMul G (X i)] [∀ i, IsCancelSMul G (X i)] :
    IsCancelSMul G (IJoin X) where
  right_cancel' g g' x h := by
    have ⟨i, hi⟩ := x.exists_pos
    have ⟨x', hx'⟩ := Option.ne_none_iff_exists.1 <| x.points_eq_none_iff.not.2 hi.ne'
    simpa [← hx'] using congrArg (fun x ↦ x.points i) h

attribute [local fun_prop] Option.continuous_some_excludedPointTopology' in
instance _root_.Option.continuousSMul_excludedPointTopology'
    {G X : Type*} [TopologicalSpace G] [TopologicalSpace X] [SMul G X] [ContinuousSMul G X] :
    ContinuousSMul G (Option X) where
  continuous_smul := by
    refine Option.continuous_excludedPointTopology'_iff.2 ⟨?_, ?_⟩
    · rw [show (fun p ↦ p.1 • p.2) ⁻¹' {none}ᶜ = Set.univ ×ˢ {none}ᶜ by ext x; simp]
      exact isOpen_univ.prod <| Option.isOpen_excludedPointTopology'_iff.2 <| by simp
    · rw [show (fun p ↦ p.1 • p.2) ⁻¹' {none}ᶜ = Prod.map id some '' Set.univ by
        ext x; simp [Option.ne_none_iff_exists]]
      rw [IsOpenEmbedding.id.prodMap (Option.isOpenEmbedding_some_excludedPointTopology')
        |>.continuousOn_image_iff, continuousOn_univ]
      simp only [Function.comp_def, Prod.map_fst, id_eq, Prod.map_snd, Option.smul_some]
      fun_prop

instance {G : Type*} [TopologicalSpace G] [∀ i, SMul G (X i)] [∀ i, ContinuousSMul G (X i)] :
    ContinuousSMul G (IJoin X) where
  continuous_smul := by
    refine continuous_iff.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simp only [smul_weights]
      exact continuous_weights.comp continuous_snd
    · exact continuous_smul.comp <| continuous_id.prodMap continuous_points

/-- TODO: move -/
lemma _root_.Topology.IsInducing.continuousOn_range_iff {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y} (hf : IsInducing f) {g : Y → Z} :
    ContinuousOn g (Set.range f) ↔ Continuous (g ∘ f) := by
  simpa using hf.continuousOn_image_iff (g := g) (s := Set.univ)

/-- TODO: move -/
lemma _root_.Option.isContinuousOn_getD_excludedPointTopology' {X : Type*} [TopologicalSpace X]
    {x : X} : ContinuousOn (Option.getD · x) (Set.range Option.some) := by
  simp [Option.isOpenEmbedding_some_excludedPointTopology'.continuousOn_range_iff, continuous_id]

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type*} :
    LocallyTrivialSMul G (IJoin (fun _ : ι ↦ G)) where
  exists_equivariant_trivialization b := by
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective b
    have ⟨i, hi⟩ := x.exists_pos
    have h :
        IsOpen {x : Quotient (MulAction.orbitRel G (IJoin fun i ↦ G)) | 0 < x.out.weights i} := by
      refine isOpen_lt continuous_const <| isQuotientMap_quotient_mk'.continuous_iff.2 <|
        (continuous_weights (i := i)).congr fun x ↦ ?_
      have ⟨g, (hg : g • x = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x
      simp [Quotient.mk', ← hg]
    refine ⟨{
      toFun x := (⟦x⟧, (x.points i).getD 1)
      invFun x := (x.2 / (x.1.out.points i).getD 1) • x.1.out
      source := {x | 0 < x.weights i}
      target := {x | 0 < x.out.weights i} ×ˢ Set.univ
      map_source' x := by
        have ⟨g, (hg : g • x = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x
        simp [← hg]
      map_target' x := by simp
      left_inv' x hx := by
        have ⟨g, (hg : g • x = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x
        simp [← hg, x.points_isSome_iff.2 hx]
      right_inv' x hx := Prod.ext (by simp) <| by
        simp [x.1.out.points_isSome_iff.2 hx.1]
      open_source := isOpen_lt continuous_const continuous_weights
      open_target := h.prod isOpen_univ
      continuousOn_toFun := .prodMk (by fun_prop) <|
        Option.isContinuousOn_getD_excludedPointTopology'.comp (by fun_prop) fun x hx ↦
          Option.ne_none_iff_exists.1 <| x.points_eq_none_iff.not.2 (Set.mem_setOf.1 hx).ne'
      continuousOn_invFun := by
        rw [MulAction.isOpenQuotientMap_quotientMk.prodMap .id
          |>.isQuotientMap.continuousOn_isOpen_iff (h.prod isOpen_univ)]
        refine continuousOn_iff.2 ⟨fun i' ↦ ?_, fun i' ↦ ?_⟩
        · refine (continuous_weights (i := i').comp continuous_fst).continuousOn.congr fun x hx ↦ ?_
          have ⟨g, (hg : g • x.1 = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x.1
          simp [← hg]
        · refine .congr (f := fun y ↦ (y.2 / (y.1.points i).getD 1) • y.1.points i') ?_
            fun x hx ↦ ?_
          · refine .smul (.div' (by fun_prop) ?_) (by fun_prop)
            refine Option.isContinuousOn_getD_excludedPointTopology'.comp (by fun_prop)
              fun x hx ↦ ?_
            have ⟨g, (hg : g • x.1 = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x.1
            exact Option.ne_none_iff_exists.1 <| x.1.points_eq_none_iff.not.2
              (show 0 < x.1.weights i by simpa [← hg] using hx).ne'
          · have ⟨g, (hg : g • x.1 = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x.1
            simp [← hg, show (x.1.points i).isSome by simpa [← hg] using hx,
              div_eq_mul_inv, mul_smul]
      baseSet := {x | 0 < x.out.weights i}
      open_baseSet := h
      source_eq := by
        ext x
        have ⟨g, (hg : g • x = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x
        simp [← hg]
      target_eq := by ext; simp
      proj_toFun := by simp }, ?_, ?_, fun hx ↦ ?_⟩
    · have ⟨g, (hg : g • x = _)⟩ := Quotient.mk_out (s := MulAction.orbitRel G _) x
      simp [← hg, hi]
    · simp
    · simp only [Set.mem_setOf_eq] at hx
      simp [hx]

@[simp]
lemma _root_.ContinuousMap.HomotopyWith.coe_mk {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} {P : C(X, Y) → Prop} (toHomotopy : f₀.Homotopy f₁)
    (prop' : ∀ t, P ⟨fun x ↦ toHomotopy.toFun (t, x),
      toHomotopy.continuous_toFun.comp (by fun_prop)⟩) :
    ⇑(ContinuousMap.HomotopyWith.mk toHomotopy prop') = toHomotopy := rfl

@[simp]
lemma _root_.ContinuousMap.Homotopy.coe_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ : C(X, Y)} (toContinuousMap : C(I × X, Y))
    (map_zero_left : ∀ x, toContinuousMap.toFun (0, x) = f₀ x)
    (map_one_left : ∀ x, toContinuousMap.toFun (1, x) = f₁ x) :
    ⇑(ContinuousMap.Homotopy.mk toContinuousMap map_zero_left map_one_left) = toContinuousMap := rfl

/-- Any two continuous equivariant maps from a `G`-space into a join of countably many
copies of `G` are homotopic.

TODO: generalise from `ℕ` to arbitrary index sets -/
lemma continuousMulActionHom_homotopic
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X : Type*} [SMul G X] [TopologicalSpace X] [ContinuousSMul G X]
    (f f' : C[G](X, IJoin fun _ : ℕ ↦ G)) : f.Homotopic f' := by
  /- The proof involves reindexing the values of `f` and `f'` by composing those functions with
  `map hf (fun _ ↦ id) : (IJoin fun _ ↦ G) → (IJoin fun _ ↦ G)` for injective functions `f : ℕ → ℕ`;
  to make working with these maps easier we define `map' hf` to be those maps upgraded to
  equivariant continuous maps, and then prove that linear interpolation gives an equivariant
  homotopy from `map' hf` to `map' hf'` when `f` and `f'` agree on `f ⁻¹' range f'`. This is in
  particular the case when `range f` and `range f'` are disjoint. -/
  classical
  let map' {f : ℕ → ℕ} (hf : f.Injective) : C[G](IJoin fun _ : ℕ ↦ G, IJoin fun _ : ℕ ↦ G) :=
    ⟨⟨map hf (fun _ ↦ id), (by fun_prop)⟩, fun g x ↦ by
      refine ext (by simp) fun i hi ↦ ?_
      obtain ⟨i, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hi.ne'
      simp⟩
  have hmap' {f f' : ℕ → ℕ} (hf : f.Injective) (hf' : f'.Injective)
      (h : (f ⁻¹' Set.range f').EqOn f f') :
        ∃ F : (map' hf).Homotopy (map' hf'), ∀ i ∈ Set.range f ∩ Set.range f', ∀ x t,
          (F (t, x)).weights i = (map' hf x).weights i ∧
            (F (t, x)).points i = (map' hf x).points i := by
    refine ⟨{
      toFun x := convexCombPair (map' hf x.2) (map' hf' x.2) x.1 <| fun i hi ↦ by
        simp only [ContinuousMulActionHom.coe_mk, ContinuousMap.coe_mk, map_weights,
          Finset.mem_inter, Finsupp.mem_support_iff, map'] at hi
        replace hi : ∃ i', f i' = i ∧ i' ∈ f ⁻¹' Set.range f' := by
          grind [Finsupp.mem_range_of_mapDomain_ne_zero hi.1,
            Finsupp.mem_range_of_mapDomain_ne_zero hi.2]
        obtain ⟨i, rfl, hi⟩ := hi
        simp only [map', ContinuousMulActionHom.coe_mk, ContinuousMap.coe_mk, map_points_apply]
        simp [h hi]
      map_zero_left := by simp
      map_one_left := by simp
      prop' t g x := by simp
    }, fun i hi x t ↦ ⟨?_, ?_⟩⟩
    · suffices h : ((map' hf) x).weights i = ((map' hf') x).weights i by simp [h, sub_mul, -id_eq]
      obtain ⟨⟨i, rfl⟩, hi⟩ := hi
      simp [map', hf, @h i hi ▸ Finsupp.mapDomain_apply hf' x.weights i]
    · simp only [ContinuousMap.HomotopyWith.coe_mk, ContinuousMap.Homotopy.coe_mk,
        ContinuousMap.coe_mk]
      refine convexCombPair_points_apply_left' ?_
      obtain ⟨⟨i, rfl⟩, hi⟩ := hi
      simp only [map', ContinuousMulActionHom.coe_mk, ContinuousMap.coe_mk, map_points_apply]
      simp [h hi]
  /- Let `even` be the (continuous, equivariant) map `(IJoin fun _ ↦ G) → (IJoin fun _ ↦ G)`
  induced by the map `fun n ↦ 2 * n`. By applying `hmap'` to `even` and the similarly defined `odd`,
  it suffices to prove that every `f : C[G](X, IJoin fun _ ↦ G)` is equivariantly homotopic
  to `even.comp f`. -/
  let even := (map' (show (fun n ↦ 2 * n).Injective from fun _ _ ↦ by grind))
  revert f f'
  suffices h : ∀ f : C[G](X, IJoin fun _ : ℕ ↦ G), f.Homotopic (even.comp f) by
    let odd := (map' (show Function.Injective (fun n ↦ 2 * n + 1) from fun _ _ ↦ by grind))
    suffices h' : ∀ f f' : C[G](X, IJoin fun _ : ℕ ↦ G), (even.comp f).Homotopic (odd.comp f') from
      fun f f' ↦ (h f).trans <| (h' f f).trans (h' f' f).symm |>.trans (h f').symm
    exact fun f f' ↦ ⟨{
      toFun x := convexCombPair (even (f x.2)) (odd (f' x.2)) x.1 <| fun i hi ↦ by
        simp only [even, odd, map', Finset.mem_inter, ContinuousMulActionHom.coe_mk,
          ContinuousMap.coe_mk, map_weights, Finsupp.mem_support_iff] at hi
        grind [Finsupp.mem_range_of_mapDomain_ne_zero hi.1,
          Finsupp.mem_range_of_mapDomain_ne_zero hi.2]
      map_zero_left := by simp
      map_one_left := by simp
      prop' := by simp }⟩
  /- Even simpler, it suffices to prove that `even` is equivariantly homotopic to the identity.-/
  suffices h : even.Homotopic (.id _ _) from fun f ↦ h.symm.comp (.refl f)
  /- We can pick a sequence of injective functions `f n : ℕ → ℕ` such that `f 0` is `fun n ↦ 2 * n`,
  `f n` and `f (n + 1)` agree on `f n ⁻¹' Set.range (f (n + 1))`, and `f` converges to the identity
  in the sense that `∀ n, ∀ m ≤ n, f n m = m`. Applying `hmap'` to these functions then gives a
  sequence of equivariant homotopies which we can concatenate into a single equivariant homotopy
  from `even` to the identity. -/
  have ⟨f, hf, hf', hf''⟩ : ∃ f : ℕ → ℕ → ℕ, (∀ n, (f n).Injective) ∧ f 0 = (fun n ↦ 2 * n) ∧ ∀ n,
      (f n ⁻¹' Set.range (f (n + 1))).EqOn (f n) (f (n + 1)) ∧ ∀ m ≤ n, f n m = m := by
    refine ⟨fun n m ↦ if m ≤ n then m else 2 * m, fun _ _ ↦ ?_, ?_, fun _ ↦ ⟨fun _ ↦ ?_, ?_⟩⟩
      <;> grind
  choose F hF using fun n ↦ hmap' (hf n) (hf (n + 1)) (hf'' n).1
  unfold even; rw! [← hf']
  refine ⟨.countableTrans F _ fun x ↦ ?_⟩
  rw [ContinuousMulActionHom.id_apply]
  refine tendsto_nhds_iff.2 fun i ↦ ⟨?_, ?_⟩
  · refine .congr' (f₁ := fun x ↦ x.2.2.weights i) ?_ ?_
    · refine Set.EqOn.eventuallyEq_of_mem ?_ <|
        Filter.prod_mem_prod (Filter.Ici_mem_atTop i) Filter.univ_mem
      rintro ⟨i', t, x⟩ ⟨hi', ⟨⟩⟩
      rw [Set.mem_Ici] at hi'
      simp [Function.comp_apply, (hF i' i ⟨⟨i, by grind⟩, ⟨i, by grind⟩⟩ x t).1, map',
        (hf'' i').2 i hi' ▸ Finsupp.mapDomain_apply (hf i') x.weights i]
    · exact .comp (g := (fun x : (IJoin _) ↦ x.weights i) ∘ Prod.snd)
        (.comp continuous_weights.continuousAt Filter.tendsto_snd) Filter.tendsto_snd
  · refine .congr' (f₁ := fun x ↦ x.2.2.points i) ?_ ?_
    · refine Set.EqOn.eventuallyEq_of_mem ?_ <|
        Filter.prod_mem_prod (Filter.Ici_mem_atTop i) Filter.univ_mem
      rintro ⟨i', t, x⟩ ⟨hi', ⟨⟩⟩
      rw [Set.mem_Ici] at hi'
      simp [Function.comp_apply, (hF i' i ⟨⟨i, by grind⟩, ⟨i, by grind⟩⟩ x t).2, map',
        (hf'' i').2 i hi' ▸ map_points_apply (X := fun _ ↦ G) (X' := fun _ ↦ G) (hf i')
        (fun _ ↦ id) (x := x) (i := i)]
    · exact .comp (g := (fun x : (IJoin _) ↦ x.points i) ∘ Prod.snd)
        (.comp continuous_points.continuousAt Filter.tendsto_snd) Filter.tendsto_snd

/-- TODO: move -/
lemma _root_.ContinuousMap.Homotopic.of_comp_homeomorph {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f f' : C(Y, Z)} {e : X ≃ₜ Y}
    (h : (f.comp e : C(X, Z)).Homotopic (f'.comp e)) : f.Homotopic f' := by
  rw [← f.comp_id, ← f'.comp_id, ← Homeomorph.coe_refl, ← e.symm_trans_self, Homeomorph.coe_trans]
  exact h.comp (.refl _)

/-- TODO: move -/
@[simp]
lemma _root_.ContinuousMap.Homotopic.comp_homeomorph_iff {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f f' : C(Y, Z)} (e : X ≃ₜ Y) :
    (f.comp e : C(X, Z)).Homotopic (f'.comp e) ↔ f.Homotopic f' :=
  ⟨fun h ↦ h.of_comp_homeomorph, fun h ↦ h.comp (.refl _)⟩

/-- TODO: generalise this to arbitrary infinite joins of any nonempty space `X`. -/
instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ContractibleSpace (IJoin fun _ : ℕ ↦ G) := by
  refine (contractible_iff_id_nullhomotopic _).2 ⟨Classical.arbitrary _, ?_⟩
  refine .of_comp_homeomorph (e := WithTrivialSMul.homeomorph G _) ?_
  rw [← ContinuousMulActionHom.Homotopic.relIsoContinuousMap (φ := .id G).symm.map_rel_iff]
  exact continuousMulActionHom_homotopic _ _

end SMul

end IJoin

end Topology
