/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.Join
import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-! # Joins of topological spaces
In this file we define joins of families of topological spaces.

## TODO
* Figure out which topology we actually want on infinite joins, the one induced by the projections
  or the one coinduced by all finite joins
* Prove associativity
* Connect to iterated binary joins, use this to prove associativity of binary joins
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

/-- The canonical inclusion `X i → IJoin X`. -/
@[simps! points weights]
noncomputable def of [DecidableEq ι] (i : ι) (x : X i) : IJoin X where
  points := Function.update (fun _ ↦ none) i x
  toStdSimplex := .single i
  points_eq_none_iff := by grind [StdSimplex.weights_single]

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
@[simps! weights]
noncomputable def map {ι' : Type*} {X' : ι' → Type*} {f : ι → ι'} [∀ i, Decidable (∃ i', f i' = i)]
    (hf : f.Injective) (g : ∀ i, X i → X' (f i)) (x : IJoin X) : IJoin X' where
  points i := if h : ∃ i', f i' = i then
    Option.map (cast (congrArg X' h.choose_spec) ∘ g h.choose) (x.points h.choose) else none
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
    simp [show cast (rfl : X' (f i) = _) = id by ext; simp]
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
  · simp [ofJoin, Finsupp.mapDomain_add, Finsupp.mapDomain_sub]
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

lemma continuous_weights {i : ι} : Continuous fun x : IJoin X ↦ x.weights i :=
  (continuous_iff.1 continuous_id).1 i

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

end IJoin

end Topology
