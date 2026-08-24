/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.Equiv
import ClassifyingBundles.Join
import ClassifyingBundles.LocallyTrivialSMul
import Mathlib.Geometry.Convex.ConvexSpace.Defs

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

## TODO
* Prove that `IJoin.of` and `IJoin.ofJoin` are closed embeddings
* Connect to iterated binary joins, use this to prove associativity of binary joins
* prove that joins of Hausdorff spaces are Hausdorff
* define Fσ sets, prove that Fσ sets in paracompact spaces are paracompact, use that to prove that
  infinite joins of compact Hausdorff spaces are paracompact
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
@[simps! weights]
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

lemma map_injective {ι' : Type*} {X' : ι' → Type*} {f : ι → ι'} [∀ i, Decidable (∃ i', f i' = i)]
    (hf : f.Injective) {g : ∀ i, X i → X' (f i)} (hg : ∀ i, (g i).Injective) :
    (map hf g).Injective := by
  intro x x' h
  refine ext ?_ fun i hi ↦ ?_
  · exact Finsupp.mapDomain_injective hf <| congrArg (fun x : IJoin X' ↦ x.weights) h
  · have h' := congrArg (fun x ↦ x.points (f i)) h
    simp only [map_points_apply] at h'
    exact Option.map_injective (hg i) h'

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

end SMul

end IJoin

end Topology
