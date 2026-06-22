/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.InducingSMul
import Mathlib.Topology.UnitInterval

/-! # Joins of topological spaces
In this file we define joins of topological spaces.

Since joins of e.g. simplicial complexes also exist but have a different underlying type, future
constructions of those joins will have to involve a new type instead of just equipping the type
we define here with the structure of a simplicial complex; because of that, we put everything here
in the `Topology` namespace to avoid confusion.

## Main definitions & results
* `Join X Y`: the join of `X` and `Y`, denoted `X ⋆ Y`. We equip this with the strong topology,
  i.e. the one induced by the projections `Join.fst`, `Join.snd` and `Join.t`.
* `Set.join s t`: the join of two sets as a set in the join of the ambient spaces. This is closed /
  compact when both sets are closed / compact, but not necessarily open when both sets are open.
* `Join.fst`: the projection `X ⋆ Y → Option X`.
* `Join.snd`: the projection `X ⋆ Y → Option Y`.
* `Join.t`: the projection `X ⋆ Y → I`.
* `Join.inl`: the inclusion `X → X ⋆ Y`. This map is always a closed embedding.
* `Join.inr`: the inclusion `Y → X ⋆ Y`. This map is always a closed embedding.
* `Join.π`: the projection `X × I × Y → X ⋆ Y`. This is a quotient map when `X` and `Y` are nonempty
  compact Hausdorff, proving that in those cases the strong and
* `Join.map`: the map `X ⋆ Y → X' ⋆ Y'` induced by two maps `X → X'` and `Y → Y'`. This map is
  continuous / inducing / an embedding whenever the two maps are.
* `Join.swap`: the map `X ⋆ Y → Y ⋆ X` swapping the two factors.
* `Homeomorph.joinCongr`: the homeomorphism `X ⋆ Y ≃ₜ X' ⋆ Y'` induced by
  two homeomorphisms `X ≃ₜ X'` and `Y ≃ₜ Y'`.
* `Homeomorph.joinIsEmpty`: the homeomorphism `X ⋆ Y ≃ₜ X` when `Y` is empty.
* `Homeomorph.isEmptyJoin`: the homeomorphism `X ⋆ Y ≃ₜ Y` when `X` is empty.
* `Homeomorph.joinComm`: the homeomorphism `X ⋆ Y ≃ₜ Y ⋆ X` swapping the two factors.
* The join of compact spaces is compact.
* The join of Hausdorff spaces is Hausdorff.

## TODO:
* prove associativity up to homeomorphism
* can `Join.isQuotientMap_π` be generalised to e.g. the locally compact case?
-/

namespace Topology

open scoped unitInterval

/-- The join of two topological spaces `X` and `Y`, denoted `X ⋆ Y` in the `Topology` scope.
For nonempty spaces the join can be thought of as a quotient of `X × I × Y` where `I` is the unit
interval, but for general spaces this is not quite right: the join should be the colimit of the
diagram `X ← X × Y → X × I × Y ← X × Y → Y` (where the first and last map are projections, the
second map is the inclusion at `0` and the third map is the inclusion at `1`), so when `X` is empty
`X ⋆ Y` should be homeomorphic to `Y` and vice versa. To solve this we instead construct the join as
a subtype of `Option X × I × Option Y`, where we require the first component to be `Option.none` iff
the middle component is `1` and the third component to be `Option.none` iff the middle component is
`0`.

We equip this with the "strong topology" as defined by Milnor, i.e. the coarsest topology making the
projections to `I`, `X` and `Y` continuous where they are defined.
-/
@[ext]
structure Join (X Y : Type*) where
  /-- Projection to the first factor, or `none` when `t = 1`. -/
  fst : Option X
  /-- Projection to the second factor, or `none` when `t = 0`. -/
  snd : Option Y
  /-- The parameter along the join. The slice of the join at `t = 0` is homeomorphic to `X`,
  the slice at `t = 1` to `Y`, and the slice at any other `t` to `X × Y`. -/
  t : I
  fst_eq_none_iff : fst = none ↔ t = 1
  snd_eq_none_iff : snd = none ↔ t = 0

attribute [simp] Join.fst_eq_none_iff Join.snd_eq_none_iff

namespace Join

@[inherit_doc] scoped[Topology] infixr:30 " ⋆ " => Join

variable {X X' Y Y' Z : Type*}

/-- The left inclusion `X → X ⋆ Y`. -/
@[simps]
def inl (x : X) : X ⋆ Y := ⟨some x, none, 0, by simp, by simp⟩

/-- The right inclusion `Y → X ⋆ Y`. -/
@[simps]
def inr (y : Y) : X ⋆ Y := ⟨none, some y, 1, by simp, by simp⟩

lemma inl_injective : (inl : X → X ⋆ Y).Injective :=
  fun _ _ h ↦ Option.some_injective _ <| congrArg fst h

lemma inr_injective : (inr : Y → X ⋆ Y).Injective :=
  fun _ _ h ↦ Option.some_injective _ <| congrArg snd h

lemma range_inl : Set.range (inl : X → X ⋆ Y) = t ⁻¹' {0} := by
  ext p
  refine ⟨fun ⟨x, hx⟩ ↦ by simp [← hx], fun h ↦ ?_⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at h
  have ⟨x, hx⟩ : ∃ x, p.fst = some x := by simpa [h] using p.fst.eq_none_or_eq_some
  use x; ext1 <;> simp [hx, h, p.snd_eq_none_iff.2 h]

lemma range_inr : Set.range (inr : Y → X ⋆ Y) = t ⁻¹' {1} := by
  ext p
  refine ⟨fun ⟨y, hy⟩ ↦ by simp [← hy], fun h ↦ ?_⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at h
  have ⟨y, hy⟩ : ∃ y, p.snd = some y := by simpa [h] using p.snd.eq_none_or_eq_some
  use y; ext1 <;> simp [hy, h, p.fst_eq_none_iff.2 h]

/-- The projection `X × I × Y → X ⋆ Y`. -/
@[simps]
noncomputable def π (p : X × I × Y) : X ⋆ Y :=
  ⟨if p.2.1 = 1 then none else p.1, if p.2.1 = 0 then none else p.2.2, p.2.1, by simp, by simp⟩

/-- When `X` and `Y` are both nonempty, the projection -/
lemma π_surjective [Nonempty X] [Nonempty Y] : (π : X × I × Y → X ⋆ Y).Surjective := by
  intro p
  by_cases h : p.t = 0
  · have ⟨x, hx⟩ : ∃ x, p.fst = some x := by simpa [h] using p.fst.eq_none_or_eq_some
    exact ⟨⟨x, 0, ‹Nonempty Y›.some⟩, by ext <;> simp_all [p.snd_eq_none_iff.2 h]⟩
  · have ⟨y, hy⟩ : ∃ x', p.snd = some x' := by simpa [h] using p.snd.eq_none_or_eq_some
    by_cases h' : p.t = 1
    · exact ⟨⟨‹Nonempty X›.some, 1, y⟩, by ext <;> simp_all [p.fst_eq_none_iff.2 h']⟩
    · have ⟨x, hx⟩ : ∃ x, p.fst = some x := by simpa [h'] using p.fst.eq_none_or_eq_some
      exact ⟨⟨x, p.t, y⟩, by ext <;> simp_all⟩

/-- The map `X ⋆ Y → X' ⋆ Y'` induced by two maps `X → X'` and `Y → Y'`. -/
@[simps]
def map (f : X → X') (g : Y → Y') (p : X ⋆ Y) : X' ⋆ Y' :=
  ⟨p.fst.map f, p.snd.map g, p.t, by simp, by simp⟩

/-- For any two injective maps `X → X'` and `Y → Y'`, the induced map `X ⋆ Y → X' ⋆ Y'` is
injective. -/
lemma _root_.Function.Injective.joinMap {f : X → X'} {g : Y → Y'} (hf : f.Injective)
    (hg : g.Injective) : (map f g).Injective := by
  intro x x' h; ext1
  · exact Option.map_injective hf (congrArg fst h)
  · exact Option.map_injective hg (congrArg snd h)
  · exact (congr_arg t h:)

@[simp]
lemma map_inl {f : X → X'} {g : Y → Y'} {x : X} : map f g (inl x) = inl (f x) :=
  rfl

@[simp]
lemma map_inr {f : X → X'} {g : Y → Y'} {y : Y} : map f g (inr y) = inr (g y) :=
  rfl

/-- The map `X ⋆ Y → Y ⋆ X` swapping the two factors. -/
@[simps]
def swap (p : X ⋆ Y) : Y ⋆ X := ⟨p.snd, p.fst, unitInterval.symm p.t, by simp, by simp⟩

@[simp]
lemma swap_swap (p : X ⋆ Y) : swap (swap p) = p := by
  ext <;> simp

/-- The join of two sets, as a set in the join of the ambient spaces. -/
def _root_.Set.join (s : Set X) (t : Set Y) : Set (X ⋆ Y) :=
  fst ⁻¹' (some '' s ∪ {none}) ∩ snd ⁻¹' (some '' t ∪ {none})

lemma _root_.Set.mem_join_iff {s : Set X} {t : Set Y} {p : X ⋆ Y} :
    p ∈ s.join t ↔ p.fst ∈ some '' s ∪ {none} ∧ p.snd ∈ some '' t ∪ {none} := Iff.rfl

lemma _root_.Set.mem_join_iff' {s : Set X} {t : Set Y} {p : X ⋆ Y} :
    p ∈ s.join t ↔ (p.t ≠ 1 → ∃ x ∈ s, some x = p.fst) ∧ (p.t ≠ 0 → ∃ y ∈ t, some y = p.snd) := by
  simp [Set.mem_join_iff, ← or_iff_not_imp_left]

@[simp]
lemma _root_.Set.join_univ : (Set.univ.join .univ : Set (X ⋆ Y)) = .univ := by
  ext; simp [Set.mem_join_iff]

@[simp]
lemma _root_.Set.image_join {f : X → X'} {g : Y → Y'} {s : Set X} {t : Set Y} :
    map f g '' s.join t = (f '' s).join (g '' t) := by
  ext p
  refine ⟨fun ⟨p', hs, h⟩ ↦ h ▸ ?_, fun h ↦ ?_⟩
  · refine Set.mem_join_iff'.2 ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;> rw [map_t] at h'
    · have ⟨x, hx⟩ : ∃ x, p'.fst = some x := by simpa [h'] using p'.fst.eq_none_or_eq_some
      exact ⟨f x, Set.mem_image_of_mem _ <| by simpa [hx] using hs.1, by simp [hx]⟩
    · have ⟨y, hy⟩ : ∃ y, p'.snd = some y := by simpa [h'] using p'.snd.eq_none_or_eq_some
      exact ⟨g y, Set.mem_image_of_mem _ <| by simpa [hy] using hs.2, by simp [hy]⟩
  · rw [Set.mem_join_iff'] at h
    by_cases h' : p.t = 1
    · have ⟨y, ⟨y', hy'⟩, hy⟩ := h.2 (by simp [h'])
      refine ⟨⟨none, y', p.t, by simp [h'], by simp [h']⟩, ?_, ?_⟩
      · simp [Set.mem_join_iff, hy']
      · ext <;> simp [*, p.fst_eq_none_iff.2 h']
    · have ⟨x, ⟨x', hx'⟩, hx⟩ := (h.1 h')
      by_cases h'' : p.t = 0
      · refine ⟨⟨x', none, p.t, by simp [h'], by simp [h'']⟩, ?_, ?_⟩
        · simp [Set.mem_join_iff, hx']
        · ext <;> simp [*, p.snd_eq_none_iff.2 h'']
      · have ⟨y, ⟨y', hy'⟩, hy⟩ := h.2 (by simp [h''])
        refine ⟨⟨x', y', p.t, by simp [h'], by simp [h'']⟩, ?_, ?_⟩
        · simp [Set.mem_join_iff, hx', hy']
        · ext <;> simp [*]

@[simp]
lemma range_map {f : X → X'} {g : Y → Y'} :
    Set.range (map f g) = (Set.range f).join (Set.range g) := by
  simp [← Set.image_univ, ← Set.image_join]

variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z]

/-- Given a type `X`, this is the topology on `Option X` consisting of all sets that do not contain
`Option.none`, and of course `Set.univ`. -/
@[implicit_reducible] def _root_.Option.excludedPointTopology : TopologicalSpace (Option X) where
  IsOpen u := none ∈ u → u = .univ
  isOpen_univ := by simp
  isOpen_inter := by grind
  isOpen_sUnion := by grind

lemma _root_.Option.continuous_map_excludedPointTopology {X Y : Type*} {f : X → Y} :
    Continuous[Option.excludedPointTopology, Option.excludedPointTopology] (Option.map f) := by
  refine @Continuous.mk _ _ (_) (_) _ fun u (hu : _ → _) h ↦ ?_
  grind

/-- Given a topological space `X`, this is the topology on `Option X` consisting of all sets that
are open in `X` as well as `Set.univ`. Lacking a better name, we call this
`excludedPointTopology'` because it is similar to `excludedPointTopology` in that `Option.none` is
excluded from every open set except `Set.univ`.

Given some other space `Y` and a map `f : Y → Option X` for which `f ⁻¹' (Set.range Option.some)` is
open, `f` is continuous with respect to this topology iff it is continuous as a map
`f ⁻¹' (Set.range Option.some) → X`. -/
@[implicit_reducible] def _root_.Option.excludedPointTopology' : TopologicalSpace (Option X) :=
  ‹TopologicalSpace X›.coinduced Option.some ⊔ Option.excludedPointTopology

lemma _root_.Option.continuous_some_excludedPointTopology' :
    Continuous[_, Option.excludedPointTopology'] (Option.some : X → _) :=
  continuous_sup_rng_left continuous_coinduced_rng

lemma _root_.Continuous.optionMap_excludedPointTopology' {f : X → Y} (hf : Continuous f) :
    Continuous[Option.excludedPointTopology', Option.excludedPointTopology'] (Option.map f) := by
  refine continuous_sup_dom.2 ⟨?_, ?_⟩
  · rw [continuous_coinduced_dom]
    exact (@Continuous.comp _ _ _ (_) (_) (_) _ _ Option.continuous_some_excludedPointTopology' hf:)
  · refine continuous_sup_rng_right ?_
    exact Option.continuous_map_excludedPointTopology

attribute [local instance] Option.excludedPointTopology'

lemma _root_.Option.isOpen_excludedPointTopology'_iff {s : Set (Option X)} :
    IsOpen s ↔ IsOpen (some ⁻¹' s) ∧ (none ∈ s → s = .univ) :=
  Iff.rfl

lemma _root_.Topology.IsInducing.optionMap_excludedPointTopology' {f : X → Y} (hf : IsInducing f) :
    IsInducing (Option.map f) := by
  rw [isInducing_iff]
  refine le_antisymm (hf.continuous.optionMap_excludedPointTopology'.le_induced) ?_
  intro u hu
  rw [Option.isOpen_excludedPointTopology'_iff] at hu
  by_cases h : none ∈ u
  · exact ⟨Set.univ, isOpen_univ, by simp [hu.2 h]⟩
  · have ⟨v, hv⟩ := hf.isOpen_iff.1 hu.1
    refine ⟨some '' v, ?_, ?_⟩
    · simp [Option.isOpen_excludedPointTopology'_iff, Option.some_injective, hv.1]
    · ext1 x
      simp only [Set.mem_preimage]
      obtain rfl | ⟨x, rfl⟩ := x.eq_none_or_eq_some
      · simp [h]
      · simp [(Option.some_injective _).mem_set_image, ← Set.mem_preimage, hv.2]

lemma _root_.Option.isOpenEmbedding_some_excludedPointTopology' :
    IsOpenEmbedding (Option.some : X → _) := by
  refine .of_continuous_injective_isOpenMap Option.continuous_some_excludedPointTopology'
    (Option.some_injective _) fun u hu ↦ Option.isOpen_excludedPointTopology'_iff.2 ⟨?_, ?_⟩
  · simpa [Option.some_injective]
  · simp

@[simp]
lemma _root_.Option.some_preimage_none {X : Type*} : (some ⁻¹' {none} : Set X) = ∅ :=
  (Set.preimage_singleton_eq_empty (f := Option.some) (y := none)).2 <| by simp

lemma _root_.Option.continuous_excludedPointTopology'_iff {f : Y → Option X} :
    Continuous f ↔ IsOpen (Set.preimage f {none}ᶜ) ∧ ContinuousOn f (Set.preimage f {none}ᶜ) := by
  refine ⟨fun h ↦ ⟨?_, h.continuousOn⟩, fun ⟨h, h'⟩ ↦ ?_⟩
  · refine IsOpen.preimage h ?_
    simp [-isOpen_compl_iff, Option.isOpen_excludedPointTopology'_iff]
  · refine ⟨fun u hu ↦ ?_⟩
    by_cases h'' : none ∈ u
    · simp [hu.2 h'']
    · refine h'.isOpen_preimage h (Set.image_subset_iff.1 ?_) hu
      exact (Set.image_preimage_subset _ _).trans <| by simpa

lemma _root_.Option.continuous_excludedPointTopology'_iff' {f : Y → X} {p : Y → Prop}
    [∀ y, Decidable (p y)] : Continuous (fun y ↦ if p y then none else some (f y)) ↔
      IsOpen {y | p y}ᶜ ∧ ContinuousOn f {y | p y}ᶜ := by
  rw [Option.continuous_excludedPointTopology'_iff]
  rw [show ((fun y ↦ if p y then none else some (f y)) ⁻¹' {none}ᶜ) = {y | p y}ᶜ by ext; simp]
  refine and_congr_right fun _ ↦ ?_
  rw [(Option.isOpenEmbedding_some_excludedPointTopology' (X := X)).continuousOn_iff]
  exact continuousOn_congr fun y ↦ by simp

/-- The "strong topology" on `X ⋆ Y` as defined by Milnor, i.e. the coarsest topology making the
projections to `unitInterval`, `X` and `Y` continuous where they are defined. -/
instance : TopologicalSpace (X ⋆ Y) :=
  .induced t inferInstance ⊓ Option.excludedPointTopology'.induced fst ⊓
    Option.excludedPointTopology'.induced snd

/-- A function `Z → X ⋆ Y` is continuous iff all three projections are continuous. -/
lemma continuous_iff {f : Z → X ⋆ Y} :
    Continuous f ↔ Continuous (t ∘ f) ∧ Continuous (fst ∘ f) ∧ Continuous (snd ∘ f) := by
  refine (continuous_inf_rng
    (t₂ := .induced t inferInstance ⊓ Option.excludedPointTopology'.induced fst)
    (t₃ := Option.excludedPointTopology'.induced snd)).trans ?_
  rw [← and_assoc, continuous_induced_rng]
  refine and_congr_left' <| (continuous_inf_rng (t₂ := .induced t inferInstance)
    (t₃ := Option.excludedPointTopology'.induced fst)).trans ?_
  simp_rw [continuous_induced_rng]

/-- The parameter `t : X ⋆ Y → I` is continuous. -/
lemma continuous_t : Continuous (t : X ⋆ Y → _) :=
  (continuous_iff.1 continuous_id).1

/-- The projection `X ⋆ Y → Option X` is continuous. -/
lemma continuous_fst : Continuous (fst : X ⋆ Y → _) :=
  (continuous_iff.1 continuous_id).2.1

/-- The projection `X ⋆ Y → Option Y` is continuous. -/
lemma continuous_snd : Continuous (snd : X ⋆ Y → _) :=
  (continuous_iff.1 continuous_id).2.2

/-- The left inclusion `X → X ⋆ Y` is continuous. -/
lemma continuous_inl : Continuous (inl : X → X ⋆ Y) :=
  continuous_iff.2 ⟨continuous_const, Option.continuous_some_excludedPointTopology',
    @continuous_const _ _ (_) (_) _⟩

/-- The right inclusion `Y → X ⋆ Y` is continuous. -/
lemma continuous_inr : Continuous (inr : Y → X ⋆ Y) :=
  continuous_iff.2 ⟨continuous_const, @continuous_const _ _ (_) (_) _,
    Option.continuous_some_excludedPointTopology'⟩

/-- The projection `X × I × Y → X ⋆ Y` is continuous. -/
lemma continuous_π : Continuous (π : X × I × Y → X ⋆ Y) := by
  refine continuous_iff.2 ⟨?_, ?_, ?_⟩
  · dsimp only [Function.comp_def, π_t]; fun_prop
  · simp_rw [Function.comp_def, π_fst]
    refine Option.continuous_excludedPointTopology'_iff'.2 ⟨?_, by fun_prop⟩
    exact (isOpen_compl_singleton.preimage (_root_.continuous_fst)).preimage (_root_.continuous_snd)
  · simp_rw [Function.comp_def, π_snd]
    refine Option.continuous_excludedPointTopology'_iff'.2 ⟨?_, by fun_prop⟩
    exact (isOpen_compl_singleton.preimage (_root_.continuous_fst)).preimage (_root_.continuous_snd)

/-- For any two continuous maps `X → X'` and `Y → Y'`, the induced map `X ⋆ Y → X' ⋆ Y'` is
continuous. -/
lemma _root_.Continuous.joinMap {f : X → X'} {g : Y → Y'} (hf : Continuous f) (hg : Continuous g) :
    Continuous (map f g) :=
  continuous_iff.2 ⟨continuous_t, hf.optionMap_excludedPointTopology'.comp continuous_fst,
    hg.optionMap_excludedPointTopology'.comp continuous_snd⟩

/-- The map `X ⋆ Y → Y ⋆ X` is continuous. -/
lemma continuous_swap : Continuous (swap : X ⋆ Y → Y ⋆ X) :=
  continuous_iff.2 ⟨unitInterval.continuous_symm.comp continuous_t, continuous_snd, continuous_fst⟩

lemma isEmbedding_inl : IsEmbedding (inl : X → X ⋆ Y) := by
  refine ⟨isInducing_iff_continuous_iff.2 fun {Z _ g} ↦ ?_, inl_injective⟩
  rw [continuous_iff]
  simp [Function.comp_def, continuous_const,
    Option.isOpenEmbedding_some_excludedPointTopology'.continuous_iff (f := g)]

lemma isEmbedding_inr : IsEmbedding (inr : Y → X ⋆ Y) := by
  refine ⟨isInducing_iff_continuous_iff.2 fun {Z _ g} ↦ ?_, inr_injective⟩
  rw [continuous_iff]
  simp [Function.comp_def, continuous_const,
    Option.isOpenEmbedding_some_excludedPointTopology'.continuous_iff (f := g)]

lemma isClosedEmbedding_inl : IsClosedEmbedding (inl : X → X ⋆ Y) :=
  ⟨isEmbedding_inl, range_inl ▸ isClosed_singleton.preimage continuous_t⟩

lemma isClosedEmbedding_inr : IsClosedEmbedding (inr : Y → X ⋆ Y) :=
  ⟨isEmbedding_inr, range_inr ▸ isClosed_singleton.preimage continuous_t⟩

/-- For any two inducing maps `X → X'` and `Y → Y'`, the induced map `X ⋆ Y → X' ⋆ Y'` is
inducing. -/
lemma _root_.Topology.IsInducing.joinMap {f : X → X'} {g : Y → Y'} (hf : IsInducing f)
    (hg : IsInducing g) : IsInducing (map f g) := by
  simp_rw [isInducing_iff, instTopologicalSpace, induced_inf, induced_compose,
    show fst ∘ map f g = Option.map f ∘ fst by ext; simp, show t ∘ map f g = t from rfl,
    show snd ∘ map f g = Option.map g ∘ snd by ext; simp, ← induced_compose,
    hf.optionMap_excludedPointTopology'.eq_induced, hg.optionMap_excludedPointTopology'.eq_induced]

/-- For any two embeddings `X → X'` and `Y → Y'`, the induced map `X ⋆ Y → X' ⋆ Y'` is an
embedding. -/
lemma _root_.Topology.IsEmbedding.joinMap {f : X → X'} {g : Y → Y'} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (map f g) :=
  ⟨hf.isInducing.joinMap hg.isInducing, hf.injective.joinMap hg.injective⟩

/-- The join on two homeomorphisms. -/
def _root_.Homeomorph.joinCongr (e : X ≃ₜ X') (e' : Y ≃ₜ Y') : X ⋆ Y ≃ₜ X' ⋆ Y' where
  toFun := map e e'
  invFun := map e.symm e'.symm
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := e.continuous.joinMap e'.continuous
  continuous_invFun := e.symm.continuous.joinMap e'.symm.continuous

/-- The homeomorphism ` X ⋆ Y ≃ₜ X` given by `inl : X → X ⋆ Y` when `Y` is empty. -/
noncomputable def _root_.Homeomorph.joinIsEmpty [IsEmpty Y] : X ⋆ Y ≃ₜ X :=
  Homeomorph.symm <| IsEmbedding.toHomeomorphOfSurjective (isEmbedding_inl) <| by
    intro x
    have h : x.t = 0 := by simpa using x.snd.eq_none_or_eq_some
    have ⟨x', hx'⟩ : ∃ x', x.fst = some x' := by simpa [h] using x.fst.eq_none_or_eq_some
    use x'; ext <;> simp_all [x.snd_eq_none_iff.2 h]

/-- The homeomorphism ` X ⋆ Y ≃ₜ Y` given by `inr : Y → X ⋆ Y` when `X` is empty. -/
noncomputable def _root_.Homeomorph.isEmptyJoin [IsEmpty X] : X ⋆ Y ≃ₜ Y :=
  Homeomorph.symm <| IsEmbedding.toHomeomorphOfSurjective (isEmbedding_inr) <| by
    intro x
    have h : x.t = 1 := by simpa using x.fst.eq_none_or_eq_some
    have ⟨x', hx'⟩ : ∃ x', x.snd = some x' := by simpa [h] using x.snd.eq_none_or_eq_some
    use x'; ext <;> simp_all [x.fst_eq_none_iff.2 h]

/-- The join operation is commutative up to homeomorphism. -/
@[simps]
def _root_.Homeomorph.joinComm : X ⋆ Y ≃ₜ Y ⋆ X where
  toFun := swap
  invFun := swap
  left_inv _ := by simp
  right_inv _ := by simp
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

/-def _root_.Homeomorph.joinAssoc : (X ⋆ Y) ⋆ Z ≃ₜ X ⋆ (Y ⋆ Z) where
  toFun p := by
    refine ⟨p.fst.bind fst,
      (p.fst.rec (fun _ ↦ some ⟨none, p.snd, 1, by simp, by simp_all⟩) ?_ :
          (p.fst = none ↔ _) → _) p.fst_eq_none_iff,
        σ (σ p.t * σ ((p.fst.map t).getD 0)), ?_, ?_⟩
    · have h := p.fst_eq_none_iff; revert h
      exact p.fst.rec (by simp) fun _ _ ↦ by simp_all
    · have h := p.fst_eq_none_iff; revert h
      --refine p.fst.rec ?_ ?_
      sorry
    all_goals sorry-/

/-- The join of compact spaces is compact. -/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X ⋆ Y) := by
  obtain _ | _ := isEmpty_or_nonempty X
  · exact Homeomorph.isEmptyJoin.symm.compactSpace
  · obtain _ | _ := isEmpty_or_nonempty Y
    · exact Homeomorph.joinIsEmpty.symm.compactSpace
    · rw [← isCompact_univ_iff, ← π_surjective.range_eq]
      exact isCompact_range continuous_π

/-- The join of Hausdorff spaces is Hausdorff. -/
instance [T2Space X] [T2Space Y] : T2Space (X ⋆ Y) := by
  refine ⟨fun p p' h ↦ ?_⟩
  by_cases h' : p.t = p'.t
  · by_cases h'' : p.fst = p'.fst
    · have h''' : p.snd ≠ p'.snd := by contrapose h; ext <;> simp_all
      have h'''' : p.t ≠ 0 := by
        contrapose h'''; rw [p.snd_eq_none_iff.2 h''', p'.snd_eq_none_iff.2 <| h'.symm.trans h''']
      have ⟨y, hy⟩ : ∃ y, p.snd = some y := by simpa [h''''] using p.snd.eq_none_or_eq_some
      have ⟨y', hy'⟩ : ∃ y', p'.snd = some y' := by
        simpa [← h', h''''] using p'.snd.eq_none_or_eq_some
      replace h''' : y ≠ y' := ne_of_apply_ne Option.some <| by rwa [hy, hy'] at h'''
      obtain ⟨u, v, hu, hv, hu', hv', huv⟩ := t2_separation h'''
      exact ⟨_, _,
        (Option.isOpenEmbedding_some_excludedPointTopology'.isOpenMap _ hu).preimage continuous_snd,
        (Option.isOpenEmbedding_some_excludedPointTopology'.isOpenMap _ hv).preimage continuous_snd,
        by simp [hy, hu'], by simp [hy', hv'],
        (Set.disjoint_image_of_injective (Option.some_injective _) huv).preimage _⟩
    · have h''' : p.t ≠ 1 := by
        contrapose h''; rw [p.fst_eq_none_iff.2 h'', p'.fst_eq_none_iff.2 <| h'.symm.trans h'']
      have ⟨x, hx⟩ : ∃ x, p.fst = some x := by simpa [h'''] using p.fst.eq_none_or_eq_some
      have ⟨x', hx'⟩ : ∃ x', p'.fst = some x' := by
        simpa [← h', h'''] using p'.fst.eq_none_or_eq_some
      replace h'' : x ≠ x' := ne_of_apply_ne Option.some <| by rwa [hx, hx'] at h''
      obtain ⟨u, v, hu, hv, hu', hv', huv⟩ := t2_separation h''
      exact ⟨_, _,
        (Option.isOpenEmbedding_some_excludedPointTopology'.isOpenMap _ hu).preimage continuous_fst,
        (Option.isOpenEmbedding_some_excludedPointTopology'.isOpenMap _ hv).preimage continuous_fst,
        by simp [hx, hu'], by simp [hx', hv'],
        (Set.disjoint_image_of_injective (Option.some_injective _) huv).preimage _⟩
  · obtain ⟨u, v, hu, hv, hu', hv', huv⟩ := t2_separation h'
    exact ⟨_, _, hu.preimage continuous_t, hv.preimage continuous_t, hu', hv', huv.preimage _⟩

/-- Joins of closed sets are closed in the join of the ambient spaces. -/
lemma _root_.IsClosed.join {s : Set X} {t : Set Y} (hs : IsClosed s) (ht : IsClosed t) :
    IsClosed (s.join t) := by
  refine .inter (.preimage continuous_fst ?_) (.preimage continuous_snd ?_)
    <;> rw [← isOpen_compl_iff, Set.compl_union, Option.isOpen_excludedPointTopology'_iff]
    <;> simpa [Option.some_injective]

noncomputable def _root_.Homeomorph.Set.join (s : Set X) (t : Set Y) : s.join t ≃ₜ s ⋆ t :=
  (IsEmbedding.subtypeVal.joinMap .subtypeVal).toHomeomorph.trans (.setCongr <| by simp) |>.symm

lemma _root_.IsCompact.join {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s.join t) := by
  rw [isCompact_iff_compactSpace] at hs ht ⊢
  exact (Homeomorph.Set.join s t).symm.compactSpace

/-- When `X` and `Y` are nonempty compact Hausdorff, `π : X × I × Y → X ⋆ Y` exhibits `X ⋆ Y`
as a quotient of `X × I × Y`. In other words, in this case the strong and weak topology on the join
agree.

TODO: can this be generalised to locally compact Hausdorff spaces? Some sources
(e.g. *Homotopical Topology* by Fomenko and Fuchs, which is cited by wikipedia) claim so, but don't
give a proof. Others (e.g. *Topology and Groupoids*) prove only the compact Hausdorff case.
I first thought it could be proven using a local argument, but if I'm seeing things right that runs
into issues at the two ends of the join - joins of locally compact spaces are often not even
locally compact at those points. -/
lemma isQuotientMap_π [Nonempty X] [Nonempty Y] [CompactSpace X] [CompactSpace Y]
    [T2Space X] [T2Space Y] : IsQuotientMap (π : _ → X ⋆ Y) := by
  refine IsQuotientMap.of_surjective_continuous π_surjective continuous_π

end Join

end Topology
