/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.UnitInterval

/-! # Joins of topological spaces
In this file we define joins of topological spaces.

Since joins of e.g. simplicial complexes also exist but have a different underlying type, future
constructions of those joins will have to involve a new type instead of just equipping the type
we define here with the structure of a simplicial complex; because of that, we put everything here
in the `Topology` namespace to avoid confusion.

## TODO:
* prove `X ⋆ Y ≃ₜ X` when `Y` is empty
* prove associativity up to homeomorphism
* show equivalence to the construction as a quotient in the locally compact case
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

/-- The map `X ⋆ Y → X' ⋆ Y'` induced by two maps `X → X'` and `Y → Y'`. -/
@[simps]
def map (f : X → X') (g : Y → Y') (p : X ⋆ Y) : X' ⋆ Y' :=
  ⟨p.fst.map f, p.snd.map g, p.t, by simp, by simp⟩

/-- The map `X ⋆ Y → Y ⋆ X` swapping the two factors. -/
@[simps]
def swap (p : X ⋆ Y) : Y ⋆ X := ⟨p.snd, p.fst, unitInterval.symm p.t, by simp, by simp⟩

@[simp]
lemma swap_swap (p : X ⋆ Y) : swap (swap p) = p := by
  ext <;> simp

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

/-- For any two continuous maps `X → X'` and `Y → Y'`, the induced map `X ⋆ Y → X' ⋆ Y'` is
continuous. -/
lemma _root_.Continuous.joinMap {f : X → X'} {g : Y → Y'} (hf : Continuous f) (hg : Continuous g) :
    Continuous (map f g) :=
  continuous_iff.2 ⟨continuous_t, hf.optionMap_excludedPointTopology'.comp continuous_fst,
    hg.optionMap_excludedPointTopology'.comp continuous_snd⟩

/-- The map `X ⋆ Y → Y ⋆ X` is continuous. -/
lemma continuous_swap : Continuous (swap : X ⋆ Y → Y ⋆ X) :=
  continuous_iff.2 ⟨unitInterval.continuous_symm.comp continuous_t, continuous_snd, continuous_fst⟩

/-- The join on two homeomorphisms. -/
def _root_.Homeomorph.joinCongr (e : X ≃ₜ X') (e' : Y ≃ₜ Y') : X ⋆ Y ≃ₜ X' ⋆ Y' where
  toFun := map e e'
  invFun := map e.symm e'.symm
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := e.continuous.joinMap e'.continuous
  continuous_invFun := e.symm.continuous.joinMap e'.symm.continuous

/-- The join operation is commutative up to homeomorphism. -/
@[simps]
def _root_.Homeomorph.joinComm : X ⋆ Y ≃ₜ Y ⋆ X where
  toFun := swap
  invFun := swap
  left_inv _ := by simp
  right_inv _ := by simp
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

end Join

end Topology
