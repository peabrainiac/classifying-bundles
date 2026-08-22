/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.IsFiberBundle
import Mathlib.Topology.Algebra.Group.Torsor

/-! # Locally trivial `G`-spaces
In this file we define locally trivial `G`-spaces: a `G`-space is called locally trivial if its
projection to is orbit space locally admits equivariant trivialisations. In this sense locally
trivial `G`-spaces are just `G`-principal bundles, represented by the `G`-action on their orbit
space. -/

open Bundle

open scoped Topology

/-- A `G`-space `X` is called locally trivial if its projection to its orbit space
locally admits `G`-equivariant trivialisations. -/
class LocallyTrivialSMul (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type*) [TopologicalSpace X] [MulAction G X] : Prop where
  exists_equivariant_trivialization b :
    ∃ e : Trivialization G (Quotient.mk (MulAction.orbitRel G X)), b ∈ e.baseSet ∧ e.IsEquivariant G

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : Type*} [TopologicalSpace X] [MulAction G X]

lemma LocallyTrivialSMul.isFiberBundleMap_quotientMk [LocallyTrivialSMul G X] :
    IsFiberBundleMap G (Quotient.mk (MulAction.orbitRel G X)) where
  exists_trivialization' b := by
    have ⟨e, he, he'⟩ := LocallyTrivialSMul.exists_equivariant_trivialization b
    exact ⟨e, he⟩

/-- Every locally trivial `G`-action is in particular free. -/
instance LocallyTrivialSMul.isCancelSMul [LocallyTrivialSMul G X] : IsCancelSMul G X where
  right_cancel' g g' x h := by
    have ⟨e, hx, he⟩ := LocallyTrivialSMul.exists_equivariant_trivialization (G := G) ⟦x⟧
    replace hx : x ∈ e.source := by simpa [e.source_eq] using hx
    simpa [he.map_smul hx] using congrArg (fun x ↦ (e x).2) h

/-- TODO: move -/
@[fun_prop]
lemma continuous_quotientMk {X : Type*} [TopologicalSpace X] {s : Setoid X} :
    Continuous (Quotient.mk s) :=
  continuous_quotient_mk'

/-- Every locally trivial `G`-action is in particular continuous. -/
instance [LocallyTrivialSMul G X] : ContinuousSMul G X where
  continuous_smul := by
    choose e he he' using LocallyTrivialSMul.exists_equivariant_trivialization (G := G) (X := X)
    suffices h : ∀ b, ContinuousOn (fun x : G × X ↦ x.1 • x.2)
        (.univ ×ˢ (Quotient.mk _ ⁻¹' (e b).baseSet)) from
      continuous_iff_continuousAt.2 fun ⟨g, x⟩ ↦ (h ⟦x⟧).continuousAt <| prod_mem_nhds
        Filter.univ_mem <| ((e ⟦x⟧).open_baseSet.preimage <| by fun_prop).mem_nhds <| he ⟦x⟧
    refine fun b ↦ ?_
    have := (e b).toOpenPartialHomeomorph.symm
    refine .congr (f := fun x ↦ (e b).toOpenPartialHomeomorph.symm ⟨⟦x.2⟧, x.1 • (e b x.2).2⟩)
        ?_ fun ⟨g, x⟩ ⟨_, hx⟩ ↦ by
      simp [(e b).isEquivariant_iff_symm.1 (he' b) ⟦x⟧ (by simpa using hx),
        show x ∈ (e b).source by simpa [(e b).source_eq] using hx, -smul_eq_mul]
    refine (e b).toOpenPartialHomeomorph.continuousOn_symm.comp ?_ ?_
    · refine (continuous_quotientMk.comp continuous_snd).continuousOn.prodMk ?_
      refine continuous_smul.comp_continuousOn ?_
        (f := fun x : G × X ↦ (x.1, (e b x.2).2))
      refine continuousOn_id.prodMap (g := fun x ↦ (e b x).2) ?_
      refine continuous_snd.comp_continuousOn ?_
      rw [← (e b).source_eq]
      exact (e b).toOpenPartialHomeomorph.continuousOn
    · exact fun ⟨g, x⟩ ⟨_, hx⟩ ↦ by simpa [(e b).target_eq] using hx
