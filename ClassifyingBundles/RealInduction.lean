/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Order.NhdsSet

/-! # Induction on real numbers
In this file we formalise a couple of variants of a classic induction principles for real numbers:
if a property holds for at least one real number, holds for at least one `t' > t` whenever it holds
for `t`, and holds for `t` whenever it holds for a sequence converging to `t` from below, it holds
for arbitrarily large real numbers. This is essentially connectness of `ℝ` in disguise - the first
condition requires the set of real numbers smaller than or equal to a number satisfying the property
to be nonempty, the second requires it to be open, and the third requires it to be closed.

Our main use case of this are variants specialised to the unit interval.
-/

open Set Topology unitInterval

@[simp]
lemma unitInterval.one_le_iff {t : I} : 1 ≤ t ↔ t = 1 :=
  ⟨fun h ↦ le_antisymm le_one' h, fun h ↦ by rw [h]⟩

/-- The unit interval is locally path-connected.
TODO: generalise, move -/
instance : LocPathConnectedSpace unitInterval := (convex_Icc 0 1).locPathConnectedSpace

/-- Induction principle stating that if a property holds for `0 : unitInterval`, holds for some
`t' ≥ t` whenever it holds for some `t < 1`, and holds for `t` whenever it holds for values
arbitrariliy close to `t`, it holds for `1`. Applying this to the property
"`P` holds for all `t' ≤ t`" for some property `P` you recover an induction principle allowing you
to prove that `P` holds in the entire interval. -/
protected lemma unitInterval.induction {motive : I → Prop} (h : motive 0)
    (h' : ∀ t < 1, motive t → ∃ t' > t, motive t')
    (h'' : ∀ t, (∃ᶠ t' in 𝓝[<] t, motive t') → motive t) : motive 1 := by
  suffices h' : IsClopen {t | ∃ t' ≥ t, motive t'} by
    simpa [-Subtype.exists] using
      (IsClopen.eq_univ h' ⟨0, 0, le_refl _, h⟩).symm.subset (mem_univ 1)
  refine ⟨?_, ?_⟩
  · refine isClosed_iff_frequently.2 fun t ht ↦ ?_
    suffices (¬∃ t' > t, motive t') → motive t by by_cases motive t <;> grind
    refine fun h' ↦ (or_not (p := motive t)).rec id fun h ↦ h'' t ?_
    refine frequently_nhdsWithin_iff.2 <|
      (LocallyConnectedSpace.open_connected_basis t).frequently_iff.2 fun u ⟨hu, htu, hu'⟩ ↦ ?_
    have ⟨t', ht', t'', ht''⟩ := Filter.frequently_iff.1 ht (hu.mem_nhds htu)
    have ht''' : t'' < t := by grind
    exact ⟨t'', hu'.Icc_subset ht' htu  ⟨ht''.1, ht'''.le⟩, ht''.2, ht'''⟩
  · refine isOpen_iff_mem_nhds.2 fun t ⟨t', ht, ht'⟩ ↦ ?_
    obtain _ | rfl := (le_one' (t := t')).lt_or_eq
    · have ⟨t'', ht'', ht'''⟩ := h' _ ‹_› ht'
      exact mem_nhds_iff.2 ⟨(Iio t''), fun t ht ↦ ⟨_, ht.le, ‹_›⟩, isOpen_Iio, ht.trans_lt ht''⟩
    · simp [show ∀ t, ∃ t' ≥ t, motive t' from fun t ↦ ⟨_, le_one', ht'⟩]

protected lemma unitInterval.induction' {motive : Set I → Prop} (h : ∀ t, ∃ u ∈ 𝓝 t, motive u)
    (h' : ∀ t, ∀ t' < t, ∀ u ∈ 𝓝ˢ (Iic t'), motive u → ∀ u' ∈ 𝓝ˢ (Icc t' t), motive u' →
      ∃ u'' ∈ 𝓝ˢ (Iic t), motive u'') : motive univ := by
  suffices h : ∃ u ∈ 𝓝ˢ (Iic 1), motive u by simpa [show (1 : I) = ⊤ by rfl] using h
  refine unitInterval.induction (motive := fun t ↦ ∃ u ∈ 𝓝ˢ (Iic t), motive u) ?_ ?_ ?_
  · simp [show (0 : I) = ⊥ by rfl, h]
  · intro t ht ⟨u, hu⟩
    have : (𝓝[>] t).NeBot := nhdsGT_neBot_of_exists_gt ⟨1, ht⟩
    obtain ⟨u', hu'⟩ := mem_nhdsSet.1 hu.1
    have ⟨t', ht'⟩ := (hasBasis_nhdsSet_Iic_Iic t).mem_iff.1 (hu'.2.1.mem_nhdsSet.2 hu'.2.2)
    exact ⟨t', ht'.1, u, Filter.mem_of_superset (hu'.2.1.mem_nhdsSet.2 ht'.2) hu'.1, hu.2⟩
  · intro t ht
    have ⟨v, hv⟩ := h t
    have ⟨v', hv'⟩ := (LocallyConnectedSpace.open_connected_basis t).mem_iff.1 hv.1
    have ⟨t', ht', u, hu⟩ :=
      Filter.frequently_iff.1 ht (inter_mem_nhdsWithin _ <| hv'.1.1.mem_nhds hv'.1.2.1)
    refine h' t t' ht'.1 _ hu.1 hu.2 v (Filter.mem_of_superset ?_ hv'.2) hv.2
    exact hv'.1.1.mem_nhdsSet.2 <| hv'.1.2.2.Icc_subset ht'.2 hv'.1.2.1
