/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Homotopy.Basic

/-! # Countable concatenations of homotopies
In this file we construct countable concatenations of homotopies that converge in some suitable
sense. This code is based on mathlib PR #21616, in which I similarly constructed countable
concatenations of paths already. The PR was never merged, but perhaps upstreaming this will be a
good occasion to revive that PR and get it merged too.
-/

open Set Topology unitInterval Filter

/-- The function `I → I × ℕ` that sends `Ico 0 (1 / 2)` linearly to the first interval in `I × ℕ`,
`Ico (1 / 2) (3 / 4)` linearly to the second and so on. This is used in the construction of
countable concatenations of homotopies.

`1` is sent to the junk value `0`. This means that `countableTransIndexFun` is not globally
monotonous, but since `I` has a maximum while `I × ℕ` does not that is unfortunately unavoidable. -/
noncomputable def countableTransIndexFun : I → I × ℕ := fun t ↦ by
  let n := Nat.log 2 ⌊(σ t).1⁻¹⌋₊
  refine if ht : t < 1 then (⟨2 * (1 - σ t * (2 ^ n : ℕ)), ?_, ?_⟩, n) else 0
  <;> have ht' := symm_one ▸ symm_lt_symm.2 ht <;> have ht'' := coe_pos.2 ht'
  · suffices (σ t : ℝ) * (2 ^ n : ℕ) ≤ 1 by linarith
    calc
      _ ≤ (σ t).1 * ⌊(σ t).1⁻¹⌋₊ := ?_
      _ ≤ (σ t).1 * (σ t).1⁻¹    := by gcongr; exact Nat.floor_le <| by simp [t.2.2]
      _ = 1                      := mul_inv_cancel₀ ht''.ne'
    gcongr
    exact Nat.pow_log_le_self _ (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne'
  · suffices h : 1 ≤ (σ t : ℝ) * (2 * (2 ^ n : ℕ)) by rw [mul_left_comm] at h; linarith
    refine (mul_inv_cancel₀ ht''.ne').symm.le.trans <|
      mul_le_mul_of_nonneg_left ?_ (σ t).2.1
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.pow_succ']
    exact (Nat.lt_succ_floor _).le.trans <| Nat.cast_le.2 <| Nat.succ_le_of_lt <|
      Nat.lt_pow_succ_log_self one_lt_two _

@[simp]
lemma countableTransIndexFun_zero : countableTransIndexFun 0 = 0 := by
  simp [countableTransIndexFun]

/-- TODO: move -/
lemma Filter.mem_principal_prod {α β : Type*} {t : Set α} {f : Filter β} {s : Set (α × β)} :
    s ∈ 𝓟 t ×ˢ f ↔ { b | ∀ a ∈ t, (a, b) ∈ s } ∈ f := by
  rw [← @exists_mem_subset_iff _ f, mem_prod_iff]
  refine ⟨?_, fun _ ↦ ⟨t, ?_⟩⟩ <;> grind [mem_principal]

/-- TODO: move -/
lemma Filter.mem_top_prod {α β : Type*} {f : Filter β} {s : Set (α × β)} :
    s ∈ (⊤ : Filter α) ×ˢ f ↔ { b | ∀ a, (a, b) ∈ s } ∈ f := by
  rw [← principal_univ, mem_principal_prod]
  simp only [mem_univ, forall_true_left]

lemma tendsto_countableTransIndexFun : Tendsto countableTransIndexFun (𝓝[≠] 1) (⊤ ×ˢ atTop) := by
  intro u hu
  simp only [mem_top_prod, mem_atTop_sets, mem_setOf_eq] at hu
  obtain ⟨n, hn⟩ := hu
  refine mem_map.2 <| mem_of_superset
    (x := Ico (σ ⟨(2 ^ n)⁻¹, by simp [inv_le_one₀, one_le_pow₀]⟩) 1) ?_ fun t ht ↦ ?_
  · rw [← Set.Icc_sdiff_right, sdiff_eq, nhdsWithin, show (1 : I) = ⊤ by rfl, Icc_top]
    refine inter_mem_inf (Ici_mem_nhds ?_) (by simp)
    simp [← Subtype.coe_lt_coe]
  · simp only [mem_Ico, ← Subtype.coe_le_coe, coe_symm_eq, tsub_le_iff_right] at ht
    simp only [mem_preimage, countableTransIndexFun, ht.2, ↓reduceDIte, coe_symm_eq, Nat.cast_pow,
      Nat.cast_ofNat]
    refine hn _ (Nat.le_log_of_pow_le one_lt_two <| (Nat.le_floor_iff (by simp [t.2.2])).2 ?_) _
    grind [le_inv_of_le_inv₀]

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : ℕ → C(X, Y)}

/-- The function underlying the concatenation of countably many homotopies
`F n : (f n).Homotopy (f (n + 1))` leading up to a map `g`. We first define this separately in order
to prove a few API lemmas that then make proving continuity of this function easier. -/
noncomputable def countableTransFun (F : (n : ℕ) → (f n).Homotopy (f (n + 1))) (g : C(X, Y))
    (x : I × X) :=
    if x.1 = 1 then g x.2 else
      F (countableTransIndexFun x.1).2 ((countableTransIndexFun x.1).1, x.2)

@[simp]
lemma countableTransFun_zero {F : (n : ℕ) → (f n).Homotopy (f (n + 1))} {g : C(X, Y)} {x : X} :
    countableTransFun F g (0, x) = f 0 x := by
  simp [countableTransFun]

@[simp]
lemma countableTransFun_one {F : (n : ℕ) → (f n).Homotopy (f (n + 1))} {g : C(X, Y)} {x : X} :
    countableTransFun F g (1, x) = g x := by
  simp [countableTransFun]

/-- The sequence of intervals from `0` to `1 / 2`, from `1 / 2` to `3 / 4` etc. in the unit
interval. This is mainly used for reasoning about countable concatenations of homotopies. -/
def _root_.unitInterval.powTwoInterval (n : ℕ) : Set I :=
  Set.Icc (σ ⟨(2 ^ n)⁻¹, by simp [inv_le_one₀, one_le_pow₀]⟩)
    (σ ⟨(2 ^ (n+1))⁻¹, by simp [inv_le_one₀, one_le_pow₀]⟩)

@[simp]
lemma _root_.unitInterval.powTwoInterval_zero : powTwoInterval 0 = Set.Iic ⟨2⁻¹, by grind⟩ := by
  simp [powTwoInterval, show (0 : I) = ⊥ by rfl, show σ ⟨2⁻¹, by grind⟩ = ⟨2⁻¹, by grind⟩ by grind]

/-- On closed intervals [1 - 2 ^ n, 1 - 2 ^ (n + 1)], `countableConcatFun γ x` agrees with a
reparametrisation of `γ n`. -/
lemma countableTransFun_eqOn {F : (n : ℕ) → (f n).Homotopy (f (n + 1))} {g : C(X, Y)} (n : ℕ) :
    Set.EqOn (countableTransFun F g)
      (fun x ↦ F n (projIcc _ _ zero_le_one (2 * (1 - (1 - x.1) * (2 ^ n))), x.2))
    (powTwoInterval n ×ˢ univ) := fun x hx ↦ by
  obtain ⟨t, x⟩ := x
  obtain ⟨ht, ⟨⟩⟩ := hx
  simp only [powTwoInterval, Set.mem_Icc, ← Subtype.coe_le_coe, coe_symm_eq] at ht
  have ht' : t < 1 := coe_lt_one.1 <| ht.2.trans_lt <| by simp
  have ht'' : 0 < 1 - t.1 := by linarith [coe_lt_one.2 ht']
  simp only [countableTransFun, ht'.ne, ↓reduceIte]
  by_cases hn : Nat.log 2 ⌊(1 - t : ℝ)⁻¹⌋₊ = n
  · rw [show (countableTransIndexFun t).2 = n by simp [countableTransIndexFun, ht', hn]]
    refine congrArg _ <| Prod.ext ?_ rfl
    rw [Set.projIcc_of_mem _ <| Set.mem_Icc.1 ⟨?_, ?_⟩]
    · simp [countableTransIndexFun, ht', hn]
    · grind [mul_le_mul_of_nonneg_right ht.1 (a := 2 ^ n) (by simp)]
    · grind [pow_succ (2 : ℝ) n ▸ mul_le_mul_of_nonneg_right ht.2 (a := 2 ^ (n+1)) (by simp)]
  · replace hn : Nat.log 2 ⌊(1 - t : ℝ)⁻¹⌋₊ = n + 1 := by
      refine le_antisymm ?_ <| n.succ_le_of_lt <| (Ne.symm hn).lt_of_le ?_
      · refine (Nat.log_mono_right <| Nat.floor_le_floor <| inv_anti₀ (by simp) <|
          le_sub_comm.1 ht.2).trans ?_
        rw [← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow, inv_inv, Nat.floor_natCast,
          Nat.log_pow one_lt_two _]
      · refine le_trans ?_ <| Nat.log_mono_right <| Nat.floor_le_floor <| inv_anti₀ ht'' <|
          sub_le_comm.1 ht.1
        rw [← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow, inv_inv, Nat.floor_natCast,
          Nat.log_pow one_lt_two _]
    rw [show (countableTransIndexFun t).2 = n + 1 by simp [countableTransIndexFun, ht', hn]]
    have ht'' : 2 * (1 - (1 - t.1) * 2 ^ n) = 1 := by
      suffices h : t.1 = 1 - (2 ^ (n + 1))⁻¹ by grind
      refine le_antisymm ht.2 ?_
      rw [sub_le_comm, ← hn, ← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow]
      refine le_trans (by rw [inv_inv]) <| inv_anti₀ (by simp) <| (Nat.cast_le.2 <|
        Nat.pow_log_le_self 2 ?_).trans <| Nat.floor_le (inv_pos.2 ht'').le
      exact (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne'
    simp [countableTransIndexFun, ht', hn, ht'',
      show 2 * (1 - (1 - t.1) * 2 ^ (n + 1)) = 0 by grind]

/-- The concatenation of countably many homotopies `F n : (f n).Homotopy (f (n + 1))` leading up to
a map `g`. -/
noncomputable def countableTrans (F : (n : ℕ) → (f n).Homotopy (f (n + 1))) (g : C(X, Y))
    (hFg : ∀ x, Tendsto (fun x : ℕ × I × X ↦ F x.1 x.2) (atTop ×ˢ ⊤ ×ˢ 𝓝 x) (𝓝 (g x))) :
    (f 0).Homotopy g where
  toFun := countableTransFun F g
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    obtain ⟨t, x⟩ := x
    by_cases ht : t < 1
    · have ht' := symm_one ▸ symm_lt_symm.2 ht; have ht'' := coe_pos.2 ht'
      have hF' : ∀ n, ContinuousOn (countableTransFun F g) _ :=
        fun n ↦ (Continuous.continuousOn (by continuity)).congr <| countableTransFun_eqOn n
      cases h : Nat.log 2 ⌊(σ t : ℝ)⁻¹⌋₊ with
      | zero =>
        refine ContinuousOn.continuousAt (s := Set.Iic ⟨2⁻¹, by grind⟩ ×ˢ univ) ?_ ?_
        · simpa using hF' 0
        · refine prod_mem_nhds (Iic_mem_nhds <| Subtype.coe_lt_coe.1 ?_) univ_mem
          rw [Nat.log_eq_zero_iff, Nat.floor_lt (inv_pos.2 ht'').le, ] at h
          grind [inv_lt_comm₀]
      | succ n =>
        refine ContinuousOn.continuousAt (s := Set.Icc
          ⟨1 - (2 ^ n)⁻¹, by simp [inv_le_one_of_one_le₀ <| one_le_pow₀ one_le_two (M₀ := ℝ)]⟩
          ⟨1 - (2 ^ (n + 2))⁻¹, by
            simp [inv_le_one_of_one_le₀ <| one_le_pow₀ one_le_two (M₀ := ℝ)]⟩ ×ˢ univ) ?_ ?_
        · convert (hF' n).union_of_isClosed (hF' (n + 1)) (isClosed_Icc.prod isClosed_univ)
            (isClosed_Icc.prod isClosed_univ) using 1
          rw [powTwoInterval, powTwoInterval, ← union_prod, Icc_union_Icc_eq_Icc]
          · simp [unitInterval.symm]
          · grind [inv_anti₀, pow_le_pow_right₀, Subtype.mk_le_mk, symm_le_symm]
          · grind [inv_anti₀, pow_le_pow_right₀, Subtype.mk_le_mk, symm_le_symm]
        · refine prod_mem_nhds (Icc_mem_nhds ?_ ?_) univ_mem
            <;> rw [← Subtype.coe_lt_coe, Subtype.coe_mk]
          · replace h := h.symm.le; rw [Nat.le_log_iff_pow_le one_lt_two (Nat.floor_pos.2 <|
              (one_le_inv₀ ht'').2 (σ t).2.2).ne', Nat.le_floor_iff (inv_pos.2 ht'').le,
              le_inv_comm₀ (by simp) ht'', coe_symm_eq, sub_le_comm] at h
            refine (sub_lt_sub_left (inv_strictAnti₀ (by simp) ?_) 1).trans_le h
            grind [pow_lt_pow_right₀]
          · replace h := h.trans_lt (Nat.lt_succ_self _)
            rw [Nat.log_lt_iff_lt_pow one_lt_two
              (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne', Nat.floor_lt
              (inv_pos.2 ht'').le, inv_lt_comm₀ ht'' (by simp), coe_symm_eq, lt_sub_comm] at h
            exact h.trans_eq <| by simp
    · rw [unitInterval.lt_one_iff_ne_one, not_ne_iff] at ht
      obtain rfl := ht
      simp only [ContinuousAt, countableTransFun_one]
      rw [nhds_prod_eq, ← nhdsNE_sup_pure 1, sup_prod, pure_prod]
      refine .sup ?_ <| tendsto_map'_iff.2 <| by
        simpa [Function.comp_def, ContinuousAt] using map_continuousAt g x
      refine ((hFg x).comp <| tendsto_prodAssoc.comp <|
        (tendsto_prod_swap.comp tendsto_countableTransIndexFun).prodMap tendsto_id).congr' ?_
      refine eventuallyEq_of_mem (prod_mem_prod self_mem_nhdsWithin univ_mem) ?_
      rintro ⟨t, x⟩ ⟨ht, ⟨⟩⟩
      replace ht : t < 1 := by grind [unitInterval.le_one' (t := t)]
      simp only [Function.comp_apply, Prod.map_apply, id_eq, Equiv.prodAssoc_apply, Prod.fst_swap,
        Prod.snd_swap, countableTransFun, ht.ne, ↓reduceIte]
      exact congrArg _ (by simp [countableTransIndexFun, ht])
  map_zero_left := by simp
  map_one_left := by simp

end ContinuousMap.Homotopy
