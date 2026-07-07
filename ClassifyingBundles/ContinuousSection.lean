/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.FiberBundle.Constructions

/-! # Continuous sections of fibre bundles
API for bundled continuous sections of topological fibre bundles. Adapted from the API for Cⁿ
sections of Cⁿ fibre bundles at `Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection`.

Aside from defining `ContinuousSection` and setting up basic API and notation (`Cₛ⟮F, E⟯`), we also
define pointwise algebraic operations on sections, currently only in the case of real vector
bundles. This could be generalised in the future using special typeclasses `ContinuousBundleAdd`,
`ContinuousBundleNeg` etc.
-/

open Bundle FiberBundle Function Filter

variable (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E]

/-- The type of continuous sections of a topological `FiberBundle F E`, written `Cₛ(F, E)` in
the `Bundle` namespace. -/
structure ContinuousSection (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
    (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] where
  toFun : ∀ b, E b
  continuous_toFun : Continuous fun b ↦ (⟨b, toFun b⟩ : TotalSpace F E)

@[inherit_doc] scoped[Bundle] notation "Cₛ⟮" F ", " E "⟯" => ContinuousSection F E

namespace ContinuousSection

variable {F E}

instance : DFunLike Cₛ⟮F, E⟯ B E where
  coe := ContinuousSection.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ⟮F, E⟯}

@[simp]
theorem toFun_eq_coe : s.toFun = s := rfl

@[simp]
theorem coeFn_mk (s : ∀ b, E b) (hs : Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) :
    (mk s hs : ∀ b, E b) = s := rfl

protected theorem continuous (s : Cₛ⟮F, E⟯) : Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F E) :=
  s.continuous_toFun

theorem coe_inj ⦃s t : Cₛ⟮F, E⟯⦄ (h : (s : ∀ b, E b) = t) : s = t :=
  DFunLike.ext' h

theorem coe_injective : Injective ((↑) : Cₛ⟮F, E⟯ → ∀ b, E b) :=
  coe_inj

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h

/-- TODO: find home -/
@[fun_prop]
lemma _root_.Bundle.TotalSpace.continuous_trivialSnd : Continuous (TotalSpace.trivialSnd B F) := by
  simp [continuous_iff_le_induced, Trivial.topologicalSpace]

/-- Continuous sections of trivial bundles are equivalently continuous maps. -/
@[simps]
def equivContinuousMap : Cₛ⟮F, Trivial B F⟯ ≃ C(B, F) where
  toFun s := ⟨fun b ↦ s b, TotalSpace.continuous_trivialSnd.comp s.continuous⟩
  invFun f := ⟨fun b ↦ f b, (Trivial.homeomorphProd B F).symm.continuous.comp <|
    continuous_id.prodMk f.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ContinuousSection

section Operations

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {B : Type*} [TopologicalSpace B]
  {E : B → Type*} [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]

lemma ContinuousWithinAt.section_add [VectorBundle ℝ F E] {s t : ∀ b, E b} {u : Set B} {b : B}
    (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b)
    (ht : ContinuousWithinAt (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ (⟨b, (s + t) b⟩ : TotalSpace F E)) u b := by
  rw [continuousWithinAt_section] at hs ht ⊢
  set e := trivializationAt F E b
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E b)
    · intro x hx
      apply (e.linear ℝ hx).1
  · apply (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' b)).1

lemma ContinuousAt.section_add [VectorBundle ℝ F E] {s t : ∀ b, E b} {b : B}
    (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b)
    (ht : ContinuousAt (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ (⟨b, (s + t) b⟩ : TotalSpace F E)) b := by
  rw [← continuousWithinAt_univ] at hs ht ⊢
  exact hs.section_add ht

lemma ContinuousOn.section_add [VectorBundle ℝ F E] {s t : ∀ b, E b} {u : Set B}
    (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u)
    (ht : ContinuousOn (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ (⟨b, (s + t) b⟩ : TotalSpace F E)) u :=
  fun b hb ↦ (hs b hb).section_add (ht b hb)

lemma Continuous.section_add [VectorBundle ℝ F E] {s t : ∀ b, E b}
    (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)))
    (ht : Continuous (fun b ↦ (⟨b, t b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ (⟨b, (s + t) b⟩ : TotalSpace F E)) := by
  rw [← continuousOn_univ] at hs ht ⊢
  exact hs.section_add ht

lemma ContinuousWithinAt.section_neg [VectorBundle ℝ F E] {s : ∀ b, E b} {u : Set B} {b : B}
    (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ (⟨b, (-s) b⟩ : TotalSpace F E)) u b := by
  rw [continuousWithinAt_section] at hs ⊢
  set e := trivializationAt F E b
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E b)
    · intro x hx
      apply (e.linear ℝ hx).map_neg
  · apply (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' b)).map_neg

lemma ContinuousAt.section_neg [VectorBundle ℝ F E] {s : ∀ b, E b} {b : B}
    (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ (⟨b, (-s) b⟩ : TotalSpace F E)) b := by
  rw [← continuousWithinAt_univ] at hs ⊢
  exact hs.section_neg

lemma ContinuousOn.section_neg [VectorBundle ℝ F E] {s : ∀ b, E b} {u : Set B}
    (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ (⟨b, (-s) b⟩ : TotalSpace F E)) u :=
  fun b hb ↦ (hs b hb).section_neg

lemma Continuous.section_neg [VectorBundle ℝ F E] {s : ∀ b, E b}
    (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ (⟨b, (-s) b⟩ : TotalSpace F E)) := by
  rw [← continuousOn_univ] at hs ⊢
  exact hs.section_neg

lemma ContinuousWithinAt.section_sub [VectorBundle ℝ F E] {s t : ∀ b, E b} {u : Set B} {b : B}
    (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b)
    (ht : ContinuousWithinAt (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ (⟨b, (s - t) b⟩ : TotalSpace F E)) u b := by
  rw [sub_eq_add_neg]
  exact hs.section_add ht.section_neg

lemma ContinuousAt.section_sub [VectorBundle ℝ F E] {s t : ∀ b, E b} {b : B}
    (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b)
    (ht : ContinuousAt (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ (⟨b, (s - t) b⟩ : TotalSpace F E)) b := by
  rw [← continuousWithinAt_univ] at hs ht ⊢
  exact hs.section_sub ht

lemma ContinuousOn.section_sub [VectorBundle ℝ F E] {s t : ∀ b, E b} {u : Set B}
    (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u)
    (ht : ContinuousOn (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ (⟨b, (s - t) b⟩ : TotalSpace F E)) u :=
  fun b hb ↦ (hs b hb).section_sub (ht b hb)

lemma Continuous.section_sub [VectorBundle ℝ F E] {s t : ∀ b, E b}
    (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)))
    (ht : Continuous (fun b ↦ (⟨b, t b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ (⟨b, (s - t) b⟩ : TotalSpace F E)) := by
  rw [← continuousOn_univ] at hs ht ⊢
  exact hs.section_sub ht

lemma ContinuousWithinAt.section_smul [VectorBundle ℝ F E] {f : B → ℝ} {s : ∀ b, E b} {u : Set B}
    {b : B} (hf : ContinuousWithinAt f u b)
    (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) u b := by
  rw [continuousWithinAt_section] at hs ⊢
  set e := trivializationAt F E b
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E b)
    · intro x hx
      dsimp
      apply (e.linear ℝ hx).map_smul
  · apply (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' b)).map_smul

lemma ContinuousAt.section_smul [VectorBundle ℝ F E] {f : B → ℝ} {s : ∀ b, E b} {b : B}
    (hf : ContinuousAt f b) (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) b := by
  rw [← continuousWithinAt_univ] at hf hs ⊢
  exact hf.section_smul hs

lemma ContinuousOn.section_smul [VectorBundle ℝ F E] {f : B → ℝ} {s : ∀ b, E b} {u : Set B}
    (hf : ContinuousOn f u) (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) u :=
  fun b hb ↦ (hf b hb).section_smul (hs b hb)

lemma Continuous.section_smul [VectorBundle ℝ F E] {f : B → ℝ} {s : ∀ b, E b}
    (hf : Continuous f) (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ (⟨b, (f • s) b⟩ : TotalSpace F E)) := by
  rw [← continuousOn_univ] at hf hs ⊢
  exact hf.section_smul hs

lemma ContinuousWithinAt.section_const_smul [VectorBundle ℝ F E] {s : ∀ b, E b} {u : Set B} {b : B}
    (r : ℝ) (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ (⟨b, (r • s) b⟩ : TotalSpace F E)) u b :=
  continuousWithinAt_const.section_smul hs

lemma ContinuousAt.section_const_smul [VectorBundle ℝ F E] {s : ∀ b, E b} {b : B}
    (r : ℝ) (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ (⟨b, (r • s) b⟩ : TotalSpace F E)) b :=
  continuousAt_const.section_smul hs

lemma ContinuousOn.section_const_smul [VectorBundle ℝ F E] {s : ∀ b, E b} {u : Set B}
    (r : ℝ) (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ (⟨b, (r • s) b⟩ : TotalSpace F E)) u :=
  continuousOn_const.section_smul hs

lemma Continuous.section_const_smul [VectorBundle ℝ F E] {s : ∀ b, E b}
    (r : ℝ) (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ (⟨b, (r • s) b⟩ : TotalSpace F E)) :=
  continuous_const.section_smul hs

namespace ContinuousSection

instance instAdd [VectorBundle ℝ F E] : Add Cₛ⟮F, E⟯ where
  add s t := ⟨_, s.continuous.section_add t.continuous⟩

@[simp]
lemma coe_add [VectorBundle ℝ F E] (s t : Cₛ⟮F, E⟯) : ⇑(s + t) = s + t := rfl

instance instSub [VectorBundle ℝ F E] : Sub Cₛ⟮F, E⟯ where
  sub s t := ⟨_, s.continuous.section_sub t.continuous⟩

@[simp]
lemma coe_sub [VectorBundle ℝ F E] (s t : Cₛ⟮F, E⟯) : ⇑(s - t) = s - t := rfl

instance instZero [VectorBundle ℝ F E] : Zero Cₛ⟮F, E⟯ :=
  ⟨⟨fun _ => 0, Trivialization.continuous_zeroSection ℝ⟩⟩

instance inhabited [VectorBundle ℝ F E] : Inhabited Cₛ⟮F, E⟯ :=
  ⟨0⟩

@[simp]
lemma coe_zero [VectorBundle ℝ F E] : ⇑(0 : Cₛ⟮F, E⟯) = 0 :=
  rfl

instance [VectorBundle ℝ F E] : Neg Cₛ⟮F, E⟯ :=
  ⟨fun s ↦ ⟨-s, s.continuous.section_neg⟩⟩

@[simp]
theorem coe_neg [VectorBundle ℝ F E] (s : Cₛ⟮F, E⟯) : ⇑(-s) = -s :=
  rfl

instance instNSMul [VectorBundle ℝ F E] : SMul ℕ Cₛ⟮F, E⟯ :=
  ⟨nsmulRec⟩

@[simp]
lemma coe_nsmul [VectorBundle ℝ F E] (s : Cₛ⟮F, E⟯) (k : ℕ) : ⇑(k • s : Cₛ⟮F, E⟯) = k • ⇑s := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

instance instZSMul [VectorBundle ℝ F E] : SMul ℤ Cₛ⟮F, E⟯ :=
  ⟨zsmulRec⟩

@[simp]
lemma coe_zsmul [VectorBundle ℝ F E] (s : Cₛ⟮F, E⟯) (z : ℤ) : ⇑(z • s : Cₛ⟮F, E⟯) = z • ⇑s := by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]

instance instAddCommGroup [VectorBundle ℝ F E] : AddCommGroup Cₛ⟮F, E⟯ :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance instSMul [VectorBundle ℝ F E] : SMul ℝ Cₛ⟮F, E⟯ :=
  ⟨fun c s ↦ ⟨c • ⇑s, s.continuous.section_const_smul c⟩⟩

@[simp]
theorem coe_smul [VectorBundle ℝ F E] (r : ℝ) (s : Cₛ⟮F, E⟯) : ⇑(r • s : Cₛ⟮F, E⟯) = r • ⇑s :=
  rfl

variable (F E) in
/-- The additive morphism from `C^n` sections to dependent maps. -/
def coeAddHom [VectorBundle ℝ F E] : Cₛ⟮F, E⟯ →+ ∀ x, E x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeAddHom_apply [VectorBundle ℝ F E] (s : Cₛ⟮F, E⟯) : coeAddHom F E s = s := rfl

instance instModule [VectorBundle ℝ F E] : Module ℝ Cₛ⟮F, E⟯ :=
  coe_injective.module ℝ (coeAddHom F E) coe_smul

end ContinuousSection

end Operations
