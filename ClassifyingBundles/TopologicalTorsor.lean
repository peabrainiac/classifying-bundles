/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.Torsor
import Mathlib.Topology.Algebra.Monoid

/-! # Topological torsors

In this file we provide API for topological torsors of multiplicative groups (i.e. multiplicative
torsors in which `•` and `/ₛ` are continuous). Mathlib already provides this API for additive
torsors; we simply provide a multiplicative variant of the same API here.
-/

@[expose] public section

open Topology

section Torsor

variable {V P α : Type*} [Group V] [TopologicalSpace V] [Torsor V P] [TopologicalSpace P]

variable (P) in
/-- A topological torsor over a topological group is a torsor where `•` and `/ₛ` are
continuous. -/
class IsTopologicalTorsor extends ContinuousSMul V P where
  continuous_sdiv : Continuous (fun x : P × P => x.1 /ₛ x.2)

export IsTopologicalTorsor (continuous_sdiv)

attribute [fun_prop] continuous_sdiv

variable [IsTopologicalTorsor P]

theorem Filter.Tendsto.sdiv {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f /ₛ g) l (𝓝 (x /ₛ y)) :=
  (continuous_sdiv.tendsto (x, y)).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α]

@[fun_prop]
theorem Continuous.sdiv {f g : α → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x /ₛ g x) :=
  continuous_sdiv.comp₂ hf hg

@[fun_prop]
nonrec theorem ContinuousAt.sdiv {f g : α → P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x ↦ f x /ₛ g x) x :=
  hf.sdiv hg

@[fun_prop]
nonrec theorem ContinuousWithinAt.sdiv {f g : α → P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ f x /ₛ g x) s x :=
  hf.sdiv hg

@[fun_prop]
theorem ContinuousOn.sdiv {f g : α → P} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ f x /ₛ g x) s := fun x hx ↦
  (hf x hx).sdiv (hg x hx)

include P in
variable (V P) in
/-- The underlying group of a topological torsor is a topological group. This is not an instance, as
`P` cannot be inferred. -/
theorem IsTopologicalTorsor.to_isTopologicalGroup : IsTopologicalGroup V where
  continuous_mul := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 • x.2 • p) /ₛ p => rw [smul_smul, smul_sdiv]
    fun_prop
  continuous_inv := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p /ₛ (v • p) => rw [sdiv_smul_eq_sdiv_div, sdiv_self, one_div]
    fun_prop

/-- The map `v ↦ v • p` as a homeomorphism between `V` and `P`. -/
@[simps!]
def Homeomorph.smulConst (p : P) : V ≃ₜ P where
  __ := Equiv.smulConst p

end Torsor

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance : IsTopologicalTorsor G where
  continuous_sdiv := by simp only [sdiv_eq_div]; fun_prop

end Group

section Prod

variable
  {V W P Q : Type*}
  [CommGroup V] [TopologicalSpace V]
  [Torsor V P] [TopologicalSpace P] [IsTopologicalTorsor P]
  [CommGroup W] [TopologicalSpace W]
  [Torsor W Q] [TopologicalSpace Q] [IsTopologicalTorsor Q]

instance : IsTopologicalTorsor (P × Q) where
  continuous_smul := Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_sdiv := Continuous.prodMk (by fun_prop) (by fun_prop)

end Prod

section Pi

variable
  {ι : Type*} {V P : ι → Type*}
  [∀ i, CommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, Torsor (V i) (P i)] [∀ i, TopologicalSpace (P i)] [∀ i, IsTopologicalTorsor (P i)]

instance : IsTopologicalTorsor ((i : ι) → P i) where
  continuous_smul := continuous_pi <| by simp only [Pi.smul_apply']; fun_prop
  continuous_sdiv := continuous_pi <| by simp only [Pi.sdiv_apply]; fun_prop

end Pi
