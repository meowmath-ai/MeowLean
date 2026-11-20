/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Modified for Lean and Mathlib 4.36.0.

import Flypitch4.Collapse
import Flypitch4.AlephOne

open scoped Flypitch
open Lattice

universe u

open Set TopologicalSpace Cardinal

local infix:65 " ⟹ " => Lattice.imp
local infix:50 " ⇔ " => Lattice.biimp

local infix:75 " ≺ " => (fun x y => (bSet.larger_than x y)ᶜ)

local infix:75 " ≼ " => (fun x y => bSet.injects_into x y)

noncomputable abbrev pSet_aleph1 : PSet.{u} := PSet.card_ex (Cardinal.aleph 1)

local notation "ω" => (bSet.omega)

attribute [local instance] Classical.propDecidable

namespace bSet

section aleph_one

variable {𝔹 : Type*} [NontrivialCompleteBooleanAlgebra 𝔹]

noncomputable def aleph_one : bSet 𝔹 := a1

lemma aleph_one_satisfies_spec {Γ : 𝔹} :
    Γ ≤ aleph_one_Ord_spec (aleph_one (𝔹 := 𝔹)) :=
  a1_spec

lemma aleph_one_check_sub_aleph_one {Γ : 𝔹} :
    Γ ≤ (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) ⊆ᴮ aleph_one :=
  aleph_one_check_sub_aleph_one_aux a1_Ord a1_spec

lemma aleph_one_le_of_omega_lt {Γ : 𝔹} :
    Γ ≤ le_of_omega_lt (aleph_one (𝔹 := 𝔹)) :=
  a1_le_of_omega_lt

end aleph_one

section lemmas

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

lemma check_forall (x : PSet.{u}) (ϕ : bSet 𝔹 → 𝔹) {b : 𝔹} :
    (∀ (y : x.Type), b ≤ ϕ (check (x.Func y))) →
    (b ≤ (⨅ (y : x.Type), ϕ (check (x.Func y)))) :=
  fun H => le_iInf H

lemma aleph_one_check_is_aleph_one_of_omega_lt {Γ : 𝔹}
    (H : Γ ≤ (larger_than bSet.omega (check pSet_aleph1) : 𝔹)ᶜ) :
    Γ ≤ (check pSet_aleph1 : bSet 𝔹) =ᴮ (aleph_one (𝔹 := 𝔹)) := by

  refine subset_ext aleph_one_check_sub_aleph_one ?_
  have hspec := @aleph_one_satisfies_spec 𝔹 _ Γ
  unfold aleph_one_Ord_spec at hspec
  have hspec_rr : Γ ≤ ⨅ y, Ord y ⟹ ((injects_into y bSet.omega)ᶜ ⟹ a1 ⊆ᴮ y) :=
    le_trans hspec (le_trans inf_le_right inf_le_right)
  have happ : Γ ≤ Ord (check pSet_aleph1) ⟹ ((injects_into (check pSet_aleph1) bSet.omega)ᶜ ⟹
      a1 ⊆ᴮ check pSet_aleph1) :=
    le_trans hspec_rr (iInf_le _ _)
  have hOrd : Γ ≤ Ord (check pSet_aleph1) := Ord_card_ex (Cardinal.aleph 1)
  have hnotinj : Γ ≤ (injects_into (check pSet_aleph1) bSet.omega)ᶜ := by
    rw [← imp_bot, ← deduction]
    apply bv_absurd (larger_than bSet.omega (check pSet_aleph1))
    · apply larger_than_of_surjects_onto
      exact surjects_onto_of_injects_into' inf_le_right aleph_one_check_exists_mem
    · exact le_trans inf_le_left H
  have step1 : Γ ≤ (injects_into (check pSet_aleph1) bSet.omega)ᶜ ⟹ a1 ⊆ᴮ check pSet_aleph1 :=
    le_trans (le_inf happ hOrd) bv_imp_elim
  exact le_trans (le_inf step1 hnotinj) bv_imp_elim

theorem CH_true_aux
    (H_aleph_one : ∀ {Γ : 𝔹}, Γ ≤ le_of_omega_lt (check pSet_aleph1 : bSet 𝔹))
    (H_not_lt    : ∀ {Γ : 𝔹}, Γ ≤ ((check pSet_aleph1 : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ)
    : ∀ {Γ : 𝔹}, Γ ≤ CH := by

  intro Γ

  unfold CH
  rw [← imp_bot, ← deduction]

  rw [inf_iSup_eq']
  apply iSup_le; intro x
  simp_rw [inf_iSup_eq']
  apply iSup_le; intro y

  set ctx := Γ ⊓ (Ord x ⊓ ((larger_than bSet.omega x)ᶜ ⊓ (larger_than x y)ᶜ ⊓
               injects_into y (bv_powerset bSet.omega)))
  have hOrd : ctx ≤ Ord x :=
    inf_le_right.trans inf_le_left
  have hLtX : ctx ≤ (larger_than bSet.omega x)ᶜ :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hLtY : ctx ≤ (larger_than x y)ᶜ :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hInj : ctx ≤ injects_into y (bv_powerset bSet.omega) :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)

  have hInj_a1_x : ctx ≤ injects_into (check pSet_aleph1) x :=

    le_trans (le_inf
      (le_trans (le_inf
        (H_aleph_one.trans (iInf_le _ x))
        hOrd)
        bv_imp_elim)
      hLtX)
      bv_imp_elim

  have hLt_a1_y : ctx ≤ (larger_than (check pSet_aleph1) y)ᶜ :=
    bSet_lt_of_le_of_lt hInj_a1_x hLtY

  have hLt_a1_cont : ctx ≤ (larger_than (check pSet_aleph1) (bv_powerset bSet.omega))ᶜ :=
    bSet_lt_of_lt_of_le hLt_a1_y hInj

  have hPos : ctx ≤ larger_than (check pSet_aleph1) (bv_powerset bSet.omega) := by
    have h : ctx ≤ ((check pSet_aleph1 : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ := H_not_lt
    simp only [compl_compl] at h
    exact h
  exact bv_absurd _ hPos hLt_a1_cont

def rel_of_array (x y : bSet 𝔹) (af : x.type → y.type → 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun pr : (prod x y).type => af pr.1 pr.2)

lemma rel_of_array_surj (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_bval₁ : ∀ i, x.bval i = ⊤)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    (H_wide : ∀ j, (⨆ i, af i j) = ⊤) {Γ}
    : Γ ≤ (is_surj x y (rel_of_array x y af)) := by

  apply le_iInf; intro v
  rw [← deduction]

  rw [← @bounded_exists 𝔹 _ x (fun w => pair w v ∈ᴮ rel_of_array x y af)
    (h_congr := B_ext_pair_mem_left)]

  rw [mem_unfold, inf_iSup_eq']
  apply iSup_le; intro j₀

  have step1 : Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀) ≤
      ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ᴮ rel_of_array x y af := by
    apply le_trans le_top
    rw [← H_wide j₀]
    apply iSup_le; intro i₀
    apply le_iSup_of_le i₀
    refine le_inf ?_ ?_
    · rw [H_bval₁]; exact le_top
    ·
      unfold rel_of_array
      rw [mem_unfold]
      simp only [set_of_indicator_bval, set_of_indicator_func, prod_func]
      apply le_iSup_of_le (i₀, j₀)
      simp [bv_eq_refl]

  have heq : Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀) ≤ v =ᴮ y.func j₀ :=
    inf_le_right.trans inf_le_right

  exact @bv_rw' 𝔹 _ v (y.func j₀) _ heq
    (ϕ := fun z => ⨆ i, x.bval i ⊓ pair (x.func i) z ∈ᴮ rel_of_array x y af)
    (h_congr := B_ext_iSup (h := fun i => B_ext_inf B_ext_const B_ext_pair_mem_right))
    (H_new := step1)

lemma mem_left_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ} (H_mem_left : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (H_bval₁ : ∀ i, x.bval i = ⊤)
    : Γ ≤ w₁ ∈ᴮ x := by

  unfold rel_of_array at H_mem_left
  rw [mem_unfold] at H_mem_left
  simp only [set_of_indicator_bval, set_of_indicator_func, prod_func] at H_mem_left

  rw [mem_unfold]
  apply H_mem_left.trans
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le i
  refine le_inf ?_ ?_
  · rw [H_bval₁]; exact le_top
  · exact inf_le_right.trans eq_of_eq_pair_left

lemma mem_right_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ} (H_mem_right : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    : Γ ≤ w₂ ∈ᴮ y := by
  unfold rel_of_array at H_mem_right
  rw [mem_unfold] at H_mem_right
  simp only [set_of_indicator_bval, set_of_indicator_func, prod_func] at H_mem_right
  rw [mem_unfold]
  apply H_mem_right.trans
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le j
  refine le_inf ?_ ?_
  · rw [H_bval₂]; exact le_top
  · exact inf_le_right.trans eq_of_eq_pair_right

lemma rel_of_array_extensional (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ (is_func (rel_of_array x y af)) := by

  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]

  unfold rel_of_array
  simp only [mem_unfold, set_of_indicator_bval, set_of_indicator_func, prod_func] at *

  simp_rw [iSup_inf_eq', inf_iSup_eq', iSup_inf_eq']
  apply iSup_le; intro p₁
  obtain ⟨i₁, j₁⟩ := p₁
  apply iSup_le; intro p₂
  obtain ⟨i₂, j₂⟩ := p₂
  simp only []

  have hpair₁ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hpair₂ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂) :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have haf₁ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              af i₁ j₁ :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have haf₂ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              af i₂ j₂ :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have heq_w : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              w₁ =ᴮ w₂ := inf_le_right

  have hw₁ := hpair₁.trans (eq_of_eq_pair_left (x := w₁) (y := v₁))
  have hv₁ := hpair₁.trans (eq_of_eq_pair_right (x := w₁) (y := v₁))
  have hw₂ := hpair₂.trans (eq_of_eq_pair_left (x := w₂) (y := v₂))
  have hv₂ := hpair₂.trans (eq_of_eq_pair_right (x := w₂) (y := v₂))

  have hxi := bv_trans (bv_symm hw₁) (bv_trans heq_w hw₂)

  by_cases hjj : j₁ = j₂
  ·

    apply bv_trans hv₁

    convert bv_symm hv₂ using 2
    exact congrArg y.func hjj
  ·

    by_cases hii : i₁ = i₂
    ·

      have haf₂_rw : af i₂ j₂ = af i₁ j₂ := by rw [hii]
      have : af i₁ j₁ ⊓ af i₂ j₂ ≤ ⊥ := by rw [haf₂_rw]; exact H_anti i₁ j₁ j₂ hjj
      exact bv_exfalso (le_trans (le_inf haf₁ haf₂) this)
    ·

      have hbot : x.func i₁ =ᴮ x.func i₂ ≤ ⊥ := by
        rw [le_bot_iff]
        by_contra h
        exact hii (H_inj i₁ i₂ (bot_lt_iff_ne_bot.mpr h))
      exact bv_exfalso (hxi.trans hbot)

lemma rel_of_array_is_func' (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    (H_tall : ∀ i, (⨆ j, af i j) = ⊤)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ is_func' x y (rel_of_array x y af) := by

  refine le_inf (rel_of_array_extensional x y af H_anti H_inj) ?_

  rw [is_total_iff_is_total']

  apply le_iInf; intro i₀
  rw [← deduction]

  apply le_trans le_top
  rw [← H_tall i₀]
  apply iSup_le; intro j₀
  apply le_iSup_of_le j₀
  refine le_inf ?_ ?_
  · rw [H_bval₂]; exact le_top
  ·
    unfold rel_of_array
    rw [mem_unfold]
    simp only [set_of_indicator_bval, set_of_indicator_func, prod_func]
    apply le_iSup_of_le (i₀, j₀)
    simp [bv_eq_refl]

section function_reflect

private lemma fBrec_exists
    {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {D : Set 𝔹} {y : PSet.{u}} {g : bSet 𝔹} {Γ : 𝔹}
    (H_is_func' : Γ ≤ is_func' bSet.omega (check y) g)
    (H_nonzero : ⊥ < Γ)
    (AE : ∀ (px py : PSet) {f : bSet 𝔹} {Γ' : 𝔹},
            Γ' ≤ is_func' (check px) (check py) f →
              ⊥ < Γ' →
                ∀ (i : px.Type),
                  ∃ (j : py.Type) (Γ'' : 𝔹), ⊥ < Γ'' ∧ Γ'' ≤ Γ' ∧
                    Γ'' ≤ is_func' (check px) (check py) f ∧
                    Γ'' ≤ pair (check (px.Func i)) (check (py.Func j)) ∈ᴮ f ∧
                    Γ'' ∈ D)

    : ∀ (n : ℕ) (Bprev : 𝔹), ⊥ < Bprev → Bprev ≤ is_func' bSet.omega (check y) g →
        ∃ (j : y.Type) (B : 𝔹), ⊥ < B ∧ B ≤ Bprev ∧
          B ≤ is_func' bSet.omega (check y) g ∧
          B ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func j)) ∈ᴮ g ∧
          B ∈ D := by
  intro n Bprev hpos hfunc
  have ae := AE PSet.omega y hfunc hpos (⟨n⟩ : PSet.omega.Type)
  obtain ⟨j, B, hpos', hle, hfunc', hpair, hmem⟩ := ae
  exact ⟨j, B, hpos', hle, hfunc', hpair, hmem⟩

open Flypitch in

lemma function_reflect_of_omega_closed
    {D : Set 𝔹} (H_docs : Flypitch.DenseOmegaClosed D)
    {y : PSet.{u}} {g : bSet 𝔹} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H_is_func' : Γ ≤ is_func' bSet.omega (check y) g)
    (H_function : Γ ≤ is_function bSet.omega (check y) g)
    (AE : ∀ (px py : PSet) {f : bSet 𝔹} {Γ' : 𝔹},
            Γ' ≤ is_func' (check px) (check py) f →
              ⊥ < Γ' →
                ∀ (i : px.Type),
                  ∃ (j : py.Type) (Γ'' : 𝔹), ⊥ < Γ'' ∧ Γ'' ≤ Γ' ∧
                    Γ'' ≤ is_func' (check px) (check py) f ∧
                    Γ'' ≤ pair (check (px.Func i)) (check (py.Func j)) ∈ᴮ f ∧
                    Γ'' ∈ D)
    : ∃ (f : PSet.{u}) (Γ' : 𝔹), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      (Γ' ≤ check f =ᴮ g) ∧ PSet.is_func PSet.omega y f := by

  let GoodB : 𝔹 → Prop := fun B => ⊥ < B ∧ B ≤ is_func' bSet.omega (check y) g

  have step_exists : ∀ n (Bprev : 𝔹), GoodB Bprev →
      ∃ (j : y.Type) (B : 𝔹), GoodB B ∧ B ≤ Bprev ∧
        B ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func j)) ∈ᴮ g ∧ B ∈ D :=
    fun n Bprev ⟨hpos, hfunc⟩ => by
      obtain ⟨j, B, hpos', hle, hfunc', hpair, hmem⟩ :=
        fBrec_exists H_is_func' H_nonzero AE n Bprev hpos hfunc
      exact ⟨j, B, ⟨hpos', hfunc'⟩, hle, hpair, hmem⟩

  let mkState : ℕ → {j : y.Type // True} × {B : 𝔹 // GoodB B} :=
    Nat.rec
      (
        let h₀ := step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩
        ⟨⟨h₀.choose, trivial⟩, ⟨h₀.choose_spec.choose, h₀.choose_spec.choose_spec.1⟩⟩)
      (
        fun n prev =>
          let h := step_exists (n + 1) prev.2.1 prev.2.2
          ⟨⟨h.choose, trivial⟩, ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩⟩)

  let fr : ℕ → y.Type := fun n => (mkState n).1.1
  let fBᵦ : ℕ → 𝔹 := fun n => (mkState n).2.1

  have fBᵦ_pos : ∀ n, ⊥ < fBᵦ n := fun n => (mkState n).2.2.1
  have fBᵦ_func' : ∀ n, fBᵦ n ≤ is_func' bSet.omega (check y) g :=
    fun n => (mkState n).2.2.2

  have fBᵦ_le : ∀ n, fBᵦ (n + 1) ≤ fBᵦ n := by
    intro n

    exact (step_exists (n + 1) (mkState n).2.1 (mkState n).2.2).choose_spec.choose_spec.2.1
  have fBᵦ0_le_Γ : fBᵦ 0 ≤ Γ := by

    exact (step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩).choose_spec.choose_spec.2.1
  have fBᵦ_pair : ∀ n, fBᵦ n ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func (fr n))) ∈ᴮ g := by
    intro n
    cases n with
    | zero =>

      exact (step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩).choose_spec.choose_spec.2.2.1
    | succ n =>

      exact (step_exists (n + 1) (mkState n).2.1 (mkState n).2.2).choose_spec.choose_spec.2.2.1
  have fBᵦ_mem : ∀ n, fBᵦ n ∈ D := by
    intro n
    cases n with
    | zero =>
      exact (step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩).choose_spec.choose_spec.2.2.2
    | succ n =>
      exact (step_exists (n + 1) (mkState n).2.1 (mkState n).2.2).choose_spec.choose_spec.2.2.2

  let fr' : PSet.omega.Type → y.Type := fun k => fr k.down
  let f' : PSet.{u} :=
    PSet.function_mk.mk (x := PSet.omega) (fun (k : PSet.omega.Type) => y.Func (fr' k))
      (fun i j heqv => by
        have hij : i = j := PSet.omega_inj heqv
        subst hij; exact PSet.Equiv.refl _)
  have f'_is_func : PSet.is_func PSet.omega y f' :=
    PSet.function_mk.mk_is_func _ (fun i => PSet.func_mem y (fr' i))

  have Γ'_pos : ⊥ < ⨅ n, fBᵦ n :=
    nonzero_iInf_of_mem_DenseOmegaClosed H_docs fBᵦ_le fBᵦ_mem
  have Γ'_le_Γ : (⨅ n, fBᵦ n) ≤ Γ :=
    (iInf_le _ 0).trans fBᵦ0_le_Γ

  have iInf_fBᵦ_pair : ∀ n, (⨅ m, fBᵦ m) ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func (fr' ⟨n⟩))) ∈ᴮ g :=
    fun n => (iInf_le _ n).trans (fBᵦ_pair n)

  have f'_mem : ∀ (i : PSet.omega.Type),
      (⊤ : 𝔹) ≤ pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ (check f' : bSet 𝔹) := by
    intro i

    have hmem : PSet.pSet_pair (PSet.omega.Func i) (y.Func (fr' i)) ∈ f' :=
      PSet.function_mk.mk_mem

    have h : (⊤ : 𝔹) ≤ check (PSet.pSet_pair (PSet.omega.Func i) (y.Func (fr' i))) ∈ᴮ check f' :=
      check_mem hmem

    exact subst_congr_mem_left' (check_pset_pair (Γ := (⊤ : 𝔹))) h

  have hΓ'_f'_is_function : (⨅ n, fBᵦ n) ≤ is_function (check PSet.omega) (check y) (check f') :=
    le_trans le_top (check_is_func f'_is_func)
  have hΓ'_g_is_function : (⨅ n, fBᵦ n) ≤ is_function bSet.omega (check y) g :=
    (iInf_le _ 0).trans (fBᵦ0_le_Γ.trans H_function)

  have hΓ'_f'_is_func' : (⨅ n, fBᵦ n) ≤ is_func' (check PSet.omega) (check y) (check f') :=
    hΓ'_f'_is_function.trans inf_le_left
  have hΓ'_g_is_func' : (⨅ n, fBᵦ n) ≤ is_func' bSet.omega (check y) g :=
    hΓ'_g_is_function.trans inf_le_left
  have Γ'_le_eq : (⨅ n, fBᵦ n) ≤ check f' =ᴮ g := by

    apply mem_ext
    ·
      apply le_iInf; intro z; rw [← deduction]

      have hz_in_f' := inf_le_right (a := ⨅ n, fBᵦ n) (b := z ∈ᴮ check f')
      rw [mem_unfold] at hz_in_f'

      have hz_in_prod : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ≤ z ∈ᴮ prod (check PSet.omega) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_f'_is_function)) inf_le_right

      rw [mem_unfold] at hz_in_prod

      have hctx_le : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ≤
          ⨆ (ij : (prod (check PSet.omega) (check y)).type),
          (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) := by
        rw [← inf_iSup_eq]
        apply le_inf
        · exact le_refl _
        · exact hz_in_prod

      apply hctx_le.trans
      apply iSup_le; intro ij

      have hstep : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) ≤
          z ∈ᴮ g := by

        have hbval : (prod (check PSet.omega) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]

        let i : PSet.omega.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2

        have hfunc : (prod (check PSet.omega) (check y)).func ij =
            pair (check (PSet.omega.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]

        have hpair_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ check f')
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hf'_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have h_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_f'_is_func')
            bv_refl hpair_eq hf'_fri
        have hg_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i.down)
        have hg_j : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' h_eq (ϕ := fun z => pair (check (PSet.omega.Func i)) z ∈ᴮ g)
            (h_congr := B_ext_pair_mem_right) (H_new := hg_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ g)
          (h_congr := B_ext_mem_left) (H_new := hg_j)
      exact hstep
    ·
      apply le_iInf; intro z; rw [← deduction]

      have hz_in_prod : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ≤ z ∈ᴮ prod (check PSet.omega) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_g_is_function)) inf_le_right

      conv at hz_in_prod => rw [show z ∈ᴮ prod (check PSet.omega) (check y) =
          ⨆ (i : (prod (check PSet.omega) (check y)).type),
          (prod (check PSet.omega) (check y)).bval i ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func i
          from mem_unfold]

      have hctx_le : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ≤
          ⨆ (ij : (prod (check PSet.omega) (check y)).type),
          (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) := by
        have heq : (⨆ (ij : (prod (check PSet.omega) (check y)).type),
              (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
              ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij)) =
              (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
              ⨆ (ij : (prod (check PSet.omega) (check y)).type),
              (prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij :=
          (inf_iSup_eq _ _).symm
        rw [heq]
        refine le_inf le_rfl ?_
        have : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ≤
            ⨆ (ij : (prod (check PSet.omega) (check y)).type),
            (prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij :=
          hz_in_prod
        exact this
      apply hctx_le.trans
      apply iSup_le; intro ij

      have hstep : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) ≤
          z ∈ᴮ check f' := by
        have hbval : (prod (check PSet.omega) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]
        let i : PSet.omega.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2
        have hfunc : (prod (check PSet.omega) (check y)).func ij =
            pair (check (PSet.omega.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]
        have hpair_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ g)
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hg_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i.down)
        have h_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_g_is_func')
            bv_refl hpair_eq hg_fri
        have hf'_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have hf'_j : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' h_eq (ϕ := fun z => pair (check (PSet.omega.Func i)) z ∈ᴮ check f')
            (h_congr := B_ext_pair_mem_right) (H_new := hf'_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ check f')
          (h_congr := B_ext_mem_left) (H_new := hf'_j)
      exact hstep
  exact ⟨f', ⨅ n, fBᵦ n, Γ'_pos, Γ'_le_Γ, Γ'_le_eq, f'_is_func⟩

end function_reflect

end lemmas

end bSet

namespace collapse_algebra

open bSet Flypitch

noncomputable def 𝔹_collapse : Type u :=
  CollapseAlgebra (pSet_aleph1 : PSet.{u}).Type
    (PSet.powerset PSet.omega : PSet.{u}).Type

private instance : Nonempty (PSet.powerset PSet.omega : PSet.{u}).Type := by
  simp only [PSet.powerset, PSet.Type]; exact ⟨Set.univ⟩

private instance : Nonempty ((pSet_aleph1 : PSet.{u}).Type →
    (PSet.powerset PSet.omega : PSet.{u}).Type) :=
  ⟨fun _ => Classical.arbitrary _⟩

noncomputable instance 𝔹_collapse_ncba :
    NontrivialCompleteBooleanAlgebra 𝔹_collapse :=
  collapseAlgebra_ncba (X := (pSet_aleph1 : PSet.{u}).Type)
    (Y := (PSet.powerset PSet.omega : PSet.{u}).Type)

noncomputable local instance collapseSpaceInstFCH :
    TopologicalSpace ((pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type) :=
  collapseSpace (pSet_aleph1 : PSet.{u}).Type (PSet.powerset PSet.omega : PSet.{u}).Type

lemma nonzero_wit'' {𝓑 : Type*} [NontrivialCompleteBooleanAlgebra 𝓑] {D : Set 𝓑}
    (H_docs : DenseOmegaClosed D) {I : Type*} {s : I → 𝓑} {Γ : 𝓑}
    (H_nonzero : ⊥ < Γ) (H_le : Γ ≤ ⨆ i, s i) :
    ∃ j : I, ∃ Γ' : 𝓑, ⊥ < Γ' ∧ Γ' ≤ s j ⊓ Γ ∧ Γ' ∈ D := by
  obtain ⟨j, Hj⟩ := nonzero_wit' H_nonzero H_le
  rcases H_docs.1 with ⟨_, H_dense₂⟩
  rcases H_dense₂ (s j ⊓ Γ) Hj with ⟨Γ', HΓ'₁, HΓ'₂⟩
  exact ⟨j, Γ', nonzero_of_mem_DenseOmegaClosed H_docs HΓ'₁, HΓ'₂, HΓ'₁⟩

lemma AE_of_check_func_check' (x y : PSet.{u})
    {f : bSet 𝔹_collapse} {Γ : 𝔹_collapse}
    (H : Γ ≤ is_func' (check x) (check y) f)
    (H_nonzero : ⊥ < Γ)
    (i : x.Type) :
    ∃ (j : y.Type) (Γ' : 𝔹_collapse), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      Γ' ≤ is_func' (check x) (check y) f ∧
      Γ' ≤ pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ f ∧
      Γ' ∈ Set.range
        (@collapseInclusion (pSet_aleph1 : PSet.{u}).Type
                           (PSet.powerset PSet.omega : PSet.{u}).Type) := by

  have Htot : Γ ≤ is_total (check x) (check y) f := is_total_of_is_func' H
  have hmem : Γ ≤ (check (x.Func i)) ∈ᴮ check x := by
    simp [check_bval_top]
  have htot_i_raw : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (x.Func i)) w ∈ᴮ f :=
    le_trans (le_inf (le_trans Htot (iInf_le _ (check (x.Func i)))) hmem) bv_imp_elim

  rw [← @bounded_exists 𝔹_collapse _ (check y) (fun w => pair (check (x.Func i)) w ∈ᴮ f)
    (h_congr := B_ext_pair_mem_right)] at htot_i_raw
  simp only [check_bval_top, top_inf_eq] at htot_i_raw

  have H' : Γ ≤ ⨆ (j₀ : (check y).type),
      is_func' (check x) (check y) f ⊓ pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f := by
    calc Γ ≤ is_func' (check x) (check y) f ⊓
              ⨆ j₀, pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f :=
          le_inf H htot_i_raw
      _ = ⨆ j₀, is_func' (check x) (check y) f ⊓
              pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f := inf_iSup_eq _ _
  obtain ⟨j₀, Γ', HΓ'_nonzero, HΓ'_le, HΓ'_mem⟩ := nonzero_wit''
    principalOpens_denseOmegaClosed H_nonzero H'

  refine ⟨check_cast j₀, Γ', HΓ'_nonzero, HΓ'_le.trans inf_le_right,
    HΓ'_le.trans (inf_le_left.trans inf_le_left), ?_, HΓ'_mem⟩

  have h := HΓ'_le.trans (inf_le_left.trans inf_le_right)
  simp only [check_func] at h
  exact h

lemma check_functions_eq_functions (y : PSet.{u}) {Γ : 𝔹_collapse} :
    Γ ≤ check (PSet.functions PSet.omega y) =ᴮ functions bSet.omega (check y) := by

  refine subset_ext check_functions_subset_functions ?_

  rw [subset_unfold']
  apply le_iInf; intro g; rw [← deduction]

  set B := Γ ⊓ g ∈ᴮ functions bSet.omega (check y) with hB
  set A := g ∈ᴮ check (PSet.functions PSet.omega y) with hA

  have hB_open : IsOpen B.val := Flypitch.Regular.isOpen_of_isRegularOpen B.property
  have hA_reg : A.valᵖᵖ = A.val := Flypitch.Regular.isRegularOpen_eq_p_p A.property

  have hRelDense : Flypitch.RelDense B.val A.val := by
    apply Flypitch.rel_dense_of_dense_in_basis B.val A.val collapseSpaceBasis_spec

    intro D HD hDB
    rcases HD with rfl | ⟨p, -, rfl⟩
    ·
      exact absurd hDB (by simp)
    ·
      let P := collapseInclusion p
      have hP_val : P.val = CollapsePoset.principalOpen p := rfl

      have hPB_val : (CollapsePoset.principalOpen p ∩ B.val) = (P ⊓ B).val := by
        simp only [RegularOpens.inf_val, P, collapseInclusion]; rfl
      rw [hPB_val] at hDB

      have hPB_pos : ⊥ < P ⊓ B := RegularOpens.bot_lt_iff.mpr hDB

      have hPB_le_Bg : P ⊓ B ≤ g ∈ᴮ functions bSet.omega (check y) :=
        inf_le_right.trans inf_le_right
      have hPB_func : P ⊓ B ≤ is_function bSet.omega (check y) g :=
        mem_functions_iff.mp hPB_le_Bg
      have hPB_func' : P ⊓ B ≤ is_func' bSet.omega (check y) g :=
        is_func'_of_is_function hPB_func

      obtain ⟨f, Γ', hΓ'_pos, hΓ'_le, hΓ'_eq, hf_func⟩ :=
        function_reflect_of_omega_closed
          principalOpens_denseOmegaClosed hPB_pos hPB_func' hPB_func
          (fun px py {f} {Γ'} hfunc hpos i => AE_of_check_func_check' px py hfunc hpos i)

      have hΓ'_le_A : Γ' ≤ A := by
        rw [hA]
        exact bv_rw' (bv_symm hΓ'_eq)
          (ϕ := fun z => z ∈ᴮ check (PSet.functions PSet.omega y))
          (h_congr := B_ext_mem_left)
          (H_new := check_mem ((PSet.mem_functions_iff f).mpr hf_func))

      obtain ⟨h, hh⟩ := RegularOpens.bot_lt_iff.mp hΓ'_pos

      refine ⟨h, ?_, hΓ'_le_A hh⟩
      rw [Set.mem_inter_iff]
      exact ⟨hP_val ▸ (RegularOpens.le_iff_subset.mp (hΓ'_le.trans inf_le_left) hh),
             RegularOpens.le_iff_subset.mp (hΓ'_le.trans inf_le_right) hh⟩

  have h := Flypitch.RegularOpens.p_p_eq_univ_of_rel_dense_of_open hB_open hRelDense

  rw [hA_reg] at h

  exact Set.inter_eq_left.mp h

noncomputable def π_af :
    (check pSet_aleph1 : bSet 𝔹_collapse).type →
    (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type → 𝔹_collapse :=
  fun η S =>
    let η' : (pSet_aleph1 : PSet.{u}).Type := check_cast η
    let S' : (PSet.powerset PSet.omega : PSet.{u}).Type := check_cast S
    ⟨{g : (pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type |
        g η' = S'},
     by
       haveI : TopologicalSpace
         ((pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type) :=
         collapseSpace _ _
       exact isRegular_setOf⟩

lemma aleph_one_type_uncountable :
    Cardinal.aleph 0 < # (pSet_aleph1 : PSet.{u}).Type := by
  simp [PSet.mk_type_mk_eq''']

lemma π_af_wide :
    ∀ (j : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type),
    (⨆ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type), π_af i j) = (⊤ : 𝔹_collapse) := by
  intro j
  apply RegularOpens.sSup_eq_top_of_dense_Union
  rw [dense'_iff_mathlib, dense_iff_inter_open]
  intro U hU ⟨g, hg⟩
  rcases collapseSpaceBasis_spec.exists_subset_of_mem_open hg hU with ⟨B, HB_basis, HB_mem, HB_sub⟩
  rcases HB_basis with rfl | ⟨p, -, rfl⟩
  · exact absurd HB_mem (by simp)
  ·

    obtain ⟨η', Hη'⟩ := exists_mem_compl_of_mk_lt_mk (PFun.Dom p.f) (by
      calc # (PFun.Dom p.f) < Order.succ (ℵ₀ : Cardinal) := p.Hc
        _ = ℵ₁ := Cardinal.succ_aleph0
        _ = # pSet_aleph1.Type := by
              simp [pSet_aleph1, PSet.mk_type_mk_eq'''])

    let h := CPFun.trivial_extension p.f (check_cast j)
    have Hh_open : h ∈ CollapsePoset.principalOpen p := trivialExtension_mem_principalOpen
    have Hh_val : h η' = check_cast j := CPFun.trivial_extension_neg (Set.mem_compl_iff _ _ |>.mp Hη')
    refine ⟨h, HB_sub Hh_open, ?_⟩
    simp only [Set.mem_sUnion, Set.mem_image, Set.mem_range]
    exact ⟨(π_af (check_cast_symm η') j).val,
      ⟨_, ⟨check_cast_symm η', rfl⟩, rfl⟩,
      by simp [π_af, Hh_val]⟩

lemma π_af_tall :
    ∀ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type),
    (⨆ (j : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type), π_af i j) =
    (⊤ : 𝔹_collapse) := by

  intro i

  apply RegularOpens.sSup_eq_top_of_dense_Union
  rw [dense'_iff_mathlib, dense_iff_inter_open]
  intro U hU ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩

  simp only [Set.mem_sUnion, Set.mem_image, Set.mem_range]

  refine ⟨(π_af i (check_cast_symm (g (check_cast i)))).val,
    ⟨_, ⟨check_cast_symm (g (check_cast i)), rfl⟩, rfl⟩, ?_⟩

  simp [π_af]

lemma π_af_anti :
    ∀ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type)
      (j₁ j₂ : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type),
    j₁ ≠ j₂ → π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ := by

  intro i j₁ j₂ hne

  rw [le_bot_iff]

  apply Subtype.ext

  simp only [RegularOpens.inf_val, RegularOpens.bot_val, π_af]
  apply Set.eq_empty_of_subset_empty
  intro g ⟨h₁, h₂⟩
  simp only [Set.mem_ofPred_eq] at h₁ h₂
  have heq : check_cast j₁ = check_cast j₂ := h₁.symm.trans h₂
  apply hne
  simp only [check_cast, cast_inj] at heq
  exact heq

lemma check_index_inj_of_pSet_index_inj {x : PSet.{u}}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂) :
    ∀ i₁ i₂ : (check x : bSet 𝔹_collapse).type,
    ⊥ < (check x : bSet 𝔹_collapse).func i₁ =ᴮ (check x : bSet 𝔹_collapse).func i₂ → i₁ = i₂ := by

  intro i₁ i₂ H
  by_contra hne
  have hne' : check_cast i₁ ≠ check_cast i₂ := by
    intro h; apply hne; simp only [check_cast, cast_inj] at h; exact h
  have hnotequiv : ¬ PSet.Equiv (x.Func (check_cast i₁)) (x.Func (check_cast i₂)) :=
    fun h => hne' (H_inj (check_cast i₁) (check_cast i₂) h)
  have heq_bot : (check x : bSet 𝔹_collapse).func i₁ =ᴮ (check x : bSet 𝔹_collapse).func i₂ = ⊥ := by
    simp only [check_func]; exact check_bv_eq_bot_of_not_equiv hnotequiv
  rw [heq_bot] at H; exact absurd H (lt_irrefl ⊥)

lemma aleph_one_inj :
    ∀ i₁ i₂ : (check pSet_aleph1 : bSet 𝔹_collapse).type,
    ⊥ < (check pSet_aleph1 : bSet 𝔹_collapse).func i₁ =ᴮ
        (check pSet_aleph1 : bSet 𝔹_collapse).func i₂ → i₁ = i₂ :=
  check_index_inj_of_pSet_index_inj (by

    intro i₁ i₂ H
    by_contra hne
    exact PSet.ordinalMk_inj (Cardinal.aleph 1).ord i₁ i₂ hne H)

noncomputable def π : bSet 𝔹_collapse :=
  rel_of_array (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π_af

lemma π_is_func {Γ : 𝔹_collapse} : Γ ≤ is_func π :=
  rel_of_array_extensional _ _ _ π_af_anti aleph_one_inj

lemma π_is_func' {Γ : 𝔹_collapse} :
    Γ ≤ is_func' (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  rel_of_array_is_func' _ _ _
    (fun _ => check_bval_top _) π_af_tall π_af_anti aleph_one_inj

lemma π_is_functional {Γ : 𝔹_collapse} : Γ ≤ is_functional π :=
  is_functional_of_is_func _ π_is_func

lemma π_is_surj {Γ : 𝔹_collapse} :
    Γ ≤ is_surj (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  rel_of_array_surj _ _ _
    (fun _ => check_bval_top _) (fun _ => check_bval_top _) π_af_wide

lemma π_spec {Γ : 𝔹_collapse} :
    Γ ≤ (is_func π) ⊓
    ⨅ v, v ∈ᴮ (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) ⟹
      (⨆ w, w ∈ᴮ (check pSet_aleph1 : bSet 𝔹_collapse) ⊓ pair w v ∈ᴮ π) :=
  le_inf π_is_func π_is_surj

lemma π_spec' {Γ : 𝔹_collapse} :
    Γ ≤ (is_func' (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π) ⊓
    is_surj (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  le_inf π_is_func' π_is_surj

lemma aleph1_larger_than_continuum {Γ : 𝔹_collapse} :
    Γ ≤ larger_than (check pSet_aleph1) (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) := by
  apply bv_use (check pSet_aleph1)
  apply bv_use π
  rw [inf_assoc]
  exact le_inf subset_self π_spec'

lemma no_pset_surj_omega_aleph_one {h : PSet.{u}}
    (hh_func : PSet.is_func PSet.omega pSet_aleph1 h) :
    ¬ PSet.is_surj PSet.omega pSet_aleph1 h := by
  intro Hsurj
  obtain ⟨hf_sub, hf_uniq⟩ := hh_func
  have hg_exist : ∀ i : PSet.omega.Type, ∃ j : pSet_aleph1.Type,
      ZFSet.pair (ZFSet.mk (PSet.omega.Func i)) (ZFSet.mk (pSet_aleph1.Func j)) ∈ ZFSet.mk h := by
    intro i
    have hi_mem : ZFSet.mk (PSet.omega.Func i) ∈ ZFSet.mk PSet.omega :=
      ZFSet.mk_mem_iff.mpr (PSet.func_mem PSet.omega i)
    obtain ⟨w, hw_pair, _⟩ := hf_uniq _ hi_mem
    have hw_in_aleph1 : w ∈ ZFSet.mk pSet_aleph1 := by
      have h_in_prod := hf_sub hw_pair
      rw [ZFSet.mem_prod] at h_in_prod
      obtain ⟨a, _, b, hb, hab⟩ := h_in_prod
      exact (ZFSet.pair_injective hab).2 ▸ hb
    obtain ⟨j, hj⟩ : ∃ j : pSet_aleph1.Type, ZFSet.mk (pSet_aleph1.Func j) = w := by
      have hwp : w.out ∈ pSet_aleph1 := by
        have : ZFSet.mk w.out ∈ ZFSet.mk pSet_aleph1 := by
          simp [ZFSet.mk_out, hw_in_aleph1]
        exact ZFSet.mk_mem_iff.mp this
      rw [PSet.mem_def] at hwp
      obtain ⟨j, hj⟩ := hwp
      exact ⟨j, (ZFSet.sound hj.symm).trans (ZFSet.mk_out w)⟩
    exact ⟨j, hj ▸ hw_pair⟩
  let G : PSet.omega.Type → pSet_aleph1.Type := fun i => (hg_exist i).choose
  have hG_surj : Function.Surjective G := by
    intro j
    obtain ⟨a, ha_omega, ha_pair⟩ := Hsurj (pSet_aleph1.Func j) (PSet.func_mem pSet_aleph1 j)
    obtain ⟨i, hi⟩ : ∃ i : PSet.omega.Type, PSet.Equiv (PSet.omega.Func i) a := by
      rw [PSet.mem_def] at ha_omega
      obtain ⟨i, hi⟩ := ha_omega
      exact ⟨i, hi.symm⟩
    refine ⟨i, ?_⟩
    have hi_mem : ZFSet.mk (PSet.omega.Func i) ∈ ZFSet.mk PSet.omega :=
      ZFSet.mk_mem_iff.mpr (PSet.func_mem PSet.omega i)
    obtain ⟨_, _, huniq⟩ := hf_uniq _ hi_mem
    have hi_pair_j : ZFSet.pair (ZFSet.mk (PSet.omega.Func i)) (ZFSet.mk (pSet_aleph1.Func j)) ∈
        ZFSet.mk h := by
      rwa [← ZFSet.sound hi] at ha_pair
    have h1 := (hg_exist i).choose_spec
    have heq : ZFSet.mk (pSet_aleph1.Func (G i)) = ZFSet.mk (pSet_aleph1.Func j) :=
      (huniq (ZFSet.mk (pSet_aleph1.Func (G i))) h1).trans
      (huniq (ZFSet.mk (pSet_aleph1.Func j)) hi_pair_j).symm
    by_contra hne
    exact PSet.ordinalMk_inj (Cardinal.aleph 1).ord (G i) j hne (ZFSet.exact heq)
  have hcard_le : #(pSet_aleph1.Type) ≤ #(PSet.omega.Type) :=
    Cardinal.mk_le_of_surjective hG_surj
  rw [@PSet.mk_type_mk_eq'' (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1),
      PSet.mk_omega_eq_mk_omega] at hcard_le
  exact absurd hcard_le (not_le.mpr PSet.omega_lt_aleph_one)

set_option maxHeartbeats 800000 in
lemma surjection_reflect {Γ : 𝔹_collapse} (H_bot_lt : ⊥ < Γ)
    (H_surj : Γ ≤ surjects_onto (bSet.omega : bSet 𝔹_collapse)
                    (check pSet_aleph1 : bSet 𝔹_collapse))
    : ∃ (f : PSet.{u}),
      PSet.is_func PSet.omega (PSet.card_ex (Cardinal.aleph 1)) f ∧
      PSet.is_surj PSet.omega (PSet.card_ex (Cardinal.aleph 1)) f := by
  by_contra H
  simp only [not_exists, not_and_or] at H
  have Hf_ex := exists_surjection_of_surjects_onto H_surj
  obtain ⟨f, Γ_1, hΓ1_pos, hΓ1_le, _hΓ1_mem⟩ :=
    nonzero_wit'' principalOpens_denseOmegaClosed H_bot_lt Hf_ex
  have Hf_left : Γ_1 ≤ is_function bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_left)
  have Hf_right : Γ_1 ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_right)
  have hrefl := function_reflect_of_omega_closed
      principalOpens_denseOmegaClosed hΓ1_pos
      (is_func'_of_is_function Hf_left) Hf_left
      (fun px py {g} {Γ''} hg'' hpos'' i => AE_of_check_func_check' px py hg'' hpos'' i)
  let h := hrefl.choose
  let hΓ' : 𝔹_collapse := hrefl.choose_spec.choose
  let hΓ'_pos : ⊥ < hΓ' := hrefl.choose_spec.choose_spec.1
  let hΓ'_le : hΓ' ≤ Γ_1 := hrefl.choose_spec.choose_spec.2.1
  let hΓ'_eq : hΓ' ≤ check h =ᴮ f := hrefl.choose_spec.choose_spec.2.2.1
  let hh_func : PSet.is_func PSet.omega pSet_aleph1 h := hrefl.choose_spec.choose_spec.2.2.2
  have hh_not_surj : ¬ PSet.is_surj PSet.omega pSet_aleph1 h :=
    no_pset_surj_omega_aleph_one hh_func
  have hΓ'_surj : hΓ' ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ'_le.trans Hf_right
  have B_ext_is_surj_last : B_ext (fun z : bSet 𝔹_collapse =>
      is_surj bSet.omega (check pSet_aleph1) z) :=
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))
  exact false_of_bot_lt_and_le_bot hΓ'_pos
    (check_not_is_surj hh_not_surj
      (bv_rw' hΓ'_eq (ϕ := fun z => is_surj bSet.omega (check pSet_aleph1) z)
        (h_congr := B_ext_is_surj_last) (H_new := hΓ'_surj)))

set_option maxHeartbeats 800000 in
lemma omega_lt_aleph_one_collapse {Γ : 𝔹_collapse} :
    Γ ≤ (larger_than bSet.omega (check pSet_aleph1) : 𝔹_collapse)ᶜ := by

  rw [← imp_bot, ← deduction]
  by_contra H
  have H_pos : ⊥ < Γ ⊓ larger_than bSet.omega (check pSet_aleph1 : bSet 𝔹_collapse) :=
    bot_lt_iff_not_le_bot.mpr H
  have H_surj : Γ ⊓ larger_than bSet.omega (check pSet_aleph1 : bSet 𝔹_collapse) ≤
      surjects_onto bSet.omega (check pSet_aleph1 : bSet 𝔹_collapse) :=
    surjects_onto_of_larger_than_and_exists_mem inf_le_right
      (le_trans inf_le_right aleph_one_check_exists_mem)

  have Hf_ex := exists_surjection_of_surjects_onto H_surj
  obtain ⟨f, Γ_1, hΓ1_pos, hΓ1_le, _hΓ1_mem⟩ :=
    nonzero_wit'' principalOpens_denseOmegaClosed H_pos Hf_ex
  have Hf_left : Γ_1 ≤ is_function bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_left)
  have Hf_right : Γ_1 ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_right)
  have hrefl := function_reflect_of_omega_closed
      principalOpens_denseOmegaClosed hΓ1_pos
      (is_func'_of_is_function Hf_left) Hf_left
      (fun px py {g} {Γ''} hg'' hpos'' i => AE_of_check_func_check' px py hg'' hpos'' i)
  let h := hrefl.choose
  let hΓ' : 𝔹_collapse := hrefl.choose_spec.choose
  let hΓ'_pos : ⊥ < hΓ' := hrefl.choose_spec.choose_spec.1
  let hΓ'_le : hΓ' ≤ Γ_1 := hrefl.choose_spec.choose_spec.2.1
  let hΓ'_eq : hΓ' ≤ check h =ᴮ f := hrefl.choose_spec.choose_spec.2.2.1
  let hh_func : PSet.is_func PSet.omega pSet_aleph1 h := hrefl.choose_spec.choose_spec.2.2.2
  have hh_not_surj : ¬ PSet.is_surj PSet.omega pSet_aleph1 h :=
    no_pset_surj_omega_aleph_one hh_func

  have hΓ'_surj : hΓ' ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ'_le.trans Hf_right
  have B_ext_is_surj_last : B_ext (fun z : bSet 𝔹_collapse =>
      is_surj bSet.omega (check pSet_aleph1) z) :=
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))
  exact false_of_bot_lt_and_le_bot hΓ'_pos
    (check_not_is_surj hh_not_surj
      (bv_rw' hΓ'_eq (ϕ := fun z => is_surj bSet.omega (check pSet_aleph1) z)
        (h_congr := B_ext_is_surj_last) (H_new := hΓ'_surj)))

lemma aleph_one_check_le_of_omega_lt_collapse (Γ : 𝔹_collapse) :
    Γ ≤ le_of_omega_lt (check pSet_aleph1 : bSet 𝔹_collapse) := by

  apply bv_rw' (bSet.aleph_one_check_is_aleph_one_of_omega_lt omega_lt_aleph_one_collapse)
  · exact B_ext_le_of_omega_lt
  · exact aleph_one_le_of_omega_lt

lemma continuum_le_continuum_check {Γ : 𝔹_collapse} :
    Γ ≤ bv_powerset (bSet.omega : bSet 𝔹_collapse) ≼
      (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) := by

  have h_pset_inj := PSet.functions_2_injects_into_powerset PSet.omega
  obtain ⟨f_pset, Hf_pset⟩ := h_pset_inj

  have h1 : Γ ≤ injects_into
      (check (PSet.functions PSet.omega (PSet.ofNat 2)))
      (check (PSet.powerset PSet.omega)) := by
    rw [injects_into_iff_injection_into]
    exact le_trans le_top (le_iSup_of_le (check f_pset) (check_is_injective_function Hf_pset))

  have h2 : Γ ≤ injects_into
      (functions bSet.omega (𝟚 : bSet 𝔹_collapse))
      (check (PSet.powerset PSet.omega)) :=
    bv_rw'' (check_functions_eq_functions (PSet.ofNat 2))
      (H_new := h1) (h_congr := B_ext_injects_into_left)

  exact injects_into_trans (powerset_injects_into_functions bSet.omega) h2

lemma aleph_one_not_lt_powerset_omega :
    ∀ {Γ : 𝔹_collapse},
    Γ ≤ ((check pSet_aleph1 : bSet 𝔹_collapse) ≺ 𝒫 bSet.omega)ᶜ := by
  intro Γ
  simp only [compl_compl]

  rw [← compl_compl (larger_than (check pSet_aleph1) (bv_powerset bSet.omega)),
      ← imp_bot, ← deduction]

  apply bv_absurd (larger_than (check pSet_aleph1) (check (PSet.powerset PSet.omega)))
  · exact le_trans inf_le_left aleph1_larger_than_continuum
  · exact le_trans inf_le_right (bSet_lt_of_lt_of_le le_rfl continuum_le_continuum_check)

theorem CH_true : (⊤ : 𝔹_collapse) ≤ CH :=
  CH_true_aux (𝔹 := 𝔹_collapse)
    (fun {Γ} => aleph_one_check_le_of_omega_lt_collapse Γ)
    (fun {_} => aleph_one_not_lt_powerset_omega)

theorem CH₂_true : (⊤ : 𝔹_collapse) ≤ CH₂ :=
  CH_iff_CH₂.mp CH_true

end collapse_algebra
