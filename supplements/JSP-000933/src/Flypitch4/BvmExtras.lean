/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Modified for Lean and Mathlib 4.36.0.

import Flypitch4.Bvm

open scoped Flypitch
open Lattice

universe u

namespace bSet

section extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

instance singleton_bSet : Singleton (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun x => bSet.insert1 x ∅⟩

@[simp] lemma mem_singleton_bSet {x y : bSet 𝔹} :
    x ∈ᴮ ({y} : bSet 𝔹) = x =ᴮ y ⊔ x ∈ᴮ (∅ : bSet 𝔹) :=
  show x ∈ᴮ bSet.insert1 y ∅ = _ from mem_insert1

@[simp] lemma insert1_bval_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).bval none = ⊤ := rfl

@[simp] lemma insert1_bval_some {u v : bSet 𝔹} {i} :
    (bSet.insert1 u ({v})).bval (some i) = (bval ({v} : bSet 𝔹)) i := rfl

@[simp] lemma insert1_func_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).func none = u := rfl

@[simp] lemma insert1_func_some {u v : bSet 𝔹} {i} :
    (bSet.insert1 u ({v})).func (some i) = (func ({v} : bSet 𝔹)) i := rfl

@[simp] lemma mem_singleton {x : bSet 𝔹} : ⊤ ≤ x ∈ᴮ ({x} : bSet 𝔹) := by
  simp [mem_singleton_bSet, bv_eq_refl]

lemma eq_of_mem_singleton' {x y : bSet 𝔹} : y ∈ᴮ ({x} : bSet 𝔹) ≤ x =ᴮ y := by
  simp only [mem_singleton_bSet]
  exact sup_le (le_of_eq bv_eq_symm) (le_trans (bot_of_mem_empty le_rfl) bot_le)

lemma eq_of_mem_singleton {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ y ∈ᴮ ({x} : bSet 𝔹)) : c ≤ x =ᴮ y :=
  le_trans h eq_of_mem_singleton'

lemma eq_mem_singleton {x y : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ y ∈ᴮ ({x} : bSet 𝔹)) : Γ ≤ y =ᴮ x :=
  le_trans (eq_of_mem_singleton h) (le_of_eq bv_eq_symm)

lemma eq_zero_of_mem_one {x : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ (1 : bSet 𝔹)) : Γ ≤ x =ᴮ 0 := by

  have h_one_eq : (1 : bSet 𝔹) = ({(0 : bSet 𝔹)} : bSet 𝔹) := by
    show of_nat 1 = bSet.insert1 (of_nat 0) ∅
    show check (PSet.ofNat 1) = bSet.insert1 (check (PSet.ofNat 0)) ∅
    simp only [show PSet.ofNat 1 = PSet.insert (PSet.ofNat 0) (PSet.ofNat 0) from rfl]
    rw [check_insert]
    simp only [show PSet.ofNat 0 = (∅ : PSet) from rfl, check_empty_eq_empty]
  rw [h_one_eq] at H_mem
  exact eq_mem_singleton H_mem

lemma mem_singleton_of_eq {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ x =ᴮ y) : c ≤ y ∈ᴮ ({x} : bSet 𝔹) := by
  simp only [mem_singleton_bSet]
  exact le_trans (le_trans h (le_of_eq bv_eq_symm)) le_sup_left

lemma eq_inserted_of_eq_singleton {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ y := by

  have hR : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ y ∈ᴮ ({x} : bSet 𝔹) := by
    have h1 : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤
        ⨅ (a : (bSet.insert1 y ({z} : bSet 𝔹)).type),
          (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
          (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹) := by
      rw [bv_eq_unfold]; exact inf_le_right
    have h2 : (⨅ (a : (bSet.insert1 y ({z} : bSet 𝔹)).type),
          (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
          (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹)) ≤
        y ∈ᴮ ({x} : bSet 𝔹) := by

      have step := iInf_le (f := fun (a : (bSet.insert1 y ({z} : bSet 𝔹)).type) =>
        (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
        (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹)) (none)

      have hbval : (bSet.insert1 y ({z} : bSet 𝔹)).bval (none : (bSet.insert1 y ({z} : bSet 𝔹)).type) = ⊤ := rfl
      have hfunc : (bSet.insert1 y ({z} : bSet 𝔹)).func (none : (bSet.insert1 y ({z} : bSet 𝔹)).type) = y := rfl
      rw [hbval, hfunc, top_imp] at step
      exact step
    exact le_trans h1 h2

  have hmem_R : y ∈ᴮ ({x} : bSet 𝔹) = y =ᴮ x := by
    show y ∈ᴮ insert x (∅ : bSet 𝔹) = _
    rw [mem_insert1]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  rw [hmem_R] at hR

  exact hR.trans (le_of_eq bv_eq_symm)

lemma insert1_symm (y z : bSet 𝔹) : ⊤ ≤ bSet.insert1 y ({z} : bSet 𝔹) =ᴮ bSet.insert1 z ({y} : bSet 𝔹) := by

  have hmem : ∀ (a b w : bSet 𝔹),
      w ∈ᴮ bSet.insert1 a ({b} : bSet 𝔹) = w =ᴮ a ⊔ w =ᴮ b := fun a b w => by
    show w ∈ᴮ insert a ({b} : bSet 𝔹) = _
    rw [mem_insert1]
    have : w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show w =ᴮ a ⊔ w ∈ᴮ insert b (∅ : bSet 𝔹) = _
    rw [mem_insert1, this, sup_bot_eq]
  apply mem_ext
  · apply le_iInf; intro w; rw [← deduction, hmem y z w, hmem z y w, top_inf_eq]
    exact le_of_eq (sup_comm _ _)
  · apply le_iInf; intro w; rw [← deduction, hmem z y w, hmem y z w, top_inf_eq]
    exact le_of_eq (sup_comm _ _)

lemma eq_inserted_of_eq_singleton' {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ z := by

  have step1 : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹)
      ≤ ({x} : bSet 𝔹) =ᴮ bSet.insert1 z ({y} : bSet 𝔹) :=
    le_trans (le_inf le_rfl (le_top.trans (insert1_symm y z))) bv_eq_trans
  exact le_trans step1 eq_inserted_of_eq_singleton

def binary_union (x y : bSet 𝔹) : bSet 𝔹 := bv_union ({x, y} : bSet 𝔹)

def binary_inter (x y : bSet 𝔹) : bSet 𝔹 :=
  ⟨x.type, x.func, fun i => x.bval i ⊓ (x.func i) ∈ᴮ y⟩

scoped infix:81 " ∩ᴮ " => bSet.binary_inter

@[simp] lemma binary_inter_bval {x y : bSet 𝔹} {i : x.type} :
    (x ∩ᴮ y).bval i = x.bval i ⊓ (x.func i) ∈ᴮ y := rfl

@[simp] lemma binary_inter_type {x y : bSet 𝔹} : (x ∩ᴮ y).type = x.type := rfl

@[simp] lemma binary_inter_func {x y : bSet 𝔹} {i} : (x ∩ᴮ y).func i = x.func i := rfl

lemma mem_binary_inter_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ∈ᴮ (x ∩ᴮ y) ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ z ∈ᴮ y) := by

  constructor
  · intro H
    constructor
    ·
      rw [mem_unfold] at H ⊢
      apply le_trans H; apply iSup_le; intro i
      apply le_iSup_of_le i
      simp only [binary_inter_bval, binary_inter_func]
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    ·

      rw [mem_unfold] at H
      apply le_trans H; apply iSup_le; intro i
      simp only [binary_inter_bval, binary_inter_func]

      exact subst_congr_mem_left' (bv_symm inf_le_right) (inf_le_left.trans inf_le_right)
  · intro ⟨H₁, H₂⟩

    rw [mem_unfold] at H₁ ⊢
    calc Γ ≤ (⨆ i : x.type, x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y := le_inf H₁ H₂
      _ ≤ ⨆ i : x.type, (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y := by
              rw [iSup_inf_eq]
      _ ≤ ⨆ i : (x ∩ᴮ y).type, (x ∩ᴮ y).bval i ⊓ z =ᴮ (x ∩ᴮ y).func i := by
              apply iSup_le; intro i; apply le_iSup_of_le i
              simp only [binary_inter_bval, binary_inter_func]

              refine le_inf (le_inf ?_ ?_) ?_
              · exact inf_le_left.trans inf_le_left
              ·

                exact le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
                               subst_congr_mem_left
              · exact inf_le_left.trans inf_le_right

lemma subset_binary_inter_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ⊆ᴮ x ∩ᴮ y ↔ (Γ ≤ z ⊆ᴮ x ∧ Γ ≤ z ⊆ᴮ y) := by
  constructor
  · intro H
    constructor
    ·
      rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
      have hmem : Γ ⊓ w ∈ᴮ z ≤ w ∈ᴮ (x ∩ᴮ y) := mem_of_mem_subset (le_trans inf_le_left H) inf_le_right
      exact (mem_binary_inter_iff.mp hmem).1
    ·
      rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
      have hmem : Γ ⊓ w ∈ᴮ z ≤ w ∈ᴮ (x ∩ᴮ y) := mem_of_mem_subset (le_trans inf_le_left H) inf_le_right
      exact (mem_binary_inter_iff.mp hmem).2
  · intro ⟨H₁, H₂⟩
    rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
    apply mem_binary_inter_iff.mpr
    exact ⟨mem_of_mem_subset (le_trans inf_le_left H₁) inf_le_right, mem_of_mem_subset (le_trans inf_le_left H₂) inf_le_right⟩

lemma binary_inter_symm {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y =ᴮ y ∩ᴮ x := by
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.2, h.1⟩
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (y ∩ᴮ x) ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ (y ∩ᴮ x) ≤ z ∈ᴮ x :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.2, h.1⟩

lemma B_congr_binary_inter_left {y : bSet 𝔹} : B_congr (fun x => x ∩ᴮ y) := by
  intro x₁ x₂ Γ H_eq
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (x₁ ∩ᴮ y) ≤ z ∈ᴮ x₁ ∧ Γ ⊓ z ∈ᴮ (x₁ ∩ᴮ y) ≤ z ∈ᴮ y :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨bv_rw'' (le_trans inf_le_left H_eq) h.1 B_ext_mem_right, h.2⟩
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (x₂ ∩ᴮ y) ≤ z ∈ᴮ x₂ ∧ Γ ⊓ z ∈ᴮ (x₂ ∩ᴮ y) ≤ z ∈ᴮ y :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨bv_rw'' (le_trans inf_le_left (bv_symm H_eq)) h.1 B_ext_mem_right, h.2⟩

lemma B_congr_binary_inter_right {y : bSet 𝔹} : B_congr (fun x => y ∩ᴮ x) := by
  intro x₁ x₂ Γ H_eq
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (y ∩ᴮ x₁) ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ (y ∩ᴮ x₁) ≤ z ∈ᴮ x₁ :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.1, bv_rw'' (le_trans inf_le_left H_eq) h.2 B_ext_mem_right⟩
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (y ∩ᴮ x₂) ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ (y ∩ᴮ x₂) ≤ z ∈ᴮ x₂ :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.1, bv_rw'' (le_trans inf_le_left (bv_symm H_eq)) h.2 B_ext_mem_right⟩

lemma binary_inter_subset_left {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ x := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
    mem_binary_inter_iff.mp inf_le_right
  exact h.1

lemma binary_inter_subset_right {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ y := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
    mem_binary_inter_iff.mp inf_le_right
  exact h.2

lemma unordered_pair_symm (x y : bSet 𝔹) {Γ : 𝔹} : Γ ≤ ({x, y} : bSet 𝔹) =ᴮ {y, x} := by

  have mem_bot : ∀ (w : bSet 𝔹), w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := fun w => by
    rw [mem_unfold]; exact exists_over_empty _
  apply mem_ext
  all_goals {
    apply le_iInf; intro z; rw [← deduction]
    simp only [mem_insert1, mem_singleton_bSet, mem_bot, sup_bot_eq]
    exact le_trans inf_le_right (le_of_eq (sup_comm _ _))
  }

lemma binary_union_symm {x y : bSet 𝔹} {Γ} : Γ ≤ binary_union x y =ᴮ binary_union y x := by
  unfold binary_union
  exact B_congr_bv_union (unordered_pair_symm x y)

@[reducible] def succ (x : bSet 𝔹) := bSet.insert1 x x

@[simp] lemma subset_succ {x : bSet 𝔹} {Γ} : Γ ≤ x ⊆ᴮ (succ x) := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have : z ∈ᴮ x.insert1 x = z =ᴮ x ⊔ z ∈ᴮ x := mem_insert1
  rw [this]; exact le_trans inf_le_right le_sup_right

lemma succ_eq_binary_union {x : bSet 𝔹} {Γ} : Γ ≤ succ x =ᴮ binary_union ({x} : bSet 𝔹) x := by

  have hbu : binary_union ({x} : bSet 𝔹) x = bv_union (insert ({x} : bSet 𝔹) {x}) := rfl
  have hmem_pair : ∀ (y : bSet 𝔹),
      y ∈ᴮ insert ({x} : bSet 𝔹) ({x} : bSet 𝔹) = y =ᴮ ({x} : bSet 𝔹) ⊔ y =ᴮ x := by
    intro y; rw [mem_insert1, mem_singleton_bSet]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have hz : Γ ⊓ z ∈ᴮ succ x ≤ z =ᴮ x ⊔ z ∈ᴮ x := inf_le_right.trans (le_of_eq mem_insert1)
    apply le_trans hz
    rw [show binary_union ({x} : bSet 𝔹) x = bv_union (insert ({x} : bSet 𝔹) ({x} : bSet 𝔹)) from hbu]
    apply sup_le
    · apply (bv_union_spec_split _ z).mpr
      apply le_iSup_of_le ({x} : bSet 𝔹)
      refine le_inf ?_ ?_
      ·
        rw [hmem_pair]; simp [bv_eq_refl]
      ·
        exact mem_singleton_of_eq (le_of_eq bv_eq_symm)
    · apply (bv_union_spec_split _ z).mpr
      apply le_iSup_of_le x
      refine le_inf ?_ le_rfl
      ·
        rw [hmem_pair]; simp [bv_eq_refl]
  · apply le_iInf; intro z; rw [← deduction]
    rw [show z ∈ᴮ succ x = z =ᴮ x ⊔ z ∈ᴮ x from mem_insert1]
    rw [show binary_union ({x} : bSet 𝔹) x = bv_union (insert ({x} : bSet 𝔹) ({x} : bSet 𝔹)) from hbu]
    apply le_trans ((bv_union_spec_split _ z).mp inf_le_right)
    apply iSup_le; intro y
    rw [hmem_pair, inf_sup_right]
    apply sup_le
    ·
      have h1 : y =ᴮ ({x} : bSet 𝔹) ⊓ z ∈ᴮ y ≤ z ∈ᴮ ({x} : bSet 𝔹) :=
        subst_congr_mem_right
      exact le_trans h1 (le_trans (le_trans eq_of_mem_singleton' (le_of_eq bv_eq_symm)) le_sup_left)
    ·
      exact le_trans subst_congr_mem_right le_sup_right

lemma succ_eq_binary_union' {x : bSet 𝔹} {Γ} : Γ ≤ succ x =ᴮ binary_union x ({x} : bSet 𝔹) :=
  bv_trans succ_eq_binary_union binary_union_symm

@[reducible] def pair (x y : bSet 𝔹) : bSet 𝔹 := ({{x}, {x, y}} : bSet 𝔹)

@[simp] lemma subst_congr_pair_left {x z y : bSet 𝔹} : x =ᴮ z ≤ pair x y =ᴮ pair z y := by
  unfold pair

  exact bv_trans
    (subst_congr_insert1_left' (subst_congr_insert1_left (v := (∅ : bSet 𝔹))))
    (subst_congr_insert1_left'' subst_congr_insert1_left)

@[simp] lemma subst_congr_pair_left' {x z y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x =ᴮ z → Γ ≤ pair x y =ᴮ pair z y :=
  poset_yoneda_inv Γ subst_congr_pair_left

lemma subst_congr_pair_right {x y z : bSet 𝔹} : y =ᴮ z ≤ pair x y =ᴮ pair x z := by
  unfold pair

  exact subst_congr_insert1_left'' (subst_congr_insert1_left'' (le_refl _))

lemma subst_congr_pair_right' {Γ} {x y z : bSet 𝔹} (H : Γ ≤ y =ᴮ z) :
    Γ ≤ pair x y =ᴮ pair x z :=
  poset_yoneda_inv Γ subst_congr_pair_right H

lemma pair_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ x₁ =ᴮ y₁) (H₂ : Γ ≤ x₂ =ᴮ y₂) :
    Γ ≤ pair x₁ x₂ =ᴮ pair y₁ y₂ :=
  bv_trans (subst_congr_pair_left' H₁) (subst_congr_pair_right' H₂)

@[simp] lemma B_congr_insert1_left {y : bSet 𝔹} : B_congr (fun x => bSet.insert1 x y) :=
  fun h => poset_yoneda_inv _ subst_congr_insert1_left h

@[simp] lemma B_congr_insert1_right {y : bSet 𝔹} : B_congr (fun x => bSet.insert1 y x) :=
  fun h => poset_yoneda_inv _ subst_congr_insert1_right h

@[simp] lemma B_congr_succ : B_congr (succ : bSet 𝔹 → bSet 𝔹) := by
  intro x y Γ h_eq; unfold succ
  exact bv_trans (B_congr_insert1_right h_eq) (B_congr_insert1_left h_eq)

@[simp] lemma B_congr_pair_left {y : bSet 𝔹} : B_congr (fun x => pair x y) :=
  fun h => poset_yoneda_inv _ subst_congr_pair_left h

@[simp] lemma B_congr_pair_right {y : bSet 𝔹} : B_congr (fun x => pair y x) :=
  fun h => poset_yoneda_inv _ subst_congr_pair_right h

@[simp] lemma B_ext_pair_left {ϕ : bSet 𝔹 → 𝔹} (H : B_ext ϕ) {x} :
    B_ext (fun z => ϕ (pair z x)) := B_ext_term ϕ (fun z => pair z x) H B_congr_pair_left

@[simp] lemma B_ext_pair_right {ϕ : bSet 𝔹 → 𝔹} (H : B_ext ϕ) {x} :
    B_ext (fun z => ϕ (pair x z)) := B_ext_term ϕ (fun z => pair x z) H B_congr_pair_right

@[simp] lemma B_ext_pair_mem_left {x y : bSet 𝔹} : B_ext (fun z => pair z x ∈ᴮ y) :=
  B_ext_term (fun w => w ∈ᴮ y) (fun z => pair z x) B_ext_mem_left B_congr_pair_left

@[simp] lemma B_ext_pair_mem_right {x y : bSet 𝔹} : B_ext (fun z => pair x z ∈ᴮ y) :=
  B_ext_term (fun w => w ∈ᴮ y) (fun z => pair x z) B_ext_mem_left B_congr_pair_right

lemma eq_of_eq_pair'_left {x z y : bSet 𝔹} : pair x y =ᴮ pair z y ≤ x =ᴮ z := by

  have hL : pair x y =ᴮ pair z y ≤ ({x} : bSet 𝔹) ∈ᴮ pair z y := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (none : (pair x y).type)

    simp only [show (pair x y).bval (none : (pair x y).type) = ⊤ from rfl,
               show (pair x y).func (none : (pair x y).type) = ({x} : bSet 𝔹) from rfl,
               top_imp, le_refl]

  have hmem : ({x} : bSet 𝔹) ∈ᴮ pair z y = ({x} : bSet 𝔹) =ᴮ ({z} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) =ᴮ ({z, y} : bSet 𝔹) := by
    show ({x} : bSet 𝔹) ∈ᴮ insert ({z} : bSet 𝔹) (insert ({z, y} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({x} : bSet 𝔹) =ᴮ ({z} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) ∈ᴮ insert ({z, y} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem] at hL

  calc pair x y =ᴮ pair z y
      ≤ ({x} : bSet 𝔹) =ᴮ ({z} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) =ᴮ ({z, y} : bSet 𝔹) := hL
    _ ≤ x =ᴮ z := by
          apply sup_le
          · exact eq_of_eq_singleton le_rfl
          · exact eq_inserted_of_eq_singleton

lemma inserted_eq_of_insert_eq {y v w : bSet 𝔹} :
    ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ y =ᴮ w := by

  have hL : ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ y ∈ᴮ ({v, w} : bSet 𝔹) := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : ({v, y} : bSet 𝔹).type)

    show (⊤ : 𝔹) ⟹ y ∈ᴮ ({v, w} : bSet 𝔹) ≤ y ∈ᴮ ({v, w} : bSet 𝔹)
    rw [top_imp]
  have hR : ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ w ∈ᴮ ({v, y} : bSet 𝔹) := by
    rw [bv_eq_unfold]
    apply inf_le_right.trans
    apply iInf_le_of_le (some none : ({v, w} : bSet 𝔹).type)
    show (⊤ : 𝔹) ⟹ w ∈ᴮ ({v, y} : bSet 𝔹) ≤ w ∈ᴮ ({v, y} : bSet 𝔹)
    rw [top_imp]

  have hmem_yw : y ∈ᴮ ({v, w} : bSet 𝔹) = y =ᴮ v ⊔ y =ᴮ w := by
    show y ∈ᴮ insert v ({w} : bSet 𝔹) = _
    rw [mem_insert1, mem_singleton_bSet]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]

  have hmem_wvy : w ∈ᴮ ({v, y} : bSet 𝔹) = w =ᴮ v ⊔ w =ᴮ y := by
    show w ∈ᴮ insert v ({y} : bSet 𝔹) = _
    rw [mem_insert1, mem_singleton_bSet]
    have : w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  rw [hmem_yw] at hL; rw [hmem_wvy] at hR
  calc ({v, y} : bSet 𝔹) =ᴮ {v, w}
      ≤ (y =ᴮ v ⊔ y =ᴮ w) ⊓ (w =ᴮ v ⊔ w =ᴮ y) := le_inf hL hR
    _ ≤ y =ᴮ w := by

          have step : (y =ᴮ v ⊔ y =ᴮ w) ⊓ (w =ᴮ v ⊔ w =ᴮ y)
              ≤ (y =ᴮ v ⊓ (w =ᴮ v ⊔ w =ᴮ y)) ⊔ (y =ᴮ w ⊓ (w =ᴮ v ⊔ w =ᴮ y)) :=
            le_of_eq (inf_sup_right _ _ _)
          apply le_trans step
          apply sup_le
          ·
            have step2 : y =ᴮ v ⊓ (w =ᴮ v ⊔ w =ᴮ y)
                ≤ (y =ᴮ v ⊓ w =ᴮ v) ⊔ (y =ᴮ v ⊓ w =ᴮ y) :=
              le_of_eq (inf_sup_left _ _ _)
            apply le_trans step2
            apply sup_le
            ·
              rw [inf_comm]
              exact le_trans (inf_le_inf_left _ (le_of_eq bv_eq_symm))
                (le_trans bv_eq_trans (le_of_eq bv_eq_symm))
            ·
              exact inf_le_right.trans (le_of_eq bv_eq_symm)
          · exact inf_le_left

lemma eq_of_eq_pair'_right {x z y : bSet 𝔹} : pair y x =ᴮ pair y z ≤ x =ᴮ z := by

  have pair_eq_sing_le : ∀ (u v : bSet 𝔹), (insert v ({u} : bSet 𝔹) : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ≤ u =ᴮ v := by
    intro u v

    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : (insert v ({u} : bSet 𝔹) : bSet 𝔹).type)

    conv_lhs =>
      rw [show ({v, u} : bSet 𝔹).bval (some none : ({v, u} : bSet 𝔹).type) = ⊤ from by
        show (bSet.insert1 v ({u} : bSet 𝔹)).bval (some none) = ⊤
        rw [insert1_bval_some]; exact singleton_bval_none]
      rw [show ({v, u} : bSet 𝔹).func (some none : ({v, u} : bSet 𝔹).type) = u from by
        show (bSet.insert1 v ({u} : bSet 𝔹)).func (some none) = u
        rw [insert1_func_some]; rfl]
    rw [top_imp]
    exact le_trans eq_of_mem_singleton' (le_of_eq bv_eq_symm)

  have hL : pair y x =ᴮ pair y z ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y z := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : (pair y x).type)
    show (⊤ : 𝔹) ⟹ ({y, x} : bSet 𝔹) ∈ᴮ pair y z ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y z
    rw [top_imp]
  have hR : pair y x =ᴮ pair y z ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y x := by
    rw [bv_eq_unfold]
    apply inf_le_right.trans
    apply iInf_le_of_le (some none : (pair y z).type)
    show (⊤ : 𝔹) ⟹ ({y, z} : bSet 𝔹) ∈ᴮ pair y x ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y x
    rw [top_imp]

  have hmem_yz : ({y, x} : bSet 𝔹) ∈ᴮ pair y z = ({y, x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, x} : bSet 𝔹) =ᴮ ({y, z} : bSet 𝔹) := by
    show ({y, x} : bSet 𝔹) ∈ᴮ insert ({y} : bSet 𝔹) (insert ({y, z} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({y, x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({y, x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, x} : bSet 𝔹) ∈ᴮ insert ({y, z} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  have hmem_yx : ({y, z} : bSet 𝔹) ∈ᴮ pair y x = ({y, z} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, z} : bSet 𝔹) =ᴮ ({y, x} : bSet 𝔹) := by
    show ({y, z} : bSet 𝔹) ∈ᴮ insert ({y} : bSet 𝔹) (insert ({y, x} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({y, z} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({y, z} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, z} : bSet 𝔹) ∈ᴮ insert ({y, x} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem_yz] at hL; rw [hmem_yx] at hR

  calc pair y x =ᴮ pair y z
      ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊔ ({y, x} : bSet 𝔹) =ᴮ {y, z}) ⊓
        (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x}) := le_inf hL hR
    _ ≤ x =ᴮ z := by

          have step : (({y, x} : bSet 𝔹) =ᴮ {y} ⊔ ({y, x} : bSet 𝔹) =ᴮ {y, z}) ⊓
              (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})
              ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})) ⊔
                (({y, x} : bSet 𝔹) =ᴮ {y, z} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})) :=
            le_of_eq (inf_sup_right _ _ _)
          apply le_trans step
          apply sup_le
          ·
            have step2 : ({y, x} : bSet 𝔹) =ᴮ {y} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})
                ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y}) ⊔
                  (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y, x}) :=
              le_of_eq (inf_sup_left _ _ _)
            apply le_trans step2
            apply sup_le
            ·
              have hxy := pair_eq_sing_le x y
              have hzy := pair_eq_sing_le z y
              calc ({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y}
                  ≤ x =ᴮ y ⊓ z =ᴮ y := le_inf (inf_le_left.trans hxy) (inf_le_right.trans hzy)
                _ ≤ x =ᴮ z := by
                    rw [inf_comm]
                    exact le_trans (inf_le_inf_left _ (le_of_eq bv_eq_symm))
                      (le_trans bv_eq_trans (le_of_eq bv_eq_symm))
            ·
              have hzx : ({y, z} : bSet 𝔹) =ᴮ {y, x} ≤ z =ᴮ x := inserted_eq_of_insert_eq
              exact inf_le_right.trans (hzx.trans (le_of_eq bv_eq_symm))
          ·
            exact inf_le_left.trans inserted_eq_of_insert_eq

theorem eq_of_eq_pair_left {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ x =ᴮ v := by

  have hL : pair x y =ᴮ pair v w ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (none : (pair x y).type)
    show (⊤ : 𝔹) ⟹ ({x} : bSet 𝔹) ∈ᴮ pair v w ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w
    rw [top_imp]
  have hmem : ({x} : bSet 𝔹) ∈ᴮ pair v w = ({x} : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) =ᴮ ({v, w} : bSet 𝔹) := by
    show ({x} : bSet 𝔹) ∈ᴮ insert ({v} : bSet 𝔹) (insert ({v, w} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({x} : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) ∈ᴮ insert ({v, w} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem] at hL
  exact hL.trans (sup_le (eq_of_eq_singleton le_rfl) eq_inserted_of_eq_singleton)

lemma eq_of_eq_pair_left' {x y v w : bSet 𝔹} {Γ} :
    Γ ≤ pair x y =ᴮ pair v w → Γ ≤ x =ᴮ v :=
  poset_yoneda_inv Γ eq_of_eq_pair_left

theorem eq_of_eq_pair_right {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ y =ᴮ w := by

  calc pair x y =ᴮ pair v w
      ≤ pair v y =ᴮ pair v w := by

          have hxv : pair x y =ᴮ pair v w ≤ x =ᴮ v := eq_of_eq_pair_left
          have hpair : pair x y =ᴮ pair v w ≤ pair x y =ᴮ pair v y := by

            exact le_trans hxv (le_trans (le_of_eq bv_eq_symm)
              (le_trans subst_congr_pair_left (le_of_eq bv_eq_symm)))

          apply le_trans (le_inf (le_trans hpair (le_of_eq bv_eq_symm)) le_rfl)
          exact bv_eq_trans
    _ ≤ y =ᴮ w := eq_of_eq_pair'_right

lemma eq_of_eq_pair_right' {x y v w : bSet 𝔹} {Γ} :
    Γ ≤ pair x y =ᴮ pair v w → Γ ≤ y =ᴮ w :=
  poset_yoneda_inv Γ eq_of_eq_pair_right

lemma eq_of_eq_pair {x y z w : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ pair x y =ᴮ pair z w) :
    Γ ≤ x =ᴮ z ∧ Γ ≤ y =ᴮ w :=
  ⟨eq_of_eq_pair_left' H_eq, eq_of_eq_pair_right' H_eq⟩

lemma pair_eq_pair_iff {x y x' y' : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y =ᴮ pair x' y' ↔ Γ ≤ x =ᴮ x' ∧ Γ ≤ y =ᴮ y' :=
  ⟨fun h => eq_of_eq_pair h, fun ⟨h₁, h₂⟩ => pair_congr h₁ h₂⟩

@[reducible] def prod (v w : bSet 𝔹) : bSet 𝔹 :=
  ⟨v.type × w.type, fun a => pair (v.func a.1) (w.func a.2), fun a => v.bval a.1 ⊓ w.bval a.2⟩

@[simp] lemma prod_type {v w : bSet 𝔹} : (prod v w).type = (v.type × w.type) := rfl

@[simp] lemma prod_func {v w : bSet 𝔹} {pr} :
    (prod v w).func pr = pair (v.func pr.1) (w.func pr.2) := rfl

@[simp] lemma prod_bval {v w : bSet 𝔹} {a b} :
    (prod v w).bval (a, b) = v.bval a ⊓ w.bval b := rfl

@[simp] lemma prod_type_forall {v w : bSet 𝔹} {ϕ : (prod v w).type → 𝔹} :
    (⨅ (z : (prod v w).type), ϕ z) = ⨅ (z : v.type × w.type), ϕ z := rfl

@[simp] lemma prod_check_bval {x y : PSet.{u}} {pr} :
    (prod (check x) (check y) : bSet 𝔹).bval pr = ⊤ := by
  cases pr; simp only [prod_bval, check_bval_top, top_inf_eq]

lemma prod_mem_old {v w x y : bSet 𝔹} :
    x ∈ᴮ v ⊓ y ∈ᴮ w ≤ pair x y ∈ᴮ prod v w := by

  rw [mem_unfold, mem_unfold, mem_unfold]

  rw [iSup_inf_iSup]
  apply iSup_le; intro ⟨i, j⟩

  apply le_iSup_of_le (i, j)
  simp only [prod_bval, prod_func]

  refine le_inf (le_inf ?_ ?_) ?_
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right.trans inf_le_left
  ·
    have hx : (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ x =ᴮ v.func i :=
      inf_le_left.trans inf_le_right
    have hy : (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ y =ᴮ w.func j :=
      inf_le_right.trans inf_le_right
    exact pair_congr hx hy

lemma prod_mem {v w x y : bSet 𝔹} {Γ} : Γ ≤ x ∈ᴮ v → Γ ≤ y ∈ᴮ w → Γ ≤ pair x y ∈ᴮ prod v w :=
  fun H₁ H₂ => le_trans (le_inf H₁ H₂) prod_mem_old

lemma mem_left_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ x ∈ᴮ v := by
  intro H

  rw [mem_unfold] at H

  rw [mem_unfold]

  apply le_trans H
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le i
  simp only [prod_bval, prod_func]

  refine le_inf (inf_le_left.trans inf_le_left) ?_

  exact inf_le_right.trans eq_of_eq_pair_left

lemma mem_right_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ y ∈ᴮ w := by
  intro H
  rw [mem_unfold] at H
  rw [mem_unfold]
  apply le_trans H
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le j
  simp only [prod_bval, prod_func]
  refine le_inf (inf_le_left.trans inf_le_right) ?_
  exact inf_le_right.trans eq_of_eq_pair_right

@[simp] lemma mem_prod_iff {v w x y : bSet 𝔹} {Γ} :
    Γ ≤ pair x y ∈ᴮ prod v w ↔ (Γ ≤ x ∈ᴮ v ∧ Γ ≤ y ∈ᴮ w) :=
  ⟨fun h => ⟨mem_left_of_prod_mem h, mem_right_of_prod_mem h⟩, fun ⟨h₁, h₂⟩ => prod_mem h₁ h₂⟩

@[simp] lemma mem_prod {v w x y : bSet 𝔹} {Γ} (H_mem₁ : Γ ≤ x ∈ᴮ v) (H_mem₂ : Γ ≤ y ∈ᴮ w) :
    Γ ≤ pair x y ∈ᴮ prod v w :=
  mem_prod_iff.mpr ⟨H_mem₁, H_mem₂⟩

@[simp] lemma B_congr_prod_left {y : bSet 𝔹} : B_congr (fun x => prod x y) := by
  intro a b Γ H_eq
  rw [bv_eq_unfold]
  simp only [prod_type, prod_bval, prod_func]

  refine le_inf (le_iInf fun ⟨i, j⟩ => ?_) (le_iInf fun ⟨i, j⟩ => ?_)
  ·
    rw [← deduction]

    have hai : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ a.func i ∈ᴮ a :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' a i))
    have hab : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ a.func i ∈ᴮ b :=
      bv_rw' (bv_symm (le_trans inf_le_left H_eq)) (ϕ := fun z => a.func i ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hai)
    have hyj : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ y.func j ∈ᴮ y :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' y j))
    exact prod_mem hab hyj
  ·
    rw [← deduction]

    have hbi : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ b.func i ∈ᴮ b :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' b i))
    have hba : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ b.func i ∈ᴮ a :=
      bv_rw' (le_trans inf_le_left H_eq) (ϕ := fun z => b.func i ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hbi)
    have hyj : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ y.func j ∈ᴮ y :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' y j))
    exact prod_mem hba hyj

@[simp] lemma B_congr_prod_right {x : bSet 𝔹} : B_congr (fun y => prod x y) := by
  intro a b Γ H_eq
  rw [bv_eq_unfold]
  simp only [prod_type, prod_bval, prod_func]
  refine le_inf (le_iInf fun ⟨i, j⟩ => ?_) (le_iInf fun ⟨i, j⟩ => ?_)
  ·
    rw [← deduction]
    have hxi : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' x i))
    have haj : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ a.func j ∈ᴮ a :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' a j))
    have hab : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ a.func j ∈ᴮ b :=
      bv_rw' (bv_symm (le_trans inf_le_left H_eq)) (ϕ := fun z => a.func j ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := haj)
    exact prod_mem hxi hab
  ·
    rw [← deduction]
    have hxi : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' x i))
    have hbj : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ b.func j ∈ᴮ b :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' b j))
    have hba : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ b.func j ∈ᴮ a :=
      bv_rw' (le_trans inf_le_left H_eq) (ϕ := fun z => b.func j ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hbj)
    exact prod_mem hxi hba

lemma prod_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ} (H₁ : Γ ≤ x₁ =ᴮ x₂) (H₂ : Γ ≤ y₁ =ᴮ y₂) :
    Γ ≤ prod x₁ y₁ =ᴮ prod x₂ y₂ :=
  bv_trans (B_congr_prod_left H₁) (B_congr_prod_right H₂)

lemma mem_prod_iff₂ {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ∈ᴮ prod x y ↔
    ∃ v, ∃ _hv : Γ ≤ v ∈ᴮ x, ∃ w, ∃ _hw : Γ ≤ w ∈ᴮ y, Γ ≤ z =ᴮ pair v w := by
  constructor
  · intro H

    have H_iSup : Γ ≤ ⨆ v : bSet 𝔹, v ∈ᴮ x ⊓ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ z =ᴮ pair v w := by
      rw [mem_unfold] at H
      apply H.trans; apply iSup_le; intro ⟨i, j⟩
      simp only [prod_func, prod_bval]

      apply le_iSup_of_le (x.func i)
      apply le_inf
      ·
        exact (inf_le_left.trans inf_le_left).trans (mem_mk' x i)
      · apply le_iSup_of_le (y.func j)
        apply le_inf
        ·
          exact (inf_le_left.trans inf_le_right).trans (mem_mk' y j)
        ·
          exact inf_le_right

    have B_outer : B_ext (fun v => v ∈ᴮ x ⊓ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ z =ᴮ pair v w) :=
      B_ext_inf B_ext_mem_left (B_ext_iSup (h := fun w =>
        B_ext_inf B_ext_const
          (B_ext_term (fun p => z =ᴮ p) (fun v => pair v w)
            B_ext_bv_eq_right (fun {_ _ _} h => pair_congr h bv_refl))))

    have B_inner (v : bSet 𝔹) : B_ext (fun w => w ∈ᴮ y ⊓ z =ᴮ pair v w) :=
      B_ext_inf B_ext_mem_left
        (B_ext_term (fun p => z =ᴮ p) (fun w => pair v w)
          B_ext_bv_eq_right (fun {_ _ _} h => pair_congr bv_refl h))
    obtain ⟨v, Hv⟩ := exists_convert H_iSup B_outer
    obtain ⟨w, Hw⟩ := exists_convert (Hv.trans inf_le_right) (B_inner v)
    exact ⟨v, Hv.trans inf_le_left, w, Hw.trans inf_le_left, Hw.trans inf_le_right⟩
  · intro ⟨v, Hv, w, Hw, H_eq⟩

    exact subst_congr_mem_left' (bv_symm H_eq) (prod_mem Hv Hw)

lemma prod_ext {S₁ S₂ x y : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ S₁ ⊆ᴮ prod x y) (H₂ : Γ ≤ S₂ ⊆ᴮ prod x y)
    (H_prod_ext : Γ ≤ ⨅ v, v ∈ᴮ x ⟹ ⨅ w, w ∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂)) :
    Γ ≤ S₁ =ᴮ S₂ := by

  apply mem_ext
  ·
    apply le_iInf; intro z; rw [← deduction]

    have Hz_prod : Γ ⊓ z ∈ᴮ S₁ ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (inf_le_left.trans H₁) inf_le_right
    obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp Hz_prod

    have H_spec₁ : Γ ⊓ z ∈ᴮ S₁ ≤ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) := by
      have h1 : Γ ⊓ z ∈ᴮ S₁ ≤ v ∈ᴮ x ⟹ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        (inf_le_left.trans H_prod_ext).trans (iInf_le _ v)
      have h2 : Γ ⊓ z ∈ᴮ S₁ ≤ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        le_trans (le_inf h1 Hv) bv_imp_elim
      have h3 : Γ ⊓ z ∈ᴮ S₁ ≤ w ∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) :=
        h2.trans (iInf_le _ w)
      exact le_trans (le_inf h3 Hw) bv_imp_elim

    have Hvw_S₁ : Γ ⊓ z ∈ᴮ S₁ ≤ pair v w ∈ᴮ S₁ := subst_congr_mem_left' H_eq inf_le_right

    have Hvw_S₂ : Γ ⊓ z ∈ᴮ S₁ ≤ pair v w ∈ᴮ S₂ :=
      le_trans (le_inf (H_spec₁.trans inf_le_left) Hvw_S₁) bv_imp_elim
    exact subst_congr_mem_left' (bv_symm H_eq) Hvw_S₂
  ·
    apply le_iInf; intro z; rw [← deduction]
    have Hz_prod : Γ ⊓ z ∈ᴮ S₂ ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (inf_le_left.trans H₂) inf_le_right
    obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp Hz_prod
    have H_spec₂ : Γ ⊓ z ∈ᴮ S₂ ≤ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) := by
      have h1 : Γ ⊓ z ∈ᴮ S₂ ≤ v ∈ᴮ x ⟹ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        (inf_le_left.trans H_prod_ext).trans (iInf_le _ v)
      have h2 : Γ ⊓ z ∈ᴮ S₂ ≤ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        le_trans (le_inf h1 Hv) bv_imp_elim
      have h3 : Γ ⊓ z ∈ᴮ S₂ ≤ w ∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) :=
        h2.trans (iInf_le _ w)
      exact le_trans (le_inf h3 Hw) bv_imp_elim
    have Hvw_S₂ : Γ ⊓ z ∈ᴮ S₂ ≤ pair v w ∈ᴮ S₂ := subst_congr_mem_left' H_eq inf_le_right
    have Hvw_S₁ : Γ ⊓ z ∈ᴮ S₂ ≤ pair v w ∈ᴮ S₁ :=
      le_trans (le_inf (H_spec₂.trans inf_le_right) Hvw_S₂) bv_imp_elim
    exact subst_congr_mem_left' (bv_symm H_eq) Hvw_S₁

@[simp] lemma check_singleton {x : PSet.{u}} {Γ : 𝔹} :
    Γ ≤ check ({x} : PSet) =ᴮ ({check x} : bSet 𝔹) := by
  have h : check ({x} : PSet) = ({check x} : bSet 𝔹) := by
    show check (PSet.insert x ∅) = bSet.insert1 (check x) ∅
    rw [check_insert]; simp [check_empty_eq_empty]
  rw [h]; exact bv_refl

@[simp] lemma check_unordered_pair {x y : PSet.{u}} {Γ} :
    Γ ≤ check ({x, y} : PSet) =ᴮ ({check x, check y} : bSet 𝔹) := by
  have h : check ({x, y} : PSet) = ({check x, check y} : bSet 𝔹) := by
    show check (PSet.insert x (PSet.insert y ∅)) = bSet.insert1 (check x) (bSet.insert1 (check y) ∅)
    rw [check_insert, check_insert]; simp [check_empty_eq_empty]
  rw [h]; exact bv_refl

@[simp] lemma eq_unordered_pair_of_eq {a b c d : bSet 𝔹} {Γ} (H₁ : Γ ≤ a =ᴮ c)
    (H₂ : Γ ≤ b =ᴮ d) : Γ ≤ ({a, b} : bSet 𝔹) =ᴮ {c, d} :=
  bv_trans (subst_congr_insert1_left' H₁) (subst_congr_insert1_left'' H₂)

lemma check_pset_pair {x y : PSet.{u}} {Γ} :
    Γ ≤ check (PSet.pSet_pair x y) =ᴮ pair (check x) (check y : bSet 𝔹) := by
  have h : check (PSet.pSet_pair x y) = pair (check x) (check y : bSet 𝔹) := by
    show check (PSet.insert (PSet.insert x ∅) (PSet.insert (PSet.insert x (PSet.insert y ∅)) ∅)) =
      bSet.insert1 (bSet.insert1 (check x) ∅)
        (bSet.insert1 (bSet.insert1 (check x) (bSet.insert1 (check y) ∅)) ∅)
    rw [check_insert, check_insert, check_insert, check_insert]
    simp [check_empty_eq_empty]
  rw [h]; exact bv_refl

private lemma check_pset_pair_eq {x y : PSet.{u}} :
    (check (PSet.pSet_pair x y) : bSet 𝔹) = pair (check x) (check y) := by
  show check (PSet.insert (PSet.insert x ∅) (PSet.insert (PSet.insert x (PSet.insert y ∅)) ∅)) =
    bSet.insert1 (bSet.insert1 (check x) ∅)
      (bSet.insert1 (bSet.insert1 (check x) (bSet.insert1 (check y) ∅)) ∅)
  rw [check_insert, check_insert, check_insert, check_insert]
  simp [check_empty_eq_empty]

lemma check_pset_prod {x y : PSet.{u}} {Γ : 𝔹} :
    Γ ≤ check (PSet.pSet_prod x y) =ᴮ prod (check x) (check y) := by
  cases x with | mk xα xA =>
  cases y with | mk yα yA =>

  have h : (check (PSet.pSet_prod (PSet.mk xα xA) (PSet.mk yα yA)) : bSet 𝔹) =
      prod (check (PSet.mk xα xA)) (check (PSet.mk yα yA)) := by
    simp only [PSet.pSet_prod, check, prod]
    congr 1
    · funext ij
      exact check_pset_pair_eq
    · funext ij
      simp [top_inf_eq]
  rw [h]; exact bv_refl

@[reducible] def is_func (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅ w₂, ⨅ v₁, ⨅ v₂, pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)

@[simp] lemma is_func_subset_of_is_func {f g : bSet 𝔹} {Γ} (H : Γ ≤ is_func f)
    (H_sub : Γ ≤ g ⊆ᴮ f) : Γ ≤ is_func g := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]

  have hspec : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤
      pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂) :=
    le_trans (le_trans inf_le_left H)
      (iInf_le _ w₁ |>.trans (iInf_le _ w₂) |>.trans (iInf_le _ v₁) |>.trans (iInf_le _ v₂))
  have hmem₁ : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤ pair w₁ v₁ ∈ᴮ f :=
    mem_of_mem_subset (le_trans inf_le_left H_sub) (inf_le_right.trans inf_le_left)
  have hmem₂ : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤ pair w₂ v₂ ∈ᴮ f :=
    mem_of_mem_subset (le_trans inf_le_left H_sub) (inf_le_right.trans inf_le_right)
  exact le_trans (le_inf hspec (le_inf hmem₁ hmem₂)) bv_imp_elim

@[reducible] def is_functional (f : bSet 𝔹) : 𝔹 :=
  ⨅ z, (⨆ w, pair z w ∈ᴮ f) ⟹ (⨆ w', ⨅ w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w'')

lemma is_functional_of_is_func (f : bSet 𝔹) {Γ} (H : Γ ≤ is_func f) : Γ ≤ is_functional f := by
  unfold is_functional
  apply le_iInf; intro z; rw [← deduction]

  rw [inf_comm]
  calc (⨆ w, pair z w ∈ᴮ f) ⊓ Γ
      ≤ ⨆ w, pair z w ∈ᴮ f ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ w', ⨅ w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w'' := by
        apply iSup_le; intro w
        apply le_iSup_of_le w
        apply le_iInf; intro w'; rw [← deduction]

        have hspec : pair z w ∈ᴮ f ⊓ Γ ⊓ pair z w' ∈ᴮ f ≤
            pair z w ∈ᴮ f ⊓ pair z w' ∈ᴮ f ⟹ (z =ᴮ z ⟹ w =ᴮ w') :=
          le_trans (le_trans (inf_le_left.trans inf_le_right) H)
            (iInf_le _ z |>.trans (iInf_le _ z) |>.trans (iInf_le _ w) |>.trans (iInf_le _ w'))
        have hmem : pair z w ∈ᴮ f ⊓ Γ ⊓ pair z w' ∈ᴮ f ≤ pair z w ∈ᴮ f ⊓ pair z w' ∈ᴮ f :=
          le_inf (inf_le_left.trans inf_le_left) inf_le_right
        exact le_trans (le_inf (le_trans (le_inf hspec hmem) bv_imp_elim) bv_refl) bv_imp_elim

@[reducible] def is_total (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, w₁ ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f

@[reducible] def is_total' (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ i, x.bval i ⟹ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ f

lemma is_total_iff_is_total' {Γ : 𝔹} {x y f} :
    Γ ≤ is_total x y f ↔ Γ ≤ is_total' x y f := by

  suffices h : is_total x y f = is_total' x y f by rw [h]
  simp only [is_total, is_total']

  have inner_eq : ∀ w₁ : bSet 𝔹, (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
      (⨆ j : y.type, y.bval j ⊓ pair w₁ (y.func j) ∈ᴮ f) :=
    fun w₁ => (@bounded_exists 𝔹 _ y (fun w₂ => pair w₁ w₂ ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right)).symm

  rw [show (⨅ w₁ : bSet 𝔹, w₁ ∈ᴮ x ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
       (⨅ i : x.type, x.bval i ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair (x.func i) w₂ ∈ᴮ f) from
    (@bounded_forall 𝔹 _ x (fun w₁ => ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f)
      (h_congr := fun w₁ w₂ =>
        B_ext_iSup (h := fun w₂ => B_ext_inf B_ext_const B_ext_pair_mem_left) w₁ w₂)).symm]
  congr 1; ext i
  congr 1
  exact inner_eq (x.func i)

@[simp] lemma is_total_subset_of_is_total {S x y f : bSet 𝔹} {Γ}
    (H_is_total : Γ ≤ is_total x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_total S y f := by
  apply le_iInf; intro z; rw [← deduction]
  exact le_trans (le_inf
    (le_trans (le_trans inf_le_left H_is_total) (iInf_le _ z))
    (mem_of_mem_subset (inf_le_left.trans H_subset) inf_le_right)) bv_imp_elim

@[reducible] def is_func' (x y f : bSet 𝔹) : 𝔹 :=
  is_func f ⊓ is_total x y f

@[simp] lemma is_func_of_is_func' {x y f : bSet 𝔹} {Γ} (H : Γ ≤ is_func' x y f) :
    Γ ≤ is_func f := le_trans H inf_le_left

lemma is_total_of_is_func' {x y f : bSet 𝔹} {Γ : 𝔹} (H_is_func' : Γ ≤ is_func' x y f) :
    Γ ≤ is_total x y f := le_trans H_is_func' inf_le_right

lemma is_func'_empty {Γ : 𝔹} {x} : Γ ≤ is_func' (∅ : bSet 𝔹) x ∅ := by
  apply le_inf
  · apply le_iInf; intro w₁; apply le_iInf; intro w₂; apply le_iInf; intro v₁; apply le_iInf; intro v₂
    rw [← deduction]

    exact le_trans (bot_of_mem_empty (inf_le_right.trans inf_le_left)) bot_le
  · exact forall_empty

@[simp] lemma eq_of_is_func_of_eq {x y f x' y' : bSet 𝔹} {Γ : 𝔹} (H_is_func : Γ ≤ is_func f)
    (H_eq₁ : Γ ≤ x =ᴮ y) (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) :
    Γ ≤ x' =ᴮ y' := by

  have hspec := le_trans H_is_func
    (iInf_le _ x |>.trans (iInf_le _ y) |>.trans (iInf_le _ x') |>.trans (iInf_le _ y'))

  exact le_trans (le_inf (le_trans (le_inf hspec (le_inf H_mem₁ H_mem₂)) bv_imp_elim) H_eq₁) bv_imp_elim

@[simp] lemma eq_of_is_func'_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹}
    (H_is_func' : Γ ≤ is_func' a b f) (H_eq₁ : Γ ≤ x =ᴮ y)
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
  eq_of_is_func_of_eq (is_func_of_is_func' H_is_func') H_eq₁ H_mem₁ H_mem₂

@[simp] lemma is_func'_subset_of_is_func' {S x y f : bSet 𝔹} {Γ : 𝔹}
    (H_is_func : Γ ≤ is_func' x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_func' S y f :=
  le_inf (is_func_of_is_func' H_is_func)
         (is_total_subset_of_is_total (is_total_of_is_func' H_is_func) H_subset)

def image (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun j : y.type => ⨆ z, z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f)

@[simp] lemma image_subset {x y f : bSet 𝔹} {Γ} : Γ ≤ image x y f ⊆ᴮ y :=
  subset.mk_subset

@[simp] lemma mem_image {x y a b f : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) :
    Γ ≤ b ∈ᴮ image x y f := by

  unfold image
  rw [mem_subset.mk_iff]

  rw [mem_unfold] at H_mem'
  calc Γ ≤ (⨆ i, y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ := le_inf H_mem' le_rfl
    _ ≤ ⨆ i, (y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ i, b =ᴮ y.func i ⊓ ((⨆ z, z ∈ᴮ x ⊓ pair z (y.func i) ∈ᴮ f) ⊓ y.bval i) := by
          apply iSup_le; intro i
          apply le_iSup_of_le i

          refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))

          apply le_iSup_of_le a

          refine le_inf (inf_le_right.trans H_mem'') ?_

          exact bv_rw' (bv_symm (inf_le_left.trans inf_le_right)) (ϕ := fun z => pair a z ∈ᴮ f)
            (h_congr := B_ext_pair_mem_right) (H_new := inf_le_right.trans H_mem)

lemma mem_image_iff {x y b f : bSet 𝔹} {Γ} :
    Γ ≤ b ∈ᴮ image x y f ↔ (Γ ≤ b ∈ᴮ y) ∧ Γ ≤ ⨆ z, z ∈ᴮ x ⊓ pair z b ∈ᴮ f := by
  constructor
  · intro H
    refine ⟨mem_of_mem_subset image_subset H, ?_⟩
    unfold image at H; rw [mem_subset.mk_iff] at H

    apply H.trans
    apply iSup_le; intro i

    set A := b =ᴮ y.func i
    set Chi := ⨆ z, z ∈ᴮ x ⊓ pair z (y.func i) ∈ᴮ f

    have hbeq : A ⊓ (Chi ⊓ y.bval i) ≤ A := inf_le_left
    have hChi : A ⊓ (Chi ⊓ y.bval i) ≤ Chi :=
      inf_le_right.trans inf_le_left

    apply le_trans (le_inf hChi hbeq)
    rw [iSup_inf_eq]
    apply iSup_le; intro z
    apply le_iSup_of_le z

    refine le_inf (inf_le_left.trans inf_le_left) ?_

    exact bv_rw' (H := inf_le_right) (ϕ := fun w => pair z w ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right) (H_new := inf_le_left.trans inf_le_right)
  · intro ⟨H_mem_y, H_ex⟩
    obtain ⟨a, Ha⟩ := exists_convert H_ex (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image (Ha.trans inf_le_right) (Ha.trans inf_le_left) H_mem_y

@[simp] lemma B_congr_image_left {y f : bSet 𝔹} : B_congr (fun x => image x y f) := by
  intro x₁ x₂ Γ H_eq
  apply mem_ext
  ·
    apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x₁ y f ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x₁ y f ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x₁ y f ≤ ⨆ w, w ∈ᴮ x₁ ⊓ pair w z ∈ᴮ f :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := bv_symm (hΓ.trans H_eq)) (ϕ := fun x => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)) (H_new := hmem.2)⟩
  ·
    apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x₂ y f ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x₂ y f ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x₂ y f ≤ ⨆ w, w ∈ᴮ x₂ ⊓ pair w z ∈ᴮ f :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := hΓ.trans H_eq) (ϕ := fun x => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)) (H_new := hmem.2)⟩

@[simp] lemma B_congr_image_right {x y : bSet 𝔹} : B_congr (fun f => image x y f) := by
  intro f₁ f₂ Γ H_eq
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x y f₁ ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x y f₁ ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x y f₁ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f₁ :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := bv_symm (hΓ.trans H_eq)) (ϕ := fun f => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)) (H_new := hmem.2)⟩
  · apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x y f₂ ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x y f₂ ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x y f₂ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f₂ :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := hΓ.trans H_eq) (ϕ := fun f => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)) (H_new := hmem.2)⟩

def preimage (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun i : x.type => ⨆ b, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f)

@[simp] lemma preimage_subset {x y f} {Γ : 𝔹} : Γ ≤ preimage x y f ⊆ᴮ x :=
  subset.mk_subset

@[simp] lemma mem_preimage {x y a b f : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) :
    Γ ≤ a ∈ᴮ preimage x y f := by
  unfold preimage; rw [mem_subset.mk_iff]
  rw [mem_unfold] at H_mem''

  calc Γ ≤ (⨆ i, x.bval i ⊓ a =ᴮ x.func i) ⊓ Γ := le_inf H_mem'' le_rfl
    _ ≤ ⨆ i, (x.bval i ⊓ a =ᴮ x.func i) ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ i, a =ᴮ x.func i ⊓ ((⨆ b', b' ∈ᴮ y ⊓ pair (x.func i) b' ∈ᴮ f) ⊓ x.bval i) := by
          apply iSup_le; intro i
          apply le_iSup_of_le i
          set A := a =ᴮ x.func i

          refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))

          apply le_iSup_of_le b
          refine le_inf (inf_le_right.trans H_mem') ?_

          exact bv_rw' (bv_symm (inf_le_left.trans inf_le_right)) (ϕ := fun w => pair w b ∈ᴮ f)
            (h_congr := B_ext_pair_mem_left) (H_new := inf_le_right.trans H_mem)

@[reducible] def is_function (x y f : bSet 𝔹) : 𝔹 :=
  is_func' x y f ⊓ (f ⊆ᴮ prod x y)

@[simp] lemma B_ext_is_function_left {y f : bSet 𝔹} : B_ext (fun x => is_function x y f) :=

  B_ext_inf
    (B_ext_inf B_ext_const
      (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
    (B_ext_term (ϕ := fun v => f ⊆ᴮ v) (t := fun x => prod x y)
      (H := B_ext_subset_right) (H' := B_congr_prod_left))

@[simp] lemma B_ext_is_function_right {x y : bSet 𝔹} : B_ext (fun f => is_function x y f) :=

  B_ext_inf
    (B_ext_inf

      (B_ext_iInf (h := fun w₁ => B_ext_iInf (h := fun w₂ => B_ext_iInf (h := fun v₁ => B_ext_iInf (h := fun v₂ =>
        B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_mem_right)
          (h₂ := B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_const)))))))

      (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
        (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))))
    (B_ext_subset_left (y := prod x y))

lemma is_func'_of_is_function {Γ : 𝔹} {x y f} (H_func : Γ ≤ is_function x y f) :
    Γ ≤ is_func' x y f := le_trans H_func inf_le_left

lemma eq_of_is_function_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹}
    (H_is_function : Γ ≤ is_function a b f) (H_eq₁ : Γ ≤ x =ᴮ y)
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
  eq_of_is_func'_of_eq (is_func'_of_is_function H_is_function) H_eq₁ H_mem₁ H_mem₂

lemma subset_prod_of_is_function {Γ : 𝔹} {x y f} (H_func : Γ ≤ is_function x y f) :
    Γ ≤ f ⊆ᴮ prod x y := le_trans H_func inf_le_right

lemma is_total_of_is_function {x y f : bSet 𝔹} {Γ} (H_func : Γ ≤ is_function x y f) :
    Γ ≤ is_total x y f :=
  is_total_of_is_func' (is_func'_of_is_function H_func)

lemma mem_domain_of_is_function {x y f : bSet 𝔹} {Γ} {z w : bSet 𝔹}
    (H_mem : Γ ≤ pair z w ∈ᴮ f) (H_func : Γ ≤ is_function x y f) : Γ ≤ z ∈ᴮ x :=
  (mem_prod_iff.mp (mem_of_mem_subset (subset_prod_of_is_function H_func) H_mem)).left

lemma mem_codomain_of_is_function {x y f : bSet 𝔹} {Γ} {z w : bSet 𝔹}
    (H_mem : Γ ≤ pair z w ∈ᴮ f) (H_func : Γ ≤ is_function x y f) : Γ ≤ w ∈ᴮ y :=
  (mem_prod_iff.mp (mem_of_mem_subset (subset_prod_of_is_function H_func) H_mem)).right

lemma factor_image_is_func' {x y f : bSet 𝔹} {Γ} (H_is_func' : Γ ≤ is_func' x y f) :
    Γ ≤ is_func' x (image x y f) f := by
  refine le_inf (le_trans H_is_func' inf_le_left) ?_
  apply le_iInf; intro w₁; rw [← deduction]

  have H_total := is_total_of_is_func' H_is_func'
  have H_Γ : Γ ⊓ w₁ ∈ᴮ x ≤ Γ := inf_le_left
  have H_w₁ : Γ ⊓ w₁ ∈ᴮ x ≤ w₁ ∈ᴮ x := inf_le_right
  have H_total_spec := le_trans H_Γ (le_trans H_total (iInf_le _ w₁))

  have H_step := le_trans (le_inf H_total_spec H_w₁) bv_imp_elim

  calc Γ ⊓ w₁ ∈ᴮ x
      ≤ (⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (Γ ⊓ w₁ ∈ᴮ x) := le_inf H_step le_rfl
    _ ≤ ⨆ w₂, (w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (Γ ⊓ w₁ ∈ᴮ x) := (iSup_inf_eq _ _).le
    _ ≤ ⨆ w₂, w₂ ∈ᴮ image x y f ⊓ pair w₁ w₂ ∈ᴮ f := by
          apply iSup_le; intro w₂; apply le_iSup_of_le w₂

          refine le_inf ?_ (inf_le_left.trans inf_le_right)
          exact mem_image (inf_le_left.trans inf_le_right)
            (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_left)

lemma factor_image_is_function {x y f : bSet 𝔹} {Γ} (H_is_function : Γ ≤ is_function x y f) :
    Γ ≤ is_function x (image x y f) f := by
  refine le_inf ?_ ?_
  · exact factor_image_is_func' (is_func'_of_is_function H_is_function)
  · rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]

    have H_sub := subset_prod_of_is_function H_is_function
    have H_w_prod_xy : Γ ⊓ w ∈ᴮ f ≤ w ∈ᴮ prod x y :=
      mem_of_mem_subset (le_trans inf_le_left H_sub) inf_le_right

    have H_w_prod_unfold : Γ ⊓ w ∈ᴮ f ≤ ⨆ p : x.type × y.type,
        (x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2) := by
      calc Γ ⊓ w ∈ᴮ f ≤ w ∈ᴮ prod x y := H_w_prod_xy
        _ = ⨆ p : x.type × y.type, (prod x y).bval p ⊓ w =ᴮ (prod x y).func p := mem_unfold
        _ = ⨆ p : x.type × y.type, (x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2) :=
              rfl
    calc Γ ⊓ w ∈ᴮ f
        ≤ (⨆ p : x.type × y.type, (x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2)) ⊓
            (Γ ⊓ w ∈ᴮ f) := le_inf H_w_prod_unfold le_rfl
      _ ≤ ⨆ p : x.type × y.type, ((x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2)) ⊓
              (Γ ⊓ w ∈ᴮ f) := (iSup_inf_eq _ _).le
      _ ≤ w ∈ᴮ prod x (image x y f) := by
            apply iSup_le; intro ⟨i, j⟩

            set L := (x.bval i ⊓ y.bval j) ⊓ w =ᴮ pair (x.func i) (y.func j)
            set R := Γ ⊓ w ∈ᴮ f

            have hxb : L ⊓ R ≤ x.bval i :=
              (inf_le_left (b := R)).trans ((inf_le_left (b := w =ᴮ pair (x.func i) (y.func j))).trans inf_le_left)
            have hyb : L ⊓ R ≤ y.bval j :=
              (inf_le_left (b := R)).trans ((inf_le_left (b := w =ᴮ pair (x.func i) (y.func j))).trans inf_le_right)
            have heq : L ⊓ R ≤ w =ᴮ pair (x.func i) (y.func j) :=
              (inf_le_left (b := R)).trans inf_le_right
            have hw_f : L ⊓ R ≤ w ∈ᴮ f :=
              (inf_le_right (a := L)).trans inf_le_right
            have hpair_f := subst_congr_mem_left' heq hw_f
            have hxi := le_trans hxb (mem_mk' x i)
            have hyj := le_trans hyb (mem_mk' y j)
            have himage := mem_image hpair_f hxi hyj
            exact subst_congr_mem_left' (bv_symm heq) (prod_mem hxi himage)

lemma check_is_total {x y f : PSet.{u}} (H_total : PSet.is_total x y f) {Γ : 𝔹} :
    Γ ≤ is_total (check x) (check y) (check f) := by
  cases y with | mk yα yA =>
  cases x with | mk xα xA =>

  rw [is_total_iff_is_total']
  apply le_iInf; intro i
  simp only [check_bval_top, top_imp]

  obtain ⟨w, Hw_mem, Hw_pair⟩ := H_total (xA i) (PSet.func_mem (PSet.mk xα xA) i)
  obtain ⟨j₀, Hj₀⟩ := Hw_mem
  apply le_iSup_of_le j₀
  simp only [check_bval_top, top_inf_eq]

  have Hpair : PSet.pSet_pair (xA i) (yA j₀) ∈ f :=
    (PSet.pSet_pair_mem_congr_right Hj₀).mp Hw_pair
  exact subst_congr_mem_left' check_pset_pair (check_mem Hpair)

private lemma check_mem_as_iSup {f : PSet.{u}} {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {z : bSet 𝔹} : z ∈ᴮ (check f : bSet 𝔹) = ⨆ k : f.Type, z =ᴮ check (f.Func k) := by
  cases f with | mk α A =>
  simp only [mem_unfold, check, bSet.bval, bSet.func, top_inf_eq]
  rfl

lemma check_is_func {x y f : PSet.{u}} (H_func : PSet.is_func x y f) {Γ : 𝔹} :
    Γ ≤ is_function (check x) (check y) (check f) := by

  refine le_inf (le_inf ?_ (check_is_total (PSet.is_total_of_is_func H_func))) ?_
  ·
    apply le_iInf; intro w₁; apply le_iInf; intro w₂
    apply le_iInf; intro v₁; apply le_iInf; intro v₂
    rw [← deduction, ← deduction]

    suffices key : ∀ k₁ k₂ : f.Type,
        Γ ⊓ (pair w₁ v₁ =ᴮ check (f.Func k₁) ⊓ pair w₂ v₂ =ᴮ check (f.Func k₂)) ⊓ w₁ =ᴮ w₂ ≤ v₁ =ᴮ v₂ by

      rw [show pair w₁ v₁ ∈ᴮ (check f : bSet 𝔹) = ⨆ k₁ : f.Type, pair w₁ v₁ =ᴮ check (f.Func k₁)
          from check_mem_as_iSup,
          show pair w₂ v₂ ∈ᴮ (check f : bSet 𝔹) = ⨆ k₂ : f.Type, pair w₂ v₂ =ᴮ check (f.Func k₂)
          from check_mem_as_iSup]

      simp only [iSup_inf_eq', inf_iSup_eq', inf_assoc]
      apply iSup_le; intro k₁
      apply iSup_le; intro k₂

      have h := key k₂ k₁; simp only [inf_assoc] at h; exact h
    intro k₁ k₂
    set Γ_kk := Γ ⊓ (pair w₁ v₁ =ᴮ check (f.Func k₁) ⊓ pair w₂ v₂ =ᴮ check (f.Func k₂)) ⊓ w₁ =ᴮ w₂
    by_cases h_pos : ⊥ < Γ_kk
    · obtain ⟨ij₁, hij₁⟩ := PSet.subset_prod_of_is_func H_func k₁
      obtain ⟨ij₂, hij₂⟩ := PSet.subset_prod_of_is_func H_func k₂
      simp only [PSet.pSet_prod] at hij₁ hij₂
      have hfk₁_bveq : Γ_kk ≤ check (f.Func k₁) =ᴮ pair (check (x.Func ij₁.1)) (check (y.Func ij₁.2)) := by
        have h : (⊤ : 𝔹) ≤ check (f.Func k₁) =ᴮ check (PSet.pSet_pair (x.Func ij₁.1) (y.Func ij₁.2)) :=
          check_bv_eq hij₁
        rw [check_pset_pair_eq] at h; exact le_trans le_top h
      have hfk₂_bveq : Γ_kk ≤ check (f.Func k₂) =ᴮ pair (check (x.Func ij₂.1)) (check (y.Func ij₂.2)) := by
        have h : (⊤ : 𝔹) ≤ check (f.Func k₂) =ᴮ check (PSet.pSet_pair (x.Func ij₂.1) (y.Func ij₂.2)) :=
          check_bv_eq hij₂
        rw [check_pset_pair_eq] at h; exact le_trans le_top h
      have hpair₁ : Γ_kk ≤ pair w₁ v₁ =ᴮ pair (check (x.Func ij₁.1)) (check (y.Func ij₁.2)) :=
        bv_trans (inf_le_left.trans (inf_le_right.trans inf_le_left)) hfk₁_bveq
      have hpair₂ : Γ_kk ≤ pair w₂ v₂ =ᴮ pair (check (x.Func ij₂.1)) (check (y.Func ij₂.2)) :=
        bv_trans (inf_le_left.trans (inf_le_right.trans inf_le_right)) hfk₂_bveq
      have hw_eq : Γ_kk ≤ w₁ =ᴮ w₂ := inf_le_right
      have hw₁ : Γ_kk ≤ w₁ =ᴮ check (x.Func ij₁.1) := (pair_eq_pair_iff.mp hpair₁).1
      have hv₁ : Γ_kk ≤ v₁ =ᴮ check (y.Func ij₁.2) := (pair_eq_pair_iff.mp hpair₁).2
      have hw₂ : Γ_kk ≤ w₂ =ᴮ check (x.Func ij₂.1) := (pair_eq_pair_iff.mp hpair₂).1
      have hv₂ : Γ_kk ≤ v₂ =ᴮ check (y.Func ij₂.2) := (pair_eq_pair_iff.mp hpair₂).2
      have hx_bveq : Γ_kk ≤ check (x.Func ij₁.1) =ᴮ check (x.Func ij₂.1) :=
        bv_trans (bv_symm hw₁) (bv_trans hw_eq hw₂)
      have hEquiv_x : PSet.Equiv (x.Func ij₁.1) (x.Func ij₂.1) :=
        check_eq_reflect h_pos hx_bveq
      have hmemf₁ : PSet.pSet_pair (x.Func ij₁.1) (y.Func ij₁.2) ∈ f :=
        PSet.mem_iff.mpr ⟨k₁, hij₁.symm⟩
      have hmemf₂ : PSet.pSet_pair (x.Func ij₂.1) (y.Func ij₂.2) ∈ f :=
        PSet.mem_iff.mpr ⟨k₂, hij₂.symm⟩
      have hEquiv_y : PSet.Equiv (y.Func ij₁.2) (y.Func ij₂.2) :=
        PSet.eq_of_is_func_of_eq H_func hmemf₁ hmemf₂ hEquiv_x
      have hy_bveq : Γ_kk ≤ check (y.Func ij₁.2) =ᴮ check (y.Func ij₂.2) :=
        le_trans le_top (check_eq hEquiv_y)
      exact bv_trans hv₁ (bv_trans hy_bveq (bv_symm hv₂))
    · rw [bot_lt_iff_not_le_bot, not_not] at h_pos
      exact le_trans h_pos bot_le
  ·

    have h_sub : Γ ≤ check f ⊆ᴮ check (PSet.pSet_prod x y) :=
      check_subset (PSet.subset_prod_of_is_func H_func)
    exact le_trans (le_inf h_sub check_pset_prod) subst_congr_subset_right

def function_of_func' {x y f : bSet 𝔹} {Γ} (_H_is_func' : Γ ≤ is_func' x y f) : bSet 𝔹 :=
  f ∩ᴮ (prod x y)

lemma function_of_func'_subset {x y f : bSet 𝔹} {Γ} {H_is_func' : Γ ≤ is_func' x y f} :
    Γ ≤ function_of_func' H_is_func' ⊆ᴮ f :=
  binary_inter_subset_left

lemma mem_function_of_func'_iff {x y f : bSet 𝔹} {Γ} {H_is_func' : Γ ≤ is_func' x y f} {z} :
    Γ ≤ z ∈ᴮ (function_of_func' H_is_func') ↔ Γ ≤ z ∈ᴮ f ∧ Γ ≤ z ∈ᴮ (prod x y) :=
  mem_binary_inter_iff

@[reducible] def is_inj (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅ w₂, ⨅ v₁, ⨅ v₂,
    (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂) ⟹ w₁ =ᴮ w₂

@[reducible] def is_injective_function (x y f : bSet 𝔹) : 𝔹 :=
  is_function x y f ⊓ is_inj f

lemma is_inj_of_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_injective_function x y f → Γ ≤ is_inj f :=
  fun h => le_trans h inf_le_right

lemma factor_image_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_is_function : Γ ≤ is_injective_function x y f) :
    Γ ≤ is_injective_function x (image x y f) f :=
  le_inf (factor_image_is_function (le_trans H_is_function inf_le_left))
         (le_trans H_is_function inf_le_right)

@[simp] lemma B_ext_is_injective_function_left {y f : bSet 𝔹} :
    B_ext (fun x => is_injective_function x y f) :=

  B_ext_inf B_ext_is_function_left B_ext_const

lemma is_func'_of_is_injective_function {x y f : bSet 𝔹} {Γ}
    (H : Γ ≤ is_injective_function x y f) : Γ ≤ is_func' x y f :=
  is_func'_of_is_function (le_trans H inf_le_left)

lemma check_is_injective_function {x y f : PSet.{u}}
    (H_inj : PSet.is_injective_function x y f) {Γ : 𝔹} :
    Γ ≤ bSet.is_injective_function (check x) (check y) (check f) := by
  refine le_inf (check_is_func H_inj.1) ?_
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]
  suffices key : ∀ k₁ k₂ : f.Type,
      Γ ⊓ (pair w₁ v₁ =ᴮ check (f.Func k₁) ⊓ (pair w₂ v₂ =ᴮ check (f.Func k₂) ⊓ v₁ =ᴮ v₂)) ≤ w₁ =ᴮ w₂ by

    rw [show pair w₁ v₁ ∈ᴮ (check f : bSet 𝔹) = ⨆ k₁ : f.Type, pair w₁ v₁ =ᴮ check (f.Func k₁)
        from check_mem_as_iSup,
        show pair w₂ v₂ ∈ᴮ (check f : bSet 𝔹) = ⨆ k₂ : f.Type, pair w₂ v₂ =ᴮ check (f.Func k₂)
        from check_mem_as_iSup]
    simp only [iSup_inf_eq', inf_iSup_eq', inf_assoc]
    apply iSup_le; intro k₁
    apply iSup_le; intro k₂
    exact key k₂ k₁
  intro k₁ k₂
  set Γ_kk := Γ ⊓ (pair w₁ v₁ =ᴮ check (f.Func k₁) ⊓ (pair w₂ v₂ =ᴮ check (f.Func k₂) ⊓ v₁ =ᴮ v₂))
  by_cases h_pos : ⊥ < Γ_kk
  · obtain ⟨ij₁, hij₁⟩ := PSet.subset_prod_of_is_func H_inj.1 k₁
    obtain ⟨ij₂, hij₂⟩ := PSet.subset_prod_of_is_func H_inj.1 k₂
    simp only [PSet.pSet_prod] at hij₁ hij₂
    have hfk₁_bveq : Γ_kk ≤ check (f.Func k₁) =ᴮ pair (check (x.Func ij₁.1)) (check (y.Func ij₁.2)) := by
      have h : (⊤ : 𝔹) ≤ check (f.Func k₁) =ᴮ check (PSet.pSet_pair (x.Func ij₁.1) (y.Func ij₁.2)) :=
        check_bv_eq hij₁
      rw [check_pset_pair_eq] at h; exact le_trans le_top h
    have hfk₂_bveq : Γ_kk ≤ check (f.Func k₂) =ᴮ pair (check (x.Func ij₂.1)) (check (y.Func ij₂.2)) := by
      have h : (⊤ : 𝔹) ≤ check (f.Func k₂) =ᴮ check (PSet.pSet_pair (x.Func ij₂.1) (y.Func ij₂.2)) :=
        check_bv_eq hij₂
      rw [check_pset_pair_eq] at h; exact le_trans le_top h
    have hpair₁ : Γ_kk ≤ pair w₁ v₁ =ᴮ pair (check (x.Func ij₁.1)) (check (y.Func ij₁.2)) :=
      bv_trans (inf_le_right.trans inf_le_left) hfk₁_bveq
    have hpair₂ : Γ_kk ≤ pair w₂ v₂ =ᴮ pair (check (x.Func ij₂.1)) (check (y.Func ij₂.2)) :=
      bv_trans (inf_le_right.trans (inf_le_right.trans inf_le_left)) hfk₂_bveq
    have hv_eq : Γ_kk ≤ v₁ =ᴮ v₂ := inf_le_right.trans (inf_le_right.trans inf_le_right)
    have hw₁ : Γ_kk ≤ w₁ =ᴮ check (x.Func ij₁.1) := (pair_eq_pair_iff.mp hpair₁).1
    have hv₁ : Γ_kk ≤ v₁ =ᴮ check (y.Func ij₁.2) := (pair_eq_pair_iff.mp hpair₁).2
    have hw₂ : Γ_kk ≤ w₂ =ᴮ check (x.Func ij₂.1) := (pair_eq_pair_iff.mp hpair₂).1
    have hv₂ : Γ_kk ≤ v₂ =ᴮ check (y.Func ij₂.2) := (pair_eq_pair_iff.mp hpair₂).2
    have hy_bveq : Γ_kk ≤ check (y.Func ij₁.2) =ᴮ check (y.Func ij₂.2) :=
      bv_trans (bv_symm hv₁) (bv_trans hv_eq hv₂)
    have hEquiv_y : PSet.Equiv (y.Func ij₁.2) (y.Func ij₂.2) :=
      check_eq_reflect h_pos hy_bveq
    have hmemf₁ : PSet.pSet_pair (x.Func ij₁.1) (y.Func ij₁.2) ∈ f :=
      PSet.mem_iff.mpr ⟨k₁, hij₁.symm⟩
    have hmemf₂ : PSet.pSet_pair (x.Func ij₂.1) (y.Func ij₂.2) ∈ f :=
      PSet.mem_iff.mpr ⟨k₂, hij₂.symm⟩
    have hEquiv_x : PSet.Equiv (x.Func ij₁.1) (x.Func ij₂.1) :=
      H_inj.2 (x.Func ij₁.1) (x.Func ij₂.1) (y.Func ij₁.2) (y.Func ij₂.2)
        ⟨hmemf₁, hmemf₂, hEquiv_y⟩
    have hx_bveq : Γ_kk ≤ check (x.Func ij₁.1) =ᴮ check (x.Func ij₂.1) :=
      le_trans le_top (check_eq hEquiv_x)
    exact bv_trans hw₁ (bv_trans hx_bveq (bv_symm hw₂))
  · rw [bot_lt_iff_not_le_bot, not_not] at h_pos
    exact le_trans h_pos bot_le

@[simp] lemma eq_of_is_inj_of_eq {x y x' y' f : bSet 𝔹} {Γ : 𝔹}
    (H_is_inj : Γ ≤ is_inj f) (H_eq : Γ ≤ x' =ᴮ y')
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x =ᴮ y := by
  have hspec := le_trans H_is_inj
    (iInf_le _ x |>.trans (iInf_le _ y) |>.trans (iInf_le _ x') |>.trans (iInf_le _ y'))

  exact le_trans (le_inf hspec (le_inf (le_inf H_mem₁ H_mem₂) H_eq)) bv_imp_elim

lemma funext {x y f g : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_function x y f) (H₂ : Γ ≤ is_function x y g)
    (H_peq : Γ ≤ ⨅ p, p ∈ᴮ prod x y ⟹ (p ∈ᴮ f ⇔ p ∈ᴮ g)) : Γ ≤ f =ᴮ g := by
  have H_sub₁ := subset_prod_of_is_function H₁
  have H_sub₂ := subset_prod_of_is_function H₂
  apply mem_ext

  ·
    apply le_iInf; intro z; rw [← deduction]

    have hz_prod : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (le_trans inf_le_left H_sub₁) inf_le_right
    have hpeq_spec : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ prod x y ⟹ (z ∈ᴮ f ⇔ z ∈ᴮ g) :=
      le_trans inf_le_left (le_trans H_peq (iInf_le _ z))
    have hiff := le_trans (le_inf hpeq_spec hz_prod) bv_imp_elim

    have hfwd : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ f ⟹ z ∈ᴮ g := le_trans hiff inf_le_left
    exact le_trans (le_inf hfwd inf_le_right) bv_imp_elim
  ·
    apply le_iInf; intro z; rw [← deduction]

    have hz_prod : Γ ⊓ z ∈ᴮ g ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (le_trans inf_le_left H_sub₂) inf_le_right
    have hpeq_spec : Γ ⊓ z ∈ᴮ g ≤ z ∈ᴮ prod x y ⟹ (z ∈ᴮ f ⇔ z ∈ᴮ g) :=
      le_trans inf_le_left (le_trans H_peq (iInf_le _ z))
    have hiff := le_trans (le_inf hpeq_spec hz_prod) bv_imp_elim
    have hbwd : Γ ⊓ z ∈ᴮ g ≤ z ∈ᴮ g ⟹ z ∈ᴮ f := le_trans hiff inf_le_right
    exact le_trans (le_inf hbwd inf_le_right) bv_imp_elim

@[reducible] def is_surj (x y : bSet 𝔹) (f : bSet 𝔹) : 𝔹 :=
  ⨅ v, v ∈ᴮ y ⟹ (⨆ w, w ∈ᴮ x ⊓ pair w v ∈ᴮ f)

def larger_than (x y : bSet 𝔹) : 𝔹 :=
  ⨆ S, ⨆ f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f)

lemma is_surj_empty {Γ : 𝔹} : Γ ≤ is_surj (∅ : bSet 𝔹) ∅ ∅ :=
  forall_empty

lemma function_of_func'_is_function {x y f : bSet 𝔹} {Γ} (H_is_func' : Γ ≤ is_func' x y f) :
    Γ ≤ is_function x y (function_of_func' H_is_func') := by
  refine le_inf (le_inf ?_ ?_) ?_
  · exact is_func_subset_of_is_func (is_func_of_is_func' H_is_func') binary_inter_subset_left
  ·
    apply le_iInf; intro w₁; rw [← deduction, inf_comm]

    have H_total : Γ ≤ is_total x y f := is_total_of_is_func' H_is_func'

    have H_total_spec : w₁ ∈ᴮ x ⊓ Γ ≤ w₁ ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f :=
      le_trans (le_trans inf_le_right H_total) (iInf_le _ w₁)

    have step : w₁ ∈ᴮ x ⊓ Γ ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f :=
      le_trans (le_inf H_total_spec (inf_le_left (b := Γ))) bv_imp_elim

    calc w₁ ∈ᴮ x ⊓ Γ
        ≤ (⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (w₁ ∈ᴮ x ⊓ Γ) := le_inf step le_rfl
      _ ≤ ⨆ w₂, (w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (w₁ ∈ᴮ x ⊓ Γ) := (iSup_inf_eq _ _).le
      _ ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ (f ∩ᴮ prod x y) := by
            apply iSup_le; intro w₂; apply le_iSup_of_le w₂
            refine le_inf (inf_le_left.trans inf_le_left) ?_

            apply mem_binary_inter_iff.mpr
            constructor
            · exact inf_le_left.trans inf_le_right
            · exact le_trans (le_inf (inf_le_right.trans inf_le_left)
                (inf_le_left.trans inf_le_left)) prod_mem_old
  · exact binary_inter_subset_right

lemma function_of_func'_surj_of_surj {x y f : bSet 𝔹} {Γ}
    (H_is_func' : Γ ≤ is_func' x y f) (H_is_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_surj x y (function_of_func' H_is_func') := by
  apply le_iInf; intro z; rw [← deduction]

  have step : Γ ⊓ z ∈ᴮ y ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f :=
    le_trans (le_inf (le_trans (le_trans inf_le_left H_is_surj) (iInf_le _ z)) inf_le_right) bv_imp_elim
  calc Γ ⊓ z ∈ᴮ y
      ≤ (⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ y) := le_inf step le_rfl
    _ ≤ ⨆ w, (w ∈ᴮ x ⊓ pair w z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ y) := (iSup_inf_eq _ _).le
    _ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ (f ∩ᴮ prod x y) := by
          apply iSup_le; intro w; apply le_iSup_of_le w
          refine le_inf (inf_le_left.trans inf_le_left) ?_
          apply mem_binary_inter_iff.mpr
          exact ⟨inf_le_left.trans inf_le_right,
            le_trans (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right))
              prod_mem_old⟩

lemma function_of_func'_inj_of_inj {x y f : bSet 𝔹} {Γ} {H : Γ ≤ is_func' x y f}
    (H_is_inj : Γ ≤ is_inj f) : Γ ≤ is_inj (function_of_func' H) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]

  set Γ₁ := Γ ⊓ (pair w₁ v₁ ∈ᴮ (f ∩ᴮ prod x y) ⊓ pair w₂ v₂ ∈ᴮ (f ∩ᴮ prod x y) ⊓ v₁ =ᴮ v₂)
  have hmem₁ : Γ₁ ≤ pair w₁ v₁ ∈ᴮ f :=
    mem_of_mem_subset binary_inter_subset_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hmem₂ : Γ₁ ≤ pair w₂ v₂ ∈ᴮ f :=
    mem_of_mem_subset binary_inter_subset_left (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hveq : Γ₁ ≤ v₁ =ᴮ v₂ := inf_le_right.trans inf_le_right
  have hspec : Γ₁ ≤ pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂ ⟹ w₁ =ᴮ w₂ :=
    le_trans inf_le_left (le_trans H_is_inj
      ((iInf_le _ w₁).trans (iInf_le _ w₂) |>.trans (iInf_le _ v₁) |>.trans (iInf_le _ v₂)))
  exact le_trans (le_inf hspec (le_inf (le_inf hmem₁ hmem₂) hveq)) bv_imp_elim

lemma surj_image {x y f : bSet 𝔹} {Γ} (H_func : Γ ≤ is_func' x y f) :
    Γ ≤ is_surj x (image x y f) f := by
  apply le_iInf; intro w; rw [← deduction]

  have hmem : Γ ⊓ w ∈ᴮ image x y f ≤ w ∈ᴮ image x y f := inf_le_right
  rw [mem_image_iff] at hmem
  exact hmem.right

lemma image_eq_codomain_of_surj {x y f : bSet 𝔹} {Γ}
    (H_surj : Γ ≤ is_surj x y f) : Γ ≤ image x y f =ᴮ y := by
  refine subset_ext image_subset ?_
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]

  have hΓ : Γ ⊓ z ∈ᴮ y ≤ Γ := inf_le_left
  have hmem : Γ ⊓ z ∈ᴮ y ≤ z ∈ᴮ y := inf_le_right
  have hspec := le_trans hΓ (le_trans H_surj (iInf_le _ z))

  rw [mem_image_iff]
  exact ⟨hmem, le_trans (le_inf hspec hmem) bv_imp_elim⟩

@[simp] lemma larger_than_domain_subset {Γ : 𝔹} {x y S : bSet 𝔹}
    (HS : Γ ≤ ⨆ f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f)) : Γ ≤ S ⊆ᴮ x := by
  exact le_trans HS (iSup_le (fun f => le_trans (le_trans inf_le_left inf_le_left) (le_refl _)))

def injects_into (x y : bSet 𝔹) : 𝔹 := ⨆ f, (is_func' x y f) ⊓ is_inj f

def injection_into (x y : bSet 𝔹) : 𝔹 := ⨆ f, is_injective_function x y f

lemma injection_into_of_injects_into {x y : bSet 𝔹} {Γ} (H : Γ ≤ injects_into x y) :
    Γ ≤ injection_into x y :=

  H.trans (iSup_le fun f =>
    le_iSup_of_le (function_of_func' inf_le_left)
      (le_inf (function_of_func'_is_function inf_le_left)
        (function_of_func'_inj_of_inj inf_le_right)))

lemma injects_into_of_injection_into {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ injection_into x y) :
    Γ ≤ injects_into x y :=

  H_inj.trans (iSup_le fun f =>
    le_iSup_of_le f (le_inf (inf_le_left.trans inf_le_left) inf_le_right))

lemma injects_into_iff_injection_into {x y : bSet 𝔹} {Γ} :
    Γ ≤ injects_into x y ↔ Γ ≤ injection_into x y :=
  ⟨injection_into_of_injects_into, injects_into_of_injection_into⟩

lemma check_injects_into {x y : PSet.{u}} (H_inj : PSet.injects_into x y) {Γ : 𝔹} :
    Γ ≤ bSet.injects_into (check x) (check y) := by

  obtain ⟨f, hf_inj⟩ := H_inj
  apply le_iSup_of_le (check f)
  refine le_inf ?_ ?_
  · exact is_func'_of_is_function (check_is_func hf_inj.1)
  · exact le_trans (check_is_injective_function hf_inj) inf_le_right

@[reducible] def is_surj_onto (x y f : bSet 𝔹) : 𝔹 := (is_func' x y f) ⊓ (is_surj x y f)

def surjects_onto (x y : bSet 𝔹) : 𝔹 := ⨆ f, is_surj_onto x y f

private def B_ext_is_total_right (S f : bSet 𝔹) : B_ext (fun z => is_total S z f) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)))

private def B_ext_is_surj_codomain (S f : bSet 𝔹) : B_ext (fun z => is_surj S z f) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))

@[simp] lemma B_ext_larger_than_right {y : bSet 𝔹} : B_ext (fun z => larger_than y z) :=
  B_ext_iSup (h := fun S => B_ext_iSup (h := fun f =>
    B_ext_inf (B_ext_inf B_ext_const
      (B_ext_inf B_ext_const (B_ext_is_total_right S f)))
    (B_ext_is_surj_codomain S f)))

@[simp] lemma B_ext_larger_than_left {y : bSet 𝔹} : B_ext (fun z => larger_than z y) :=

  B_ext_iSup (h := fun S => B_ext_iSup (h := fun f =>
    B_ext_inf (B_ext_inf B_ext_subset_right B_ext_const) B_ext_const))

@[simp] lemma B_ext_injects_into_left {y : bSet 𝔹} : B_ext (fun z => injects_into z y) :=
  B_ext_iSup (h := fun f =>
    B_ext_inf
      (B_ext_inf B_ext_const
        (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
      B_ext_const)

@[simp] lemma B_ext_injects_into_right {y : bSet 𝔹} : B_ext (fun z => injects_into y z) :=
  B_ext_iSup (h := fun f =>
    B_ext_inf
      (B_ext_inf B_ext_const (B_ext_is_total_right y f))
      B_ext_const)

def pointed_extension {x y : bSet 𝔹} {Γ : 𝔹} {S f : bSet 𝔹}
    (b : bSet 𝔹) (_H_b : Γ ≤ b ∈ᴮ y) (_H_S : Γ ≤ S ⊆ᴮ x)
    (_H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x y).type =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ (y.func pr.2) =ᴮ b))

@[simp] lemma pointed_extension_func {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    {H_b : Γ ≤ b ∈ᴮ y} {H_S : Γ ≤ S ⊆ᴮ x} {H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f}
    {pr : (prod x y).type} :
    (pointed_extension b H_b H_S H_surj).func pr = pair (x.func pr.1) (y.func pr.2) := rfl

lemma pointed_extension_is_func {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_func (pointed_extension b H_b H_S H_surj) := by

  set pe := pointed_extension b H_b H_S H_surj
  set φ : (prod x y).type → 𝔹 := fun pr =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ y.func pr.2 =ᴮ b)
  have hpe_eq : pe = subset.mk φ := rfl
  have hmem_pe : ∀ (w v : bSet 𝔹), pair w v ∈ᴮ pe ≤
      ⨆ pr : (prod x y).type, pair w v =ᴮ (prod x y).func pr ⊓ (φ pr ⊓ (prod x y).bval pr) :=
    fun w v => hpe_eq ▸ mem_subset.mk_iff.mp le_rfl
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]

  apply (le_inf (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans (hmem_pe w₁ v₁)))) le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans; apply iSup_le; intro pr₁; obtain ⟨i, j⟩ := pr₁
  simp only [prod_func, prod_bval, φ]

  apply (le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans (hmem_pe w₂ v₂))))) le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans
  apply iSup_le; intro pr₂; obtain ⟨i', j'⟩ := pr₂
  simp only [prod_func, prod_bval, φ]

  set ctx2 := (pair w₂ v₂ =ᴮ pair (x.func i') (y.func j') ⊓
      (((x.func i' ∈ᴮ S ⟹ pair (x.func i') (y.func j') ∈ᴮ f) ⊓ ((x.func i' ∈ᴮ S)ᶜ ⟹ y.func j' =ᴮ b)) ⊓
        (x.bval i' ⊓ y.bval j'))) ⊓
    ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓
        (((x.func i ∈ᴮ S ⟹ pair (x.func i) (y.func j) ∈ᴮ f) ⊓ ((x.func i ∈ᴮ S)ᶜ ⟹ y.func j =ᴮ b)) ⊓
          (x.bval i ⊓ y.bval j))) ⊓
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ pe ⊓ pair w₂ v₂ ∈ᴮ pe) ⊓ w₁ =ᴮ w₂))

  have hw1xi : ctx2 ≤ w₁ =ᴮ x.func i :=
    inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left))
  have hv1yj : ctx2 ≤ v₁ =ᴮ y.func j :=
    inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right))
  have hw2xi' : ctx2 ≤ w₂ =ᴮ x.func i' :=
    inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left)
  have hv2yj' : ctx2 ≤ v₂ =ᴮ y.func j' :=
    inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right)
  have hw12 : ctx2 ≤ w₁ =ᴮ w₂ := inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hφij : ctx2 ≤ (x.func i ∈ᴮ S ⟹ pair (x.func i) (y.func j) ∈ᴮ f) ⊓
      ((x.func i ∈ᴮ S)ᶜ ⟹ y.func j =ᴮ b) :=
    inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))
  have hφi'j' : ctx2 ≤ (x.func i' ∈ᴮ S ⟹ pair (x.func i') (y.func j') ∈ᴮ f) ⊓
      ((x.func i' ∈ᴮ S)ᶜ ⟹ y.func j' =ᴮ b) :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)

  have hxi_xi' : ctx2 ≤ x.func i =ᴮ x.func i' :=
    le_trans (le_inf (bv_symm hw1xi) (le_trans (le_inf hw12 hw2xi') bv_eq_trans)) bv_eq_trans

  have h_em_i : ctx2 ≤ x.func i ∈ᴮ S ⊔ (x.func i ∈ᴮ S)ᶜ := le_top.trans (by rw [sup_compl_eq_top])
  apply le_trans (le_inf le_rfl h_em_i)
  apply bv_or_elim_right
  ·
    have hmem_S : ctx2 ⊓ x.func i ∈ᴮ S ≤ x.func i ∈ᴮ S := inf_le_right
    have hpair1_f : _ ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
      le_trans (le_inf (inf_le_left.trans (hφij.trans inf_le_left)) hmem_S) bv_imp_elim
    have hmem_S' : _ ≤ x.func i' ∈ᴮ S :=
      bv_rw' (H := bv_symm (inf_le_left.trans hxi_xi')) (h_congr := B_ext_mem_left)
        (H_new := hmem_S)
    have hpair2_f : _ ≤ pair (x.func i') (y.func j') ∈ᴮ f :=
      le_trans (le_inf (inf_le_left.trans (hφi'j'.trans inf_le_left)) hmem_S') bv_imp_elim

    have his_func : ctx2 ⊓ x.func i ∈ᴮ S ≤ is_func f :=
      is_func_of_is_func' (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans
        (inf_le_left.trans (inf_le_left.trans (H_surj.trans inf_le_left))))))
    have hyfunc_eq : ctx2 ⊓ x.func i ∈ᴮ S ≤ y.func j =ᴮ y.func j' :=
      eq_of_is_func_of_eq his_func (inf_le_left.trans hxi_xi') hpair1_f hpair2_f

    exact le_trans (le_inf (le_trans (le_inf (inf_le_left.trans hv1yj) hyfunc_eq) bv_eq_trans)
          (bv_symm (inf_le_left.trans hv2yj')))
        bv_eq_trans
  ·
    have hnot_S : ctx2 ⊓ (x.func i ∈ᴮ S)ᶜ ≤ (x.func i ∈ᴮ S)ᶜ := inf_le_right
    have hyj_b : _ ≤ y.func j =ᴮ b :=
      le_trans (le_inf (inf_le_left.trans (hφij.trans inf_le_right)) hnot_S) bv_imp_elim

    have hnot_S' : _ ≤ (x.func i' ∈ᴮ S)ᶜ :=
      bv_rw' (H := bv_symm (inf_le_left.trans hxi_xi'))
        (h_congr := B_ext_neg (h := B_ext_mem_left (y := S))) (H_new := hnot_S)
    have hyj'_b : _ ≤ y.func j' =ᴮ b :=
      le_trans (le_inf (inf_le_left.trans (hφi'j'.trans inf_le_right)) hnot_S') bv_imp_elim

    exact le_trans (le_inf
          (le_trans (le_inf (inf_le_left.trans hv1yj) hyj_b) bv_eq_trans)
          (le_trans (le_inf (bv_symm hyj'_b) (bv_symm (inf_le_left.trans hv2yj'))) bv_eq_trans))
        bv_eq_trans

lemma pointed_extension_is_total {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_total x y (pointed_extension b H_b H_S H_surj) := by
  set pe := pointed_extension b H_b H_S H_surj
  set φ : (prod x y).type → 𝔹 := fun pr =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ y.func pr.2 =ᴮ b)

  have hmem_pe_of_bval : ∀ (i : x.type) (j : y.type),
      ∀ {Δ : 𝔹}, Δ ≤ x.bval i → Δ ≤ y.bval j → Δ ≤ φ (i, j) →
      Δ ≤ pair (x.func i) (y.func j) ∈ᴮ pe := by
    intro i j Δ hxi hyj hφ
    show Δ ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]
    apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]
    exact le_inf bv_refl (le_inf hφ (le_inf hxi hyj))

  rw [is_total_iff_is_total']
  apply le_iInf; intro i; rw [← deduction]

  have h_split_i : Γ ⊓ x.bval i ≤ (Γ ⊓ x.bval i) ⊓ x.func i ∈ᴮ S ⊔
      (Γ ⊓ x.bval i) ⊓ (x.func i ∈ᴮ S)ᶜ := by
    rw [← inf_sup_left]; simp [sup_compl_eq_top]
  apply le_trans h_split_i; apply bv_or_elim
  ·
    set ctx_iS := (Γ ⊓ x.bval i) ⊓ x.func i ∈ᴮ S
    have hxi_bval : ctx_iS ≤ x.bval i := inf_le_left.trans inf_le_right
    have hxi_mem_S : ctx_iS ≤ x.func i ∈ᴮ S := inf_le_right
    have htotal_S : ctx_iS ≤ is_total S y f :=
      is_total_of_is_func' (inf_le_left.trans (inf_le_left.trans (H_surj.trans inf_le_left)))
    have hget_v : _ ≤ ⨆ v₂, v₂ ∈ᴮ y ⊓ pair (x.func i) v₂ ∈ᴮ f :=
      le_trans (le_inf (le_trans htotal_S (iInf_le _ (x.func i))) hxi_mem_S) bv_imp_elim

    apply le_trans (le_inf hget_v le_rfl); rw [iSup_inf_eq']; apply iSup_le; intro v₂

    have hv2_mem_y : (v₂ ∈ᴮ y ⊓ pair (x.func i) v₂ ∈ᴮ f) ⊓ ctx_iS ≤ v₂ ∈ᴮ y :=
      inf_le_left.trans inf_le_left
    apply le_trans (le_inf (hv2_mem_y.trans (le_of_eq mem_unfold)) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro j

    set ctx_j := (y.bval j ⊓ v₂ =ᴮ y.func j) ⊓ ((v₂ ∈ᴮ y ⊓ pair (x.func i) v₂ ∈ᴮ f) ⊓ ctx_iS)
    have hyj_bval : ctx_j ≤ y.bval j := inf_le_left.trans inf_le_left
    have hv2_yj : ctx_j ≤ v₂ =ᴮ y.func j := inf_le_left.trans inf_le_right
    have hpair_f : ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
      bv_rw' (H := bv_symm hv2_yj) (h_congr := B_ext_pair_mem_right)
        (H_new := inf_le_right.trans (inf_le_left.trans inf_le_right))

    apply le_iSup_of_le j; refine le_inf hyj_bval ?_
    show ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]; apply le_iSup_of_le (i, j); simp only [prod_func, prod_bval]
    refine le_inf bv_refl (le_inf ?_
      (le_inf (inf_le_right.trans (inf_le_right.trans hxi_bval)) hyj_bval))

    exact le_inf
      (bv_imp_intro_lemma (le_trans inf_le_left hpair_f))
      (bv_imp_intro_lemma (bv_exfalso (le_trans
        (le_inf (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
          inf_le_right)
        (le_of_eq inf_compl_eq_bot))))
  ·
    set ctx_notS := (Γ ⊓ x.bval i) ⊓ (x.func i ∈ᴮ S)ᶜ
    have hxi_bval : ctx_notS ≤ x.bval i := inf_le_left.trans inf_le_right
    have hnot_S : ctx_notS ≤ (x.func i ∈ᴮ S)ᶜ := inf_le_right
    have hb_mem_y : ctx_notS ≤ b ∈ᴮ y := inf_le_left.trans (inf_le_left.trans H_b)

    apply le_trans (le_inf (hb_mem_y.trans (le_of_eq mem_unfold)) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro j
    set ctx_jn := (y.bval j ⊓ b =ᴮ y.func j) ⊓ ctx_notS
    have hyj_bval : ctx_jn ≤ y.bval j := inf_le_left.trans inf_le_left
    have hb_yj : ctx_jn ≤ b =ᴮ y.func j := inf_le_left.trans inf_le_right

    apply le_iSup_of_le j; refine le_inf hyj_bval ?_
    show ctx_jn ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]; apply le_iSup_of_le (i, j); simp only [prod_func, prod_bval]
    refine le_inf bv_refl (le_inf ?_ (le_inf (inf_le_right.trans hxi_bval) hyj_bval))

    exact le_inf
      (bv_imp_intro_lemma (bv_exfalso (le_trans
        (le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans inf_le_right)))
        (le_of_eq inf_compl_eq_bot))))
      (bv_imp_intro_lemma (bv_symm (inf_le_left.trans hb_yj)))

lemma pointed_extension_is_func' {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_func' x y (pointed_extension b H_b H_S H_surj) :=
  le_inf (pointed_extension_is_func H_b H_S H_surj)
         (pointed_extension_is_total H_b H_S H_surj)

lemma pointed_extension_is_surj {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_surj x y (pointed_extension b H_b H_S H_surj) := by
  set pe := pointed_extension b H_b H_S H_surj
  set φ : (prod x y).type → 𝔹 := fun pr =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ y.func pr.2 =ᴮ b)

  apply le_iInf; intro v; rw [← deduction]

  have hfunc'_Sf : Γ ⊓ v ∈ᴮ y ≤ is_func' S y f :=
    inf_le_left.trans (H_surj.trans inf_le_left)
  have hsurj_Sf : Γ ⊓ v ∈ᴮ y ≤ is_surj S y f :=
    inf_le_left.trans (H_surj.trans inf_le_right)
  have hv_mem_y : Γ ⊓ v ∈ᴮ y ≤ v ∈ᴮ y := inf_le_right
  have hget_w : _ ≤ ⨆ w, w ∈ᴮ S ⊓ pair w v ∈ᴮ f :=
    le_trans (le_inf (le_trans hsurj_Sf (iInf_le _ v)) hv_mem_y) bv_imp_elim

  apply le_trans (le_inf hget_w le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro w

  set ctx_w := (w ∈ᴮ S ⊓ pair w v ∈ᴮ f) ⊓ (Γ ⊓ v ∈ᴮ y)
  have hw_mem_S : ctx_w ≤ w ∈ᴮ S := inf_le_left.trans inf_le_left
  have hpair_wv_f : ctx_w ≤ pair w v ∈ᴮ f := inf_le_left.trans inf_le_right

  have hw_mem_x : ctx_w ≤ w ∈ᴮ x :=
    mem_of_mem_subset (inf_le_right.trans (inf_le_left.trans H_S)) hw_mem_S

  apply le_trans (le_inf (hw_mem_x.trans (le_of_eq mem_unfold)) le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro i

  set ctx_i := (x.bval i ⊓ w =ᴮ x.func i) ⊓ ctx_w
  have hxi_bval : ctx_i ≤ x.bval i := inf_le_left.trans inf_le_left
  have hw_xi : ctx_i ≤ w =ᴮ x.func i := inf_le_left.trans inf_le_right

  apply le_trans (le_inf ((inf_le_right.trans (inf_le_right.trans hv_mem_y)).trans
    (le_of_eq mem_unfold)) le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro j

  set ctx_j := (y.bval j ⊓ v =ᴮ y.func j) ⊓ ctx_i
  have hyj_bval : ctx_j ≤ y.bval j := inf_le_left.trans inf_le_left
  have hv_yj : ctx_j ≤ v =ᴮ y.func j := inf_le_left.trans inf_le_right

  have hxi_mem_S : ctx_j ≤ x.func i ∈ᴮ S :=
    bv_rw' (H := bv_symm (inf_le_right.trans hw_xi))
      (h_congr := B_ext_mem_left)
      (H_new := inf_le_right.trans (inf_le_right.trans hw_mem_S))

  have hpair_ij_f : ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
    bv_rw' (H := bv_symm (pair_congr (inf_le_right.trans hw_xi) hv_yj))
      (h_congr := B_ext_mem_left)
      (H_new := inf_le_right.trans (inf_le_right.trans hpair_wv_f))

  apply le_iSup_of_le (x.func i)
  refine le_inf ?_ ?_
  ·
    rw [mem_unfold]; apply le_iSup_of_le i
    exact le_inf (inf_le_right.trans hxi_bval) bv_refl
  ·
    apply bv_rw' (H := hv_yj) (h_congr := B_ext_pair_mem_right)
    show ctx_j ≤ pair (x.func i) (y.func j) ∈ᴮ subset.mk φ
    rw [mem_subset.mk_iff]; apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]
    refine le_inf bv_refl (le_inf ?_ (le_inf (inf_le_right.trans hxi_bval) hyj_bval))

    exact le_inf (bv_imp_intro_lemma (le_trans inf_le_left hpair_ij_f))
      (bv_imp_intro_lemma (bv_exfalso
        (le_trans (le_inf (inf_le_left.trans hxi_mem_S) inf_le_right)
          (le_of_eq inf_compl_eq_bot))))

lemma pointed_extension_spec {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ surjects_onto x y :=
  le_iSup_of_le (pointed_extension b H_b H_S H_surj)
    (le_inf (pointed_extension_is_func' H_b H_S H_surj)
            (pointed_extension_is_surj H_b H_S H_surj))

lemma surjects_onto_of_larger_than_and_exists_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (H_larger_than : Γ ≤ larger_than x y) (H_nonempty : Γ ≤ ⨆ w, w ∈ᴮ y) :
    Γ ≤ surjects_onto x y := by

  obtain ⟨b, Hb⟩ := exists_convert H_nonempty B_ext_mem_left

  simp only [larger_than] at H_larger_than
  apply le_trans (le_inf H_larger_than le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro S
  simp_rw [iSup_inf_eq']; apply iSup_le; intro f

  apply le_trans (le_inf (inf_le_right.trans Hb) le_rfl)

  apply pointed_extension_spec
  · exact inf_le_left
  · exact inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  ·
    exact le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
                 (inf_le_right.trans (inf_le_left.trans inf_le_right))

lemma larger_than_of_surjects_onto {x y : bSet 𝔹} {Γ} (H_surj : Γ ≤ surjects_onto x y) :
    Γ ≤ larger_than x y := by

  unfold larger_than
  apply le_trans H_surj
  apply iSup_le; intro f
  apply le_iSup_of_le x
  apply le_iSup_of_le f

  apply le_inf (le_inf ?_ inf_le_left) inf_le_right
  exact le_top.trans subset_self

lemma check_not_is_func {x y f : PSet.{u}} (H : ¬ PSet.is_func x y f) :
    ∀ {Γ : 𝔹}, (Γ ≤ is_function (check x) (check y) (check f) → Γ ≤ (⊥ : 𝔹)) := by
  rw [PSet.is_func_iff] at H
  simp only [not_and_or] at H
  intro Γ H'
  have H'_func' : Γ ≤ is_func' (check x) (check y) (check f) := H'.trans inf_le_left
  have H'_sub : Γ ≤ check f ⊆ᴮ prod (check x) (check y) := H'.trans inf_le_right
  rcases H with H_notsubset | H_notfunc
  ·
    have h_notsubset : (Γ : 𝔹) ≤ (check f ⊆ᴮ check (PSet.pSet_prod x y))ᶜ :=
      check_not_subset H_notsubset
    have h_subset : Γ ≤ check f ⊆ᴮ check (PSet.pSet_prod x y) :=
      le_trans (le_inf H'_sub (bv_symm check_pset_prod)) subst_congr_subset_right
    exact le_trans (le_inf h_subset h_notsubset) (le_of_eq inf_compl_eq_bot)
  ·
    push Not at H_notfunc
    obtain ⟨z, Hz_mem, Hz⟩ := H_notfunc

    have h_z_mem : (Γ : 𝔹) ≤ check z ∈ᴮ check x := check_mem Hz_mem
    have H_total := is_total_of_is_func' H'_func'
    have h_ex : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check z) w ∈ᴮ check f :=
      le_trans (le_inf (le_trans H_total (iInf_le _ (check z))) h_z_mem) bv_imp_elim

    suffices h : Γ ≤ ⊥ from h
    by_contra H_nonzero
    have H_nonzero' : ⊥ < Γ := bot_lt_iff_ne_bot.mpr
      (fun heq => H_nonzero (heq.symm ▸ le_refl ⊥))

    let i_y := @instantiate_existential_over_check 𝔹 _ (fun w => pair (check z) w ∈ᴮ check f)
        B_ext_pair_mem_right y Γ H_nonzero' h_ex

    have HΓ'_pos := @instantiate_existential_over_check_spec 𝔹 _
        (fun w => pair (check z) w ∈ᴮ check f) B_ext_pair_mem_right y Γ H_nonzero' h_ex

    let Γ' := pair (check z) (check (y.Func i_y)) ∈ᴮ check f ⊓ Γ
    have HΓ'_le_Γ : Γ' ≤ Γ := inf_le_right
    have HΓ'_le_pair : Γ' ≤ pair (check z) (check (y.Func i_y)) ∈ᴮ check f := inf_le_left
    have HΓ'_func' : Γ' ≤ is_func' (check x) (check y) (check f) := HΓ'_le_Γ.trans H'_func'

    rcases Classical.em (PSet.pSet_pair z (y.Func i_y) ∈ f) with H_mem_pset | H_notmem_pset
    ·
      obtain ⟨b, Hb_mem, Hb_neq⟩ := Hz _ H_mem_pset
      have H_neq : Γ' ≤ (check b =ᴮ check (y.Func i_y))ᶜ :=
        le_trans le_top (check_not_eq Hb_neq)
      have H_b_pair_mem : Γ' ≤ pair (check z) (check b) ∈ᴮ check f := by
        exact le_trans le_top (by rw [← check_pset_pair_eq]; exact check_mem Hb_mem)
      have H_eq : Γ' ≤ check b =ᴮ check (y.Func i_y) :=
        eq_of_is_func_of_eq (is_func_of_is_func' HΓ'_func') bv_refl H_b_pair_mem HΓ'_le_pair
      exact false_of_bot_lt_and_le_bot HΓ'_pos
        (le_trans (le_inf H_eq H_neq) (le_of_eq inf_compl_eq_bot))
    ·
      rw [← check_pset_pair_eq] at HΓ'_le_pair
      exact false_of_bot_lt_and_le_bot HΓ'_pos (check_not_mem H_notmem_pset HΓ'_le_pair)

lemma check_not_is_surj {x y f : PSet.{u}} (H : ¬ PSet.is_surj x y f) :
    ∀ {Γ : 𝔹}, Γ ≤ is_surj (check x) (check y) (check f) → Γ ≤ (⊥ : 𝔹) := by

  simp only [PSet.is_surj] at H
  push Not at H
  obtain ⟨b, Hb₁, Hb₂⟩ := H

  have Hb₂' : ∀ a : PSet.{u}, a ∈ x → PSet.pSet_pair a b ∉ f := by
    intro a ha hm
    apply Hb₂ a ha
    rwa [← PSet.pSet_pair_sound, ← PSet.mem_iff]
  intro Γ H_surj

  have hb_mem : Γ ≤ check b ∈ᴮ check y := check_mem Hb₁
  have h_spec : Γ ≤ check b ∈ᴮ check y ⟹ ⨆ w, w ∈ᴮ check x ⊓ pair w (check b) ∈ᴮ check f :=
    le_trans H_surj (iInf_le _ (check b))
  have h_ex : Γ ≤ ⨆ w, w ∈ᴮ check x ⊓ pair w (check b) ∈ᴮ check f :=
    le_trans (le_inf h_spec hb_mem) bv_imp_elim

  rw [← @bounded_exists _ _ (check x) (fun w => pair w (check b) ∈ᴮ check f)
      (h_congr := B_ext_pair_mem_left)] at h_ex

  apply le_trans h_ex
  apply iSup_le; intro i_a
  simp only [check_bval_top, top_inf_eq, check_func]

  have hxa_mem : x.Func (check_cast i_a) ∈ x := PSet.func_mem x (check_cast i_a)
  have hpair_not : PSet.pSet_pair (x.Func (check_cast i_a)) b ∉ f := Hb₂' _ hxa_mem
  rw [← check_pset_pair_eq]
  exact check_not_mem hpair_not le_rfl

lemma bot_lt_of_true {b : 𝔹} (H : ∀ {Γ}, Γ ≤ b) : ⊥ < b := by
  have := @H ⊤
  rw [top_le_iff] at this
  simp [this]

def lift_surj_inj {x z f g : bSet 𝔹} (y : bSet 𝔹) {Γ : 𝔹}
    (_H_surj : Γ ≤ is_surj x z f) (_H_inj : Γ ≤ is_inj g) : bSet 𝔹 :=
  @subset.mk _ _ (prod x y)
    (fun p => ⨆ w, w ∈ᴮ z ⊓ (pair (x.func p.1) w) ∈ᴮ f ⊓
                           (pair (y.func p.2) w ∈ᴮ g))

lemma ex_witness_of_mem_lift_surj_inj {x y z f g : bSet 𝔹} {Γ : 𝔹} {w₁ w₂ : bSet 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (_H_is_func'_f : Γ ≤ is_func' x z f)
    (H : Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj)) :
    Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) := by
  unfold lift_surj_inj at H
  rw [mem_subset.mk_iff] at H
  apply H.trans
  apply iSup_le; intro pr; obtain ⟨i, j⟩ := pr
  simp only [prod_func, prod_bval]

  have hw1 : pair w₁ w₂ =ᴮ pair (x.func i) (y.func j) ⊓
      ((⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g) ⊓ (x.bval i ⊓ y.bval j))
      ≤ w₁ =ᴮ x.func i :=
    inf_le_left.trans eq_of_eq_pair_left
  have hw2 : pair w₁ w₂ =ᴮ pair (x.func i) (y.func j) ⊓
      ((⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g) ⊓ (x.bval i ⊓ y.bval j))
      ≤ w₂ =ᴮ y.func j :=
    inf_le_left.trans eq_of_eq_pair_right
  have hsupr : pair w₁ w₂ =ᴮ pair (x.func i) (y.func j) ⊓
      ((⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g) ⊓ (x.bval i ⊓ y.bval j))
      ≤ ⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g :=
    inf_le_right.trans inf_le_left

  apply (le_inf hsupr le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans
  apply iSup_le; intro w
  apply le_iSup_of_le w

  refine le_inf (le_inf ?_ ?_) ?_
  ·
    exact inf_le_left.trans (inf_le_left.trans inf_le_left)
  ·

    exact bv_rw' (H := inf_le_right.trans hw1) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_left.trans (inf_le_left.trans inf_le_right))
  ·
    exact bv_rw' (H := inf_le_right.trans hw2) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_left.trans inf_le_right)

lemma mem_lift_surj_inj_iff {x y z f g : bSet 𝔹} {Γ : 𝔹} {w₁ w₂ : bSet 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_is_func'_f : Γ ≤ is_func' x z f) {H_mem₁ : Γ ≤ w₁ ∈ᴮ x} {H_mem₂ : Γ ≤ w₂ ∈ᴮ y} :
    Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj) ↔
      Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) := by
  constructor
  · exact ex_witness_of_mem_lift_surj_inj H_is_func'_f
  · intro H_ex

    rw [mem_unfold] at H_mem₁ H_mem₂

    apply le_trans (le_inf (le_inf H_ex H_mem₁) H_mem₂)
    rw [inf_iSup_eq']; apply iSup_le; intro j
    rw [inf_iSup_eq', iSup_inf_eq']; apply iSup_le; intro i
    rw [iSup_inf_eq', iSup_inf_eq']; apply iSup_le; intro w

    have hw1xi : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
        (y.bval j ⊓ w₂ =ᴮ y.func j) ≤ w₁ =ᴮ x.func i :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hw2yj : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
        (y.bval j ⊓ w₂ =ᴮ y.func j) ≤ w₂ =ᴮ y.func j :=
      inf_le_right.trans inf_le_right

    have hmem_ij : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
        (y.bval j ⊓ w₂ =ᴮ y.func j) ≤
        pair (x.func i) (y.func j) ∈ᴮ lift_surj_inj y H_surj H_inj := by
      unfold lift_surj_inj; rw [mem_subset.mk_iff]
      apply le_iSup_of_le (i, j)

      simp only [bv_eq_refl, prod_func, prod_bval, top_inf_eq]

      have hDw : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
          (y.bval j ⊓ w₂ =ᴮ y.func j) ≤
          w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g := inf_le_left.trans inf_le_left
      refine le_inf ?_ ?_
      · apply bv_use w
        refine le_inf (le_inf ?_ ?_) ?_
        · exact hDw.trans (inf_le_left.trans inf_le_left)
        · exact bv_rw' (H := bv_symm hw1xi) (h_congr := B_ext_pair_mem_left)
            (H_new := hDw.trans (inf_le_left.trans inf_le_right))
        · exact bv_rw' (H := bv_symm hw2yj) (h_congr := B_ext_pair_mem_left)
            (H_new := hDw.trans inf_le_right)
      · exact le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left))
          (inf_le_right.trans inf_le_left)

    exact subst_congr_mem_left' (bv_symm (pair_congr hw1xi hw2yj)) hmem_ij

lemma lift_surj_inj_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_is_func_f : Γ ≤ is_func' x z f) :
    Γ ≤ is_func (lift_surj_inj y H_surj H_inj) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]

  have H_gr₁ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤
      ⨆ c₁, (c₁ ∈ᴮ z ⊓ pair w₁ c₁ ∈ᴮ f ⊓ pair v₁ c₁ ∈ᴮ g) :=
    inf_le_left.trans (@ex_witness_of_mem_lift_surj_inj 𝔹 _ x y z f g
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
             pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj))
      w₁ v₁ (le_trans inf_le_left H_surj) (le_trans inf_le_left H_inj)
      (le_trans inf_le_left H_is_func_f) (inf_le_right.trans inf_le_left))
  have H_gr₂ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤
      ⨆ c₂, (c₂ ∈ᴮ z ⊓ pair w₂ c₂ ∈ᴮ f ⊓ pair v₂ c₂ ∈ᴮ g) :=
    inf_le_left.trans (@ex_witness_of_mem_lift_surj_inj 𝔹 _ x y z f g
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
             pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj))
      w₂ v₂ (le_trans inf_le_left H_surj) (le_trans inf_le_left H_inj)
      (le_trans inf_le_left H_is_func_f) (inf_le_right.trans inf_le_right))

  obtain ⟨c₁, Hc₁⟩ := exists_convert H_gr₁
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_pair_mem_right) B_ext_pair_mem_right)
  obtain ⟨c₂, Hc₂⟩ := exists_convert H_gr₂
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_pair_mem_right) B_ext_pair_mem_right)

  have hw₁c₁_f : _ ≤ pair w₁ c₁ ∈ᴮ f := Hc₁.trans (inf_le_left.trans inf_le_right)
  have hw₂c₂_f : _ ≤ pair w₂ c₂ ∈ᴮ f := Hc₂.trans (inf_le_left.trans inf_le_right)
  have hv₁c₁_g : _ ≤ pair v₁ c₁ ∈ᴮ g := Hc₁.trans inf_le_right
  have hv₂c₂_g : _ ≤ pair v₂ c₂ ∈ᴮ g := Hc₂.trans inf_le_right
  have hw₁w₂ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ w₂ := inf_le_right

  have hfunc' : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤ is_func' x z f :=
    inf_le_left.trans (inf_le_left.trans H_is_func_f)
  have hinj : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤ is_inj g :=
    inf_le_left.trans (inf_le_left.trans H_inj)
  have hc₁c₂ := eq_of_is_func'_of_eq hfunc' hw₁w₂ hw₁c₁_f hw₂c₂_f
  exact eq_of_is_inj_of_eq hinj hc₁c₂ hv₁c₁_g hv₂c₂_g

lemma lift_surj_inj_is_total {y z f g S : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g) (H_is_func_f : Γ ≤ is_func' S z f) :
    Γ ≤ is_total (subset.mk (fun i : S.type =>
      ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y
      (lift_surj_inj y H_surj H_inj) := by
  unfold is_total
  apply le_iInf; intro w₁; rw [← deduction]

  apply le_trans (le_inf (mem_subset.mk_iff.mp inf_le_right) le_rfl)

  rw [iSup_inf_eq']; apply iSup_le; intro i

  apply le_trans (le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left)) le_rfl)

  rw [iSup_inf_eq']; apply iSup_le; intro b

  apply le_iSup_of_le b
  refine le_inf (inf_le_left.trans inf_le_left) ?_

  have H_b_mem_y : (b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g) ⊓
      ((w₁ =ᴮ S.func i ⊓ ((⨆ b', b' ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓
        pair b' c ∈ᴮ g) ⊓ S.bval i)) ⊓
        (Γ ⊓ w₁ ∈ᴮ subset.mk (fun i : S.type =>
          ⨆ b', b' ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b' c ∈ᴮ g))) ≤
      ⨆ j : y.type, y.bval j ⊓ b =ᴮ y.func j := by
    rw [← mem_unfold]; exact inf_le_left.trans inf_le_left
  apply le_trans (le_inf H_b_mem_y le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro j

  apply subst_congr_mem_left' (bv_symm (pair_congr
    (show _ ≤ w₁ =ᴮ S.func i from inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    (show _ ≤ b =ᴮ y.func j from inf_le_left.trans inf_le_right)))

  unfold lift_surj_inj; rw [mem_subset.mk_iff]
  apply le_iSup_of_le (i, j)
  simp only [bv_eq_refl, prod_func, prod_bval, top_inf_eq]

  refine le_inf ?_ (le_inf ?_ ?_)
  ·
    apply le_trans (le_inf (inf_le_right.trans (inf_le_left.trans inf_le_right)) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro c
    apply le_iSup_of_le c
    refine le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))) ?_

    exact bv_rw' (H := bv_symm (inf_le_right.trans (inf_le_left.trans inf_le_right)))
      (ϕ := fun w => pair w c ∈ᴮ g) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_left.trans inf_le_right)
  ·
    exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_right)))
  ·
    exact inf_le_left.trans inf_le_left

lemma lift_surj_inj_is_surj {y z f g S : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g)
    (H_is_func_f : Γ ≤ is_func' S z f) (H_is_func_g : Γ ≤ is_func' y z g) :
    Γ ≤ is_surj (subset.mk (fun i : S.type =>
      ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y
      (lift_surj_inj y H_surj H_inj) := by
  unfold is_surj
  apply le_iInf; intro b; rw [← deduction]

  have H_tot_g : Γ ⊓ b ∈ᴮ y ≤ ⨆ w₂, w₂ ∈ᴮ z ⊓ pair b w₂ ∈ᴮ g :=
    le_trans (le_inf (inf_le_left.trans (le_trans (is_total_of_is_func' H_is_func_g)
      (iInf_le _ b))) inf_le_right) bv_imp_elim
  obtain ⟨w₂, Hw₂⟩ := exists_convert H_tot_g
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

  have H_surj_w₂ : Γ ⊓ b ∈ᴮ y ≤ ⨆ v, v ∈ᴮ S ⊓ pair v w₂ ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (le_trans H_surj (iInf_le _ w₂)))
      (Hw₂.trans inf_le_left)) bv_imp_elim
  obtain ⟨v, Hv⟩ := exists_convert H_surj_w₂
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)

  apply le_iSup_of_le v
  refine le_inf ?_ ?_
  ·
    have Hv_mem_S : Γ ⊓ b ∈ᴮ y ≤ ⨆ i : S.type, S.bval i ⊓ v =ᴮ S.func i := by
      rw [← mem_unfold]; exact Hv.trans inf_le_left

    apply le_trans (le_inf Hv_mem_S le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro i

    rw [mem_subset.mk_iff]
    apply le_iSup_of_le i

    refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))

    apply le_iSup_of_le b
    refine le_inf (inf_le_right.trans inf_le_right) ?_
    apply le_iSup_of_le w₂
    refine le_inf (le_inf (inf_le_right.trans (Hw₂.trans inf_le_left)) ?_)
      (inf_le_right.trans (Hw₂.trans inf_le_right))

    exact bv_rw' (H := bv_symm (inf_le_left.trans inf_le_right))
      (ϕ := fun w => pair w w₂ ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_right.trans (Hv.trans inf_le_right))
  ·

    apply (mem_lift_surj_inj_iff (H_surj := le_trans inf_le_left H_surj)
        (H_inj := le_trans inf_le_left H_inj)
        (H_is_func'_f := le_trans inf_le_left H_is_func_f)
        (H_mem₁ := Hv.trans inf_le_left)
        (H_mem₂ := inf_le_right)).mpr
    apply le_iSup_of_le w₂
    exact le_inf (le_inf (Hw₂.trans inf_le_left) (Hv.trans inf_le_right))
      (Hw₂.trans inf_le_right)

def extend_surj_inj {x z f g : bSet 𝔹} (y : bSet 𝔹) {Γ : 𝔹}
    (_H_surj : Γ ≤ is_surj x z f) (_H_inj : Γ ≤ is_inj g) : bSet 𝔹 :=
  @subset.mk _ _ (prod y z)
    (fun p => ⨆ w, w ∈ᴮ x ⊓ (pair w (z.func p.2)) ∈ᴮ f ⊓
                           (pair w (y.func p.1) ∈ᴮ g))

lemma ex_witness_of_mem_extend_surj_inj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    {w₁ w₂ : bSet 𝔹}
    (H_is_func'_f : Γ ≤ is_func' x z f)
    (H : Γ ≤ pair w₁ w₂ ∈ᴮ extend_surj_inj y H_surj H_inj) :
    Γ ≤ ⨆ w, (w ∈ᴮ x ⊓ (pair w w₁ ∈ᴮ g) ⊓ (pair w w₂ ∈ᴮ f)) := by
  unfold extend_surj_inj at H
  rw [mem_subset.mk_iff] at H
  apply H.trans
  apply iSup_le; intro pr; obtain ⟨i, j⟩ := pr
  simp only [prod_func, prod_bval]

  have hw1 : pair w₁ w₂ =ᴮ pair (y.func i) (z.func j) ⊓
      ((⨆ w, w ∈ᴮ x ⊓ pair w (z.func j) ∈ᴮ f ⊓ pair w (y.func i) ∈ᴮ g) ⊓ (y.bval i ⊓ z.bval j))
      ≤ w₁ =ᴮ y.func i := inf_le_left.trans eq_of_eq_pair_left
  have hw2 : pair w₁ w₂ =ᴮ pair (y.func i) (z.func j) ⊓
      ((⨆ w, w ∈ᴮ x ⊓ pair w (z.func j) ∈ᴮ f ⊓ pair w (y.func i) ∈ᴮ g) ⊓ (y.bval i ⊓ z.bval j))
      ≤ w₂ =ᴮ z.func j := inf_le_left.trans eq_of_eq_pair_right
  have hsupr : pair w₁ w₂ =ᴮ pair (y.func i) (z.func j) ⊓
      ((⨆ w, w ∈ᴮ x ⊓ pair w (z.func j) ∈ᴮ f ⊓ pair w (y.func i) ∈ᴮ g) ⊓ (y.bval i ⊓ z.bval j))
      ≤ ⨆ w, w ∈ᴮ x ⊓ pair w (z.func j) ∈ᴮ f ⊓ pair w (y.func i) ∈ᴮ g :=
    inf_le_right.trans inf_le_left
  apply (le_inf hsupr le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans
  apply iSup_le; intro w
  apply le_iSup_of_le w

  refine le_inf (le_inf ?_ ?_) ?_
  ·
    exact inf_le_left.trans (inf_le_left.trans inf_le_left)
  ·
    exact bv_rw' (H := inf_le_right.trans hw1) (h_congr := B_ext_pair_mem_right)
      (H_new := inf_le_left.trans inf_le_right)
  ·
    exact bv_rw' (H := inf_le_right.trans hw2) (h_congr := B_ext_pair_mem_right)
      (H_new := inf_le_left.trans (inf_le_left.trans inf_le_right))

lemma mem_extend_surj_inj_iff {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    {w₁ w₂ : bSet 𝔹}
    {H_mem₁ : Γ ≤ w₁ ∈ᴮ y} {H_mem₂ : Γ ≤ w₂ ∈ᴮ z}
    (H_is_func'_f : Γ ≤ is_func' x z f) :
    Γ ≤ pair w₁ w₂ ∈ᴮ extend_surj_inj y H_surj H_inj ↔
      Γ ≤ ⨆ w, (w ∈ᴮ x ⊓ (pair w w₁ ∈ᴮ g) ⊓ (pair w w₂ ∈ᴮ f)) := by
  constructor
  · exact ex_witness_of_mem_extend_surj_inj H_is_func'_f
  · intro H_ex
    rw [mem_unfold] at H_mem₁ H_mem₂
    apply le_trans (le_inf (le_inf H_ex H_mem₁) H_mem₂)
    rw [inf_iSup_eq']; apply iSup_le; intro j
    rw [inf_iSup_eq', iSup_inf_eq']; apply iSup_le; intro i
    rw [iSup_inf_eq', iSup_inf_eq']; apply iSup_le; intro w
    have hw1yi : (w ∈ᴮ x ⊓ pair w w₁ ∈ᴮ g ⊓ pair w w₂ ∈ᴮ f ⊓ (y.bval i ⊓ w₁ =ᴮ y.func i)) ⊓
        (z.bval j ⊓ w₂ =ᴮ z.func j) ≤ w₁ =ᴮ y.func i :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hw2zj : (w ∈ᴮ x ⊓ pair w w₁ ∈ᴮ g ⊓ pair w w₂ ∈ᴮ f ⊓ (y.bval i ⊓ w₁ =ᴮ y.func i)) ⊓
        (z.bval j ⊓ w₂ =ᴮ z.func j) ≤ w₂ =ᴮ z.func j :=
      inf_le_right.trans inf_le_right
    have hmem_ij : (w ∈ᴮ x ⊓ pair w w₁ ∈ᴮ g ⊓ pair w w₂ ∈ᴮ f ⊓ (y.bval i ⊓ w₁ =ᴮ y.func i)) ⊓
        (z.bval j ⊓ w₂ =ᴮ z.func j) ≤
        pair (y.func i) (z.func j) ∈ᴮ extend_surj_inj y H_surj H_inj := by
      unfold extend_surj_inj; rw [mem_subset.mk_iff]
      apply le_iSup_of_le (i, j)
      simp only [bv_eq_refl, prod_func, prod_bval, top_inf_eq]
      have hDw : (w ∈ᴮ x ⊓ pair w w₁ ∈ᴮ g ⊓ pair w w₂ ∈ᴮ f ⊓ (y.bval i ⊓ w₁ =ᴮ y.func i)) ⊓
          (z.bval j ⊓ w₂ =ᴮ z.func j) ≤
          w ∈ᴮ x ⊓ pair w w₁ ∈ᴮ g ⊓ pair w w₂ ∈ᴮ f := inf_le_left.trans inf_le_left
      refine le_inf ?_ ?_
      · apply bv_use w
        refine le_inf (le_inf ?_ ?_) ?_
        · exact hDw.trans (inf_le_left.trans inf_le_left)
        · exact bv_rw' (H := bv_symm hw2zj) (h_congr := B_ext_pair_mem_right)
            (H_new := hDw.trans inf_le_right)
        · exact bv_rw' (H := bv_symm hw1yi) (h_congr := B_ext_pair_mem_right)
            (H_new := hDw.trans (inf_le_left.trans inf_le_right))
      · exact le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left))
          (inf_le_right.trans inf_le_left)
    exact subst_congr_mem_left' (bv_symm (pair_congr hw1yi hw2zj)) hmem_ij

lemma extend_surj_inj_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_f_is_func' : Γ ≤ is_func' x z f) (H_g_is_func' : Γ ≤ is_func' x y g) :
    Γ ≤ is_func (extend_surj_inj y H_surj H_inj) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]

  have H_gr₁ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ extend_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ extend_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤
      ⨆ u, (u ∈ᴮ x ⊓ pair u w₁ ∈ᴮ g ⊓ pair u v₁ ∈ᴮ f) :=
    inf_le_left.trans (@ex_witness_of_mem_extend_surj_inj 𝔹 _ x y z f g
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ extend_surj_inj y H_surj H_inj ⊓
             pair w₂ v₂ ∈ᴮ extend_surj_inj y H_surj H_inj))
      (le_trans inf_le_left H_surj) (le_trans inf_le_left H_inj)
      w₁ v₁ (le_trans inf_le_left H_f_is_func') (inf_le_right.trans inf_le_left))
  have H_gr₂ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ extend_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ extend_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤
      ⨆ u, (u ∈ᴮ x ⊓ pair u w₂ ∈ᴮ g ⊓ pair u v₂ ∈ᴮ f) :=
    inf_le_left.trans (@ex_witness_of_mem_extend_surj_inj 𝔹 _ x y z f g
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ extend_surj_inj y H_surj H_inj ⊓
             pair w₂ v₂ ∈ᴮ extend_surj_inj y H_surj H_inj))
      (le_trans inf_le_left H_surj) (le_trans inf_le_left H_inj)
      w₂ v₂ (le_trans inf_le_left H_f_is_func') (inf_le_right.trans inf_le_right))
  obtain ⟨u₁, Hu₁⟩ := exists_convert H_gr₁
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_pair_mem_left) B_ext_pair_mem_left)
  obtain ⟨u₂, Hu₂⟩ := exists_convert H_gr₂
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_pair_mem_left) B_ext_pair_mem_left)

  have hu₁g : _ ≤ pair u₁ w₁ ∈ᴮ g := Hu₁.trans (inf_le_left.trans inf_le_right)
  have hu₂g : _ ≤ pair u₂ w₂ ∈ᴮ g := Hu₂.trans (inf_le_left.trans inf_le_right)
  have hu₁f : _ ≤ pair u₁ v₁ ∈ᴮ f := Hu₁.trans inf_le_right
  have hu₂f : _ ≤ pair u₂ v₂ ∈ᴮ f := Hu₂.trans inf_le_right
  have hw₁w₂ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ extend_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ extend_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ w₂ := inf_le_right

  have hu₁u₂ := eq_of_is_inj_of_eq
    (inf_le_left.trans (inf_le_left.trans H_inj) : _ ≤ is_inj g) hw₁w₂ hu₁g hu₂g

  exact eq_of_is_func'_of_eq
    (inf_le_left.trans (inf_le_left.trans H_f_is_func') : _ ≤ is_func' x z f)
    hu₁u₂ hu₁f hu₂f

lemma extend_surj_inj_is_total {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_f_is_func' : Γ ≤ is_func' x z f) (H_g_is_func' : Γ ≤ is_func' x y g) :
    Γ ≤ is_total (image x y g) z (extend_surj_inj y H_surj H_inj) := by
  unfold is_total
  apply le_iInf; intro w₁; rw [← deduction]

  have Hw₁_mem_y : Γ ⊓ w₁ ∈ᴮ image x y g ≤ w₁ ∈ᴮ y :=
    mem_of_mem_subset (inf_le_left.trans image_subset) inf_le_right
  have Hw₁_iSup : Γ ⊓ w₁ ∈ᴮ image x y g ≤ ⨆ b', b' ∈ᴮ x ⊓ pair b' w₁ ∈ᴮ g :=
    (mem_image_iff.mp inf_le_right).2

  obtain ⟨b', Hb'⟩ := exists_convert Hw₁_iSup
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)

  have H_tot_f : Γ ⊓ w₁ ∈ᴮ image x y g ≤ ⨆ b, b ∈ᴮ z ⊓ pair b' b ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (le_trans (is_total_of_is_func' H_f_is_func')
      (iInf_le _ b'))) (Hb'.trans inf_le_left)) bv_imp_elim
  obtain ⟨b, Hb⟩ := exists_convert H_tot_f
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

  apply le_iSup_of_le b
  refine le_inf (Hb.trans inf_le_left) ?_

  apply (mem_extend_surj_inj_iff (H_surj := inf_le_left.trans H_surj)
      (H_inj := inf_le_left.trans H_inj)
      (H_mem₁ := Hw₁_mem_y)
      (H_mem₂ := Hb.trans inf_le_left)
      (H_is_func'_f := inf_le_left.trans H_f_is_func')).mpr
  apply le_iSup_of_le b'
  refine le_inf (le_inf (Hb'.trans inf_le_left) ?_) (Hb.trans inf_le_right)

  exact Hb'.trans inf_le_right

lemma extend_surj_inj_is_surj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_f_is_func' : Γ ≤ is_func' x z f) (H_g_is_func' : Γ ≤ is_func' x y g) :
    Γ ≤ is_surj (image x y g) z (extend_surj_inj y H_surj H_inj) := by
  unfold is_surj
  apply le_iInf; intro b'; rw [← deduction]

  have H_surj_b' : Γ ⊓ b' ∈ᴮ z ≤ ⨆ b, b ∈ᴮ x ⊓ pair b b' ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (le_trans H_surj (iInf_le _ b'))) inf_le_right) bv_imp_elim
  obtain ⟨b, Hb⟩ := exists_convert H_surj_b'
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)

  have H_tot_g : Γ ⊓ b' ∈ᴮ z ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair b w₂ ∈ᴮ g :=
    le_trans (le_inf (inf_le_left.trans (le_trans (is_total_of_is_func' H_g_is_func')
      (iInf_le _ b))) (Hb.trans inf_le_left)) bv_imp_elim
  obtain ⟨w₂, Hw₂⟩ := exists_convert H_tot_g
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

  apply le_iSup_of_le w₂
  refine le_inf ?_ ?_
  ·
    exact mem_image (Hw₂.trans inf_le_right) (Hb.trans inf_le_left) (Hw₂.trans inf_le_left)
  ·
    apply (mem_extend_surj_inj_iff (H_surj := inf_le_left.trans H_surj)
        (H_inj := inf_le_left.trans H_inj)
        (H_mem₁ := Hw₂.trans inf_le_left)
        (H_mem₂ := inf_le_right)
        (H_is_func'_f := inf_le_left.trans H_f_is_func')).mpr
    apply le_iSup_of_le b
    exact le_inf (le_inf (Hb.trans inf_le_left) (Hw₂.trans inf_le_right)) (Hb.trans inf_le_right)

lemma bSet_lt_of_lt_of_le {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ (larger_than x y)ᶜ) (H₂ : Γ ≤ injects_into y z) :
    Γ ≤ (larger_than x z)ᶜ := by

  simp only [← imp_bot]; rw [← deduction]

  have H₁' : Γ ⊓ larger_than x y ≤ ⊥ := by
    simp only [← imp_bot] at H₁; rwa [← deduction] at H₁

  apply le_trans _ H₁'
  apply le_inf inf_le_left

  simp only [larger_than, injects_into] at *

  apply le_trans (le_inf inf_le_right (inf_le_left.trans H₂))

  rw [iSup_inf_eq']; simp_rw [inf_iSup_eq']; apply iSup_le; intro S; apply iSup_le; intro g
  simp_rw [iSup_inf_eq']; apply iSup_le; intro f

  have H_func_f : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_func' S z f :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have H_surj_f : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_surj S z f :=
    inf_le_left.trans inf_le_right
  have H_sub_x : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ S ⊆ᴮ x :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have H_inj_g : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_inj g :=
    inf_le_right.trans inf_le_right
  have H_func_g : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_func' y z g :=
    inf_le_right.trans inf_le_left
  apply le_iSup_of_le (subset.mk (fun i : S.type =>
    ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g))
  apply le_iSup_of_le (lift_surj_inj y H_surj_f H_inj_g)
  refine le_inf (le_inf (subset_trans' subset.mk_subset H_sub_x) (le_inf ?_ ?_)) ?_
  · exact lift_surj_inj_is_func H_func_f
  · exact lift_surj_inj_is_total H_surj_f H_inj_g H_func_f
  · exact lift_surj_inj_is_surj H_surj_f H_inj_g H_func_f H_func_g

lemma bSet_lt_of_le_of_lt {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ injects_into x y) (H₂ : Γ ≤ (larger_than y z)ᶜ) :
    Γ ≤ (larger_than x z)ᶜ := by
  simp only [← imp_bot]; rw [← deduction]

  have H₂' : Γ ⊓ larger_than y z ≤ ⊥ := by
    simp only [← imp_bot] at H₂; rwa [← deduction] at H₂

  apply le_trans _ H₂'
  apply le_inf inf_le_left

  simp only [larger_than, injects_into] at *

  apply le_trans (le_inf inf_le_right (inf_le_left.trans H₁))

  rw [iSup_inf_eq']; simp_rw [inf_iSup_eq']; apply iSup_le; intro S; apply iSup_le; intro g
  simp_rw [iSup_inf_eq']; apply iSup_le; intro f

  have H_func_f : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' x y g ⊓ is_inj g) ≤ is_func' S z f :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have H_surj_f : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' x y g ⊓ is_inj g) ≤ is_surj S z f :=
    inf_le_left.trans inf_le_right
  have H_sub_x : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' x y g ⊓ is_inj g) ≤ S ⊆ᴮ x :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have H_inj_g : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' x y g ⊓ is_inj g) ≤ is_inj g :=
    inf_le_right.trans inf_le_right
  have H_func_g_x : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' x y g ⊓ is_inj g) ≤ is_func' x y g :=
    inf_le_right.trans inf_le_left

  have H_func_g_S := is_func'_subset_of_is_func' H_func_g_x H_sub_x
  apply le_iSup_of_le (image S y g)
  apply le_iSup_of_le (extend_surj_inj y H_surj_f H_inj_g)
  refine le_inf (le_inf subset.mk_subset (le_inf ?_ ?_)) ?_
  · exact extend_surj_inj_is_func H_func_f H_func_g_S
  · exact extend_surj_inj_is_total H_func_f H_func_g_S
  · exact extend_surj_inj_is_surj H_func_f H_func_g_S

def is_func'_comp {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (_Hf_func : Γ ≤ is_func' x y f) (_Hg_func : Γ ≤ is_func' y z g) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x z).type =>
    ⨆ b, b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓ pair b (z.func pr.2) ∈ᴮ g)

lemma mem_is_func'_comp_iff {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) {Γ' : 𝔹} {a c : bSet 𝔹} :
    Γ' ≤ pair a c ∈ᴮ is_func'_comp Hf_func Hg_func ↔
      Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ c ∈ᴮ z ∧ Γ' ≤ ⨆ b, b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g) := by
  simp only [is_func'_comp]
  constructor
  · intro H

    have H_ac_prod : Γ' ≤ pair a c ∈ᴮ prod x z :=
      mem_of_mem_subset subset.mk_subset H
    refine ⟨(mem_prod_iff.mp H_ac_prod).1, (mem_prod_iff.mp H_ac_prod).2, ?_⟩

    have H_iSup := mem_subset.mk_iff.mp H

    apply le_trans (le_inf H_iSup le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro ⟨i, k⟩
    simp only [prod_func, prod_bval]

    have H_eq : (pair a c =ᴮ pair (x.func i) (z.func k) ⊓
        ((⨆ b, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f ⊓ pair b (z.func k) ∈ᴮ g) ⊓
         (x.bval i ⊓ z.bval k))) ⊓ Γ' ≤
        pair a c =ᴮ pair (x.func i) (z.func k) :=
      inf_le_left.trans inf_le_left
    have H_phi : (pair a c =ᴮ pair (x.func i) (z.func k) ⊓
        ((⨆ b, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f ⊓ pair b (z.func k) ∈ᴮ g) ⊓
         (x.bval i ⊓ z.bval k))) ⊓ Γ' ≤
        ⨆ b, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f ⊓ pair b (z.func k) ∈ᴮ g :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)

    have ⟨H_a_i, H_c_k⟩ := (pair_eq_pair_iff.mp H_eq)

    apply le_trans (le_inf H_phi le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro b

    apply le_iSup_of_le b

    refine le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) (le_inf ?_ ?_)
    ·

      exact bv_rw' (H := inf_le_right.trans H_a_i) (ϕ := fun z => pair z b ∈ᴮ f)
        (h_congr := B_ext_pair_mem_left)
        (H_new := inf_le_left.trans (inf_le_left.trans inf_le_right))
    ·
      exact bv_rw' (H := inf_le_right.trans H_c_k) (ϕ := fun w => pair b w ∈ᴮ g)
        (h_congr := B_ext_pair_mem_right)
        (H_new := inf_le_left.trans inf_le_right)
  · intro ⟨Ha, Hc, Hb⟩

    rw [mem_subset.mk_iff]
    simp only [prod_func, prod_bval]

    have Ha_iSup : Γ' ≤ ⨆ i : x.type, x.bval i ⊓ a =ᴮ x.func i := by
      rw [← mem_unfold]; exact Ha
    have Hc_iSup : Γ' ≤ ⨆ k : z.type, z.bval k ⊓ c =ᴮ z.func k := by
      rw [← mem_unfold]; exact Hc

    apply le_trans (le_inf Ha_iSup le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro i

    apply le_trans (le_inf (inf_le_right.trans Hc_iSup) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro k

    apply le_trans (le_inf (inf_le_right.trans (inf_le_right.trans Hb)) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro b

    apply le_iSup_of_le (i, k)
    simp only [prod_func, prod_bval]

    refine le_inf (pair_congr
        (show _ ≤ a =ᴮ x.func i from
          inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))
        (show _ ≤ c =ᴮ z.func k from
          inf_le_right.trans (inf_le_left.trans inf_le_right)))
      (le_inf ?_ ?_)
    ·
      apply le_iSup_of_le b

      refine le_inf (le_inf (inf_le_left.trans inf_le_left) ?_) ?_
      ·
        exact bv_rw'
          (H := bv_symm (show _ ≤ a =ᴮ x.func i from
            inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))))
          (ϕ := fun z => pair z b ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
          (H_new := inf_le_left.trans (inf_le_right.trans inf_le_left))
      ·
        exact bv_rw'
          (H := bv_symm (show _ ≤ c =ᴮ z.func k from
            inf_le_right.trans (inf_le_left.trans inf_le_right)))
          (ϕ := fun w => pair b w ∈ᴮ g) (h_congr := B_ext_pair_mem_right)
          (H_new := inf_le_left.trans (inf_le_right.trans inf_le_right))
    ·

      exact le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
                   (inf_le_right.trans (inf_le_left.trans inf_le_left))

lemma is_func'_comp_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) :
    Γ ≤ is_func (is_func'_comp Hf_func Hg_func) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]

  have H_mem₁ := (mem_is_func'_comp_iff Hf_func Hg_func).mp
    (show (Γ ⊓ (pair w₁ v₁ ∈ᴮ is_func'_comp Hf_func Hg_func ⊓
                pair w₂ v₂ ∈ᴮ is_func'_comp Hf_func Hg_func)) ⊓ w₁ =ᴮ w₂ ≤
         pair w₁ v₁ ∈ᴮ is_func'_comp Hf_func Hg_func from
      inf_le_left.trans (inf_le_right.trans inf_le_left))
  have H_mem₂ := (mem_is_func'_comp_iff Hf_func Hg_func).mp
    (show (Γ ⊓ (pair w₁ v₁ ∈ᴮ is_func'_comp Hf_func Hg_func ⊓
                pair w₂ v₂ ∈ᴮ is_func'_comp Hf_func Hg_func)) ⊓ w₁ =ᴮ w₂ ≤
         pair w₂ v₂ ∈ᴮ is_func'_comp Hf_func Hg_func from
      inf_le_left.trans (inf_le_right.trans inf_le_right))

  obtain ⟨b₁, Hb₁⟩ := exists_convert H_mem₁.2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
  obtain ⟨b₂, Hb₂⟩ := exists_convert H_mem₂.2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))

  have hb₁b₂ := eq_of_is_func'_of_eq (inf_le_left.trans (inf_le_left.trans Hf_func))
    inf_le_right
    (Hb₁.trans (inf_le_right.trans inf_le_left))
    (Hb₂.trans (inf_le_right.trans inf_le_left))

  exact eq_of_is_func'_of_eq (inf_le_left.trans (inf_le_left.trans Hg_func))
    hb₁b₂
    (Hb₁.trans (inf_le_right.trans inf_le_right))
    (Hb₂.trans (inf_le_right.trans inf_le_right))

lemma is_func'_comp_is_total {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) :
    Γ ≤ is_total x z (is_func'_comp Hf_func Hg_func) := by
  unfold is_total
  apply le_iInf; intro a; rw [← deduction]

  have H_tot_f : Γ ⊓ a ∈ᴮ x ≤ ⨆ b, b ∈ᴮ y ⊓ pair a b ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (le_trans (is_total_of_is_func' Hf_func)
      (iInf_le _ a))) inf_le_right) bv_imp_elim
  obtain ⟨b, Hb⟩ := exists_convert H_tot_f
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

  have H_tot_g : Γ ⊓ a ∈ᴮ x ≤ ⨆ c, c ∈ᴮ z ⊓ pair b c ∈ᴮ g :=
    le_trans (le_inf (inf_le_left.trans (le_trans (is_total_of_is_func' Hg_func)
      (iInf_le _ b))) (Hb.trans inf_le_left)) bv_imp_elim
  obtain ⟨c, Hc⟩ := exists_convert H_tot_g
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

  apply le_iSup_of_le c
  refine le_inf (Hc.trans inf_le_left) ?_

  apply (mem_is_func'_comp_iff Hf_func Hg_func).mpr
  refine ⟨inf_le_right, Hc.trans inf_le_left, ?_⟩
  apply le_iSup_of_le b
  exact le_inf (Hb.trans inf_le_left) (le_inf (Hb.trans inf_le_right) (Hc.trans inf_le_right))

lemma is_func'_comp_is_func' {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) :
    Γ ≤ is_func' x z (is_func'_comp Hf_func Hg_func) :=
  le_inf (is_func'_comp_is_func Hf_func Hg_func) (is_func'_comp_is_total Hf_func Hg_func)

lemma is_func'_comp_inj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g)
    (Hf_inj : Γ ≤ is_inj f) (Hg_inj : Γ ≤ is_inj g) :
    Γ ≤ is_inj (is_func'_comp Hf_func Hg_func) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]

  have H_mem₁ := (mem_is_func'_comp_iff Hf_func Hg_func).mp
    (show Γ ⊓ (pair w₁ v₁ ∈ᴮ is_func'_comp Hf_func Hg_func ⊓
               pair w₂ v₂ ∈ᴮ is_func'_comp Hf_func Hg_func ⊓ v₁ =ᴮ v₂) ≤
         pair w₁ v₁ ∈ᴮ is_func'_comp Hf_func Hg_func from
      inf_le_right.trans (inf_le_left.trans inf_le_left))
  have H_mem₂ := (mem_is_func'_comp_iff Hf_func Hg_func).mp
    (show Γ ⊓ (pair w₁ v₁ ∈ᴮ is_func'_comp Hf_func Hg_func ⊓
               pair w₂ v₂ ∈ᴮ is_func'_comp Hf_func Hg_func ⊓ v₁ =ᴮ v₂) ≤
         pair w₂ v₂ ∈ᴮ is_func'_comp Hf_func Hg_func from
      inf_le_right.trans (inf_le_left.trans inf_le_right))

  obtain ⟨b₁, Hb₁⟩ := exists_convert H_mem₁.2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
  obtain ⟨b₂, Hb₂⟩ := exists_convert H_mem₂.2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))

  have hb₁b₂ := eq_of_is_inj_of_eq (inf_le_left.trans Hg_inj)
    (inf_le_right.trans inf_le_right)
    (Hb₁.trans (inf_le_right.trans inf_le_right))
    (Hb₂.trans (inf_le_right.trans inf_le_right))

  exact eq_of_is_inj_of_eq (inf_le_left.trans Hf_inj)
    hb₁b₂
    (Hb₁.trans (inf_le_right.trans inf_le_left))
    (Hb₂.trans (inf_le_right.trans inf_le_left))

lemma is_func'_comp_surj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g)
    (H₁ : Γ ≤ is_surj x y f) (H₂ : Γ ≤ is_surj y z g) :
    Γ ≤ is_surj x z (is_func'_comp Hf_func Hg_func) := by
  unfold is_surj
  apply le_iInf; intro wz; rw [← deduction]

  have H_surj_g : Γ ⊓ wz ∈ᴮ z ≤ ⨆ wy, wy ∈ᴮ y ⊓ pair wy wz ∈ᴮ g :=
    le_trans (le_inf (inf_le_left.trans (le_trans H₂ (iInf_le _ wz))) inf_le_right) bv_imp_elim
  obtain ⟨wy, Hwy⟩ := exists_convert H_surj_g
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)

  have H_surj_f : Γ ⊓ wz ∈ᴮ z ≤ ⨆ wx, wx ∈ᴮ x ⊓ pair wx wy ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (le_trans H₁ (iInf_le _ wy))) (Hwy.trans inf_le_left)) bv_imp_elim
  obtain ⟨wx, Hwx⟩ := exists_convert H_surj_f
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)

  apply le_iSup_of_le wx
  refine le_inf (Hwx.trans inf_le_left) ?_

  apply (mem_is_func'_comp_iff Hf_func Hg_func).mpr
  refine ⟨Hwx.trans inf_le_left, inf_le_right, ?_⟩
  apply le_iSup_of_le wy
  exact le_inf (Hwy.trans inf_le_left) (le_inf (Hwx.trans inf_le_right) (Hwy.trans inf_le_right))

def function_comp {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    (H₁ : Γ' ≤ is_function x y f) (H₂ : Γ' ≤ is_function y z g) : bSet 𝔹' :=
  is_func'_comp (is_func'_of_is_function H₁) (is_func'_of_is_function H₂)

lemma function_comp_is_function {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    {H₁ : Γ' ≤ is_function x y f} {H₂ : Γ' ≤ is_function y z g} :
    Γ' ≤ is_function x z (function_comp H₁ H₂) :=
  le_inf (is_func'_comp_is_func' _ _) subset.mk_subset

def injective_function_comp {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    (H₁ : Γ' ≤ is_injective_function x y f) (H₂ : Γ' ≤ is_injective_function y z g) : bSet 𝔹' :=
  is_func'_comp (is_func'_of_is_injective_function H₁) (is_func'_of_is_injective_function H₂)

lemma injective_function_comp_is_injective_function {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    {H₁ : Γ' ≤ is_injective_function x y f} {H₂ : Γ' ≤ is_injective_function y z g} :
    Γ' ≤ is_injective_function x z (injective_function_comp H₁ H₂) :=
  le_inf (function_comp_is_function (H₁ := H₁.trans inf_le_left) (H₂ := H₂.trans inf_le_left))
         (is_func'_comp_inj _ _ (H₁.trans inf_le_right) (H₂.trans inf_le_right))

lemma injective_function_comp_is_function {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    {H₁ : Γ' ≤ is_injective_function x y f} {H₂ : Γ' ≤ is_injective_function y z g} :
    Γ' ≤ is_function x z (injective_function_comp H₁ H₂) :=
  injective_function_comp_is_injective_function.trans inf_le_left

lemma injects_into_trans {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ injects_into x y) (H₂ : Γ ≤ injects_into y z) :
    Γ ≤ injects_into x z :=

  calc Γ ≤ (⨆ f, is_func' x y f ⊓ is_inj f) ⊓ (⨆ g, is_func' y z g ⊓ is_inj g) :=
          le_inf H₁ H₂
    _ ≤ ⨆ f, (is_func' x y f ⊓ is_inj f) ⊓ (⨆ g, is_func' y z g ⊓ is_inj g) :=
          (iSup_inf_eq _ _).le
    _ ≤ ⨆ f, ⨆ g, (is_func' x y f ⊓ is_inj f) ⊓ (is_func' y z g ⊓ is_inj g) := by
          apply iSup_le; intro f
          rw [inf_iSup_eq' (a := is_func' x y f ⊓ is_inj f)
            (s := fun g => is_func' y z g ⊓ is_inj g)]
          exact iSup_le (fun g => le_iSup_of_le f (le_iSup_of_le g le_rfl))
    _ ≤ ⨆ h, is_func' x z h ⊓ is_inj h := by
          apply iSup_le; intro f; apply iSup_le; intro g
          apply le_iSup_of_le (is_func'_comp (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          exact le_inf
            (is_func'_comp_is_func' (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
            (is_func'_comp_inj (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
              (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))

lemma injection_into_trans {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ injection_into x y) (H₂ : Γ ≤ injection_into y z) :
    Γ ≤ injection_into x z := by
  rw [← injects_into_iff_injection_into] at H₁ H₂ ⊢
  exact injects_into_trans H₁ H₂

lemma AE_of_check_func_check₀ (x y : PSet.{u}) {f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ is_func' (check x) (check y) f) (H_nonzero : ⊥ < Γ) :
    ∀ (i : x.Type), ∃ (j : y.Type),
      ⊥ < (is_func' (check x) (check y) f) ⊓
          (pair (check (x.Func i)) (check (y.Func j))) ∈ᴮ f := by
  cases y with | mk α A =>
  intro i
  have H_total := is_total_of_is_func' H
  have H_ex : Γ ≤ ⨆ w₂, w₂ ∈ᴮ (check (PSet.mk α A) : bSet 𝔹) ⊓
      pair (check (x.Func i)) w₂ ∈ᴮ f :=
    le_trans (le_inf (H_total.trans (iInf_le _ (check (x.Func i)))) mem_check_of_mem)
      bv_imp_elim
  rw [← @bounded_exists 𝔹 _ (check (PSet.mk α A) : bSet 𝔹)
      (fun w₂ => pair (check (x.Func i)) w₂ ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right)] at H_ex
  simp only [check_bval_top, top_inf_eq] at H_ex

  have H_combined : ⊥ < ⨆ j : α, is_func' (check x) (check (PSet.mk α A)) f ⊓
      pair (check (x.Func i)) (check (A j)) ∈ᴮ f :=
    lt_of_lt_of_le H_nonzero (le_trans (le_inf H H_ex) (le_of_eq inf_iSup_eq'))
  exact nonzero_wit H_combined

lemma AE_of_check_func_check (x y : PSet.{u}) {f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ is_func' (check x) (check y) f) (H_nonzero : ⊥ < Γ) :
    ∀ (i : x.Type), ∃ (j : y.Type) (Γ' : 𝔹) (_H_nonzero' : ⊥ < Γ') (_H_le : Γ' ≤ Γ),
      Γ' ≤ (is_func' (check x) (check y) f) ∧
      Γ' ≤ (pair (check (x.Func i)) (check (y.Func j))) ∈ᴮ f := by
  cases y with | mk α A =>
  intro i
  have H_total := is_total_of_is_func' H
  have H_ex : Γ ≤ ⨆ w₂, w₂ ∈ᴮ (check (PSet.mk α A) : bSet 𝔹) ⊓
      pair (check (x.Func i)) w₂ ∈ᴮ f :=
    le_trans (le_inf (H_total.trans (iInf_le _ (check (x.Func i)))) mem_check_of_mem)
      bv_imp_elim
  rw [← @bounded_exists 𝔹 _ (check (PSet.mk α A) : bSet 𝔹)
      (fun w₂ => pair (check (x.Func i)) w₂ ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right)] at H_ex
  simp only [check_bval_top, top_inf_eq] at H_ex

  have H_supr : Γ ≤ ⨆ j : α,
      is_func' (check x) (check (PSet.mk α A)) f ⊓ pair (check (x.Func i)) (check (A j)) ∈ᴮ f :=
    le_trans (le_inf H H_ex) (le_of_eq inf_iSup_eq')
  obtain ⟨j, Hj⟩ := nonzero_wit' H_nonzero H_supr
  exact ⟨j,
    is_func' (check x) (check (PSet.mk α A)) f ⊓ pair (check (x.Func i)) (check (A j)) ∈ᴮ f ⊓ Γ,
    Hj,
    inf_le_right,
    ⟨inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right⟩⟩

lemma exists_surjection_of_surjects_onto {x y : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ surjects_onto x y) :
    Γ ≤ ⨆ f, is_function x y f ⊓ is_surj x y f :=

  H_surj.trans (iSup_le fun f' =>
    le_iSup_of_le (function_of_func' inf_le_left)
      (le_inf (function_of_func'_is_function inf_le_left)
        (function_of_func'_surj_of_surj inf_le_left inf_le_right)))

def functions (x y : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun s : (bv_powerset (prod x y) : bSet 𝔹).type =>
    is_function x y ((bv_powerset (prod x y)).func s))

@[simp] lemma functions_func {x y : bSet 𝔹} {i} :
    (functions x y).func i = (bv_powerset (prod x y)).func i := rfl

@[simp] lemma functions_bval {x y : bSet 𝔹} {i} :
    (functions x y).bval i = is_function x y ((bv_powerset (prod x y)).func i) := rfl

@[simp] lemma functions_type {x y : bSet 𝔹} :
    (functions x y).type = (bv_powerset (prod x y)).type := rfl

lemma mem_functions_iff {g x y : bSet 𝔹} {Γ : 𝔹} :
    (Γ ≤ g ∈ᴮ functions x y) ↔ (Γ ≤ is_function x y g) := by
  constructor
  · intro H

    rw [mem_unfold] at H
    apply H.trans; apply iSup_le; intro i
    simp only [functions_bval, functions_func]

    exact bv_rw' (H := inf_le_right) (ϕ := fun f => is_function x y f)
      (h_congr := B_ext_is_function_right) (H_new := inf_le_left)
  · intro H

    rw [mem_unfold]; unfold functions set_of_indicator

    have Hfunc := H
    simp only [is_function] at Hfunc
    have Hsub : Γ ≤ g ⊆ᴮ prod x y := Hfunc.trans inf_le_right

    have Hsub2 := bv_powerset_spec.mp Hsub
    rw [mem_unfold] at Hsub2

    apply (le_inf Hsub2 H).trans

    apply (iSup_inf_eq _ _).le.trans
    apply iSup_le; intro i; apply le_iSup_of_le i

    refine le_inf ?_ (inf_le_left.trans inf_le_right)

    exact bv_rw' (H := bv_symm (inf_le_left.trans inf_le_right))
      (h_congr := B_ext_is_function_right) (H_new := inf_le_right)

def functionMk' {x y : bSet 𝔹}
    (F : x.type → y.type)
    (χ : x.type → 𝔹)
    (_H_ext : ∀ i j {Γ : 𝔹}, Γ ≤ x.func i =ᴮ x.func j → Γ ≤ y.func (F i) =ᴮ y.func (F j))
    (_H_mem : ∀ i {Γ : 𝔹}, Γ ≤ x.bval i → Γ ≤ y.bval (F i) ∧ Γ ≤ χ i) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x y).type => χ pr.1 ⊓ y.func pr.2 =ᴮ y.func (F pr.1))

lemma functionMk'_is_func {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ is_func (functionMk' F χ H_ext H_mem) := by

  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]

  set φ : (prod x y).type → 𝔹 := fun pr => χ pr.1 ⊓ y.func pr.2 =ᴮ y.func (F pr.1)
  have hfmk : functionMk' F χ H_ext H_mem = subset.mk φ := rfl
  have hmem1 : pair w₁ v₁ ∈ᴮ functionMk' F χ H_ext H_mem ≤
      ⨆ pr₁ : (prod x y).type, pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓ (φ pr₁ ⊓ (prod x y).bval pr₁) :=
    hfmk ▸ mem_subset.mk_iff.mp le_rfl
  have hmem2 : pair w₂ v₂ ∈ᴮ functionMk' F χ H_ext H_mem ≤
      ⨆ pr₂ : (prod x y).type, pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂) :=
    hfmk ▸ mem_subset.mk_iff.mp le_rfl

  set ctx6 := Γ ⊓ (pair w₁ v₁ ∈ᴮ functionMk' F χ H_ext H_mem ⊓ pair w₂ v₂ ∈ᴮ functionMk' F χ H_ext H_mem) ⊓ w₁ =ᴮ w₂
  calc ctx6
      ≤ (⨆ pr₁, pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓ (φ pr₁ ⊓ (prod x y).bval pr₁)) ⊓ ctx6 :=
        le_inf (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans hmem1))) le_rfl
    _ ≤ ⨆ pr₁, (pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓ (φ pr₁ ⊓ (prod x y).bval pr₁)) ⊓ ctx6 :=
        (iSup_inf_eq _ _).le
    _ ≤ v₁ =ᴮ v₂ := by
        apply iSup_le; intro pr₁
        obtain ⟨i, j⟩ := pr₁
        simp only [prod_func, prod_bval, φ]

        have hmem2_w2 : (pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx6 ≤
            ⨆ pr₂ : (prod x y).type, pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂) :=
          le_trans inf_le_right (le_trans inf_le_left (le_trans inf_le_right (le_trans inf_le_right hmem2)))
        calc (pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx6
            ≤ (⨆ pr₂, pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂)) ⊓
                ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx6) :=
              le_inf hmem2_w2 le_rfl
          _ ≤ ⨆ pr₂, (pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂)) ⊓
                ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx6) :=
              (iSup_inf_eq _ _).le
          _ ≤ v₁ =ᴮ v₂ := by
              apply iSup_le; intro pr₂
              obtain ⟨i', j'⟩ := pr₂
              simp only [prod_func, prod_bval, φ]
              set ctx7 := (pair w₂ v₂ =ᴮ pair (x.func i') (y.func j') ⊓ ((χ i' ⊓ y.func j' =ᴮ y.func (F i')) ⊓ (x.bval i' ⊓ y.bval j'))) ⊓
                    ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx6)

              have hw1xi : ctx7 ≤ w₁ =ᴮ x.func i :=
                inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left))
              have hv1yj : ctx7 ≤ v₁ =ᴮ y.func j :=
                inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right))

              have hyj_yFi : ctx7 ≤ y.func j =ᴮ y.func (F i) :=
                inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))

              have hw2xi' : ctx7 ≤ w₂ =ᴮ x.func i' :=
                inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left)
              have hv2yj' : ctx7 ≤ v₂ =ᴮ y.func j' :=
                inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right)

              have hyj'_yFi' : ctx7 ≤ y.func j' =ᴮ y.func (F i') :=
                inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))

              have hw12 : ctx7 ≤ w₁ =ᴮ w₂ :=
                inf_le_right.trans (inf_le_right.trans inf_le_right)

              have hxi_xi' : ctx7 ≤ x.func i =ᴮ x.func i' :=
                bv_trans (bv_symm hw1xi) (bv_trans hw12 hw2xi')

              have hyFi_yFi' : ctx7 ≤ y.func (F i) =ᴮ y.func (F i') :=
                H_ext i i' hxi_xi'

              exact bv_trans hv1yj (bv_trans hyj_yFi (bv_trans hyFi_yFi' (bv_trans (bv_symm hyj'_yFi') (bv_symm hv2yj'))))

lemma functionMk'_is_total {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ is_total x y (functionMk' F χ H_ext H_mem) := by

  rw [is_total_iff_is_total']
  unfold is_total'
  apply le_iInf; intro i; rw [← deduction]

  obtain ⟨hyF, hχ⟩ := H_mem i inf_le_right
  apply le_iSup_of_le (F i)

  refine le_inf hyF ?_
  rw [mem_unfold]
  apply le_iSup_of_le (i, F i)

  simp only [functionMk', subset.mk, set_of_indicator_bval, set_of_indicator_func, prod_func, prod_bval]
  refine le_inf (le_inf (le_inf hχ bv_refl) (le_inf inf_le_right hyF)) bv_refl

lemma functionMk'_is_subset {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ functionMk' F χ H_ext H_mem ⊆ᴮ prod x y :=
  subset.mk_subset

lemma functionMk'_is_function {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ is_function x y (functionMk' F χ H_ext H_mem) :=
  le_inf (le_inf (functionMk'_is_func F χ H_ext H_mem) (functionMk'_is_total F χ H_ext H_mem))
         (functionMk'_is_subset F χ H_ext H_mem)

lemma functionMk'_is_inj {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i)
    (H_inj : ∀ i j {Γ'' : 𝔹}, Γ'' ≤ y.func (F i) =ᴮ y.func (F j) → Γ'' ≤ x.func i =ᴮ x.func j) :
    Γ ≤ is_inj (functionMk' F χ H_ext H_mem) := by

  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]

  set φ : (prod x y).type → 𝔹 := fun pr => χ pr.1 ⊓ y.func pr.2 =ᴮ y.func (F pr.1)
  have hfmk : functionMk' F χ H_ext H_mem = subset.mk φ := rfl

  have hmem1 : pair w₁ v₁ ∈ᴮ functionMk' F χ H_ext H_mem ≤
      ⨆ pr₁ : (prod x y).type, pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓ (φ pr₁ ⊓ (prod x y).bval pr₁) :=
    hfmk ▸ mem_subset.mk_iff.mp le_rfl
  have hmem2 : pair w₂ v₂ ∈ᴮ functionMk' F χ H_ext H_mem ≤
      ⨆ pr₂ : (prod x y).type, pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂) :=
    hfmk ▸ mem_subset.mk_iff.mp le_rfl

  set ctx := Γ ⊓ (pair w₁ v₁ ∈ᴮ functionMk' F χ H_ext H_mem ⊓ pair w₂ v₂ ∈ᴮ functionMk' F χ H_ext H_mem ⊓ v₁ =ᴮ v₂)
  calc ctx
      ≤ (⨆ pr₁, pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓ (φ pr₁ ⊓ (prod x y).bval pr₁)) ⊓ ctx :=
        le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans hmem1))) le_rfl
    _ ≤ ⨆ pr₁, (pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓ (φ pr₁ ⊓ (prod x y).bval pr₁)) ⊓ ctx :=
        (iSup_inf_eq _ _).le
    _ ≤ w₁ =ᴮ w₂ := by
        apply iSup_le; intro pr₁; obtain ⟨i, j⟩ := pr₁
        simp only [prod_func, prod_bval, φ]
        have hmem2_w2 : (pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx ≤
            ⨆ pr₂ : (prod x y).type, pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂) :=
          inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans hmem2)))
        calc (pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx
            ≤ (⨆ pr₂, pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂)) ⊓
                ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx) :=
              le_inf hmem2_w2 le_rfl
          _ ≤ ⨆ pr₂, (pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓ (φ pr₂ ⊓ (prod x y).bval pr₂)) ⊓
                ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx) :=
              (iSup_inf_eq _ _).le
          _ ≤ w₁ =ᴮ w₂ := by
              apply iSup_le; intro pr₂; obtain ⟨i', j'⟩ := pr₂
              simp only [prod_func, prod_bval, φ]
              set ctx8 := (pair w₂ v₂ =ᴮ pair (x.func i') (y.func j') ⊓ ((χ i' ⊓ y.func j' =ᴮ y.func (F i')) ⊓ (x.bval i' ⊓ y.bval j'))) ⊓
                    ((pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) ⊓ ((χ i ⊓ y.func j =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval j))) ⊓ ctx)

              have hw1xi : ctx8 ≤ w₁ =ᴮ x.func i :=
                inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left))
              have hv1yj : ctx8 ≤ v₁ =ᴮ y.func j :=
                inf_le_right.trans (inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right))

              have hyj_yFi : ctx8 ≤ y.func j =ᴮ y.func (F i) :=
                inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))

              have hw2xi' : ctx8 ≤ w₂ =ᴮ x.func i' :=
                inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_left)
              have hv2yj' : ctx8 ≤ v₂ =ᴮ y.func j' :=
                inf_le_left.trans (inf_le_left.trans eq_of_eq_pair_right)

              have hyj'_yFi' : ctx8 ≤ y.func j' =ᴮ y.func (F i') :=
                inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))

              have hv12 : ctx8 ≤ v₁ =ᴮ v₂ :=
                inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))

              have hyFi_yFi' : ctx8 ≤ y.func (F i) =ᴮ y.func (F i') :=
                bv_trans (bv_symm (bv_trans hv1yj hyj_yFi)) (bv_trans hv12 (bv_trans hv2yj' hyj'_yFi'))

              have hxi_xi' : ctx8 ≤ x.func i =ᴮ x.func i' := H_inj i i' hyFi_yFi'

              exact bv_trans hw1xi (bv_trans hxi_xi' (bv_symm hw2xi'))

def inj_inverse {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) : bSet 𝔹 :=
  subset.mk (fun pr : (prod (image x y f) x).type =>
    pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f)

lemma mem_inj_inverse_iff {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)
    {Γ' : 𝔹} {b a : bSet 𝔹} :
    Γ' ≤ pair b a ∈ᴮ inj_inverse H_func H_inj ↔
      Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ b ∈ᴮ y ∧ Γ' ≤ pair a b ∈ᴮ f := by
  simp only [inj_inverse]
  constructor
  · intro H

    have H_iSup := mem_subset.mk_iff.mp H

    refine ⟨?_, ?_, ?_⟩
    ·

      apply H_iSup.trans; apply iSup_le; intro ⟨i, j⟩
      simp only [prod_func, prod_bval]

      exact bv_rw' (H := (pair_eq_pair_iff.mp inf_le_left).2)
        (ϕ := fun z => z ∈ᴮ x) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_right.trans (inf_le_right.trans inf_le_right)).trans (mem_mk' x j))
    ·
      apply H_iSup.trans; apply iSup_le; intro ⟨i, j⟩
      simp only [prod_func, prod_bval]
      exact mem_of_mem_subset image_subset
        (bv_rw' (H := (pair_eq_pair_iff.mp inf_le_left).1)
          (ϕ := fun z => z ∈ᴮ image x y f) (h_congr := B_ext_mem_left)
          (H_new := (inf_le_right.trans (inf_le_right.trans inf_le_left)).trans
            (mem_mk' (image x y f) i)))
    ·
      apply H_iSup.trans; apply iSup_le; intro ⟨i, j⟩
      simp only [prod_func, prod_bval]
      exact bv_rw' (H := (pair_eq_pair_iff.mp inf_le_left).2)
        (ϕ := fun z => pair z b ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
        (H_new := bv_rw' (H := (pair_eq_pair_iff.mp inf_le_left).1)
          (ϕ := fun z => pair (x.func j) z ∈ᴮ f) (h_congr := B_ext_pair_mem_right)
          (H_new := inf_le_right.trans inf_le_left))
  · intro ⟨Ha, Hb, Hf⟩

    rw [mem_subset.mk_iff]
    simp only [prod_func, prod_bval]

    have Hb_img : Γ' ≤ b ∈ᴮ image x y f := by
      apply (mem_image_iff).mpr
      exact ⟨Hb, le_iSup_of_le a (le_inf Ha Hf)⟩

    have Hb_iSup : Γ' ≤ ⨆ i : (image x y f).type, (image x y f).bval i ⊓ b =ᴮ (image x y f).func i := by
      rw [← mem_unfold]; exact Hb_img

    have Ha_iSup : Γ' ≤ ⨆ j : x.type, x.bval j ⊓ a =ᴮ x.func j := by
      rw [← mem_unfold]; exact Ha

    apply le_trans (le_inf Hb_iSup le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro i
    apply le_trans (le_inf (inf_le_right.trans Ha_iSup) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro j

    apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]

    refine le_inf (pair_congr
        (show _ ≤ b =ᴮ (image x y f).func i from
          inf_le_right.trans (inf_le_left.trans inf_le_right))
        (show _ ≤ a =ᴮ x.func j from
          inf_le_left.trans inf_le_right))
      (le_inf ?_ ?_)
    ·

      exact bv_rw'
        (H := bv_symm (show _ ≤ a =ᴮ x.func j from inf_le_left.trans inf_le_right))
        (ϕ := fun z => pair z ((image x y f).func i) ∈ᴮ f)
        (h_congr := B_ext_pair_mem_left)
        (H_new := bv_rw'
          (H := bv_symm (show _ ≤ b =ᴮ (image x y f).func i from
            inf_le_right.trans (inf_le_left.trans inf_le_right)))
          (ϕ := fun z => pair a z ∈ᴮ f)
          (h_congr := B_ext_pair_mem_right)
          (H_new := inf_le_right.trans (inf_le_right.trans Hf)))
    ·
      exact le_inf (inf_le_right.trans (inf_le_left.trans inf_le_left))
                   (inf_le_left.trans inf_le_left)

lemma inj_inverse_is_func {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_func (inj_inverse H_func H_inj) := by

  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]

  have H_mem₁ := (mem_inj_inverse_iff H_func H_inj).mp
    (show (Γ ⊓ (pair w₁ v₁ ∈ᴮ inj_inverse H_func H_inj ⊓
                pair w₂ v₂ ∈ᴮ inj_inverse H_func H_inj)) ⊓ w₁ =ᴮ w₂ ≤
         pair w₁ v₁ ∈ᴮ inj_inverse H_func H_inj from
      inf_le_left.trans (inf_le_right.trans inf_le_left))
  have H_mem₂ := (mem_inj_inverse_iff H_func H_inj).mp
    (show (Γ ⊓ (pair w₁ v₁ ∈ᴮ inj_inverse H_func H_inj ⊓
                pair w₂ v₂ ∈ᴮ inj_inverse H_func H_inj)) ⊓ w₁ =ᴮ w₂ ≤
         pair w₂ v₂ ∈ᴮ inj_inverse H_func H_inj from
      inf_le_left.trans (inf_le_right.trans inf_le_right))

  exact eq_of_is_inj_of_eq (inf_le_left.trans (inf_le_left.trans H_inj))
    inf_le_right H_mem₁.2.2 H_mem₂.2.2

lemma inj_inverse_is_total {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_total (image x y f) x (inj_inverse H_func H_inj) := by
  unfold is_total
  apply le_iInf; intro z; rw [← deduction]

  have Hz_mem := (mem_image_iff.mp (show Γ ⊓ z ∈ᴮ image x y f ≤ z ∈ᴮ image x y f from
    inf_le_right))
  have Hz_y := Hz_mem.1
  have Hz_iSup := Hz_mem.2
  obtain ⟨z', Hz'⟩ := exists_convert Hz_iSup (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)

  apply le_iSup_of_le z'
  refine le_inf (Hz'.trans inf_le_left) ?_

  apply (mem_inj_inverse_iff H_func H_inj).mpr
  exact ⟨Hz'.trans inf_le_left, Hz_y, Hz'.trans inf_le_right⟩

lemma inj_inverse_is_func' {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_func' (image x y f) x (inj_inverse H_func H_inj) :=
  le_inf (inj_inverse_is_func H_func H_inj) (inj_inverse_is_total H_func H_inj)

lemma inj_inverse_is_surj {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_surj (image x y f) x (inj_inverse H_func H_inj) := by
  unfold is_surj
  apply le_iInf; intro z; rw [← deduction]

  have H_tot := is_total_of_is_func' H_func
  have H_tot_z : Γ ⊓ z ∈ᴮ x ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (H_tot.trans (iInf_le _ z))) inf_le_right) bv_imp_elim
  obtain ⟨w₂, Hw₂⟩ := exists_convert H_tot_z (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

  apply le_iSup_of_le w₂
  refine le_inf ?_ ?_
  ·
    apply mem_image_iff.mpr
    exact ⟨Hw₂.trans inf_le_left, le_iSup_of_le z (le_inf inf_le_right (Hw₂.trans inf_le_right))⟩
  ·
    apply (mem_inj_inverse_iff H_func H_inj).mpr
    exact ⟨inf_le_right, Hw₂.trans inf_le_left, Hw₂.trans inf_le_right⟩

lemma inj_inverse_subset_prod {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ inj_inverse H_func H_inj ⊆ᴮ prod (image x y f) x :=
  subset.mk_subset

lemma inj_inverse_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_function (image x y f) x (inj_inverse H_func H_inj) :=
  le_inf (inj_inverse_is_func' H_func H_inj) (inj_inverse_subset_prod H_func H_inj)

lemma inj_inverse_is_inj {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_inj (inj_inverse H_func H_inj) := by

  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]

  have H_mem₁ := (mem_inj_inverse_iff H_func H_inj).mp
    (show Γ ⊓ (pair w₁ v₁ ∈ᴮ inj_inverse H_func H_inj ⊓
               pair w₂ v₂ ∈ᴮ inj_inverse H_func H_inj ⊓ v₁ =ᴮ v₂) ≤
         pair w₁ v₁ ∈ᴮ inj_inverse H_func H_inj from
      inf_le_right.trans (inf_le_left.trans inf_le_left))
  have H_mem₂ := (mem_inj_inverse_iff H_func H_inj).mp
    (show Γ ⊓ (pair w₁ v₁ ∈ᴮ inj_inverse H_func H_inj ⊓
               pair w₂ v₂ ∈ᴮ inj_inverse H_func H_inj ⊓ v₁ =ᴮ v₂) ≤
         pair w₂ v₂ ∈ᴮ inj_inverse H_func H_inj from
      inf_le_right.trans (inf_le_left.trans inf_le_right))

  exact eq_of_is_func'_of_eq (inf_le_left.trans H_func)
    (inf_le_right.trans inf_le_right) H_mem₁.2.2 H_mem₂.2.2

section injective_function_inverse_section
variable {Γ : 𝔹}

def injective_function_inverse {x y f : bSet 𝔹} (H_inj : Γ ≤ is_injective_function x y f) :
    bSet 𝔹 :=
  inj_inverse (is_func'_of_is_injective_function H_inj)
              (is_inj_of_is_injective_function H_inj)

lemma injective_function_inverse_is_injective_function {x y f : bSet 𝔹}
    {H_inj : Γ ≤ is_injective_function x y f} :
    Γ ≤ is_injective_function (image x y f) x (injective_function_inverse H_inj) :=
  le_inf (inj_inverse_is_function _ _) (inj_inverse_is_inj _ _)

lemma injective_function_inverse_is_inj {x y f : bSet 𝔹}
    {H_inj : Γ ≤ is_injective_function x y f} :
    Γ ≤ is_inj (injective_function_inverse H_inj) :=
  injective_function_inverse_is_injective_function.trans inf_le_right

end injective_function_inverse_section

private lemma function_eval_exists {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function x y f) (z : bSet 𝔹) (H_mem : Γ ≤ z ∈ᴮ x) :
    ∃ w, Γ ≤ w ∈ᴮ y ⊓ pair z w ∈ᴮ f :=

  have H_total_spec : Γ ≤ z ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f :=
    le_trans (is_total_of_is_function H_func) (iInf_le _ z)
  have H_ex : Γ ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f :=
    le_trans (le_inf H_total_spec H_mem) bv_imp_elim
  exists_convert H_ex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

noncomputable def function_eval {x y f : bSet 𝔹} {Γ : 𝔹} (H_func : Γ ≤ is_function x y f)
    (z : bSet 𝔹) (H_mem : Γ ≤ z ∈ᴮ x) : bSet 𝔹 :=
  (function_eval_exists H_func z H_mem).choose

lemma function_eval_spec {x y f : bSet 𝔹} {Γ : 𝔹} {H_func : Γ ≤ is_function x y f}
    {z : bSet 𝔹} {H_mem : Γ ≤ z ∈ᴮ x} :
    Γ ≤ (function_eval H_func z H_mem) ∈ᴮ y ⊓ pair z (function_eval H_func z H_mem) ∈ᴮ f :=
  (function_eval_exists H_func z H_mem).choose_spec

lemma function_eval_mem_codomain {x y f : bSet 𝔹} {Γ : 𝔹} {H_func : Γ ≤ is_function x y f}
    {z : bSet 𝔹} {H_mem : Γ ≤ z ∈ᴮ x} :
    Γ ≤ (function_eval H_func z H_mem) ∈ᴮ y :=
  function_eval_spec.trans inf_le_left

lemma function_eval_pair_mem {x y f : bSet 𝔹} {Γ : 𝔹} {H_func : Γ ≤ is_function x y f}
    {z : bSet 𝔹} {H_mem : Γ ≤ z ∈ᴮ x} :
    Γ ≤ pair z (function_eval H_func z H_mem) ∈ᴮ f :=
  function_eval_spec.trans inf_le_right

lemma surjects_onto_of_injects_into' {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ injects_into x y)
    (H_exists_mem : Γ ≤ exists_mem x) : Γ ≤ surjects_onto y x := by

  apply surjects_onto_of_larger_than_and_exists_mem _ H_exists_mem

  simp only [larger_than, injects_into] at *

  apply le_trans (le_inf H_inj le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro f

  apply le_iSup_of_le (image x y f)
  apply le_iSup_of_le (inj_inverse
    (inf_le_left.trans inf_le_left : _ ≤ is_func' x y f)
    (inf_le_left.trans inf_le_right : _ ≤ is_inj f))

  refine le_inf (le_inf image_subset (le_inf ?_ ?_)) ?_
  ·
    exact inj_inverse_is_func (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
  ·
    exact inj_inverse_is_total (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
  ·
    exact inj_inverse_is_surj (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)

def functionMk {u : bSet 𝔹} (F : u.type → bSet 𝔹)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : bSet 𝔹 :=
  ⟨u.type, fun a => pair (u.func a) (F a), u.bval⟩

@[simp] lemma functionMk_type {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} :
    (functionMk F h_congr).type = u.type := rfl

@[simp] lemma functionMk_func {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} :
    (functionMk F h_congr).func i = pair (u.func i) (F i) := rfl

@[simp] lemma functionMk_bval {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} :
    (functionMk F h_congr).bval i = u.bval i := rfl

@[simp] lemma functionMk_self {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i : u.type} :
    u.bval i ≤ pair (u.func i) (F i) ∈ᴮ functionMk F h_congr := by
  simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]
  exact le_iSup_of_le i (le_inf le_rfl bv_refl)

def check'' {α : Type u} (A : α → bSet 𝔹) : bSet 𝔹 := ⟨α, A, fun _ => ⊤⟩

@[simp] lemma check''_type {α : Type u} {A : α → bSet 𝔹} : (check'' A).type = α := rfl
@[simp] lemma check''_bval {α : Type u} {A : α → bSet 𝔹} {i} : (check'' A).bval i = ⊤ := rfl
@[simp] lemma check''_func {α : Type u} {A : α → bSet 𝔹} {i} : (check'' A).func i = A i := rfl

lemma functionMk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
    (⊤ : 𝔹) ≤ is_func (functionMk F h_congr) := by

  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, top_inf_eq]

  have hmem_left : pair w₁ v₁ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ i : u.type, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  have hmem_right : pair w₂ v₂ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ j : u.type, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl

  calc pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)
      ≤ (⨆ i, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)) :=
        le_inf (inf_le_left.trans hmem_left) le_rfl
    _ ≤ ⨆ i, (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)) :=
        (iSup_inf_eq _ _).le
    _ ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂ := by
        apply iSup_le; intro i
        calc (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
              (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))
            ≤ (⨆ j, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) :=
              le_inf (inf_le_right.trans (inf_le_right.trans hmem_right)) le_rfl
          _ ≤ ⨆ j, (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) :=
              (iSup_inf_eq _ _).le
          _ ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂ := by
              apply iSup_le; intro j

              have hw1 : (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) ≤
                    pair w₁ v₁ =ᴮ pair (u.func i) (F i) :=
                inf_le_right.trans (inf_le_left.trans inf_le_right)
              have hw2 : (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) ≤
                    pair w₂ v₂ =ᴮ pair (u.func j) (F j) :=
                inf_le_left.trans inf_le_right
              rw [← deduction]

              set ctx4 := (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)))

              have hv1_Fi : ctx4 ⊓ w₁ =ᴮ w₂ ≤ v₁ =ᴮ F i :=
                le_trans inf_le_left (le_trans hw1 eq_of_eq_pair_right)

              have hv2_Fj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ v₂ =ᴮ F j :=
                le_trans inf_le_left (le_trans hw2 eq_of_eq_pair_right)

              have hw1_ui : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ u.func i :=
                le_trans inf_le_left (le_trans hw1 eq_of_eq_pair_left)

              have hw2_uj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₂ =ᴮ u.func j :=
                le_trans inf_le_left (le_trans hw2 eq_of_eq_pair_left)

              have hw12 : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ w₂ := inf_le_right

              have h_ui_uj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ u.func i =ᴮ u.func j :=
                bv_trans (bv_symm hw1_ui) (bv_trans hw12 hw2_uj)

              have h_Fi_Fj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ F i =ᴮ F j :=
                le_trans h_ui_uj (h_congr i j)

              exact bv_trans hv1_Fi (bv_trans h_Fi_Fj (bv_symm hv2_Fj))

lemma functionMk_inj_of_inj {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    (h_inj : ∀ i j, i ≠ j → F i =ᴮ F j ≤ ⊥)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
    (⊤ : 𝔹) ≤ is_inj (functionMk F h_congr) := by

  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, top_inf_eq]

  have hmem_left : pair w₁ v₁ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ i : u.type, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  have hmem_right : pair w₂ v₂ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ j : u.type, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl

  calc pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂
      ≤ (⨆ i, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂) :=
        le_inf (inf_le_left.trans (inf_le_left.trans hmem_left)) le_rfl
    _ ≤ ⨆ i, (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂) :=
        (iSup_inf_eq _ _).le
    _ ≤ w₁ =ᴮ w₂ := by
        apply iSup_le; intro i
        calc (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
              (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂)
            ≤ (⨆ j, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂)) :=
              le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans hmem_right))) le_rfl
          _ ≤ ⨆ j, (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂)) :=
              (iSup_inf_eq _ _).le
          _ ≤ w₁ =ᴮ w₂ := by
              apply iSup_le; intro j
              set ctx5 := (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ⊓ v₁ =ᴮ v₂))

              have hw1_ui : ctx5 ≤ w₁ =ᴮ u.func i :=
                inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left))
              have hv1_Fi : ctx5 ≤ v₁ =ᴮ F i :=
                inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right))

              have hw2_uj : ctx5 ≤ w₂ =ᴮ u.func j :=
                inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left)
              have hv2_Fj : ctx5 ≤ v₂ =ᴮ F j :=
                inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right)

              have hv12 : ctx5 ≤ v₁ =ᴮ v₂ :=
                inf_le_right.trans (inf_le_right.trans inf_le_right)
              by_cases h_ij : i = j
              ·
                subst h_ij
                exact bv_trans hw1_ui (bv_symm hw2_uj)
              ·

                have hFiFj : ctx5 ≤ F i =ᴮ F j :=
                  bv_trans (bv_symm hv1_Fi) (bv_trans hv12 hv2_Fj)
                have h_bot : ctx5 ≤ ⊥ :=
                  le_trans hFiFj (h_inj i j h_ij)
                exact le_trans h_bot bot_le

lemma bot_of_mem_self {x : bSet 𝔹} : (⊤ : 𝔹) ≤ (x ∈ᴮ x ⟹ ⊥) := by
  induction x using bSet.rec' with
  | _ x IH =>

    rw [← deduction, top_inf_eq]

    rw [mem_unfold]; apply iSup_le; intro i

    have h_mem : x.bval i ⊓ x =ᴮ x.func i ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_left (mem_mk'' le_rfl)
    have h_self_mem : x.bval i ⊓ x =ᴮ x.func i ≤ x.func i ∈ᴮ x.func i :=
      le_trans (le_inf inf_le_right h_mem) subst_congr_mem_right
    have h_bot_iff : (⊤ : 𝔹) ≤ x.func i ∈ᴮ x.func i ⟹ ⊥ := IH i
    rw [← deduction, top_inf_eq] at h_bot_iff
    exact le_trans h_self_mem h_bot_iff

lemma bot_of_mem_self' {x : bSet 𝔹} {Γ} (H : Γ ≤ (x ∈ᴮ x)) : Γ ≤ ⊥ := by
  have h := @bot_of_mem_self 𝔹 _ x

  calc Γ ≤ ⊤ ⊓ x ∈ᴮ x := le_inf le_top H
    _ ≤ ⊥ := by rwa [← deduction] at h

lemma bot_of_zero_eq_one {Γ : 𝔹} (H : Γ ≤ (0 : bSet 𝔹) =ᴮ 1) : Γ ≤ ⊥ := by
  apply bot_of_mem_self'

  exact bv_rw' H (ϕ := fun z => (0 : bSet 𝔹) ∈ᴮ z)
    (h_congr := B_ext_mem_right) (H_new := zero_mem_one)

lemma bot_of_mem_mem (x y : bSet 𝔹) : (⊤ : 𝔹) ≤ ((x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥) := by
  induction x using bSet.rec' generalizing y with
  | _ x IHx =>
    induction y using bSet.rec' with
    | _ y IHy =>

      rw [← deduction, top_inf_eq]

      rw [mem_unfold (v := y), mem_unfold (v := x)]

      calc (⨆ a'' : y.type, y.bval a'' ⊓ x =ᴮ y.func a'') ⊓
            (⨆ a' : x.type, x.bval a' ⊓ y =ᴮ x.func a')
          ≤ ⨆ a'' : y.type, (y.bval a'' ⊓ x =ᴮ y.func a'') ⊓
              (⨆ a' : x.type, x.bval a' ⊓ y =ᴮ x.func a') := (iSup_inf_eq _ _).le
        _ ≤ ⊥ := by
            apply iSup_le; intro a''
            calc (y.bval a'' ⊓ x =ᴮ y.func a'') ⊓
                (⨆ a' : x.type, x.bval a' ⊓ y =ᴮ x.func a')
                ≤ ⨆ a' : x.type, (x.bval a' ⊓ y =ᴮ x.func a') ⊓
                    (y.bval a'' ⊓ x =ᴮ y.func a'') := by
                      rw [inf_comm]; exact (iSup_inf_eq _ _).le
              _ ≤ ⊥ := by
                  apply iSup_le; intro a'

                  have h_IH := IHx a' (y.func a'')
                  rw [← deduction, top_inf_eq] at h_IH
                  apply le_trans _ h_IH

                  refine le_inf ?_ ?_
                  ·

                    have h1 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        x.func a' ∈ᴮ x :=
                      inf_le_left.trans (inf_le_left.trans (mem_mk'' le_rfl))
                    have h2 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        x =ᴮ y.func a'' := inf_le_right.trans inf_le_right

                    exact le_trans (le_inf h2 h1) subst_congr_mem_right
                  ·

                    have h3 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        y.func a'' ∈ᴮ y :=
                      inf_le_right.trans (inf_le_left.trans (mem_mk'' le_rfl))
                    have h4 : (x.bval a' ⊓ y =ᴮ x.func a') ⊓ (y.bval a'' ⊓ x =ᴮ y.func a'') ≤
                        y =ᴮ x.func a' := inf_le_left.trans inf_le_right

                    exact le_trans (le_inf h4 h3) subst_congr_mem_right

lemma bot_of_mem_mem' (x y : bSet 𝔹) {Γ} (H : Γ ≤ x ∈ᴮ y) (H' : Γ ≤ y ∈ᴮ x) : Γ ≤ ⊥ := by
  have h : (⊤ : 𝔹) ≤ (x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥ := bot_of_mem_mem x y
  calc Γ ≤ ⊤ ⊓ (x ∈ᴮ y ⊓ y ∈ᴮ x) := le_inf le_top (le_inf H H')
    _ ≤ ⊥ := by rwa [← deduction] at h

end extras

section bSet_check_extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

lemma check_powerset_subset_powerset (x : PSet) {Γ : 𝔹} :
    Γ ≤ (check (PSet.powerset x) : bSet 𝔹) ⊆ᴮ (bv_powerset (check x)) := by

  rw [subset_unfold']
  apply le_iInf; intro z; rw [← deduction]

  rw [mem_powerset_iff]

  have h_mem : Γ ⊓ z ∈ᴮ (check (PSet.powerset x) : bSet 𝔹) ≤
      ⨆ p : (PSet.powerset x).Type, z =ᴮ check ((PSet.powerset x).Func p) := by
    calc Γ ⊓ z ∈ᴮ (check (PSet.powerset x) : bSet 𝔹)
        ≤ z ∈ᴮ (check (PSet.powerset x) : bSet 𝔹) := inf_le_right
      _ = ⨆ p, ⊤ ⊓ z =ᴮ check ((PSet.powerset x).Func p) := mem_unfold
      _ = ⨆ p, z =ᴮ check ((PSet.powerset x).Func p) := by simp [top_inf_eq]

  apply (le_inf h_mem le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans
  apply iSup_le; intro p

  have h_sub : (PSet.powerset x).Func p ⊆ x :=
    PSet.mem_powerset.mp (PSet.func_mem _ p)

  have h_csub : Γ ≤ check ((PSet.powerset x).Func p) ⊆ᴮ (check x : bSet 𝔹) :=
    check_subset h_sub

  exact le_trans (le_inf (le_trans le_top (check_subset h_sub)) inf_le_left) subst_congr_subset_left

lemma check_functions_subset_functions {x y : PSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check (PSet.functions x y) : bSet 𝔹) ⊆ᴮ functions (check x) (check y) := by

  rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]

  rw [check_mem_as_iSup, inf_iSup_eq']
  apply iSup_le; intro i

  have h_mem : (PSet.functions x y).Func i ∈ PSet.functions x y :=
    PSet.func_mem (PSet.functions x y) i
  rw [PSet.mem_functions_iff] at h_mem

  have h_in_func : (⊤ : 𝔹) ≤ check ((PSet.functions x y).Func i) ∈ᴮ functions (check x) (check y) :=
    mem_functions_iff.mpr (le_trans le_top (check_is_func h_mem))

  exact bv_rw' (H := inf_le_right) (ϕ := fun z => z ∈ᴮ functions (check x) (check y))
    (h_congr := B_ext_mem_left) (H_new := le_trans le_top h_in_func)

@[simp] lemma check_mem'' {y : PSet} {i : y.Type} :
    ((check (y.Func i) : bSet 𝔹)) ∈ᴮ (check y) = (⊤ : 𝔹) := by
  apply top_unique; simp

lemma of_nat_inj' {n k : ℕ} (H_neq : n ≠ k) :
    ((of_nat n : bSet 𝔹) =ᴮ of_nat k) = ⊥ :=
  check_bv_eq_bot_of_not_equiv (PSet.ofNat_inj H_neq)

lemma of_nat_mem_of_lt' {k₁ k₂ : ℕ} (H_lt : k₁ < k₂) {Γ : 𝔹} :
    Γ ≤ (of_nat k₁ : bSet 𝔹) ∈ᴮ (of_nat k₂) :=
  check_mem (PSet.ofNat_mem_of_lt H_lt)

@[simp] lemma zero_eq_some_none' {Γ : 𝔹} :
    Γ ≤ (0 : bSet 𝔹) =ᴮ (𝟚 : bSet 𝔹).func (some none) :=
  bv_refl

end bSet_check_extras

section powerset_section
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable (x : bSet 𝔹)

def powerset_injects_F : (bv_powerset x).type → (functions x 𝟚).type :=
  fun χ pr =>
    (x.func pr.1 ∈ᴮ set_of_indicator χ ⊓ ((𝟚 : bSet 𝔹).func pr.2 =ᴮ 0)) ⊔
    (x.func pr.1 ∈ᴮ subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ)ᶜ) ⊓
      ((𝟚 : bSet 𝔹).func pr.2 =ᴮ 1))

lemma mem_powerset_injects_F_iff {Γ : 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} :
    Γ ≤ pair z 0 ∈ᴮ (functions x 𝟚).func (powerset_injects_F x χ) ↔
    Γ ≤ z ∈ᴮ set_of_indicator χ := by

  have hFuncs : pair z 0 ∈ᴮ (functions x 𝟚).func (powerset_injects_F x χ) =
      ⨆ pr : x.type × (𝟚 : bSet 𝔹).type, (powerset_injects_F x χ pr) ⊓
        pair z 0 =ᴮ pair (x.func pr.1) ((𝟚 : bSet 𝔹).func pr.2) := by
    rw [functions_func]; rfl
  have hSOI : z ∈ᴮ set_of_indicator χ =
      ⨆ i : x.type, χ i ⊓ z =ᴮ x.func i := by rfl
  constructor
  · intro H
    rw [hFuncs] at H

    apply le_trans H
    apply iSup_le; intro ⟨i, j⟩
    simp only [powerset_injects_F, inf_sup_right]
    apply bv_or_elim
    ·

      set ctx₁ := (x.func i ∈ᴮ set_of_indicator χ ⊓ (𝟚 : bSet 𝔹).func j =ᴮ 0) ⊓
          pair z 0 =ᴮ pair (x.func i) ((𝟚 : bSet 𝔹).func j)
      have h_zeq : ctx₁ ≤ z =ᴮ x.func i := (pair_eq_pair_iff.mp inf_le_right).1
      have h_xi_mem : ctx₁ ≤ x.func i ∈ᴮ set_of_indicator χ := inf_le_left.trans inf_le_left
      exact bv_rw' (H := h_zeq) (h_congr := B_ext_mem_left) (H_new := h_xi_mem)
    ·
      set ctx₂ := (x.func i ∈ᴮ subset.mk (fun i_1 => (x.func i_1 ∈ᴮ set_of_indicator χ)ᶜ) ⊓
          (𝟚 : bSet 𝔹).func j =ᴮ 1) ⊓ pair z 0 =ᴮ pair (x.func i) ((𝟚 : bSet 𝔹).func j)
      have h_0eq : ctx₂ ≤ (0 : bSet 𝔹) =ᴮ (𝟚 : bSet 𝔹).func j :=
        (pair_eq_pair_iff.mp inf_le_right).2
      have h_1eq : ctx₂ ≤ (𝟚 : bSet 𝔹).func j =ᴮ 1 := inf_le_left.trans inf_le_right
      exact (bot_of_zero_eq_one (le_trans (le_inf h_0eq h_1eq) bv_eq_trans)).trans bot_le
  · intro H

    rw [hFuncs]
    apply le_trans H
    apply iSup_le; intro i
    apply le_iSup_of_le (i, (some none : (𝟚 : bSet 𝔹).type))
    unfold powerset_injects_F
    simp only [Prod.fst, Prod.snd]
    apply le_inf
    ·
      apply le_trans _ le_sup_left
      apply le_inf
      ·
        exact le_iSup_of_le i (le_inf inf_le_left bv_refl)
      ·
        exact bv_symm zero_eq_some_none'
    ·
      exact pair_congr inf_le_right (bv_symm zero_eq_some_none')

private lemma subset_mk_compl_of_subset {x : bSet 𝔹} {χ_a χ_b : x.type → 𝔹} {Γ : 𝔹}
    (H_ba : Γ ≤ set_of_indicator χ_b ⊆ᴮ set_of_indicator χ_a) :
    Γ ≤ subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ_a)ᶜ) ⊆ᴮ
        subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ_b)ᶜ) := by
  rw [subset_unfold]
  apply le_iInf; intro k'; rw [← deduction]

  rw [mem_subset.mk_iff]
  apply le_iSup_of_le k'
  apply le_inf (le_trans inf_le_right (le_trans inf_le_left bv_refl))
  apply le_inf
  ·

    rw [← imp_bot, ← deduction]

    apply bv_absurd (x.func k' ∈ᴮ set_of_indicator χ_a)
    ·

      exact mem_of_mem_subset (le_trans (le_trans inf_le_left inf_le_left) H_ba) inf_le_right
    ·
      exact inf_le_left.trans (inf_le_right.trans inf_le_left)
  · exact inf_le_right.trans inf_le_right

lemma powerset_injects_F_ext : ∀ (χ₁ χ₂ : (bv_powerset x).type) {Γ : 𝔹},
    Γ ≤ (bv_powerset x).func χ₁ =ᴮ (bv_powerset x).func χ₂ →
    Γ ≤ (functions x 𝟚).func (powerset_injects_F x χ₁) =ᴮ
        (functions x 𝟚).func (powerset_injects_F x χ₂) := by
  intro χ₁ χ₂ Γ H
  have H₁ : Γ ≤ set_of_indicator χ₁ ⊆ᴮ set_of_indicator χ₂ :=
    le_trans H (le_trans (le_of_eq eq_iff_subset_subset) inf_le_left)
  have H₂ : Γ ≤ set_of_indicator χ₂ ⊆ᴮ set_of_indicator χ₁ :=
    le_trans H (le_trans (le_of_eq eq_iff_subset_subset) inf_le_right)

  suffices helper : ∀ (χ_a χ_b : (bv_powerset x).type),
      Γ ≤ set_of_indicator χ_a ⊆ᴮ set_of_indicator χ_b →
      Γ ≤ set_of_indicator χ_b ⊆ᴮ set_of_indicator χ_a →
      Γ ≤ set_of_indicator (powerset_injects_F x χ_a) ⊆ᴮ
          set_of_indicator (powerset_injects_F x χ_b) by
    rw [eq_iff_subset_subset]
    exact le_inf (helper χ₁ χ₂ H₁ H₂) (helper χ₂ χ₁ H₂ H₁)
  intro χ_a χ_b H_ab H_ba

  have h_compl_sub : Γ ≤ subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ_a)ᶜ) ⊆ᴮ
      subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ_b)ᶜ) :=
    subset_mk_compl_of_subset H_ba
  rw [subset_unfold]
  apply le_iInf; intro ⟨k, l⟩; rw [← deduction]
  apply le_iSup_of_le (k, l)
  apply le_inf _ bv_refl
  show Γ ⊓ ((x.func k ∈ᴮ set_of_indicator χ_a ⊓ ((𝟚 : bSet 𝔹).func l =ᴮ 0)) ⊔
    (x.func k ∈ᴮ subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ_a)ᶜ) ⊓
      ((𝟚 : bSet 𝔹).func l =ᴮ 1))) ≤
    (x.func k ∈ᴮ set_of_indicator χ_b ⊓ ((𝟚 : bSet 𝔹).func l =ᴮ 0)) ⊔
    (x.func k ∈ᴮ subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ_b)ᶜ) ⊓
      ((𝟚 : bSet 𝔹).func l =ᴮ 1))
  rw [inf_sup_left]
  apply bv_or_elim
  ·
    apply le_sup_left.trans'
    apply le_inf
    · exact mem_of_mem_subset (le_trans inf_le_left H_ab) (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans inf_le_right
  ·
    apply le_sup_right.trans'
    apply le_inf
    ·
      exact mem_of_mem_subset (le_trans inf_le_left h_compl_sub) (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans inf_le_right

lemma powerset_injects_F_subset_prod {χ : x.type → 𝔹} {Γ : 𝔹}
    (H_le : Γ ≤ set_of_indicator χ ⊆ᴮ x) :
    Γ ≤ (bv_powerset (prod x 𝟚)).func (powerset_injects_F x χ) ⊆ᴮ prod x 𝟚 := by

  rw [show (bv_powerset (prod x 𝟚)).func (powerset_injects_F x χ) =
      set_of_indicator (u := prod x 𝟚) (powerset_injects_F x χ) from rfl]
  rw [subset_unfold]
  apply le_iInf; intro ⟨i, j⟩; rw [← deduction]

  have hxi_mem_x : Γ ⊓ powerset_injects_F x χ (i, j) ≤ x.func i ∈ᴮ x := by
    simp only [powerset_injects_F]
    rw [inf_sup_left]
    apply bv_or_elim
    ·
      exact mem_of_mem_subset (le_trans inf_le_left H_le) (inf_le_right.trans inf_le_left)
    ·
      exact mem_of_mem_subset (le_trans le_top subset.mk_subset) (inf_le_right.trans inf_le_left)
  have htwo_mem : Γ ⊓ powerset_injects_F x χ (i, j) ≤ (𝟚 : bSet 𝔹).func j ∈ᴮ (𝟚 : bSet 𝔹) :=
    @mem_check_of_mem 𝔹 _ (PSet.ofNat 2) j (Γ := Γ ⊓ powerset_injects_F x χ (i, j))
  exact prod_mem hxi_mem_x htwo_mem

lemma powerset_injects_F_mem : ∀ (i : (bv_powerset x).type) {Γ : 𝔹},
    Γ ≤ (bv_powerset x).bval i →
    Γ ≤ (functions x 𝟚).bval (powerset_injects_F x i) ∧ Γ ≤ (⊤ : 𝔹) := by
  intro χ Γ H_le

  change Γ ≤ set_of_indicator χ ⊆ᴮ x at H_le
  refine ⟨?_, le_top⟩

  simp only [functions_bval]

  refine le_inf (le_inf ?_ ?_) ?_
  ·

    have hF_mem : ∀ (w v : bSet 𝔹), pair w v ∈ᴮ (bv_powerset (prod x 𝟚)).func (powerset_injects_F x χ) ≤
        ⨆ pr : (prod x 𝟚).type, powerset_injects_F x χ pr ⊓ pair w v =ᴮ (prod x 𝟚).func pr := by
      intro w v
      change pair w v ∈ᴮ set_of_indicator (u := prod x 𝟚) (powerset_injects_F x χ) ≤ _
      simp only [mem_unfold, set_of_indicator_bval, set_of_indicator_func]
      exact le_refl _
    apply le_iInf; intro w₁; apply le_iInf; intro w₂
    apply le_iInf; intro v₁; apply le_iInf; intro v₂
    rw [← deduction, ← deduction]

    apply (le_inf (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans (hF_mem w₁ v₁)))) le_rfl).trans
    apply (iSup_inf_eq _ _).le.trans; apply iSup_le; intro pr₁; obtain ⟨i₁, j₁⟩ := pr₁
    simp only [prod_func, powerset_injects_F, Prod.fst, Prod.snd]

    apply (le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans
      (inf_le_right.trans (hF_mem w₂ v₂))))) le_rfl).trans
    apply (iSup_inf_eq _ _).le.trans; apply iSup_le; intro pr₂; obtain ⟨i₂, j₂⟩ := pr₂
    simp only [prod_func, powerset_injects_F, Prod.fst, Prod.snd]

    set ctx2 := ((x.func i₂ ∈ᴮ set_of_indicator χ ⊓ ((𝟚 : bSet 𝔹).func j₂ =ᴮ 0)) ⊔
          (x.func i₂ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
            ((𝟚 : bSet 𝔹).func j₂ =ᴮ 1))) ⊓
        pair w₂ v₂ =ᴮ pair (x.func i₂) ((𝟚 : bSet 𝔹).func j₂) ⊓
      (((x.func i₁ ∈ᴮ set_of_indicator χ ⊓ ((𝟚 : bSet 𝔹).func j₁ =ᴮ 0)) ⊔
          (x.func i₁ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
            ((𝟚 : bSet 𝔹).func j₁ =ᴮ 1))) ⊓
        pair w₁ v₁ =ᴮ pair (x.func i₁) ((𝟚 : bSet 𝔹).func j₁) ⊓
        (Γ ⊓ (pair w₁ v₁ ∈ᴮ (bv_powerset (prod x 𝟚)).func (powerset_injects_F x χ) ⊓
                pair w₂ v₂ ∈ᴮ (bv_powerset (prod x 𝟚)).func (powerset_injects_F x χ)) ⊓
          w₁ =ᴮ w₂))

    have hF2 : ctx2 ≤ (x.func i₂ ∈ᴮ set_of_indicator χ ⊓ (𝟚 : bSet 𝔹).func j₂ =ᴮ 0) ⊔
        (x.func i₂ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
          (𝟚 : bSet 𝔹).func j₂ =ᴮ 1) :=
      inf_le_left.trans inf_le_left
    have hw2xi2 : ctx2 ≤ w₂ =ᴮ x.func i₂ :=
      inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left)
    have hv2j2 : ctx2 ≤ v₂ =ᴮ (𝟚 : bSet 𝔹).func j₂ :=
      inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right)
    have hF1 : ctx2 ≤ (x.func i₁ ∈ᴮ set_of_indicator χ ⊓ (𝟚 : bSet 𝔹).func j₁ =ᴮ 0) ⊔
        (x.func i₁ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
          (𝟚 : bSet 𝔹).func j₁ =ᴮ 1) :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hw1xi1 : ctx2 ≤ w₁ =ᴮ x.func i₁ :=
      inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left))
    have hv1j1 : ctx2 ≤ v₁ =ᴮ (𝟚 : bSet 𝔹).func j₁ :=
      inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right))
    have hw12 : ctx2 ≤ w₁ =ᴮ w₂ :=
      inf_le_right.trans (inf_le_right.trans inf_le_right)

    have hxi1xi2 : ctx2 ≤ x.func i₁ =ᴮ x.func i₂ :=
      le_trans (le_inf (bv_symm hw1xi1) (le_trans (le_inf hw12 hw2xi2) bv_eq_trans)) bv_eq_trans

    have subset_mk_to_compl : ∀ (i : x.type) {Δ : 𝔹},
        Δ ≤ x.func i ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) →
        Δ ≤ (x.func i ∈ᴮ set_of_indicator χ)ᶜ := by
      intro i Δ h
      rw [mem_subset.mk_iff] at h
      apply h.trans; apply iSup_le; intro k

      exact bv_rw' (H := inf_le_left)
        (h_congr := B_ext_neg (h := B_ext_mem_left (y := set_of_indicator χ)))
        (H_new := inf_le_right.trans inf_le_left)

    apply le_trans (le_inf le_rfl hF1); apply bv_or_elim_right
    ·
      set ctxL₁ := ctx2 ⊓ (x.func i₁ ∈ᴮ set_of_indicator χ ⊓ (𝟚 : bSet 𝔹).func j₁ =ᴮ 0)
      have hmem1 : ctxL₁ ≤ x.func i₁ ∈ᴮ set_of_indicator χ := inf_le_right.trans inf_le_left
      have hj1_0 : ctxL₁ ≤ (𝟚 : bSet 𝔹).func j₁ =ᴮ 0 := inf_le_right.trans inf_le_right
      apply le_trans (le_inf le_rfl (inf_le_left.trans hF2)); apply bv_or_elim_right
      ·

        have hj2_0 : ctxL₁ ⊓ (x.func i₂ ∈ᴮ set_of_indicator χ ⊓ (𝟚 : bSet 𝔹).func j₂ =ᴮ 0) ≤
            (𝟚 : bSet 𝔹).func j₂ =ᴮ 0 := inf_le_right.trans inf_le_right
        set ctxLL := ctxL₁ ⊓ (x.func i₂ ∈ᴮ set_of_indicator χ ⊓ (𝟚 : bSet 𝔹).func j₂ =ᴮ 0)

        exact le_trans
          (le_inf
            (le_trans (le_inf (inf_le_left.trans (inf_le_left.trans hv1j1))
              (inf_le_left.trans hj1_0)) bv_eq_trans)
            (le_trans (le_inf (bv_symm hj2_0)
              (bv_symm (inf_le_left.trans (inf_le_left.trans hv2j2)))) bv_eq_trans))
          bv_eq_trans
      ·
        set ctxLR := ctxL₁ ⊓ (x.func i₂ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
            (𝟚 : bSet 𝔹).func j₂ =ᴮ 1)
        have hnot2_chi : ctxLR ≤ (x.func i₂ ∈ᴮ set_of_indicator χ)ᶜ :=
          subset_mk_to_compl i₂ (inf_le_right.trans inf_le_left)

        have h_xi_lr : ctxLR ≤ x.func i₁ =ᴮ x.func i₂ :=
          inf_le_left.trans (inf_le_left.trans hxi1xi2)
        have hmem2_chi : ctxLR ≤ x.func i₂ ∈ᴮ set_of_indicator χ :=
          bv_rw' (H := bv_symm h_xi_lr)
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans hmem1)
        exact le_trans (le_inf hmem2_chi hnot2_chi)
          (le_of_eq inf_compl_eq_bot |>.trans bot_le)
    ·
      set ctxR₁ := ctx2 ⊓ (x.func i₁ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
          (𝟚 : bSet 𝔹).func j₁ =ᴮ 1)
      have hnot1_chi : ctxR₁ ≤ (x.func i₁ ∈ᴮ set_of_indicator χ)ᶜ :=
        subset_mk_to_compl i₁ (inf_le_right.trans inf_le_left)
      have hj1_1 : ctxR₁ ≤ (𝟚 : bSet 𝔹).func j₁ =ᴮ 1 := inf_le_right.trans inf_le_right
      apply le_trans (le_inf le_rfl (inf_le_left.trans hF2)); apply bv_or_elim_right
      ·
        set ctxRL := ctxR₁ ⊓ (x.func i₂ ∈ᴮ set_of_indicator χ ⊓ (𝟚 : bSet 𝔹).func j₂ =ᴮ 0)
        have hmem2 : ctxRL ≤ x.func i₂ ∈ᴮ set_of_indicator χ := inf_le_right.trans inf_le_left

        have h_xi_rl : ctxRL ≤ x.func i₁ =ᴮ x.func i₂ :=
          inf_le_left.trans (inf_le_left.trans hxi1xi2)
        have hmem2_via_i1 : ctxRL ≤ x.func i₁ ∈ᴮ set_of_indicator χ :=
          bv_rw' (H := h_xi_rl)
            (h_congr := B_ext_mem_left) (H_new := hmem2)
        exact le_trans (le_inf hmem2_via_i1 (inf_le_left.trans hnot1_chi))
          (le_of_eq inf_compl_eq_bot |>.trans bot_le)
      ·

        have hj2_1 : ctxR₁ ⊓ (x.func i₂ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
              (𝟚 : bSet 𝔹).func j₂ =ᴮ 1) ≤
            (𝟚 : bSet 𝔹).func j₂ =ᴮ 1 := inf_le_right.trans inf_le_right
        set ctxRR := ctxR₁ ⊓ (x.func i₂ ∈ᴮ subset.mk (fun k => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
            (𝟚 : bSet 𝔹).func j₂ =ᴮ 1)
        exact le_trans
          (le_inf
            (le_trans (le_inf (inf_le_left.trans (inf_le_left.trans hv1j1))
              (inf_le_left.trans hj1_1)) bv_eq_trans)
            (le_trans (le_inf (bv_symm hj2_1)
              (bv_symm (inf_le_left.trans (inf_le_left.trans hv2j2)))) bv_eq_trans))
          bv_eq_trans
  ·
    rw [is_total_iff_is_total']
    apply le_iInf; intro i; rw [← deduction]

    have h_split : Γ ⊓ x.bval i ≤
        (Γ ⊓ x.bval i) ⊓ x.func i ∈ᴮ set_of_indicator χ ⊔
        (Γ ⊓ x.bval i) ⊓ (x.func i ∈ᴮ set_of_indicator χ)ᶜ := by
      rw [← inf_sup_left]; simp [sup_compl_eq_top]
    apply le_trans h_split; apply bv_or_elim
    ·
      set ctx_iS := (Γ ⊓ x.bval i) ⊓ x.func i ∈ᴮ set_of_indicator χ
      have hbval : ctx_iS ≤ x.bval i := inf_le_left.trans inf_le_right
      have hmem_chi : ctx_iS ≤ x.func i ∈ᴮ set_of_indicator χ := inf_le_right
      apply le_iSup_of_le (some none)

      refine le_inf le_top ?_

      change ctx_iS ≤ pair (x.func i) ((𝟚 : bSet 𝔹).func (some none)) ∈ᴮ
          set_of_indicator (u := prod x 𝟚) (powerset_injects_F x χ)
      rw [mem_unfold]
      apply le_iSup_of_le (i, some none)
      simp only [set_of_indicator_bval, set_of_indicator_func, prod_func, prod_bval, powerset_injects_F,
        check_bval_top, inf_top_eq, Prod.fst, Prod.snd]

      refine le_inf ?_ bv_refl
      apply bv_or_left
      exact le_inf hmem_chi bv_refl
    ·
      set ctx_iN := (Γ ⊓ x.bval i) ⊓ (x.func i ∈ᴮ set_of_indicator χ)ᶜ
      have hbval : ctx_iN ≤ x.bval i := inf_le_left.trans inf_le_right
      have hnot_chi : ctx_iN ≤ (x.func i ∈ᴮ set_of_indicator χ)ᶜ := inf_le_right
      apply le_iSup_of_le none
      refine le_inf le_top ?_
      change ctx_iN ≤ pair (x.func i) ((𝟚 : bSet 𝔹).func none) ∈ᴮ
          set_of_indicator (u := prod x 𝟚) (powerset_injects_F x χ)
      rw [mem_unfold]
      apply le_iSup_of_le (i, none)
      simp only [set_of_indicator_bval, set_of_indicator_func, prod_func, prod_bval, powerset_injects_F,
        check_bval_top, inf_top_eq, Prod.fst, Prod.snd]
      refine le_inf ?_ bv_refl
      apply bv_or_right

      refine le_inf ?_ bv_refl

      rw [mem_subset.mk_iff]
      apply le_iSup_of_le i

      exact le_inf bv_refl (le_inf hnot_chi hbval)
  ·
    exact @powerset_injects_F_subset_prod 𝔹 _ x χ Γ H_le

lemma powerset_injects_F_inj : ∀ (i j : (bv_powerset x).type) {Γ : 𝔹},
    Γ ≤ (functions x 𝟚).func (powerset_injects_F x i) =ᴮ
        (functions x 𝟚).func (powerset_injects_F x j) →
    Γ ≤ (bv_powerset x).func i =ᴮ (bv_powerset x).func j := by
  intro i j Γ H

  apply mem_ext
  ·
    apply le_iInf; intro z; rw [← deduction]

    show Γ ⊓ z ∈ᴮ set_of_indicator i ≤ z ∈ᴮ set_of_indicator j

    have hFi : Γ ⊓ z ∈ᴮ set_of_indicator i ≤ pair z 0 ∈ᴮ (functions x 𝟚).func (powerset_injects_F x i) :=
      (mem_powerset_injects_F_iff (x := x) (χ := i)).mpr inf_le_right
    have hFi_to_Fj : Γ ⊓ z ∈ᴮ set_of_indicator i ≤ pair z 0 ∈ᴮ (functions x 𝟚).func (powerset_injects_F x j) :=
      bv_rw'' (H := le_trans inf_le_left H) hFi B_ext_mem_right
    exact (mem_powerset_injects_F_iff (x := x) (χ := j)).mp hFi_to_Fj
  ·
    apply le_iInf; intro z; rw [← deduction]
    show Γ ⊓ z ∈ᴮ set_of_indicator j ≤ z ∈ᴮ set_of_indicator i
    have hFj : Γ ⊓ z ∈ᴮ set_of_indicator j ≤ pair z 0 ∈ᴮ (functions x 𝟚).func (powerset_injects_F x j) :=
      (mem_powerset_injects_F_iff (x := x) (χ := j)).mpr inf_le_right
    have hFj_to_Fi : Γ ⊓ z ∈ᴮ set_of_indicator j ≤ pair z 0 ∈ᴮ (functions x 𝟚).func (powerset_injects_F x i) :=
      bv_rw'' (H := le_trans inf_le_left (bv_symm H)) hFj B_ext_mem_right
    exact (mem_powerset_injects_F_iff (x := x) (χ := i)).mp hFj_to_Fi

noncomputable def powerset_injects_f : bSet 𝔹 :=
  functionMk' (powerset_injects_F x) (fun _ => ⊤)
    (powerset_injects_F_ext x) (powerset_injects_F_mem x)

lemma powerset_injects_into_functions {Γ : 𝔹} :
    Γ ≤ injects_into (bv_powerset x) (functions x 𝟚) :=
  le_iSup_of_le (powerset_injects_f x)
    (le_inf (is_func'_of_is_function (functionMk'_is_function _ _ _ _))
            (functionMk'_is_inj _ _ _ _ (powerset_injects_F_inj x)))

end powerset_section

lemma check_succ_eq_succ_check {n : ℕ} {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] :
    (of_nat (n.succ) : bSet 𝔹) = succ (of_nat n) := by

  simp only [of_nat, succ]

  have h : PSet.ofNat n.succ = PSet.insert (PSet.ofNat n) (PSet.ofNat n) := by
    rw [Nat.succ_eq_add_one, PSet.ofNat_succ]; rfl
  conv_lhs => rw [h]
  exact check_insert (PSet.ofNat n) (PSet.ofNat n)

section ordinals
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

@[reducible] def epsilon_trichotomy (x : bSet 𝔹) : 𝔹 :=
  ⨅ y, y ∈ᴮ x ⟹ (⨅ z, z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))

@[reducible] def epsilon_well_founded (x : bSet 𝔹) : 𝔹 :=
  ⨅ u, u ⊆ᴮ x ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ))

def epsilon_well_orders (x : bSet 𝔹) : 𝔹 :=
  epsilon_trichotomy x ⊓ epsilon_well_founded x

@[reducible] def ewo (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x

@[simp] lemma B_ext_ewo : B_ext (fun w : bSet 𝔹 => epsilon_well_orders w) := by
  unfold epsilon_well_orders epsilon_trichotomy epsilon_well_founded
  apply B_ext_inf
  ·
    exact B_ext_iInf (h := fun y => B_ext_imp (h₁ := B_ext_mem_right) (h₂ :=
      B_ext_iInf (h := fun z => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
  ·
    exact B_ext_iInf (h := fun u => B_ext_imp (h₁ := B_ext_subset_right) (h₂ := B_ext_const))

lemma epsilon_dichotomy (x y z : bSet 𝔹) :
    epsilon_well_orders x ≤ y ∈ᴮ x ⟹ (z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)) := by
  unfold epsilon_well_orders
  rw [← deduction, ← deduction]

  have h1 : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
      y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
    have htri : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        epsilon_trichotomy x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hy_mem : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        y ∈ᴮ x := inf_le_left.trans inf_le_right
    have hz_mem : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        z ∈ᴮ x := inf_le_right
    have h_iinf_y : epsilon_trichotomy x ⊓ epsilon_well_founded x ⊓ y ∈ᴮ x ⊓ z ∈ᴮ x ≤
        ⨅ z', z' ∈ᴮ x ⟹ (y =ᴮ z' ⊔ y ∈ᴮ z' ⊔ z' ∈ᴮ y) :=
      le_trans (le_inf (htri.trans (iInf_le _ y)) hy_mem) bv_imp_elim
    exact le_trans (le_inf (h_iinf_y.trans (iInf_le _ z)) hz_mem) bv_imp_elim
  exact h1

def is_transitive (x : bSet 𝔹) : 𝔹 := ⨅ y, y ∈ᴮ x ⟹ y ⊆ᴮ x

lemma subset_of_mem_transitive {x w : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_transitive x)
    (H₂ : Γ ≤ w ∈ᴮ x) : Γ ≤ w ⊆ᴮ x :=
  le_trans (le_inf (le_trans H₁ (iInf_le _ w)) H₂) bv_imp_elim

@[simp] lemma B_ext_is_transitive : B_ext (is_transitive : bSet 𝔹 → 𝔹) := by
  unfold is_transitive
  exact B_ext_iInf (h := fun y => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_subset_right))

def Ord (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x ⊓ is_transitive x

lemma epsilon_trichotomy_of_Ord {x a b : bSet 𝔹} {Γ : 𝔹} (Ha_mem : Γ ≤ a ∈ᴮ x)
    (Hb_mem : Γ ≤ b ∈ᴮ x) (H_Ord : Γ ≤ Ord x) :
    Γ ≤ a =ᴮ b ⊔ a ∈ᴮ b ⊔ b ∈ᴮ a := by
  have h_tri : Γ ≤ epsilon_trichotomy x :=
    le_trans (le_trans H_Ord inf_le_left) inf_le_left
  have h1 : Γ ≤ ⨅ z, z ∈ᴮ x ⟹ (a =ᴮ z ⊔ a ∈ᴮ z ⊔ z ∈ᴮ a) :=
    le_trans (le_inf (le_trans h_tri (iInf_le _ a)) Ha_mem) bv_imp_elim
  exact le_trans (le_inf (le_trans h1 (iInf_le _ b)) Hb_mem) bv_imp_elim

lemma injects_into_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ injects_into x y := by

  rw [subset_unfold] at H

  set F : x.type → bSet 𝔹 := fun i => x.func i
  have h_congr : ∀ i j, x.func i =ᴮ x.func j ≤ F i =ᴮ F j := fun i j => le_refl _

  have h_func : (⊤ : 𝔹) ≤ is_func (functionMk F h_congr) := functionMk_is_func F h_congr

  have h_total : Γ ≤ is_total x y (functionMk F h_congr) := by
    rw [is_total_iff_is_total']; unfold is_total'
    apply le_iInf; intro i; rw [← deduction]

    have hxi_y : Γ ⊓ x.bval i ≤ x.func i ∈ᴮ y :=
      le_trans (le_inf (le_trans inf_le_left H |>.trans (iInf_le _ i)) inf_le_right) bv_imp_elim
    rw [mem_unfold] at hxi_y

    calc Γ ⊓ x.bval i
        ≤ (⨆ j : y.type, y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) :=
          le_inf hxi_y le_rfl
      _ ≤ ⨆ j, (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) :=
          (iSup_inf_eq _ _).le
      _ ≤ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ functionMk F h_congr := by
          apply iSup_le; intro j
          apply le_iSup_of_le j
          have hyj : (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) ≤ y.bval j :=
            inf_le_left.trans inf_le_left
          have hxij : (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) ≤
              x.func i =ᴮ y.func j := inf_le_left.trans inf_le_right
          have hxbi : (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) ≤ x.bval i :=
            inf_le_right.trans inf_le_right

          refine le_inf hyj ?_
          apply bv_rw' (H := bv_symm hxij) (ϕ := fun z => pair (x.func i) z ∈ᴮ functionMk F h_congr)
            (h_congr := B_ext_pair_mem_right)
          exact le_trans hxbi (functionMk_self (h_congr := h_congr))

  have h_inj : (⊤ : 𝔹) ≤ is_inj (functionMk F h_congr) := by

    apply le_iInf; intro w₁; apply le_iInf; intro w₂
    apply le_iInf; intro v₁; apply le_iInf; intro v₂
    rw [← deduction, top_inf_eq]
    have hmemL : pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ≤
        ⨆ i : x.type, x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i) := by
      simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
    have hmemR : pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ≤
        ⨆ j : x.type, x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j) := by
      simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
    set ctxI := pair w₁ v₁ ∈ᴮ functionMk F h_congr ⊓ pair w₂ v₂ ∈ᴮ functionMk F h_congr ⊓ v₁ =ᴮ v₂
    calc ctxI
        ≤ (⨆ i, x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI :=
          le_inf (inf_le_left.trans (inf_le_left.trans hmemL)) le_rfl
      _ ≤ ⨆ i, (x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI :=
          (iSup_inf_eq _ _).le
      _ ≤ w₁ =ᴮ w₂ := by
          apply iSup_le; intro i
          calc (x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI
              ≤ (⨆ j, x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j)) ⊓
                  ((x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI) :=
                le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans hmemR))) le_rfl
            _ ≤ ⨆ j, (x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j)) ⊓
                  ((x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI) :=
                (iSup_inf_eq _ _).le
            _ ≤ w₁ =ᴮ w₂ := by
                apply iSup_le; intro j
                set ctxJ := (x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j)) ⊓
                      ((x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI)
                have hw1xi : ctxJ ≤ w₁ =ᴮ x.func i :=
                  inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left))
                have hv1Fi : ctxJ ≤ v₁ =ᴮ F i :=
                  inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right))
                have hw2xj : ctxJ ≤ w₂ =ᴮ x.func j :=
                  inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left)
                have hv2Fj : ctxJ ≤ v₂ =ᴮ F j :=
                  inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right)
                have hv12 : ctxJ ≤ v₁ =ᴮ v₂ := inf_le_right.trans (inf_le_right.trans inf_le_right)

                have hxi_xj : ctxJ ≤ x.func i =ᴮ x.func j :=
                  bv_trans (bv_symm hv1Fi) (bv_trans hv12 hv2Fj)
                exact bv_trans hw1xi (bv_trans hxi_xj (bv_symm hw2xj))

  unfold injects_into
  apply le_iSup_of_le (functionMk F h_congr)
  apply le_inf
  · exact le_inf (le_top.trans h_func) h_total
  · exact le_top.trans h_inj

lemma injects_into_refl {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ injects_into x x :=
  injects_into_of_subset subset_self

lemma bSet_le_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) : Γ ≤ injects_into x y :=
  injects_into_of_subset H

lemma injection_into_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ injection_into x y :=
  injects_into_iff_injection_into.mp (injects_into_of_subset H)

def Card (y : bSet 𝔹) : 𝔹 := Ord y ⊓ ⨅ x, x ∈ᴮ y ⟹ (larger_than y x)ᶜ

lemma is_transitive_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ is_transitive y := by
  induction y using bSet.rec' generalizing x with
  | _ y IH =>

    apply le_iInf; intro w; rw [← deduction]

    rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]

    set ctx := Ord x ⊓ y ∈ᴮ x ⊓ w ∈ᴮ y ⊓ z ∈ᴮ w

    have hOrd : ctx ≤ Ord x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hyx : ctx ≤ y ∈ᴮ x := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hwy : ctx ≤ w ∈ᴮ y := inf_le_left.trans inf_le_right
    have hzw : ctx ≤ z ∈ᴮ w := inf_le_right

    have hy_sub_x : ctx ≤ y ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd.trans inf_le_right) hyx

    have hwx : ctx ≤ w ∈ᴮ x :=
      mem_of_mem_subset hy_sub_x hwy

    have hw_sub_x : ctx ≤ w ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd.trans inf_le_right) hwx

    have hzx : ctx ≤ z ∈ᴮ x :=
      mem_of_mem_subset hw_sub_x hzw

    have h_tri : ctx ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
      have hewo : ctx ≤ epsilon_well_orders x := hOrd.trans inf_le_left
      have h_step1 : ctx ≤ z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y) :=
        le_trans (le_inf (hewo.trans (epsilon_dichotomy x y z)) hyx) bv_imp_elim
      exact le_trans (le_inf h_step1 hzx) bv_imp_elim

    calc ctx
        ≤ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y) ⊓ ctx := le_inf h_tri le_rfl
      _ ≤ z ∈ᴮ y := by
          apply bv_or_elim_left
          ·
            apply bv_or_elim_left
            ·

              apply le_trans _ bot_le

              have h_yw : (y =ᴮ z) ⊓ ctx ≤ y ∈ᴮ w :=
                bv_rw' (H := inf_le_left) (ϕ := fun v => v ∈ᴮ w) (h_congr := B_ext_mem_left)
                  (H_new := le_trans inf_le_right hzw)
              exact bot_of_mem_mem' y w h_yw (inf_le_right.trans hwy)
            ·

              apply le_trans _ bot_le

              have hwmem_iSup : (y ∈ᴮ z) ⊓ ctx ≤ ⨆ i : y.type, y.bval i ⊓ w =ᴮ y.func i := by
                calc (y ∈ᴮ z) ⊓ ctx ≤ w ∈ᴮ y := inf_le_right.trans hwy
                  _ = ⨆ i : y.type, y.bval i ⊓ w =ᴮ y.func i := mem_unfold
              calc (y ∈ᴮ z) ⊓ ctx
                  ≤ (⨆ i : y.type, y.bval i ⊓ w =ᴮ y.func i) ⊓ ((y ∈ᴮ z) ⊓ ctx) :=
                    le_inf hwmem_iSup le_rfl
                _ ≤ ⨆ i, (y.bval i ⊓ w =ᴮ y.func i) ⊓ ((y ∈ᴮ z) ⊓ ctx) :=
                    (iSup_inf_eq _ _).le
                _ ≤ ⊥ := by
                    apply iSup_le; intro i_w
                    set ctx2 := (y.bval i_w ⊓ w =ᴮ y.func i_w) ⊓ ((y ∈ᴮ z) ⊓ ctx)
                    have hw_eq : ctx2 ≤ w =ᴮ y.func i_w := inf_le_left.trans inf_le_right
                    have h_hyz : ctx2 ≤ y ∈ᴮ z := inf_le_right.trans inf_le_left

                    have hyf_x : ctx2 ≤ y.func i_w ∈ᴮ x :=
                      bv_rw' (H := bv_symm hw_eq) (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
                        (H_new := le_trans inf_le_right (inf_le_right.trans hwx))

                    have h_ihiw : ctx2 ≤ is_transitive (y.func i_w) :=
                      le_trans (le_inf (le_trans inf_le_right (inf_le_right.trans hOrd)) hyf_x) (IH i_w x)

                    have h_z_in_yfi : ctx2 ≤ z ∈ᴮ y.func i_w :=
                      bv_rw' (H := bv_symm hw_eq) (ϕ := fun v => z ∈ᴮ v) (h_congr := B_ext_mem_right)
                        (H_new := le_trans inf_le_right (inf_le_right.trans hzw))
                    have h_ztrans : ctx2 ≤ z ⊆ᴮ y.func i_w :=
                      subset_of_mem_transitive h_ihiw h_z_in_yfi

                    have h_y_yfi : ctx2 ≤ y ∈ᴮ y.func i_w :=
                      mem_of_mem_subset h_ztrans h_hyz
                    have h_yw : ctx2 ≤ y ∈ᴮ w :=
                      bv_rw' (H := hw_eq) (ϕ := fun v => y ∈ᴮ v) (h_congr := B_ext_mem_right)
                        (H_new := h_y_yfi)

                    exact bot_of_mem_mem' y w h_yw (le_trans inf_le_right (inf_le_right.trans hwy))
          ·
            exact inf_le_left

lemma is_ewo_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ epsilon_well_orders y := by

  apply le_inf
  ·
    apply le_iInf; intro w; rw [← deduction]
    apply le_iInf; intro z; rw [← deduction]

    set ctx := Ord x ⊓ y ∈ᴮ x ⊓ w ∈ᴮ y ⊓ z ∈ᴮ y
    have hOrd : ctx ≤ Ord x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hyx : ctx ≤ y ∈ᴮ x := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hwy : ctx ≤ w ∈ᴮ y := inf_le_left.trans inf_le_right
    have hzy : ctx ≤ z ∈ᴮ y := inf_le_right

    have hy_sub_x : ctx ≤ y ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd.trans inf_le_right) hyx

    have hwx : ctx ≤ w ∈ᴮ x := mem_of_mem_subset hy_sub_x hwy
    have hzx : ctx ≤ z ∈ᴮ x := mem_of_mem_subset hy_sub_x hzy

    have hewo : ctx ≤ epsilon_well_orders x := hOrd.trans inf_le_left
    have htri : ctx ≤ epsilon_trichotomy x := hewo.trans inf_le_left
    have h_step0 : ctx ≤ ⨅ z', z' ∈ᴮ x ⟹ (w =ᴮ z' ⊔ w ∈ᴮ z' ⊔ z' ∈ᴮ w) :=
      le_trans (le_inf (htri.trans (iInf_le _ w)) hwx) bv_imp_elim
    exact le_trans (le_inf (h_step0.trans (iInf_le _ z)) hzx) bv_imp_elim
  ·

    apply le_iInf; intro u
    rw [← deduction, ← deduction]

    set ctx2 := Ord x ⊓ y ∈ᴮ x ⊓ u ⊆ᴮ y ⊓ (u =ᴮ ∅)ᶜ
    have hOrd2 : ctx2 ≤ Ord x := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hyx2 : ctx2 ≤ y ∈ᴮ x := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have huby : ctx2 ≤ u ⊆ᴮ y := inf_le_left.trans inf_le_right
    have hne : ctx2 ≤ (u =ᴮ ∅)ᶜ := inf_le_right

    have hy_sub_x2 : ctx2 ≤ y ⊆ᴮ x :=
      subset_of_mem_transitive (hOrd2.trans inf_le_right) hyx2

    have hubx : ctx2 ≤ u ⊆ᴮ x := subset_trans' huby hy_sub_x2

    have hewo2 : ctx2 ≤ epsilon_well_orders x := hOrd2.trans inf_le_left
    have hwf2 : ctx2 ≤ epsilon_well_founded x := hewo2.trans inf_le_right
    have hwf3 : ctx2 ≤ u ⊆ᴮ x ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ v, v ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ v)ᶜ)) :=
      hwf2.trans (iInf_le _ u)
    have hwf4 : ctx2 ≤ (u =ᴮ ∅)ᶜ ⟹ ⨆ v, v ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ v)ᶜ) :=
      le_trans (le_inf hwf3 hubx) bv_imp_elim
    exact le_trans (le_inf hwf4 hne) bv_imp_elim

theorem Ord_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) :
    Γ ≤ Ord x :=
  le_inf
    (le_trans (le_inf H_Ord H_mem) (is_ewo_of_mem_Ord x y))
    (le_trans (le_inf H_Ord H_mem) (is_transitive_of_mem_Ord x y))

lemma check_is_transitive {x : PSet} (H : PSet.is_transitive x) {Γ : 𝔹} :
    Γ ≤ is_transitive (check x : bSet 𝔹) := by

  apply le_iInf; intro y; rw [← deduction]

  have h_ymem : Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ≤
      ⨆ i : x.Type, y =ᴮ check (x.Func i) := by
    calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)
        ≤ y ∈ᴮ (check x : bSet 𝔹) := inf_le_right
      _ = y ∈ᴮ bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by rw [check_unfold]
      _ = ⨆ i : x.Type, ⊤ ⊓ y =ᴮ check (x.Func i) := mem_unfold
      _ = ⨆ i : x.Type, y =ᴮ check (x.Func i) := by simp only [top_inf_eq]

  calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)
      ≤ (⨆ i : x.Type, y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)) :=
        le_inf h_ymem le_rfl
    _ ≤ ⨆ i : x.Type, (y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)) :=
        (iSup_inf_eq _ _).le
    _ ≤ y ⊆ᴮ (check x : bSet 𝔹) := by
        apply iSup_le; intro i

        apply bv_rw' (H := inf_le_left) (ϕ := fun z => z ⊆ᴮ check x)
          (h_congr := B_ext_subset_left)

        exact check_subset (H (x.Func i) (PSet.func_mem x i))

lemma check_ewo_left {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ (⨅ y, y ∈ᴮ (check x : bSet 𝔹) ⟹
      (⨅ z, z ∈ᴮ (check x : bSet 𝔹) ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) := by
  apply le_iInf; intro y; rw [← deduction]
  apply le_iInf; intro z; rw [← deduction]

  have hy : Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹) ≤
      ⨆ i : x.Type, y =ᴮ check (x.Func i) :=
    calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
        ≤ y ∈ᴮ (check x : bSet 𝔹) := inf_le_left.trans inf_le_right
      _ = y ∈ᴮ bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by rw [check_unfold]
      _ = ⨆ i : x.Type, ⊤ ⊓ y =ᴮ check (x.Func i) := mem_unfold
      _ = ⨆ i : x.Type, y =ᴮ check (x.Func i) := by simp only [top_inf_eq]
  have hz : Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹) ≤
      ⨆ j : x.Type, z =ᴮ check (x.Func j) :=
    calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
        ≤ z ∈ᴮ (check x : bSet 𝔹) := inf_le_right
      _ = z ∈ᴮ bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by rw [check_unfold]
      _ = ⨆ j : x.Type, ⊤ ⊓ z =ᴮ check (x.Func j) := mem_unfold
      _ = ⨆ j : x.Type, z =ᴮ check (x.Func j) := by simp only [top_inf_eq]

  calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
      ≤ (⨆ i, y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)) :=
        le_inf hy le_rfl
    _ ≤ ⨆ i, (y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)) :=
        (iSup_inf_eq _ _).le
    _ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
        apply iSup_le; intro i

        calc (y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹))
            ≤ (⨆ j, z =ᴮ check (x.Func j)) ⊓
                ((y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹))) :=
              le_inf (inf_le_right.trans hz) le_rfl
          _ ≤ ⨆ j, (z =ᴮ check (x.Func j)) ⊓
                ((y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹))) :=
              (iSup_inf_eq _ _).le
          _ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
              apply iSup_le; intro j

              have h_tri := H.1 (x.Func i) (PSet.func_mem x i) (x.Func j) (PSet.func_mem x j)
              set ctx3 := Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
              have hy_eq : (z =ᴮ check (x.Func j)) ⊓ ((y =ᴮ check (x.Func i)) ⊓ ctx3) ≤
                  y =ᴮ check (x.Func i) := inf_le_right.trans inf_le_left
              have hz_eq : (z =ᴮ check (x.Func j)) ⊓ ((y =ᴮ check (x.Func i)) ⊓ ctx3) ≤
                  z =ᴮ check (x.Func j) := inf_le_left
              set ctx2 := (z =ᴮ check (x.Func j)) ⊓ ((y =ᴮ check (x.Func i)) ⊓ ctx3)
              rcases h_tri with h_eq | h_mem_ij | h_mem_ji
              ·

                have h_yz := bv_trans hy_eq (bv_trans (le_top.trans (check_bv_eq h_eq)) (bv_symm hz_eq))
                exact h_yz.trans (le_sup_left.trans le_sup_left)
              ·

                have h_cm : ctx2 ≤ check (x.Func i) ∈ᴮ check (x.Func j) :=
                  le_top.trans (check_mem h_mem_ij)

                have h_ymemz := mem_congr (bv_symm hy_eq) (bv_symm hz_eq) h_cm
                exact h_ymemz.trans (le_sup_right.trans le_sup_left)
              ·

                have h_cm : ctx2 ≤ check (x.Func j) ∈ᴮ check (x.Func i) :=
                  le_top.trans (check_mem h_mem_ji)

                exact (mem_congr (bv_symm hz_eq) (bv_symm hy_eq) h_cm).trans le_sup_right

lemma check_ewo_right {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ (⨅ u, u ⊆ᴮ (check x : bSet 𝔹) ⟹
      ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ))) := by
  apply le_iInf; intro u
  rw [← deduction, ← deduction]
  exact bSet_axiom_of_regularity u inf_le_right

lemma check_ewo {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ epsilon_well_orders (check x : bSet 𝔹) :=
  le_inf (check_ewo_left H) (check_ewo_right H)

@[simp] lemma check_Ord {x : PSet} (H : PSet.Ord x) {Γ : 𝔹} :
    Γ ≤ Ord (check x : bSet 𝔹) :=
  le_inf (check_ewo H.left) (check_is_transitive H.right)

@[simp] lemma Ord_card_ex (κ : Cardinal) {Γ : 𝔹} :
    Γ ≤ Ord (check (PSet.card_ex κ) : bSet 𝔹) := by
  apply check_Ord; simp [PSet.card_ex]

def closed_under_successor (Γ : 𝔹) (x : bSet 𝔹) := Γ ≤ ⨅ y, y ∈ᴮ x ⟹ succ y ∈ᴮ x

def omega_spec (ω : bSet 𝔹) : Prop :=
  (∀ {Γ : 𝔹}, Γ ≤ not_empty ω ∧ closed_under_successor Γ ω) ∧
  ∀ (x : bSet 𝔹) {Γ : 𝔹} (H₁ : Γ ≤ ∅ ∈ᴮ x) (H₂ : closed_under_successor Γ x), Γ ≤ ω ⊆ᴮ x

lemma omega_closed_under_succ {Γ : 𝔹} : closed_under_successor Γ (bSet.omega) := by
  unfold closed_under_successor

  apply le_iInf; intro y; rw [← deduction]

  have h_ymem : Γ ⊓ y ∈ᴮ (bSet.omega : bSet 𝔹) ≤
      ⨆ k : ULift ℕ, y =ᴮ bSet.of_nat k.down := by
    apply inf_le_right.trans

    rw [mem_unfold]

    apply iSup_le; intro k; apply le_iSup_of_le k
    simp only [omega_func, check_bval_top, top_inf_eq, le_refl]

  calc Γ ⊓ y ∈ᴮ (bSet.omega : bSet 𝔹)
      ≤ (⨆ k : ULift ℕ, y =ᴮ bSet.of_nat k.down) ⊓ (Γ ⊓ y ∈ᴮ (bSet.omega : bSet 𝔹)) :=
        le_inf h_ymem le_rfl
    _ ≤ ⨆ k : ULift ℕ, (y =ᴮ bSet.of_nat k.down) ⊓ (Γ ⊓ y ∈ᴮ (bSet.omega : bSet 𝔹)) :=
        (iSup_inf_eq _ _).le
    _ ≤ succ y ∈ᴮ (bSet.omega : bSet 𝔹) := by
        apply iSup_le; intro k

        have h_yk : (y =ᴮ bSet.of_nat k.down) ⊓ (Γ ⊓ y ∈ᴮ (bSet.omega : bSet 𝔹)) ≤
            y =ᴮ bSet.of_nat k.down := inf_le_left

        have h_succ_eq : succ (bSet.of_nat k.down : bSet 𝔹) = bSet.of_nat (k.down + 1) :=
          (@check_succ_eq_succ_check k.down 𝔹 _).symm

        have h_mem : (y =ᴮ bSet.of_nat k.down) ⊓ (Γ ⊓ y ∈ᴮ (bSet.omega : bSet 𝔹)) ≤
            bSet.of_nat (k.down + 1) ∈ᴮ (bSet.omega : bSet 𝔹) :=
          le_top.trans of_nat_mem_omega

        rw [← h_succ_eq] at h_mem

        apply bv_rw' (H := h_yk) (ϕ := fun z => succ z ∈ᴮ (bSet.omega : bSet 𝔹))
        ·
          exact B_ext_term (ϕ := fun v => v ∈ᴮ (bSet.omega : bSet 𝔹)) (t := succ)
            B_ext_mem_left B_congr_succ
        · exact h_mem

lemma omega_nonempty {Γ : 𝔹} : Γ ≤ not_empty bSet.omega := by
  unfold not_empty
  rw [nonempty_iff_exists_mem]
  exact le_iSup_of_le (of_nat 0) of_nat_mem_omega

lemma omega_is_omega : omega_spec (bSet.omega : bSet 𝔹) := by
  constructor
  · intro Γ; exact ⟨omega_nonempty, omega_closed_under_succ⟩
  · intro x Γ H₁ H₂

    rw [subset_unfold]
    apply le_iInf; intro k

    simp only [omega_func, check_bval_top, top_imp]

    suffices h : ∀ n : ℕ, Γ ≤ of_nat n ∈ᴮ x from h k.down
    intro n
    induction n with
    | zero =>

        exact bv_rw' (H := @zero_eq_empty 𝔹 _ Γ) (H_new := H₁) (h_congr := B_ext_mem_left)
    | succ n ih =>

        rw [@check_succ_eq_succ_check n 𝔹 _]

        exact le_trans (le_inf (le_trans H₂ (iInf_le _ (of_nat n))) ih) bv_imp_elim

lemma Ord_omega {Γ : 𝔹} : Γ ≤ Ord (omega : bSet 𝔹) :=
  le_inf (check_ewo PSet.is_ewo_omega) (check_is_transitive PSet.is_transitive_omega)

lemma Ord_of_nat {Γ : 𝔹} {n : ℕ} : Γ ≤ Ord (of_nat n) :=
  Ord_of_mem_Ord of_nat_mem_omega Ord_omega

lemma Ord_one {Γ : 𝔹} : Γ ≤ Ord (1 : bSet 𝔹) := Ord_of_nat

lemma Ord_zero {Γ : 𝔹} : Γ ≤ Ord (0 : bSet 𝔹) := Ord_of_nat

lemma of_nat_subset_omega {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ⊆ᴮ omega :=
  subset_of_mem_transitive (le_trans Ord_omega inf_le_right) of_nat_mem_omega

@[reducible] def aleph_one_Ord_spec (x : bSet 𝔹) : 𝔹 :=
  (injects_into x omega)ᶜ ⊓
    (Ord x ⊓ (⨅ y, Ord y ⟹ ((injects_into y bSet.omega)ᶜ ⟹ x ⊆ᴮ y)))

@[simp] lemma aleph_one_check_exists_mem {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {Γ : 𝔹} : Γ ≤ exists_mem (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) := by
  apply check_exists_mem
  have : ∃ z, z ∈ PSet.card_ex (Cardinal.aleph (1 : ℕ)) :=
    @PSet.card_ex_aleph_exists_mem 1
  convert this using 2
  norm_cast

@[simp] lemma B_ext_Ord : B_ext (Ord : bSet 𝔹 → 𝔹) :=
  B_ext_inf B_ext_ewo B_ext_is_transitive

@[reducible] def le_of_omega_lt (x : bSet 𝔹) : 𝔹 :=
  ⨅ z, Ord z ⟹ ((larger_than bSet.omega z)ᶜ ⟹ injects_into x z)

@[simp] lemma B_ext_le_of_omega_lt : B_ext (le_of_omega_lt : bSet 𝔹 → 𝔹) := by
  unfold le_of_omega_lt
  exact B_ext_iInf (h := fun z => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_injects_into_left)))

end ordinals

section zorns_lemma
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem bSet_zorns_lemma' {Γ : 𝔹} :
    Γ ≤ ⨅ (X : bSet 𝔹), (X =ᴮ ∅)ᶜ ⟹
      ((⨅ y, (y ⊆ᴮ X ⊓ (⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
          w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ bv_union y ∈ᴮ X) ⟹
        (⨆ c, c ∈ᴮ X ⊓ (⨅ z, z ∈ᴮ X ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z)))) := by
  apply le_iInf; intro X
  rw [← curry_uncurry]
  suffices h : (⨅ (Y : bSet 𝔹), ((Y =ᴮ ∅)ᶜ ⊓ ⨅ y, (y ⊆ᴮ Y ⊓
      (⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
        w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ bv_union y ∈ᴮ Y) ⟹
    (⨆ c, c ∈ᴮ Y ⊓ (⨅ z, z ∈ᴮ Y ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z)))) = ⊤ by
    exact le_top.trans (h ▸ iInf_le _ X)
  apply core_aux_lemma2
  · exact B_ext_inf (h₁ := B_ext_neg (h := B_ext_bv_eq_left))
      (h₂ := B_ext_iInf (h := fun y => B_ext_imp
        (h₁ := B_ext_inf B_ext_subset_right B_ext_const)
        (h₂ := B_ext_mem_right)))
  · exact B_ext_iSup (h := fun c => B_ext_inf (h₁ := B_ext_mem_right)
      (h₂ := B_ext_iInf (h := fun z => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
  · intro u hu
    have h_nonempty : (u =ᴮ ∅)ᶜ = ⊤ := top_unique (hu ▸ inf_le_left)
    have h_chain : (⊤ : 𝔹) ≤ ⨅ y, (y ⊆ᴮ u ⊓
        (⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
          w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ bv_union y ∈ᴮ u :=
      hu ▸ inf_le_right
    exact top_unique (bSet_zorns_lemma u h_nonempty h_chain)
  · apply top_unique; apply le_iSup_of_le ({∅} : bSet 𝔹)
    apply le_inf
    · apply nonempty_of_exists_mem; apply le_iSup_of_le (∅ : bSet 𝔹)
      have hmem : (∅ : bSet 𝔹) ∈ᴮ ({∅} : bSet 𝔹) = ⊤ := by
        simp [mem_singleton_bSet, bv_eq_refl]
      exact le_of_eq hmem.symm
    · apply le_iInf; intro y; apply bv_imp_intro_lemma; rw [top_inf_eq]
      simp only [mem_singleton_bSet]
      apply le_sup_of_le_left
      rw [eq_iff_subset_subset]
      apply le_inf
      ·

        rw [show bv_union y ⊆ᴮ (∅ : bSet 𝔹) = ⨅ w : bSet 𝔹, w ∈ᴮ bv_union y ⟹ w ∈ᴮ ∅
              from subset_unfold']
        apply le_iInf; intro w; apply bv_imp_intro_lemma

        apply le_trans (b := y ⊆ᴮ ({∅} : bSet 𝔹) ⊓ ⨆ z, z ∈ᴮ y ⊓ w ∈ᴮ z)
        · exact le_inf (inf_le_left.trans inf_le_left) ((bv_union_spec_split y w).mp inf_le_right)
        · rw [inf_iSup_eq']; apply iSup_le; intro z

          have hz_sing : y ⊆ᴮ ({∅} : bSet 𝔹) ⊓ (z ∈ᴮ y ⊓ w ∈ᴮ z) ≤ z ∈ᴮ ({∅} : bSet 𝔹) :=
            mem_of_mem_subset inf_le_left (inf_le_right.trans inf_le_left)

          have hz_eq : y ⊆ᴮ ({∅} : bSet 𝔹) ⊓ (z ∈ᴮ y ⊓ w ∈ᴮ z) ≤ z =ᴮ (∅ : bSet 𝔹) := by
            have hh := hz_sing; simp only [mem_singleton_bSet] at hh
            have hbot_z : z ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by
              rw [mem_unfold]; exact exists_over_empty _
            simpa only [hbot_z, sup_bot_eq] using hh

          exact bv_rw' (H := bv_symm hz_eq)
            (h_congr := B_ext_mem_right) (H_new := inf_le_right.trans inf_le_right)
      · exact le_trans le_top empty_subset

end zorns_lemma

section CH
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def CH : 𝔹 :=
  (⨆ (x : bSet 𝔹), Ord x ⊓ ⨆ (y : bSet 𝔹),
    (larger_than omega x)ᶜ ⊓ (larger_than x y)ᶜ ⊓
    injects_into y (bv_powerset omega))ᶜ

def CH₂ : 𝔹 :=
  (⨆ (x : bSet 𝔹), Ord x ⊓ (larger_than omega x)ᶜ ⊓ (larger_than x (bv_powerset omega))ᶜ)ᶜ

lemma CH_iff_CH₂ : ∀ {Γ : 𝔹}, Γ ≤ CH ↔ Γ ≤ CH₂ := by
  intro Γ
  constructor
  · intro H

    apply H.trans
    apply compl_le_compl

    apply iSup_le; intro x
    apply le_iSup_of_le x
    refine le_inf (inf_le_left.trans inf_le_left) ?_

    apply le_iSup_of_le (bv_powerset omega)

    refine le_inf (le_inf ?_ ?_) injects_into_refl
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  · intro H

    apply H.trans
    apply compl_le_compl

    apply iSup_le; intro x
    apply le_iSup_of_le x

    refine le_inf (le_inf inf_le_left ?_) ?_
    ·

      rw [inf_iSup_eq']; apply iSup_le; intro y

      exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    ·
      rw [inf_iSup_eq']; apply iSup_le; intro y

      exact bSet_lt_of_lt_of_le (inf_le_right.trans (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)

end CH

end bSet
