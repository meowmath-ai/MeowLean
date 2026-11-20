/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Modified for Lean and Mathlib 4.36.0.

import Flypitch4.PSetOrdinal
import Flypitch4.BvTauto
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Zorn

open scoped Flypitch

namespace Lattice

section natded
variable {𝔹 : Type*} [CompleteBooleanAlgebra 𝔹]

lemma supr_imp_eq {ι : Type*} {s : ι → 𝔹} {b : 𝔹} :
    (⨆ (i : ι), s i) ⟹ b = ⨅ (i : ι), s i ⟹ b := by
  unfold imp; rw [compl_iSup, iInf_sup_eq']

lemma imp_infi_eq {ι : Type*} {s : ι → 𝔹} {b : 𝔹} :
    (b ⟹ (⨅ i, s i)) = ⨅ i, b ⟹ s i := by
  unfold imp; rw [sup_iInf_eq']

lemma bv_Or_elim {ι : Type*} {s : ι → 𝔹} {c : 𝔹}
    (H : ∀ i : ι, s i ≤ c) : (⨆ (i : ι), s i) ≤ c :=
  iSup_le H

lemma bv_And_intro {ι : Type*} {s : ι → 𝔹} {c : 𝔹}
    (H : ∀ i : ι, c ≤ s i) : c ≤ ⨅ (i : ι), s i :=
  le_iInf H

lemma bv_or_elim {b₁ b₂ c : 𝔹} (h : b₁ ≤ c) (h' : b₂ ≤ c) : b₁ ⊔ b₂ ≤ c :=
  sup_le h h'

lemma bv_or_elim_left {b₁ b₂ c d : 𝔹} (h₁ : b₁ ⊓ d ≤ c) (h₂ : b₂ ⊓ d ≤ c) :
    (b₁ ⊔ b₂) ⊓ d ≤ c := by
  rw [deduction]; apply sup_le <;> rw [← deduction] <;> assumption

lemma bv_or_elim_right {b₁ b₂ c d : 𝔹} (h₁ : d ⊓ b₁ ≤ c) (h₂ : d ⊓ b₂ ≤ c) :
    d ⊓ (b₁ ⊔ b₂) ≤ c := by
  rw [inf_comm]; rw [inf_comm] at h₁ h₂; exact bv_or_elim_left h₁ h₂

lemma bv_exfalso {a b : 𝔹} (h : a ≤ ⊥) : a ≤ b :=
  le_trans h bot_le

lemma bv_cases_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, s i ⊓ c ≤ b) :
    ((⨆ (i : ι), s i) ⊓ c) ≤ b := by
  rw [deduction]; apply iSup_le; intro i; rw [← deduction]; exact h i

lemma bv_cases_right {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, c ⊓ s i ≤ b) :
    (c ⊓ (⨆ (i : ι), s i)) ≤ b := by
  rw [inf_comm]; exact bv_cases_left (fun i => by rw [inf_comm]; exact h i)

lemma bv_specialize {ι : Type*} {s : ι → 𝔹} (i : ι) {b : 𝔹} (h : s i ≤ b) :
    (⨅ (i : ι), s i) ≤ b :=
  iInf_le_of_le i h

lemma bv_specialize_twice {ι : Type*} {s : ι → 𝔹} (i j : ι) {b : 𝔹}
    (h : s i ⊓ s j ≤ b) : (⨅ (i : ι), s i) ≤ b :=
  calc (⨅ k, s k) ≤ s i ⊓ s j := le_inf (iInf_le _ i) (iInf_le _ j)
    _ ≤ b := h

lemma bv_specialize_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i : ι)
    (h : s i ⊓ c ≤ b) : (⨅ (i : ι), s i) ⊓ c ≤ b := by
  rw [deduction]; exact bv_specialize i (by rwa [← deduction])

lemma bv_specialize_left_twice {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i j : ι)
    (h : s i ⊓ s j ⊓ c ≤ b) : (⨅ (i : ι), s i) ⊓ c ≤ b := by
  rw [deduction]; exact bv_specialize_twice i j (by rwa [← deduction])

lemma bv_specialize_right {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i : ι)
    (h : c ⊓ s i ≤ b) : c ⊓ (⨅ (i : ι), s i) ≤ b := by
  rw [inf_comm]; exact bv_specialize_left i (by rwa [inf_comm])

lemma bv_specialize_right_twice {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i j : ι)
    (h : c ⊓ (s i ⊓ s j) ≤ b) : c ⊓ (⨅ (i : ι), s i) ≤ b := by
  rw [inf_comm]; exact bv_specialize_left_twice i j (by rwa [← inf_comm])

lemma bv_imp_elim {a b : 𝔹} : (a ⟹ b) ⊓ a ≤ b := imp_inf_le a b

lemma bv_imp_elim' {a b : 𝔹} : (a ⟹ b) ⊓ a ≤ a ⊓ b :=
  le_inf inf_le_right bv_imp_elim

lemma bv_cancel_antecedent {a b c : 𝔹} (h : b ≤ c) : a ⟹ b ≤ a ⟹ c := by
  rw [← deduction]; exact le_trans bv_imp_elim h

lemma bv_imp_iff {Γ b₁ b₂ : 𝔹} :
    Γ ≤ b₁ ⟹ b₂ ↔ (∀ {Γ' : 𝔹}, Γ' ≤ Γ → Γ' ≤ b₁ → Γ' ≤ b₂) := by
  constructor
  · intro H Γ' H_le H'
    rw [← deduction] at H
    exact le_trans (le_inf H_le H') H
  · intro H
    rw [← deduction]; exact H inf_le_left inf_le_right

lemma bv_biimp_iff {b₁ b₂ : 𝔹} {Γ : 𝔹} :
    (Γ ≤ (b₁ ⇔ b₂)) ↔ (∀ {Γ' : 𝔹}, Γ' ≤ Γ → (Γ' ≤ b₁ ↔ Γ' ≤ b₂)) := by
  constructor
  · intro H
    have Hmp : Γ ≤ b₁ ⟹ b₂ := le_trans H inf_le_left
    have Hmpr : Γ ≤ b₂ ⟹ b₁ := le_trans H inf_le_right
    intro Γ' H_le
    exact ⟨bv_imp_iff.mp Hmp H_le, bv_imp_iff.mp Hmpr H_le⟩
  · intro H
    apply le_inf
    · rw [bv_imp_iff]; exact fun H_le H' => (H H_le).mp H'
    · rw [bv_imp_iff]; exact fun H_le H' => (H H_le).mpr H'

lemma bv_and_intro {a b₁ b₂ : 𝔹} (h₁ : a ≤ b₁) (h₂ : a ≤ b₂) : a ≤ b₁ ⊓ b₂ :=
  le_inf h₁ h₂

lemma bv_or_left {a b₁ b₂ : 𝔹} (h₁ : a ≤ b₁) : a ≤ b₁ ⊔ b₂ :=
  le_trans h₁ le_sup_left

lemma bv_or_right {a b₁ b₂ : 𝔹} (h₂ : a ≤ b₂) : a ≤ b₁ ⊔ b₂ :=
  le_trans h₂ le_sup_right

lemma bv_and_left {a b : 𝔹} {Γ : 𝔹} (H : Γ ≤ a ⊓ b) : Γ ≤ a :=
  le_trans H inf_le_left

lemma bv_and_right {a b : 𝔹} {Γ : 𝔹} (H : Γ ≤ a ⊓ b) : Γ ≤ b :=
  le_trans H inf_le_right

lemma from_empty_context {a b : 𝔹} (h : ⊤ ≤ b) : a ≤ b :=
  le_trans le_top h

lemma bv_imp_intro_lemma {a b c : 𝔹} (h : a ⊓ b ≤ c) : a ≤ b ⟹ c := by
  rwa [deduction] at h

lemma bv_have {a b c : 𝔹} (h : a ≤ b) (h' : a ⊓ b ≤ c) : a ≤ c :=
  le_trans (le_inf le_rfl h) h'

lemma bv_have_true {a b c : 𝔹} (h₁ : ⊤ ≤ b) (h₂ : a ⊓ b ≤ c) : a ≤ c := by
  have hb : b = ⊤ := le_antisymm le_top h₁
  rw [hb, inf_top_eq] at h₂; exact h₂

lemma bv_use {ι} (i : ι) {s : ι → 𝔹} {b : 𝔹} (h : b ≤ s i) : b ≤ ⨆ (j : ι), s j :=
  le_trans h (le_iSup _ i)

lemma bv_context_apply {β : Type*} [CompleteBooleanAlgebra β] {Γ a₁ a₂ : β}
    (h₁ : Γ ≤ a₁ ⟹ a₂) (h₂ : Γ ≤ a₁) : Γ ≤ a₂ :=
  context_imp_elim h₁ h₂

lemma bv_Or_imp {Γ : 𝔹} {ι} {ϕ₁ ϕ₂ : ι → 𝔹} (H_sub : Γ ≤ ⨅ x, ϕ₁ x ⟹ ϕ₂ x)
    (H : Γ ≤ ⨆ x, ϕ₁ x) : Γ ≤ ⨆ x, ϕ₂ x := by

  calc Γ ≤ (⨅ x, ϕ₁ x ⟹ ϕ₂ x) ⊓ ⨆ x, ϕ₁ x := le_inf H_sub H
    _ ≤ ⨆ x, ϕ₂ x := by
        rw [inf_iSup_eq]
        apply iSup_le; intro x
        exact le_trans (le_inf (inf_le_left.trans (iInf_le _ x)) inf_le_right)
          (le_trans bv_imp_elim (le_iSup _ x))

lemma bv_iff_neg {b₁ b₂ : 𝔹} (H : ∀ {Γ : 𝔹}, Γ ≤ b₁ ↔ Γ ≤ b₂) :
    ∀ {Γ : 𝔹}, Γ ≤ b₁ᶜ ↔ Γ ≤ b₂ᶜ := by
  intro Γ
  simp only [← imp_bot]
  have h12 : b₁ ≤ b₂ := (H (Γ := b₁)).mp le_rfl
  have h21 : b₂ ≤ b₁ := (H (Γ := b₂)).mpr le_rfl
  exact ⟨fun h => le_trans h (imp_le_of_left_le (h := h21)),
         fun h => le_trans h (imp_le_of_left_le (h := h12))⟩

end natded
end Lattice

open Lattice

universe u

namespace PSet

lemma not_equiv {x y : PSet} (h_neq : ¬ PSet.Equiv x y) :
    (∃ a : x.Type, ∀ a' : y.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) ∨
    (∃ a' : y.Type, ∀ a : x.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) := by
  rw [PSet.equiv_iff] at h_neq
  by_cases hleft : ∀ i : x.Type, ∃ j : y.Type, PSet.Equiv (x.Func i) (y.Func j)
  · right
    have hright : ¬ ∀ j : y.Type, ∃ i : x.Type, PSet.Equiv (x.Func i) (y.Func j) := by
      intro hright; exact h_neq ⟨hleft, hright⟩
    simp only [not_forall, not_exists] at hright
    obtain ⟨a', ha'⟩ := hright
    exact ⟨a', ha'⟩
  · left
    simp only [not_forall, not_exists] at hleft
    obtain ⟨a, ha⟩ := hleft
    exact ⟨a, ha⟩

end PSet

inductive bSet (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] : Type (u + 1)
  | mk (α : Type u) (A : α → bSet 𝔹) (B : α → 𝔹) : bSet 𝔹

namespace bSet

open scoped Flypitch

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

noncomputable instance decidable_eq_𝔹 : DecidableEq 𝔹 :=
  fun _ _ => Classical.propDecidable _

@[simp] def type : bSet 𝔹 → Type u
  | ⟨α, _, _⟩ => α

@[simp] lemma type_iInf {α : Type u} {A : α → bSet 𝔹} {B : α → 𝔹} {C : α → 𝔹} :
    (⨅ (a : (mk α A B).type), C a) = ⨅ (a : α), C a := rfl

@[simp] lemma type_iSup {α : Type u} {A : α → bSet 𝔹} {B : α → 𝔹} {C : α → 𝔹} :
    (⨆ (a : (mk α A B).type), C a) = ⨆ (a : α), C a := rfl

@[simp] def func : ∀ x : bSet 𝔹, x.type → bSet 𝔹
  | ⟨_, A, _⟩ => A

@[simp] def bval : ∀ x : bSet 𝔹, x.type → 𝔹
  | ⟨_, _, B⟩ => B

@[simp] def mk_type_func_bval : ∀ x : bSet 𝔹, mk x.type x.func x.bval = x :=
  fun x => by cases x; rfl

def empty : bSet 𝔹 :=
  ⟨PEmpty, PEmpty.elim, PEmpty.elim⟩

instance nonempty_bSet : Nonempty (@bSet 𝔹 _) := ⟨empty⟩

instance has_empty_bSet : EmptyCollection (bSet 𝔹) := ⟨empty⟩

@[simp] lemma forall_over_empty (ϕ : (empty : bSet 𝔹).type → 𝔹) : (⨅ a, ϕ a) = ⊤ := by
  apply top_unique; apply le_iInf; intro a; exact a.elim

@[simp] lemma exists_over_empty (ϕ : (empty : bSet 𝔹).type → 𝔹) : (⨆ a, ϕ a) = ⊥ := by
  apply bot_unique; apply iSup_le; intro i; exact i.elim

def bv_eq : ∀ (x y : bSet 𝔹), 𝔹
  | ⟨α, A, B⟩, ⟨α', A', B'⟩ =>
    (⨅ a : α, B a ⟹ ⨆ a', B' a' ⊓ bv_eq (A a) (A' a')) ⊓
    (⨅ a' : α', B' a' ⟹ ⨆ a, B a ⊓ bv_eq (A a) (A' a'))

scoped infixl:79 " =ᴮ " => bv_eq

def bv_eq' (Γ : 𝔹) : bSet 𝔹 → bSet 𝔹 → Prop := fun x y => Γ ≤ x =ᴮ y

@[simp] theorem bv_eq_refl : ∀ x : bSet 𝔹, x =ᴮ x = ⊤ := by
  intro x
  induction x with
  | mk α A B ih =>
    simp only [bv_eq, inf_eq_top_iff, iInf_eq_top]
    constructor
    all_goals intro i
    all_goals rw [imp_top_iff_le]
    all_goals exact le_iSup_of_le i (le_inf le_rfl (ih i ▸ le_top))

@[simp] lemma bv_refl {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ x =ᴮ x :=
  le_trans le_top (by simp)

@[simp] lemma bv_eq_top_of_eq {x y : bSet 𝔹} (h_eq : x = y) : x =ᴮ y = ⊤ := by
  subst h_eq; simp

@[reducible] def empty' : bSet 𝔹 := mk PUnit (fun _ => ∅) (fun _ => ⊥)

def mem : bSet 𝔹 → bSet 𝔹 → 𝔹
  | a, ⟨α', A', B'⟩ => ⨆ a', B' a' ⊓ a =ᴮ A' a'

@[reducible] def empty'' : bSet 𝔹 :=
  mk (ULift Bool) (fun _ => ∅) fun x =>
    match x.down with
    | false => ⊥
    | true => ⊤

scoped infixl:80 " ∈ᴮ " => mem

lemma mem_unfold {u v : bSet 𝔹} : u ∈ᴮ v = ⨆ (i : v.type), v.bval i ⊓ u =ᴮ v.func i := by
  cases v; simp [mem, bv_eq]

theorem mem_mk {α : Type u} (A : α → bSet 𝔹) (B : α → 𝔹) (a : α) :
    B a ≤ A a ∈ᴮ mk α A B :=
  le_iSup_of_le a (by simp)

theorem mem_mk' (x : bSet 𝔹) (a : x.type) : x.bval a ≤ x.func a ∈ᴮ x := by
  cases x; exact mem_mk _ _ _

@[simp] theorem mem_mk'' {x : bSet 𝔹} {a : x.type} {Γ : 𝔹} :
    Γ ≤ x.bval a → Γ ≤ x.func a ∈ᴮ x :=
  poset_yoneda_inv Γ (mem_mk' x a)

@[reducible] protected def subset : bSet 𝔹 → bSet 𝔹 → 𝔹
  | ⟨α, A, B⟩, b => ⨅ a : α, B a ⟹ (A a ∈ᴮ b)

scoped infixl:80 " ⊆ᴮ " => bSet.subset

lemma subset_unfold {x u : bSet 𝔹} :
    x ⊆ᴮ u = (⨅ (j : x.type), x.bval j ⟹ x.func j ∈ᴮ u) := by
  cases x; simp [bSet.subset]

@[simp] protected def insert : bSet 𝔹 → 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, b, ⟨α, A, B⟩ => ⟨Option α, fun o => Option.rec u A o, fun o => Option.rec b B o⟩

protected def insert' : bSet 𝔹 → 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, b, ⟨α, A, B⟩ => ⟨Unit ⊕ α, Sum.rec (fun _ => u) A, Sum.rec (fun _ => b) B⟩

@[reducible] protected def insert1 : bSet 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, v => bSet.insert u ⊤ v

lemma insert1_unfold {u v : bSet 𝔹} :
    bSet.insert1 u v =
    ⟨Option v.type, fun o => Option.rec u v.func o, fun o => Option.rec ⊤ v.bval o⟩ := by
  cases v; simp [bSet.insert1, bSet.insert]

instance insert_bSet : Insert (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun u v => bSet.insert1 u v⟩

@[simp] lemma insert_unfold {y z : bSet 𝔹} : insert y z = bSet.insert y ⊤ z := rfl

@[simp] theorem mem_insert {x y z : bSet 𝔹} {b : 𝔹} :
    x ∈ᴮ bSet.insert y b z = (b ⊓ x =ᴮ y) ⊔ x ∈ᴮ z := by
  cases y; cases z
  simp only [bSet.insert, mem]
  rw [iSup_option]

@[simp] theorem mem_insert1 {x y z : bSet 𝔹} : x ∈ᴮ insert y z = x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [insert_unfold, mem_insert, top_inf_eq]

@[simp] theorem mem_insert1' {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ insert y z ↔ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [mem_insert1]

private def bv_eq_symm_aux : ∀ (x y : bSet 𝔹), x =ᴮ y = y =ᴮ x
  | ⟨α, A, B⟩, ⟨α', A', B'⟩ => by
    have : ∀ a a', A' a' =ᴮ A a = A a =ᴮ A' a' := fun a a' => (bv_eq_symm_aux (A a) (A' a')).symm
    simp only [bv_eq, this, inf_comm]

theorem bv_eq_symm {x y : bSet 𝔹} : x =ᴮ y = y =ᴮ x := bv_eq_symm_aux x y

theorem bv_eq_unfold (x y : bSet 𝔹) :
    x =ᴮ y = (⨅ (a : x.type), x.bval a ⟹ (x.func a ∈ᴮ y))
            ⊓ (⨅ (a' : y.type), (y.bval a' ⟹ (y.func a' ∈ᴮ x))) := by
  cases x; cases y; simp [mem, bv_eq, bv_eq_symm]

theorem bSet_axiom_of_extensionality (x y : bSet 𝔹) :
    (⨅ (z : bSet 𝔹), (z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (z ∈ᴮ y ⟹ z ∈ᴮ x)) ≤ x =ᴮ y := by
  rw [bv_eq_unfold]
  apply le_inf <;> apply le_iInf <;> intro i
  · apply iInf_le_of_le (x.func i)
    apply inf_le_left.trans
    apply imp_le_of_left_le
    cases x with | mk xα xA xB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i (le_inf le_rfl (by simp))
  · apply iInf_le_of_le (y.func i)
    apply inf_le_right.trans
    apply imp_le_of_left_le
    cases y with | mk yα yA yB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i (le_inf le_rfl (by simp))

lemma eq_of_subset_subset (x y : bSet 𝔹) : x ⊆ᴮ y ⊓ y ⊆ᴮ x ≤ x =ᴮ y := by
  rw [bv_eq_unfold, subset_unfold, subset_unfold]

lemma subset_subset_of_eq (x y : bSet 𝔹) : x =ᴮ y ≤ x ⊆ᴮ y ⊓ y ⊆ᴮ x := by
  rw [bv_eq_unfold, subset_unfold, subset_unfold]

theorem eq_iff_subset_subset {x y : bSet 𝔹} : x =ᴮ y = x ⊆ᴮ y ⊓ y ⊆ᴮ x :=
  le_antisymm (subset_subset_of_eq x y) (eq_of_subset_subset x y)

lemma subset_subset_of_eq' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) :
    Γ ≤ x ⊆ᴮ y ∧ Γ ≤ y ⊆ᴮ x := by
  rw [eq_iff_subset_subset] at H
  exact ⟨le_trans H inf_le_left, le_trans H inf_le_right⟩

lemma subset_of_eq {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) : Γ ≤ x ⊆ᴮ y :=
  (subset_subset_of_eq' H).left

@[simp] lemma subset_self {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ x :=
  le_trans le_top (by rw [show ⊤ = x =ᴮ x by simp, eq_iff_subset_subset]; exact inf_le_left)

theorem subset_ext {x y : bSet 𝔹} {Γ : 𝔹} (h₁ : Γ ≤ x ⊆ᴮ y) (h₂ : Γ ≤ y ⊆ᴮ x) :
    Γ ≤ x =ᴮ y := by
  rw [eq_iff_subset_subset]; exact le_inf h₁ h₂

theorem bv_eq_trans {x y z : bSet 𝔹} : (x =ᴮ y ⊓ y =ᴮ z) ≤ x =ᴮ z := by
  induction x generalizing y z with
  | mk α A B ih =>
  induction y with
  | mk α' A' B' =>
  induction z with
  | mk α'' A'' B'' =>

  have trans_fwd : ∀ (a : α) (a' : α') (a'' : α''),
      A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' ≤ A a =ᴮ A'' a'' := by
    intro a a' a''
    exact @ih a (A' a') (A'' a'')

  have trans_bwd : ∀ (a'' : α'') (a' : α') (a : α),
      A'' a'' =ᴮ A' a' ⊓ A' a' =ᴮ A a ≤ A'' a'' =ᴮ A a := by
    intro a'' a' a
    have h := trans_fwd a a' a''

    have eq1 : A'' a'' =ᴮ A' a' = A' a' =ᴮ A'' a'' := bv_eq_symm
    have eq2 : A' a' =ᴮ A a = A a =ᴮ A' a' := bv_eq_symm
    have eq3 : A a =ᴮ A'' a'' = A'' a'' =ᴮ A a := bv_eq_symm
    calc A'' a'' =ᴮ A' a' ⊓ A' a' =ᴮ A a
        = A' a' =ᴮ A'' a'' ⊓ A a =ᴮ A' a' := by rw [eq1, eq2]
      _ = A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' := by rw [inf_comm]
      _ ≤ A a =ᴮ A'' a'' := h
      _ = A'' a'' =ᴮ A a := eq3
  simp only [bv_eq]
  apply le_inf
  ·
    apply le_iInf; intro i
    rw [← deduction]

    have mem_y : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B i
        ≤ A i ∈ᴮ mk α' A' B' := by
      calc (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B i
          ≤ mk α A B =ᴮ mk α' A' B' ⊓ B i :=
            le_inf (inf_le_left.trans inf_le_left) inf_le_right
        _ ≤ A i ∈ᴮ mk α' A' B' := by
            rw [deduction]; exact inf_le_left.trans (iInf_le _ i)

    have yz_eq_avail : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B i
        ≤ mk α' A' B' =ᴮ mk α'' A'' B'' :=
      inf_le_left.trans inf_le_right

    suffices h : A i ∈ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'' ≤ A i ∈ᴮ mk α'' A'' B'' by
      exact le_trans (le_inf mem_y yz_eq_avail) h
    simp only [mem, bv_eq, func]
    rw [iSup_inf_eq]
    apply iSup_le; intro a'

    have elim_a' : B' a' ⊓ A i =ᴮ A' a' ⊓
        ((⨅ a_1, B' a_1 ⟹ ⨆ a'', B'' a'' ⊓ A' a_1 =ᴮ A'' a'') ⊓
         (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))
        ≤ A i =ᴮ A' a' ⊓ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'' := by
      apply le_inf (inf_le_left.trans inf_le_right)
      have h_imp : B' a' ⊓ A i =ᴮ A' a' ⊓
          ((⨅ a_1, B' a_1 ⟹ ⨆ a'', B'' a'' ⊓ A' a_1 =ᴮ A'' a'') ⊓
           (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))
          ≤ (B' a' ⟹ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'') ⊓ B' a' :=
        le_inf (inf_le_right.trans inf_le_left |>.trans (iInf_le _ a'))
               (inf_le_left.trans inf_le_left)
      exact le_trans h_imp bv_imp_elim
    calc B' a' ⊓ A i =ᴮ A' a' ⊓
        ((⨅ a_1, B' a_1 ⟹ ⨆ a'', B'' a'' ⊓ A' a_1 =ᴮ A'' a'') ⊓
         (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))
        ≤ A i =ᴮ A' a' ⊓ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'' := elim_a'
      _ ≤ ⨆ a'', B'' a'' ⊓ A i =ᴮ A'' a'' := by
          rw [inf_iSup_eq]
          apply iSup_le; intro a''
          apply le_iSup_of_le a''

          apply le_inf (inf_le_right.trans inf_le_left)
          calc A i =ᴮ A' a' ⊓ (B'' a'' ⊓ A' a' =ᴮ A'' a'')
              ≤ A i =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' :=
                le_inf inf_le_left (inf_le_right.trans inf_le_right)
            _ ≤ A i =ᴮ A'' a'' := trans_fwd i a' a''
  ·

    apply le_iInf; intro i''
    rw [← deduction]

    have yz_step : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B'' i''
        ≤ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' i'' := by

      simp only [bv_eq, func]
      calc (((⨅ a, B a ⟹ ⨆ a', B' a' ⊓ A a =ᴮ A' a') ⊓
             (⨅ a', B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a')) ⊓
            ((⨅ a', B' a' ⟹ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'') ⊓
             (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))) ⊓ B'' i''
          ≤ (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a'') ⊓ B'' i'' := by
            apply le_inf
            · exact inf_le_left.trans (inf_le_right.trans inf_le_right)
            · exact inf_le_right
        _ ≤ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' i'' :=
            le_trans (inf_le_inf_right _ (iInf_le _ i'')) bv_imp_elim

    have xy_eq_avail : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B'' i''
        ≤ mk α A B =ᴮ mk α' A' B' :=
      inf_le_left.trans inf_le_left

    calc (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B'' i''
        ≤ (⨆ a', B' a' ⊓ A' a' =ᴮ A'' i'') ⊓ mk α A B =ᴮ mk α' A' B' :=
          le_inf yz_step xy_eq_avail
      _ ≤ ⨆ a, B a ⊓ A a =ᴮ A'' i'' := by
          rw [iSup_inf_eq]
          apply iSup_le; intro a'

          simp only [bv_eq, func]

          have xy_step2 : B' a' ⊓ A' a' =ᴮ A'' i'' ⊓
              ((⨅ a, B a ⟹ ⨆ a', B' a' ⊓ A a =ᴮ A' a') ⊓
               (⨅ a', B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a'))
              ≤ A' a' =ᴮ A'' i'' ⊓ ⨆ a, B a ⊓ A a =ᴮ A' a' := by
            refine le_inf (inf_le_left.trans inf_le_right) ?_
            exact le_trans
              (le_inf (inf_le_right.trans inf_le_right |>.trans (iInf_le _ a'))
                      (inf_le_left.trans inf_le_left))
              bv_imp_elim
          calc B' a' ⊓ A' a' =ᴮ A'' i'' ⊓
              ((⨅ a, B a ⟹ ⨆ a', B' a' ⊓ A a =ᴮ A' a') ⊓
               (⨅ a', B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a'))
              ≤ A' a' =ᴮ A'' i'' ⊓ ⨆ a, B a ⊓ A a =ᴮ A' a' := xy_step2
            _ ≤ ⨆ a, B a ⊓ A a =ᴮ A'' i'' := by
                rw [inf_iSup_eq]
                apply iSup_le; intro a
                apply le_iSup_of_le a

                apply le_inf (inf_le_right.trans inf_le_left)

                calc A' a' =ᴮ A'' i'' ⊓ (B a ⊓ A a =ᴮ A' a')
                    ≤ A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' i'' := by
                      apply le_inf
                      · exact (inf_le_right.trans inf_le_right)
                      · exact inf_le_left
                  _ ≤ A a =ᴮ A'' i'' := trans_fwd a a' i''

lemma bv_trans {Γ : 𝔹} {a₁ a₂ a₃ : bSet 𝔹} (H₁ : Γ ≤ a₁ =ᴮ a₂) (H₂ : Γ ≤ a₂ =ᴮ a₃) :
    Γ ≤ a₁ =ᴮ a₃ :=
  le_trans (le_inf H₁ H₂) bv_eq_trans

@[symm] lemma bv_symm {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) : Γ ≤ y =ᴮ x := by
  rwa [bv_eq_symm]

lemma bv_rw {x y : bSet 𝔹} (H : x =ᴮ y = ⊤) (ϕ : bSet 𝔹 → 𝔹)
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} : ϕ y = ϕ x := by
  apply le_antisymm
  ·
    have : y =ᴮ x = ⊤ := by rw [bv_eq_symm]; exact H
    calc ϕ y ≤ ⊤ ⊓ ϕ y := by simp
      _ = (y =ᴮ x) ⊓ ϕ y := by rw [this]
      _ ≤ ϕ x := h_congr y x
  ·
    calc ϕ x ≤ ⊤ ⊓ ϕ x := by simp
      _ = (x =ᴮ y) ⊓ ϕ x := by rw [H]
      _ ≤ ϕ y := h_congr x y

lemma subst_congr_mem_left {u v w : bSet 𝔹} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w := by
  simp only [mem_unfold]
  rw [inf_iSup_eq]
  apply iSup_le; intro i
  apply le_iSup_of_le i

  apply le_inf (inf_le_right.trans inf_le_left)

  calc u =ᴮ v ⊓ (w.bval i ⊓ u =ᴮ w.func i)
      ≤ u =ᴮ v ⊓ u =ᴮ w.func i := le_inf inf_le_left (inf_le_right.trans inf_le_right)
    _ = v =ᴮ u ⊓ u =ᴮ w.func i := by rw [bv_eq_symm]
    _ ≤ v =ᴮ w.func i := bv_eq_trans

@[simp] lemma subst_congr_mem_left' {Γ : 𝔹} {u v w : bSet 𝔹} :
    Γ ≤ u =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ v ∈ᴮ w :=
  fun h₁ h₂ => poset_yoneda_inv Γ subst_congr_mem_left (le_inf h₁ h₂)

lemma subst_congr_mem_right {u v w : bSet 𝔹} : (v =ᴮ w ⊓ u ∈ᴮ v) ≤ u ∈ᴮ w := by
  cases v with | mk vα vA vB =>
  rw [mem_unfold (v := mk vα vA vB)]
  rw [inf_iSup_eq]
  apply iSup_le; intro i

  have mem_w : mk vα vA vB =ᴮ w ⊓ vB i ≤ vA i ∈ᴮ w := by
    rw [deduction]

    calc mk vα vA vB =ᴮ w
        ≤ ⨅ j, vB j ⟹ vA j ∈ᴮ w := by rw [bv_eq_unfold]; exact inf_le_left
      _ ≤ vB i ⟹ vA i ∈ᴮ w := iInf_le _ i

  have step1 : mk vα vA vB =ᴮ w ⊓ (vB i ⊓ u =ᴮ vA i) ≤ vA i ∈ᴮ w ⊓ u =ᴮ vA i :=
    le_inf (le_trans (le_inf inf_le_left (inf_le_right.trans inf_le_left)) mem_w)
           (inf_le_right.trans inf_le_right)
  have step2 : vA i ∈ᴮ w ⊓ u =ᴮ vA i ≤ u ∈ᴮ w := by

    have h : vA i =ᴮ u ⊓ vA i ∈ᴮ w ≤ u ∈ᴮ w := subst_congr_mem_left
    have heq : vA i ∈ᴮ w ⊓ u =ᴮ vA i = vA i =ᴮ u ⊓ vA i ∈ᴮ w := by
      rw [inf_comm (a := vA i ∈ᴮ w)]
      congr 1
      exact bv_eq_symm
    rw [heq]; exact h
  exact le_trans step1 step2

@[simp] lemma subst_congr_mem_right' {Γ : 𝔹} {u v w : bSet 𝔹} :
    Γ ≤ w =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ u ∈ᴮ v :=
  fun h₁ h₂ => poset_yoneda_inv Γ subst_congr_mem_right (le_inf h₁ h₂)

lemma bounded_forall {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
    (⨅ (i_x : v.type), (v.bval i_x ⟹ ϕ (v.func i_x))) =
    (⨅ (x : bSet 𝔹), x ∈ᴮ v ⟹ ϕ x) := by
  apply le_antisymm
  · apply le_iInf; intro x
    cases v with | mk vα vA vB =>
    simp only [bval, func, mem]
    rw [supr_imp_eq]
    apply le_iInf; intro i_y
    apply iInf_le_of_le i_y
    rw [← deduction, ← inf_assoc]
    apply le_trans
    · exact inf_le_inf bv_imp_elim le_rfl
    rw [inf_comm, bv_eq_symm]
    exact h_congr _ _
  · apply le_iInf; intro i_x'
    apply iInf_le_of_le (func v i_x')
    apply imp_le_of_left_le
    cases v with | mk vα vA vB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i_x' (le_inf le_rfl (by simp))

lemma bounded_exists {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
    (⨆ (i_x : v.type), (v.bval i_x ⊓ ϕ (v.func i_x))) =
    (⨆ (x : bSet 𝔹), x ∈ᴮ v ⊓ ϕ x) := by
  apply le_antisymm
  · apply iSup_le; intro i_x
    apply le_iSup_of_le (v.func i_x)
    exact le_inf (inf_le_left.trans (mem_mk' v i_x)) inf_le_right
  · apply iSup_le; intro x
    rw [mem_unfold]
    apply bv_cases_left (h := fun i_x => ?_)

    apply le_iSup_of_le i_x

    apply le_inf
    · exact inf_le_left.trans inf_le_left
    ·

      have : (v.bval i_x ⊓ x =ᴮ v.func i_x) ⊓ ϕ x ≤ x =ᴮ v.func i_x ⊓ ϕ x :=
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
      exact le_trans this (h_congr x (v.func i_x))

lemma mem_unfold' {u v : bSet 𝔹} : u ∈ᴮ v = ⨆ z, z ∈ᴮ v ⊓ u =ᴮ z := by

  rw [← @bounded_exists _ _ v (fun z => u =ᴮ z)
        (h_congr := fun x y => by rw [inf_comm]; exact bv_eq_trans),
      mem_unfold]

lemma subset_unfold' {x u : bSet 𝔹} : x ⊆ᴮ u = ⨅ (w : bSet 𝔹), w ∈ᴮ x ⟹ w ∈ᴮ u := by
  simp only [subset_unfold]
  rw [bounded_forall (h_congr := fun a b => subst_congr_mem_left)]

lemma bv_eq_unfold' {x y : bSet 𝔹} :
    x =ᴮ y = (⨅ z, z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (⨅ z, z ∈ᴮ y ⟹ z ∈ᴮ x) := by
  rw [eq_iff_subset_subset, subset_unfold', subset_unfold']

theorem mem_ext {x y : bSet 𝔹} {Γ : 𝔹}
    (h₁ : Γ ≤ ⨅ z, z ∈ᴮ x ⟹ z ∈ᴮ y)
    (h₂ : Γ ≤ ⨅ z, z ∈ᴮ y ⟹ z ∈ᴮ x) : Γ ≤ x =ᴮ y := by
  rw [bv_eq_unfold']; exact le_inf h₁ h₂

@[simp] lemma subset_self_eq_top {x : bSet 𝔹} : x ⊆ᴮ x = ⊤ :=
  top_unique subset_self

lemma subset_trans {x y z : bSet 𝔹} : x ⊆ᴮ y ⊓ y ⊆ᴮ z ≤ x ⊆ᴮ z := by
  simp only [subset_unfold']
  apply le_iInf; intro w
  rw [← deduction]

  have hxy_spec : (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ≤ w ∈ᴮ x ⟹ w ∈ᴮ y := iInf_le _ w
  have hyz_spec : (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ≤ w ∈ᴮ y ⟹ w ∈ᴮ z := iInf_le _ w
  have hxy : (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x
      ≤ w ∈ᴮ y :=
    le_trans (le_inf ((inf_le_left.trans inf_le_left).trans hxy_spec) inf_le_right) bv_imp_elim
  calc (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x
      ≤ (w ∈ᴮ y ⟹ w ∈ᴮ z) ⊓ w ∈ᴮ y :=
        le_inf ((inf_le_left.trans inf_le_right).trans hyz_spec) hxy
    _ ≤ w ∈ᴮ z := bv_imp_elim

lemma subset_trans' {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ x ⊆ᴮ y) (H₂ : Γ ≤ y ⊆ᴮ z) : Γ ≤ x ⊆ᴮ z :=
  poset_yoneda_inv Γ subset_trans (le_inf H₁ H₂)

lemma mem_of_mem_subset {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₂ : Γ ≤ y ⊆ᴮ z) (H₁ : Γ ≤ x ∈ᴮ y) : Γ ≤ x ∈ᴮ z := by
  rw [subset_unfold'] at H₂
  exact context_imp_elim (context_specialize H₂ x) H₁

lemma subst_congr_subset_left {x v u : bSet 𝔹} :
    ((v ⊆ᴮ u) ⊓ (x =ᴮ v) : 𝔹) ≤ (x ⊆ᴮ u) := by
  rw [subset_unfold' (x := x), subset_unfold' (x := v)]
  apply le_iInf; intro z
  rw [← deduction]

  have h_mem : (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ x =ᴮ v ⊓ z ∈ᴮ x ≤ z ∈ᴮ v := by
    calc (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ x =ᴮ v ⊓ z ∈ᴮ x
        ≤ x =ᴮ v ⊓ z ∈ᴮ x :=
          le_inf (inf_le_left.trans inf_le_right) inf_le_right
      _ ≤ z ∈ᴮ v := subst_congr_mem_right
  have h_sub : (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ z ∈ᴮ v ≤ z ∈ᴮ u := by
    have hspec : (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ≤ z ∈ᴮ v ⟹ z ∈ᴮ u := iInf_le _ z
    exact le_trans (le_inf (inf_le_left.trans hspec) inf_le_right) bv_imp_elim
  calc (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ x =ᴮ v ⊓ z ∈ᴮ x
      ≤ (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ z ∈ᴮ v :=
        le_inf (inf_le_left.trans inf_le_left) h_mem
    _ ≤ z ∈ᴮ u := h_sub

lemma subst_congr_subset_right {x v u : bSet 𝔹} :
    ((v ⊆ᴮ u) ⊓ (u =ᴮ x) : 𝔹) ≤ (v ⊆ᴮ x) := by
  rw [subset_unfold, subset_unfold]
  apply le_iInf; intro j
  rw [← deduction]

  calc (⨅ j', v.bval j' ⟹ v.func j' ∈ᴮ u) ⊓ u =ᴮ x ⊓ v.bval j
      ≤ (v.bval j ⟹ v.func j ∈ᴮ u) ⊓ v.bval j ⊓ u =ᴮ x :=
        le_inf (le_inf ((inf_le_left.trans inf_le_left).trans (iInf_le _ j)) inf_le_right)
               (inf_le_left.trans inf_le_right)
    _ ≤ v.func j ∈ᴮ u ⊓ u =ᴮ x :=
        le_inf (le_trans inf_le_left bv_imp_elim) inf_le_right
    _ ≤ v.func j ∈ᴮ x := by
        rw [inf_comm]; exact subst_congr_mem_right

lemma bv_rw'₀ {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {H_new : Γ ≤ ϕ y} : Γ ≤ ϕ x :=
  poset_yoneda_inv Γ (h_congr _ _) (le_inf (by rwa [bv_eq_symm]) H_new)

@[reducible] def B_ext (ϕ : bSet 𝔹 → 𝔹) : Prop :=
  ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y

lemma bv_rw' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : B_ext ϕ} {H_new : Γ ≤ ϕ y} : Γ ≤ ϕ x :=
  bv_rw'₀ H (h_congr := h_congr) (H_new := H_new)

@[simp] lemma B_ext_bv_eq_left {y : bSet 𝔹} : B_ext (fun x => x =ᴮ y) :=
  fun _ _ => by rw [bv_eq_symm (x := _) (y := _)]; exact bv_eq_trans

@[simp] lemma B_ext_bv_eq_right {x : bSet 𝔹} : B_ext (fun y => x =ᴮ y) :=
  fun _ _ => by rw [inf_comm]; exact bv_eq_trans

@[simp] lemma B_ext_mem_left {y : bSet 𝔹} : B_ext (fun x => x ∈ᴮ y) :=
  fun _ _ => subst_congr_mem_left

@[simp] lemma B_ext_mem_right {x : bSet 𝔹} : B_ext (fun y => x ∈ᴮ y) :=
  fun _ _ => subst_congr_mem_right

@[simp] lemma B_ext_subset_left {y : bSet 𝔹} : B_ext (fun x => x ⊆ᴮ y) :=
  fun _ _ => by rw [inf_comm, bv_eq_symm]; exact subst_congr_subset_left

@[simp] lemma B_ext_subset_right {x : bSet 𝔹} : B_ext (fun y => x ⊆ᴮ y) :=
  fun _ _ => by rw [inf_comm]; exact subst_congr_subset_right

@[simp] lemma B_ext_sup {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
    B_ext (fun x => ϕ₁ x ⊔ ϕ₂ x) := by
  intros x y
  rw [inf_comm, deduction]
  apply sup_le
  · rw [← deduction]; exact le_trans (by rw [inf_comm]; exact h₁ x y) le_sup_left
  · rw [← deduction]; exact le_trans (by rw [inf_comm]; exact h₂ x y) le_sup_right

@[simp] lemma B_ext_inf {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} (h₁ : B_ext ϕ₁) (h₂ : B_ext ϕ₂) :
    B_ext (fun x => ϕ₁ x ⊓ ϕ₂ x) := by
  intros x y
  apply le_inf
  · exact le_trans (inf_le_inf_left _ inf_le_left) (h₁ x y)
  · exact le_trans (inf_le_inf_left _ inf_le_right) (h₂ x y)

@[simp] lemma B_ext_imp {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
    B_ext (fun x => ϕ₁ x ⟹ ϕ₂ x) := by
  intros x y
  rw [← deduction]

  have step1 : x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₁ x := by
    apply le_trans _ (h₁ y x)
    · exact le_inf (inf_le_left.trans (by rw [bv_eq_symm]; exact inf_le_left)) inf_le_right
  have step2 : x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₂ x :=
    le_trans (le_inf (inf_le_left.trans inf_le_right) step1) bv_imp_elim
  exact le_trans (le_inf (inf_le_left.trans inf_le_left) step2) (h₂ x y)

@[simp] lemma B_ext_const {b : 𝔹} : B_ext (fun _ : bSet 𝔹 => b) :=
  fun _ _ => inf_le_right

@[simp] lemma B_ext_neg {ϕ₁ : bSet 𝔹 → 𝔹} {h : B_ext ϕ₁} : B_ext (fun x => (ϕ₁ x)ᶜ) := by
  simp only [← imp_bot]
  exact B_ext_imp (h₁ := h) (h₂ := B_ext_const)

@[simp] lemma B_ext_iInf {ι : Type*} {Ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀ i, B_ext (Ψ i)} :
    B_ext (fun x => ⨅ i, Ψ i x) := by
  intros x y
  apply le_iInf; intro i
  apply bv_specialize_right i
  exact h i x y

@[simp] lemma B_ext_iSup {ι : Type*} {ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀ i, B_ext (ψ i)} :
    B_ext (fun x => ⨆ i, ψ i x) := by
  intros x y
  apply bv_cases_right; intro i
  apply bv_use i
  exact h i x y

@[reducible] def B_congr (t : bSet 𝔹 → bSet 𝔹) : Prop :=
  ∀ {x₁ x₂ : bSet 𝔹} {Γ : 𝔹}, Γ ≤ x₁ =ᴮ x₂ → Γ ≤ t x₁ =ᴮ t x₂

@[simp] lemma B_ext_term (ϕ : bSet 𝔹 → 𝔹) (t : bSet 𝔹 → bSet 𝔹)
    (H : B_ext ϕ) (H' : B_congr t) :
    B_ext (fun z => ϕ (t z)) := by
  intros x y

  calc x =ᴮ y ⊓ ϕ (t x)
      ≤ t x =ᴮ t y ⊓ ϕ (t x) :=
        le_inf (H' inf_le_left) inf_le_right
    _ ≤ ϕ (t y) := H (t x) (t y)

lemma bv_rw'' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    (H_new : Γ ≤ ϕ x) (h_congr : B_ext ϕ) : Γ ≤ ϕ y :=
  poset_yoneda_inv Γ (h_congr x y) (le_inf H H_new)

lemma mem_congr {Γ : 𝔹} {x₁ x₂ y₁ y₂ : bSet 𝔹}
    (H₁ : Γ ≤ x₁ =ᴮ y₁) (H₂ : Γ ≤ x₂ =ᴮ y₂) (H₃ : Γ ≤ x₁ ∈ᴮ x₂) :
    Γ ≤ y₁ ∈ᴮ y₂ := by
  apply bv_rw' (H := by rwa [bv_eq_symm]) (h_congr := B_ext_mem_left)
  apply bv_rw' (H := by rwa [bv_eq_symm]) (h_congr := B_ext_mem_right)
  exact H₃

@[reducible] def b_setoid (Γ : 𝔹) : Setoid (bSet 𝔹) :=
  { r := bv_eq' Γ
    iseqv := ⟨fun _ => bv_refl, fun h => bv_symm h, fun h1 h2 => bv_trans h1 h2⟩ }

lemma bv_cc_mk_iff {Γ : 𝔹} {x y : bSet 𝔹} :
    Γ ≤ x =ᴮ y ↔ (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x) = (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) := by
  constructor
  · intro h; exact Quotient.sound h
  · intro h; exact Quotient.exact h

lemma bv_cc_mk {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) :
    (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x) = (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) :=
  bv_cc_mk_iff.mp H

def b_setoid_mem (Γ : 𝔹) :
    Quotient (b_setoid Γ) → Quotient (b_setoid Γ) → Prop :=
  Quotient.lift₂ (fun x y => Γ ≤ x ∈ᴮ y)
    (by intros a₁ b₁ a₂ b₂ H_eqv₁ H_eqv₂
        apply propext; constructor <;> intro H
        · exact mem_congr H_eqv₁ H_eqv₂ H
        · exact mem_congr (bv_symm H_eqv₁) (bv_symm H_eqv₂) H)

lemma bv_cc_mk_mem_iff {Γ : 𝔹} {x y : bSet 𝔹} :
    Γ ≤ x ∈ᴮ y ↔ b_setoid_mem Γ (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x)
      (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) := by
  rfl

lemma bv_cc_mk_mem {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x ∈ᴮ y) :
    b_setoid_mem Γ (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x) (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) :=
  bv_cc_mk_mem_iff.mp H

def is_definite (u : bSet 𝔹) : Prop := ∀ i : u.type, u.bval i = ⊤

lemma eq_empty {u : bSet 𝔹} : u =ᴮ ∅ = (⨆ i, u.bval i)ᶜ := by
  apply le_antisymm
  ·
    rw [compl_iSup]
    apply le_iInf; intro i

    rw [← imp_bot, ← deduction]

    have h2 : u.func i ∈ᴮ ∅ = ⊥ := by
      rw [mem_unfold]; exact exists_over_empty _

    have h1 : u =ᴮ ∅ ≤ u.bval i ⟹ u.func i ∈ᴮ ∅ := by
      rw [bv_eq_unfold]; exact inf_le_left.trans (iInf_le _ i)
    rw [h2] at h1

    rw [imp_bot] at h1
    exact le_trans (le_inf (inf_le_left.trans h1) inf_le_right) disjoint_compl_left.le_bot
  ·
    rw [bv_eq_unfold]
    apply le_inf
    · apply le_iInf; intro j

      have : u.func j ∈ᴮ ∅ = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
      rw [this, imp_bot]
      exact compl_le_compl (le_iSup _ j)
    · apply le_iInf; intro j; exact j.elim

@[simp] lemma empty_subset {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ ∅ ⊆ᴮ x := by
  rw [subset_unfold]
  apply le_iInf; intro i
  exact i.elim

lemma empty_spec {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ (x ∈ᴮ ∅)ᶜ := by
  have : x ∈ᴮ ∅ = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
  rw [this, compl_bot]; exact le_top

lemma bot_of_mem_empty {x : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ∈ᴮ ∅) : Γ ≤ ⊥ := by
  have hmem : x ∈ᴮ ∅ = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
  rw [hmem] at H; exact H

@[simp] lemma subst_congr_insert1_left {u w v : bSet 𝔹} :
    u =ᴮ w ≤ bSet.insert1 u v =ᴮ bSet.insert1 w v := by
  cases v with | mk α A B =>
  simp only [bSet.insert1, bSet.insert, bv_eq, mem, iInf_option, iSup_option,
    top_inf_eq, inf_top_eq]
  apply le_inf
  ·
    apply le_inf
    ·

      have : (⊤ : 𝔹) ⟹ (u =ᴮ w ⊔ ⨆ b, B b ⊓ u =ᴮ A b) = u =ᴮ w ⊔ ⨆ b, B b ⊓ u =ᴮ A b := by
        unfold imp; simp
      rw [this]; exact le_sup_left
    · apply le_iInf; intro i

      rw [← deduction]
      exact le_trans inf_le_right (le_trans (mem_mk' (mk α A B) i) le_sup_right)
  ·
    apply le_inf
    ·

      have : (⊤ : 𝔹) ⟹ (u =ᴮ w ⊔ ⨆ b, B b ⊓ A b =ᴮ w) = u =ᴮ w ⊔ ⨆ b, B b ⊓ A b =ᴮ w := by
        unfold imp; simp
      rw [this]; exact le_sup_left
    · apply le_iInf; intro i
      rw [← deduction]

      apply le_trans inf_le_right
      apply le_trans _ le_sup_right
      exact le_iSup_of_le i (by simp [bv_eq_refl])

@[simp] lemma subst_congr_insert1_left' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ bSet.insert1 u v =ᴮ bSet.insert1 w v :=
  le_trans h subst_congr_insert1_left

@[simp] lemma subst_congr_insert1_right {u w v : bSet 𝔹} :
    u =ᴮ w ≤ bSet.insert1 v u =ᴮ bSet.insert1 v w := by
  rw [eq_iff_subset_subset (x := bSet.insert1 v u) (y := bSet.insert1 v w)]
  apply le_inf
  ·
    rw [subset_unfold']
    apply le_iInf; intro z
    rw [← deduction, show z ∈ᴮ bSet.insert1 v u = z =ᴮ v ⊔ z ∈ᴮ u from mem_insert1,
        show z ∈ᴮ bSet.insert1 v w = z =ᴮ v ⊔ z ∈ᴮ w from mem_insert1]
    apply bv_or_elim_right
    · exact le_trans inf_le_right le_sup_left
    · apply le_trans _ le_sup_right; exact subst_congr_mem_right
  ·
    rw [subset_unfold']
    apply le_iInf; intro z
    rw [← deduction, show z ∈ᴮ bSet.insert1 v w = z =ᴮ v ⊔ z ∈ᴮ w from mem_insert1,
        show z ∈ᴮ bSet.insert1 v u = z =ᴮ v ⊔ z ∈ᴮ u from mem_insert1]
    apply bv_or_elim_right
    · exact le_trans inf_le_right le_sup_left
    · apply le_trans _ le_sup_right
      rw [bv_eq_symm]; exact subst_congr_mem_right

@[simp] lemma subst_congr_insert1_right' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ bSet.insert1 v u =ᴮ bSet.insert1 v w :=
  le_trans h subst_congr_insert1_right

@[simp] lemma subst_congr_insert1_left'' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ (bSet.insert1 v (bSet.insert1 u ∅)) =ᴮ (bSet.insert1 v (bSet.insert1 w ∅)) :=
  subst_congr_insert1_right' (subst_congr_insert1_left' h)

@[simp] lemma subst_congr_insert1_right'' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ (bSet.insert1 u (bSet.insert1 v ∅)) =ᴮ (bSet.insert1 w (bSet.insert1 v ∅)) :=
  le_trans h subst_congr_insert1_left

@[simp] lemma eq_singleton_of_eq {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ x =ᴮ y) :
    c ≤ (bSet.insert1 x ∅) =ᴮ (bSet.insert1 y ∅) :=
  subst_congr_insert1_left' h

lemma eq_of_eq_singleton {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ (bSet.insert1 x ∅) =ᴮ (bSet.insert1 y ∅)) :
    c ≤ x =ᴮ y := by

  have mem_eq : x ∈ᴮ bSet.insert1 y ∅ = x =ᴮ y := by
    show x ∈ᴮ bSet.insert1 y ∅ = x =ᴮ y
    rw [show bSet.insert1 y ∅ = insert y ∅ from rfl, mem_insert1]
    have : x ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]

  have h1 : bSet.insert1 x ∅ =ᴮ bSet.insert1 y ∅ ≤ bSet.insert1 x ∅ ⊆ᴮ bSet.insert1 y ∅ := by
    rw [bv_eq_unfold]; exact inf_le_left
  have h2 : bSet.insert1 x ∅ ⊆ᴮ bSet.insert1 y ∅ ≤ x ∈ᴮ bSet.insert1 y ∅ := by
    rw [subset_unfold']
    apply iInf_le_of_le x

    have hmem : x ∈ᴮ bSet.insert1 x ∅ = ⊤ := by
      rw [show bSet.insert1 x ∅ = insert x ∅ from rfl, mem_insert1]
      simp [bv_eq_refl, mem_unfold, exists_over_empty]
    unfold imp
    rw [hmem, compl_top, bot_sup_eq]
  rw [mem_eq] at h2
  exact le_trans (le_trans h h1) h2

lemma eq_singleton_iff_eq {x y : bSet 𝔹} {c : 𝔹} :
    c ≤ (bSet.insert1 x ∅) =ᴮ (bSet.insert1 y ∅) ↔ c ≤ x =ᴮ y :=
  ⟨fun h => eq_of_eq_singleton h, fun h => eq_singleton_of_eq h⟩

lemma singleton_unfold {x : bSet 𝔹} : (insert x (∅ : bSet 𝔹)) = bSet.insert1 x ∅ := rfl

@[simp] lemma singleton_type {x : bSet 𝔹} :
    (type (bSet.insert1 x ∅)) = Option PEmpty := by
  simp only [bSet.insert1, bSet.insert, bSet.type, empty, bSet.mk.injEq]
  rfl

@[simp] lemma singleton_func {x : bSet 𝔹} {o : Option PEmpty} :
    func (bSet.insert1 x ∅) o = Option.casesOn o x (fun e => e.elim) := by
  simp only [bSet.insert1, bSet.insert]
  cases o with
  | none => rfl
  | some e => exact (e.elim)

@[simp] lemma singleton_bval {x : bSet 𝔹} {o : Option PEmpty} :
    bval (bSet.insert1 x ∅) o = Option.casesOn o ⊤ (fun e => e.elim) := by
  simp only [bSet.insert1, bSet.insert]
  cases o with
  | none => rfl
  | some e => exact (e.elim)

@[simp] lemma singleton_bval_none {x : bSet 𝔹} : bval (bSet.insert1 x ∅) none = ⊤ := by
  have := singleton_bval (x := x) (o := none)
  simp at this; exact this

def mixture {ι : Type u} (a : ι → 𝔹) (u : ι → bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ (i : ι), (u i).type, fun x => (u x.1).func x.2,
    fun x => ⨆ (j : ι), a j ⊓ (u x.1).func x.2 ∈ᴮ u j⟩

@[reducible] def bool_map {α : Type*} (a₁ a₂ : α) : ULift Bool → α :=
  fun x => Bool.rec a₁ a₂ x.down

def two_term_mixture (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) : bSet 𝔹 :=
  @mixture 𝔹 _ (ULift Bool) (bool_map a₁ a₂) (bool_map u₁ u₂)

@[simp] lemma bval_mixture {ι : Type u} {a : ι → 𝔹} {u : ι → bSet 𝔹} :
    (mixture a u).bval = fun x => ⨆ (j : ι), a j ⊓ (u x.1).func x.2 ∈ᴮ u j := rfl

@[simp] lemma two_term_mixture_bval (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
    ∀ i, (two_term_mixture a₁ a₂ h_anti u₁ u₂).bval i =
      (a₁ ⊓ ((two_term_mixture a₁ a₂ h_anti u₁ u₂).func i ∈ᴮ u₁)) ⊔
      (a₂ ⊓ ((two_term_mixture a₁ a₂ h_anti u₁ u₂).func i ∈ᴮ u₂)) := fun i => by
  simp only [two_term_mixture, bval_mixture, bool_map]

  apply le_antisymm
  · apply iSup_le; intro ⟨j⟩; cases j
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le
    · exact le_iSup_of_le ⟨false⟩ le_rfl
    · exact le_iSup_of_le ⟨true⟩ le_rfl

def floris_mixture {ι : Type u} (a : ι → 𝔹) (u : ι → bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ (i : ι), (u i).type, fun x => (u x.1).func x.2, fun x => a x.1 ⊓ (u x.1).bval x.2⟩

lemma two_term_mixture_h_star (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
    ∀ i j : ULift Bool, (bool_map a₁ a₂) i ⊓ (bool_map a₁ a₂) j ≤
      (bool_map u₁ u₂) i =ᴮ (bool_map u₁ u₂) j := by
  intro ⟨bi⟩ ⟨bj⟩
  cases bi <;> cases bj <;> simp [bool_map, bv_eq_refl]
  all_goals simp [bool_map, h_anti, inf_comm]

lemma mixing_lemma' {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹)
    (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) :
    ∀ i : ι, a i ≤ (mixture a τ) =ᴮ τ i := fun i => by
  rw [bv_eq_unfold]
  apply le_inf
  ·
    apply le_iInf; intro ⟨i_z_fst, i_z_snd⟩
    rw [← deduction]

    simp only [bval_mixture, mixture, func, bval]
    rw [inf_iSup_eq]
    apply iSup_le; intro j

    rw [← inf_assoc]

    have h_eq := h_star i j

    have heq : a i ⊓ a j ≤ τ i =ᴮ τ j := h_eq
    calc a i ⊓ a j ⊓ (τ i_z_fst).func i_z_snd ∈ᴮ τ j
        ≤ (τ i =ᴮ τ j) ⊓ (τ i_z_fst).func i_z_snd ∈ᴮ τ j :=
          le_inf (inf_le_left.trans heq) inf_le_right
      _ = (τ j =ᴮ τ i) ⊓ (τ i_z_fst).func i_z_snd ∈ᴮ τ j := by rw [bv_eq_symm]
      _ ≤ (τ i_z_fst).func i_z_snd ∈ᴮ τ i := subst_congr_mem_right
  ·
    apply le_iInf; intro i_z
    rw [← deduction]

    apply le_trans _ (mem_mk' (mixture a τ) ⟨i, i_z⟩)

    simp only [bval_mixture, mixture, func]

    apply le_iSup_of_le i

    exact le_inf inf_le_left (inf_le_right.trans (mem_mk' (τ i) i_z))

lemma mixing_lemma {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹)
    (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) :
    ∃ x, ∀ i : ι, a i ≤ x =ᴮ τ i :=
  ⟨mixture a τ, fun i => mixing_lemma' a τ h_star i⟩

lemma mixing_lemma_two_term (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
    a₁ ≤ (two_term_mixture a₁ a₂ h_anti u₁ u₂ =ᴮ u₁) ∧
    a₂ ≤ (two_term_mixture a₁ a₂ h_anti u₁ u₂ =ᴮ u₂) := by
  have h := mixing_lemma' (bool_map a₁ a₂) (bool_map u₁ u₂)
    (two_term_mixture_h_star a₁ a₂ h_anti u₁ u₂)
  exact ⟨h ⟨false⟩, h ⟨true⟩⟩

section smallness
variable {ϕ : bSet 𝔹 → 𝔹}

@[reducible, simp] noncomputable def fiber_lift (b : ϕ '' Set.univ) :=
  Classical.indefiniteDescription (fun a : bSet 𝔹 => ϕ a = b.val) (by
    obtain ⟨x, _, hx⟩ := b.2
    exact ⟨x, hx⟩)

noncomputable def B_small_witness : bSet 𝔹 :=
  ⟨ϕ '' Set.univ, fun b => (fiber_lift b).val, fun _ => ⊤⟩

@[simp] lemma B_small_witness_spec : ∀ b, ϕ ((@B_small_witness _ _ ϕ).func b) = b.val :=
  fun b => (fiber_lift b).2

lemma B_small_witness_supr :
    (⨆ (x : bSet 𝔹), ϕ x) = ⨆ (b : (@B_small_witness _ _ ϕ).type), ϕ (B_small_witness.func b) := by
  apply le_antisymm
  · apply iSup_le; intro x
    let b : (@B_small_witness _ _ ϕ).type :=
      ⟨ϕ x, Set.mem_image_of_mem _ (Set.mem_univ _)⟩
    apply le_iSup_of_le b

    have h := @B_small_witness_spec _ _ ϕ b

    simp only [b, Subtype.coe_mk] at h
    exact h.symm.le
  · apply iSup_le; intro b
    apply le_iSup_of_le (fiber_lift b).val
    simp only [B_small_witness, func]
    exact le_rfl

@[reducible, simp] def not_b (b : 𝔹) : Set 𝔹 := {y | y ≠ b}

section well_ordering
variable {α : Type*} (r : α → α → Prop) [IsWellOrder α r]
local infix:50 " ≺ " => r

def down_set (a : α) : Set α := {a' | a' ≺ a}

def down_set' (a : α) : Set α := insert a (down_set r a)

lemma down_set_trans {a b : α} (h : a ≺ b) : down_set r a ⊆ down_set r b := by
  intro x (H : r x a)
  exact (inferInstance : IsTrans α r).trans x a b H h

end well_ordering

variable (r : type (@B_small_witness _ _ ϕ) → type (@B_small_witness _ _ ϕ) → Prop)
variable [IsWellOrder _ r]
local infix:50 " ≺ " => r

lemma down_set_mono_supr {a b : type B_small_witness} (h : r a b)
    {s : type (@B_small_witness _ _ ϕ) → 𝔹} :
    (⨆ i ∈ down_set r a, s i) ≤ (⨆ i ∈ down_set r b, s i) :=
  biSup_mono (fun i H => down_set_trans r h H)

lemma down_set'_mono_supr {a b : type B_small_witness} (h : r a b)
    {s : type (@B_small_witness _ _ ϕ) → 𝔹} :
    (⨆ i ∈ down_set' r a, s i) ≤ (⨆ i ∈ down_set' r b, s i) :=
  biSup_mono (fun i H => by
    rcases H with rfl | H
    · exact Or.inr h
    · exact Or.inr (down_set_trans r h H))

def witness_antichain (b : type (@B_small_witness _ _ ϕ)) : 𝔹 :=
  b.val \ ⨆ (b' : ↑(down_set r b)), b'.val.val

lemma r_trichotomy (x y : type B_small_witness) : r x y ∨ x = y ∨ r y x :=
  @trichotomous _ r _ x y

lemma dichotomy_of_neq (x y : type B_small_witness) : x ≠ y → r x y ∨ r y x := by
  intro h
  rcases r_trichotomy r x y with h1 | rfl | h1
  · exact Or.inl h1
  · exact absurd rfl h
  · exact Or.inr h1

lemma not_ge_of_in_down_set (a b : type B_small_witness) : a ∈ down_set r b → ¬ r b a := by
  intro H H'
  have H'' : r a b := H
  have : r a a := Trans.trans H'' H'
  exact absurd this (irrefl a)

lemma witness_antichain_index {i j : type B_small_witness} (h_neq : i ≠ j) :
    witness_antichain r i ⊓ witness_antichain r j = ⊥ := by
  apply bot_unique
  simp only [witness_antichain, sdiff_eq]

  rcases dichotomy_of_neq r i j h_neq with hij | hji
  ·

    have h_mem : i.val ≤ ⨆ (b' : ↑(down_set r j)), b'.val.val :=
      le_iSup_of_le ⟨i, hij⟩ le_rfl

    have step1 : i.val ⊓ (⨆ (b' : ↑(down_set r j)), b'.val.val)ᶜ ≤ ⊥ := by
      have : i.val ⊓ (⨆ (b' : ↑(down_set r j)), b'.val.val)ᶜ ≤
          (⨆ (b' : ↑(down_set r j)), b'.val.val) ⊓ (⨆ (b' : ↑(down_set r j)), b'.val.val)ᶜ :=
        inf_le_inf_right _ h_mem
      exact le_trans this (le_of_eq inf_compl_eq_bot)

    exact le_trans (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)) step1
  ·
    have h_mem : j.val ≤ ⨆ (b' : ↑(down_set r i)), b'.val.val :=
      le_iSup_of_le ⟨j, hji⟩ le_rfl
    have step1 : (⨆ (b' : ↑(down_set r i)), b'.val.val)ᶜ ⊓ j.val ≤ ⊥ := by
      have : (⨆ (b' : ↑(down_set r i)), b'.val.val)ᶜ ⊓ j.val ≤
          (⨆ (b' : ↑(down_set r i)), b'.val.val)ᶜ ⊓ (⨆ (b' : ↑(down_set r i)), b'.val.val) :=
        inf_le_inf_left _ h_mem
      exact le_trans this (le_of_eq (by rw [inf_comm, inf_compl_eq_bot]))

    exact le_trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left)) step1

lemma witness_antichain_antichain :
    ∀ i j : type (@B_small_witness _ _ ϕ), i ≠ j →
    witness_antichain r i ⊓ witness_antichain r j = ⊥ :=
  fun _i _j h => witness_antichain_index r h

lemma witness_antichain_property : ∀ b : type (@B_small_witness _ _ ϕ), witness_antichain r b ≤ b.val := by
  intro b; unfold witness_antichain; exact sdiff_le

lemma supr_antichain2_contains :
    (⨆ (b' : type (@B_small_witness _ _ ϕ)), ϕ (func (@B_small_witness _ _ ϕ) b')) ≤
    ⨆ (b : type (@B_small_witness _ _ ϕ)), witness_antichain r b := by
  apply iSup_le
  intro i

  have hspec := @B_small_witness_spec _ _ ϕ i
  rw [hspec]

  apply (IsWellOrder.wf (r := r)).induction i
  intro i ih

  calc i.val
      = witness_antichain r i ⊔ (i.val ⊓ ⨆ (j : ↑(down_set r i)), j.val.val) := by
          simp only [witness_antichain]; exact (sup_sdiff_inf _ _).symm
    _ ≤ (⨆ b, witness_antichain r b) ⊔ (⨆ b, witness_antichain r b) := by
          apply sup_le_sup
          · exact le_iSup (witness_antichain r) i
          ·
            calc i.val ⊓ ⨆ (j : ↑(down_set r i)), j.val.val
                ≤ ⨆ (j : ↑(down_set r i)), j.val.val := inf_le_right
              _ ≤ ⨆ b, witness_antichain r b := by
                  apply iSup_le; intro ⟨j, hj⟩; exact ih j hj
    _ = ⨆ b, witness_antichain r b := sup_idem _

end smallness

lemma maximum_principle (ϕ : bSet 𝔹 → 𝔹) (h_congr : B_ext ϕ) : ∃ u, (⨆ (x : bSet 𝔹), ϕ x) = ϕ u := by

  let r := @WellOrderingRel ((@B_small_witness 𝔹 _ ϕ).type)
  haveI : IsWellOrder _ r := WellOrderingRel.isWellOrder

  have mixing_hyp : ∀ i j : (@B_small_witness 𝔹 _ ϕ).type,
      witness_antichain r i ⊓ witness_antichain r j ≤
      ((@B_small_witness 𝔹 _ ϕ).func i) =ᴮ ((@B_small_witness 𝔹 _ ϕ).func j) := by
    intro i j
    by_cases h : i = j
    · subst h; simp [bv_eq_refl]
    · rw [witness_antichain_index r h]; exact bot_le

  obtain ⟨u, H_w⟩ := mixing_lemma (witness_antichain r) ((@B_small_witness 𝔹 _ ϕ).func) mixing_hyp
  refine ⟨u, le_antisymm ?_ (le_iSup ϕ u)⟩

  rw [B_small_witness_supr]
  apply le_trans (supr_antichain2_contains r)
  apply iSup_le; intro ξ

  have hw_ξ := H_w ξ
  have hprop_ξ : witness_antichain r ξ ≤ ξ.val := witness_antichain_property r ξ
  have hspec_ξ : ϕ ((@B_small_witness 𝔹 _ ϕ).func ξ) = ξ.val := @B_small_witness_spec 𝔹 _ ϕ ξ
  calc witness_antichain r ξ
      ≤ (u =ᴮ (@B_small_witness 𝔹 _ ϕ).func ξ) ⊓ ϕ ((@B_small_witness 𝔹 _ ϕ).func ξ) :=
          le_inf hw_ξ (hspec_ξ ▸ hprop_ξ)
    _ = ((@B_small_witness 𝔹 _ ϕ).func ξ =ᴮ u) ⊓ ϕ ((@B_small_witness 𝔹 _ ϕ).func ξ) := by
          rw [bv_eq_symm]
    _ ≤ ϕ u := h_congr _ _

lemma exists_convert {ϕ : bSet 𝔹 → 𝔹} {Γ : 𝔹} (H : Γ ≤ ⨆ x, ϕ x)
    (H_congr : B_ext ϕ) : ∃ u, Γ ≤ ϕ u := by
  obtain ⟨u, Hu⟩ := maximum_principle ϕ H_congr
  exact ⟨u, Hu ▸ H⟩

lemma maximum_principle_verbose {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {b : 𝔹}
    (h_eq_top : (⨆ (x : bSet 𝔹), ϕ x) = b) : ∃ u, ϕ u = b := by
  obtain ⟨w, h⟩ := maximum_principle ϕ h_congr
  exact ⟨w, h.symm ▸ h_eq_top⟩

lemma weaken_ex_scope {α : Type*} (A : α → bSet 𝔹) (ϕ : bSet 𝔹 → 𝔹) :
    (⨆ (a : α), ϕ (A a)) ≤ (⨆ (x : bSet 𝔹), ϕ x) :=
  iSup_le fun a => le_iSup_of_le (A a) le_rfl

lemma maximum_principle_bounded_top {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {α : Type*} {A : α → bSet 𝔹}
    (h_eq_top : (⨆ (a : α), ϕ (A a)) = ⊤) : ∃ u, ϕ u = ⊤ := by
  apply @maximum_principle_verbose 𝔹 _ ϕ h_congr
  have h := weaken_ex_scope A ϕ
  apply le_antisymm le_top
  rw [← h_eq_top]
  exact h

lemma AE_convert {α : Type*} (A : α → bSet 𝔹)
    (B : α → 𝔹) (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹) (h_congr : ∀ z, B_ext (fun x => ϕ z x)) :
    ∀ i : α, ∃ y : bSet 𝔹, (⨅ (j : α), (B j ⟹ ⨆ (z : bSet 𝔹), ϕ (A j) z)) ≤
      (B i ⟹ ϕ (A i) y) := by
  intro i
  obtain ⟨u', H'⟩ := maximum_principle (fun y => ϕ (A i) y) (h_congr (A i))
  exact ⟨u', le_trans (iInf_le (fun j => (B j ⟹ ⨆ (z : bSet 𝔹), ϕ (A j) z)) i)
    (@imp_le_of_right_le 𝔹 _ _ _ _ (le_of_eq H'))⟩

lemma AE_convert' (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹) (h_congr : ∀ z, B_ext (fun x => ϕ z x))
    (x : bSet 𝔹) :
    ∀ v : bSet 𝔹, ∃ w : bSet 𝔹, ∀ {Γ : 𝔹},
      (Γ ≤ ⨅ z, z ∈ᴮ x ⟹ ⨆ w, ϕ z w) → Γ ≤ v ∈ᴮ x → Γ ≤ ϕ v w := by
  intro v
  obtain ⟨u, Hu⟩ := maximum_principle (fun y => ϕ v y) (h_congr v)
  exact ⟨u, fun H_AE H_mem => by
    rw [← Hu]
    exact le_trans (le_inf (le_trans H_AE (iInf_le _ v)) H_mem) bv_imp_elim⟩

section mixing_corollaries

variable (X u₁ u₂ : bSet 𝔹) (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (h_partition : a₁ ⊔ a₂ = ⊤)

include h_partition in
lemma two_term_mixture_mem_top (h₁ : u₁ ∈ᴮ X = ⊤) (h₂ : u₂ ∈ᴮ X = ⊤) :
    two_term_mixture a₁ a₂ h_anti u₁ u₂ ∈ᴮ X = ⊤ := by
  apply top_unique
  set U := two_term_mixture a₁ a₂ h_anti u₁ u₂
  have mixing := mixing_lemma_two_term a₁ a₂ h_anti u₁ u₂

  calc ⊤ = a₁ ⊔ a₂ := by rw [h_partition]
    _ ≤ (U =ᴮ u₁) ⊔ (U =ᴮ u₂) := sup_le_sup mixing.1 mixing.2
    _ ≤ U ∈ᴮ X := bv_or_elim
        (by calc U =ᴮ u₁ = u₁ =ᴮ U := bv_eq_symm
              _ ≤ u₁ =ᴮ U ⊓ u₁ ∈ᴮ X := le_inf le_rfl (h₁ ▸ le_top)
              _ ≤ U ∈ᴮ X := subst_congr_mem_left)
        (by calc U =ᴮ u₂ = u₂ =ᴮ U := bv_eq_symm
              _ ≤ u₂ =ᴮ U ⊓ u₂ ∈ᴮ X := le_inf le_rfl (h₂ ▸ le_top)
              _ ≤ U ∈ᴮ X := subst_congr_mem_left)

include h_partition in
lemma two_term_mixture_subset_top (H : a₁ = u₂ ⊆ᴮ u₁) :
    ⊤ ≤ u₂ ⊆ᴮ (two_term_mixture a₁ a₂ h_anti u₁ u₂) := by
  set U := two_term_mixture a₁ a₂ h_anti u₁ u₂
  have mixing := mixing_lemma_two_term a₁ a₂ h_anti u₁ u₂
  have h_eq₁ : a₁ ≤ u₁ =ᴮ U := mixing.1.trans (le_of_eq bv_eq_symm)
  have h_eq₂ : a₂ ≤ u₂ =ᴮ U := mixing.2.trans (le_of_eq bv_eq_symm)
  rw [subset_unfold', le_iInf_iff]
  intro w
  rw [← deduction, top_inf_eq]

  have h_mem_u₂_le_u₁ : a₁ ⊓ w ∈ᴮ u₂ ≤ w ∈ᴮ u₁ := by
    have hsub : (u₂ ⊆ᴮ u₁) ⊓ w ∈ᴮ u₂ ≤ w ∈ᴮ u₁ := by
      rw [subset_unfold']
      exact le_trans (le_inf (inf_le_left.trans (iInf_le _ w)) inf_le_right) bv_imp_elim
    rw [H]; exact hsub

  calc w ∈ᴮ u₂
      = (a₁ ⊔ a₂) ⊓ w ∈ᴮ u₂ := by rw [h_partition, top_inf_eq]
    _ = a₁ ⊓ w ∈ᴮ u₂ ⊔ a₂ ⊓ w ∈ᴮ u₂ := inf_sup_right a₁ a₂ _
    _ ≤ w ∈ᴮ U :=
        sup_le

          (le_trans (le_inf (inf_le_left.trans h_eq₁) h_mem_u₂_le_u₁) subst_congr_mem_right)

          (le_trans (le_inf (inf_le_left.trans h_eq₂) inf_le_right) subst_congr_mem_right)

end mixing_corollaries

lemma core_aux_lemma (ϕ : bSet 𝔹 → 𝔹) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y)
    (h_definite : (⨆ (w : bSet 𝔹), ϕ w) = ⊤) (v : bSet 𝔹) :
    ∃ u : bSet 𝔹, ϕ u = ⊤ ∧ ϕ v = u =ᴮ v := by
  obtain ⟨w, H_w⟩ := maximum_principle ϕ h_congr
  have H_w_eq : ϕ w = ⊤ := by rw [← H_w, h_definite]
  set b := ϕ v with hb
  have h_inf : b ⊓ bᶜ = ⊥ := inf_compl_eq_bot
  set U := two_term_mixture b bᶜ h_inf v w with hU
  have mixing := mixing_lemma_two_term b bᶜ h_inf v w

  have hm1 : b ≤ U =ᴮ v := mixing.1
  have hm2 : bᶜ ≤ U =ᴮ w := mixing.2
  have h_U_eq_v : U =ᴮ v = v =ᴮ U := bv_eq_symm
  have h_U_eq_w : U =ᴮ w = w =ᴮ U := bv_eq_symm
  have h_phi_U : ϕ U = ⊤ := by
    apply top_unique; rw [← sup_compl_eq_top]; apply sup_le
    · exact (le_inf (hm1.trans (le_of_eq h_U_eq_v)) le_rfl).trans (h_congr v U)
    · exact (le_inf (hm2.trans (le_of_eq h_U_eq_w)) (H_w_eq ▸ le_top)).trans (h_congr w U)
  refine ⟨U, h_phi_U, ?_⟩
  apply le_antisymm
  ·
    exact hm1
  ·
    have := h_congr U v; rw [h_phi_U, inf_top_eq] at this; exact this

lemma core_aux_lemma2 (ϕ ψ : bSet 𝔹 → 𝔹) (h_congrϕ : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y)
    (h_congrψ : ∀ x y, x =ᴮ y ⊓ ψ x ≤ ψ y) (h_sub : ∀ u, ϕ u = ⊤ → ψ u = ⊤)
    (h_definite : (⨆ (w : bSet 𝔹), ϕ w) = ⊤) :
    (⨅ (x : bSet 𝔹), ϕ x ⟹ ψ x) = ⊤ := by
  apply top_unique; apply le_iInf; intro x
  rw [← deduction, top_inf_eq]
  obtain ⟨u, h₁, h₂⟩ := core_aux_lemma ϕ h_congrϕ h_definite x
  have hψu : ψ u = ⊤ := h_sub u h₁

  rw [h₂]
  calc u =ᴮ x
      = u =ᴮ x ⊓ ψ u := by rw [hψu, inf_top_eq]
    _ ≤ ψ x := h_congrψ u x

section smallness'
variable {α : Type u} (ϕ' : bSet 𝔹 → α)

@[reducible, simp] noncomputable def fiber_lift' (b : ϕ' '' Set.univ) :
    { x : bSet 𝔹 // ϕ' x = b.val } :=
  Classical.indefiniteDescription (fun a : bSet 𝔹 => ϕ' a = b.val) (by
    obtain ⟨x, _, hx⟩ := b.2; exact ⟨x, hx⟩)

end smallness'

section cores

@[reducible] def pullback_eq_rel {α β : Type*} (f : α → β) (E : β → β → Prop) :
    α → α → Prop :=
  fun a₁ a₂ => E (f a₁) (f a₂)

def core {α : Type u} (u : bSet 𝔹) (S : α → bSet 𝔹) : Prop :=
  (∀ x : α, S x ∈ᴮ u = ⊤) ∧
  (∀ y : bSet 𝔹, y ∈ᴮ u = ⊤ → ∃! x_y : α, y =ᴮ S x_y = ⊤)

noncomputable def core_witness {α : Type u} {u : bSet 𝔹} {S : α → bSet 𝔹}
    (h_core : core u S) (x : bSet 𝔹) (h_X : x ∈ᴮ u = ⊤) :
    Σ' (x_y : α), x =ᴮ S x_y = ⊤ := by
  have h := h_core.2 x h_X
  exact ⟨h.choose, h.choose_spec.1⟩

lemma core_inj {α : Type u} (u : bSet 𝔹) (S : α → bSet 𝔹) (h_core : core u S) :
    Function.Injective S := by
  intro x y H
  have h_left₁ := h_core.1 x
  have he := h_core.2 (S x) h_left₁
  obtain ⟨w1, H1, H2⟩ := he
  have hSxSy : S x =ᴮ S y = ⊤ := by
    have : S y = S x := H.symm; rw [this]; exact bv_eq_refl (S x)
  have Q2 : y = w1 := H2 y hSxSy
  have Q3 : x = w1 := H2 x (bv_eq_refl (S x))
  exact Q3.trans Q2.symm

lemma core_inj' {α : Type u} {u : bSet 𝔹} {S : α → bSet 𝔹} (h_core : core u S) :
    ∀ a b : α, S a =ᴮ S b = ⊤ → a = b := by
  intro x y H
  have h_left₁ := h_core.1 x
  obtain ⟨w1, H1, H2⟩ := h_core.2 (S x) h_left₁
  have Q2 : y = w1 := H2 y H
  have Q3 : x = w1 := H2 x (bv_eq_refl (S x))
  exact Q3.trans Q2.symm

def core.mk_ϕ (u : bSet 𝔹) : bSet 𝔹 → (u.type → 𝔹) :=
  fun x => fun a => u.bval a ⊓ x =ᴮ u.func a

lemma core.mk_ϕ_inj (u : bSet 𝔹) (x y : bSet 𝔹)
    (h₁ : x ∈ᴮ u = ⊤) (h₂ : y ∈ᴮ u = ⊤) (H : core.mk_ϕ u x = core.mk_ϕ u y) :
    x =ᴮ y = ⊤ := by

  have H' := congr_fun H
  simp only [core.mk_ϕ] at H'

  apply top_unique

  rw [← h₁, mem_unfold]
  apply iSup_le; intro a

  calc u.bval a ⊓ x =ᴮ u.func a
      ≤ x =ᴮ u.func a ⊓ u.func a =ᴮ y := by
          apply le_inf inf_le_right

          calc u.bval a ⊓ x =ᴮ u.func a
              = u.bval a ⊓ y =ᴮ u.func a := H' a
            _ ≤ y =ᴮ u.func a := inf_le_right
            _ = u.func a =ᴮ y := bv_eq_symm
    _ ≤ x =ᴮ y := bv_eq_trans

noncomputable def core.S' (u : bSet 𝔹) : (core.mk_ϕ u '' Set.univ) → bSet 𝔹 :=
  fun x => (fiber_lift' (core.mk_ϕ u) x).val

def core.α_S'' (u : bSet 𝔹) : Type u :=
  { i : core.mk_ϕ u '' Set.univ // core.S' u i ∈ᴮ u = ⊤ }

noncomputable def core.S'' (u : bSet 𝔹) : core.α_S'' u → bSet 𝔹 :=
  fun x => core.S' u x.val

lemma core.S'_spec (u : bSet 𝔹) (x : core.mk_ϕ u '' Set.univ) :
    core.mk_ϕ u (core.S' u x) = x.val :=
  (fiber_lift' (core.mk_ϕ u) x).2

def core.bv_eq_top : bSet 𝔹 → bSet 𝔹 → Prop :=
  fun x₁ x₂ => x₁ =ᴮ x₂ = ⊤

def core.bv_eq_top_setoid : Setoid (bSet 𝔹) where
  r := core.bv_eq_top
  iseqv := {
    refl := fun _ => bv_eq_refl _
    symm := fun h => by simp only [core.bv_eq_top] at *; rwa [bv_eq_symm]
    trans := fun h1 h2 => by
      simp only [core.bv_eq_top] at *
      exact top_unique (le_trans (by rw [h1, h2]; simp) bv_eq_trans)
  }

instance core.S''_setoid (u : bSet 𝔹) : Setoid (core.α_S'' u) where
  r := pullback_eq_rel (core.S'' u) core.bv_eq_top
  iseqv := {
    refl := fun x => bv_eq_refl _
    symm := fun h => by simp only [pullback_eq_rel, core.bv_eq_top] at *; rwa [bv_eq_symm]
    trans := fun h1 h2 => by
      simp only [pullback_eq_rel, core.bv_eq_top] at *
      exact top_unique (le_trans (by rw [h1, h2]; simp) bv_eq_trans)
  }

noncomputable def core.mk_aux (u : bSet 𝔹) :
    (Quotient (@core.S''_setoid 𝔹 _ u)) → bSet 𝔹 :=
  fun x => (core.S'' u) (Quotient.out x)

@[reducible] private def image_mk {α β : Type*} {f : α → β} (a : α) : f '' Set.univ :=
  ⟨f a, Set.mem_image_of_mem _ (Set.mem_univ _)⟩

lemma core.mk (u : bSet 𝔹) : ∃ α : Type u, ∃ S : α → bSet 𝔹, core u S := by

  refine ⟨Quotient (@core.S''_setoid 𝔹 _ u), core.mk_aux u, ?_, ?_⟩
  ·
    intro x

    exact (Quotient.out x).property
  ·
    intro y H_y

    let y' := core.S' u (image_mk y)

    have H_y' : core.mk_ϕ u y = core.mk_ϕ u y' := (core.S'_spec u (image_mk y)).symm

    have H_y'2 : y' ∈ᴮ u = ⊤ := by
      simp only [mem_unfold]
      apply top_unique
      rw [← H_y, mem_unfold]
      apply iSup_le; intro a

      have := congr_fun H_y' a
      simp only [core.mk_ϕ] at this
      rw [this]; exact le_iSup (fun i => u.bval i ⊓ y' =ᴮ u.func i) a

    let y_q : core.α_S'' u := ⟨image_mk y, H_y'2⟩

    let y'' := core.mk_aux u ⟦y_q⟧

    have H_y'' : y'' =ᴮ y' = ⊤ := by

      exact Quotient.mk_out y_q

    have H₃ : y =ᴮ y' = ⊤ := core.mk_ϕ_inj u y y' H_y H_y'2 H_y'

    have H₁ : y =ᴮ y'' = ⊤ := by
      apply top_unique
      calc (⊤ : 𝔹) ≤ y =ᴮ y' ⊓ y' =ᴮ y'' := by
              rw [H₃, show y' =ᴮ y'' = ⊤ from by rw [bv_eq_symm]; exact H_y'']; simp
        _ ≤ y =ᴮ y'' := bv_eq_trans

    refine ⟨⟦y_q⟧, H₁, ?_⟩

    intro i H_y'''

    suffices h : core.mk_aux u i =ᴮ y' = ⊤ by

      have hiy'' : core.mk_aux u i =ᴮ y'' = ⊤ := by
        apply top_unique
        calc (⊤ : 𝔹) ≤ core.mk_aux u i =ᴮ y' ⊓ y' =ᴮ y'' := by
                rw [h, show y' =ᴮ y'' = ⊤ from by rw [bv_eq_symm]; exact H_y'']; simp
          _ ≤ core.mk_aux u i =ᴮ y'' := bv_eq_trans

      have hrel : (core.S''_setoid u).r
          (@Quotient.out _ (core.S''_setoid u) i)
          (@Quotient.out _ (core.S''_setoid u) ⟦y_q⟧) := by

        show core.bv_eq_top (core.S'' u _) (core.S'' u _)
        simp only [core.bv_eq_top, core.S'', core.mk_aux] at hiy'' ⊢
        exact hiy''
      have heq : ⟦(@Quotient.out _ (core.S''_setoid u) i)⟧ =
                 ⟦(@Quotient.out _ (core.S''_setoid u) ⟦y_q⟧)⟧ :=
        Quotient.sound hrel
      rw [Quotient.out_eq, Quotient.out_eq] at heq
      exact heq

    apply top_unique
    rw [show (⊤ : 𝔹) = core.mk_aux u i =ᴮ y ⊓ y =ᴮ y' by
      rw [show core.mk_aux u i =ᴮ y = ⊤ by rw [bv_eq_symm]; exact H_y''', H₃]; simp]
    exact bv_eq_trans

def bSet_of_core_set {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S)
    (C : Set α) : bSet 𝔹 :=
  ⟨C, fun x => S x, fun _ => ⊤⟩

def bSet_of_core {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) : bSet 𝔹 :=
  bSet_of_core_set h Set.univ

@[simp] lemma of_core_type {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S}
    {C : Set α} : (bSet_of_core_set h C).type = C := rfl

@[simp] lemma of_core_bval {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S}
    {C : Set α} {i : C} : (bSet_of_core_set h C).bval i = ⊤ := rfl

lemma of_core_mem {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S}
    {C : Set α} {i : C} : ⊤ ≤ (bSet_of_core_set h C).func i ∈ᴮ u :=
  top_le_iff.mpr (h.1 _)

def subset' {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) : α → α → Prop :=
  fun a₁ a₂ => S a₁ ⊆ᴮ S a₂ = ⊤

def subset'_partial_order {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) :
    PartialOrder α where
  le := subset' h
  le_refl := by intro a; simp [subset', bv_eq_refl]
  le_trans := by
    intro a b c
    simp only [subset']
    intro h₁ h₂
    rw [eq_top_iff] at h₁ h₂ ⊢
    exact subset_trans' h₁ h₂
  le_antisymm := by
    intro a b H₁ H₂
    apply core_inj' h
    simp only [subset'] at H₁ H₂
    rw [eq_top_iff] at H₁ H₂ ⊢
    exact subset_ext H₁ H₂

lemma subset'_trans {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} {a b c : α}
    (hab : subset' h a b) (hbc : subset' h b c) : subset' h a c := by
  simp only [subset'] at *
  rw [eq_top_iff] at *
  exact subset_trans' hab hbc

lemma subset'_unfold {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S} {a₁ a₂ : α} :
    subset' h a₁ a₂ ↔ S a₁ ⊆ᴮ S a₂ = ⊤ := Iff.rfl

@[reducible] def exists_mem (x : bSet 𝔹) : 𝔹 := ⨆ (y : bSet 𝔹), y ∈ᴮ x

@[reducible] def not_empty (x : bSet 𝔹) : 𝔹 := (x =ᴮ ∅)ᶜ

lemma exists_mem_of_nonempty (u : bSet 𝔹) {Γ : 𝔹} (H : Γ ≤ (u =ᴮ ∅)ᶜ) : Γ ≤ ⨆ x, x ∈ᴮ u := by
  apply le_trans H
  simp [eq_empty]
  intro x
  apply bv_use (u.func x)
  apply mem_mk'

lemma nonempty_of_exists_mem (u : bSet 𝔹) {Γ : 𝔹} (H : Γ ≤ (⨆ x, x ∈ᴮ u)) : Γ ≤ (u =ᴮ ∅)ᶜ := by
  apply le_trans H
  simp [eq_empty]
  intro x
  rw [mem_unfold]
  apply bv_Or_elim
  intro i
  apply bv_use i
  apply inf_le_left

lemma nonempty_iff_exists_mem {u : bSet 𝔹} {Γ : 𝔹} : Γ ≤ (u =ᴮ ∅)ᶜ ↔ Γ ≤ ⨆ x, x ∈ᴮ u :=
  ⟨fun H => exists_mem_of_nonempty _ H, fun H => nonempty_of_exists_mem _ H⟩

lemma empty_iff_forall_not_mem {u : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ u =ᴮ ∅ ↔ Γ ≤ ⨅ x, (x ∈ᴮ u)ᶜ := by

  have h_eq : (u =ᴮ ∅ : 𝔹) = ⨅ x, (x ∈ᴮ u)ᶜ := by
    have h_compl : (u =ᴮ ∅ : 𝔹)ᶜ = ⨆ x, x ∈ᴮ u :=
      le_antisymm (nonempty_iff_exists_mem.mp le_rfl)
                  (nonempty_iff_exists_mem.mpr le_rfl)
    calc (u =ᴮ ∅ : 𝔹) = ((u =ᴮ ∅ : 𝔹)ᶜ)ᶜ := compl_compl _ |>.symm
      _ = (⨆ x, x ∈ᴮ u)ᶜ := by rw [h_compl]
      _ = ⨅ x, (x ∈ᴮ u)ᶜ := compl_iSup
  rw [h_eq]

lemma core_aux_lemma3 (u : bSet 𝔹) (h_nonempty : (u =ᴮ ∅)ᶜ = ⊤) {α : Type u} (S : α → bSet 𝔹)
    (h_core : core u S) : ∀ x, ∃ y ∈ S '' Set.univ, x =ᴮ y = x ∈ᴮ u := by
  intro x

  have h_congr : ∀ a b : bSet 𝔹, a =ᴮ b ⊓ a ∈ᴮ u ≤ b ∈ᴮ u :=
    fun a b => subst_congr_mem_left
  have h_definite : (⨆ (w : bSet 𝔹), w ∈ᴮ u) = ⊤ :=
    top_unique (le_trans (h_nonempty ▸ le_rfl) (exists_mem_of_nonempty u le_rfl))
  obtain ⟨y, h₁, h₂⟩ := core_aux_lemma (fun z => z ∈ᴮ u) h_congr h_definite x

  obtain ⟨y', H_y'_eq, -⟩ := h_core.2 y h₁

  refine ⟨S y', Set.mem_image_of_mem _ (Set.mem_univ _), ?_⟩

  have h_rw : x =ᴮ S y' = x =ᴮ y := by
    apply bv_rw H_y'_eq (fun z => x =ᴮ z)
    intro a b
    rw [inf_comm]; exact bv_eq_trans
  rw [h_rw, bv_eq_symm, h₂]

lemma core_mem_of_mem_image {u y : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h_core : core u S) :
    y ∈ S '' Set.univ → y ∈ᴮ u = ⊤ := by
  rintro ⟨a, -, rfl⟩
  exact h_core.1 a

end cores

section check_names

@[simp] def check : PSet.{u} → bSet 𝔹
  | ⟨α, A⟩ => ⟨α, fun a => check (A a), fun _ => ⊤⟩

scoped postfix:9999 "̌" => check

@[simp] lemma check_type {α : Type u} {A : α → PSet} :
    (check (PSet.mk α A) : bSet 𝔹).type = α := rfl

@[simp] lemma check_type_iInf {α : Type u} {A : α → PSet} {s : α → 𝔹} :
    (⨅ (a : (check (PSet.mk α A) : bSet 𝔹).type), s a) = (⨅ (a : α), s a : 𝔹) :=
  rfl

@[simp] lemma check_type_iSup {α : Type u} {A : α → PSet} {s : α → 𝔹} :
    (⨆ (a : (check (PSet.mk α A) : bSet 𝔹).type), s a) = (⨆ (a : α), s a : 𝔹) :=
  rfl

@[simp] lemma check_type' {x : PSet.{u}} :
    (check x : bSet 𝔹).type = x.Type := by
  cases x; simp [check]

@[simp] lemma check_type'_set {x : PSet} :
    Set (check x : bSet 𝔹).type = Set (x.Type) := by
  cases x; simp [check]

@[reducible, simp] def check_cast {x : PSet} (i : (check x : bSet 𝔹).type) : x.Type :=
  cast check_type' i

@[reducible, simp] def check_cast_symm {x : PSet} (i : x.Type) : (check x : bSet 𝔹).type :=
  cast check_type'.symm i

@[reducible, simp] def check_cast_set {x : PSet} (S : Set (check x : bSet 𝔹).type) :
    Set (x.Type) :=
  cast check_type'_set S

lemma check_func {x : PSet} {i} :
    (check x : bSet 𝔹).func i = check (x.Func (check_cast i)) := by
  cases x; rfl

lemma check_unfold {x : PSet.{u}} :
    (check x : bSet 𝔹) = bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by
  cases x; rfl

@[simp] lemma check_bval_top (x : PSet) {i} : (check x : bSet 𝔹).bval i = ⊤ := by
  cases x; rfl

@[simp] lemma check_bval_mk {α : Type u} {A : α → PSet} {i} :
    (check (PSet.mk α A) : bSet 𝔹).bval i = (⊤ : 𝔹) := rfl

@[simp] lemma check_empty_eq_empty : check (∅ : PSet) = (∅ : bSet 𝔹) := by

  show bSet.mk PEmpty (fun i => check (PEmpty.elim i)) (fun _ => ⊤) =
       bSet.mk PEmpty PEmpty.elim PEmpty.elim
  congr 1 <;> funext i <;> exact i.elim

@[simp] lemma mem_top_of_bval_top {u : bSet 𝔹} {i : u.type} (H_top : u.bval i = ⊤) :
    u.func i ∈ᴮ u = ⊤ := by
  apply top_unique; rw [← H_top]; apply mem_mk'

@[simp] lemma check_mem_top {x : PSet} {i : (check x : bSet 𝔹).type} :
    (check x : bSet 𝔹).func i ∈ᴮ check x = ⊤ :=
  mem_top_of_bval_top (check_bval_top x)

@[simp] lemma mem_check_of_mem {x : PSet} {i : x.Type} {Γ : 𝔹} :
    Γ ≤ check (x.Func i) ∈ᴮ check x := by
  rw [mem_unfold]
  apply bv_use (check_cast_symm i)
  simp only [true_and, le_inf_iff, le_top, check_cast_symm, check_bval_top]
  convert bv_refl
  cases x; rfl

lemma check_bv_eq_top_of_equiv {x y : PSet} (h : PSet.Equiv x y) :
    (check x : bSet 𝔹) =ᴮ check y = (⊤ : 𝔹) := by
  induction x generalizing y with
  | mk α A ih =>
  cases y with
  | mk β B =>
  rw [check_unfold, check_unfold, bv_eq]
  apply top_unique
  apply le_inf
  · apply le_iInf; intro a
    rw [← deduction, top_inf_eq]
    obtain ⟨b, hb⟩ := h.1 a
    exact le_iSup_of_le b (le_inf le_top (le_of_eq (ih a hb).symm))
  · apply le_iInf; intro b
    rw [← deduction, top_inf_eq]
    obtain ⟨a, ha⟩ := h.2 b
    exact le_iSup_of_le a (le_inf le_top (le_of_eq (ih a ha).symm))

lemma check_bv_eq {x y : PSet} {Γ : 𝔹} (H : PSet.Equiv x y) :
    (Γ : 𝔹) ≤ check x =ᴮ check y := by
  exact le_trans le_top (by rw [top_le_iff]; exact check_bv_eq_top_of_equiv H)

lemma check_eq {x y : PSet} {Γ : 𝔹} (H : PSet.Equiv x y) :
    (Γ : 𝔹) ≤ check x =ᴮ check y :=
  check_bv_eq H

lemma check_bv_eq_bot_of_not_equiv {x y : PSet} (H : ¬ PSet.Equiv x y) :
    (check x : bSet 𝔹) =ᴮ check y = (⊥ : 𝔹) := by
  induction x generalizing y with
  | mk α A ih =>
  cases y with
  | mk β B =>
  rw [check_unfold, check_unfold, bv_eq]
  apply bot_unique
  rcases PSet.not_equiv H with ⟨a, ha⟩ | ⟨b, hb⟩
  ·
    apply inf_le_left.trans; apply iInf_le_of_le a
    simp only [imp, compl_top, bot_sup_eq]
    apply iSup_le; intro b; simp only [top_inf_eq]
    exact le_of_eq (@ih a (B b) (ha b))
  ·
    apply inf_le_right.trans; apply iInf_le_of_le b
    simp only [imp, compl_top, bot_sup_eq]
    apply iSup_le; intro a; simp only [top_inf_eq]
    exact le_of_eq (@ih a (B b) (hb a))

lemma check_bv_eq_dichotomy (x y : PSet) :
    (check x : bSet 𝔹) =ᴮ check y = (⊤ : 𝔹) ∨ (check x : bSet 𝔹) =ᴮ check y = (⊥ : 𝔹) := by
  classical
  by_cases h : PSet.Equiv x y
  · left; exact check_bv_eq_top_of_equiv h
  · right; exact check_bv_eq_bot_of_not_equiv h

lemma check_bv_eq_iff {x y : PSet} :
    PSet.Equiv x y ↔ (check x : bSet 𝔹) =ᴮ check y = (⊤ : 𝔹) := by
  constructor
  · exact check_bv_eq_top_of_equiv
  · intro h
    classical
    by_contra hne
    have hbot : (check x : bSet 𝔹) =ᴮ check y = (⊥ : 𝔹) := check_bv_eq_bot_of_not_equiv hne
    rw [hbot] at h; exact absurd h (by simp)

lemma not_check_bv_eq_iff {x y : PSet} :
    ¬ PSet.Equiv x y ↔ (check x : bSet 𝔹) =ᴮ check y = (⊥ : 𝔹) :=
  ⟨check_bv_eq_bot_of_not_equiv,
   fun (H : (check x : bSet 𝔹) =ᴮ check y = (⊥ : 𝔹)) hE =>
     by have := check_bv_eq_top_of_equiv (𝔹 := 𝔹) hE; rw [this] at H; simp at H⟩

lemma check_not_eq {x y : PSet.{u}} (H : ¬ PSet.Equiv x y) {Γ : 𝔹} :
    Γ ≤ ((check x : bSet 𝔹) =ᴮ check y)ᶜ := by
  have : (check x : bSet 𝔹) =ᴮ check y = (⊥ : 𝔹) := check_bv_eq_bot_of_not_equiv H
  rw [this]; simp

lemma check_bv_eq_nonzero_iff_eq_top {x y : PSet} :
    (⊥ : 𝔹) < check x =ᴮ check y ↔ (check x : bSet 𝔹) =ᴮ check y = (⊤ : 𝔹) :=
  ⟨fun H => by
    rcases @check_bv_eq_dichotomy 𝔹 _ x y with h | h
    · exact h
    · rw [h] at H; exact absurd H (lt_irrefl _),
   fun H => by rw [H]; exact nontrivial_bot_lt_top⟩

lemma check_eq_reflect {x y : PSet} {Γ : 𝔹} (H_lt : ⊥ < Γ)
    (H_mem : Γ ≤ check x =ᴮ check y) : PSet.Equiv x y :=
  check_bv_eq_iff.mpr (check_bv_eq_nonzero_iff_eq_top.mp (lt_of_lt_of_le H_lt H_mem))

@[simp] lemma check_insert (a b : PSet) :
    check (PSet.insert a b) = (bSet.insert1 (check a) (check b) : bSet 𝔹) := by
  cases a with | mk α A => cases b with | mk β B =>

  simp only [PSet.insert, bSet.insert1, bSet.insert, check]
  congr 1
  · funext o; cases o <;> rfl
  · funext o; cases o <;> rfl

lemma mem_check_witness {y x : PSet.{u}} {Γ : 𝔹} (h_nonzero : ⊥ < Γ)
    (H : Γ ≤ check y ∈ᴮ check x) : ∃ i : x.Type, Γ ≤ check y =ᴮ check (x.Func i) := by
  rw [mem_unfold] at H
  simp only [check_bval_top, top_inf_eq, check_func] at H

  obtain ⟨i, hi⟩ := supr_eq_Gamma_max h_nonzero H (h_bounded := fun a H_neg => by
    rcases @check_bv_eq_dichotomy 𝔹 _ y (x.Func (check_cast a)) with h | h
    · exact absurd (h ▸ le_top) H_neg
    · exact h)
  exact ⟨check_cast i, hi⟩

lemma check_mem_iff {x y : PSet} :
    x ∈ y ↔ (check x : bSet 𝔹) ∈ᴮ check y = (⊤ : 𝔹) := by
  constructor
  · intro H
    cases y
    rename_i β B
    rw [← top_le_iff]
    simp only [PSet.mem_iff] at H
    obtain ⟨b, hb⟩ := H
    apply bv_use b
    exact le_inf (by simp) (check_bv_eq hb)
  · intro H
    cases y
    rename_i β B
    rw [← top_le_iff] at H
    obtain ⟨i, hi⟩ := mem_check_witness (by simp) H
    have hi' : (check x : bSet 𝔹) =ᴮ check (B i) = ⊤ := by rwa [top_le_iff] at hi
    exact ⟨i, check_bv_eq_iff.mpr hi'⟩

lemma not_check_mem_iff {x y : PSet} :
    x ∉ y ↔ (check x : bSet 𝔹) ∈ᴮ check y = (⊥ : 𝔹) := by
  constructor
  · intro H

    have H' : ∀ b : y.Type, ¬ PSet.Equiv x (y.Func b) := fun b hE => H ⟨b, hE⟩
    rw [← le_bot_iff, mem_unfold, iSup_le_iff]
    intro i
    simp only [check_bval_top, check_func, top_inf_eq]
    exact le_of_eq (check_bv_eq_bot_of_not_equiv (H' (check_cast i)))
  · intro H h_mem
    have htop := @check_mem_iff 𝔹 _ x y |>.mp h_mem
    rw [H] at htop
    exact absurd htop (by simp)

lemma check_not_mem {x y : PSet} : x ∉ y → ∀ {Γ : 𝔹}, Γ ≤ check x ∈ᴮ check y → Γ ≤ ⊥ := by
  intro H
  have H' : (check x : bSet 𝔹) ∈ᴮ check y = ⊥ := not_check_mem_iff.mp H
  intros Γ HΓ
  rwa [← H']

lemma check_mem_dichotomy (x y : PSet) :
    (check x : bSet 𝔹) ∈ᴮ check y = (⊤ : 𝔹) ∨ (check x : bSet 𝔹) ∈ᴮ check y = (⊥ : 𝔹) := by
  classical
  by_cases h : x ∈ y
  · left; exact check_mem_iff.mp h
  · right; exact not_check_mem_iff.mp h

lemma check_mem_nonzero_iff_eq_top {x y : PSet} :
    (⊥ : 𝔹) < (check x : bSet 𝔹) ∈ᴮ check y ↔ (check x : bSet 𝔹) ∈ᴮ check y = (⊤ : 𝔹) := by
  constructor
  · intro H
    rcases @check_mem_dichotomy 𝔹 _ x y with h | h
    · exact h
    · rw [h] at H; exact absurd H (lt_irrefl _)
  · intro H; simp [H]

lemma check_mem_reflect {x y : PSet} {Γ : 𝔹} (H_lt : ⊥ < Γ)
    (H_mem : Γ ≤ (check x : bSet 𝔹) ∈ᴮ check y) : x ∈ y :=
  check_mem_iff.mpr (check_mem_nonzero_iff_eq_top.mp (lt_of_lt_of_le H_lt H_mem))

@[simp] lemma check_mem {x y : PSet} {Γ : 𝔹} (h_mem : x ∈ y) :
    (Γ : 𝔹) ≤ check x ∈ᴮ check y := by
  rw [mem_unfold]
  cases y
  rename_i β B
  simp only [PSet.mem_iff] at h_mem
  obtain ⟨w, hw⟩ := h_mem
  apply bv_use w
  apply le_inf
  · simp
  · exact check_bv_eq hw

@[simp] lemma check_subset_of_subset {x y : PSet} (h_subset : x ⊆ y) :
    (⊤ : 𝔹) ≤ check x ⊆ᴮ check y := by
  rw [subset_unfold]
  apply le_iInf; intro j
  simp only [check_bval_top, top_imp, check_func]

  obtain ⟨b, hb⟩ := h_subset (check_cast j)
  exact check_mem ⟨b, hb⟩

lemma check_subset {x y : PSet} {Γ : 𝔹} (h_subset : x ⊆ y) :
    Γ ≤ check x ⊆ᴮ check y :=
  le_trans le_top (check_subset_of_subset h_subset)

lemma check_not_subset {x y : PSet} (H : ¬ x ⊆ y) {Γ} :
    (Γ : 𝔹) ≤ (check x ⊆ᴮ check y)ᶜ := by

  have H' : ∃ a : x.Type, x.Func a ∉ y := by
    by_contra h
    push Not at h
    exact H (fun a => h a)
  obtain ⟨a, h_notmem⟩ := H'

  have h_bot : (check (x.Func a) : bSet 𝔹) ∈ᴮ check y = ⊥ :=
    not_check_mem_iff.mp h_notmem

  have h_sub_bot : check x ⊆ᴮ check y = (⊥ : 𝔹) := by
    rw [← le_bot_iff, subset_unfold]
    apply le_trans (iInf_le _ (check_cast_symm a))
    simp only [check_bval_top, top_imp, check_func, check_cast, check_cast_symm,
               cast_cast, cast_eq]
    rw [h_bot]
  rw [h_sub_bot, compl_bot]
  exact le_top

@[simp] lemma check_exists_mem {y : PSet} (H_exists_mem : ∃ z, z ∈ y) {Γ : 𝔹} :
    Γ ≤ exists_mem (check y) := by
  obtain ⟨z, hz⟩ := H_exists_mem
  apply bv_use (check z)
  simp [check_mem hz]

lemma instantiate_existential_over_check_aux {ϕ : bSet 𝔹 → 𝔹} (H_congr : B_ext ϕ)
    (x : PSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆ y, (y ∈ᴮ check x ⊓ ϕ y)) :
    ∃ i : x.Type, ⊥ < (ϕ (check (x.Func i)) ⊓ Γ) := by

  have h_cong : ∀ a b : bSet 𝔹, a =ᴮ b ⊓ ϕ a ≤ ϕ b := H_congr
  rw [← @bounded_exists _ _ (check x) ϕ h_cong] at H_ex
  simp only [check_bval_top, top_inf_eq, check_func] at H_ex
  obtain ⟨i, hi⟩ := nonzero_inf_of_nonzero_le_supr H_nonzero H_ex
  exact ⟨check_cast i, by rwa [inf_comm]⟩

noncomputable def instantiate_existential_over_check
    {ϕ : bSet 𝔹 → 𝔹} (H_congr : B_ext ϕ) (x : PSet) {Γ}
    (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆ y, (y ∈ᴮ check x ⊓ ϕ y)) : x.Type :=
  Classical.choose (instantiate_existential_over_check_aux H_congr x H_nonzero H_ex)

lemma instantiate_existential_over_check_spec {ϕ : bSet 𝔹 → 𝔹} (H_congr : B_ext ϕ)
    (x : PSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆ y, (y ∈ᴮ check x ⊓ ϕ y)) :
    ⊥ < (ϕ (check (x.Func (instantiate_existential_over_check H_congr x H_nonzero H_ex))) ⊓ Γ) :=
  Classical.choose_spec (instantiate_existential_over_check_aux H_congr x H_nonzero H_ex)

lemma instantiate_existential_over_check_spec₂ (ϕ : bSet 𝔹 → 𝔹) (H_congr : B_ext ϕ)
    (x : PSet) {Γ} (H_nonzero : ⊥ < Γ) (H_ex : Γ ≤ ⨆ y, (y ∈ᴮ check x ⊓ ϕ y)) :
    ⊥ < ϕ (check (x.Func (instantiate_existential_over_check H_congr x H_nonzero H_ex))) :=
  bot_lt_resolve_right H_nonzero (instantiate_existential_over_check_spec H_congr x H_nonzero H_ex)

lemma eq_check_of_mem_check {Γ : 𝔹} (h_nonzero : ⊥ < Γ) {x : PSet.{u}} {y : bSet 𝔹}
    (H_mem : Γ ≤ y ∈ᴮ check x) :
    ∃ (i : x.Type) (Γ' : 𝔹) (_ : ⊥ < Γ') (_ : Γ' ≤ Γ), Γ' ≤ y =ᴮ check (x.Func i) := by
  let ϕ : bSet 𝔹 → 𝔹 := fun z => y =ᴮ z
  have H_congr : B_ext ϕ := B_ext_bv_eq_right (x := y)
  have H_ex : Γ ≤ ⨆ z, z ∈ᴮ check x ⊓ ϕ z := by
    apply bv_use y; exact le_inf H_mem bv_refl
  let i : x.Type := instantiate_existential_over_check H_congr x h_nonzero H_ex
  exact ⟨i, ϕ (check (x.Func i)) ⊓ Γ,
         instantiate_existential_over_check_spec H_congr x h_nonzero H_ex,
         inf_le_right,
         inf_le_left⟩

lemma eq_check_of_mem_check₂ {Γ : 𝔹} (h_nonzero : ⊥ < Γ) (x : PSet.{u}) (y : bSet 𝔹)
    (H_mem : Γ ≤ y ∈ᴮ check x) : ∃ i : x.Type, ⊥ < y =ᴮ check (x.Func i) := by
  obtain ⟨i, Γ', HΓ'₁, HΓ'₂, HΓ'₃⟩ := eq_check_of_mem_check h_nonzero H_mem
  exact ⟨i, lt_of_lt_of_le HΓ'₁ HΓ'₃⟩

end check_names

noncomputable def collect.func
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (u : bSet 𝔹) : u.type → bSet 𝔹 :=
  Classical.choose (Classical.axiomOfChoice
    (AE_convert u.func u.bval ϕ (by intro z; intro xv yv; exact h_congr_right xv yv z)))

noncomputable def collect
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) : bSet 𝔹 :=
  ⟨u.type, collect.func ϕ h_congr_right u, u.bval⟩

lemma collect.func_spec
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) (Γ : 𝔹)
    (H : Γ ≤ ⨅ (j : u.type), u.bval j ⟹ ⨆ (z : bSet 𝔹), ϕ (u.func j) z) :
    Γ ≤ ⨅ (x : u.type), u.bval x ⟹ ϕ (u.func x) (collect.func ϕ h_congr_right u x) := by
  apply le_iInf; intro i
  rw [← deduction]
  have hspec := Classical.choose_spec (Classical.axiomOfChoice
    (AE_convert u.func u.bval ϕ (by intro z; intro xv yv; exact h_congr_right xv yv z)))
  specialize hspec i
  have hΓ_imp : Γ ≤ u.bval i ⟹ ϕ (u.func i) _ := le_trans H hspec
  rwa [← deduction] at hΓ_imp

lemma collect_spec₁
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) {Γ : 𝔹}
    (H_AE : Γ ≤ ⨅ i : u.type, u.bval i ⟹ ⨆ w, ϕ (u.func i) w) :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ u ⟹ ⨆ w, w ∈ᴮ collect ϕ h_congr_right h_congr_left u ⊓ ϕ z w := by
  apply le_iInf; intro z
  rw [← deduction]

  rw [mem_unfold, inf_iSup_eq]
  apply iSup_le; intro i

  apply le_iSup_of_le (collect.func ϕ h_congr_right u i)
  apply le_inf
  ·

    apply @mem_mk'' 𝔹 _ (collect ϕ h_congr_right h_congr_left u) i
    exact inf_le_right.trans inf_le_left
  ·

    have hϕi := poset_yoneda_inv (Γ ⊓ u.bval i) bv_imp_elim
      (le_inf (inf_le_left.trans (collect.func_spec ϕ h_congr_right h_congr_left u Γ H_AE |>.trans
        (iInf_le _ i))) inf_le_right)

    have hΓbval : Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ Γ ⊓ u.bval i :=
      inf_le_inf_left _ inf_le_left
    have hbval : Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ ϕ (u.func i) (collect.func ϕ h_congr_right u i) :=
      hΓbval.trans hϕi

    have heq_sym : Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ u.func i =ᴮ z := by
      calc Γ ⊓ (u.bval i ⊓ z =ᴮ u.func i) ≤ z =ᴮ u.func i := inf_le_right.trans inf_le_right
        _ ≤ u.func i =ᴮ z := le_of_eq bv_eq_symm
    exact le_trans (le_inf heq_sym hbval) (h_congr_left (u.func i) z _)

lemma collect_spec₂
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) {Γ : 𝔹}
    (H_AE : Γ ≤ ⨅ i : u.type, u.bval i ⟹ ⨆ w, ϕ (u.func i) w) :
    Γ ≤ ⨅ (w : bSet 𝔹), w ∈ᴮ collect ϕ h_congr_right h_congr_left u ⟹ ⨆ z, z ∈ᴮ u ⊓ ϕ z w := by
  apply le_iInf; intro w
  rw [← deduction]

  rw [mem_unfold (v := collect ϕ h_congr_right h_congr_left u), inf_iSup_eq]
  apply iSup_le; intro i

  apply le_iSup_of_le (u.func i)
  apply le_inf
  ·
    apply @mem_mk'' 𝔹 _ u i
    exact inf_le_right.trans inf_le_left
  ·

    have hϕi := poset_yoneda_inv (Γ ⊓ u.bval i) bv_imp_elim
      (le_inf (inf_le_left.trans (collect.func_spec ϕ h_congr_right h_congr_left u Γ H_AE |>.trans
        (iInf_le _ i))) inf_le_right)

    have hbval : Γ ⊓ (u.bval i ⊓ w =ᴮ collect.func ϕ h_congr_right u i) ≤
        ϕ (u.func i) (collect.func ϕ h_congr_right u i) :=
      (inf_le_inf_left _ inf_le_left).trans hϕi
    have heq_sym : Γ ⊓ (u.bval i ⊓ w =ᴮ collect.func ϕ h_congr_right u i) ≤
        collect.func ϕ h_congr_right u i =ᴮ w :=
      (inf_le_right.trans inf_le_right).trans (le_of_eq bv_eq_symm)
    exact le_trans (le_inf heq_sym hbval) (h_congr_right _ _ _)

theorem bSet_axiom_of_collection (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z) :
    ⊤ ≤ ⨅ u, (⨅ x, x ∈ᴮ u ⟹ ⨆ y, ϕ x y) ⟹ ⨆ v, (⨅ w, w ∈ᴮ u ⟹ ⨆ w', w' ∈ᴮ v ⊓ ϕ w w') ⊓
      ⨅ w', w' ∈ᴮ v ⟹ ⨆ w, w ∈ᴮ u ⊓ ϕ w w' := by
  apply le_iInf; intro u
  rw [← deduction, top_inf_eq]

  apply le_iSup_of_le (collect ϕ h_congr_right h_congr_left u)

  have H_AE : (⨅ x, x ∈ᴮ u ⟹ ⨆ y, ϕ x y) ≤
      ⨅ (i : u.type), u.bval i ⟹ ⨆ (w : bSet 𝔹), ϕ (u.func i) w := by
    apply le_iInf; intro i
    rw [← deduction]
    calc (⨅ x, x ∈ᴮ u ⟹ ⨆ y, ϕ x y) ⊓ u.bval i
        ≤ (u.func i ∈ᴮ u ⟹ ⨆ y, ϕ (u.func i) y) ⊓ u.bval i :=
          inf_le_inf_right _ (iInf_le _ (u.func i))
      _ ≤ (u.func i ∈ᴮ u ⟹ ⨆ y, ϕ (u.func i) y) ⊓ (u.func i ∈ᴮ u) :=
          inf_le_inf_left _ (mem_mk'' le_rfl)
      _ ≤ ⨆ w, ϕ (u.func i) w := bv_imp_elim
  apply le_inf
  · exact collect_spec₁ ϕ h_congr_right h_congr_left u H_AE
  · exact collect_spec₂ ϕ h_congr_right h_congr_left u H_AE

def bv_union (u : bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ (i : u.type), (u.func i).type,
   fun x => (u.func x.1).func x.2,
   fun x => ⨆ (y : u.type), u.bval y ⊓ (u.func x.1).func x.2 ∈ᴮ u.func y⟩

lemma bv_union_spec (u : bSet 𝔹) : ⊤ ≤ ⨅ (x : bSet 𝔹),
    (x ∈ᴮ bv_union u ⟹ ⨆ (y : u.type), u.bval y ⊓ x ∈ᴮ u.func y) ⊓
    ((⨆ (y : u.type), u.bval y ⊓ x ∈ᴮ u.func y) ⟹ x ∈ᴮ bv_union u) := by
  apply le_iInf; intro x
  apply le_inf
  ·
    rw [← deduction, top_inf_eq, mem_unfold (v := bv_union u)]

    apply iSup_le; intro ⟨a, i⟩

    change (⨆ y, u.bval y ⊓ (u.func a).func i ∈ᴮ u.func y) ⊓ x =ᴮ (u.func a).func i ≤ _
    rw [iSup_inf_eq]
    apply iSup_le; intro y
    apply le_iSup_of_le y

    apply le_inf (inf_le_left.trans inf_le_left)

    exact poset_yoneda_inv _ subst_congr_mem_left
      (le_inf (by rw [← bv_eq_symm]; exact inf_le_right) (inf_le_left.trans inf_le_right))
  ·
    rw [← deduction, top_inf_eq, mem_unfold (v := bv_union u)]
    apply iSup_le; intro y
    rw [mem_unfold, inf_iSup_eq]
    apply iSup_le; intro j
    apply le_iSup_of_le ⟨y, j⟩

    change _ ≤ (⨆ z, u.bval z ⊓ (u.func y).func j ∈ᴮ u.func z) ⊓ x =ᴮ (u.func y).func j
    apply le_inf
    · apply le_iSup_of_le y
      apply le_inf inf_le_left
      exact le_trans (inf_le_right.trans inf_le_left) (mem_mk'' le_rfl)
    · exact inf_le_right.trans inf_le_right

lemma bv_union_spec' (u : bSet 𝔹) {Γ : 𝔹} : Γ ≤ ⨅ (x : bSet 𝔹),
    (x ∈ᴮ bv_union u ⟹ ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) ⊓
    ((⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) ⟹ x ∈ᴮ bv_union u) := by
  apply le_iInf; intro x
  have hspec := bv_union_spec u |>.trans (iInf_le _ x)

  have h_fwd_raw : x ∈ᴮ bv_union u ≤ ⨆ i, u.bval i ⊓ x ∈ᴮ u.func i :=
    le_trans (le_inf (le_top.trans (hspec.trans inf_le_left)) le_rfl) bv_imp_elim
  have h_bwd_raw : (⨆ i, u.bval i ⊓ x ∈ᴮ u.func i) ≤ x ∈ᴮ bv_union u :=
    le_trans (le_inf (le_top.trans (hspec.trans inf_le_right)) le_rfl) bv_imp_elim
  rw [@bounded_exists _ _ u (fun z => x ∈ᴮ z) (h_congr := fun a b => subst_congr_mem_right)] at h_fwd_raw h_bwd_raw
  apply le_inf
  · exact le_top.trans (le_of_eq (imp_top_iff_le.mpr h_fwd_raw).symm)
  · exact le_top.trans (le_of_eq (imp_top_iff_le.mpr h_bwd_raw).symm)

lemma bv_union_spec_split (u : bSet 𝔹) {Γ : 𝔹} (x : bSet 𝔹) :
    (Γ ≤ x ∈ᴮ bv_union u) ↔ (Γ ≤ ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) := by
  have hspec := bv_union_spec' u (Γ := Γ) |>.trans (iInf_le _ x)
  constructor
  · intro H
    exact poset_yoneda_inv Γ bv_imp_elim (le_inf (hspec.trans inf_le_left) H)
  · intro H
    exact poset_yoneda_inv Γ bv_imp_elim (le_inf (hspec.trans inf_le_right) H)

lemma mem_bv_union_iff {u : bSet 𝔹} {Γ : 𝔹} {x : bSet 𝔹} :
    (Γ ≤ x ∈ᴮ bv_union u) ↔ (Γ ≤ ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) :=
  bv_union_spec_split u x

lemma bv_union_spec'' (u : bSet 𝔹) : ⊤ ≤ ⨅ (x : bSet 𝔹), (x ∈ᴮ u) ⟹ (x ⊆ᴮ bv_union u) := by
  apply le_iInf; intro x
  rw [← deduction, top_inf_eq, subset_unfold']
  apply le_iInf; intro v
  rw [← deduction]

  rw [bv_union_spec_split]

  exact le_iSup_of_le x (le_inf inf_le_left inf_le_right)

lemma bv_union_congr {x y : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ x =ᴮ y) :
    Γ ≤ bv_union x =ᴮ bv_union y := by

  have aux : ∀ (a b : bSet 𝔹) (H : Γ ≤ a =ᴮ b) (z w : bSet 𝔹),
      Γ ⊓ (w ∈ᴮ a ⊓ z ∈ᴮ w) ≤ w ∈ᴮ b ⊓ z ∈ᴮ w := fun a b H z w =>
    le_inf
      (le_trans (le_inf (inf_le_left.trans H) (inf_le_right.trans inf_le_left)) subst_congr_mem_right)
      (inf_le_right.trans inf_le_right)
  apply mem_ext
  · apply le_iInf; intro z
    rw [← deduction]

    have hx : z ∈ᴮ bv_union x = ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split x z (Γ := z ∈ᴮ bv_union x)).mp le_rfl)
                  ((bv_union_spec_split x z (Γ := ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w)).mpr le_rfl)
    have hy : z ∈ᴮ bv_union y = ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split y z (Γ := z ∈ᴮ bv_union y)).mp le_rfl)
                  ((bv_union_spec_split y z (Γ := ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w)).mpr le_rfl)
    rw [hx, hy, inf_iSup_eq]
    exact iSup_le fun w => le_iSup_of_le w (aux x y H_eq z w)
  · apply le_iInf; intro z
    rw [← deduction]
    have hx : z ∈ᴮ bv_union x = ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split x z (Γ := z ∈ᴮ bv_union x)).mp le_rfl)
                  ((bv_union_spec_split x z (Γ := ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w)).mpr le_rfl)
    have hy : z ∈ᴮ bv_union y = ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split y z (Γ := z ∈ᴮ bv_union y)).mp le_rfl)
                  ((bv_union_spec_split y z (Γ := ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w)).mpr le_rfl)
    rw [hy, hx, inf_iSup_eq]
    exact iSup_le fun w => le_iSup_of_le w
      (aux y x (H_eq.trans (le_of_eq bv_eq_symm)) z w)

@[simp] lemma B_congr_bv_union : B_congr (bv_union : bSet 𝔹 → bSet 𝔹) :=
  fun H => bv_union_congr H

theorem bSet_axiom_of_union : (⨅ (u : bSet 𝔹), (⨆ v, ⨅ x,
    (x ∈ᴮ v ⇔ (⨆ (y : u.type), u.bval y ⊓ x ∈ᴮ u.func y)))) = ⊤ := by
  apply top_unique
  apply le_iInf; intro u
  apply le_iSup_of_le (bv_union u)
  apply le_iInf; intro x
  exact le_trans le_top (bv_union_spec u) |>.trans (iInf_le _ x)

@[simp] def set_of_indicator {u : bSet 𝔹} (f : u.type → 𝔹) : bSet 𝔹 :=
  ⟨u.type, u.func, f⟩

@[simp] lemma set_of_indicator_type {u : bSet 𝔹} {f : u.type → 𝔹} :
    (set_of_indicator f).type = u.type := rfl

@[simp] lemma set_of_indicator_func {u : bSet 𝔹} {f : u.type → 𝔹} {i : u.type} :
    (set_of_indicator f).func i = u.func i := rfl

@[simp] lemma set_of_indicator_bval {u : bSet 𝔹} {f : u.type → 𝔹} {i : u.type} :
    (set_of_indicator f).bval i = f i := rfl

def bv_powerset (u : bSet 𝔹) : bSet 𝔹 :=
  ⟨u.type → 𝔹,
   fun (f : u.type → 𝔹) => (⟨u.type, u.func, f⟩ : bSet 𝔹),
   fun (f : u.type → 𝔹) => (⟨u.type, u.func, f⟩ : bSet 𝔹) ⊆ᴮ u⟩

prefix:80 "𝒫" => bv_powerset

private lemma bv_powerset_mem_unfold {u x : bSet 𝔹} :
    x ∈ᴮ bv_powerset u =
    ⨆ f : u.type → 𝔹, (set_of_indicator (u := u) f ⊆ᴮ u) ⊓ x =ᴮ set_of_indicator (u := u) f := by
  rw [mem_unfold]
  rfl

lemma bv_powerset_spec {u x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ u ↔ Γ ≤ x ∈ᴮ (bv_powerset u) := by
  rw [bv_powerset_mem_unfold]
  constructor
  ·
    intro H

    apply bv_use (fun j => u.func j ∈ᴮ x)
    apply le_inf
    ·

      rw [subset_unfold]
      simp only [set_of_indicator_bval, set_of_indicator_func]
      apply le_iInf; intro j; rw [← deduction]

      have hspec : Γ ≤ u.func j ∈ᴮ x ⟹ u.func j ∈ᴮ u :=
        le_trans H (by rw [subset_unfold']; exact iInf_le _ (u.func j))
      exact le_trans (le_inf (le_trans inf_le_left hspec) inf_le_right) bv_imp_elim
    ·
      apply mem_ext
      ·
        apply le_iInf; intro z; rw [← deduction]

        rw [mem_unfold (v := set_of_indicator (u := u) (fun j => u.func j ∈ᴮ x))]
        simp only [set_of_indicator_bval, set_of_indicator_func]

        have hmem_u : Γ ⊓ z ∈ᴮ x ≤ z ∈ᴮ u := by
          have : Γ ≤ z ∈ᴮ x ⟹ z ∈ᴮ u :=
            le_trans H (by rw [subset_unfold']; exact iInf_le _ z)
          exact le_trans (le_inf (le_trans inf_le_left this) inf_le_right) bv_imp_elim

        calc Γ ⊓ z ∈ᴮ x
            ≤ (Γ ⊓ z ∈ᴮ x) ⊓ (z ∈ᴮ u) := le_inf le_rfl hmem_u
          _ = (Γ ⊓ z ∈ᴮ x) ⊓ ⨆ j, u.bval j ⊓ z =ᴮ u.func j := by rw [← mem_unfold]
          _ = ⨆ j, (Γ ⊓ z ∈ᴮ x) ⊓ (u.bval j ⊓ z =ᴮ u.func j) := by
              rw [inf_iSup_eq]
          _ ≤ ⨆ j, (u.func j ∈ᴮ x) ⊓ z =ᴮ u.func j := by
              apply iSup_le; intro j; apply le_iSup_of_le j
              apply le_inf
              ·
                have : (Γ ⊓ z ∈ᴮ x) ⊓ (u.bval j ⊓ z =ᴮ u.func j) ≤
                       z ∈ᴮ x ⊓ z =ᴮ u.func j :=
                  le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
                exact le_trans this (by rw [inf_comm]; exact subst_congr_mem_left)
              · exact inf_le_right.trans inf_le_right
      ·

        apply le_iInf; intro z; rw [← deduction]

        rw [mem_unfold (v := set_of_indicator (u := u) (fun j => u.func j ∈ᴮ x))]
        simp only [set_of_indicator_bval, set_of_indicator_func]

        rw [inf_iSup_eq]
        apply iSup_le; intro j

        calc Γ ⊓ (u.func j ∈ᴮ x ⊓ z =ᴮ u.func j)
            ≤ u.func j ∈ᴮ x ⊓ z =ᴮ u.func j := inf_le_right
          _ ≤ u.func j =ᴮ z ⊓ u.func j ∈ᴮ x :=
              le_inf (inf_le_right.trans (le_of_eq bv_eq_symm)) inf_le_left
          _ ≤ z ∈ᴮ x := subst_congr_mem_left
  ·
    intro H
    apply le_trans H
    apply iSup_le; intro f

    exact le_trans (le_inf inf_le_left inf_le_right) subst_congr_subset_left

lemma mem_powerset_iff {u x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ∈ᴮ (bv_powerset u) ↔ Γ ≤ x ⊆ᴮ u :=
  bv_powerset_spec.symm

private lemma bSet_axiom_of_powerset_slice (u : bSet 𝔹) :
    (⊤ : 𝔹) ≤ ⨆ (v : bSet 𝔹), ⨅ (x : bSet 𝔹), biimp (x ∈ᴮ v) (x ⊆ᴮ u) := by
  apply le_iSup_of_le (bv_powerset u)
  apply le_iInf; intro x
  simp only [biimp]
  apply le_inf
  ·
    rw [← deduction, top_inf_eq]
    exact bv_powerset_spec.mpr le_rfl
  ·
    rw [← deduction, top_inf_eq]
    exact bv_powerset_spec.mp le_rfl

theorem bSet_axiom_of_powerset :
    (⨅ (u : bSet 𝔹), ⨆ (v : bSet 𝔹), ⨅ (x : bSet 𝔹),
      ((x ∈ᴮ v) ⇔ (x ⊆ᴮ u))) = ⊤ :=

  top_unique (le_iInf bSet_axiom_of_powerset_slice)

lemma bv_powerset_congr {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) :
    Γ ≤ bv_powerset x =ᴮ bv_powerset y := by
  apply mem_ext
  ·
    apply le_iInf; intro z; rw [← deduction]

    have hz_sub_x : Γ ⊓ z ∈ᴮ bv_powerset x ≤ z ⊆ᴮ x :=
      le_trans inf_le_right (bv_powerset_spec.mpr le_rfl)

    have hz_sub_y : Γ ⊓ z ∈ᴮ bv_powerset x ≤ z ⊆ᴮ y :=
      le_trans (le_inf hz_sub_x (le_trans inf_le_left H)) subst_congr_subset_right

    exact bv_powerset_spec.mp hz_sub_y
  ·
    apply le_iInf; intro z; rw [← deduction]
    have hz_sub_y : Γ ⊓ z ∈ᴮ bv_powerset y ≤ z ⊆ᴮ y :=
      le_trans inf_le_right (bv_powerset_spec.mpr le_rfl)
    have Hy : Γ ≤ y =ᴮ x := le_trans H (le_of_eq bv_eq_symm)
    have hz_sub_x : Γ ⊓ z ∈ᴮ bv_powerset y ≤ z ⊆ᴮ x :=
      le_trans (le_inf hz_sub_y (le_trans inf_le_left Hy)) subst_congr_subset_right
    exact bv_powerset_spec.mp hz_sub_x

@[simp] lemma set_of_indicator_mem.mk {x : bSet 𝔹} {i : x.type} {χ : x.type → 𝔹} {Γ : 𝔹}
    (H_Γ : Γ ≤ χ i) : Γ ≤ x.func i ∈ᴮ set_of_indicator χ := by
  rw [mem_unfold]
  apply bv_use i
  exact le_inf H_Γ bv_refl

@[simp] lemma set_of_indicator_subset {x : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹}
    (H_χ : ∀ i, χ i ≤ x.bval i) : Γ ≤ set_of_indicator χ ⊆ᴮ x := by
  rw [subset_unfold']
  apply le_iInf; intro z
  rw [← deduction]

  apply le_trans inf_le_right

  simp only [mem_unfold, set_of_indicator_bval, set_of_indicator_func]
  apply iSup_le; intro i
  apply le_iSup_of_le i
  exact inf_le_inf_right _ (H_χ i)

@[reducible, simp] def subset.mk {u : bSet 𝔹} (χ : u.type → 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun i => χ i ⊓ u.bval i)

@[simp] lemma subset.mk_subset {u : bSet 𝔹} {χ : u.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ subset.mk χ ⊆ᴮ u := by
  apply set_of_indicator_subset; intro i; simp

lemma check_set_of_indicator_subset {x : PSet} {χ : (check x).type → 𝔹} {Γ : 𝔹} :
    Γ ≤ set_of_indicator χ ⊆ᴮ check x :=
  set_of_indicator_subset (fun i => by rw [check_bval_top]; exact le_top)

lemma mem_set_of_indicator_iff {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹}
    (H_χ : ∀ i, χ i ≤ x.bval i) :
    Γ ≤ z ∈ᴮ set_of_indicator χ ↔ Γ ≤ ⨆ (i : x.type), z =ᴮ x.func i ⊓ χ i := by

  rw [mem_unfold]
  simp only [set_of_indicator_bval, set_of_indicator_func]
  constructor <;> intro H <;> apply le_trans H <;> apply iSup_le <;> intro i <;>
    apply le_iSup_of_le i <;> simp [inf_comm]

lemma mem_subset.mk_iff {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ subset.mk χ ↔ Γ ≤ ⨆ (i : x.type), z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i) :=
  mem_set_of_indicator_iff (by simp)

lemma mem_subset.mk_iff₂ {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ subset.mk χ ↔ Γ ≤ ⨆ (i : x.type), x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i) := by
  rw [mem_subset.mk_iff]

  have heq : (⨆ i : x.type, z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i)) =
             (⨆ i : x.type, x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i)) :=
    iSup_congr fun i => by rw [← inf_assoc, inf_comm (z =ᴮ x.func i ⊓ χ i)]
  rw [heq]

@[simp] lemma mem_of_mem_subset.mk {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹}
    (Hz : Γ ≤ z ∈ᴮ subset.mk χ) : Γ ≤ z ∈ᴮ x :=
  mem_of_mem_subset subset.mk_subset Hz

lemma check_mem_set_of_indicator_iff {x : PSet}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂)
    (i : x.Type) {χ : (check x).type → 𝔹} :
    (∀ {Γ : 𝔹}, Γ ≤ check (x.Func i) ∈ᴮ set_of_indicator χ) ↔
    (∀ {Γ : 𝔹}, Γ ≤ χ (cast check_type'.symm i)) := by

  cases x with | mk α A =>

  constructor
  ·
    intro H Γ

    rw [mem_unfold] at H
    simp only [set_of_indicator_bval, set_of_indicator_func, check_func, check_cast] at H

    apply le_trans H
    apply iSup_le; intro j
    classical
    by_cases hj : j = i
    · subst hj; exact inf_le_left
    · have hne : ¬ PSet.Equiv (A i) (A j) := fun heq =>
        hj (H_inj i j heq).symm
      have hbot : (check (A i) : bSet 𝔹) =ᴮ check (A j) = ⊥ :=
        check_bv_eq_bot_of_not_equiv hne
      simp [hbot]
  ·
    intro H Γ
    rw [mem_unfold]
    simp only [set_of_indicator_bval, set_of_indicator_func, check_func, check_cast]
    apply bv_use i
    exact le_inf H bv_refl

lemma subset_of_pointwise_bounded {Γ : 𝔹} {x : bSet 𝔹} {p p' : x.type → 𝔹}
    (H_bd : ∀ i : x.type, p i ≤ p' i) : Γ ≤ set_of_indicator p ⊆ᴮ set_of_indicator p' := by
  rw [subset_unfold]
  apply le_iInf; intro j
  rw [← deduction]

  apply le_iSup_of_le j
  exact le_inf (le_trans inf_le_right (H_bd j)) bv_refl

lemma pointwise_bounded_of_check_subset_check {x : PSet} {p₁ p₂ : (check x).type → 𝔹}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂)
    (H_eq : ∀ {Γ : 𝔹}, Γ ≤ set_of_indicator p₁ ⊆ᴮ set_of_indicator p₂) :
    ∀ i, p₁ i ≤ p₂ i := by
  intro i

  have hle : p₁ i ≤ set_of_indicator p₁ ⊆ᴮ set_of_indicator p₂ := H_eq

  rw [subset_unfold] at hle
  simp only [set_of_indicator_bval, set_of_indicator_func] at hle

  have himp : p₁ i ≤ p₁ i ⟹ (check x).func i ∈ᴮ set_of_indicator p₂ :=
    le_trans hle (iInf_le _ i)

  have hmem : p₁ i ≤ (check x).func i ∈ᴮ set_of_indicator p₂ :=
    le_trans (le_inf himp le_rfl) bv_imp_elim

  rw [mem_unfold] at hmem
  simp only [set_of_indicator_bval, set_of_indicator_func, check_func] at hmem

  calc p₁ i ≤ ⨆ j, p₂ j ⊓ check (x.Func (check_cast i)) =ᴮ (check (x.Func (check_cast j)) : bSet 𝔹) := hmem
    _ ≤ p₂ i := by
        apply iSup_le; intro j
        classical
        by_cases hj : check_cast j = check_cast i
        · have hjj : j = i := by
            simp only [check_cast, cast_inj] at hj; exact hj
          subst hjj; simp
        · have hne : ¬ PSet.Equiv (x.Func (check_cast i)) (x.Func (check_cast j)) := fun heq =>
            hj (H_inj (check_cast i) (check_cast j) heq).symm
          rw [check_bv_eq_bot_of_not_equiv hne]; simp

lemma pointwise_eq_of_eq_set_of_indicator {x : PSet} {p₁ p₂ : (check x).type → 𝔹}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂)
    (H_eq : ∀ {Γ : 𝔹}, Γ ≤ set_of_indicator p₁ =ᴮ set_of_indicator p₂) :
    ∀ i, p₁ i = p₂ i := by
  intro i
  apply le_antisymm
  · apply pointwise_bounded_of_check_subset_check H_inj
    intro Γ
    exact le_trans (H_eq (Γ := Γ)) (by rw [bv_eq_unfold]; exact inf_le_left)
  · apply pointwise_bounded_of_check_subset_check H_inj
    intro Γ
    exact le_trans (H_eq (Γ := Γ)) (by rw [bv_eq_unfold]; exact inf_le_right)

lemma set_of_indicator_eq_iff_pointwise_eq {x : PSet} {p₁ p₂ : (check x).type → 𝔹}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂) :
    (∀ {Γ : 𝔹}, Γ ≤ set_of_indicator p₁ =ᴮ set_of_indicator p₂) ↔ ∀ i, p₁ i = p₂ i := by
  constructor
  · intro H_eq
    exact pointwise_eq_of_eq_set_of_indicator H_inj H_eq
  · intro H_eq Γ
    simp [show p₁ = p₂ from funext H_eq]

section infinity

private def ω' := PSet.omega

@[simp] lemma check_omega_type : (check ω' : bSet 𝔹).type = ULift ℕ := rfl
@[simp] lemma check_omega_func :
    (check ω' : bSet 𝔹).func = fun x => check (PSet.ofNat x.down) := rfl

@[simp, reducible] def axiom_of_infinity_spec (u : bSet 𝔹) : 𝔹 :=
  (∅ ∈ᴮ u) ⊓ (⨅ (i_x : u.type), ⨆ (i_y : u.type), u.func i_x ∈ᴮ u.func i_y)

@[reducible] def contains_empty (u : bSet 𝔹) : 𝔹 := ∅ ∈ᴮ u

@[reducible] def contains_succ (u : bSet 𝔹) : 𝔹 :=
  ⨅ (i_x : u.type), ⨆ (i_y : u.type), u.func i_x ∈ᴮ u.func i_y

lemma infinity_of_empty_succ {u : bSet 𝔹} {c : 𝔹} (h₁ : c ≤ contains_empty u)
    (h₂ : c ≤ contains_succ u) : c ≤ axiom_of_infinity_spec u :=
  le_inf h₁ h₂

lemma contains_empty_check_omega : (⊤ : 𝔹) ≤ contains_empty (check ω') := by
  simp only [contains_empty]

  have h : (∅ : bSet 𝔹) = (check ω').func ⟨0⟩ := by
    simp only [check_omega_func]

    norm_cast
    simp [show PSet.ofNat 0 = ∅ from rfl, check_empty_eq_empty]
  rw [h, top_le_iff]
  exact check_mem_top

lemma contains_succ_check_omega : (⊤ : 𝔹) ≤ contains_succ (check ω') := by
  simp only [contains_succ]
  apply le_iInf; intro ⟨n⟩
  apply le_iSup_of_le ⟨n + 1⟩
  simp only [check_omega_func]

  apply le_trans le_top; rw [top_le_iff]
  have hmem := @PSet.ofNat_mem_of_lt n (n + 1) (Nat.lt_succ_self n)
  rcases hmem with ⟨i, hi⟩

  apply top_unique
  have h_eq : check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) = (⊤ : 𝔹) :=
    check_bv_eq_top_of_equiv hi
  have h_mem : (⊤ : 𝔹) ≤ check ((PSet.ofNat (n + 1)).Func i) ∈ᴮ check (PSet.ofNat (n + 1)) :=
    mem_check_of_mem
  calc ⊤
      = check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) ⊓
          check ((PSet.ofNat (n + 1)).Func i) ∈ᴮ check (PSet.ofNat (n + 1)) := by
          rw [h_eq, top_inf_eq, top_le_iff.mp h_mem]
    _ ≤ check (PSet.ofNat n) ∈ᴮ check (PSet.ofNat (n + 1)) := by
          rw [show check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) =
              check ((PSet.ofNat (n + 1)).Func i) =ᴮ check (PSet.ofNat n) from bv_eq_symm]
          exact subst_congr_mem_left

theorem bSet_axiom_of_infinity : (⨆ (u : bSet 𝔹), axiom_of_infinity_spec u) = ⊤ := by
  apply top_unique
  apply bv_use (check ω')
  exact infinity_of_empty_succ contains_empty_check_omega contains_succ_check_omega

@[reducible] def omega : bSet 𝔹 := check ω'

@[simp] lemma omega_type : (omega : bSet 𝔹).type = ULift ℕ := rfl

@[reducible] def of_nat : ℕ → bSet 𝔹 := fun n => check (PSet.ofNat n)

@[simp] lemma omega_func {k : ULift ℕ} : (omega : bSet 𝔹).func k = of_nat k.down := rfl

lemma omega_definite {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega := by
  suffices h : of_nat n ∈ᴮ omega = (⊤ : 𝔹) by
    exact le_trans le_top (by rwa [top_le_iff])
  apply top_unique
  induction n with
  | zero => apply bv_use (ULift.up 0); simp
  | succ k _ => apply bv_use (ULift.up (k + 1)); simp

lemma of_nat_mem_omega {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega := omega_definite

instance has_zero_bSet : Zero (bSet 𝔹) := ⟨of_nat 0⟩
instance has_one_bSet : One (bSet 𝔹) := ⟨of_nat 1⟩

@[reducible] def two : bSet 𝔹 := of_nat 2
notation "𝟚" => bSet.two

lemma zero_eq_empty {Γ : 𝔹} : Γ ≤ (0 : bSet 𝔹) =ᴮ ∅ := by
  change Γ ≤ of_nat 0 =ᴮ ∅
  rw [← check_empty_eq_empty]
  exact check_bv_eq (by rfl)

private lemma of_nat_mem_of_nat_succ (n : ℕ) : (of_nat n : bSet 𝔹) ∈ᴮ of_nat (n + 1) = ⊤ := by
  show check (PSet.ofNat n) ∈ᴮ check (PSet.ofNat (n + 1)) = (⊤ : 𝔹)
  have hmem := @PSet.ofNat_mem_of_lt n (n + 1) (Nat.lt_succ_self n)
  rcases hmem with ⟨i, hi⟩
  apply top_unique
  have h_eq : check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) = (⊤ : 𝔹) :=
    check_bv_eq_top_of_equiv hi
  have h_mem : (⊤ : 𝔹) ≤ check ((PSet.ofNat (n + 1)).Func i) ∈ᴮ check (PSet.ofNat (n + 1)) :=
    @mem_check_of_mem 𝔹 _ (PSet.ofNat (n + 1)) i (Γ := ⊤)
  calc ⊤
      = check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) ⊓
          check ((PSet.ofNat (n + 1)).Func i) ∈ᴮ check (PSet.ofNat (n + 1)) := by
            rw [h_eq, top_inf_eq, top_le_iff.mp h_mem]
    _ ≤ check (PSet.ofNat n) ∈ᴮ check (PSet.ofNat (n + 1)) := by
          rw [show check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) =
              check ((PSet.ofNat (n + 1)).Func i) =ᴮ check (PSet.ofNat n) from bv_eq_symm]
          exact subst_congr_mem_left

@[simp] lemma zero_mem_one {Γ : 𝔹} : Γ ≤ (0 : bSet 𝔹) ∈ᴮ (1 : bSet 𝔹) := by
  apply le_trans le_top; rw [top_le_iff]
  exact of_nat_mem_of_nat_succ 0

lemma forall_empty {Γ : 𝔹} {ϕ : bSet 𝔹 → 𝔹} : Γ ≤ ⨅ x, x ∈ᴮ ∅ ⟹ ϕ x := by
  apply le_iInf; intro x
  rw [← deduction]
  exact le_trans (bot_of_mem_empty inf_le_right) bot_le

@[simp] lemma omega_bval {k : ULift ℕ} : (omega : bSet 𝔹).bval k = ⊤ := rfl

theorem bSet_axiom_of_infinity' :
    (⊤ : 𝔹) ≤ (∅ ∈ᴮ omega) ⊓ (⨅ x, x ∈ᴮ omega ⟹ ⨆ y, y ∈ᴮ omega ⊓ x ∈ᴮ y) := by
  apply le_inf
  · exact contains_empty_check_omega
  ·

    apply le_iInf; intro x
    rw [← deduction, top_inf_eq]

    rw [mem_unfold]; simp only [omega_bval, omega_func, top_inf_eq]
    apply iSup_le; intro ⟨k⟩

    apply le_iSup_of_le (of_nat (k + 1))
    apply le_inf
    ·
      exact le_trans le_top omega_definite
    ·

      have h_kmem : (of_nat k : bSet 𝔹) ∈ᴮ of_nat (k + 1) = ⊤ := of_nat_mem_of_nat_succ k
      calc x =ᴮ of_nat k
          = of_nat k =ᴮ x := bv_eq_symm
        _ ≤ of_nat k =ᴮ x ⊓ (of_nat k : bSet 𝔹) ∈ᴮ of_nat (k + 1) :=
            le_inf le_rfl (h_kmem ▸ le_top)
        _ ≤ x ∈ᴮ of_nat (k + 1) := subst_congr_mem_left

end infinity

theorem bSet_epsilon_induction (ϕ : bSet 𝔹 → 𝔹) (h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y) :
    (⨅ (x : bSet 𝔹), (⨅ (y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x) ⟹ (⨅ (z : bSet 𝔹), ϕ z) = ⊤ := by
  apply top_unique; rw [← deduction, top_inf_eq]

  apply le_iInf; intro z

  induction z with
  | mk α A B ih =>

  have h_bdd : (⨅ (y : bSet 𝔹), y ∈ᴮ mk α A B ⟹ ϕ y) =
               ⨅ (i : α), (B i ⟹ ϕ (A i)) := by
    rw [← bounded_forall (h_congr := h_congr)]
    simp [func, bval]

  have h_inner : (⨅ (x : bSet 𝔹), (⨅ (y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x) ≤
                 ⨅ (i : α), (B i ⟹ ϕ (A i)) := by
    apply le_iInf; intro i

    rw [← deduction]
    exact inf_le_left.trans (ih i)

  apply bv_have (h_bdd.symm ▸ h_inner)

  calc (⨅ (x : bSet 𝔹), (⨅ y, y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x) ⊓
       (⨅ (y : bSet 𝔹), y ∈ᴮ mk α A B ⟹ ϕ y)
      ≤ ((⨅ y, y ∈ᴮ mk α A B ⟹ ϕ y) ⟹ ϕ (mk α A B)) ⊓
        (⨅ y, y ∈ᴮ mk α A B ⟹ ϕ y) := by
          apply inf_le_inf_right
          apply iInf_le_of_le (mk α A B); rfl
    _ ≤ ϕ (mk α A B) := bv_imp_elim

lemma epsilon_induction {Γ : 𝔹} (ϕ : bSet 𝔹 → 𝔹) (h_congr : B_ext ϕ)
    (H_ih : ∀ x, Γ ≤ (⨅ (y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x) :
    ∀ z, Γ ≤ ϕ z := by

  have h_eps := bSet_epsilon_induction ϕ h_congr

  have h_le : (⨅ (x : bSet 𝔹), (⨅ (y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x) ≤
              (⨅ (z : bSet 𝔹), ϕ z) := by

    have hle : (⊤ : 𝔹) ≤ (⨅ (x : bSet 𝔹), (⨅ y, y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x) ⟹ ⨅ z, ϕ z :=
      h_eps ▸ le_refl _
    have := deduction.mpr hle
    rwa [top_inf_eq] at this
  intro z
  have H_a : Γ ≤ ⨅ (x : bSet 𝔹), (⨅ (y : bSet 𝔹), y ∈ᴮ x ⟹ ϕ y) ⟹ ϕ x :=
    le_iInf (fun x => H_ih x)
  exact le_trans H_a (le_trans h_le (iInf_le _ z))

@[elab_as_elim] protected noncomputable def rec_on' {C : bSet 𝔹 → Sort*} (y : bSet 𝔹)
    (IH : ∀ (x : bSet 𝔹), (∀ (a : x.type), C (x.func a)) → C x) : C y := by
  induction y with
  | mk α A B ih => exact IH ⟨α, A, B⟩ ih

@[elab_as_elim] protected noncomputable def rec' {C : bSet 𝔹 → Sort*}
    (IH : ∀ (x : bSet 𝔹), (∀ (a : x.type), C (x.func a)) → C x) : ∀ (y : bSet 𝔹), C y :=
  fun y => bSet.rec_on' y IH

private lemma regularity_aux_top (x : bSet 𝔹) :
    (⊤ : 𝔹) ≤ ⨅ u, x ∈ᴮ u ⟹ (⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ)) := by
  induction x using bSet.rec' with
  | _ x IH =>

    have IH_spec : ∀ (a : x.type) (u' : bSet 𝔹),
        x.func a ∈ᴮ u' ≤ ⨆ y, y ∈ᴮ u' ⊓ (⨅ z', z' ∈ᴮ u' ⟹ (z' ∈ᴮ y)ᶜ) := fun a u' =>
      le_trans
        (le_inf (le_trans le_top (le_trans (IH a) (iInf_le _ u'))) le_rfl)
        bv_imp_elim
    apply le_iInf; intro u
    rw [← deduction, top_inf_eq]

    set P := ⨅ (z' : bSet 𝔹), z' ∈ᴮ u ⟹ (z' ∈ᴮ x)ᶜ with hP_def

    calc x ∈ᴮ u
        = x ∈ᴮ u ⊓ (P ⊔ Pᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = (x ∈ᴮ u ⊓ P) ⊔ (x ∈ᴮ u ⊓ Pᶜ) := inf_sup_left (a := x ∈ᴮ u) (b := P) (c := Pᶜ)
      _ ≤ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ) := by
          apply sup_le
          ·

            apply le_iSup_of_le x
            exact le_inf inf_le_left inf_le_right
          ·

            rw [show Pᶜ = ⨆ (z' : bSet 𝔹), z' ∈ᴮ u ⊓ z' ∈ᴮ x by
              simp only [hP_def, compl_iInf, neg_imp, compl_compl]]
            rw [inf_iSup_eq]

            apply iSup_le; intro z'

            rw [mem_unfold (v := x), inf_iSup_eq, inf_iSup_eq]
            apply iSup_le; intro a

            have h_mem : x ∈ᴮ u ⊓ (z' ∈ᴮ u ⊓ (x.bval a ⊓ z' =ᴮ x.func a)) ≤ x.func a ∈ᴮ u :=
              calc x ∈ᴮ u ⊓ (z' ∈ᴮ u ⊓ (x.bval a ⊓ z' =ᴮ x.func a))
                  ≤ z' ∈ᴮ u ⊓ z' =ᴮ x.func a :=
                    le_inf (inf_le_right.trans inf_le_left)
                           (inf_le_right.trans inf_le_right |>.trans inf_le_right)
                _ ≤ x.func a ∈ᴮ u := by rw [inf_comm]; exact subst_congr_mem_left
            exact le_trans h_mem (IH_spec a u)

lemma regularity_aux (x : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ ⨅ u, x ∈ᴮ u ⟹ (⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ)) :=
  le_trans le_top (regularity_aux_top x)

theorem bSet_axiom_of_regularity (x : bSet 𝔹) {Γ : 𝔹} (H : Γ ≤ (x =ᴮ ∅)ᶜ) :
    Γ ≤ ⨆ y, y ∈ᴮ x ⊓ (⨅ z', z' ∈ᴮ x ⟹ (z' ∈ᴮ y)ᶜ) := by

  have H_nonempty : Γ ≤ ⨆ u, u ∈ᴮ x := nonempty_iff_exists_mem.mp H

  have h_each : ∀ u : bSet 𝔹, u ∈ᴮ x ≤ ⨆ y, y ∈ᴮ x ⊓ (⨅ z', z' ∈ᴮ x ⟹ (z' ∈ᴮ y)ᶜ) := fun u =>
    le_trans
      (le_inf (le_trans le_top (le_trans (regularity_aux_top u) (iInf_le _ x))) le_rfl)
      bv_imp_elim
  exact le_trans H_nonempty (iSup_le h_each)

@[reducible] def bv_exists_unique (ϕ : bSet 𝔹 → 𝔹) : 𝔹 :=
  ⨆ (x : bSet 𝔹), ⨅ (y : bSet 𝔹), ϕ y ⟹ y =ᴮ x

section zorns_lemma

lemma B_ext_subset_or_subset_left (y : bSet 𝔹) : B_ext (fun x => x ⊆ᴮ y ⊔ y ⊆ᴮ x) :=
  B_ext_sup (h₁ := B_ext_subset_left) (h₂ := B_ext_subset_right (x := y))
lemma B_ext_subset_or_subset_right (x : bSet 𝔹) : B_ext (fun y => x ⊆ᴮ y ⊔ y ⊆ᴮ x) :=
  B_ext_sup (h₁ := B_ext_subset_right (x := x)) (h₂ := B_ext_subset_left (y := x))

lemma forall_forall_reindex (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h₁ : ∀ x, B_ext (fun y => ϕ x y))
    (h₂ : ∀ y, B_ext (fun x => ϕ x y)) (C : bSet 𝔹) :
    (⨅ (i₁ : C.type), (C.bval i₁ ⟹ ⨅ (i₂ : C.type), (C.bval i₂ ⟹ ϕ (C.func i₁) (C.func i₂)))) =
    ⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹), w₁ ∈ᴮ C ⊓ w₂ ∈ᴮ C ⟹ ϕ w₁ w₂ := by

  have imp_iInf : ∀ (a : 𝔹) (f : bSet 𝔹 → 𝔹), (a ⟹ ⨅ w, f w) = ⨅ w, a ⟹ f w := by
    intro a f; simp only [imp, sup_iInf_eq]

  simp_rw [fun w₁ => @bounded_forall _ _ C (fun w₂ => ϕ w₁ w₂) (h_congr := fun a b => h₁ w₁ a b)]

  have h_cong_outer : ∀ (a b : bSet 𝔹), a =ᴮ b ⊓ (⨅ w₂, w₂ ∈ᴮ C ⟹ ϕ a w₂) ≤
      ⨅ w₂, w₂ ∈ᴮ C ⟹ ϕ b w₂ := by
    intro a b; apply le_iInf; intro w₂
    apply le_trans (inf_le_inf_left _ (iInf_le _ w₂))
    rw [← deduction]
    calc (a =ᴮ b ⊓ (w₂ ∈ᴮ C ⟹ ϕ a w₂)) ⊓ w₂ ∈ᴮ C
        ≤ a =ᴮ b ⊓ ((w₂ ∈ᴮ C ⟹ ϕ a w₂) ⊓ w₂ ∈ᴮ C) :=
          le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      _ ≤ a =ᴮ b ⊓ ϕ a w₂ := inf_le_inf_left _ bv_imp_elim
      _ ≤ ϕ b w₂ := h₂ w₂ a b
  rw [@bounded_forall _ _ C (fun w₁ => ⨅ w₂, w₂ ∈ᴮ C ⟹ ϕ w₁ w₂) (h_congr := h_cong_outer)]

  simp_rw [imp_iInf, curry_uncurry]

private def zorn_chain_hyp (X : bSet 𝔹) : 𝔹 :=
  ⨅ y, (y ⊆ᴮ X ⊓ ⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
    w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁)) ⟹ bv_union y ∈ᴮ X

lemma subset'_inductive (X : bSet 𝔹)
    (H : ⊤ ≤ zorn_chain_hyp X)
    {α : Type u} {S : α → bSet 𝔹} (h_core : core X S) :
    haveI := subset'_partial_order h_core
    ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c := by
  haveI hPO := subset'_partial_order h_core
  intro C C_chain

  set C' := bSet_of_core_set h_core C with hC'_def

  have H_internal_chain : (⊤ : 𝔹) ≤
      ⨅ (i₁ : C'.type), (C'.bval i₁ ⟹
      ⨅ (i₂ : C'.type), (C'.bval i₂ ⟹
        (C'.func i₁ ⊆ᴮ C'.func i₂ ⊔ C'.func i₂ ⊆ᴮ C'.func i₁))) := by
    apply le_iInf; intro ⟨i₁, H₁⟩
    rw [show C'.bval ⟨i₁, H₁⟩ = ⊤ from rfl, top_imp]
    apply le_iInf; intro ⟨i₂, H₂⟩
    rw [show C'.bval ⟨i₂, H₂⟩ = ⊤ from rfl, top_imp]
    show (⊤ : 𝔹) ≤ S i₁ ⊆ᴮ S i₂ ⊔ S i₂ ⊆ᴮ S i₁

    by_cases heq : i₁ = i₂
    ·
      subst heq
      apply le_sup_of_le_left
      exact le_of_eq (subset_self_eq_top (x := S i₁)).symm
    ·
      have hchain := C_chain H₁ H₂ heq
      cases hchain with
      | inl h =>
        apply le_sup_of_le_left
        exact le_of_eq (subset'_unfold.mp h).symm
      | inr h =>
        apply le_sup_of_le_right
        exact le_of_eq (subset'_unfold.mp h).symm

  have H_C'_sub_X : (⊤ : 𝔹) ≤ C' ⊆ᴮ X := by
    rw [hC'_def, subset_unfold]
    apply le_iInf; intro ⟨i, hi⟩
    rw [show (bSet_of_core_set h_core C).bval ⟨i, hi⟩ = ⊤ from rfl, top_imp]
    exact top_le_iff.mpr (h_core.1 i)

  have H_chain_quant : (⊤ : 𝔹) ≤ ⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
      w₁ ∈ᴮ C' ⊓ w₂ ∈ᴮ C' ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁) := by
    rw [← forall_forall_reindex (fun x y => x ⊆ᴮ y ⊔ y ⊆ᴮ x)
        (h₁ := fun x => B_ext_subset_or_subset_right x)
        (h₂ := fun y => B_ext_subset_or_subset_left y)]
    exact H_internal_chain

  have H_internal_ub_mem : (⊤ : 𝔹) ≤ bv_union C' ∈ᴮ X := by
    apply bv_context_apply (le_trans H (iInf_le _ C'))
    exact le_inf H_C'_sub_X H_chain_quant

  have H_internal_ub_spec : ∀ i_w : C,
      (⊤ : 𝔹) ≤ S i_w.val ⊆ᴮ bv_union C' := by
    intro ⟨i_w, H_i_w⟩

    have hmem : (⊤ : 𝔹) ≤ C'.func ⟨i_w, H_i_w⟩ ∈ᴮ C' :=
      le_trans (le_of_eq (of_core_bval (i := ⟨i_w, H_i_w⟩)).symm)
               (mem_mk' C' ⟨i_w, H_i_w⟩)

    have hspec : (⊤ : 𝔹) ≤ C'.func ⟨i_w, H_i_w⟩ ∈ᴮ C' ⟹ C'.func ⟨i_w, H_i_w⟩ ⊆ᴮ bv_union C' :=
      (bv_union_spec'' C').trans (iInf_le _ (C'.func ⟨i_w, H_i_w⟩))
    exact le_trans (le_inf hspec hmem) bv_imp_elim

  have H_ub_mem : bv_union C' ∈ᴮ X = ⊤ := top_unique H_internal_ub_mem
  obtain ⟨w, H_w⟩ := core_witness h_core (bv_union C') H_ub_mem

  refine ⟨w, fun x_w' H_x_w' => ?_⟩

  show subset' h_core x_w' w
  rw [subset'_unfold]
  apply top_unique

  have h_ub_spec : (⊤ : 𝔹) ≤ S x_w' ⊆ᴮ bv_union C' :=
    H_internal_ub_spec ⟨x_w', H_x_w'⟩

  calc (⊤ : 𝔹) ≤ S x_w' ⊆ᴮ bv_union C' ⊓ bv_union C' =ᴮ S w :=
          le_inf h_ub_spec (le_of_eq H_w.symm)
    _ ≤ S x_w' ⊆ᴮ S w := subst_congr_subset_right

theorem bSet_zorns_lemma (X : bSet 𝔹) (H_nonempty : (X =ᴮ ∅)ᶜ = ⊤)
    (H : ⊤ ≤ zorn_chain_hyp X) :
    ⊤ ≤ ⨆ c, c ∈ᴮ X ⊓ ⨅ z, z ∈ᴮ X ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z) := by

  obtain ⟨α, S, h_core⟩ := core.mk X

  letI hPO := subset'_partial_order h_core
  have H_zorn := @zorn_le α hPO.toPreorder (subset'_inductive X H h_core)
  obtain ⟨c, H_c⟩ := H_zorn

  have H_c_in_X : S c ∈ᴮ X = ⊤ := h_core.1 c

  have aux : ∀ (a : α), S a ∈ᴮ X = ⊤ → S c ⊆ᴮ S a ≤ S a =ᴮ S c := by
    intro a H_a

    set p := S c ⊆ᴮ S a with hp_def
    have h_anti : p ⊓ pᶜ = ⊥ := inf_compl_eq_bot
    have h_partition : p ⊔ pᶜ = ⊤ := sup_compl_eq_top
    set v := two_term_mixture p pᶜ h_anti (S a) (S c) with hv_def

    have claim_1 : v ∈ᴮ X = ⊤ :=
      two_term_mixture_mem_top X (S a) (S c) p pᶜ h_anti h_partition H_a H_c_in_X

    obtain ⟨z, H_z⟩ := core_witness h_core v claim_1

    have claim_3 : (⊤ : 𝔹) ≤ S c ⊆ᴮ v :=
      two_term_mixture_subset_top (S a) (S c) p pᶜ h_anti h_partition hp_def

    have claim_4 : c ≤ z := by
      show subset' h_core c z
      rw [subset'_unfold]
      apply top_unique
      calc (⊤ : 𝔹) ≤ S c ⊆ᴮ v ⊓ v =ᴮ S z :=
              le_inf claim_3 (le_of_eq H_z.symm)
        _ ≤ S c ⊆ᴮ S z := subst_congr_subset_right

    have claim_5 : S c =ᴮ S z = ⊤ := by
      have hz_le_c : z ≤ c := H_c claim_4
      apply top_unique
      rw [eq_iff_subset_subset]
      apply le_inf
      ·
        exact le_of_eq (subset'_unfold.mp claim_4).symm
      ·
        exact le_of_eq (subset'_unfold.mp hz_le_c).symm

    have hSz_eq_Sc : S z =ᴮ S c = ⊤ := by rw [bv_eq_symm]; exact claim_5
    have claim_6 : (⊤ : 𝔹) ≤ v =ᴮ S c := by
      calc (⊤ : 𝔹) ≤ v =ᴮ S z ⊓ S z =ᴮ S c :=
              le_inf (le_of_eq H_z.symm) (le_of_eq hSz_eq_Sc.symm)
        _ ≤ v =ᴮ S c := bv_eq_trans

    have mixing := mixing_lemma_two_term p pᶜ h_anti (S a) (S c)

    calc p ≤ v =ᴮ S a := mixing.1
      _ = S a =ᴮ v := bv_eq_symm
      _ ≤ S a =ᴮ S c := by
          calc S a =ᴮ v ≤ S a =ᴮ v ⊓ v =ᴮ S c :=
                  le_inf le_rfl (le_top.trans claim_6)
            _ ≤ S a =ᴮ S c := bv_eq_trans

  apply bv_use (S c)
  rw [H_c_in_X, top_inf_eq]

  apply le_iInf; intro x
  rw [← deduction, top_inf_eq, ← deduction]

  obtain ⟨y, H₁_y, H₂_y⟩ := core_aux_lemma3 X H_nonempty S h_core x
  obtain ⟨a, -, rfl⟩ := H₁_y

  have H₂_y_le : x ∈ᴮ X ≤ x =ᴮ S a := le_of_eq H₂_y.symm
  have h_Sc_sub_Sa : x ∈ᴮ X ⊓ S c ⊆ᴮ x ≤ S c ⊆ᴮ S a :=
    calc x ∈ᴮ X ⊓ S c ⊆ᴮ x
        ≤ x =ᴮ S a ⊓ S c ⊆ᴮ x :=
            le_inf (inf_le_left.trans H₂_y_le) inf_le_right
      _ ≤ S c ⊆ᴮ S a := by
            rw [inf_comm]; exact subst_congr_subset_right
  have h_Sa_eq_Sc : S c ⊆ᴮ S a ≤ S a =ᴮ S c :=
    aux a (core_mem_of_mem_image h_core ⟨a, Set.mem_univ _, rfl⟩)
  calc x ∈ᴮ X ⊓ S c ⊆ᴮ x
      ≤ x =ᴮ S a ⊓ S a =ᴮ S c := by
          apply le_inf
          · exact inf_le_left.trans H₂_y_le
          · exact h_Sc_sub_Sa.trans h_Sa_eq_Sc
    _ ≤ x =ᴮ S c := bv_eq_trans
    _ = S c =ᴮ x := bv_eq_symm

end zorns_lemma

section comprehension
variable (ϕ : bSet 𝔹 → 𝔹) (x : bSet 𝔹) (H_congr : B_ext ϕ)

@[reducible] def comprehend : bSet 𝔹 := subset.mk (fun i : x.type => ϕ (x.func i))

lemma mem_comprehend_iff : ∀ {z : bSet 𝔹} {Γ : 𝔹}, Γ ≤ z ∈ᴮ comprehend ϕ x ↔
    Γ ≤ ⨆ (i : x.type), x.bval i ⊓ (z =ᴮ x.func i ⊓ (fun i : x.type => ϕ (x.func i)) i) := by
  intros; exact mem_subset.mk_iff₂

include H_congr in
lemma mem_comprehend_iff₂ : ∀ {z : bSet 𝔹} {Γ : 𝔹}, Γ ≤ z ∈ᴮ comprehend ϕ x ↔
    Γ ≤ ⨆ w, w ∈ᴮ x ⊓ (z =ᴮ w ⊓ ϕ w) := by
  intro z Γ
  rw [mem_comprehend_iff]

  have h_cong : ∀ a b : bSet 𝔹, a =ᴮ b ⊓ (z =ᴮ a ⊓ ϕ a) ≤ z =ᴮ b ⊓ ϕ b := by
    intro a b
    apply le_inf
    ·
      calc a =ᴮ b ⊓ (z =ᴮ a ⊓ ϕ a)
          ≤ a =ᴮ b ⊓ z =ᴮ a := inf_le_inf_left _ inf_le_left
        _ = z =ᴮ a ⊓ a =ᴮ b := by rw [inf_comm]
        _ ≤ z =ᴮ b := bv_eq_trans
    · exact le_trans (inf_le_inf_left _ inf_le_right) (H_congr a b)
  rw [← @bounded_exists _ _ x (fun w => z =ᴮ w ⊓ ϕ w) (h_congr := h_cong)]

include H_congr in
lemma B_congr_comprehend : B_congr (fun x : bSet 𝔹 => comprehend ϕ x) := by
  intro a b Γ H_eq
  apply mem_ext
  ·
    apply le_iInf; intro z; rw [← deduction]

    have ha : z ∈ᴮ comprehend ϕ a = ⨆ w, w ∈ᴮ a ⊓ (z =ᴮ w ⊓ ϕ w) :=
      le_antisymm ((mem_comprehend_iff₂ ϕ a H_congr (Γ := _)).mp le_rfl)
                  ((mem_comprehend_iff₂ ϕ a H_congr (Γ := _)).mpr le_rfl)
    have hb : z ∈ᴮ comprehend ϕ b = ⨆ w, w ∈ᴮ b ⊓ (z =ᴮ w ⊓ ϕ w) :=
      le_antisymm ((mem_comprehend_iff₂ ϕ b H_congr (Γ := _)).mp le_rfl)
                  ((mem_comprehend_iff₂ ϕ b H_congr (Γ := _)).mpr le_rfl)
    rw [ha, hb, inf_iSup_eq]
    apply iSup_le; intro w; apply le_iSup_of_le w

    apply le_inf
    · calc Γ ⊓ (w ∈ᴮ a ⊓ (z =ᴮ w ⊓ ϕ w))
          ≤ Γ ⊓ w ∈ᴮ a := inf_le_inf_left _ inf_le_left
        _ ≤ a =ᴮ b ⊓ w ∈ᴮ a := inf_le_inf_right _ H_eq
        _ ≤ w ∈ᴮ b := subst_congr_mem_right
    · exact le_trans (inf_le_inf_left _ inf_le_right) inf_le_right
  · apply le_iInf; intro z; rw [← deduction]
    have ha : z ∈ᴮ comprehend ϕ a = ⨆ w, w ∈ᴮ a ⊓ (z =ᴮ w ⊓ ϕ w) :=
      le_antisymm ((mem_comprehend_iff₂ ϕ a H_congr (Γ := _)).mp le_rfl)
                  ((mem_comprehend_iff₂ ϕ a H_congr (Γ := _)).mpr le_rfl)
    have hb : z ∈ᴮ comprehend ϕ b = ⨆ w, w ∈ᴮ b ⊓ (z =ᴮ w ⊓ ϕ w) :=
      le_antisymm ((mem_comprehend_iff₂ ϕ b H_congr (Γ := _)).mp le_rfl)
                  ((mem_comprehend_iff₂ ϕ b H_congr (Γ := _)).mpr le_rfl)
    rw [hb, ha, inf_iSup_eq]
    apply iSup_le; intro w; apply le_iSup_of_le w

    apply le_inf
    · calc Γ ⊓ (w ∈ᴮ b ⊓ (z =ᴮ w ⊓ ϕ w))
          ≤ Γ ⊓ w ∈ᴮ b := inf_le_inf_left _ inf_le_left
        _ ≤ b =ᴮ a ⊓ w ∈ᴮ b := inf_le_inf_right _ (H_eq.trans (le_of_eq bv_eq_symm))
        _ ≤ w ∈ᴮ a := subst_congr_mem_right
    · exact le_trans (inf_le_inf_left _ inf_le_right) inf_le_right

variable {ϕ} {H_congr}

lemma comprehend_subset {Γ : 𝔹} : Γ ≤ comprehend ϕ x ⊆ᴮ x := by
  exact subset.mk_subset

variable (ϕ) (H_congr)

include H_congr in

lemma bSet_axiom_of_comprehension {Γ : 𝔹} :
    Γ ≤ ⨆ y, (y ⊆ᴮ x ⊓ ⨅ z, ((z ∈ᴮ y) ⇔ (z ∈ᴮ x ⊓ ϕ z))) := by
  apply bv_use (comprehend ϕ x)
  apply le_inf
  · exact @comprehend_subset 𝔹 _ ϕ x Γ
  · apply le_iInf; intro z
    rw [bv_biimp_iff]
    intro Γ' _
    constructor
    · intro H

      have hsupr := (mem_comprehend_iff₂ ϕ x H_congr (Γ := Γ')).mp H

      apply le_trans (a := Γ') hsupr
      apply iSup_le; intro w

      have hmem : w ∈ᴮ x ⊓ (z =ᴮ w ⊓ ϕ w) ≤ w ∈ᴮ x := inf_le_left
      have heq : w ∈ᴮ x ⊓ (z =ᴮ w ⊓ ϕ w) ≤ z =ᴮ w := inf_le_right.trans inf_le_left
      have hϕ : w ∈ᴮ x ⊓ (z =ᴮ w ⊓ ϕ w) ≤ ϕ w := inf_le_right.trans inf_le_right
      exact le_inf
        (bv_rw' (H := heq) (h_congr := B_ext_mem_left (y := x)) (H_new := hmem))
        (bv_rw' (H := heq) (h_congr := H_congr) (H_new := hϕ))
    · intro H

      apply (mem_comprehend_iff₂ ϕ x H_congr (Γ := Γ')).mpr
      apply le_iSup_of_le z
      exact le_inf (H.trans inf_le_left) (le_inf bv_refl (H.trans inf_le_right))

end comprehension

def dom : ∀ _ : bSet 𝔹, PSet.{u}
  | ⟨α, A, _⟩ => ⟨α, fun i => dom (A i)⟩

@[reducible] def check_shadow : bSet 𝔹 → bSet 𝔹 := fun x => check (dom x)

lemma check_shadow_type {x : bSet 𝔹} : (check_shadow x).type = x.type := by
  cases x; rfl

@[reducible] def check_shadow_cast {x : bSet 𝔹} : (check_shadow x).type → x.type :=
  cast check_shadow_type

@[reducible] def check_shadow_cast_symm {x : bSet 𝔹} : x.type → (check_shadow x).type :=
  cast check_shadow_type.symm

lemma dom_check : ∀ {x : PSet.{u}}, dom (check x : bSet 𝔹) = x := by
  intro x
  induction x with
  | mk α A ih => simp [dom, check, ih]

lemma dom_left_inv_check : Function.LeftInverse dom (check : PSet.{u} → bSet 𝔹) :=
  fun x => dom_check

lemma check_injective : Function.Injective (check : PSet.{u} → bSet 𝔹) :=
  Function.LeftInverse.injective dom_left_inv_check

end bSet
