/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Modified for Lean and Mathlib 4.36.0.

import Flypitch4.BvmExtras
import Flypitch4.CantorSpace
import Mathlib.SetTheory.Cardinal.Pigeonhole

abbrev Finset.toSet {α : Type*} (s : Finset α) : Set α := ↑s

open scoped Cardinal
open Flypitch Flypitch.Regular

universe u

namespace bSet

section cardinal_preservation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

lemma AE_of_check_larger_than_check'' {x y : PSet.{u}} (f : bSet 𝔹) {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ is_surj_onto (check x) (check y) f)
    (H_nonempty : ∃ z, z ∈ y) :
    ∀ i : y.Type, ∃ j : x.Type, ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by
  intro i

  have H_func' : Γ ≤ is_func' (check x) (check y) f := le_trans H inf_le_left
  have H_surj : Γ ≤ is_surj (check x) (check y) f := le_trans H inf_le_right

  have H_surj_i : Γ ≤ ⨆ w, w ∈ᴮ check x ⊓ pair w (check (y.Func i)) ∈ᴮ f := by
    have h_step := le_trans H_surj (iInf_le (f := fun v => v ∈ᴮ check y ⟹
        ⨆ w, w ∈ᴮ check x ⊓ pair w v ∈ᴮ f) (check (y.Func i)))
    exact le_trans (le_inf h_step mem_check_of_mem) (imp_inf_le _ _)

  rw [← @bounded_exists 𝔹 _ (check x) (fun w => pair w (check (y.Func i)) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)] at H_surj_i
  simp only [check_bval_top, top_inf_eq] at H_surj_i

  have H_combined : ⊥ < ⨆ j : (check x : bSet 𝔹).type,
      is_func f ⊓ pair ((check x : bSet 𝔹).func j) (check (y.Func i)) ∈ᴮ f := by
    apply lt_of_lt_of_le H_nonzero
    calc Γ
        ≤ is_func' (check x) (check y) f ⊓ ⨆ j, pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          le_inf H_func' H_surj_i
      _ = ⨆ j, is_func' (check x) (check y) f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          inf_iSup_eq'
      _ ≤ ⨆ j, is_func f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          iSup_mono fun j => le_inf (is_func_of_is_func' inf_le_left) inf_le_right
  obtain ⟨j, Hj⟩ := nonzero_wit H_combined
  exact ⟨check_cast j, by rwa [← check_func]⟩

lemma AE_of_check_larger_than_check' {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ surjects_onto (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by

  simp only [surjects_onto] at H
  obtain ⟨f, Hf⟩ := nonzero_wit' H_nonzero H

  have Hf_nonzero : ⊥ < is_surj_onto (check x) (check y) f ⊓ Γ := Hf
  have Hf_le : is_surj_onto (check x) (check y) f ⊓ Γ ≤ is_surj_onto (check x) (check y) f :=
    inf_le_left
  exact ⟨f, AE_of_check_larger_than_check'' f Hf_nonzero Hf_le H_mem⟩

lemma AE_of_check_larger_than_check {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ larger_than (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f :=
  AE_of_check_larger_than_check' H_nonzero
    (surjects_onto_of_larger_than_and_exists_mem H
      (by obtain ⟨z, hz⟩ := H_mem; exact le_trans le_top (le_iSup_of_le (check z) (check_mem hz))))
    H_mem

variable
  (η₁ η₂ : PSet.{u}) (H_infinite : Cardinal.aleph0 ≤ #(η₁.Type))
  (H_lt : #(η₁.Type) < #(η₂.Type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
  (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
  (H : ∀ β : η₂.Type, (⊥ : 𝔹) < is_func f ⊓ pair (check (η₁.Func (g β))) (check (η₂.Func β)) ∈ᴮ f)

include H_infinite H_lt H_inj₂ f H in

lemma not_CCC_of_uncountable_fiber
    (H_ex : ∃ ξ : η₁.Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ})) : ¬ CCC 𝔹 := by
  obtain ⟨ξ, H_ξ⟩ := H_ex
  let 𝓐 : (g⁻¹' {ξ}) → 𝔹 :=
    fun β => is_func f ⊓ pair (check (η₁.Func (g β.val))) (check (η₂.Func β.val)) ∈ᴮ f
  have 𝓐_nontriv : ∀ β, ⊥ < 𝓐 β := fun β => H β.val
  have 𝓐_anti : ∀ β₁ β₂ : (g⁻¹' {ξ}), β₁ ≠ β₂ → 𝓐 β₁ ⊓ 𝓐 β₂ ≤ ⊥ := by
    intro β₁ β₂ h_sep
    apply poset_yoneda; intro Γ a
    simp only [le_inf_iff] at a
    obtain ⟨ha₁, ha₂⟩ := a
    obtain ⟨H_func₁, H_mem₁⟩ := le_inf_iff.mp ha₁
    obtain ⟨_, H_mem₂⟩ := le_inf_iff.mp ha₂
    have hg₁ : g β₁.val = ξ := β₁.property
    have hg₂ : g β₂.val = ξ := β₂.property
    rw [hg₁] at H_mem₁; rw [hg₂] at H_mem₂
    have H_le_eq : Γ ≤ check (η₂.Func β₁.val) =ᴮ check (η₂.Func β₂.val) :=
      eq_of_is_func_of_eq H_func₁ bv_refl H_mem₁ H_mem₂
    apply le_trans H_le_eq
    rw [le_bot_iff]
    exact check_bv_eq_bot_of_not_equiv (H_inj₂ _ _ (fun heq => h_sep (Subtype.ext heq)))
  intro H_CCC
  exact absurd (le_antisymm (lt_iff_le_and_ne.mp H_ξ).1
    (H_CCC _ 𝓐 𝓐_nontriv 𝓐_anti)) (lt_iff_le_and_ne.mp H_ξ).2

end cardinal_preservation

end bSet

open bSet

namespace PSet

@[reducible] noncomputable def pSet_aleph1 : PSet.{0} := ordinalMk (Cardinal.aleph 1).ord

@[reducible] noncomputable def pSet_aleph2 : PSet.{0} := ordinalMk (Cardinal.aleph 2).ord

lemma pSet_aleph2_unfold : pSet_aleph2 = ⟨pSet_aleph2.Type, pSet_aleph2.Func⟩ := by
  cases pSet_aleph2; rfl

end PSet

open PSet

noncomputable def 𝔹_cohen : Type :=
  @Flypitch.RegularOpens (Set (PSet.pSet_aleph2.Type × ℕ)) inferInstance

local notation "𝔹" => 𝔹_cohen

instance H_nonempty : Nonempty (Set (PSet.pSet_aleph2.Type × ℕ)) := ⟨∅⟩

noncomputable instance 𝔹_boolean_algebra :
    NontrivialCompleteBooleanAlgebra 𝔹 :=
  @Flypitch.RegularOpens.instNontrivialCBA _ _ H_nonempty

lemma le_iff_subset' {x y : 𝔹} : x ≤ y ↔ x.val ⊆ y.val :=
  Flypitch.RegularOpens.le_iff_subset

lemma bot_eq_empty : (⊥ : 𝔹) = ⟨∅, isRegularOpen_empty⟩ := by
  apply Flypitch.RegularOpens.ext; rfl

private lemma eq₀ : (check (PSet.pSet_aleph2) : bSet 𝔹).type = PSet.pSet_aleph2.Type :=
  check_type'

private lemma eq₁ :
    ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg (· × ℕ) eq₀

private lemma eq₂ :
    Set ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Set (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Set eq₁

private lemma eq₃ :
    Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Finset (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Finset eq₁

universe w in
lemma pi₂_cast₁ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    HEq p.1 q.1 := by
  subst H'; exact heq_of_eq (congr_arg Prod.fst (eq_of_heq H))

universe w in
lemma pi₂_cast₂ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    p.2 = q.2 := by
  subst H'; exact congr_arg Prod.snd (eq_of_heq H)

universe w in
lemma compl_cast₂ {α β : Type w} {a : Set α} {b : Set β} (H' : α = β) (H : HEq aᶜ b) :
    HEq a bᶜ := by
  subst H'; exact heq_of_eq ((eq_of_heq H) ▸ (compl_compl a).symm)

lemma eq₁_cast (p : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) :
    cast eq₁ p = (cast eq₀ p.1, p.2) := by

  have hcast : HEq p (cast eq₁ p) := (cast_heq eq₁ p).symm
  apply Prod.ext
  ·

    apply eq_of_heq
    exact (pi₂_cast₁ eq₀ hcast).symm.trans (cast_heq eq₀ p.1).symm
  · exact (pi₂_cast₂ eq₀ hcast).symm

lemma eq₁_cast' (p : PSet.pSet_aleph2.Type × ℕ) :
    cast eq₁.symm p = (cast eq₀.symm p.1, p.2) := by
  have hcast : HEq p (cast eq₁.symm p) := (cast_heq eq₁.symm p).symm
  apply Prod.ext
  · apply eq_of_heq
    exact (pi₂_cast₁ eq₀.symm hcast).symm.trans (cast_heq eq₀.symm p.1).symm
  · exact (pi₂_cast₂ eq₀.symm hcast).symm

theorem 𝔹_CCC : CCC 𝔹 :=
  Flypitch.RegularOpens.CCC_regular_opens CantorSpace.countable_chain_condition_set

local notation "𝒳" => Set (PSet.pSet_aleph2.Type × ℕ)

noncomputable def principal_open (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
  ⟨CantorSpace.principalOpen (cast eq₁ (ν, n)),
   isRegularOpen_of_isClopen CantorSpace.isClopen_principalOpen⟩

lemma is_clopen_principal_open {ν n} : IsClopen (principal_open ν n).val :=
  CantorSpace.isClopen_principalOpen

lemma perp_eq_compl_of_clopen {β : Type*} [TopologicalSpace β] {S : Set β}
    (H : IsClopen S) : Sᵖ = Sᶜ := by
  unfold Flypitch.perp; rw [IsClosed.closure_eq H.1]

lemma mem_neg_principal_open_of_not_mem {ν n S} :
    (cast eq₁ (ν, n) ∈ Sᶜ) → S ∈ ((principal_open ν n)ᶜ).val := by
  intro H

  have hval : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᶜ := by
    have h1 : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᵖ :=
      Flypitch.RegularOpens.compl_val (principal_open ν n)
    rw [h1, perp_eq_compl_of_clopen is_clopen_principal_open]
  rw [hval]

  simp only [Set.mem_compl_iff, principal_open, CantorSpace.principalOpen, Set.mem_ofPred_eq]
  exact H

structure 𝒞 : Type where
  ins : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  out : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  H : ins ∩ out = ∅

@[reducible] def π₂ : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ → ℕ := fun x => x.2

private noncomputable def ι : 𝒞 → 𝔹 :=
  fun p => ⟨{S | (p.ins.toSet) ⊆ (cast eq₂.symm S) ∧
                  (p.out.toSet) ⊆ (cast eq₂.symm Sᶜ)},
    isRegularOpen_of_isClopen (by

      have cast_mem_iff : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
          x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp

      have hset : {S : Set (PSet.pSet_aleph2.Type × ℕ) |
                    p.ins.toSet ⊆ cast eq₂.symm S ∧ p.out.toSet ⊆ cast eq₂.symm Sᶜ} =
                  CantorSpace.principalOpenFinset (cast eq₃ p.ins) ∩
                  CantorSpace.coPrincipalOpenFinset (cast eq₃ p.out) := by
        ext S
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, CantorSpace.mem_principalOpenFinset_iff,
          CantorSpace.coPrincipalOpenFinset, Set.mem_ofPred_eq]

        have cast_finset_mem : ∀ (F : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ))
            (x : PSet.pSet_aleph2.Type × ℕ),
            x ∈ (cast eq₃ F : Finset (PSet.pSet_aleph2.Type × ℕ)) ↔ cast eq₁.symm x ∈ F := by
          intro F x

          have key : ∀ {A B : Type} (h : A = B) (F : Finset A) (x : B),
              x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F := by
            intro A B h; subst h; intro F x; simp
          have heq : eq₃ = congr_arg Finset eq₁ := rfl
          rw [heq]; exact key eq₁ F x
        constructor
        · intro ⟨h₁, h₂⟩
          constructor
          ·
            intro x hx
            rw [Finset.mem_coe, cast_finset_mem] at hx

            have hmem := (cast_mem_iff eq₁ S (cast eq₁.symm x)).mp (h₁ (Finset.mem_coe.mpr hx))

            have hx_eq : cast eq₁ (cast eq₁.symm x) = x := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm x
            rw [hx_eq] at hmem; exact hmem
          · intro x hx
            rw [Finset.mem_coe, cast_finset_mem] at hx
            have hmem := (cast_mem_iff eq₁ Sᶜ (cast eq₁.symm x)).mp (h₂ (Finset.mem_coe.mpr hx))
            have hx_eq : cast eq₁ (cast eq₁.symm x) = x := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm x
            rw [hx_eq] at hmem; exact hmem
        · intro ⟨h₁, h₂⟩
          constructor
          · intro y hy
            rw [cast_mem_iff eq₁]
            apply h₁
            rw [Finset.mem_coe, cast_finset_mem]

            have hcast : cast eq₁.symm (cast eq₁ y) = y := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁ y
            rw [hcast]; exact hy
          · intro y hy
            rw [cast_mem_iff eq₁]
            apply h₂
            rw [Finset.mem_coe, cast_finset_mem]
            have hcast : cast eq₁.symm (cast eq₁ y) = y := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁ y
            rw [hcast]; exact hy
      rw [hset]
      exact (CantorSpace.isClopen_principalOpenFinset _).inter
        (CantorSpace.isClopen_coPrincipalOpenFinset _))⟩

open CantorSpace

universe w₁ in
lemma prop_decidable_cast_lemma {α β : Type w₁} (H : α = β) {a b : α} {a' b' : β}
    (H_a : HEq a a') (H_b : HEq b b') :
    HEq (Classical.propDecidable (a = b)) (Classical.propDecidable (a' = b')) := by
  subst H; cases H_a; cases H_b; rfl

lemma 𝒞_dense_basis : ∀ T ∈ @standardBasis (PSet.pSet_aleph2.Type × ℕ), ∀ _h : T ≠ ∅,
    ∃ p : 𝒞, (ι p).val ⊆ T := by
  intro T hT _h
  simp only [standardBasis, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hT
  rcases hT with ⟨p_ins, p_out, hTeq, hDisj⟩ | hTe
  ·

    have key_finset_mem : ∀ {A B : Type} (h : A = B) (F : Finset A) (x : B),
        x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F := by
      intro A B h; subst h; intro F x; simp

    have key_set_mem : ∀ {A B : Type} (h : A = B) (S : Set B) (x : A),
        x ∈ cast (congr_arg Set h).symm S ↔ cast h x ∈ S := by
      intro A B h; subst h; intro S x; simp

    have cast_finset_symm : ∀ (F' : Finset (PSet.pSet_aleph2.Type × ℕ))
        (a : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ),
        a ∈ (cast eq₃.symm F' : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)) ↔ cast eq₁ a ∈ F' := by
      intro F' a

      have heq : eq₃.symm = congr_arg Finset eq₁.symm := rfl
      rw [heq, key_finset_mem eq₁.symm F' a]

    have cast_set_symm : ∀ (S : Set (PSet.pSet_aleph2.Type × ℕ))
        (a : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ),
        a ∈ cast eq₂.symm S ↔ cast eq₁ a ∈ S := by
      intro S a
      have heq : eq₂.symm = (congr_arg Set eq₁).symm := by rfl
      rw [heq, key_set_mem eq₁ S a]

    let p' : 𝒞 :=
      { ins := cast eq₃.symm p_ins
        out := cast eq₃.symm p_out
        H := by
          have hd := Finset.disjoint_left.mp hDisj
          ext a
          simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
          intro ⟨ha1, ha2⟩
          exact hd ((cast_finset_symm p_ins a).mp ha1) ((cast_finset_symm p_out a).mp ha2) }
    refine ⟨p', ?_⟩

    rw [hTeq, ← principalOpenFinset_eq_inter, ← coPrincipalOpenFinset_eq_inter]
    intro S hS
    simp only [ι, Set.mem_ofPred_eq] at hS
    obtain ⟨hS_ins, hS_out⟩ := hS
    simp only [Set.mem_inter_iff, mem_principalOpenFinset_iff, coPrincipalOpenFinset,
      Set.mem_ofPred_eq]

    have cast_eq₁_symm_eq : ∀ (z : PSet.pSet_aleph2.Type × ℕ),
        cast eq₁ (cast eq₁.symm z) = z := by
      intro z; rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm z
    constructor
    · intro z hz

      have ha : cast eq₁.symm z ∈ p'.ins := (cast_finset_symm p_ins (cast eq₁.symm z)).mpr
        (by rw [cast_eq₁_symm_eq]; exact hz)
      have hmem := hS_ins (Finset.mem_coe.mpr ha)
      rw [cast_set_symm] at hmem
      rw [cast_eq₁_symm_eq] at hmem
      exact hmem
    · intro z hz hzS

      have ha : cast eq₁.symm z ∈ p'.out := (cast_finset_symm p_out (cast eq₁.symm z)).mpr
        (by rw [cast_eq₁_symm_eq]; exact hz)
      have hmem := hS_out (Finset.mem_coe.mpr ha)
      rw [cast_set_symm] at hmem
      rw [cast_eq₁_symm_eq] at hmem
      exact hmem hzS
  ·
    exact absurd hTe _h

lemma 𝒞_dense {b : 𝔹} (H : ⊥ < b) : ∃ p : 𝒞, ι p ≤ b := by
  have hne : b.val ≠ ∅ := by
    intro heq
    exact H.ne (Flypitch.RegularOpens.ext (Flypitch.RegularOpens.bot_val.trans heq.symm))
  obtain ⟨S_wit, H_wit⟩ := Set.nonempty_iff_ne_empty.mpr hne
  change ∃ p, (ι p).val ⊆ b.val
  rcases (is_topological_basis_standardBasis.exists_subset_of_mem_open H_wit
      (isOpen_of_isRegularOpen b.property))
    with ⟨v, Hv₁, Hv₂, Hv₃⟩
  obtain ⟨p, H_p⟩ := 𝒞_dense_basis v Hv₁ (fun hv => by rw [hv] at Hv₂; exact Hv₂)
  exact ⟨p, Set.Subset.trans H_p Hv₃⟩

lemma to_set_inter {α : Type*} {p₁ p₂ : Finset α} :
    (p₁ ∩ p₂).toSet = p₁.toSet ∩ p₂.toSet := by
  ext; simp [Finset.mem_coe, Finset.mem_inter]

lemma not_mem_of_inter_empty_left {α : Type*} {p₁ p₂ : Finset α}
    (H : p₁ ∩ p₂ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet := by
  intro H' H''
  have : a ∈ p₁.toSet ∩ p₂.toSet := ⟨H', H''⟩
  rw [← to_set_inter] at this
  rw [congr_arg Finset.toSet H] at this
  exact absurd this (by simp [Finset.toSet])

lemma not_mem_of_inter_empty_right {α : Type*} {p₁ p₂ : Finset α}
    (H : p₂ ∩ p₁ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet := by
  rw [Finset.inter_comm] at H; exact not_mem_of_inter_empty_left H

lemma 𝒞_nonzero (p : 𝒞) : ⊥ ≠ ι p := by

  intro H

  have hval_empty : (ι p).val = ∅ := by
    rw [← H]; exact Flypitch.RegularOpens.bot_val

  let S : 𝒳 := cast eq₂ p.ins.toSet
  have hS_mem : S ∈ (ι p).val := by
    simp only [ι, Set.mem_ofPred_eq]
    constructor
    ·
      intro x hx

      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T1) (x : T1),
          x ∈ cast (congr_arg Set h).symm (cast (congr_arg Set h) T) ↔ x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      exact (key eq₁ p.ins.toSet x).mpr hx
    ·
      intro x hx

      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T1) (x : T1),
          x ∈ cast (congr_arg Set h).symm (cast (congr_arg Set h) T)ᶜ ↔ x ∉ T := by
        intro T1 T2 h; subst h; intro T x; simp
      rw [key eq₁]

      intro h_ins
      have : x ∈ p.ins ∩ p.out := by
        simp only [Finset.mem_inter, Finset.mem_coe] at *
        exact ⟨h_ins, hx⟩
      rw [p.H] at this
      exact absurd this (Finset.notMem_empty _)

  exact absurd hS_mem (by rw [hval_empty]; simp)

lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : PSet.pSet_aleph2.Type,
    (cast eq₁.symm (ξ, n)) ∉ p.ins ∧ (cast eq₁.symm (ξ, n)) ∉ p.out := by

  let Y' := Finset.image π₂ (p.ins ∪ p.out)
  by_cases h_empty : (p.ins ∪ p.out) = ∅
  ·
    use 0; intro ξ
    have h_ins : p.ins = ∅ := Finset.subset_empty.mp (h_empty ▸ Finset.subset_union_left)
    have h_out : p.out = ∅ := Finset.subset_empty.mp (h_empty ▸ Finset.subset_union_right)
    refine ⟨?_, ?_⟩
    all_goals intro h
    · rw [h_ins] at h; exact Finset.notMem_empty _ h
    · rw [h_out] at h; exact Finset.notMem_empty _ h
  ·
    have h_Y'_nonempty : Y'.Nonempty := by
      apply Finset.Nonempty.image
      exact Finset.nonempty_of_ne_empty h_empty
    let N := Y'.max' h_Y'_nonempty
    use N + 1
    intro ξ
    constructor
    · intro H_mem
      rw [eq₁_cast'] at H_mem
      have hNmem : N + 1 ∈ Y' := by
        simp only [Y', Finset.mem_image]
        exact ⟨_, Finset.mem_union_left _ H_mem, rfl⟩
      exact Nat.not_succ_le_self N (Finset.le_max' _ _ hNmem)
    · intro H_mem
      rw [eq₁_cast'] at H_mem
      have hNmem : N + 1 ∈ Y' := by
        simp only [Y', Finset.mem_image]
        exact ⟨_, Finset.mem_union_right _ H_mem, rfl⟩
      exact Nat.not_succ_le_self N (Finset.le_max' _ _ hNmem)

lemma 𝒞_anti {p₁ p₂ : 𝒞} : p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → ι p₂ ≤ ι p₁ := by
  intro H₁ H₂
  intro S hS
  obtain ⟨hS₁, hS₂⟩ := hS
  exact ⟨fun x hx => hS₁ (H₁ hx), fun x hx => hS₂ (H₂ hx)⟩

namespace bSet

namespace cohen_real

noncomputable def χ (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : ℕ → 𝔹 :=
  fun n => principal_open ν n

noncomputable def mk (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : bSet 𝔹 :=
  @set_of_indicator 𝔹 _ omega (fun n => χ ν n.down)

@[simp] lemma mk_type {ν} : (mk ν).type = ULift ℕ := rfl

@[simp] lemma mk_func {ν} {n} : (mk ν).func n = of_nat (n.down) := rfl

@[simp] lemma mk_bval {ν} {n} : (mk ν).bval n = (χ ν) (n.down) := rfl

lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ omega := by
  rw [subset_unfold]
  apply le_iInf; intro i
  rw [← deduction]
  simp only [mk_bval, mk_func]

  exact le_trans inf_le_left (le_trans le_top omega_definite)

lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

lemma sep {n} {Γ} {ν₁ ν₂} (H₁ : Γ ≤ of_nat n ∈ᴮ mk ν₁)
    (H₂ : Γ ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ) :
    Γ ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ := by

  apply le_neg_of_inf_eq_bot
  rw [le_antisymm_iff]; constructor
  ·
    apply le_bot_iff.mpr

    rw [eq_bot_iff]
    have hmem : mk ν₁ =ᴮ mk ν₂ ⊓ Γ ≤ of_nat n ∈ᴮ mk ν₂ :=
      le_trans (le_inf inf_le_left (le_trans inf_le_right H₁)) subst_congr_mem_right
    exact le_trans (le_inf hmem (le_trans inf_le_right H₂)) inf_compl_eq_bot.le
  · exact bot_le

lemma not_mem_of_not_mem {p : 𝒞} {ν} {n} (H : (ν, n) ∈ p.out) :
    ι p ≤ (of_nat n ∈ᴮ mk ν)ᶜ := by
  rw [mem_unfold, compl_iSup]
  apply le_iInf; intro k
  rw [compl_inf]
  by_cases hk : n = k.down
  · subst hk
    simp only [mk_bval, mk_func]
    rw [bv_eq_refl, compl_top, sup_bot_eq]
    intro S hS
    apply mem_neg_principal_open_of_not_mem
    have hS₂ := hS.2 (Finset.mem_coe.mpr H)
    have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
        x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
      intro T1 T2 h; subst h; intro T x; simp
    exact (key eq₁ Sᶜ (ν, k.down)).mp hS₂
  · have : of_nat n =ᴮ (of_nat k.down : bSet 𝔹) = ⊥ := of_nat_inj' hk
    simp only [mk_bval, mk_func, this, compl_bot, sup_top_eq]; exact le_top

private lemma inj_cast_lemma (ν' : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n' : ℕ) :
    cast eq₁.symm (cast eq₀ ν', n') = (ν', n') := by
  rw [eq₁_cast']; simp [cast_cast]

lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : mk ν₁ =ᴮ mk ν₂ ≤ (⊥ : 𝔹) := by
  by_contra h
  replace h : ⊥ < mk ν₁ =ᴮ mk ν₂ := lt_of_le_of_ne bot_le (Ne.symm (mt le_bot_iff.mpr h))
  obtain ⟨p, H_p⟩ := 𝒞_dense h
  obtain ⟨n, H_n⟩ := 𝒞_disjoint_row p

  have Hν₁_ins : (ν₁, n) ∉ p.ins := by
    have := (H_n (cast eq₀ ν₁)).1
    rwa [inj_cast_lemma] at this
  have Hν₁_out : (ν₁, n) ∉ p.out := by
    have := (H_n (cast eq₀ ν₁)).2
    rwa [inj_cast_lemma] at this
  have Hν₂_ins : (ν₂, n) ∉ p.ins := by
    have := (H_n (cast eq₀ ν₂)).1
    rwa [inj_cast_lemma] at this
  have Hν₂_out : (ν₂, n) ∉ p.out := by
    have := (H_n (cast eq₀ ν₂)).2
    rwa [inj_cast_lemma] at this
  let p' : 𝒞 :=
    { ins := insert (ν₁, n) p.ins
      out := insert (ν₂, n) p.out
      H := by
        ext a
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨ha_ins, ha_out⟩
        simp only [Finset.mem_insert] at ha_ins ha_out
        rcases ha_ins with rfl | ha_ins
        ·
          rcases ha_out with h_eq | ha_out
          ·
            exact H_neq (Prod.mk.inj h_eq).1
          · exact Hν₁_out ha_out
        ·
          rcases ha_out with rfl | ha_out
          ·
            exact Hν₂_ins ha_ins
          ·
            have : a ∈ p.ins ∩ p.out := Finset.mem_inter.mpr ⟨ha_ins, ha_out⟩
            rw [p.H] at this
            exact Finset.notMem_empty _ this }

  have anti : ι p' ≤ ι p :=
    𝒞_anti (fun i hi => Finset.mem_insert_of_mem hi)
           (fun i hi => Finset.mem_insert_of_mem hi)

  have this₁ : ι p' ≤ of_nat n ∈ᴮ mk ν₁ := by
    rw [mem_unfold]
    apply le_iSup_of_le (ULift.up n)
    simp only [mk_bval, mk_func, χ, bv_refl, le_inf_iff]
    constructor
    ·
      intro S hS
      simp only [ι, Set.mem_ofPred_eq] at hS
      have hins : (ν₁, n) ∈ (p' : 𝒞).ins.toSet :=
        Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
      have hmem := hS.1 hins

      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
          x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      rw [show (principal_open ν₁ n).val = CantorSpace.principalOpen (cast eq₁ (ν₁, n)) from rfl]
      exact (key eq₁ S (ν₁, n)).mp hmem
    · trivial

  have this₂ : ι p' ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ :=
    not_mem_of_not_mem (Finset.mem_insert_self (ν₂, n) p.out)

  have this₃ : ι p' ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ := sep this₁ this₂

  have this₄ : ι p' ≤ mk ν₁ =ᴮ mk ν₂ := le_trans anti H_p

  have this₅ : ι p' = ⊥ := le_antisymm (le_trans (le_inf this₄ this₃) inf_compl_eq_bot.le) bot_le
  exact (𝒞_nonzero p') this₅.symm

end cohen_real

section neg_CH

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)

lemma uncountable_fiber_of_regular' (κ₁ κ₂ : Cardinal) (H_inf : Cardinal.aleph0 ≤ κ₁)
    (H_lt : κ₁ < κ₂) (H : κ₂.ord.cof = κ₂) (α : Type u) (H_α : #α = κ₁)
    (β : Type u) (H_β : #β = κ₂) (g : β → α) :
    ∃ (ξ : α), Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by

  have h₁ : Cardinal.aleph0 ≤ #β := H_β ▸ le_of_lt (lt_of_le_of_lt H_inf H_lt)
  have h₂ : #α < (#β).ord.cof := by
    rw [H_α, H_β, H]; exact H_lt
  obtain ⟨ξ, Hξ⟩ := Cardinal.infinite_pigeonhole g h₁ h₂

  refine ⟨ξ, ?_⟩
  rw [Hξ, H_β]
  exact lt_of_le_of_lt H_inf H_lt

lemma uncountable_fiber_of_regular (κ₁ κ₂ : Cardinal) (H_inf : Cardinal.aleph0 ≤ κ₁)
    (H_lt : κ₁ < κ₂) (H : κ₂.ord.cof = κ₂)
    (g : (PSet.card_ex κ₂).Type → (PSet.card_ex κ₁).Type) :
    ∃ (ξ : (PSet.card_ex κ₁).Type), Cardinal.aleph0 < #↥((fun β => g β)⁻¹' {ξ}) :=
  uncountable_fiber_of_regular' κ₁ κ₂ H_inf H_lt H _
    (PSet.mk_type_mk_eq κ₁ H_inf) _ (PSet.mk_type_mk_eq κ₂ (le_of_lt (lt_of_le_of_lt H_inf H_lt))) g

lemma cardinal_inequality_of_regular (κ₁ κ₂ : Cardinal)
    (H_reg₁ : Cardinal.IsRegular κ₁) (H_reg₂ : Cardinal.IsRegular κ₂)
    (H_inf : Cardinal.aleph0 ≤ κ₁) (H_lt : κ₁ < κ₂) {Γ : 𝔹} :
    Γ ≤ (larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)))ᶜ := by

  apply le_neg_of_inf_eq_bot
  rw [inf_comm]

  rw [eq_bot_iff]

  by_contra H_nonzero
  rw [← bot_lt_iff_not_le_bot] at H_nonzero

  have H_larger : Γ ⊓ larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) ≤
      larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) := inf_le_right
  rcases AE_of_check_larger_than_check H_nonzero H_larger
    (PSet.exists_mem_of_regular H_reg₂) with ⟨f, Hf⟩

  obtain ⟨g, g_spec⟩ := Classical.axiomOfChoice Hf

  have H_inf₁ : Cardinal.aleph0 ≤ #((PSet.card_ex κ₁).Type) := by simp [H_inf]
  have H_lt₁ : #((PSet.card_ex κ₁).Type) < #((PSet.card_ex κ₂).Type) := by
    rw [@PSet.mk_type_mk_eq'' κ₁ H_inf, @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))]
    exact H_lt
  have H_inj₂₁ : ∀ i j, i ≠ j → ¬ PSet.Equiv ((PSet.card_ex κ₂).Func i) ((PSet.card_ex κ₂).Func j) :=
    fun i j h => PSet.ordinalMk_inj _ _ _ h
  have H_ex : ∃ ξ : (PSet.card_ex κ₁).Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by
    apply uncountable_fiber_of_regular' κ₁ κ₂ H_inf H_lt H_reg₂.cof_ord
    · exact @PSet.mk_type_mk_eq'' κ₁ H_inf
    · exact @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))
  exact absurd 𝔹_CCC (not_CCC_of_uncountable_fiber (PSet.card_ex κ₁) (PSet.card_ex κ₂)
    H_inf₁ H_lt₁ H_inj₂₁ f g g_spec H_ex)

lemma aleph0_lt_aleph1_bSet : (⊤ : 𝔹) ≤
    (larger_than omega (check (PSet.card_ex (Cardinal.aleph 1))))ᶜ := by

  apply le_neg_of_inf_eq_bot
  rw [inf_comm, eq_bot_iff]
  by_contra H_nonzero
  rw [← bot_lt_iff_not_le_bot] at H_nonzero
  rcases AE_of_check_larger_than_check H_nonzero (le_trans inf_le_right (le_refl _))
    (PSet.exists_mem_of_regular PSet.is_regular_aleph_one) with ⟨f, Hf⟩
  obtain ⟨g, g_spec⟩ := Classical.axiomOfChoice Hf
  suffices h : ¬ CCC 𝔹 from absurd 𝔹_CCC h

  have H_omega_card : #(PSet.omega.Type) = Cardinal.aleph0 := PSet.mk_omega_eq_mk_omega
  have H_aleph1_card : #((PSet.card_ex (Cardinal.aleph 1)).Type) = Cardinal.aleph 1 :=
    @PSet.mk_type_mk_eq'' (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1)
  have H_inf₁ : Cardinal.aleph0 ≤ #(PSet.omega.Type) := H_omega_card.symm ▸ le_refl _
  have H_lt₁ : #(PSet.omega.Type) < #((PSet.card_ex (Cardinal.aleph 1)).Type) := by
    rw [H_omega_card, H_aleph1_card]; exact Cardinal.aleph0_lt_aleph_one
  have H_inj₂₁ : ∀ i j, i ≠ j →
      ¬ PSet.Equiv ((PSet.card_ex (Cardinal.aleph 1)).Func i)
                   ((PSet.card_ex (Cardinal.aleph 1)).Func j) :=
    fun i j h => PSet.ordinalMk_inj _ _ _ h
  have H_ex : ∃ ξ : PSet.omega.Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ}) :=
    uncountable_fiber_of_regular' (Cardinal.aleph 0) (Cardinal.aleph 1)
      (Cardinal.aleph0_le_aleph 0)
      (by rw [Cardinal.aleph_lt_aleph]; exact zero_lt_one)
      PSet.is_regular_aleph_one.cof_ord
      PSet.omega.Type (H_omega_card.trans Cardinal.aleph_zero.symm)
      (PSet.card_ex (Cardinal.aleph 1)).Type H_aleph1_card g
  exact not_CCC_of_uncountable_fiber PSet.omega (PSet.card_ex (Cardinal.aleph 1))
    H_inf₁ H_lt₁ H_inj₂₁ f g g_spec H_ex

lemma aleph1_lt_aleph2_bSet : (⊤ : 𝔹) ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  cardinal_inequality_of_regular _ _ PSet.is_regular_aleph_one PSet.is_regular_aleph_two
    (Cardinal.aleph0_le_aleph 1) PSet.aleph_one_lt_aleph_two

lemma aleph1_lt_aleph2_bSet' {Γ : 𝔹} : Γ ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  le_trans le_top aleph1_lt_aleph2_bSet

lemma cohen_real.mk_ext : ∀ (i j : (check (PSet.pSet_aleph2) : bSet 𝔹).type),
    (check (PSet.pSet_aleph2) : bSet 𝔹).func i =ᴮ (check (PSet.pSet_aleph2) : bSet 𝔹).func j ≤
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) i =ᴮ
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) j := by
  intro i j; by_cases h : i = j
  · simp [h]
  · apply poset_yoneda; intro Γ a
    rw [check_func, check_func] at a
    suffices h_bot : (check (PSet.pSet_aleph2.Func (check_cast i)) : bSet 𝔹) =ᴮ
        check (PSet.pSet_aleph2.Func (check_cast j)) ≤ ⊥ by
      exact le_trans a (le_trans h_bot bot_le)
    rw [le_bot_iff]
    apply check_bv_eq_bot_of_not_equiv

    apply PSet.ordinalMk_inj (Cardinal.aleph 2).ord
    intro H; exact h (by simp [check_cast] at H ⊢; exact H)

noncomputable def neg_CH_func : bSet 𝔹 :=
  @functionMk _ _ (check PSet.pSet_aleph2) (fun x => cohen_real.mk x) cohen_real.mk_ext

set_option maxHeartbeats 400000 in
theorem aleph2_le_powerset_omega :
    ⊤ ≤ is_func' (check PSet.pSet_aleph2) 𝔠 neg_CH_func ⊓ is_inj neg_CH_func := by
  apply le_inf
  ·
    apply le_inf
    ·
      exact functionMk_is_func _ cohen_real.mk_ext
    ·
      apply le_iInf; intro w₁; rw [← deduction, top_inf_eq]

      rw [mem_unfold]

      apply iSup_le; intro ν

      rw [check_bval_top, top_inf_eq]

      apply le_iSup_of_le (cohen_real.mk ν)

      apply le_inf
      ·
        exact le_trans le_top cohen_real.definite'
      ·

        have h_func_mem : (⊤ : 𝔹) ≤ pair ((check PSet.pSet_aleph2).func ν) (cohen_real.mk ν) ∈ᴮ neg_CH_func := by
          have := @functionMk_self 𝔹 _ (check PSet.pSet_aleph2) (fun x => cohen_real.mk x)
            cohen_real.mk_ext ν
          rwa [check_bval_top] at this

        exact bv_rw' (H := le_refl _) (ϕ := fun z => pair z (cohen_real.mk ν) ∈ᴮ neg_CH_func)
          (h_congr := B_ext_pair_mem_left) (H_new := le_trans le_top h_func_mem)
  ·
    exact functionMk_inj_of_inj (fun i j h => cohen_real.inj h) cohen_real.mk_ext

lemma aleph1_Ord {Γ : 𝔹} : Γ ≤ Ord (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) :=
  Ord_card_ex _

lemma aleph2_Ord {Γ : 𝔹} : Γ ≤ Ord (check (PSet.card_ex (Cardinal.aleph 2)) : bSet 𝔹) :=
  Ord_card_ex _

theorem neg_CH : (⊤ : 𝔹) ≤ CHᶜ := by
  simp only [CH, compl_compl]
  exact le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 1)))
    (le_inf aleph1_Ord (le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 2)))
      (le_inf (le_inf aleph0_lt_aleph1_bSet aleph1_lt_aleph2_bSet)
        (le_iSup_of_le neg_CH_func aleph2_le_powerset_omega))))

theorem neg_CH₂ : (⊤ : 𝔹) ≤ CH₂ᶜ :=
  (Lattice.bv_iff_neg CH_iff_CH₂).mp neg_CH

end neg_CH

end bSet
