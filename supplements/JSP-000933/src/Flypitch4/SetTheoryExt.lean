/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Modified for Lean and Mathlib 4.36.0.

import Flypitch4.ToMathlib
import Mathlib.Topology.Bases
import Mathlib.Data.Set.Card
import Mathlib.Order.Zorn

universe u v

open Set TopologicalSpace Cardinal

section CCC

variable (α : Type u) [TopologicalSpace α]

def countable_chain_condition : Prop :=
  ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → IsOpen o) → s.PairwiseDisjoint id → s.Countable

variable {α}

lemma countable_chain_condition_of_nonempty
    (h : ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → o ≠ ∅) → (∀ ⦃o⦄, o ∈ s → IsOpen o) →
      s.PairwiseDisjoint id → s.Countable) : countable_chain_condition α := by
  intro s open_s hs
  let s' : Set (Set α) := s \ {∅}
  have hs' : ∀ ⦃o : Set α⦄, o ∈ s' → o ≠ ∅ := fun o ho h2o => ho.2 (by rw [mem_singleton_iff, h2o])
  have open_s' : ∀ ⦃o : Set α⦄, o ∈ s' → IsOpen o := fun o ho => open_s ho.1
  have h2s' : s'.PairwiseDisjoint id := hs.subset sdiff_subset
  have hcountable : s'.Countable := h s' hs' open_s' h2s'
  exact (hcountable.insert ∅).mono (by rw [insert_sdiff_singleton]; exact subset_insert _ _)

lemma countable_chain_condition_of_separable_space [SeparableSpace α] :
    countable_chain_condition α := by
  intro s open_s hs
  suffices h : (s \ {(∅ : Set α)}).Countable by
    have hsub : s ⊆ insert (∅ : Set α) (s \ {∅}) := by
      intro o ho
      rcases eq_or_ne o ∅ with rfl | hne
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨ho, fun h => hne (Set.mem_singleton_iff.mp h)⟩)
    exact (h.insert ∅).mono hsub
  apply Set.PairwiseDisjoint.countable_of_isOpen (s := id) (a := s \ {(∅ : Set α)})
  · intro o ⟨ho, _⟩ o' ⟨ho', _⟩ hne
    exact hs ho ho' hne
  · intro o ⟨ho, _⟩; exact open_s ho
  · intro o ⟨_, hne⟩
    exact Set.nonempty_iff_ne_empty.mpr (fun h => hne (Set.mem_singleton_iff.mpr h))

lemma countable_chain_condition_of_countable (h : #α ≤ ℵ₀) : countable_chain_condition α := by
  haveI : Countable α := Cardinal.mk_le_aleph0_iff.mp h
  haveI : SeparableSpace α := inferInstance
  exact countable_chain_condition_of_separable_space

lemma countable_chain_condition_of_topological_basis (B : Set (Set α))
    (hB : IsTopologicalBasis B)
    (h : ∀ s : Set (Set α), s ⊆ B → s.PairwiseDisjoint id → s.Countable) :
    countable_chain_condition α := by
  apply countable_chain_condition_of_nonempty
  intro s s_nonempty s_open hs

  have hpick : ∀ x : s, ∃ b : Set α, b ∈ B ∧ b ≠ ∅ ∧ b ⊆ x.1 := by
    rintro ⟨x, hx⟩
    have hxne : x.Nonempty := Set.nonempty_iff_ne_empty.mpr (s_nonempty hx)
    obtain ⟨y, hy⟩ := hxne
    obtain ⟨b, hbB, hyb, hbx⟩ := hB.isOpen_iff.mp (s_open hx) y hy
    refine ⟨b, hbB, ?_, hbx⟩
    intro hbe; rw [hbe] at hyb; exact hyb
  choose f hfB hfne hfsub using hpick

  let s' : Set (Set α) := Set.range f
  have hs'B : s' ⊆ B := by rintro _ ⟨x, rfl⟩; exact hfB x
  have hs'pd : s'.PairwiseDisjoint id := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
    have hxy' : x ≠ y := by
      rintro rfl; exact hne rfl
    have h1 : (x : Set α) ≠ y := fun h => hxy' (Subtype.ext h)
    exact (hs x.2 y.2 h1).mono (hfsub x) (hfsub y)
  have hs'count : s'.Countable := h s' hs'B hs'pd

  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hxy' : (x : Set α) ≠ y := fun h => hne (Subtype.ext h)
    have hd : Disjoint (x : Set α) (y : Set α) := hs x.2 y.2 hxy'
    have : (f x).Nonempty := Set.nonempty_iff_ne_empty.mpr (hfne x)
    obtain ⟨z, hz⟩ := this
    have hzx : z ∈ (x : Set α) := hfsub x hz
    have hzy : z ∈ (y : Set α) := hfsub y (hxy ▸ hz)
    have : ¬ Disjoint (x : Set α) (y : Set α) := by
      rw [Set.not_disjoint_iff]; exact ⟨z, hzx, hzy⟩
    exact this hd

  have hs_count : s.Countable := by
    have hsub : Countable (Set.range f) := hs'count.to_subtype
    have : Countable s := by
      have hf' : Function.Injective (fun x : s => (⟨f x, Set.mem_range_self x⟩ : Set.range f)) := by
        intro x y hxy
        exact hf_inj (Subtype.ext_iff.mp hxy)
      exact hf'.countable
    exact Set.countable_coe_iff.mp this
  exact hs_count

end CCC

def IsDeltaSystem {ι : Type*} {α : Type*} (A : ι → Set α) : Prop :=
  ∃ root : Set α, ∀ ⦃x y : ι⦄, x ≠ y → A x ∩ A y = root

namespace DeltaSystemAux

private lemma aleph0_lt_of_not_countable {ι : Type v} {t : Set ι} (h : ¬ t.Countable) :
    ℵ₀ < #t := by
  rw [← not_le]
  intro hle
  exact h (Cardinal.le_aleph0_iff_set_countable.mp hle)

private lemma not_countable_of_aleph0_lt {ι : Type v} {t : Set ι} (h : ℵ₀ < #t) :
    ¬ t.Countable := by
  intro hc
  exact absurd (Cardinal.le_aleph0_iff_set_countable.mpr hc) (not_le.mpr h)

private lemma exists_uncountable_fiber_nat {ι : Type v} (f : ι → ℕ)
    (hι : ¬ (Set.univ : Set ι).Countable) :
    ∃ n : ℕ, ¬ (f ⁻¹' {n}).Countable := by
  by_contra hne
  push Not at hne

  have huniv : (Set.univ : Set ι) = ⋃ n : ℕ, f ⁻¹' {n} := by
    ext x; simp
  apply hι
  rw [huniv]
  exact Set.countable_iUnion hne

private theorem delta_system_size_n {α : Type u} {ι : Type v}
    (n : ℕ) (A : ι → Set α)
    (hι : ¬ (Set.univ : Set ι).Countable)
    (hA_fin : ∀ i, (A i).Finite)
    (hA_card : ∀ i, Set.ncard (A i) = n) :
    ∃ t : Set ι, ¬ t.Countable ∧ ∃ root : Set α,
      ∀ ⦃x⦄, x ∈ t → ∀ ⦃y⦄, y ∈ t → x ≠ y → A x ∩ A y = root := by
  induction n generalizing ι with
  | zero =>

    refine ⟨Set.univ, hι, ∅, ?_⟩
    intro x _ y _ _
    have hx : A x = ∅ := by
      have h0 : Set.ncard (A x) = 0 := hA_card x
      exact (Set.ncard_eq_zero (hA_fin x)).mp h0
    rw [hx, Set.empty_inter]
  | succ n ih =>
    by_cases hcase : ∃ x : α, ¬ {i | x ∈ A i}.Countable
    ·
      obtain ⟨x, hx⟩ := hcase
      let t₀ : Set ι := {i | x ∈ A i}
      let A' : t₀ → Set α := fun i => A i.1 \ {x}
      have hA'_fin : ∀ i : t₀, (A' i).Finite := fun i => (hA_fin i.1).sdiff
      have hA'_card : ∀ i : t₀, Set.ncard (A' i) = n := by
        intro i
        have hxA : x ∈ A i.1 := i.2
        have h := Set.ncard_sdiff_singleton_add_one hxA (hA_fin i.1)
        have h2 : Set.ncard (A i.1) = n + 1 := hA_card i.1
        change Set.ncard (A i.1 \ {x}) = n
        omega
      have ht₀_ucnt : ¬ (Set.univ : Set t₀).Countable := by
        intro hc
        apply hx
        rw [Set.countable_univ_iff] at hc
        exact Set.countable_coe_iff.mp hc
      obtain ⟨t', ht'_ucnt, r', hr'⟩ := ih A' ht₀_ucnt hA'_fin hA'_card

      let t : Set ι := Subtype.val '' t'
      have ht_inj : Set.InjOn (Subtype.val : t₀ → ι) t' := fun a _ b _ h => Subtype.ext h
      have ht_ucnt : ¬ t.Countable := by
        intro hc
        apply ht'_ucnt
        exact Set.countable_of_injective_of_countable_image ht_inj hc
      refine ⟨t, ht_ucnt, insert x r', ?_⟩
      rintro _ ⟨⟨a, ha₀⟩, hat', rfl⟩ _ ⟨⟨b, hb₀⟩, hbt', rfl⟩ hab
      have hab' : (⟨a, ha₀⟩ : t₀) ≠ ⟨b, hb₀⟩ := fun h => hab (congr_arg Subtype.val h)
      have h_intersect : A' ⟨a, ha₀⟩ ∩ A' ⟨b, hb₀⟩ = r' := hr' hat' hbt' hab'

      ext y
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨hya, hyb⟩
        by_cases hyx : y = x
        · exact Or.inl hyx
        · refine Or.inr ?_
          have hyA' : y ∈ A' ⟨a, ha₀⟩ ∩ A' ⟨b, hb₀⟩ := by
            refine ⟨⟨hya, ?_⟩, ⟨hyb, ?_⟩⟩ <;> simp [hyx]
          rw [h_intersect] at hyA'
          exact hyA'
      · rintro (rfl | hyr)
        · exact ⟨ha₀, hb₀⟩
        · have : y ∈ A' ⟨a, ha₀⟩ ∩ A' ⟨b, hb₀⟩ := by rw [h_intersect]; exact hyr
          exact ⟨this.1.1, this.2.1⟩
    ·
      push Not at hcase

      have key : ∀ s : Set α, s.Countable →
          {i : ι | (A i ∩ s).Nonempty}.Countable := by
        intro s hs
        have hsub : {i : ι | (A i ∩ s).Nonempty} ⊆ ⋃ y ∈ s, {i | y ∈ A i} := by
          intro i ⟨y, hy⟩
          exact Set.mem_iUnion₂.mpr ⟨y, hy.2, hy.1⟩
        exact Set.Countable.mono hsub (hs.biUnion (fun y _ => hcase y))

      have hAne : ∀ i, (A i).Nonempty := by
        intro i
        rw [← Set.ncard_pos (hA_fin i), hA_card i]
        omega

      let P : Set ι → Prop := fun M => M.PairwiseDisjoint A
      have hP_chain : ∀ c ⊆ {M | P M}, IsChain (· ⊆ ·) c → ∃ ub ∈ {M | P M}, ∀ s ∈ c, s ⊆ ub := by
        intro c hc hchain
        refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
        rintro i ⟨M₁, hM₁c, hi⟩ j ⟨M₂, hM₂c, hj⟩ hij
        rcases hchain.total hM₁c hM₂c with hsub | hsub
        · exact (hc hM₂c) (hsub hi) hj hij
        · exact (hc hM₁c) hi (hsub hj) hij
      obtain ⟨M, hM_max⟩ := zorn_subset {M | P M} hP_chain
      have hM_S : P M := hM_max.prop

      by_cases hM_cnt : M.Countable
      ·
        let B : Set α := ⋃ i ∈ M, A i
        have hB_cnt : B.Countable :=
          hM_cnt.biUnion (fun i _ => (hA_fin i).countable)
        have hbad_cnt : {i : ι | (A i ∩ B).Nonempty}.Countable := key B hB_cnt

        have hex : ∃ i : ι, ¬ (A i ∩ B).Nonempty := by
          by_contra hne
          push Not at hne
          apply hι
          have huniv : (Set.univ : Set ι) ⊆ {i | (A i ∩ B).Nonempty} := fun i _ => hne i
          exact hbad_cnt.mono huniv
        obtain ⟨i₀, hi₀⟩ := hex
        rw [Set.not_nonempty_iff_eq_empty] at hi₀
        have hi₀_dis : ∀ i ∈ M, Disjoint (A i₀) (A i) := by
          intro i hi
          rw [Set.disjoint_iff_inter_eq_empty]
          have hsub : A i₀ ∩ A i ⊆ A i₀ ∩ B := fun y ⟨ha, hb⟩ =>
            ⟨ha, Set.mem_biUnion hi hb⟩
          exact Set.eq_empty_of_subset hsub hi₀
        have hi₀_notM : i₀ ∉ M := by
          intro hin
          have hAi : A i₀ ⊆ B := Set.subset_biUnion_of_mem hin
          obtain ⟨y, hy⟩ := hAne i₀
          have : y ∈ A i₀ ∩ B := ⟨hy, hAi hy⟩
          rw [hi₀] at this
          exact this.elim

        let M' : Set ι := insert i₀ M
        have hM'_P : P M' := by
          intro a ha b hb hab
          simp only [M', Set.mem_insert_iff] at ha hb
          rcases ha with rfl | ha
          · rcases hb with rfl | hb
            · exact absurd rfl hab
            · exact hi₀_dis b hb
          · rcases hb with rfl | hb
            · exact (hi₀_dis a ha).symm
            · exact hM_S ha hb hab
        have hM_sub : M ⊆ M' := Set.subset_insert _ _
        have heq : M' = M := hM_max.eq_of_superset hM'_P hM_sub
        have hin : i₀ ∈ M := heq ▸ Set.mem_insert _ _
        exact absurd hin hi₀_notM

      refine ⟨M, hM_cnt, ∅, ?_⟩
      intro a ha b hb hab
      exact Set.disjoint_iff_inter_eq_empty.mp (hM_S ha hb hab)

end DeltaSystemAux

theorem delta_system_lemma_aleph1
    {α : Type u} {ι : Type v} (A : ι → Set α)
    (hι : ℵ₀ < #ι) (h2A : ∀ i, (A i).Finite) :
    ∃ t : Set ι, ℵ₀ < #t ∧ IsDeltaSystem (fun i : t => A i.1) := by

  have hι_uncnt : ¬ (Set.univ : Set ι).Countable := by
    intro hc
    have hCount : Countable ι := by
      rw [← Set.countable_univ_iff]; exact hc
    have : #ι ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr hCount
    exact absurd hι (not_lt.mpr this)
  let f : ι → ℕ := fun i => Set.ncard (A i)
  obtain ⟨n, hn⟩ := DeltaSystemAux.exists_uncountable_fiber_nat f hι_uncnt
  let t₀ : Set ι := f ⁻¹' {n}
  let A' : t₀ → Set α := fun i => A i.1
  have ht₀_uncnt : ¬ (Set.univ : Set t₀).Countable := by
    intro hc
    apply hn
    rw [Set.countable_univ_iff] at hc
    exact Set.countable_coe_iff.mp hc
  have hA'_fin : ∀ i : t₀, (A' i).Finite := fun i => h2A i.1
  have hA'_card : ∀ i : t₀, Set.ncard (A' i) = n := fun i => i.2
  obtain ⟨t', ht'_uncnt, root, hroot⟩ :=
    DeltaSystemAux.delta_system_size_n n A' ht₀_uncnt hA'_fin hA'_card
  let t : Set ι := Subtype.val '' t'
  have ht_inj : Set.InjOn (Subtype.val : t₀ → ι) t' := fun a _ b _ h => Subtype.ext h
  refine ⟨t, ?_, root, ?_⟩
  ·
    apply DeltaSystemAux.aleph0_lt_of_not_countable
    intro hc
    exact ht'_uncnt (Set.countable_of_injective_of_countable_image ht_inj hc)
  ·
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨a, hat', rfl⟩ := hx
    obtain ⟨b, hbt', rfl⟩ := hy
    have hab' : a ≠ b := by
      intro h; apply hxy
      apply Subtype.ext
      show (↑a : ι) = ↑b
      rw [h]
    exact hroot hat' hbt' hab'

variable {α : Type u} {β : α → Type v} [∀ x, TopologicalSpace (β x)]

private def piOpenBasis : Set (Set (∀ x, β x)) :=
  { S | ∃ (U : ∀ x, Set (β x)) (F : Finset α),
        (∀ x, x ∈ F → IsOpen (U x)) ∧ S = (F : Set α).pi U }

private lemma isTopologicalBasis_piOpenBasis :
    IsTopologicalBasis (piOpenBasis (β := β)) :=
  isTopologicalBasis_pi (X := β) (T := fun _ => { U | IsOpen U })
    (fun _ => isTopologicalBasis_opens)

private lemma isOpen_restrict_image_piOpenBasis
    (R : Set α) {S : Set (∀ x, β x)} (hS : S ∈ piOpenBasis (β := β)) :
    IsOpen ((fun f : ∀ x, β x => fun x : R => f x.1) '' S) := by
  classical
  obtain ⟨U, F, hU, rfl⟩ := hS

  by_cases hpi : ((F : Set α).pi U).Nonempty
  ·
    obtain ⟨f₀, hf₀⟩ := hpi
    have himg : (fun f : ∀ x, β x => fun x : R => f x.1) '' ((F : Set α).pi U) =
        (Subtype.val ⁻¹' (F : Set α) : Set R).pi (fun x : R => U x.1) := by
      ext g
      constructor
      · rintro ⟨f, hf, rfl⟩ ⟨x, hxR⟩ hxF
        exact hf x hxF
      · intro hg
        refine ⟨fun x => if hx : x ∈ R then g ⟨x, hx⟩ else f₀ x, ?_, ?_⟩
        · intro x hxF
          by_cases hxR : x ∈ R
          · simp only [dite_eq_left hxR]; exact hg ⟨x, hxR⟩ hxF
          · simp only [dite_eq_right hxR]; exact hf₀ x hxF
        · funext ⟨x, hxR⟩; simp only [dite_eq_left hxR]
    rw [himg]
    apply isTopologicalBasis_piOpenBasis.isOpen
    refine ⟨fun x : R => U x.1, F.subtype (· ∈ R), ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_subtype] at hx
      exact hU x.1 hx
    · ext g
      constructor
      · intro hg x hxF
        rw [Finset.mem_coe, Finset.mem_subtype] at hxF
        exact hg ⟨x, x.2⟩ hxF
      · intro hg ⟨x, hxR⟩ hxF
        have : (⟨x, hxR⟩ : R) ∈ F.subtype (· ∈ R) := by
          rw [Finset.mem_subtype]; exact hxF
        exact hg _ this
  ·
    rw [Set.not_nonempty_iff_eq_empty] at hpi
    rw [hpi, Set.image_empty]
    exact isOpen_empty

private lemma disjoint_restrict_image_of_delta
    {S₁ S₂ : Set (∀ x, β x)}
    {U₁ U₂ : ∀ x, Set (β x)} {F₁ F₂ : Finset α}
    (h₁ : S₁ = (F₁ : Set α).pi U₁) (h₂ : S₂ = (F₂ : Set α).pi U₂)
    (hd : Disjoint S₁ S₂) (R : Set α)
    (hroot : ((F₁ : Set α)) ∩ ((F₂ : Set α)) = R) :
    Disjoint ((fun f : ∀ x, β x => fun x : R => f x.1) '' S₁)
             ((fun f : ∀ x, β x => fun x : R => f x.1) '' S₂) := by
  classical
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro g ⟨⟨f₁, hf₁S, rfl⟩, ⟨f₂, hf₂S, hfeq⟩⟩

  rw [h₁] at hf₁S
  rw [h₂] at hf₂S
  let f : ∀ x, β x := fun x => if x ∈ F₁ then f₁ x else f₂ x
  have hfS₁ : f ∈ S₁ := by
    rw [h₁]
    intro x hxF
    simp only [Finset.mem_coe] at hxF
    show f x ∈ U₁ x
    simp only [f, ite_eq_left hxF]
    exact hf₁S x hxF
  have hfS₂ : f ∈ S₂ := by
    rw [h₂]
    intro x hxF
    simp only [Finset.mem_coe] at hxF
    show f x ∈ U₂ x
    by_cases hx1 : x ∈ F₁
    ·
      have hxR : x ∈ R := by
        rw [← hroot]
        exact ⟨hx1, hxF⟩
      simp only [f, ite_eq_left hx1]
      have heq : f₂ x = f₁ x := by
        have := congr_fun hfeq ⟨x, hxR⟩
        simpa using this
      rw [← heq]
      exact hf₂S x hxF
    · simp only [f, ite_eq_right hx1]
      exact hf₂S x hxF
  exact (Set.disjoint_iff_forall_ne.mp hd hfS₁ hfS₂) rfl

theorem countable_chain_condition_pi
    (h : ∀ s : Set α, s.Finite → countable_chain_condition (∀ x : s, β x)) :
    countable_chain_condition (∀ x, β x) := by
  classical
  apply countable_chain_condition_of_topological_basis (piOpenBasis (β := β))
    isTopologicalBasis_piOpenBasis
  intro C hC h2C
  by_contra h3Cne
  have h3C : ℵ₀ < #C := by
    by_contra hle
    push Not at hle
    exact h3Cne (Cardinal.le_aleph0_iff_set_countable.mp hle)

  have hCdata : ∀ S : C, ∃ (U : ∀ x, Set (β x)) (F : Finset α),
      (∀ x ∈ F, IsOpen (U x)) ∧ S.1 = (F : Set α).pi U := by
    rintro ⟨S, hS⟩; exact hC hS
  choose U F hUopen hSeq using hCdata

  let A : C → Set α := fun S => (F S : Set α)
  have hA_fin : ∀ S : C, (A S).Finite := fun S => Finset.finite_toSet _
  obtain ⟨C', hC'_card, R, hR⟩ := delta_system_lemma_aleph1 A h3C hA_fin

  have h2R : R.Finite := by

    have : ∃ x y : C', x ≠ y := by
      by_contra hne
      push Not at hne
      have hsub : Subsingleton C' := ⟨fun x y => hne x y⟩
      have hone : #C' ≤ 1 := Cardinal.mk_le_one_iff_set_subsingleton.mpr (by
        intro x hx y hy
        exact congr_arg Subtype.val (hsub.elim ⟨x, hx⟩ ⟨y, hy⟩))
      have : ℵ₀ < (1 : Cardinal) := lt_of_lt_of_le hC'_card hone
      have : ℵ₀ < ℵ₀ := this.trans_le (by simp)
      exact absurd this (lt_irrefl _)
    obtain ⟨x, y, hxy⟩ := this
    rw [← hR hxy]
    exact (hA_fin x.1).inter_of_left _

  let π : (∀ x, β x) → (∀ x : R, β x) := fun f x => f x.1
  let D : Set (Set (∀ x : R, β x)) := (fun S : C' => π '' S.1.1) '' Set.univ

  have hD_open : ∀ ⦃o⦄, o ∈ D → IsOpen o := by
    rintro _ ⟨S, _, rfl⟩
    exact isOpen_restrict_image_piOpenBasis _ (hC S.1.2)

  have h2'D : ∀ S₁ S₂ : C', S₁ ≠ S₂ → Disjoint (π '' S₁.1.1) (π '' S₂.1.1) := by
    intro S₁ S₂ hne

    have h12 : S₁.1.1 ≠ S₂.1.1 := fun heq => by
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact heq

    have hdis : Disjoint S₁.1.1 S₂.1.1 :=
      h2C S₁.1.2 S₂.1.2 h12

    apply disjoint_restrict_image_of_delta (hSeq S₁.1) (hSeq S₂.1) hdis R

    have := hR (x := S₁) (y := S₂) hne

    simpa [A] using this

  have hD_disj : D.PairwiseDisjoint id := by
    rintro _ ⟨S₁, _, rfl⟩ _ ⟨S₂, _, rfl⟩ hne
    have hS₁S₂ : S₁ ≠ S₂ := fun heq => by rw [heq] at hne; exact hne rfl
    exact h2'D S₁ S₂ hS₁S₂

  have hD_card : ℵ₀ < #D := by

    let C'ne : Set C' := { S | S.1.1 ≠ ∅ }
    have hC'ne_card : ℵ₀ < #C'ne := by

      have hcompl : (C'ne)ᶜ ⊆ {S : C' | S.1.1 = ∅} := by
        intro S hS
        simp only [Set.mem_compl_iff, ne_eq, not_not] at hS
        change S.1.1 = ∅
        by_contra hne
        exact hS hne
      have hsub : { S : C' | S.1.1 = ∅ }.Subsingleton := by
        intro x hx y hy
        apply Subtype.ext
        apply Subtype.ext
        rw [hx, hy]
      have hsub_card : #({ S : C' | S.1.1 = ∅ } : Set C') ≤ 1 := by
        rw [Cardinal.mk_le_one_iff_set_subsingleton]
        exact hsub

      have hsplit : (Set.univ : Set C') = C'ne ∪ (C'ne)ᶜ := (Set.union_compl_self _).symm
      have hcard_le : #C' ≤ #C'ne + #((C'ne)ᶜ : Set C') := by
        have hsplit2 : #(Set.univ : Set C') ≤ #C'ne + #((C'ne)ᶜ : Set C') := by
          have := Cardinal.mk_union_le C'ne (C'ne)ᶜ
          rw [Set.union_compl_self] at this
          exact this
        rwa [Cardinal.mk_univ] at hsplit2
      have hcompl_card : #((C'ne)ᶜ : Set C') ≤ 1 :=
        le_trans (Cardinal.mk_le_mk_of_subset hcompl) hsub_card

      have h1 : ℵ₀ < #C'ne + #((C'ne)ᶜ : Set C') := lt_of_lt_of_le hC'_card hcard_le
      by_contra hle
      push Not at hle
      have : #C'ne + #((C'ne)ᶜ : Set C') ≤ ℵ₀ := by
        have h_cmpl : #((C'ne)ᶜ : Set C') ≤ ℵ₀ := le_trans hcompl_card (by exact_mod_cast (one_le_aleph0))
        exact Cardinal.add_le_aleph0.mpr ⟨hle, h_cmpl⟩
      exact absurd h1 (not_lt.mpr this)

    let f : C'ne → D := fun S =>
      ⟨π '' S.1.1.1, S.1, trivial, rfl⟩
    have hf_inj : Function.Injective f := by
      intro S₁ S₂ hSeq
      have heq : π '' S₁.1.1.1 = π '' S₂.1.1.1 := by
        have := congr_arg Subtype.val hSeq
        exact this

      by_contra hne
      have hSne : S₁.1 ≠ S₂.1 := fun heq' => hne (Subtype.ext heq')
      have hdisj := h2'D S₁.1 S₂.1 hSne
      rw [heq] at hdisj

      have : π '' S₂.1.1.1 = ∅ := by
        rw [disjoint_self] at hdisj
        exact hdisj

      have hS₂ne : S₂.1.1.1 ≠ ∅ := S₂.2
      rw [Set.image_eq_empty] at this
      exact hS₂ne this

    have : #C'ne ≤ #D := Cardinal.mk_le_of_injective hf_inj
    exact lt_of_lt_of_le hC'ne_card this

  have hD_count : D.Countable := h R h2R D hD_open hD_disj
  have : #D ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hD_count
  exact absurd hD_card (not_lt.mpr this)
