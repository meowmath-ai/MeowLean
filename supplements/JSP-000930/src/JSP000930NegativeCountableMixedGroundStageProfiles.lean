import JSP000930NegativeRelativeCheckedKappaContinuousLimit

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion

variable {P : Type} [Preorder P]

theorem countable_mixed_profiles_cover (hP : IsCountablyClosed P)
    {J I : Type} [Countable J] (C : J → DiscreteChoiceOn I (⊤ : RO P)) :
    (⨆ f : J → I,⨅ j,(C j).value (f j)) = ⊤ := by
  classical
  apply top_unique
  let V := ⨆ f : J → I,⨅ j,(C j).value (f j)
  change ⊤ ≤ V
  by_contra hn
  have hV : Vᶜ ≠ ⊥ := fun he => hn (compl_eq_bot.mp he).ge
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 Vᶜ hV
  by_cases hJ : Nonempty J
  · letI : Nonempty J := hJ
    obtain ⟨e,he⟩ := exists_surjective_nat J
    obtain ⟨q,g,hqp,hq⟩ := exists_allChoiceProfiles_r411 hP p
      (fun n i => (C (e n)).value i)
      (fun n => le_top.trans (C (e n)).covers.ge)
    let f (j : J) := g (Classical.choose (he j))
    have hF (j : J) : imageCondition q ≤ (C j).value (f j) := by
      let n := Classical.choose (he j)
      have hJ' : e n = j := Classical.choose_spec (he j)
      have h := hq n
      rw [hJ'] at h
      exact h
    have hQV : imageCondition q ≤ V :=
      (le_iInf hF).trans (le_iSup (fun f : J → I => ⨅ j,(C j).value (f j)) f)
    exact imageCondition_ne_bot_r50 q (disjoint_compl_right.out _ hQV
      ((imageCondition_mono_r50 hqp).trans hp))
  · let f (j : J) : I := False.elim (hJ ⟨j⟩)
    have hFV : (⊤ : RO P) ≤ V := le_iSup_of_le f (le_iInf (fun j => False.elim (hJ ⟨j⟩)))
    exact hn hFV

def CheckedGroundLimit {I : Type} [LinearOrder I] (d : I) : Prop :=
  (∃ i,i < d) ∧ ∀ i < d,∃ j,i < j ∧ j < d

variable {I : Type} [LinearOrder I] [WellFoundedLT I] [Nonempty I]

def AllCountableGroundBounded (I : Type) [LT I] : Prop :=
  ∀ f : ℕ → I,∃ b,∀ n,f n < b

theorem all_countable_groundProfiles_bounded (hI : AllCountableGroundBounded I)
    {J : Type} [Countable J] (f : J → I) : ∃ b,∀ j,f j < b := by
  by_cases hJ : Nonempty J
  · letI : Nonempty J := hJ
    obtain ⟨e,he⟩ := exists_surjective_nat J
    obtain ⟨b,hb⟩ := hI (f ∘ e)
    exact ⟨b,by intro j; obtain ⟨n,rfl⟩ := he j; exact hb n⟩
  · exact ⟨Classical.choice inferInstance,fun j => False.elim (hJ ⟨j⟩)⟩

theorem actual_limit_of_profile (hI : AllCountableGroundBounded I)
    {J : Type} [Countable J] [Nonempty J] [Preorder J]
    (hJ : ∀ j : J,∃ k,j < k) (f : J → I) (hf : StrictMono f) :
    ∃ t,CheckedGroundLimit t ∧ (∀ j,f j < t) ∧
      ∀ s < t,∃ j,s < f j := by
  let U : Set I := {b | ∀ j,f j < b}
  have hU : U.Nonempty := all_countable_groundProfiles_bounded hI f
  obtain ⟨t,ht,hMin⟩ := wellFounded_lt.has_min U hU
  have hCof (s : I) (hs : s < t) : ∃ j,s < f j := by
    by_contra hn
    have hS (j : J) : f j ≤ s := le_of_not_gt (fun h => hn ⟨j,h⟩)
    have hb : s ∈ U := by
      intro j
      obtain ⟨k,hk⟩ := hJ j
      exact (hf hk).trans_le (hS k)
    exact hMin s hb hs
  refine ⟨t,⟨⟨f (Classical.choice inferInstance),ht _⟩,?_⟩,ht,hCof⟩
  intro s hs
  obtain ⟨j,hj⟩ := hCof s hs
  exact ⟨f j,hj,ht j⟩

end JSP000930.Negative
