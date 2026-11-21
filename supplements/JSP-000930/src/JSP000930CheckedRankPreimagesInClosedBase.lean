import JSP000930AnalyticFiniteSupportLimit
import JSP000930CoherentPreparedPalettes
import JSP000933CountableChoiceProfiles

open Lattice
open scoped Flypitch bSet

namespace JSP000930.MixedPalettes

open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.RelativeOCA
open JSP000933.OpenGraphForcing JSP000933.CantorCodes

variable {P D X : Type} [Preorder P] [LinearOrder D] [Nonempty D]

private theorem rank_Iic_countable_p135 (c : OmegaOneIndex) : Countable (Set.Iic c) := by
  have hC : (Set.Iio c).Countable :=
    Set.countable_coe_iff.mp (OmegaOneIndex_initial_countable_r61 c)
  apply Set.countable_coe_iff.mpr
  apply (hC.union (Set.countable_singleton c)).mono
  intro t ht
  change t ≤ c at ht
  rcases lt_or_eq_of_le ht with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

open scoped Classical in
set_option maxHeartbeats 600000 in
theorem countablyClosed_rank_preimages_have_checkedBound
    (hP : IsCountablyClosed P)
    (rank : X → Label (RO P)) (hRank : SeparatesRanks rank)
    (height : X → D) (hB : ∀ a : ℕ → D,∃ e : D,∀ n,a n<e)
    (cut : OmegaOneIndex) :
    (⊤ : RO P) ≤ ⨆ d : D, ⨅ x : X, ⨅ c : Set.Iic cut,
      if height x < d then ⊤ else ((rank x).value c.1)ᶜ := by
  classical
  let U (d : D) : RO P := ⨅ x : X, ⨅ c : Set.Iic cut,
    if height x<d then ⊤ else ((rank x).value c.1)ᶜ
  let V : RO P := ⨆ d,U d
  change ⊤ ≤ V
  by_contra hn
  have hV : Vᶜ ≠ ⊥ := fun he => hn ((compl_eq_bot.mp he).ge)
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 Vᶜ hV
  let C := Set.Iic cut
  letI : Countable C := rank_Iic_countable_p135 cut
  letI : Nonempty C := ⟨⟨cut,show cut ≤ cut from le_rfl⟩⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat C
  let chooseByRank (n : ℕ) (x : Option X) : RO P :=
    match x with
    | some x => (rank x).value (f n).1
    | none => (⨆ x : X,(rank x).value (f n).1)ᶜ
  have hTop (n : ℕ) : (⊤ : RO P) ≤ ⨆ x,chooseByRank n x := by
    let v := ⨆ x : X,(rank x).value (f n).1
    have h1 : v ≤ ⨆ x,chooseByRank n x := by
      apply iSup_le
      intro x
      exact le_iSup (chooseByRank n) (some x)
    have h2 : vᶜ ≤ ⨆ x,chooseByRank n x := le_iSup (chooseByRank n) none
    rw [← (sup_compl_eq_top : v ⊔ vᶜ = ⊤)]
    exact sup_le h1 h2
  obtain ⟨q,g,hqp,hg⟩ := exists_allChoiceProfiles_r411 hP p chooseByRank
    (fun n => le_top.trans (hTop n))
  let d₀ : D := Classical.choice ‹Nonempty D›
  let heightOr (n : ℕ) : D := match g n with
    | some x => height x
    | none => d₀
  obtain ⟨d,hd⟩ := hB heightOr
  have hU : imageCondition q ≤ U d := by
    unfold U
    apply le_iInf
    intro x
    apply le_iInf
    intro c
    by_cases hx : height x < d
    · simp only [ite_eq_left hx,le_top]
    · rw [ite_eq_right hx]
      obtain ⟨n,hnc⟩ := hf c
      have hF := hg n
      cases he : g n with
      | none =>
        have hh : imageCondition q ≤ (⨆ y : X,(rank y).value c.1)ᶜ := by
          simpa only [he,chooseByRank,hnc] using hF
        exact hh.trans (compl_le_compl (le_iSup (fun y => (rank y).value c.val) x))
      | some y =>
        have hy : height y<d := by simpa only [heightOr,he] using hd n
        have hxy : y≠x := fun h => hx (h ▸ hy)
        have hh : imageCondition q ≤ (rank y).value c.1 := by
          simpa only [he,chooseByRank,hnc] using hF
        exact hh.trans (le_compl_iff_disjoint_right.mpr (hRank y x hxy c.1))
  exact imageCondition_ne_bot_r50 q (disjoint_compl_right.out _
    (hU.trans (le_iSup U d)) ((imageCondition_mono_r50 hqp).trans hp))

end JSP000930.MixedPalettes
