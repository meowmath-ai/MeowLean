import JSP000933PreparedSmallDiamondClosure
import JSP000933BooleanNamedCliqueStage
import JSP000933CountablyClosedNoReals

open Cardinal Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

structure CollapseBasicCondition where
  basic : BaseCollapseBasic

noncomputable def basicValue (p : CollapseBasicCondition) : CHBase := baseCollapseImage p.basic

noncomputable instance : Preorder CollapseBasicCondition where
  le p q := basicValue p≤basicValue q
  le_refl _ := le_rfl
  le_trans _ _ _ hp hq := hp.trans hq

noncomputable def baseBasicEmpty : CollapseBasicCondition :=
  ⟨CollapsePoset.empty zero_lt_aleph0_succ⟩

theorem basicValue_ne_bot_r401 (p : CollapseBasicCondition) : basicValue p≠⊥ := by
  intro he
  exact baseCollapse_denseOmegaClosed_r390.1.1 ⟨p.basic,he⟩

theorem basicValue_dense_r401 (b : CHBase) (hb : b≠⊥) :
    ∃ p : CollapseBasicCondition, basicValue p≤b := by
  obtain ⟨v,⟨a,rfl⟩,hv⟩ :=
    baseCollapse_denseOmegaClosed_r390.1.2 b (bot_lt_iff_ne_bot.mpr hb)
  exact ⟨⟨a⟩,hv⟩

theorem basicValue_card_le_continuum_r401 : Cardinal.mk CollapseBasicCondition≤𝔠 :=
  (Cardinal.mk_le_of_injective (show Function.Injective CollapseBasicCondition.basic from by
    intro p q he
    cases p
    cases q
    cases he
    rfl)).trans baseCollapseBasic_card_le_continuum_r391

theorem basicValue_pair_compatible_r401 (p q : CollapseBasicCondition)
    (h : ¬Disjoint (basicValue p) (basicValue q)) :
    ∃ s : CollapseBasicCondition, s≤p ∧ s≤q := by
  obtain ⟨s,hs⟩ := basicValue_dense_r401 (basicValue p⊓basicValue q)
    (fun he => h (disjoint_iff_inf_le.mpr he.le))
  exact ⟨s,hs.trans inf_le_left,hs.trans inf_le_right⟩

abbrev PreparedCondition := CollapseBasicCondition×SmallDiamondCondition

noncomputable instance : Nonempty PreparedCondition := ⟨(baseBasicEmpty,emptySmallDiamond)⟩

abbrev PreparedBA := RO PreparedCondition

theorem preparedProduct_countablyClosed_r401 : IsCountablyClosed PreparedCondition := by
  intro s hS
  let f (n : ℕ) := basicValue (s n).1
  have hRange (n : ℕ) : f n∈Set.range baseCollapseImage := ⟨(s n).1.basic,rfl⟩
  have hPos (n : ℕ) : ⊥<f n := bot_lt_iff_ne_bot.mpr (basicValue_ne_bot_r401 (s n).1)
  have hStep (n : ℕ) : f (n+1)≤f n := (hS (Nat.le_succ n)).1
  obtain ⟨p,hp⟩ := baseCollapse_denseOmegaClosed_r390.2 f hRange hPos hStep
  have hNat : Cardinal.mk ℕ<GroundContinuumSucc := by
    rw [Cardinal.mk_nat]
    exact Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _)
  have hChain (i j : ℕ) : (s i).2≤(s j).2 ∨ (s j).2≤(s i).2 := by
    rcases le_total i j with h | h
    · exact Or.inr (hS h).2
    · exact Or.inl (hS h).2
  obtain ⟨q,hq⟩ := smallDiamond_chain_lower_r400 (fun n => (s n).2) hNat hChain
  refine ⟨(⟨p⟩,q),fun n => ⟨?_,hq n⟩⟩
  change baseCollapseImage p≤f n
  exact hp.le.trans (iInf_le f n)

end PreparedModel
end JSP000933
