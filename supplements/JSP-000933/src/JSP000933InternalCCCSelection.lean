import JSP000933DisjointFixedCardClique

open scoped Cardinal

namespace JSP000933
namespace CantorCodes

open BooleanCompletion BooleanTwoStep OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem nonzero_meet_of_uncountable_r157 (hCCC : BooleanCCC B) {I : Type}
    (hI : ¬ Countable I) (u : I → B) (hU : ∀ i, u i ≠ ⊥) :
    ∃ i j, i ≠ j ∧ u i ⊓ u j ≠ ⊥ := by
  classical
  by_contra h
  have hInj : Function.Injective u := by
    intro i j he
    by_contra hn
    apply h
    refine ⟨i,j,hn,?_⟩
    rw [← he]
    simpa using hU i
  have hCount : (Set.range u).Countable := by
    apply hCCC
    · rintro _ ⟨i,rfl⟩
      exact hU i
    · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hne
      apply disjoint_iff_inf_le.mpr
      apply le_of_eq
      by_contra hn
      exact h ⟨i,j,fun he => hne (congrArg u he),hn⟩
  have hAll : (Set.univ : Set I).Countable := (hCount.preimage hInj).mono (show (Set.univ : Set I) ⊆ u ⁻¹' Set.range u from fun i _ => Set.mem_range_self i)
  exact hI (Set.countable_univ_iff.mp hAll)

theorem booleanPair_allCards_r157 (hCCC : BooleanCCC B)
    (D : (ℕ → B) → B) (K : Word × Word → B) (mark : B)
    (hIrr : ∀ x, mark ⊓ D x ≤ (colorValue K x x)ᶜ)
    (hSym : ∀ x y, (mark ⊓ (D x ⊓ D y)) ⊓ colorValue K x y ≤ colorValue K y x)
    (S : BooleanAvoidanceSchedule B) (Y : OmegaOneIndex → ℕ → B)
    (hY : ∀ i, mark ≤ D (Y i))
    (hAvoid : ∀ j, AvoidsOn D K mark S j (fun i => Y i.1) (Y j)) :
    ∀ n, BooleanPairForCard mark (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) n := by
  classical
  let D' (i : OmegaOneIndex) := D (Y i)
  let K' (i j : OmegaOneIndex) := colorValue K (Y i) (Y j)
  intro n
  induction n with
  | zero =>
    intro I s w hI hCard hW
    obtain ⟨i,j,hij,hmeet⟩ := nonzero_meet_of_uncountable_r157 hCCC hI w (fun i => (hW i).1)
    have he (i : I) : s i = ∅ := Finset.card_eq_zero.mp (hCard i)
    refine ⟨i,j,hij,w i ⊓ w j,hmeet,inf_le_left,inf_le_right,?_⟩
    rw [he i,he j,Finset.empty_union,cliqueAdmitted_empty_r121] <;> exact le_top
  | succ n lower =>
    intro I s w hI hCard hW
    by_cases hShared : ∃ c : OmegaOneIndex, ¬ ({i : I | c ∈ s i} : Set I).Countable
    · obtain ⟨c,hc⟩ := hShared
      let V : Set I := {i | c ∈ s i}
      have hV : ¬ Countable (↥V) := fun h => hc (Set.countable_coe_iff.mp h)
      let erase (i : ↥V) := (s i.1).erase c
      have he (i : ↥V) : (erase i).card = n := by
        rw [show erase i = (s i.1).erase c from rfl,Finset.card_erase_of_mem i.2,hCard i.1] <;> omega
      obtain ⟨i,j,hij,q,hq,hqi,hqj,hSmall⟩ := lower erase (fun i => w i.1) hV he
        (fun i => ⟨(hW i.1).1,(hW i.1).2.trans (cliqueAdmitted_anti_r121 mark D' K'
          (Finset.erase_subset c (s i.1)))⟩)
      exact ⟨i.1,j.1,fun h => hij (Subtype.ext h),q,hq,hqi,hqj,
        cliqueAdmitted_restoreShared_r155 mark D' K' i.2 j.2
          (hqi.trans (hW i.1).2) (hqj.trans (hW j.1).2) hSmall⟩
    · have hHit (c : OmegaOneIndex) : ({i : I | c ∈ s i} : Set I).Countable := by
        by_contra h
        exact hShared ⟨c,h⟩
      obtain ⟨e,he,hDis⟩ := exists_disjointLabelSequence_r154 s hI hHit
      obtain ⟨i,j,hij,q,hq,hqi,hqj,hAll⟩ := booleanPair_disjoint_succ_r156 hCCC D K mark hIrr hSym
        S Y hY hAvoid lower (fun j => s (e j)) (fun j => w (e j)) OmegaOneIndex_not_countable_r61
        (fun j => hCard (e j)) (fun j => hW (e j)) hDis
      exact ⟨e i,e j,fun h => hij (he h),q,hq,hqi,hqj,hAll⟩

theorem countableAntichains_cliqueLabelStage_r157 (mark : B)
    (d : OmegaOneIndex → B) (K : OmegaOneIndex → OmegaOneIndex → B)
    (hPair : ∀ n, BooleanPairForCard mark d K n) :
    HasCountableAntichains (Condition (cliqueLabelStage mark d K)) := by
  classical
  intro F hAnt
  by_contra hF
  have hU : ¬ Countable (↥F) := fun h => hF (Set.countable_coe_iff.mp h)
  let size (i : ↥F) := (OrderDual.ofDual i.1.name).card
  obtain ⟨n,hN⟩ := exists_uncountable_fiber_r151 hU size
  let I := {i : ↥F // size i = n}
  let s (i : I) := OrderDual.ofDual i.1.1.name
  let w (i : I) := i.1.1.base
  obtain ⟨i,j,hij,q,hq,hqi,hqj,hQ⟩ := hPair n s w hN
    (fun i => i.2) (fun i => ⟨i.1.1.nonzero,i.1.1.admitted⟩)
  have he : i.1.1 ≠ j.1.1 := fun h => hij (Subtype.ext (Subtype.ext h))
  apply hAnt i.1.1 i.1.2 j.1.1 j.1.2 he
  apply (compatible_iff_nonzero_r78 i.1.1 j.1.1).mpr
  rw [cliqueLabelStage_comp_r121]
  exact fun h => hq (le_bot_iff.mp ((le_inf (le_inf hqi hqj) hQ).trans_eq h))

theorem exists_CH_activatedCliqueFamily_r157 (hCCC : BooleanCCC B)
    (c : B → RealCode) (hc : Function.Injective c) (CH : (𝔠 : Cardinal.{0}) = ℵ₁)
    (D : (ℕ → B) → B) (hD : RealTestExt D) (K : Word × Word → B) (mark : B)
    (hNo : ∀ u : CoverCode B, mark ≤ (goodCoverValue id D K u)ᶜ)
    (hIrr : ∀ x, mark ⊓ D x ≤ (colorValue K x x)ᶜ)
    (hSym : ∀ x y, (mark ⊓ (D x ⊓ D y)) ⊓ colorValue K x y ≤ colorValue K y x) :
    ∃ Y : OmegaOneIndex → ℕ → B,
      (∀ i, mark ≤ D (Y i)) ∧
      (∀ i j, i ≠ j → Disjoint mark (realEqValue (Y i) (Y j))) ∧
      HasCountableAntichains
        (Condition (cliqueLabelStage mark (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)))) := by
  obtain ⟨S⟩ := exists_BooleanAvoidanceSchedule_r144 c hc CH
  obtain ⟨Y,hY,hSep,hAvoid⟩ := exists_BooleanAvoidanceSequence_r146 D hD K mark hNo hIrr S
  exact ⟨Y,hY,hSep,countableAntichains_cliqueLabelStage_r157 mark _ _
    (booleanPair_allCards_r157 hCCC D K mark hIrr hSym S Y hY hAvoid)⟩

end CantorCodes
end JSP000933
