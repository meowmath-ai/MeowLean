import JSP000930MixedPaletteTable
import JSP000933PreparedSmallTraceEnum
import JSP000933RelativeMixedEnumTransport
import JSP000933PreparedNameCodes

open scoped Cardinal

namespace JSP000930
namespace MixedPalettes

open JSP000933.PreparedModel JSP000933.RelativeOCA JSP000933.OpenGraphForcing
  JSP000933.BooleanNames JSP000933.BooleanCompletion

variable {B : Type} [CompleteBooleanAlgebra B]

theorem mixed_ranks_of_small_ground_type
    (F : CompleteValueMap PreparedBA B) (J : Type) (hJ : #J ≤ 𝔠) :
    ∃ R : J → Label B, SeparatesRanks R := by
  classical
  by_cases hN : Nonempty J
  · letI : Nonempty J := hN
    obtain ⟨E0⟩ := prepared_smallMixedTraceEnum_r471 J hJ
    let E := E0.map_r470 F
    let w (j : J) (i : OmegaOneIndex) : B :=
      firstChoiceCell (fun t : OmegaOneIndex => E.cell t j) i
    have hLe (j : J) (i : OmegaOneIndex) : w j i ≤ E.cell i j :=
      firstChoiceCell_le_r435 _ _
    have hApart (j : J) : Pairwise fun i i' => Disjoint (w j i) (w j i') := by
      intro i i' h
      rcases lt_or_gt_of_ne h with h | h
      · exact firstChoiceCell_disjoint_r435 _ i i' h
      · exact (firstChoiceCell_disjoint_r435 _ i' i h).symm
    have hCover (j : J) : (⨆ i : OmegaOneIndex, w j i) = ⊤ :=
      (firstChoiceCell_join_r435 _).trans (E.colFull j)
    refine ⟨(fun j => ⟨w j, hApart j, (fun _ => le_top), hCover j⟩), ?_⟩
    intro i j hij t
    exact (E.rowApart t hij).mono (hLe i t) (hLe j t)
  · refine ⟨(fun j => False.elim (hN ⟨j⟩)), ?_⟩
    intro j
    exact (hN ⟨j⟩).elim

private theorem strict_ground_rank_small (a : GroundContinuumSuccIndex) :
    #{b : GroundContinuumSuccIndex // b < a} ≤ 𝔠 :=
  Order.lt_succ_iff.mp (continuumSuccInitial_card_lt_r406 a)

private theorem weak_ground_rank_small (a : GroundContinuumSuccIndex) :
    #{b : GroundContinuumSuccIndex // b ≤ a} ≤ 𝔠 := by
  have hUnit₀ : #Unit ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hUnit : #Unit < GroundContinuumSucc :=
    hUnit₀.trans_lt (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _))
  obtain ⟨b,hb⟩ := continuumSuccIndex_family_bounded_r399 (fun _ : Unit => a) hUnit
  let f (x : {x : GroundContinuumSuccIndex // x ≤ a}) : {x : GroundContinuumSuccIndex // x < b} :=
    ⟨x.1, x.2.trans_lt (hb ())⟩
  exact (Cardinal.mk_le_of_injective (f := f)
    (fun _ _ he => Subtype.ext (congrArg (fun t : {t : GroundContinuumSuccIndex // t < b} => t.val) he))).trans (strict_ground_rank_small b)

noncomputable def preparedRankSystem (F : CompleteValueMap PreparedBA B) :
    RankSystem GroundContinuumSuccIndex B where
  strict := fun a => Classical.choose
    (mixed_ranks_of_small_ground_type F _ (strict_ground_rank_small a))
  strict_separates := fun a => Classical.choose_spec
    (mixed_ranks_of_small_ground_type F _ (strict_ground_rank_small a))
  weak := fun a => Classical.choose
    (mixed_ranks_of_small_ground_type F _ (weak_ground_rank_small a))
  weak_separates := fun a => Classical.choose_spec
    (mixed_ranks_of_small_ground_type F _ (weak_ground_rank_small a))

end MixedPalettes
end JSP000930
