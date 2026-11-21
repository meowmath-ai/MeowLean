import JSP000930NegativeOmegaOneSegmentedOccurrences
import JSP000933RelativeKappaAntichainBound

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion

variable {B D J : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]

theorem prefixReduce_meet_of_embedded (F : CompleteValueMap B D) (x : D) (b : B) :
    prefixReduce F (x ⊓ F.toFun b) = prefixReduce F x ⊓ b := by
  let G := prefixReduce_gc F
  apply le_antisymm
  · exact le_inf (G.monotone_l inf_le_left)
      ((prefixReduce_le_iff F _ _).2 inf_le_right)
  · let p := prefixReduce F (x ⊓ F.toFun b)
    let q := prefixReduce F (x ⊓ F.toFun bᶜ)
    have hp : p ≤ b := (prefixReduce_le_iff F _ _).2 inf_le_right
    have hq : q ≤ bᶜ := (prefixReduce_le_iff F _ _).2 inf_le_right
    have hD : (x ⊓ F.toFun b) ⊔ (x ⊓ F.toFun bᶜ) = x := by
      rw [F.map_compl,← inf_sup_left,sup_compl_eq_top,inf_top_eq]
    have hSplit : prefixReduce F x = p ⊔ q :=
      (congrArg (prefixReduce F) hD.symm).trans G.l_sup
    rw [hSplit,inf_sup_right,inf_eq_left.mpr hp]
    have hn : q ⊓ b = ⊥ := (disjoint_compl_left.mono_left hq).eq_bot
    rw [hn,sup_bot_eq]

theorem projectedCCC_forbids_skew_unbounded
    (hB : BoundsCountableOmegaOneNames B) (F : CompleteValueMap B D)
    (hCCC : ProjectedAntichainCCC (prefixReduce F))
    (rank row : J → OmegaOneIndex) (X : J → D) (W : J → B)
    (hW : ∀ j,W j ≤ prefixReduce F (X j))
    (hApart : ∀ i j,rank i < row j → Disjoint (X i) (X j))
    (m : B) (hTail : ∀ b,m ≤ ⨆ j : {j : J // b < row j},W j.val) :
    m = ⊥ := by
  obtain ⟨S⟩ := exists_segmentedOmegaChoices hB rank row W m hTail
  let Y (i : OmegaOneIndex) := ⨆ j,X j ⊓ F.toFun ((S.pick i).value j)
  have hY (i j : OmegaOneIndex) (hij : i < j) : Disjoint (Y i) (Y j) := by
    apply disjoint_iff_inf_le.mpr
    simp only [Y,iSup_inf_iSup]
    apply iSup_le
    rintro ⟨x,y⟩
    by_cases hr : rank x < row y
    · exact disjoint_iff_inf_le.mp ((hApart x y hr).mono inf_le_left inf_le_left)
    · have hZ₀ := (inf_le_inf (S.separated i j hij y) le_rfl).trans
        (guardByChoice_elim_r445 (S.pick i) (fun t => occurrenceBefore rank row t y) x)
      have hZ : (S.pick i).value x ⊓ (S.pick j).value y = ⊥ := by
        apply le_bot_iff.mp
        rw [inf_comm]
        simpa only [occurrenceBefore,ite_eq_right hr] using hZ₀
      have hF : F.toFun ((S.pick i).value x) ⊓ F.toFun ((S.pick j).value y) = ⊥ := by
        rw [← F.map_inf,hZ,F.map_bot]
      exact (inf_le_inf inf_le_right inf_le_right).trans_eq hF
  have hProj (i : OmegaOneIndex) : prefixReduce F (Y i) = m := by
    change prefixReduce F (⨆ j, X j ⊓ F.toFun ((S.pick i).value j)) = m
    rw [(prefixReduce_gc F).l_iSup]
    have he (j : J) : prefixReduce F (X j) ⊓ (S.pick i).value j = (S.pick i).value j :=
      inf_eq_right.mpr ((S.valid i j).trans (hW j))
    simp only [prefixReduce_meet_of_embedded,he,(S.pick i).covers]
  have he := hCCC Y hY
  rw [show (fun i => prefixReduce F (Y i)) = fun _ => m from funext hProj,
    unboundedValue_const_r475] at he
  exact he

end JSP000930.Negative
