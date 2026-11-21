import JSP000930PositivePreserveCheckedOmegaOne
import JSP000933RelativeMixedEnumTransport
import JSP000933MarkedTraceRectangles

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.PreparedModel JSP000933.BooleanNames JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.BooleanCompletion JSP000933.MarkedForcing

noncomputable def totalBaseMap {B N : Type} [CompleteBooleanAlgebra B]
    (Q : ValuedPoset B N) : CompleteValueMap B (TotalBA Q) where
  toFun := baseEmbed Q
  injective := fun _ _ h => le_antisymm ((baseEmbed_reflects_r428 Q).mp h.le)
    ((baseEmbed_reflects_r428 Q).mp h.ge)
  monotone := baseEmbed_mono_r427 Q
  map_bot := baseEmbed_bot_r427 Q
  map_top := baseEmbed_top_r427 Q
  map_compl := baseEmbed_compl_r427 Q
  map_inf := baseEmbed_meets_r429 Q
  map_iSup := fun U => baseEmbed_joins_r427 Q U
  map_iInf := fun U => by
    calc
      baseEmbed Q (⨅ i,U i) = baseEmbed Q ((⨆ i,(U i)ᶜ)ᶜ) := by
        rw [compl_iSup]
        simp only [compl_compl]
      _ = ⨅ i,baseEmbed Q (U i) := by
        rw [baseEmbed_compl_r427,baseEmbed_joins_r427,compl_iSup]
        simp only [baseEmbed_compl_r427,compl_compl]

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B] [LinearOrder I] [WellFoundedLT I]

theorem mixedEnumeration_injects_into
    (E : MixedEnumeration I J B) (x : J → bSet B) (y : I → bSet B) (D R : bSet B)
    (hD : ∀ a,(a ∈ᴮ D) ≤ ⨆ j,a =ᴮ x j)
    (hR : ∀ i,(⊤ : B) ≤ y i ∈ᴮ R)
    (hx : ∀ j k,j ≠ k → (x j =ᴮ x k) = ⊥)
    (hy : ∀ i l,i ≠ l → (y i =ᴮ y l) = ⊥) :
    (⊤ : B) ≤ injects_into D R := by
  classical
  let W (z : I × J) := firstChoiceCell (fun i => E.cell i z.2) z.1
  have hW (i : I) (j : J) : W (i,j) ≤ E.cell i j :=
    firstChoiceCell_le_r435 _ _
  have hCol (j : J) : (⨆ i : I,W (i,j)) = ⊤ :=
    (firstChoiceCell_join_r435 _).trans (E.colFull j)
  apply weightedGraph_injects_into (fun z : I × J => x z.2) (fun z : I × J => y z.1) W D R
  · rintro ⟨i,j⟩ ⟨k,l⟩
    by_cases h : j = l
    · subst l
      by_cases h' : i = k
      · subst k
        exact bv_refl
      · have hd : Disjoint (W (i,j)) (W (k,j)) := by
          rcases lt_or_gt_of_ne h' with hi | hk
          · exact firstChoiceCell_disjoint_r435 _ i k hi
          · exact (firstChoiceCell_disjoint_r435 _ k i hk).symm
        exact inf_le_left.trans ((disjoint_iff_inf_le.mp hd).trans bot_le)
    · simp only [hx _ _ h,inf_bot_eq,bot_le]
  · rintro ⟨i,j⟩ ⟨k,l⟩
    by_cases h : i = k
    · subst k
      by_cases h' : j = l
      · subst l
        exact bv_refl
      · have hd : Disjoint (W (i,j)) (W (i,l)) :=
          ((E.rowApart i h').mono_left (hW i j)).mono_right (hW i l)
        exact inf_le_left.trans ((disjoint_iff_inf_le.mp hd).trans bot_le)
    · simp only [hy _ _ h,inf_bot_eq,bot_le]
  · intro a
    apply (hD a).trans
    apply iSup_le
    intro j
    have h : (a =ᴮ x j) = (⨆ i : I,W (i,j)) ⊓ (a =ᴮ x j) := by
      rw [hCol,top_inf_eq]
    rw [h,iSup_inf_eq]
    apply iSup_le
    intro i
    exact le_iSup (fun z : I × J => W z ⊓ (a =ᴮ x z.2)) (i,j)
  · exact fun p => hR p.1

end JSP000930.Positive
