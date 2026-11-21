import JSP000930NegativeMixSiteCore
import JSP000933RelativeChoiceNormalization

open bSet Cardinal Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.RelativeOCA JSP000930.Positive
  JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_newSite_captures_trial {I : Type}
    (hB : BoundsSmallKappaNames B) (hI : Cardinal.mk I < GroundContinuumSucc)
    (old : I → ComplexBits B) (u : KappaSiteIndex → ComplexBits B)
    (hu : ∀ j,(u j).CutOn ⊤)
    (hd : ∀ i j,i ≠ j → ((u i).name =ᴮ (u j).name) = (⊥ : B))
    (z : ComplexBits B) (p : B) (hz : z.CutOn p) :
    ∃ y : ComplexBits B, y.CutOn ⊤ ∧
      (∀ i, ((y.name =ᴮ (old i).name) : B) = ⊥) ∧
      p ≤ (⨆ i,z.name =ᴮ (old i).name) ⊔ (z.name =ᴮ y.name) := by
  classical
  let D : B := ⨆ i,z.name =ᴮ (old i).name
  let good : B := p ⊓ Dᶜ
  let V (j : KappaSiteIndex) : B := (⨆ i,(old i).name =ᴮ (u j).name)ᶜ
  let C := firstChoiceCell V
  let w : Option KappaSiteIndex → B
    | none => good
    | some j => goodᶜ ⊓ C j
  let v : Option KappaSiteIndex → ComplexBits B
    | none => z
    | some j => u j
  have hV : (⨆ j,V j) = ⊤ := availableReservoirSites_cover hB hI old u hd
  have hCover : (⨆ a,w a) = ⊤ := by
    apply top_unique
    have h₀ : good ≤ ⨆ a,w a := le_iSup w none
    have h₁ : goodᶜ ≤ ⨆ a,w a := by
      have h := iSup_le (fun j => le_iSup w (some j))
      change (⨆ j,goodᶜ ⊓ C j) ≤ _ at h
      rw [← inf_iSup_eq,firstChoiceCell_join_r435,hV,inf_top_eq] at h
      exact h
    rw [← (sup_compl_eq_top (x := good))]
    exact sup_le h₀ h₁
  have hDisj : ∀ a b,a ≠ b → Disjoint (w a) (w b) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some j => exact disjoint_compl_right.mono_right inf_le_left
    | some i =>
      cases b with
      | none => exact disjoint_compl_left.mono_left inf_le_left
      | some j =>
        have hij : i ≠ j := fun h => hab (congrArg some h)
        have hc : Disjoint (C i) (C j) := by
          rcases lt_or_gt_of_ne hij with h | h
          · exact firstChoiceCell_disjoint_r435 V i j h
          · exact (firstChoiceCell_disjoint_r435 V j i h).symm
        exact hc.mono inf_le_right inf_le_right
  let y := mixSite w v
  refine ⟨y,?_,?_,?_⟩
  · rw [← hCover]
    apply mixSite_proper w v hDisj
    intro t
    cases t with
    | none =>
      exact ⟨JSP000930.Positive.properCutOn_mono inf_le_left hz.1,
        JSP000930.Positive.properCutOn_mono inf_le_left hz.2⟩
    | some j =>
      exact ⟨JSP000930.Positive.properCutOn_mono le_top (hu j).1,
        JSP000930.Positive.properCutOn_mono le_top (hu j).2⟩
  · intro i
    apply le_bot_iff.mp
    have he : (y.name =ᴮ (old i).name) ≤ (⨆ a,w a) ⊓ (y.name =ᴮ (old i).name) := by
      rw [hCover,top_inf_eq]
    apply he.trans
    rw [iSup_inf_eq]
    apply iSup_le
    intro t
    have ht : w t ≤ (v t).name =ᴮ y.name := sameMaskedComplex_name (mixSite_on w v hDisj t)
    have hEq : w t ⊓ (y.name =ᴮ (old i).name) ≤ (v t).name =ᴮ (old i).name :=
      bv_trans (inf_le_left.trans ht) inf_le_right
    cases t with
    | none =>
      exact (le_inf (inf_le_left.trans (show good ≤ Dᶜ from inf_le_right))
        (hEq.trans (le_iSup (fun i => z.name =ᴮ (old i).name) i))).trans_eq compl_inf_eq_bot
    | some j =>
      have hn : w (some j) ≤ ((old i).name =ᴮ (u j).name)ᶜ :=
        inf_le_right.trans ((firstChoiceCell_le_r435 V j).trans
          (compl_le_compl (le_iSup (fun i => (old i).name =ᴮ (u j).name) i)))
      exact (le_inf (inf_le_left.trans hn) (bv_symm hEq)).trans_eq compl_inf_eq_bot
  · have ht : good ≤ z.name =ᴮ y.name := sameMaskedComplex_name (mixSite_on w v hDisj none)
    change p ≤ D ⊔ (z.name =ᴮ y.name)
    have hp : p ≤ p ⊓ (D ⊔ Dᶜ) := by rw [sup_compl_eq_top,inf_top_eq]
    apply hp.trans
    rw [inf_sup_left]
    exact sup_le_sup inf_le_right ht

end JSP000930.Negative
