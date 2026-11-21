import JSP000930NegativeNamedPaletteScheduleCardinals
import JSP000930PositiveNativeTaylorLimitRespectsMask
import JSP000930PositiveCheckedKappaPreservation

open bSet Cardinal Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.RelativeOCA
  JSP000930.Positive JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev KappaSiteIndex := GroundContinuumSuccIndex

theorem availableReservoirSites_cover {I : Type}
    (hB : BoundsSmallKappaNames B) (hI : Cardinal.mk I < GroundContinuumSucc)
    (old : I → ComplexBits B) (u : KappaSiteIndex → ComplexBits B)
    (hDistinct : ∀ i j,i ≠ j → ((u i).name =ᴮ (u j).name) = (⊥ : B)) :
    (⨆ j : KappaSiteIndex, (⨆ i, (old i).name =ᴮ (u j).name)ᶜ) = (⊤ : B) := by
  let V (i : I) (j : KappaSiteIndex) : B := (old i).name =ᴮ (u j).name
  classical
  let a₀ : KappaSiteIndex := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
  let W (i : I) (j : KappaSiteIndex) : B :=
    V i j ⊔ if j = a₀ then (⨆ n,V i n)ᶜ else ⊥
  have hW (i : I) : (⨆ j,W i j) = ⊤ := by
    apply top_unique
    rw [← (sup_compl_eq_top (x := ⨆ n,V i n))]
    exact sup_le (iSup_le (fun j => le_sup_left.trans (le_iSup (W i) j)))
      ((show (⨆ n,V i n)ᶜ ≤ W i a₀ by simp [W]).trans (le_iSup (W i) a₀))
  have hCover : (⨆ a : KappaSiteIndex, ⨅ i,⨆ j : {j : KappaSiteIndex // j < a},W i j.val) = ⊤ :=
    top_unique ((le_iInf (fun i => (hW i).ge)).trans (hB I hI W))
  apply top_unique
  rw [← hCover]
  apply iSup_le
  intro a
  apply le_iSup_of_le a
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff_inf_le,inf_iSup_eq]
  apply iSup_le
  intro i
  apply (inf_le_inf_right _ (iInf_le _ i)).trans
  rw [iSup_inf_eq]
  apply iSup_le
  intro j
  change W i j.val ⊓ V i a ≤ ⊥
  apply disjoint_iff_inf_le.mp
  unfold W
  rw [disjoint_sup_left]
  refine ⟨disjoint_iff_inf_le.mpr ?_,?_⟩
  · calc
      V i j.val ⊓ V i a ≤ ((u j.val).name =ᴮ (u a).name) :=
        bv_trans (bv_symm inf_le_left) inf_le_right
      _ = ⊥ := hDistinct _ _ (ne_of_lt j.property)
  · by_cases hj : j.val = a₀
    · rw [ite_eq_left hj]
      exact disjoint_compl_left.mono_right (le_iSup (V i) a)
    · rw [ite_eq_right hj]
      exact disjoint_bot_left

noncomputable def mixSite {T : Type} (w : T → B) (u : T → ComplexBits B) :
    ComplexBits B :=
  ⟨fun q => ⨆ t,w t ⊓ (u t).re q, fun q => ⨆ t,w t ⊓ (u t).im q⟩

theorem mixSite_on {T : Type} (w : T → B) (u : T → ComplexBits B)
    (hw : ∀ i j,i ≠ j → Disjoint (w i) (w j)) (t : T) :
    sameMaskedComplex (w t) (u t) (mixSite w u) := by
  classical
  have h (f : T → B) : w t ⊓ f t = w t ⊓ (⨆ j,w j ⊓ f j) := by
    apply le_antisymm
    · exact le_inf inf_le_left (le_iSup (fun j => w j ⊓ f j) t)
    · rw [inf_iSup_eq]
      apply iSup_le
      intro j
      by_cases hj : t = j
      · subst j
        exact inf_le_right
      · exact ((inf_le_inf_left _ inf_le_left).trans
          (disjoint_iff_inf_le.mp (hw t j hj))).trans bot_le
  exact ⟨fun q => h (fun j => (u j).re q),fun q => h (fun j => (u j).im q)⟩

theorem mixSite_proper {T : Type} (w : T → B) (u : T → ComplexBits B)
    (hw : ∀ i j,i ≠ j → Disjoint (w i) (w j))
    (hc : ∀ t,(u t).CutOn (w t)) :
    (mixSite w u).CutOn (⨆ t,w t) := by
  exact ⟨properCutOn_iSup w (fun t =>
      properCutOn_of_same_mask (hc t).1 (mixSite_on w u hw t).1),
    properCutOn_iSup w (fun t =>
      properCutOn_of_same_mask (hc t).2 (mixSite_on w u hw t).2)⟩

end JSP000930.Negative
