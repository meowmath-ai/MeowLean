import JSP000930ActualCohenSuccessorPredensity
import JSP000930NegativeLocalTraceInclusion

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.BooleanAnalysis JSP000930.Negative JSP000930.MixedPalettes
open JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype I]

variable (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
variable (M : I → Label B) (A : J → Prop) (z : J) (hz : ¬ A z)

noncomputable def actualCohenSuccessorMap := includeAnalyticProductCondition
  (fun j (hj : A j) => Or.inl (b := j=z) hj) (stageCohenMap B) site H
  (cohenSiteLift site) (extendActualPalette H M z) (fun j hj => rfl)
  (fun i j hj n => (extendActualPalette_old H M z i (fun h => hz (h ▸ hj)) n).symm)

noncomputable abbrev EarlierAnalyticProduct := rowProductQ (fun i => supportedSymbolicQ site (H i) A)
noncomputable abbrev LaterAnalyticProduct := rowProductQ (fun i =>
  supportedSymbolicQ (cohenSiteLift site) (extendActualPalette H M z i) (fun j => A j ∨ j=z))

noncomputable def actualCohenSuccessorInsideMap (b : B)
    (p : MaskedCondition (EarlierAnalyticProduct site H A) b) :
    MaskedCondition (LaterAnalyticProduct site H M A z) ((stageCohenMap B).toFun b) :=
  ⟨actualCohenSuccessorMap site H M A z hz p.val,(stageCohenMap B).monotone p.2⟩

set_option maxHeartbeats 650000 in
theorem actualCohenSuccessorInsideMap_predensity (b : B)
    (hSep : ∀ i j,i≠j → b ≤ (labelAgreement (M i) (M j))ᶜ)
    (hSite : ∀ j,(site j).CutOn (⊤ : B))
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ j,A j ∨ j=z → ∀ k,A k ∨ k=z → j ≠ k →
      (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ) :
    PreservesPredensity (actualCohenSuccessorInsideMap site H M A z hz b) := by
  classical
  intro E hE q
  let Q := EarlierAnalyticProduct site H A
  let F := stageCohenMap B
  let Ewide : Set (TotalCondition Q) := {d | Disjoint d.mask b ∨
    ∃ hd : d.mask ≤ b,(⟨d,hd⟩ : MaskedCondition Q b) ∈ E}
  have hWide : DenseConditionSet Ewide := by
    intro d
    by_cases hd : d.mask ⊓ b = ⊥
    · exact ⟨d,le_rfl,Or.inl (disjoint_iff_inf_le.mpr hd.le)⟩
    · let d' : MaskedCondition Q b := ⟨intersectMask d b hd,inf_le_right⟩
      obtain ⟨a,ha,haE⟩ := hE d'
      have ha' : a.val ≤ d'.val := ha
      exact ⟨a.val,ha'.trans (intersectMask_le_r426 d b hd),
         Or.inr ⟨a.property,haE⟩⟩
  obtain ⟨d,hd,w,hwQ,hwD⟩ := actualCohenSuccessor_meets_dense_on_mark site H M A z hz
    b hSep hSite hH hApart Ewide hWide q.val q.property
  rcases hd with hd | ⟨hd,hdE⟩
  · have hwd : w.mask ≤ F.toFun d.mask := hwD.1
    have hwb : w.mask ≤ F.toFun b := hwQ.1.trans q.property
    have hInf : w.mask ≤ F.toFun (d.mask ⊓ b) := by rw [F.map_inf]; exact le_inf hwd hwb
    have he : d.mask ⊓ b = ⊥ := le_bot_iff.mp (disjoint_iff_inf_le.mp hd)
    rw [he,F.map_bot] at hInf
    exact (w.nonzero (le_bot_iff.mp hInf)).elim
  · exact ⟨⟨d,hd⟩,hdE,⟨w,hwQ.1.trans q.property⟩,hwQ,hwD⟩

theorem actualCohenSuccessorInsideMap_reflects_compatible (b : B)
    (hSite : ∀ j,(site j).CutOn (⊤ : B))
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ j,A j ∨ j=z → ∀ k,A k ∨ k=z → j ≠ k →
      (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    {p q : MaskedCondition (EarlierAnalyticProduct site H A) b}
    (h : Compatible (actualCohenSuccessorInsideMap site H M A z hz b p)
      (actualCohenSuccessorInsideMap site H M A z hz b q)) : Compatible p q := by
  obtain ⟨w,hwp,hwq⟩ := h
  have hCompat : Compatible (actualCohenSuccessorMap site H M A z hz p.val)
      (actualCohenSuccessorMap site H M A z hz q.val) := ⟨w.val,hwp,hwq⟩
  obtain ⟨a,haP,haQ⟩ := (includeAnalyticProductCondition_compatible_iff
    (fun j hj => Or.inl hj) (stageCohenMap B) site H (cohenSiteLift site) (extendActualPalette H M z)
    (fun j hj => rfl)
    (fun i j hj n => (extendActualPalette_old H M z i (fun h => hz (h ▸ hj)) n).symm)
    (fun j _ => cohenSiteLift_cutOn site hSite j)
    (fun i j hj n => extendActualPalette_cutOn H M A z hz hH i j (Or.inl hj) n)
    (fun j hj k hk h => cohenSiteLift_apart site (hApart j (Or.inl hj) k (Or.inl hk) h)) p.val q.val).mp hCompat
  exact ⟨⟨a,haP.1.trans p.property⟩,haP,haQ⟩

noncomputable def actualCohenSuccessor_markedComplete (b : B)
    (hSep : ∀ i j,i≠j → b ≤ (labelAgreement (M i) (M j))ᶜ)
    (hSite : ∀ j,(site j).CutOn (⊤ : B))
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ j,A j ∨ j=z → ∀ k,A k ∨ k=z → j ≠ k →
      (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ) :
    CompleteValueMap (RO (MaskedCondition (EarlierAnalyticProduct site H A) b))
      (RO (MaskedCondition (LaterAnalyticProduct site H M A z) ((stageCohenMap B).toFun b))) :=
  completeMapFromPredensity (actualCohenSuccessorInsideMap site H M A z hz b)
    (actualCohenSuccessorInsideMap_predensity site H M A z hz b hSep hSite hH hApart)
    (actualCohenSuccessorInsideMap_reflects_compatible site H M A z hz b hSite hH hApart)

end JSP000930.Negative.Cohen
