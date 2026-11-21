import JSP000930ActualMixedFreshPalettes

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.BooleanAnalysis JSP000930.Negative JSP000930.Positive.Cohen
open JSP000930.MixedPalettes JSP000933.MarkedForcing JSP000933.ForcingTransport
open JSP000933.BooleanCompletion

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype I]

noncomputable def cohenSiteLift (site : J → ComplexBits B) : J → ComplexBits (StageCohenBA B) :=
  fun j => (site j).map (stageCohenMap B)

theorem cohenSiteLift_cutOn (site : J → ComplexBits B) (hSite : ∀ j,(site j).CutOn (⊤ : B)) :
    ∀ j,(cohenSiteLift site j).CutOn (⊤ : StageCohenBA B) := by
  intro j
  have h := ComplexBits.map_cutOn (stageCohenMap B) (hSite j)
  rw [(stageCohenMap B).map_top] at h
  exact h

theorem cohenSiteLift_apart (site : J → ComplexBits B)
    {j k : J} (h : (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ) :
    (⊤ : StageCohenBA B) ≤ ((cohenSiteLift site j).name =ᴮ (cohenSiteLift site k).name)ᶜ := by
  have hh := (stageCohenMap B).monotone h
  rw [(stageCohenMap B).map_top,(stageCohenMap B).map_compl,ComplexBits.map_nameEq] at hh
  exact hh

theorem extendActualPalette_cutOn (H : I → J → ℕ → ComplexBits B)
    (M : I → Label B) (A : J → Prop) (z : J) (hz : ¬ A z)
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B)) :
    ∀ i j,A j ∨ j=z → ∀ n,(extendActualPalette H M z i j n).CutOn (⊤ : StageCohenBA B) := by
  intro i j hj n
  rcases hj with hj|rfl
  · rw [extendActualPalette_old H M z i (fun h => hz (h ▸ hj))]
    have h := ComplexBits.map_cutOn (stageCohenMap B) (hH i j hj n)
    rw [(stageCohenMap B).map_top] at h
    exact h
  · rw [extendActualPalette_fresh]
    exact actualMixedPalette_cutOn (M i) n

theorem actualCohenSuccessor_meets_dense_on_mark
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (M : I → Label B) (A : J → Prop) (z : J) (hz : ¬ A z) (b₀ : B)
    (hSep : ∀ i j,i≠j → b₀ ≤ (labelAgreement (M i) (M j))ᶜ)
    (hSite : ∀ j,(site j).CutOn (⊤ : B))
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ j,A j ∨ j=z → ∀ k,A k ∨ k=z → j ≠ k →
      (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    (E : Set (AnalyticRowTotal site H A)) (hE : DenseConditionSet E)
    (q : AnalyticRowTotal (cohenSiteLift site) (extendActualPalette H M z) (fun j => A j ∨ j=z))
    (hq : q.mask ≤ (stageCohenMap B).toFun b₀) :
    ∃ d : AnalyticRowTotal site H A,d ∈ E ∧
      Compatible q (includeAnalyticProductCondition (fun j hj => Or.inl hj) (stageCohenMap B)
        site H (cohenSiteLift site) (extendActualPalette H M z) (fun j hj => rfl)
        (fun i j hj n => (extendActualPalette_old H M z i (fun h => hz (h ▸ hj)) n).symm) d) := by
  classical
  let s := cohenSiteLift site
  let G := extendActualPalette H M z
  obtain ⟨q',hqq',hqMask,hL⟩ := analyticProduct_refine_to_real_labels s G q
  choose p hp using hL
  obtain ⟨t,ht⟩ := imageCondition_dense_r50 q'.mask q'.nonzero
  have htB : t.mask ≤ b₀ :=
    (baseEmbed_reflects_mask_r427 _ _).mp (ht.trans (hqMask.le.trans hq))
  obtain ⟨u,hu,route,hRoute,interval,hValue⟩ :=
    choose_actual_fresh_allocation H M z b₀ hSep p t htB
  have huQ : imageCondition u ≤ q'.mask := (imageCondition_mono_r50 hu).trans ht
  have hOld (i : I) (j : J) (hj : A j) (n : ℕ) :=
    (extendActualPalette_old H M z i (fun h => hz (h ▸ hj)) n).symm
  obtain ⟨d,hd,w,hwq,hwd⟩ := actual_freshAllocation_meets_old_dense_product site H s G A z hz
    (fun j hj => rfl) hOld hSite hH hApart (cohenSiteLift_cutOn site hSite)
    (extendActualPalette_cutOn H M A z hz hH) (fun j hj k hk h =>
      cohenSiteLift_apart site (hApart j hj k hk h)) E hE q' p hp u huQ route hRoute interval hValue
  exact ⟨d,hd,w,hwq.trans hqq',hwd⟩

end JSP000930.Negative.Cohen
