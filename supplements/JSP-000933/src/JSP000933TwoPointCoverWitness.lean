import JSP000933ActualNativeOCATop
import JSP000933MaximumRealName

namespace JSP000933
namespace ForcingTransport

open CantorCodes BooleanCompletion

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def twoPointCoverFailure (D : (ℕ→B)→B) (K : Word×Word→B)
    (c : CoverCode B) (x y : ℕ→B) : B :=
  missedPoint id D c x ⊔ ⨆ n : ℕ, badEdge id D K c (n,x,y)

theorem mask_sup_congr {p x y u v : B} (h₁ : p⊓x=p⊓u) (h₂ : p⊓y=p⊓v) :
    p⊓(x⊔y)=p⊓(u⊔v) := by
  have h := mask_compl_congr_r126 (mask_inf_congr_r126
    (mask_compl_congr_r126 h₁) (mask_compl_congr_r126 h₂))
  simpa only [compl_inf,compl_compl] using h

theorem twoPointCoverFailure_ext
    (D : (ℕ→B)→B) (hD : RealTestExt D) (K : Word×Word→B)
    (c : CoverCode B) {p : B} {x x' y y' : ℕ→B}
    (hx : p≤realEqValue x x') (hy : p≤realEqValue y y') :
    p⊓twoPointCoverFailure D K c x y=p⊓twoPointCoverFailure D K c x' y' := by
  have hD₁ := hD p x x' hx
  have hD₂ := hD p y y' hy
  have hOpen₁ (n : ℕ) := mask_openValue_congr_r127 (c n) hx
  have hOpen₂ (n : ℕ) := mask_openValue_congr_r127 (c n) hy
  apply mask_sup_congr
  · exact mask_inf_congr_r126 hD₁ (mask_iInf_congr_r126 hOpen₁)
  · apply mask_iSup_congr_r126
    intro n
    exact mask_inf_congr_r126
      (mask_inf_congr_r126 (mask_inf_congr_r126 hD₁ hD₂)
        (mask_inf_congr_r126 (mask_compl_congr_r126 (hOpen₁ n))
          (mask_compl_congr_r126 (hOpen₂ n))))
      (mask_colorValue_congr_r127 K hx hy)

theorem twoPointCoverFailure_rows (D : (ℕ→B)→B)
    (K : Word×Word→B) (c : CoverCode B) :
    (goodCoverValue id D K c)ᶜ = ⨆ x : ℕ→B,⨆ y : ℕ→B,twoPointCoverFailure D K c x y := by
  rw [goodCover_compl_r112]
  apply le_antisymm
  · apply sup_le
    · apply iSup_le
      intro x
      exact le_iSup_of_le x (le_iSup_of_le x le_sup_left)
    · apply iSup_le
      rintro ⟨n,x,y⟩
      exact le_iSup_of_le x (le_iSup_of_le y ((le_iSup (fun k : ℕ => badEdge id D K c (k,x,y)) n).trans le_sup_right))
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    unfold twoPointCoverFailure
    apply sup_le
    · exact (le_iSup _ x).trans le_sup_left
    · apply iSup_le
      intro n
      exact (le_iSup _ (n,x,y)).trans le_sup_right

theorem exists_twoPointCoverFailure_maximum
    (D : (ℕ→B)→B) (hD : RealTestExt D) (K : Word×Word→B)
    (c : CoverCode B) (p : B) (hp : p≤(goodCoverValue id D K c)ᶜ) :
    ∃ x y, p≤twoPointCoverFailure D K c x y := by
  rw [twoPointCoverFailure_rows] at hp
  let test (x : ℕ→B) := ⨆ y : ℕ→B,twoPointCoverFailure D K c x y
  have hExt : RealTestExt test := by
    intro m x x' hx
    apply mask_iSup_congr_r126
    intro y
    exact twoPointCoverFailure_ext D hD K c hx
      (by rw [realEqValue_refl_r127]; exact le_top)
  obtain ⟨x,hx⟩ := exists_realName_maximum_r138 test hExt p hp
  have hExt' : RealTestExt (twoPointCoverFailure D K c x) := by
    intro m y y' hy
    exact twoPointCoverFailure_ext D hD K c (by rw [realEqValue_refl_r127]; exact le_top) hy
  obtain ⟨y,hy⟩ := exists_realName_maximum_r138 _ hExt' p hx
  exact ⟨x,y,hy⟩

end ForcingTransport
end JSP000933
