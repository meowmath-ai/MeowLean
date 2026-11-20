import JSP000933ActualClosedCoverSamples

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def decodedClosedCover (x : ℕ → B) (n : ℕ) (u : Word) : B :=
  x (Encodable.encode (n,u))

noncomputable def encodedClosedCover (C : CoverCode B) (i : ℕ) : B :=
  match Encodable.decode (α := ℕ × Word) i with
  | none => ⊥
  | some nu => C nu.1 nu.2

theorem decoded_encodedClosedCover_r262 (C : CoverCode B) : decodedClosedCover (encodedClosedCover C) = C := by
  funext n u
  simp only [decodedClosedCover,encodedClosedCover,Encodable.encodek]

theorem mask_openValue_codeCongr_r262 {p : B} {c c' : Word → B} (x : ℕ → B)
    (he : ∀ u, p⊓c u=p⊓c' u) :
    p⊓openValue c x=p⊓openValue c' x :=
  mask_iSup_congr_r126 (fun u => mask_inf_congr_r126 (he u) rfl)

theorem goodCover_mask_codeCongr_r262 (D : (ℕ → B) → B) (K : Word × Word → B)
    {p : B} {C C' : CoverCode B} (he : ∀ n u, p⊓C n u=p⊓C' n u) :
    p⊓goodCoverValue id D K C=p⊓goodCoverValue id D K C' := by
  have hCl (n : ℕ) (x : ℕ → B) : p⊓ClosedMember C n x=p⊓ClosedMember C' n x :=
    mask_compl_congr_r126 (mask_openValue_codeCongr_r262 x (he n))
  unfold goodCoverValue coverValue independentValue
  apply mask_inf_congr_r126
  · apply mask_iInf_congr_r126
    intro x
    exact mask_sup_congr_r211 rfl (mask_iSup_congr_r126 (fun n => hCl n x))
  · apply mask_iInf_congr_r126
    rintro ⟨n,x,y⟩
    exact mask_imp_ante_congr_r211 (mask_inf_congr_r126 rfl
      (mask_inf_congr_r126 (hCl n x) (hCl n y)))

theorem goodCover_decoded_ext_r262 (D : (ℕ → B) → B) (K : Word × Word → B) :
    RealTestExt (fun x => goodCoverValue id D K (decodedClosedCover x)) := by
  intro p x y h
  exact goodCover_mask_codeCongr_r262 D K
    (fun n u => (le_realEqValue_iff_r126 _ _ _).mp h (Encodable.encode (n,u)))

theorem closedCoverExists_has_actualCode_r262 (D : (ℕ → B) → B) (K : Word × Word → B)
    (p : B) (h : p≤closedCoverExistsValue D K) :
    ∃ C : CoverCode B, p≤goodCoverValue id D K C := by
  have he : p≤⨆ x : ℕ → B, goodCoverValue id D K (decodedClosedCover x) := by
    unfold closedCoverExistsValue at h
    apply h.trans
    apply iSup_le
    intro C
    apply le_iSup_of_le (encodedClosedCover C)
    rw [decoded_encodedClosedCover_r262]
  obtain ⟨x,hx⟩ := exists_realName_maximum_r138 _ (goodCover_decoded_ext_r262 D K) p he
  exact ⟨decodedClosedCover x,hx⟩

theorem actualOCA_allBudget_crossing_covers_r262 (G : bSet B) (e : ℕ ↪ Word)
    (k : ℕ → ℕ) (hk : ∀ j, k j≠0)
    (extra : (ℕ → B) → B) (hE : RealTestExt extra) {p : B} (F : CoherentSelectedIso B p)
    (hOCA : p≤namedCantorOCAValue B) (hG : p≤actualPreserveReflectValue G)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x)) :
    ∃ C : ℕ → CoverCode B, ∀ j,
      p≤goodCoverValue id (concreteCrossDomain e G extra) (concreteCrossColorTable e (k j)) (C j) := by
  classical
  have he (j : ℕ) := closedCoverExists_has_actualCode_r262 _ _ p
    (actualOCA_concrete_crossing_cover_r260 G e (k j) (hk j) extra hE F hOCA hG hF)
  choose C hC using he
  exact ⟨C,hC⟩

end SetLanguage
end JSP000933
