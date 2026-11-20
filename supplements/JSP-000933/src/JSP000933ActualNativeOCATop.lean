import JSP000933NativeCliqueWitness

namespace JSP000933
namespace CantorCodes

open FiniteSupport BooleanCompletion OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def closedCoverExistsValue (D : (ℕ → B) → B) (K : Word × Word → B) : B :=
  ⨆ c : CoverCode B, goodCoverValue id D K c

noncomputable def weightedCliqueExistsValue (D : (ℕ → B) → B) (K : Word × Word → B) : B :=
  ⨆ x : OmegaOneIndex → ℕ → B, ⨆ g : OmegaOneIndex → B, weightedCliqueValue D K x g

noncomputable def irreflexiveGraphValue (D : (ℕ → B) → B) (K : Word × Word → B) : B :=
  ⨅ x : ℕ → B, (D x)ᶜ ⊔ (colorValue K x x)ᶜ

noncomputable def symmetricGraphValue (D : (ℕ → B) → B) (K : Word × Word → B) : B :=
  ⨅ x : ℕ → B, ⨅ y : ℕ → B,
    ((D x ⊓ D y) ⊓ colorValue K x y)ᶜ ⊔ colorValue K y x

noncomputable def nativeOCAValue (B : Type) [CompleteBooleanAlgebra B] : B :=
  ⨅ D : {D : (ℕ → B) → B // RealTestExt D}, ⨅ K : Word × Word → B,
    (irreflexiveGraphValue D.1 K ⊓ symmetricGraphValue D.1 K)ᶜ ⊔
      (closedCoverExistsValue D.1 K ⊔ weightedCliqueExistsValue D.1 K)

theorem ocaIteration_validGraphs_r170 (P : OCAParameters) (hDia : DiamondAtOmegaOne P.guess)
    (D : (ℕ → ocaB P) → ocaB P) (hD : RealTestExt D) (K : Word × Word → ocaB P) :
    irreflexiveGraphValue D K ⊓ symmetricGraphValue D K ≤
      closedCoverExistsValue D K ⊔ weightedCliqueExistsValue D K := by
  by_contra hNo
  let g := irreflexiveGraphValue D K ⊓ symmetricGraphValue D K
  let bad := g ⊓ (closedCoverExistsValue D K ⊔ weightedCliqueExistsValue D K)ᶜ
  have hb : bad ≠ ⊥ := by
    intro he
    apply hNo
    have hd : Disjoint g (closedCoverExistsValue D K ⊔ weightedCliqueExistsValue D K)ᶜ :=
      disjoint_iff_inf_le.mpr he.le
    exact (le_compl_iff_disjoint_right.mpr hd).trans_eq (compl_compl _)
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 bad hb
  have hG : imageCondition p ≤ g := hp.trans inf_le_left
  have hF : imageCondition p ≤ (closedCoverExistsValue D K ⊔ weightedCliqueExistsValue D K)ᶜ :=
    hp.trans inf_le_right
  rw [compl_sup] at hF
  have hNoCover (c : CoverCode (ocaB P)) :
      imageCondition p ≤ (goodCoverValue id D K c)ᶜ :=
    (hF.trans inf_le_left).trans (compl_le_compl (le_iSup (fun v => goodCoverValue id D K v) c))
  have hIrr (x : ℕ → ocaB P) : imageCondition p ⊓ D x ≤ (colorValue K x x)ᶜ := by
    have h := hG.trans (inf_le_left.trans (iInf_le (fun x : ℕ → ocaB P => (D x)ᶜ ⊔ (colorValue K x x)ᶜ) x))
    exact (le_materialImp_iff_r126 _ _ _).mp h
  have hSym (x y : ℕ → ocaB P) :
      (imageCondition p ⊓ (D x ⊓ D y)) ⊓ colorValue K x y ≤ colorValue K y x := by
    have h0 : imageCondition p ≤ symmetricGraphValue D K := hG.trans inf_le_right
    have hh : imageCondition p ≤ ((D x ⊓ D y) ⊓ colorValue K x y)ᶜ ⊔ colorValue K y x :=
      h0.trans ((iInf_le _ x).trans (iInf_le _ y))
    rw [inf_assoc]
    exact (le_materialImp_iff_r126 _ _ _).mp hh
  obtain ⟨a,⟨A⟩⟩ := exists_matching_activation_r168 P hDia D hD K p hNoCover hIrr hSym
  obtain ⟨q,hqp,x,u,hQu⟩ := exists_finalWeightedClique_from_activation_r169 P D K p a A
  have hQ : imageCondition q ≤ weightedCliqueExistsValue D K :=
    le_iSup_of_le x (le_iSup_of_le u hQu)
  exact imageCondition_ne_bot_r50 q (le_bot_iff.mp
    ((le_inf hQ (hqp.trans (hF.trans inf_le_right))).trans_eq (inf_compl_eq_bot')))

theorem ocaIteration_nativeOCA_top_r170 (P : OCAParameters) (hDia : DiamondAtOmegaOne P.guess) :
    nativeOCAValue (ocaB P) = ⊤ := by
  apply top_unique
  apply le_iInf
  intro D
  apply le_iInf
  intro K
  apply (le_materialImp_iff_r126 _ _ _).mpr
  rw [top_inf_eq]
  exact ocaIteration_validGraphs_r170 P hDia D.1 D.2 K

end CantorCodes
end JSP000933
