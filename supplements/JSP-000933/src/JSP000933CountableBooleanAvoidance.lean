import JSP000933BooleanClosedMasks

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem exists_real_avoids_countableIndependent_r140
    (D : (ℕ → B) → B) (hD : RealTestExt D) (K : Word × Word → B) (p : B)
    (hNo : ∀ c : CoverCode B, p ≤ (goodCoverValue id D K c)ᶜ)
    (S : ℕ → (ℕ → B) → B)
    (hS : ∀ n x y, Disjoint (p ⊓ (S n x ⊓ S n y)) (colorValue K x y)) :
    ∃ x : ℕ → B, p ≤ D x ∧ ∀ n, p ≤ (S n x)ᶜ := by
  let c : CoverCode B := fun n w => (hitsWord (S n) w)ᶜ
  have hClosure (n : ℕ) (x : ℕ → B) :
      ClosedMember c n x = closureValue (S n) x := by
    change (openValue (fun w => (hitsWord (S n) w)ᶜ) x)ᶜ = _
    rw [← closure_has_openCode_r139,compl_compl]
  have hInd : p ≤ independentValue id D K c := by
    apply le_iInf
    rintro ⟨n,x,y⟩
    change p ≤ ((D x ⊓ D y) ⊓ (ClosedMember c n x ⊓ ClosedMember c n y))ᶜ ⊔
      (colorValue K x y)ᶜ
    rw [hClosure,hClosure]
    apply (le_materialImp_iff_r126 _ _ _).mpr
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have hh : p ⊓ ((D x ⊓ D y) ⊓ (closureValue (S n) x ⊓ closureValue (S n) y)) ≤
        p ⊓ (closureValue (S n) x ⊓ closureValue (S n) y) :=
      le_inf inf_le_left (inf_le_right.trans inf_le_right)
    exact (inf_le_inf_right _ hh).trans
      (disjoint_iff_inf_le.mp (closure_preserves_independent_r139 (S n) K p (hS n) x y))
  have hFailCover : p ≤ (coverValue id D c)ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have hh : p ⊓ coverValue id D c ≤ p ⊓ goodCoverValue id D K c :=
      le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hInd))
    exact hh.trans (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp (hNo c)))
  let test (x : ℕ → B) := D x ⊓ (⨅ n, openValue (c n) x)
  have hSup : p ≤ ⨆ x : ℕ → B, test x := by
    simpa only [coverValue,ClosedMember,compl_iInf,compl_sup,compl_compl,compl_iSup,id_eq,test]
      using hFailCover
  have hExt : RealTestExt test :=
    hD.inf_r138 (RealTestExt.iInf_r138 (fun n => fun _ _ _ h => mask_openValue_congr_r127 (c n) h))
  obtain ⟨x,hx⟩ := exists_realName_maximum_r138 test hExt p hSup
  refine ⟨x,hx.trans inf_le_left,fun n => ?_⟩
  have hOpen : p ≤ (closureValue (S n) x)ᶜ :=
    (hx.trans (inf_le_right.trans (iInf_le (fun n => openValue (c n) x) n))).trans_eq
      (closure_has_openCode_r139 (S n) x).symm
  exact hOpen.trans (compl_le_compl (le_ownClosure_r139 (S n) x))

theorem exists_real_avoids_independentFamily_r140 {I : Type} [Countable I]
    (D : (ℕ → B) → B) (hD : RealTestExt D) (K : Word × Word → B) (p : B)
    (hNo : ∀ c : CoverCode B, p ≤ (goodCoverValue id D K c)ᶜ)
    (S : I → (ℕ → B) → B)
    (hS : ∀ i x y, Disjoint (p ⊓ (S i x ⊓ S i y)) (colorValue K x y)) :
    ∃ x : ℕ → B, p ≤ D x ∧ ∀ i, p ≤ (S i x)ᶜ := by
  obtain ⟨E,hE⟩ := exists_optionEnumeration_r60 (Set.univ : Set I) Set.countable_univ
  let f (n : ℕ) : (ℕ → B) → B :=
    match E n with
    | none => fun _ => ⊥
    | some i => S i
  have hF (n : ℕ) (x y : ℕ → B) : Disjoint (p ⊓ (f n x ⊓ f n y)) (colorValue K x y) := by
    cases h : E n with
    | none => simp [f,h]
    | some i => simpa only [f,h] using hS i x y
  obtain ⟨x,hx,hAx⟩ := exists_real_avoids_countableIndependent_r140 D hD K p hNo f hF
  refine ⟨x,hx,fun i => ?_⟩
  obtain ⟨n,hn⟩ := (hE i).mp (Set.mem_univ _)
  simpa only [f,hn] using hAx n

end CantorCodes
end JSP000933
