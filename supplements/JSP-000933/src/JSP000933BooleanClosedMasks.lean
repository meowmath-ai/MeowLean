import JSP000933MaximumRealName

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def hitsWord (D : (ℕ → B) → B) (w : Word) : B :=
  ⨆ y : ℕ → B, D y ⊓ cylinderValue y w

noncomputable def closureValue (D : (ℕ → B) → B) (x : ℕ → B) : B :=
  ⨅ w : Word, (cylinderValue x w)ᶜ ⊔ hitsWord D w

theorem closure_has_openCode_r139 (D : (ℕ → B) → B) (x : ℕ → B) :
    (closureValue D x)ᶜ = openValue (fun w => (hitsWord D w)ᶜ) x := by
  unfold closureValue openValue
  rw [compl_iInf]
  apply congrArg (fun f : Word → B => iSup f)
  funext w
  simp only [compl_sup,compl_compl,inf_comm]

theorem le_ownClosure_r139 (D : (ℕ → B) → B) (x : ℕ → B) :
    D x ≤ closureValue D x := by
  apply le_iInf
  intro w
  apply (le_materialImp_iff_r126 _ _ _).mpr
  exact le_iSup (fun y : ℕ → B => D y ⊓ cylinderValue y w) x

theorem closure_given_word_r139 (D : (ℕ → B) → B) (x : ℕ → B)
    (w : Word) {p : B} (hx : p ≤ closureValue D x) (hw : p ≤ cylinderValue x w) :
    p ≤ hitsWord D w := by
  have hImp := hx.trans (iInf_le (fun w => (cylinderValue x w)ᶜ ⊔ hitsWord D w) w)
  exact (le_inf le_rfl hw).trans ((le_materialImp_iff_r126 _ _ _).mp hImp)

theorem closure_preserves_independent_r139 (D : (ℕ → B) → B) (K : Word × Word → B)
    (under : B)
    (h : ∀ x y, Disjoint (under ⊓ (D x ⊓ D y)) (colorValue K x y)) :
    ∀ x y, Disjoint (under ⊓ (closureValue D x ⊓ closureValue D y)) (colorValue K x y) := by
  intro x y
  apply disjoint_iff_inf_le.mpr
  apply le_of_eq
  by_contra hN
  let p := (under ⊓ (closureValue D x ⊓ closureValue D y)) ⊓ colorValue K x y
  obtain ⟨w,q,hq,hqp,hw⟩ := exists_nonzero_below_choice_r135 p hN
    (fun w => K w ⊓ (cylinderValue x w.1 ⊓ cylinderValue y w.2)) inf_le_right
  have hcx : q ≤ closureValue D x :=
    hqp.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))
  have hcy : q ≤ closureValue D y :=
    hqp.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))
  have hW₁ : q ≤ cylinderValue x w.1 := hw.trans (inf_le_right.trans inf_le_left)
  have hW₂ : q ≤ cylinderValue y w.2 := hw.trans (inf_le_right.trans inf_le_right)
  obtain ⟨z,r,hr,hrq,hrz⟩ := exists_nonzero_below_choice_r135 q hq
    (fun z => D z ⊓ cylinderValue z w.1) (closure_given_word_r139 D x w.1 hcx hW₁)
  obtain ⟨t,s,hs,hsr,hst⟩ := exists_nonzero_below_choice_r135 r hr
    (fun t => D t ⊓ cylinderValue t w.2) (hrq.trans (closure_given_word_r139 D y w.2 hcy hW₂))
  have hK : s ≤ K w := hsr.trans (hrq.trans (hw.trans inf_le_left))
  have hEdge : s ≤ colorValue K z t := edgeBox_suffices_r136 K z t w hK
    (hsr.trans (hrz.trans inf_le_right)) (hst.trans inf_le_right)
  have hBase : s ≤ under := hsr.trans (hrq.trans (hqp.trans (inf_le_left.trans inf_le_left)))
  have hd : s ≤ under ⊓ (D z ⊓ D t) :=
    le_inf hBase (le_inf (hsr.trans (hrz.trans inf_le_left)) (hst.trans inf_le_left))
  exact hs (le_bot_iff.mp ((le_inf hd hEdge).trans (disjoint_iff_inf_le.mp (h z t))))

end CantorCodes
end JSP000933
