import JSP000933MarkedGraphReflection

namespace JSP000933
namespace ForcingTransport

open CantorCodes BooleanCompletion

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

noncomputable def twoMarkedFailure (k : Word×Word→B) (c : CoverCode B)
    (x y : ℕ→B) (a b : B) : B :=
  (a⊓⨅ n,openValue (c n) x) ⊔
  ⨆ n, ((a⊓b)⊓(ClosedMember c n x⊓ClosedMember c n y))⊓colorValue k x y

theorem twoMarkedFailure_mono (k : Word×Word→B) (c : CoverCode B)
    (x y : ℕ→B) {a b a' b' : B} (ha : a≤a') (hb : b≤b') :
    twoMarkedFailure k c x y a b≤twoMarkedFailure k c x y a' b' := by
  unfold twoMarkedFailure
  apply sup_le_sup (inf_le_inf ha le_rfl)
  apply iSup_mono
  intro n
  exact inf_le_inf (inf_le_inf (inf_le_inf ha hb) le_rfl) le_rfl

theorem mask_openCode_congr {m : B} {a b : Word→B} (h : ∀ w,m⊓a w=m⊓b w) (x : ℕ→B) :
    m⊓openValue a x=m⊓openValue b x :=
  mask_iSup_congr_r126 (fun w => mask_inf_congr_r126 (h w) rfl)

theorem mask_twoMarkedFailure_congr {m : B} {k k' : Word×Word→B}
    {c c' : CoverCode B} {x x' y y' : ℕ→B} {a a' b b' : B}
    (hk : ∀ w,m⊓k w=m⊓k' w) (hc : ∀ n w,m⊓c n w=m⊓c' n w)
    (hx : m≤realEqValue x x') (hy : m≤realEqValue y y')
    (ha : m⊓a=m⊓a') (hb : m⊓b=m⊓b') :
    m⊓twoMarkedFailure k c x y a b=m⊓twoMarkedFailure k' c' x' y' a' b' := by
  have h₁ (n : ℕ) : m⊓openValue (c n) x=m⊓openValue (c' n) x' :=
    (mask_openValue_congr_r127 (c n) hx).trans (mask_openCode_congr (hc n) x')
  have h₂ (n : ℕ) : m⊓openValue (c n) y=m⊓openValue (c' n) y' :=
    (mask_openValue_congr_r127 (c n) hy).trans (mask_openCode_congr (hc n) y')
  have hcol : m⊓colorValue k x y=m⊓colorValue k' x' y' :=
    (mask_colorValue_congr_r127 k hx hy).trans (mask_colorCode_congr hk x' y')
  apply mask_sup_congr
  · exact mask_inf_congr_r126 ha (mask_iInf_congr_r126 h₁)
  · apply mask_iSup_congr_r126
    intro n
    exact mask_inf_congr_r126
      (mask_inf_congr_r126 (mask_inf_congr_r126 ha hb)
        (mask_inf_congr_r126 (mask_compl_congr_r126 (h₁ n)) (mask_compl_congr_r126 (h₂ n)))) hcol

theorem map_twoMarkedFailure (F : CompleteValueMap B C)
    (k : Word×Word→B) (c : CoverCode B) (x y : ℕ→B) (a b : B) :
    F.toFun (twoMarkedFailure k c x y a b) =
      twoMarkedFailure (F.toFun ∘ k) (fun n => F.toFun ∘ c n)
        (F.toFun ∘ x) (F.toFun ∘ y) (F.toFun a) (F.toFun b) := by
  simp only [twoMarkedFailure,ClosedMember,F.map_sup_r93,F.map_inf,F.map_compl,F.map_iSup,F.map_iInf,
    map_openValue_r105,map_colorValue_r105,Function.comp_apply]
  rfl

theorem twoPointCoverFailure_eq_twoMarked (D : (ℕ→B)→B) (k : Word×Word→B)
    (c : CoverCode B) (x y : ℕ→B) :
    twoPointCoverFailure D k c x y = twoMarkedFailure k c x y (D x) (D y) := rfl

theorem join_failure_of_local_rows {I : Type} (F : CompleteValueMap B C)
    (q : B) (x : I→ℕ→B) (d : I→B) (k : Word×Word→B)
    (D : (ℕ→C)→C) (K : Word×Word→C) (c : CoverCode B)
    (hLocal : ∀ r : B,r≤q → r≠⊥ → ∃ s : B, s≤r ∧ s≠⊥ ∧ ∃ i j : I,
      ∃ X Y : ℕ→C, ∃ C' : CoverCode C,
      (∀ w,F.toFun s⊓F.toFun (k w)=F.toFun s⊓K w) ∧
      (∀ n w,F.toFun s⊓F.toFun (c n w)=F.toFun s⊓C' n w) ∧
      F.toFun s≤realEqValue (F.toFun ∘ x i) X ∧
      F.toFun s≤realEqValue (F.toFun ∘ x j) Y ∧
      F.toFun s⊓F.toFun (d i)=F.toFun s⊓D X ∧
      F.toFun s⊓F.toFun (d j)=F.toFun s⊓D Y ∧
      F.toFun s≤twoPointCoverFailure D K C' X Y) :
    q≤(goodCoverValue id (saturatedDomain x d) k c)ᶜ := by
  let goal := (goodCoverValue id (saturatedDomain x d) k c)ᶜ
  by_contra hn
  have hR : q⊓goalᶜ≠⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨s,hs,hs0,i,j,X,Y,C',hk,hc,hx,hy,ha,hb,hFail⟩ := hLocal _ inf_le_left hR
  have hSmall : s≤twoMarkedFailure k c (x i) (x j) (d i) (d j) := by
    apply F.reflect_le_r93
    rw [map_twoMarkedFailure]
    have hh := mask_twoMarkedFailure_congr hk hc hx hy ha hb
    rw [←twoPointCoverFailure_eq_twoMarked] at hh
    exact (le_inf le_rfl hFail).trans (hh.ge.trans inf_le_right)
  have hSmall' : twoMarkedFailure k c (x i) (x j) (d i) (d j) ≤ goal := by
    unfold goal
    rw [twoPointCoverFailure_rows]
    apply le_iSup_of_le (x i)
    apply le_iSup_of_le (x j)
    rw [twoPointCoverFailure_eq_twoMarked]
    exact twoMarkedFailure_mono _ _ _ _ (saturatedDomain_ge_row x d i) (saturatedDomain_ge_row x d j)
  exact hs0 (disjoint_compl_right.out _ (hSmall.trans hSmall') (hs.trans inf_le_right))

end ForcingTransport
end JSP000933
