import JSP000933MaskNativeClique

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

def ExtendsWord (s u : Word) : Prop :=
  ∃ h : s.length ≤ u.length, ∀ i : Fin s.length,
    s[i.val] = u[i.val]'(i.isLt.trans_le h)

def WordsDisagree (u v : Word) : Prop :=
  ∃ i : ℕ, ∃ hu : i < u.length, ∃ hv : i < v.length, u[i]'hu ≠ v[i]'hv

theorem cylinderWord_mono_r173 (x : ℕ → B) {s u : Word} (h : ExtendsWord s u) :
    cylinderValue x u ≤ cylinderValue x s := by
  obtain ⟨hlen,hagree⟩ := h
  apply le_iInf
  intro i
  rw [hagree i]
  exact iInf_le _ (⟨i.val,i.isLt.trans_le hlen⟩ : Fin u.length)

theorem literals_eq_of_nonzero_r173 (x p : B) (a b : Bool)
    (hp : p ≠ ⊥) (ha : p ≤ literal x a) (hb : p ≤ literal x b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact False.elim (hp (le_bot_iff.mp ((le_inf hb ha).trans_eq (inf_compl_eq_bot' (x := x)))))
  · exact False.elim (hp (le_bot_iff.mp ((le_inf ha hb).trans_eq (inf_compl_eq_bot' (x := x)))))
  · rfl

theorem extendsWord_of_compatible_r173 (x : ℕ → B) {p : B} (hp : p ≠ ⊥)
    {s u : Word} (hlen : s.length ≤ u.length)
    (hs : p ≤ cylinderValue x s) (hu : p ≤ cylinderValue x u) :
    ExtendsWord s u := by
  refine ⟨hlen,fun i => ?_⟩
  exact literals_eq_of_nonzero_r173 (x i.val) p _ _ hp
    (hs.trans (iInf_le _ i)) (hu.trans (iInf_le _ (⟨i.val,i.isLt.trans_le hlen⟩ : Fin u.length)))

theorem differentBox_disjoint_r173 (x y : ℕ → B) {u v : Word} (h : WordsDisagree u v) :
    cylinderValue x u ⊓ cylinderValue y v ≤ (realEqValue x y)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  classical
  obtain ⟨i,hu,hv,hd⟩ := h
  let p := (cylinderValue x u ⊓ cylinderValue y v) ⊓ realEqValue x y
  have hX : p ≤ literal (x i) (u[i]'hu) := inf_le_left.trans
    (inf_le_left.trans (iInf_le _ (⟨i,hu⟩ : Fin u.length)))
  have hY : p ≤ literal (y i) (v[i]'hv) := inf_le_left.trans
    (inf_le_right.trans (iInf_le _ (⟨i,hv⟩ : Fin v.length)))
  have hxy := (le_realEqValue_iff_r126 p x y).mp inf_le_right i
  have hL : p ⊓ literal (x i) (v[i]'hv) = p ⊓ literal (y i) (v[i]'hv) := by
    cases hbit : v[i]'hv
    · simpa only [literal] using mask_compl_congr_r126 hxy
    · simpa only [literal] using hxy
  have hY' : p ≤ literal (x i) (v[i]'hv) :=
    ((le_inf le_rfl hY).trans_eq hL.symm).trans inf_le_right
  by_contra hn
  exact hd (literals_eq_of_nonzero_r173 _ p _ _ (fun he => hn he.le) hX hY')

noncomputable def offDiagonalTable (K : Word × Word → B) : Word × Word → B :=
  fun uv => ⨆ st : {st : Word × Word // ExtendsWord st.1 uv.1 ∧
    ExtendsWord st.2 uv.2 ∧ WordsDisagree uv.1 uv.2}, K st.1

theorem offDiagonalTable_color_r173 (K : Word × Word → B) (x y : ℕ → B) :
    colorValue (offDiagonalTable K) x y =
      colorValue K x y ⊓ (realEqValue x y)ᶜ := by
  classical
  apply le_antisymm
  · unfold colorValue
    apply iSup_le
    intro uv
    rw [offDiagonalTable, iSup_inf_eq]
    apply iSup_le
    intro st
    apply le_inf
    · exact le_iSup_of_le st.1 (le_inf inf_le_left
        (inf_le_right.trans (inf_le_inf
          (cylinderWord_mono_r173 x st.2.1) (cylinderWord_mono_r173 y st.2.2.1))))
    · exact inf_le_right.trans (differentBox_disjoint_r173 x y st.2.2.2)
  · by_contra hn
    let V := colorValue K x y ⊓ (realEqValue x y)ᶜ
    let U := colorValue (offDiagonalTable K) x y
    let p := V ⊓ Uᶜ
    have hp : p ≠ ⊥ := by
      intro hz
      have h : Disjoint V Uᶜ := disjoint_iff_inf_le.mpr hz.le
      exact hn (by simpa only [compl_compl] using (le_compl_iff_disjoint_right.mpr h))
    have hpV : p ≤ V := inf_le_left
    obtain ⟨st,q,hq,hqp,hst⟩ := exists_nonzero_below_choice_r135 p hp
      (fun st : Word × Word => K st ⊓ (cylinderValue x st.1 ⊓ cylinderValue y st.2))
      (hpV.trans inf_le_left)
    have hqDiff : q ≤ ⨆ i, (bitEq (x i) (y i))ᶜ := by
      have h := hqp.trans (hpV.trans inf_le_right)
      simpa only [realEqValue,compl_iInf] using h
    obtain ⟨i,r,hr,hrq,hdiff⟩ :=
      exists_nonzero_below_choice_r135 q hq (fun i => (bitEq (x i) (y i))ᶜ) hqDiff
    obtain ⟨u,hu,s,hs,hsr,hU⟩ := exists_decided_initialWord_r136 x (max st.1.length (i+1)) r hr
    obtain ⟨v,hv,t,ht,hts,hV⟩ := exists_decided_initialWord_r136 y (max st.2.length (i+1)) s hs
    have htq : t ≤ q := hts.trans (hsr.trans hrq)
    have hiU : i < u.length := hu ▸ (Nat.lt_succ_self i).trans_le (le_max_right _ _)
    have hiV : i < v.length := hv ▸ (Nat.lt_succ_self i).trans_le (le_max_right _ _)
    have hwords : WordsDisagree u v := by
      refine ⟨i,hiU,hiV,fun he => ?_⟩
      have hx : t ≤ literal (x i) (u[i]'hiU) :=
        hts.trans (hU.trans (iInf_le _ (⟨i,hiU⟩ : Fin u.length)))
      have hy : t ≤ literal (y i) (u[i]'hiU) := by
        rw [he]
        exact hV.trans (iInf_le _ (⟨i,hiV⟩ : Fin v.length))
      have heq : t ≤ bitEq (x i) (y i) := by
        apply (le_bitEq_iff_r126 _ _ _).mpr
        cases hb : u[i]'hiU
        · rw [hb] at hx hy
          have h1 : t ⊓ x i = ⊥ := le_bot_iff.mp
            ((inf_le_inf_right (x i) hx).trans_eq (by rw [literal,inf_comm,inf_compl_eq_bot']))
          have h2 : t ⊓ y i = ⊥ := le_bot_iff.mp
            ((inf_le_inf_right (y i) hy).trans_eq (by rw [literal,inf_comm,inf_compl_eq_bot']))
          exact h1.trans h2.symm
        · rw [hb] at hx hy
          exact (inf_eq_left.mpr hx).trans (inf_eq_left.mpr hy).symm
      exact ht (le_bot_iff.mp ((le_inf heq (hts.trans (hsr.trans hdiff))).trans_eq (inf_compl_eq_bot')))
    have hu' : ExtendsWord st.1 u := extendsWord_of_compatible_r173 x ht
      (hu ▸ le_max_left _ _) (htq.trans (hst.trans (inf_le_right.trans inf_le_left))) (hts.trans hU)
    have hv' : ExtendsWord st.2 v := extendsWord_of_compatible_r173 y ht
      (hv ▸ le_max_left _ _) (htq.trans (hst.trans (inf_le_right.trans inf_le_right))) hV
    have htCode : t ≤ offDiagonalTable K (u,v) :=
      (htq.trans (hst.trans inf_le_left)).trans (le_iSup (fun r : {r : Word × Word // ExtendsWord r.1 u ∧ ExtendsWord r.2 v ∧ WordsDisagree u v} => K r.val)
        ⟨st,hu',hv',hwords⟩)
    have htU : t ≤ U := edgeBox_suffices_r136 _ x y (u,v) htCode (hts.trans hU) hV
    have htUC : t ≤ Uᶜ := htq.trans (hqp.trans inf_le_right)
    exact ht (le_bot_iff.mp ((le_inf htU htUC).trans_eq (inf_compl_eq_bot')))

end CantorCodes
end JSP000933
