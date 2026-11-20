import JSP000933BooleanCantorBaire

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def saturateOpenCode (K : Word → B) : Word → B :=
  fun u => ⨆ v : {v : Word // ExtendsWord v u}, K v.1

theorem openValue_saturate_r219 (K : Word → B) (x : ℕ → B) :
    openValue (saturateOpenCode K) x = openValue K x := by
  unfold openValue
  apply le_antisymm
  · apply iSup_le
    intro u
    rw [saturateOpenCode,iSup_inf_eq]
    apply iSup_le
    intro v
    exact le_iSup_of_le v.1 (le_inf inf_le_left
      (inf_le_right.trans (cylinderWord_mono_r173 x v.2)))
  · apply iSup_le
    intro u
    exact le_iSup_of_le u (le_inf (inf_le_left.trans
      (le_iSup (fun v : {v : Word // ExtendsWord v u} => K v.1) ⟨u,extendsWord_refl_r216 u⟩))
      inf_le_right)

def DenseOpenNaming (p : B) (K : Word → B) : Prop :=
  ∀ s : Word, p ≤ ⨆ x : ℕ → B, cylinderValue x s ⊓ openValue K x

theorem le_of_dense_named_refinements_r219 (p v : B)
    (h : ∀ q : B, q ≠ ⊥ → q ≤ p → ∃ r : B, r ≠ ⊥ ∧ r ≤ q ∧ r ≤ v) : p ≤ v := by
  classical
  by_contra hn
  let q := p ⊓ vᶜ
  have hq : q ≠ ⊥ := by
    intro h0
    have hd : Disjoint p vᶜ := disjoint_iff_inf_le.mpr h0.le
    exact hn (by simpa only [compl_compl] using (le_compl_iff_disjoint_right.mpr hd))
  obtain ⟨r,hr,hrq,hrv⟩ := h q hq inf_le_left
  exact hr (le_bot_iff.mp ((le_inf hrv (hrq.trans inf_le_right)).trans_eq (inf_compl_eq_bot' (x := v))))

theorem DenseOpenNaming.longExtensions_r219 {p : B} {K : Word → B}
    (h : DenseOpenNaming p K) (n : ℕ) : DenseLongExtensions p n (saturateOpenCode K) := by
  intro u
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨x,r,hr,hrq,hxr⟩ := exists_nonzero_below_choice_r135 q hq
    (fun x : ℕ → B => cylinderValue x u ⊓ openValue K x) (hqp.trans (h u))
  obtain ⟨v,s,hs,hsr,hvs⟩ := exists_nonzero_below_choice_r135 r hr
    (fun v : Word => K v ⊓ cylinderValue x v) (hxr.trans inf_le_right)
  obtain ⟨w,hw,t,ht,hts,hwt⟩ := exists_decided_initialWord_r136 x
    (max n (max u.length v.length)) s hs
  have hu : ExtendsWord u w := extendsWord_of_compatible_r173 x ht
    (hw ▸ (le_max_left _ _).trans (le_max_right _ _))
    (hts.trans (hsr.trans (hxr.trans inf_le_left))) hwt
  have hv : ExtendsWord v w := extendsWord_of_compatible_r173 x ht
    (hw ▸ (le_max_right _ _).trans (le_max_right _ _))
    (hts.trans (hvs.trans inf_le_right)) hwt
  have hn : n ≤ w.length := hw ▸ le_max_left _ _
  refine ⟨t,ht,hts.trans (hsr.trans hrq),le_iSup_of_le ⟨w,hu,hn⟩ ?_⟩
  exact (hts.trans (hvs.trans inf_le_left)).trans
    (le_iSup (fun v : {v : Word // ExtendsWord v w} => K v.1) ⟨v,hv⟩)

theorem exists_namedReal_meeting_denseOpen_r219 (p : B) (s : Word) (K : ℕ → Word → B)
    (hK : ∀ n, DenseOpenNaming p (K n)) :
    ∃ x : ℕ → B, p ≤ cylinderValue x s ∧ ∀ n, p ≤ openValue (K n) x := by
  obtain ⟨x,hs,h⟩ := exists_namedReal_meeting_denseCodes_r218 p s (fun n => saturateOpenCode (K n))
    (fun n => (hK n).longExtensions_r219 (n+1))
  exact ⟨x,hs,fun n => (h n).trans_eq (openValue_saturate_r219 (K n) x)⟩

end CantorCodes
end JSP000933
