import JSP000933ActualTwoSideRegularApproximation

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem extendsWord_append_r292 (u v : Word) : ExtendsWord u (u++v) := by
  refine ⟨by simp,fun i => ?_⟩
  exact List.getElem_append_left' i.isLt v

theorem _root_.JSP000933.CantorCodes.ExtendsWord.to_listPrefix_r292 {u v : Word} (h : ExtendsWord u v) : List.IsPrefix u v := by
  obtain ⟨hl,he⟩ := h
  apply List.prefix_iff_eq_take.mpr
  apply List.ext_getElem (List.length_take_of_le hl).symm
  intro i hi hj
  rw [List.getElem_take]
  exact he ⟨i,hi⟩

theorem saturatedOpenCode_monoWord_r292 (K : Word → B) {u v : Word} (h : ExtendsWord u v) :
    saturateOpenCode K u ≤ saturateOpenCode K v := by
  unfold saturateOpenCode
  exact iSup_le (fun w => le_iSup_of_le ⟨w.val,extendsWord_trans_r216 w.property h⟩ le_rfl)

theorem term_le_saturatedOpenCode_r292 (K : Word → B) (u : Word) :
    K u ≤ saturateOpenCode K u :=
  le_iSup (fun t : {t : Word // ExtendsWord t u} => K t.val) ⟨u,extendsWord_refl_r216 u⟩

theorem denseOpen_has_finite_extension_r292 (K : Word → B) {p : B} (hp : p≠⊥)
    (hd : DenseOpenNaming p K) (u : Word) :
    ∃ (q : B) (w : Word), q≠⊥ ∧ q≤p ∧ q ≤ saturateOpenCode K (u++w) := by
  obtain ⟨x,r,hr,hrp,hR⟩ := exists_nonzero_below_choice_r135 p hp
    (fun x : ℕ → B => cylinderValue x u⊓openValue K x) (hd u)
  obtain ⟨v,t,ht,htr,hT⟩ := exists_nonzero_below_choice_r135 r hr
    (fun v : Word => K v⊓cylinderValue x v) (hR.trans inf_le_right)
  have hU : t≤cylinderValue x u := htr.trans (hR.trans inf_le_left)
  have hV : t≤cylinderValue x v := hT.trans inf_le_right
  rcases le_total u.length v.length with h | h
  · have he := extendsWord_of_compatible_r173 x ht h hU hV
    obtain ⟨w,hw⟩ := he.to_listPrefix_r292
    refine ⟨t,w,ht,htr.trans hrp,?_⟩
    rw [hw]
    exact (hT.trans inf_le_left).trans (term_le_saturatedOpenCode_r292 K v)
  · have he := extendsWord_of_compatible_r173 x ht h hV hU
    refine ⟨t,[],ht,htr.trans hrp,?_⟩
    rw [List.append_nil]
    exact (hT.trans inf_le_left).trans (le_iSup (fun t : {t : Word // ExtendsWord t u} => K t.val) ⟨v,he⟩)

end SetLanguage
end JSP000933
