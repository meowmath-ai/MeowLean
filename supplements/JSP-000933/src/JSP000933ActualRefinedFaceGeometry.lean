import JSP000933ActualRegularUniformToContinuous

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def namedSplitMerge (a b z x y : ℕ → B) (m : ℕ) : B :=
  (a m⊓x m)⊔((b m⊓y m)⊔((a m⊔b m)ᶜ⊓z m))

theorem namedSplitMerge_first_prefix_r322 (a b z y : ℕ → B) :
    NamedPrefixMap (fun x => namedSplitMerge a b z x y) := by
  intro p n x x' h m hm
  exact mask_sup_congr_r211 (mask_inf_congr_r126 rfl (h m hm)) rfl

theorem namedSplitMerge_second_prefix_r322 (a b z x : ℕ → B) :
    NamedPrefixMap (fun y => namedSplitMerge a b z x y) := by
  intro p n y y' h m hm
  exact mask_sup_congr_r211 rfl (mask_sup_congr_r211 (mask_inf_congr_r126 rfl (h m hm)) rfl)

theorem namedSplitMerge_first_mask_r322 (a b z x y : ℕ → B) (m : ℕ) (hab : a m⊓b m=⊥) :
    a m⊓namedSplitMerge a b z x y m=a m⊓x m := by
  have hc : a m⊓(a m⊔b m)ᶜ=⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ (compl_le_compl le_sup_left)).trans_eq inf_compl_eq_bot')
  simp only [namedSplitMerge,inf_sup_left,← inf_assoc,inf_idem,hab,hc,bot_inf_eq,bot_sup_eq,sup_bot_eq]

theorem namedSplitMerge_outside_mask_r322 (a b z x y : ℕ → B) (m : ℕ) :
    (a m⊔b m)ᶜ⊓namedSplitMerge a b z x y m=(a m⊔b m)ᶜ⊓z m := by
  have hA : (a m⊔b m)ᶜ⊓a m=⊥ := le_bot_iff.mp
    ((inf_le_inf_left _ le_sup_left).trans_eq ((inf_comm _ _).trans inf_compl_eq_bot'))
  have hB : (a m⊔b m)ᶜ⊓b m=⊥ := le_bot_iff.mp
    ((inf_le_inf_left _ le_sup_right).trans_eq ((inf_comm _ _).trans inf_compl_eq_bot'))
  simp only [namedSplitMerge,inf_sup_left,← inf_assoc,inf_idem,hA,hB,bot_inf_eq,bot_sup_eq]

def refinedFaceFixed (a b z x P : ℕ → B) (side : Bool) (m : ℕ) : B :=
  (a m⊓x m)⊔((b m⊓((sectionFreeBits P side m)ᶜ⊓sectionTemplateBits P m))⊔((a m⊔b m)ᶜ⊓z m))

theorem refinedFaceFixed_eq_merge_zero_r322 (a b z x P : ℕ → B) (side : Bool) :
    refinedFaceFixed a b z x P side=
      namedSplitMerge a b z x (actualSectionPoint P side (fun _ => ⊥)) := by
  funext m
  simp only [refinedFaceFixed,namedSplitMerge,actualSectionPoint,inf_bot_eq,bot_sup_eq]

theorem namedSplitMerge_section_eq_face_r322 (a b z x P y : ℕ → B) (side : Bool)
    (hD : ∀ m, a m⊓b m=⊥) :
    namedSplitMerge a b z x (actualSectionPoint P side y)=
      namedFacePoint (bitsMeet b (sectionFreeBits P side)) (refinedFaceFixed a b z x P side) y := by
  funext m
  let e := sectionFreeBits P side m
  let t := sectionTemplateBits P m
  let u := b m⊓e
  let v := refinedFaceFixed a b z x P side m
  have hA : u⊓(a m⊓x m)≤⊥ := ((le_inf (inf_le_right.trans inf_le_left)
    (inf_le_left.trans inf_le_left)).trans_eq (hD m))
  have hB : u⊓(b m⊓(eᶜ⊓t))≤⊥ := ((le_inf (inf_le_left.trans inf_le_right)
    (inf_le_right.trans (inf_le_right.trans inf_le_left))).trans_eq inf_compl_eq_bot')
  have hC : u⊓((a m⊔b m)ᶜ⊓z m)≤⊥ := ((le_inf
    (inf_le_left.trans (inf_le_left.trans le_sup_right))
    (inf_le_right.trans inf_le_left)).trans_eq inf_compl_eq_bot')
  have hv : v≤uᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    rw [inf_comm]
    change u⊓((a m⊓x m)⊔((b m⊓(eᶜ⊓t))⊔((a m⊔b m)ᶜ⊓z m)))≤⊥
    rw [inf_sup_left,inf_sup_left]
    exact sup_le hA (sup_le hB hC)
  have he : uᶜ⊓v=v := inf_eq_right.mpr hv
  change (a m⊓x m)⊔((b m⊓((e⊓y m)⊔(eᶜ⊓t)))⊔((a m⊔b m)ᶜ⊓z m))=(u⊓y m)⊔(uᶜ⊓v)
  rw [he,inf_sup_left]
  dsimp only [u,v,refinedFaceFixed]
  change (a m⊓x m)⊔(((b m⊓(e⊓y m))⊔(b m⊓(eᶜ⊓t)))⊔((a m⊔b m)ᶜ⊓z m))=
    ((b m⊓e)⊓y m)⊔((a m⊓x m)⊔((b m⊓(eᶜ⊓t))⊔((a m⊔b m)ᶜ⊓z m)))
  rw [← inf_assoc (b m) e (y m)]
  ac_rfl

end SetLanguage
end JSP000933
