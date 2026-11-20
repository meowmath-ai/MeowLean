import JSP000933ActualContinuousCountableSameBranch

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def valuedBit (b : Bool) (a : B) : B := if b then a else aᶜ

theorem mask_valuedBit_congr_r301 (b : Bool) {p a c : B} (he : p⊓a=p⊓c) :
    p⊓valuedBit b a=p⊓valuedBit b c := by
  cases b
  · exact mask_compl_congr_r126 he
  · exact he

noncomputable def namedOutputOpenCode (f : (ℕ → B) → ℕ → B) (m : ℕ) (b : Bool) (u : Word) : B :=
  ⨅ x : ℕ → B, (cylinderValue x u)ᶜ⊔valuedBit b (f x m)

theorem outputOpenCode_le_bit_r301 (f : (ℕ → B) → ℕ → B) (x : ℕ → B) (m : ℕ) (b : Bool) :
    openValue (namedOutputOpenCode f m b) x≤valuedBit b (f x m) := by
  unfold openValue
  apply iSup_le
  intro u
  apply (le_inf le_rfl inf_le_right).trans
  have h : namedOutputOpenCode f m b u≤(cylinderValue x u)ᶜ⊔valuedBit b (f x m) := iInf_le _ x
  exact ((le_materialImp_iff_r126 _ _ _).mp (inf_le_left.trans h))

theorem NamedContinuousOn.outputOpenCode_mask_r301 {p : B} {f : (ℕ → B) → ℕ → B}
    (h : NamedContinuousOn p f) (x : ℕ → B) (m : ℕ) (b : Bool) :
    p⊓openValue (namedOutputOpenCode f m b) x=p⊓valuedBit b (f x m) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (outputOpenCode_le_bit_r301 f x m b)
  · apply le_inf inf_le_left
    apply le_of_dense_named_refinements_r219
    intro q hq hQ
    obtain ⟨r,u,hr,hrq,hR,hM⟩ := h x (m+1) q hq (hQ.trans inf_le_left)
    have hCode : r≤namedOutputOpenCode f m b u := by
      unfold namedOutputOpenCode
      apply le_iInf
      intro z
      apply (le_materialImp_iff_r126 _ _ _).mpr
      let t := r⊓cylinderValue z u
      have ht : t≤valuedBit b (f x m) := inf_le_left.trans (hrq.trans (hQ.trans inf_le_right))
      have hEq := mask_valuedBit_congr_r301 b
        (hM z t inf_le_left inf_le_right m (Nat.lt_succ_self m))
      exact ((le_inf le_rfl ht).trans_eq hEq).trans inf_le_right
    exact ⟨r,hr,hrq,le_iSup_of_le u (le_inf hCode hR)⟩

end SetLanguage
end JSP000933
