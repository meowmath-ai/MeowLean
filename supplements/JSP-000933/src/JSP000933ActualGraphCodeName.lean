import JSP000933ActualProfileDomain

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def wordPairName (v : Word × Word) : bSet B :=
  bSet.pair (wordName v.1) (wordName v.2)

noncomputable def graphCodeName (K : Word × Word → B) : bSet B :=
  familyName wordPairName K

theorem wordPairName_separated_r241 {u v : Word × Word} (h : u ≠ v) :
    ((wordPairName u : bSet B) =ᴮ wordPairName v) = ⊥ := by
  apply le_bot_iff.mp
  by_cases h1 : u.1=v.1
  · have h2 : u.2≠v.2 := fun he => h (Prod.ext h1 he)
    exact bSet.eq_of_eq_pair_right.trans_eq (wordNames_separated_r175 h2)
  · exact bSet.eq_of_eq_pair_left.trans_eq (wordNames_separated_r175 h1)

theorem graphCodeName_mem_r241 (K : Word × Word → B) (u : Word × Word) :
    (wordPairName u ∈ᴮ graphCodeName K) = K u :=
  mem_familyName_self_r70 wordPairName (fun _ _ h => wordPairName_separated_r241 h) K u

theorem namedRawColorCode_of_graphCode_r241 (K : Word × Word → B) :
    namedRawColorCode (graphCodeName K) = fun u => K u ⊔ K (u.2,u.1) := by
  funext u
  exact congrArg₂ (· ⊔ ·) (graphCodeName_mem_r241 K u) (graphCodeName_mem_r241 K (u.2,u.1))

theorem colorValue_symmetrized_r241 (K : Word × Word → B) (x y : ℕ → B) :
    colorValue (fun u => K u ⊔ K (u.2,u.1)) x y = colorValue K x y ⊔ colorValue K y x := by
  unfold colorValue
  apply le_antisymm
  · apply iSup_le
    intro uv
    rw [inf_sup_right]
    apply sup_le
    · exact (le_iSup (fun w : Word × Word => K w ⊓ (cylinderValue x w.1 ⊓ cylinderValue y w.2)) uv).trans le_sup_left
    · apply (le_iSup_of_le (uv.2,uv.1) ?_).trans le_sup_right
      rw [inf_comm (cylinderValue x uv.1) (cylinderValue y uv.2)]
  · apply sup_le
    · apply iSup_le
      intro u
      exact le_iSup_of_le u (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
    · apply iSup_le
      intro u
      apply le_iSup_of_le (u.2,u.1)
      exact le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans_eq (inf_comm _ _))

theorem namedOpenEdge_graphCode_r241 (K : Word × Word → B) (x y : ℕ → B) :
    namedOpenEdgeValue (graphCodeName K) (realBitsName x) (realBitsName y) =
      (realEqValue x y)ᶜ ⊓ (colorValue K x y ⊔ colorValue K y x) := by
  unfold namedOpenEdgeValue
  rw [realBitsName_eq_r128,namedRawEdge_eq_color_r177,namedRawColorCode_of_graphCode_r241,
    colorValue_symmetrized_r241,membershipBits_realBitsName_r128,membershipBits_realBitsName_r128]

end SetLanguage
end JSP000933
