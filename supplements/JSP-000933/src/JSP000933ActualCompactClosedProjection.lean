import JSP000933BinaryClosedSampleFibers
import JSP000933BooleanCantorCompactness

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def enumeratedWord (i : ℕ) : Word := (Encodable.decode (α := Word) i).getD []

theorem enumeratedWord_surj_r277 : Function.Surjective enumeratedWord :=
  Encodable.surjective_decode_getD Word []

noncomputable def namedRowOpen (K : Word × Word → B) (x : ℕ → B) (i : ℕ) (v : Word) : B :=
  K (enumeratedWord i,v)⊓cylinderValue x (enumeratedWord i)

theorem rightSection_eq_rows_r277 (K : Word × Word → B) (x : ℕ → B) :
    rightSectionOpenCode K x=(fun v => ⨆ i, namedRowOpen K x i v) := by
  funext v
  unfold rightSectionOpenCode namedRowOpen
  apply le_antisymm
  · apply iSup_le
    intro u
    obtain ⟨i,hi⟩ := enumeratedWord_surj_r277 u
    apply le_iSup_of_le i
    rw [hi]
  · exact iSup_le (fun i => le_iSup (fun u : Word => K (u,v) ⊓ cylinderValue x u) (enumeratedWord i))

theorem namedClosedColor_eq_iInf_rows_r277 (K : Word × Word → B) (x y : ℕ → B) :
    (colorValue K x y)ᶜ=⨅ i : ℕ, (openValue (namedRowOpen K x i) y)ᶜ := by
  rw [← rightSectionOpenCode_value_r276,rightSection_eq_rows_r277,openValue_iSup_code_r274,compl_iSup]

noncomputable def actualFiberFeasible (K : Word × Word → B) (x : ℕ → B) (s : Word) : B :=
  ⨆ y : ℕ → B, cylinderValue y s⊓(colorValue K x y)ᶜ

theorem actualFiberFeasible_eq_finite_potential_r277 (K : Word × Word → B) (x : ℕ → B) (s : Word) :
    actualFiberFeasible K x s=closedPotential (namedRowOpen K x) s := by
  apply le_antisymm
  · unfold actualFiberFeasible closedPotential
    apply iSup_le
    intro y
    apply le_iInf
    intro n
    change cylinderValue y s⊓(colorValue K x y)ᶜ≤
      ⨆ z : ℕ → B, cylinderValue z s⊓finiteClosedValue (namedRowOpen K x) n z
    apply le_iSup_of_le y
    apply le_inf inf_le_left
    unfold finiteClosedValue
    apply le_iInf
    intro i
    exact inf_le_right.trans ((namedClosedColor_eq_iInf_rows_r277 K x y).le.trans (iInf_le _ i.val))
  · obtain ⟨y,hCyl,hCl⟩ := exists_namedReal_allClosed_r225
      (closedPotential (namedRowOpen K x) s) s (namedRowOpen K x) le_rfl
    have hColor := (le_iInf hCl).trans_eq (namedClosedColor_eq_iInf_rows_r277 K x y).symm
    exact le_iSup_of_le y (le_inf hCyl hColor)

end SetLanguage
end JSP000933
