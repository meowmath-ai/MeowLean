import JSP000933InterleavedCylinderCoordinates

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def binaryFromQuadTable (K : Word → B) (a A : ℕ → B) (uv : Word × Word) : B :=
  ⨆ w : {w : Word // quadWordProjection w 1=uv.1 ∧ quadWordProjection w 3=uv.2},
    K w.val ⊓ (cylinderValue a (quadWordProjection w.val 0) ⊓ cylinderValue A (quadWordProjection w.val 2))

theorem binaryFromQuadTable_value_r276 (K : Word → B) (a b A z : ℕ → B) :
    colorValue (binaryFromQuadTable K a A) b z=openValue K (interleaveCrossQuad a b A z) := by
  apply le_antisymm
  · unfold colorValue binaryFromQuadTable
    simp only [iSup_inf_eq]
    apply iSup_le
    intro uv
    apply iSup_le
    intro w
    apply le_iSup_of_le w.val
    rw [cylinderValue_crossQuad_r275,w.property.1,w.property.2]
    simp only [inf_assoc,le_rfl]
  · unfold openValue
    apply iSup_le
    intro w
    let u := quadWordProjection w 1
    let v := quadWordProjection w 3
    apply le_iSup_of_le (u,v)
    have hInside : K w ⊓ (cylinderValue a (quadWordProjection w 0) ⊓
        cylinderValue A (quadWordProjection w 2))≤binaryFromQuadTable K a A (u,v) :=
      le_iSup (fun t : {t : Word // quadWordProjection t 1 = u ∧ quadWordProjection t 3 = v} =>
        K t.val ⊓ (cylinderValue a (quadWordProjection t.val 0) ⊓
          cylinderValue A (quadWordProjection t.val 2))) ⟨w,rfl,rfl⟩
    rw [cylinderValue_crossQuad_r275,← inf_assoc]
    exact inf_le_inf_right _ hInside

noncomputable def rightSectionOpenCode (K : Word × Word → B) (x : ℕ → B) (v : Word) : B :=
  ⨆ u : Word, K (u,v)⊓cylinderValue x u

theorem rightSectionOpenCode_value_r276 (K : Word × Word → B) (x y : ℕ → B) :
    openValue (rightSectionOpenCode K x) y=colorValue K x y := by
  unfold openValue rightSectionOpenCode colorValue
  simp only [iSup_inf_eq,inf_assoc]
  apply le_antisymm
  · exact iSup_le (fun v => iSup_le (fun u => le_iSup_of_le (u,v) le_rfl))
  · apply iSup_le
    rintro ⟨u,v⟩
    exact le_iSup_of_le v (le_iSup_of_le u le_rfl)

noncomputable def actualSampleTreeBinaryCode {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (a A : ℕ → B) : Word × Word → B :=
  binaryFromQuadTable (missingActualSampleTree T j l side) a A

theorem actualSampleTree_binaryClosed_r276 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (a b A z : ℕ → B) :
    fixedActualSampleTree T j l side (interleaveCrossQuad a b A z)=
      (colorValue (actualSampleTreeBinaryCode T j l side a A) b z)ᶜ := by
  rw [fixedActualSampleTree_eq_compl_open_r274,actualSampleTreeBinaryCode,binaryFromQuadTable_value_r276]

theorem actualSampleTree_closed_fiber_r276 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (a b A z : ℕ → B) :
    fixedActualSampleTree T j l side (interleaveCrossQuad a b A z)=
      (openValue (rightSectionOpenCode (actualSampleTreeBinaryCode T j l side a A) b) z)ᶜ := by
  rw [rightSectionOpenCode_value_r276,actualSampleTree_binaryClosed_r276]

end SetLanguage
end JSP000933
