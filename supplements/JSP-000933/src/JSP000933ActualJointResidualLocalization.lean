import JSP000933ActualSectionErrorAlgebra

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev RegularSectionSlot := ℕ × ℕ × Bool × Word

theorem exists_actual_lexRegular_sections_r299 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p) :
    ∃ P : ℕ → B, ∀ (j l : ℕ) (side b : Bool) (x : ℕ → B),
      p≤actualLexRegularValue (actualSideCode T F j l side) (actualSectionPoint P b x) := by
  let slot (i : ℕ) : RegularSectionSlot :=
    (Encodable.decode (α := RegularSectionSlot) i).getD (0,0,false,[])
  let V (s : RegularSectionSlot) : Word → B :=
    closedBoundaryRegularCode (projectedFailureCode (actualSideCode T F s.1 s.2.1 s.2.2.1) s.2.2.2)
  let K (i : ℕ) : Word → B := V (slot i)
  have hD (i : ℕ) : DenseOpenNaming p (K i) :=
    (closedBoundaryRegular_dense_r280 _).restrict_r293 le_top
  obtain ⟨P,hP⟩ := exists_actualComplementarySections_r296 K p hD
  refine ⟨P,fun j l side b x => ?_⟩
  unfold actualLexRegularValue
  apply le_iInf
  intro s
  let z : RegularSectionSlot := (j,l,side,s)
  have hz := hP (Encodable.encode z) b x
  unfold K slot at hz
  rw [Encodable.encodek] at hz
  exact hz

noncomputable def localizedApproxSide {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (P : ℕ → B) (j : ℕ) (i : ℕ × ℕ) (b : Bool) (x : ℕ → B) : ℕ → B :=
  bitsMeet (F.toName (actualCoordinateFace T.freshCap P b))
    (actualJoinedApprox T F j i (actualSectionPoint P b x))

noncomputable def localizedApproxPair {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (P : ℕ → B) (j : ℕ) (i : (ℕ × ℕ) × (ℕ × ℕ)) (x : ℕ → B) : ℕ → B :=
  bitsSymmDiff (localizedApproxSide T F P j i.1 false x) (localizedApproxSide T F P j i.2 true x)

theorem localizedApproxSide_continuous_r299 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p) (P : ℕ → B)
    (hR : ∀ j l side b x, p≤actualLexRegularValue
      (actualSideCode T F j l side) (actualSectionPoint P b x))
    (j : ℕ) (i : ℕ × ℕ) (b : Bool) :
    NamedContinuousOn p (localizedApproxSide T F P j i b) := by
  have h0 := actualLex_on_regular_section_continuous_r297 P b (actualSideCode T F j i.1 false) p
    (hR j i.1 false b)
  have h1 := actualLex_on_regular_section_continuous_r297 P b (actualSideCode T F j i.2 true) p
    (hR j i.2 true b)
  have hA0 := h0.meet_fixed_r297 (F.toName (actualParityCap T.freshCap j false))
  have hA1 := h1.meet_fixed_r297 (F.toName (actualParityCap T.freshCap j true))
  exact (hA0.xor_r297 hA1).meet_fixed_r297 (F.toName (actualCoordinateFace T.freshCap P b))

theorem localizedApproxPair_continuous_r299 {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p) (P : ℕ → B)
    (hR : ∀ j l side b x, p≤actualLexRegularValue
      (actualSideCode T F j l side) (actualSectionPoint P b x))
    (j : ℕ) (i : (ℕ × ℕ) × (ℕ × ℕ)) :
    NamedContinuousOn p (localizedApproxPair T F P j i) :=
  (localizedApproxSide_continuous_r299 T F P hR j i.1 false).xor_r297
    (localizedApproxSide_continuous_r299 T F P hR j i.2 true)

end SetLanguage
end JSP000933
