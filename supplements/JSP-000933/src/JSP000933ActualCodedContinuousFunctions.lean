import JSP000933ActualExactCoherentRepresentatives

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev NamedBitTable (B : Type) := ℕ → Bool → Word → B

noncomputable def namedTableOutput (C : NamedBitTable B) (x : ℕ → B) (m : ℕ) : B :=
  openValue (C m true) x

noncomputable def namedBitTableValid (C : NamedBitTable B) : B :=
  ⨅ x : ℕ → B, ⨅ m : ℕ, bitEq (openValue (C m false) x) (namedTableOutput C x m)ᶜ

noncomputable def actualFunctionBitTable (f : (ℕ → B) → ℕ → B) : NamedBitTable B :=
  namedOutputOpenCode f

theorem NamedContinuousOn.actualBitTable_valid_r311 {p : B} {f : (ℕ → B) → ℕ → B}
    (h : NamedContinuousOn p f) : p≤namedBitTableValid (actualFunctionBitTable f) := by
  unfold namedBitTableValid
  apply le_iInf
  intro x
  apply le_iInf
  intro m
  apply (le_bitEq_iff_r126 _ _ _).mpr
  exact (h.outputOpenCode_mask_r301 x m false).trans
    (mask_compl_congr_r126 (h.outputOpenCode_mask_r301 x m true)).symm

theorem NamedContinuousOn.actualBitTable_mask_r311 {p : B} {f : (ℕ → B) → ℕ → B}
    (h : NamedContinuousOn p f) (x : ℕ → B) :
    p≤realEqValue (namedTableOutput (actualFunctionBitTable f) x) (f x) :=
  (le_realEqValue_iff_r126 _ _ _).mpr (fun m => h.outputOpenCode_mask_r301 x m true)

abbrev BitTableSlot := ℕ × Bool × Word

def decodedBitTable (x : ℕ → B) (m : ℕ) (b : Bool) (u : Word) : B :=
  x (Encodable.encode ((m,b,u) : BitTableSlot))

def encodedBitTable (C : NamedBitTable B) (i : ℕ) : B :=
  match Encodable.decode (α := BitTableSlot) i with
  | none => ⊥
  | some s => C s.1 s.2.1 s.2.2

theorem decoded_encodedBitTable_r311 (C : NamedBitTable B) : decodedBitTable (encodedBitTable C)=C := by
  funext m b u
  simp only [decodedBitTable,encodedBitTable,Encodable.encodek]

theorem namedTableOutput_ext_r311 (C : NamedBitTable B) : NameMapExt (namedTableOutput C) :=
  fun p x y h => (le_realEqValue_iff_r126 _ _ _).mpr
    (fun m => mask_openValue_congr_r127 (C m true) h)

theorem decodedBitTable_output_mask_r311 {p : B} {c d : ℕ → B}
    (he : p≤realEqValue c d) (x : ℕ → B) :
    p≤realEqValue (namedTableOutput (decodedBitTable c) x) (namedTableOutput (decodedBitTable d) x) :=
  (le_realEqValue_iff_r126 _ _ _).mpr (fun m => mask_openValue_codeCongr_r262 x
    (fun u => (le_realEqValue_iff_r126 p c d).mp he (Encodable.encode ((m,true,u) : BitTableSlot))))

theorem decodedBitTable_valid_ext_r311 : RealTestExt (fun c : ℕ → B => namedBitTableValid (decodedBitTable c)) := by
  intro p c d he
  unfold namedBitTableValid
  apply mask_iInf_congr_r126
  intro x
  apply mask_iInf_congr_r126
  intro m
  exact mask_bitEq_congr_r257
    (mask_openValue_codeCongr_r262 x (fun u => (le_realEqValue_iff_r126 p c d).mp he
      (Encodable.encode ((m,false,u) : BitTableSlot))))
    (mask_compl_congr_r126 ((le_realEqValue_iff_r126 _ _ _).mp (decodedBitTable_output_mask_r311 he x) m))

end SetLanguage
end JSP000933
