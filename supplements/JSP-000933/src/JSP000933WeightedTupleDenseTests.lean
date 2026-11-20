import JSP000933InternalAvoidanceSequence

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def listCylinder (x : ℕ → B) (W : List Word) : B :=
  W.foldr (fun w b => cylinderValue x w ⊓ b) ⊤

noncomputable def multiStemCylinder {n : ℕ} (x : Fin n → ℕ → B) (U : Fin n → List Word) : B :=
  ⨅ i, listCylinder (x i) (U i)

noncomputable def sampleBox {n : ℕ} (s : BooleanSample B n) (U : Fin n → List Word) (V : List Word) : B :=
  s.weight ⊓ (multiStemCylinder s.stem U ⊓ listCylinder s.tip V)

theorem exists_countable_weightedBoxDense_r147 (hCCC : BooleanCCC B) {n : ℕ}
    (F : I → BooleanSample B n) :
    ∃ S : Set I, S.Countable ∧ ∀ (U : Fin n → List Word) (V : List Word),
      (⨆ i : ↥S, sampleBox (F i.1) U V) = ⨆ i, sampleBox (F i) U V := by
  obtain ⟨S,hS,hEq⟩ := exists_countable_preserving_all_tests_r134
    (W := (Fin n → List Word) × List Word) hCCC (fun w i => sampleBox (F i) w.1 w.2)
  exact ⟨S,hS,fun U V => hEq (U,V)⟩

theorem exists_matchedWordPairs_r147 (K : Word × Word → B) {n : ℕ}
    (x y : Fin n → ℕ → B) (p : B) (hp : p ≠ ⊥) (h : p ≤ matchedValue K x y) :
    ∃ words : Fin n → Word × Word, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧
      ∀ i, q ≤ K (words i) ∧ q ≤ cylinderValue (x i) (words i).1 ∧
        q ≤ cylinderValue (y i) (words i).2 := by
  let test (i : Fin n) (w : Word × Word) :=
    K w ⊓ (cylinderValue (x i) w.1 ⊓ cylinderValue (y i) w.2)
  obtain ⟨W,q,hq,hqp,hW⟩ := exists_nonzero_finiteChoices_fin_r135 n test p hp h
  exact ⟨W,q,hq,hqp,fun i => ⟨(hW i).trans inf_le_left,
    (hW i).trans (inf_le_right.trans inf_le_left), (hW i).trans (inf_le_right.trans inf_le_right)⟩⟩

theorem matchedValue_of_wordPairs_r147 (K : Word × Word → B) {n : ℕ}
    (x y : Fin n → ℕ → B) (words : Fin n → Word × Word) {q : B}
    (h : ∀ i, q ≤ K (words i) ∧ q ≤ cylinderValue (x i) (words i).1 ∧
      q ≤ cylinderValue (y i) (words i).2) : q ≤ matchedValue K x y :=
  le_iInf (fun i => edgeBox_suffices_r136 K (x i) (y i) (words i)
    (h i).1 (h i).2.1 (h i).2.2)

end CantorCodes
end JSP000933
