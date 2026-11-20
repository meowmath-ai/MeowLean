import JSP000933IdleStageCCC
import JSP000933CantorMaskCongruence
import Mathlib.Logic.Equiv.List
import Mathlib.Logic.Encodable.Pi

namespace JSP000933
namespace CantorCodes

open BooleanCompletion OpenGraphForcing

variable {B I W : Type} [CompleteBooleanAlgebra B]

theorem exists_countable_preserving_all_tests_r134 [Countable W] (hCCC : BooleanCCC B)
    (test : W → I → B) :
    ∃ S : Set I, S.Countable ∧ ∀ w, (⨆ i : ↥S, test w i.1) = ⨆ i, test w i := by
  classical
  choose A hA hJoin using (fun w => exists_countable_subjoin_r67 hCCC (test w))
  let S := ⋃ w, A w
  refine ⟨S,Set.countable_iUnion hA,fun w => le_antisymm ?_ ?_⟩
  · exact iSup_le (fun i => le_iSup (test w) i.1)
  · rw [← hJoin w]
    apply iSup_le
    intro i
    exact le_iSup (fun j : ↥S => test w j.1) ⟨i.1,Set.mem_iUnion.mpr ⟨w,i.2⟩⟩

noncomputable def namedTupleClique {n : ℕ} (x : I → ℕ → B) (D : I → B)
    (K : Word × Word → B) (t : Fin n → I) : B :=
  (⨅ i, D (t i)) ⊓
  (⨅ ij : {ij : Fin n × Fin n // ij.1 ≠ ij.2},
    (realEqValue (x (t ij.1.1)) (x (t ij.1.2)))ᶜ ⊓
      colorValue K (x (t ij.1.1)) (x (t ij.1.2)))

noncomputable def namedTupleBasis {n : ℕ} (x : I → ℕ → B)
    (w : Fin n → Word) (t : Fin n → I) : B :=
  ⨅ i, cylinderValue (x (t i)) (w i)

theorem exists_countable_denseCliqueSamples_r134 (hCCC : BooleanCCC B) (n : ℕ)
    (x : I → ℕ → B) (D : I → B) (K : Word × Word → B) :
    ∃ S : Set (Fin n → I), S.Countable ∧
      ∀ w : Fin n → Word,
        (⨆ t : ↥S, namedTupleClique x D K t.1 ⊓ namedTupleBasis x w t.1) =
          ⨆ t : Fin n → I, namedTupleClique x D K t ⊓ namedTupleBasis x w t := by
  exact exists_countable_preserving_all_tests_r134 (W := Fin n → Word) hCCC
    (fun w t => namedTupleClique x D K t ⊓ namedTupleBasis x w t)

end CantorCodes
end JSP000933
