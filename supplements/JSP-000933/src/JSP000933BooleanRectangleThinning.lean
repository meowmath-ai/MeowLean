import JSP000933BooleanRectangleCompatibility

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

abbrev OffDiag (n : ℕ) := {q : Fin n × Fin n // q.1 ≠ q.2}

theorem exists_uniformOffDiagonal_r153 (K : Word × Word → B) {n : ℕ}
    (X : I → Fin n → ℕ → B) (r : I → B)
    (hI : ¬ Countable I) (hN : ∀ i, r i ≠ ⊥)
    (hC : ∀ i j k, j ≠ k → r i ≤ colorValue K (X i j) (X i k)) :
    ∃ S : Set I, ¬ Countable (↥S) ∧
      ∃ w : ↥S → B, (∀ i, w i ≠ ⊥ ∧ w i ≤ r i.1) ∧
        ∀ i j a b, a ≠ b → w i ⊓ w j ≤ colorValue K (X i.1 a) (X j.1 b) := by
  classical
  have hEach (i : I) : ∃ code : OffDiag n → Word × Word, ∃ w : B,
      w ≠ ⊥ ∧ w ≤ r i ∧ ∀ a : OffDiag n, w ≤ K (code a) ∧
        w ≤ cylinderValue (X i a.1.1) (code a).1 ∧ w ≤ cylinderValue (X i a.1.2) (code a).2 := by
    let f (a : OffDiag n) (u : Word × Word) :=
      K u ⊓ (cylinderValue (X i a.1.1) u.1 ⊓ cylinderValue (X i a.1.2) u.2)
    obtain ⟨c,p,hp,hpr,hBox⟩ := exists_nonzero_finiteChoices_r135 f (r i) (hN i)
      (le_iInf (fun a : OffDiag n => hC i a.1.1 a.1.2 a.2))
    exact ⟨c,p,hp,hpr,fun a => ⟨(hBox a).trans inf_le_left,
      (hBox a).trans (inf_le_right.trans inf_le_left),
      (hBox a).trans (inf_le_right.trans inf_le_right)⟩⟩
  choose code w h using hEach
  obtain ⟨c,hc⟩ := exists_uncountable_fiber_r151 hI code
  let S : Set I := {i | code i = c}
  refine ⟨S,hc,fun i => w i.1,fun i => ⟨(h i.1).1,(h i.1).2.1⟩,?_⟩
  intro i j a b hne
  let q : OffDiag n := ⟨(a,b),hne⟩
  have hj : code i.1 q = code j.1 q := congrFun (i.2.trans j.2.symm) q
  apply edgeBox_suffices_r136 K (X i.1 a) (X j.1 b) (code i.1 q)
    (inf_le_left.trans (((h i.1).2.2 q).1))
    (inf_le_left.trans (((h i.1).2.2 q).2.1))
  rw [hj]
  exact inf_le_right.trans (((h j.1).2.2 q).2.2)

end CantorCodes
end JSP000933
