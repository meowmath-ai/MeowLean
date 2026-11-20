import JSP000933CantorBinarySplits

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def finiteClosedValue (K : ℕ → Word → B) (n : ℕ) (x : ℕ → B) : B :=
  ⨅ i : Fin n, (openValue (K i.val) x)ᶜ

noncomputable def closedPotentialAt (K : ℕ → Word → B) (n : ℕ) (u : Word) : B :=
  ⨆ x : ℕ → B, cylinderValue x u ⊓ finiteClosedValue K n x

noncomputable def closedPotential (K : ℕ → Word → B) (u : Word) : B :=
  ⨅ n : ℕ, closedPotentialAt K n u

theorem finiteClosedValue_antitone_r222 (K : ℕ → Word → B) (x : ℕ → B) :
    Antitone (fun n => finiteClosedValue K n x) := by
  intro m n h
  apply le_iInf
  intro i
  exact iInf_le _ (⟨i.val,i.isLt.trans_le h⟩ : Fin n)

theorem closedPotentialAt_antitone_r222 (K : ℕ → Word → B) (u : Word) :
    Antitone (fun n => closedPotentialAt K n u) := by
  intro m n h
  apply iSup_le
  intro x
  exact le_iSup_of_le x (inf_le_inf_left _ (finiteClosedValue_antitone_r222 K x h))

theorem closedPotentialAt_binary_r222 (K : ℕ → Word → B) (n : ℕ) (u : Word) :
    closedPotentialAt K n u =
      closedPotentialAt K n (u++[false]) ⊔ closedPotentialAt K n (u++[true]) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [← cylinder_binary_split_r221 x u,inf_sup_right]
    exact sup_le_sup
      (le_iSup (fun y => cylinderValue y (u ++ [false]) ⊓ finiteClosedValue K n y) x)
      (le_iSup (fun y => cylinderValue y (u ++ [true]) ⊓ finiteClosedValue K n y) x)
  · apply sup_le
    all_goals
      apply iSup_le
      intro x
      exact le_iSup_of_le x (inf_le_inf_right _ (cylinderWord_mono_r173 x (wordExtends_appendBit_r221 u _)))

theorem closedPotential_binary_r222 (K : ℕ → Word → B) (u : Word) :
    closedPotential K u = closedPotential K (u++[false]) ⊔ closedPotential K (u++[true]) := by
  calc
    _ = ⨅ n, closedPotentialAt K n (u++[false]) ⊔ closedPotentialAt K n (u++[true]) :=
      congrArg iInf (funext (fun n => closedPotentialAt_binary_r222 K n u))
    _ = _ := iInf_sup_antitone_r221 _ _ (closedPotentialAt_antitone_r222 K _)
      (closedPotentialAt_antitone_r222 K _)

end CantorCodes
end JSP000933
