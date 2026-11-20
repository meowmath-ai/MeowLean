import JSP000933ActualProjectedFeasibility

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def closedBoundaryRegularCode (K : Word → B) (u : Word) : B :=
  K u⊔cylinderInClosedValue K u

theorem paddedWord_in_ownCylinder_r280 (u : Word) : (⊤ : B)≤cylinderValue (paddedWordBits u) u := by
  unfold cylinderValue
  apply le_iInf
  intro m
  cases hb : u[m.val]'m.isLt <;> simp [paddedWordBits,wordBit,dite_eq_left m.isLt,hb,literal,truthBit]

theorem openValue_monoCode_r280 {K L : Word → B} (h : ∀ u, K u≤L u) (x : ℕ → B) :
    openValue K x≤openValue L x := by
  unfold openValue
  exact iSup_le (fun u => le_iSup_of_le u (inf_le_inf_right _ (h u)))

theorem closedBoundaryRegular_dense_r280 (K : Word → B) :
    DenseOpenNaming (⊤ : B) (closedBoundaryRegularCode K) := by
  intro u
  let I := cylinderInClosedValue K u
  have hC : (⊤ : B)≤cylinderValue (paddedWordBits u) u := paddedWord_in_ownCylinder_r280 u
  have hI : I≤⨆ x : ℕ → B, cylinderValue x u⊓openValue (closedBoundaryRegularCode K) x := by
    apply le_iSup_of_le (paddedWordBits u)
    exact le_inf (le_top.trans hC)
      (le_iSup_of_le u (le_inf le_sup_right (le_top.trans hC)))
  have hO : Iᶜ≤⨆ x : ℕ → B, cylinderValue x u⊓openValue (closedBoundaryRegularCode K) x := by
    change (cylinderInClosedValue K u)ᶜ≤_
    rw [cylinderInClosedValue_compl_r220]
    exact iSup_le (fun x => le_iSup_of_le x
      (inf_le_inf_left _ (openValue_monoCode_r280 (fun _ => le_sup_left) x)))
  exact ((sup_compl_eq_top : I⊔Iᶜ=⊤).symm.le).trans (sup_le hI hO)

def DecidesOnCylinder (q : B) (s : Word) (f : (ℕ → B) → B) : Prop :=
  (∀ (x : ℕ → B) (r : B), r≤q → r≤cylinderValue x s → r≤f x) ∨
    (∀ (x : ℕ → B) (r : B), r≤q → r≤cylinderValue x s → r≤(f x)ᶜ)

theorem cylinderInClosedValue_elim_r280 (K : Word → B) (s : Word) (x : ℕ → B)
    {q : B} (hI : q≤cylinderInClosedValue K s) (hX : q≤cylinderValue x s) :
    q≤(openValue K x)ᶜ := by
  have h := hI.trans (iInf_le _ x)
  exact (le_inf le_rfl hX).trans ((le_materialImp_iff_r126 _ _ _).mp h)

theorem boundaryRegular_local_decision_r280 (K : Word → B) (x : ℕ → B)
    {p : B} (hp : p≠⊥) (h : p≤openValue (closedBoundaryRegularCode K) x) :
    ∃ (q : B) (u : Word), q≠⊥ ∧ q≤p ∧ q≤cylinderValue x u ∧
      DecidesOnCylinder q u (fun y => (openValue K y)ᶜ) := by
  obtain ⟨u,r,hr,hrp,hR⟩ := exists_nonzero_below_choice_r135 p hp
    (fun u : Word => closedBoundaryRegularCode K u⊓cylinderValue x u) h
  let I := cylinderInClosedValue K u
  have hRI : r≤K u⊔I := hR.trans inf_le_left
  have hRC : r≤cylinderValue x u := hR.trans inf_le_right
  by_cases hZ : r⊓K u=⊥
  · have hI : r≤I := calc
      r = r⊓(K u⊔I) := le_antisymm (le_inf le_rfl hRI) inf_le_left
      _ = (r⊓K u)⊔(r⊓I) := inf_sup_left _ _ _
      _ = r⊓I := by rw [hZ,bot_sup_eq]
      _ ≤ I := inf_le_right
    exact ⟨r,u,hr,hrp,hRC,Or.inl (fun y t ht hT => cylinderInClosedValue_elim_r280 K u y (ht.trans hI) hT)⟩
  · refine ⟨r⊓K u,u,hZ,inf_le_left.trans hrp,inf_le_left.trans hRC,Or.inr ?_⟩
    intro y t ht hT
    rw [compl_compl]
    exact le_iSup_of_le u (le_inf (ht.trans inf_le_right) hT)

end SetLanguage
end JSP000933
