import JSP000933FiniteBitLocalOpenCode

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def rowPrefixBound (N : ℕ) : ℕ :=
  (Finset.range N).sup (fun i => (enumeratedWord i).length)

theorem rowPrefixBound_spec_r279 (N : ℕ) (i : Fin N) :
    (enumeratedWord i.val).length≤rowPrefixBound N :=
  Finset.le_sup (f := fun j => (enumeratedWord j).length) (Finset.mem_range.mpr i.isLt)

theorem closedPotentialAt_rows_bounded_r279 (K : Word × Word → B) (s : Word) (N : ℕ) :
    BoundedBitLocal (rowPrefixBound N) (fun x => closedPotentialAt (namedRowOpen K x) N s) := by
  intro p x y h
  unfold closedPotentialAt
  apply mask_iSup_congr_r126
  intro z
  apply mask_inf_congr_r126 rfl
  unfold finiteClosedValue
  apply mask_iInf_congr_r126
  intro i
  apply mask_compl_congr_r126
  apply mask_openValue_codeCongr_r262
  intro v
  unfold namedRowOpen
  exact mask_inf_congr_r126 rfl (mask_cylinder_bounded_r278 (enumeratedWord i.val)
    (fun m hm => h m (hm.trans_le (rowPrefixBound_spec_r279 N i))))

noncomputable def projectedFailureCode (K : Word × Word → B) (s u : Word) : B :=
  ⨆ N : ℕ, boundedTestOpenCode (rowPrefixBound N)
    (fun x => (closedPotentialAt (namedRowOpen K x) N s)ᶜ) u

theorem projectedFailureCode_value_r279 (K : Word × Word → B) (s : Word) (x : ℕ → B) :
    openValue (projectedFailureCode K s) x=(actualFiberFeasible K x s)ᶜ := by
  unfold projectedFailureCode
  rw [openValue_iSup_code_r274,actualFiberFeasible_eq_finite_potential_r277]
  unfold closedPotential
  rw [compl_iInf]
  exact congrArg iSup (funext (fun N => boundedTestOpenCode_value_r278 (rowPrefixBound N) _
    ((closedPotentialAt_rows_bounded_r279 K s N).compl_r278) x))

end SetLanguage
end JSP000933
