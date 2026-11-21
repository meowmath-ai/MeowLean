import JSP000930NegativePolynomialActualPin
import JSP000930GenericPins

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualFineTower_palette_top930 (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (j : J) (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hApart : ∀ i : J,j≠i → (⊤ : B) ≤ ((site j).name =ᴮ (site i).name)ᶜ)
    (hY : ∀ n,(H j n).CutOn (⊤ : B)) (hD : DensePalette (H j)) :
    let Q := polynomialQ site H
    let F := polynomialBaseValueMap site H
    let T := actualFinePolynomialTower site H
    (⊤ : TotalBA Q) ≤ ⨆ n : ℕ,
      (taylorLimitBits T.limitCoefficients ((site j).map F)).name =ᴮ ((H j n).map F).name := by
  let Q := polynomialQ site H
  let F := polynomialBaseValueMap site H
  let T := actualFinePolynomialTower site H
  let w := taylorLimitBits T.limitCoefficients ((site j).map F)
  change (⊤ : TotalBA Q) ≤ ⨆ n : ℕ, w.name =ᴮ ((H j n).map F).name
  rw [← activePinValue_top site H j hSite hApart hY hD]
  unfold activePinValue
  apply iSup_le
  intro a
  let m := traceValue Q (some a.val)
  have hV : m ≤ F.toFun (polyValid site H a.val) := by
    change traceValue Q (some a.val) ≤ baseEmbed Q (polyValid site H a.val)
    apply (supportProjection_le_iff_r428 Q _ _).mp
    rw [traceValue_support_r429]
    exact le_rfl
  have hP : polyValid site H a.val ≤ ⨆ n : ℕ,
      (a.val.eval (site j)).name =ᴮ (H j n).name :=
    inf_le_right.trans (iInf_le (fun i : {i : J // i ∈ a.val.pins} =>
      ⨆ n : ℕ, (a.val.eval (site i.val)).name =ᴮ (H i.val n).name) ⟨j,a.property⟩)
  have hQ : m ≤ ⨆ n : ℕ,
      (((a.val.eval (site j)).map F).name =ᴮ ((H j n).map F).name) := by
    have h := hV.trans (F.monotone hP)
    simpa only [F.map_iSup,ComplexBits.map_nameEq] using h
  have hEq : m ≤ w.name =ᴮ ((a.val.eval (site j)).map F).name :=
    actualFineTower_preserves_pin site H a.val j a.property (hSite j)
  apply (le_inf hEq hQ).trans
  rw [inf_iSup_eq]
  exact iSup_le fun n => le_iSup_of_le n (bSet.bv_trans inf_le_left inf_le_right)

end JSP000930.Negative
