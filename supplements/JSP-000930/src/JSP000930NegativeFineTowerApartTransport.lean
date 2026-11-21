import JSP000930NegativeFineTowerApartOld
import JSP000930PositiveSubmodelTaylorNameTransport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.ForcingTransport JSP000930.Positive

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem liftName_codeNameOfComplexBits (F : CompleteValueMap B C) (a : ℕ → ComplexBits B) :
    (coefficientsOfValueMap F).liftName (codeNameOfComplexBits a) = transportedTaylorCode F a := by
  unfold codeNameOfComplexBits
  rw [liftName_taylorCode]
  change taylorCodeName _ = taylorCodeName _
  congr 1
  funext j
  rcases j with ⟨n,b,q⟩
  cases b <;> rfl

theorem map_mixed_taylor_code_apart (F : CompleteValueMap B C) (a d : ℕ → ComplexBits B)
    (p : B) (h : p ≤ (codeNameOfComplexBits a =ᴮ codeNameOfComplexBits d)ᶜ) :
    F.toFun p ≤ (transportedTaylorCode F a =ᴮ transportedTaylorCode F d)ᶜ := by
  let S := coefficientsOfValueMap F
  have he : F.toFun (codeNameOfComplexBits a =ᴮ codeNameOfComplexBits d) =
      (transportedTaylorCode F a =ᴮ transportedTaylorCode F d) := by
    change S.map (codeNameOfComplexBits a =ᴮ codeNameOfComplexBits d) = _
    exact (S.liftName_eq (codeNameOfComplexBits a) (codeNameOfComplexBits d)).symm.trans
      (congrArg₂ (fun x y : bSet C => x =ᴮ y)
        (liftName_codeNameOfComplexBits F a) (liftName_codeNameOfComplexBits F d))
  simpa only [F.map_compl,he] using F.monotone h

theorem transportedActualFineTower_apart_old_code [Infinite J]
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (G : CompleteValueMap (TotalBA (polynomialQ site H)) C)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hSep : ∀ i j, i ≠ j → (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hY : ∀ i n,(H i n).CutOn (⊤ : B))
    (hAvoid : ∀ i, AvoidingPalette (H i))
    (a : ℕ → ComplexBits B) (ha : ∀ n,(a n).CutOn (⊤ : B))
    (hg : GrowthOn (⊤ : B) a) :
    let F := polynomialBaseValueMap site H
    let T := actualFinePolynomialTower site H
    (⊤ : C) ≤ (transportedTaylorCode G T.limitCoefficients =ᴮ
      transportedTaylorCode G (fun n => (a n).map F))ᶜ := by
  let Q := polynomialQ site H
  let F := polynomialBaseValueMap site H
  let T := actualFinePolynomialTower site H
  have h : (⊤ : TotalBA Q) ≤
      (codeNameOfComplexBits T.limitCoefficients =ᴮ codeNameOfComplexBits (fun n => (a n).map F))ᶜ :=
    actualFineTower_apart_old_code site H hSite hSep hY hAvoid a ha hg
  simpa only [G.map_top] using
    map_mixed_taylor_code_apart G T.limitCoefficients (fun n => (a n).map F) ⊤ h

end JSP000930.Negative
