import JSP000933GroundCantorCode

namespace JSP000933
namespace CantorCodes

open BooleanCompletion

variable {B C I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

abbrev CoverCode (B : Type) := ℕ → Word → B

noncomputable def ClosedMember (c : CoverCode B) (n : ℕ) (x : ℕ → B) : B :=
  (openValue (c n) x)ᶜ

noncomputable def coverValue (x : I → ℕ → B) (d : I → B) (c : CoverCode B) : B :=
  ⨅ i : I, (d i)ᶜ ⊔ (⨆ n, ClosedMember c n (x i))

noncomputable def independentValue (x : I → ℕ → B) (d : I → B)
    (K : Word × Word → B) (c : CoverCode B) : B :=
  ⨅ a : ℕ × I × I,
    ((d a.2.1 ⊓ d a.2.2) ⊓ (ClosedMember c a.1 (x a.2.1) ⊓ ClosedMember c a.1 (x a.2.2)))ᶜ
      ⊔ (colorValue K (x a.2.1) (x a.2.2))ᶜ

noncomputable def goodCoverValue (x : I → ℕ → B) (d : I → B)
    (K : Word × Word → B) (c : CoverCode B) : B :=
  coverValue x d c ⊓ independentValue x d K c

noncomputable def missedPoint (x : I → ℕ → B) (d : I → B) (c : CoverCode B) (i : I) : B :=
  d i ⊓ (⨅ n, openValue (c n) (x i))

noncomputable def badEdge (x : I → ℕ → B) (d : I → B)
    (K : Word × Word → B) (c : CoverCode B) (a : ℕ × I × I) : B :=
  ((d a.2.1 ⊓ d a.2.2) ⊓ (ClosedMember c a.1 (x a.2.1) ⊓ ClosedMember c a.1 (x a.2.2)))
    ⊓ colorValue K (x a.2.1) (x a.2.2)

theorem goodCover_compl_r112 (x : I → ℕ → B) (d : I → B)
    (K : Word × Word → B) (c : CoverCode B) :
    (goodCoverValue x d K c)ᶜ =
      (⨆ i, missedPoint x d c i) ⊔ (⨆ a, badEdge x d K c a) := by
  simp only [goodCoverValue,coverValue,independentValue,missedPoint,badEdge,ClosedMember,
    compl_inf,compl_iInf,compl_sup,compl_compl,compl_iSup]

theorem map_missedPoint_r112 (F : CompleteValueMap B C)
    (x : I → ℕ → B) (d : I → B) (c : CoverCode B) (i : I) :
    F.toFun (missedPoint x d c i) =
      missedPoint (fun j n => F.toFun (x j n)) (fun j => F.toFun (d j))
        (fun n w => F.toFun (c n w)) i := by
  simp only [missedPoint,F.map_inf,F.map_iInf,map_openValue_r105]

theorem map_badEdge_r112 (F : CompleteValueMap B C)
    (x : I → ℕ → B) (d : I → B) (K : Word × Word → B) (c : CoverCode B) (a : ℕ × I × I) :
    F.toFun (badEdge x d K c a) =
      badEdge (fun j n => F.toFun (x j n)) (fun j => F.toFun (d j)) (fun w => F.toFun (K w))
        (fun n w => F.toFun (c n w)) a := by
  simp only [badEdge,ClosedMember,F.map_inf,F.map_compl,map_openValue_r105,map_colorValue_r105]

end CantorCodes
end JSP000933
