import JSP000930PositiveEntireTaylorNameCover
import JSP000933CompleteNameTransport

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanCompletion JSP000933.ForcingTransport
  JSP000933.BooleanNames JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

def coefficientsOfValueMap (F : CompleteValueMap B C) : NameCoefficients B C where
  map := F.toFun
  map_top := F.map_top
  map_inf := F.map_inf
  map_compl := F.map_compl
  map_iSup := F.map_iSup

theorem liftName_weighted_insert (F : NameCoefficients B C) (x y : bSet B) (b : B) :
    F.liftName (bSet.insert x b y) =
      bSet.insert (F.liftName x) (F.map b) (F.liftName y) := by
  cases y with
  | mk I f w =>
    change bSet.mk (Option I) (fun i => F.liftName (Option.rec x f i))
      (fun i => F.map (Option.rec b w i)) =
      bSet.mk (Option I)
        (fun i => Option.rec (F.liftName x) (fun j => F.liftName (f j)) i)
        (fun i => Option.rec (F.map b) (fun j => F.map (w j)) i)
    congr 1
    · funext i
      cases i <;> rfl
    · funext i
      cases i <;> rfl

theorem liftName_empty (F : NameCoefficients B C) :
    F.liftName (∅ : bSet B) = (∅ : bSet C) := by
  change bSet.mk PEmpty (fun i => F.liftName (PEmpty.elim i))
    (fun i => F.map (PEmpty.elim i)) = bSet.mk PEmpty PEmpty.elim PEmpty.elim
  congr 1 <;> funext i <;> exact PEmpty.elim i

theorem liftName_insert1 (F : NameCoefficients B C) (x y : bSet B) :
    F.liftName (bSet.insert1 x y) = bSet.insert1 (F.liftName x) (F.liftName y) := by
  simp only [bSet.insert1,liftName_weighted_insert,F.map_top]

theorem liftName_pair (F : NameCoefficients B C) (x y : bSet B) :
    F.liftName (pair x y) = pair (F.liftName x) (F.liftName y) := by
  change F.liftName (bSet.insert1 (bSet.insert1 x ∅)
    (bSet.insert1 (bSet.insert1 x (bSet.insert1 y ∅)) ∅)) =
    bSet.insert1 (bSet.insert1 (F.liftName x) ∅)
      (bSet.insert1 (bSet.insert1 (F.liftName x) (bSet.insert1 (F.liftName y) ∅)) ∅)
  simp only [bSet.insert1,liftName_weighted_insert,F.map_top,liftName_empty]

theorem liftName_of_nat (F : NameCoefficients B C) (n : ℕ) :
    F.liftName (bSet.of_nat n) = bSet.of_nat n :=
  F.liftName_check _

theorem liftName_ratName (F : NameCoefficients B C) (q : RatPresentation) :
    F.liftName (ratName q) = ratName q := by
  simp only [ratName,liftName_pair,liftName_of_nat]

theorem liftName_cut (F : NameCoefficients B C) (u : RatPresentation → B) :
    F.liftName (weightedRationalSet u) = weightedRationalSet (fun q => F.map (u q)) := by
  change familyName (fun q => F.liftName (ratName q)) (fun q => F.map (u q)) = _
  simp only [liftName_ratName,weightedRationalSet]

theorem liftName_coefficient (F : NameCoefficients B C) (U : TaylorSlot → B) (n : ℕ) :
    F.liftName (coefficientName U n) = coefficientName (fun i => F.map (U i)) n := by
  simp only [coefficientName,liftName_pair,liftName_cut]

theorem liftName_taylorCode (F : NameCoefficients B C) (U : TaylorSlot → B) :
    F.liftName (taylorCodeName U) = taylorCodeName (fun i => F.map (U i)) := by
  change familyName (fun n : ℕ => F.liftName (pair (bSet.of_nat n) (coefficientName U n)))
    (fun _ => F.map ⊤) =
      familyName (fun n : ℕ => pair (bSet.of_nat n)
        (coefficientName (fun i => F.map (U i)) n)) (fun _ => ⊤)
  simp only [liftName_pair,liftName_of_nat,liftName_coefficient,F.map_top]

theorem decodeTaylorBits_map (F : NameCoefficients B C) (x : ℕ → B) :
    decodeTaylorBits (fun n => F.map (x n)) = fun j => F.map (decodeTaylorBits x j) :=
  rfl

end JSP000930.Positive
