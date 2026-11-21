import JSP000930NegativePlacementPrefixReduction
import JSP000930NegativeActualBulkReservoir

open bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes JSP000933.PreparedModel
  JSP000930.Positive JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C] {N : Type}

noncomputable def realCutRow (x : ℕ → B) : RatPresentation → B :=
  fun q => decodeTaylorBits x (0,false,q)

noncomputable def packRealCut (u : RatPresentation → B) : ℕ → B :=
  encodeTaylorBits (fun j => u j.2.2)

theorem realCutRow_pack (u : RatPresentation → B) :
    realCutRow (packRealCut u) = u := by
  funext q
  exact congrFun (decode_encode_taylorBits (fun j : TaylorSlot => u j.2.2)) (0,false,q)

noncomputable def decodeTrial (x y : ℕ → B) : ComplexBits B :=
  ⟨realCutRow x,realCutRow y⟩

theorem decodeTrial_commutes (F : CompleteValueMap B C)
    (x y : ℕ → B) (U V : ℕ → C)
    (hx : ∀ n,F.toFun (x n) = U n) (hy : ∀ n,F.toFun (y n) = V n) :
    mapComplexBits F (decodeTrial x y) = decodeTrial U V := by
  letI := taylorSlotEncodable
  change ComplexBits.mk (fun q => F.toFun (x (Encodable.encode ((0,false,q) : TaylorSlot))))
      (fun q => F.toFun (y (Encodable.encode ((0,false,q) : TaylorSlot)))) =
    ComplexBits.mk (fun q => U (Encodable.encode ((0,false,q) : TaylorSlot)))
      (fun q => V (Encodable.encode ((0,false,q) : TaylorSlot)))
  exact congrArg₂ ComplexBits.mk (funext fun _ => hx _) (funext fun _ => hy _)

noncomputable def trialValidity (z : ComplexBits B) : B :=
  properCutValue z.re ⊓ properCutValue z.im

theorem le_trialValidity_iff (z : ComplexBits B) (p : B) :
    p ≤ trialValidity z ↔ z.CutOn p := by
  exact le_inf_iff.trans (and_congr (le_properCutValue_iff _ _) (le_properCutValue_iff _ _))

theorem trialValidity_map (F : CompleteValueMap B C) (z : ComplexBits B) :
    F.toFun (trialValidity z) = trialValidity (mapComplexBits F z) := by
  simp only [trialValidity,F.map_inf,properCutValue_map,mapComplexBits]

abbrev PlacementTrialIndex := PlacementTableIndex × PlacementTableIndex

noncomputable def PlacementBook.trial (F : PlacementBook N) (Q : ValuedPoset PreparedBA N)
    (i : PlacementTrialIndex) :
    ComplexBits (TotalBA Q) :=
  decodeTrial (F.row Q i.1) (F.row Q i.2)

theorem PlacementPrefixSystem.localTrial
    {Q : ValuedPoset PreparedBA N}
    (P : PlacementPrefixSystem Q)
    (F : PlacementBook N) (i : PlacementTrialIndex) :
    ∃ (a : GroundContinuumSuccIndex) (z : ComplexBits (TotalBA (P.poset a))),
      z.CutOn (trialValidity z) ∧
      mapComplexBits (P.into a) z = F.trial Q i ∧
      (P.into a).toFun (trialValidity z) = trialValidity (F.trial Q i) := by
  obtain ⟨a,x,y,hx,hy⟩ := P.two_actualRows_in_prefix F i.1 i.2
  let z := decodeTrial x y
  have h := decodeTrial_commutes (P.into a) x y _ _ hx hy
  exact ⟨a,z,(le_trialValidity_iff _ _).mp le_rfl,h,
    (trialValidity_map (P.into a) z).trans (congrArg trialValidity h)⟩

end JSP000930.Negative
