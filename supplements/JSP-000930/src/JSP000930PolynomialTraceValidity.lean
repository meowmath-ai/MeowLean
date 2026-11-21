import JSP000930NamedComplexMetricLaw

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

noncomputable def properCutValue (u : RatPresentation → B) : B :=
  ((⨆ q : RatPresentation, u q) ⊓ (⨆ q : RatPresentation, (u q)ᶜ)) ⊓
    ((⨅ q : RatPresentation, ⨅ r : RatPresentation, ⨅ (_ : q.value ≤ r.value),
        imp (u r) (u q)) ⊓
     (⨅ q : RatPresentation, imp (u q)
       (⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), u r)))

theorem le_properCutValue_iff (p : B) (u : RatPresentation → B) :
    p ≤ properCutValue u ↔ ProperCutOn p u := by
  unfold properCutValue ProperCutOn
  simp only [le_inf_iff, le_iInf_iff, ← _root_.deduction, and_assoc]

theorem map_properCutValue (F : CompleteValueMap B C) (u : RatPresentation → B) :
    F.toFun (properCutValue u) = properCutValue (mapCut F u) := by
  simp only [properCutValue, _root_.imp, F.map_inf, F.map_iInf, map_iInf_prop930 F,
    F.map_iSup, map_iSup_prop930 F, F.map_sup_r93, F.map_compl, mapCut]

noncomputable def complexCutValue (z : ComplexBits B) : B :=
  properCutValue z.re ⊓ properCutValue z.im

theorem le_complexCutValue_iff (p : B) (z : ComplexBits B) :
    p ≤ complexCutValue z ↔ z.CutOn p := by
  simp only [complexCutValue, le_inf_iff, le_properCutValue_iff, ComplexBits.CutOn]

theorem map_complexCutValue (F : CompleteValueMap B C) (z : ComplexBits B) :
    F.toFun (complexCutValue z) = complexCutValue (z.map F) := by
  simp only [complexCutValue, F.map_inf, map_properCutValue, ComplexBits.map]

noncomputable def coeffValue (l : List (ComplexBits B)) : B :=
  l.foldr (fun c r => complexCutValue c ⊓ r) ⊤

theorem le_coeffValue_iff (p : B) (l : List (ComplexBits B)) :
    p ≤ coeffValue l ↔ ∀ c ∈ l, c.CutOn p := by
  induction l with
  | nil =>
    change p ≤ ⊤ ↔ ∀ c ∈ ([] : List (ComplexBits B)), c.CutOn p
    simp
  | cons a t ih =>
    change p ≤ complexCutValue a ⊓ coeffValue t ↔ _
    rw [le_inf_iff, le_complexCutValue_iff, ih]
    constructor
    · rintro ⟨ha,ht⟩ c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ha
      · exact ht c hc
    · intro h
      exact ⟨h a List.mem_cons_self, fun c hc => h c (List.mem_cons_of_mem _ hc)⟩

theorem map_coeffValue (F : CompleteValueMap B C) (l : List (ComplexBits B)) :
    F.toFun (coeffValue l) = coeffValue (l.map (ComplexBits.map F)) := by
  induction l with
  | nil => exact F.map_top
  | cons a t ih =>
    change F.toFun (complexCutValue a ⊓ coeffValue t) =
      complexCutValue (a.map F) ⊓ coeffValue (t.map (ComplexBits.map F))
    rw [F.map_inf, map_complexCutValue, ih]

noncomputable def polyValid (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J) : B :=
  coeffValue p.coeff ⊓ paletteValue site H p

theorem map_polyValid (F : CompleteValueMap B C) (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : PolyTrace B J) :
    F.toFun (polyValid site H p) =
      polyValid (fun z => (site z).map F) (fun z n => (H z n).map F) (p.map F) := by
  simp only [polyValid, F.map_inf, map_coeffValue, map_paletteValue, PolyTrace.map]

end JSP000930.Negative
