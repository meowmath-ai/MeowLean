import JSP000933GroundSubsetNames
import JSP000933GenericCouplingValue

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace PositiveForcing

open CantorCodes BooleanNames BooleanCompletion Erdos1123

variable {W V : WeightSequence ℕ}

abbrev CouplingBA (W V : WeightSequence ℕ) := RO (CouplingCondition W V)

def fromPositive (S : Set ℕ) : Set ℕ := Nat.succ ⁻¹' S

def toPositive (S : Set ℕ) : Set ℕ := Nat.succ '' S

@[simp] theorem from_toPositive_r187 (S : Set ℕ) : fromPositive (toPositive S) = S := by
  ext n
  change n.succ ∈ Nat.succ '' S ↔ n ∈ S
  constructor
  · rintro ⟨m,hm,he⟩
    exact (Nat.succ.inj he) ▸ hm
  · exact fun h => ⟨n,h,rfl⟩

noncomputable def genericCouplingPair (W V : WeightSequence ℕ) (a : Set ℕ × Set ℕ) :
    bSet (CouplingBA W V) :=
  bSet.pair (groundSubsetName _ (fromPositive a.1)) (groundSubsetName _ (fromPositive a.2))

noncomputable def genericCouplingGraph (W V : WeightSequence ℕ) : bSet (CouplingBA W V) :=
  familyName (genericCouplingPair W V) (pairValue (W := W) (V := V))

section Scope

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def graphPairsOnlyValue (G : bSet B) : B :=
  ⨅ u : bSet B, imp (u ∈ᴮ G)
    (⨆ a : bSet B, (a ⊆ᴮ bSet.omega) ⊓
      (⨆ b : bSet B, (b ⊆ᴮ bSet.omega) ⊓ (bSet.pair a b =ᴮ u)))

def orderedPairSide (s : Bool) (a b : bSet B) : bSet B :=
  if s then bSet.pair b a else bSet.pair a b

noncomputable def graphTotalSideValue (G : bSet B) (s : Bool) : B :=
  ⨅ a : bSet B, imp (a ⊆ᴮ bSet.omega) (⨆ b : bSet B,
    (b ⊆ᴮ bSet.omega) ⊓ (orderedPairSide s a b ∈ᴮ G))

end Scope

theorem generic_graph_pairsOnly_r187 (W V : WeightSequence ℕ) :
    (⊤ : CouplingBA W V) ≤ graphPairsOnlyValue (genericCouplingGraph W V) := by
  apply le_iInf
  intro u
  rw [← _root_.deduction,top_inf_eq]
  change (u ∈ᴮ familyName (genericCouplingPair W V) (pairValue (W := W) (V := V))) ≤ _
  rw [mem_familyName_r70]
  apply iSup_le
  intro a
  apply le_iSup_of_le (groundSubsetName (CouplingBA W V) (fromPositive a.1))
  refine le_inf (le_top.trans (realBitsName_subset_r103 _)) ?_
  apply le_iSup_of_le (groundSubsetName (CouplingBA W V) (fromPositive a.2))
  exact le_inf (le_top.trans (realBitsName_subset_r103 _)) (inf_le_right.trans_eq bSet.bv_eq_symm)

theorem pairValue_canonicalSide_r187 (W V : WeightSequence ℕ) (s : Bool) (a b : Set ℕ) :
    pairValue (W := W) (V := V)
      (if s then (b,toPositive a) else (toPositive a,b)) ≤
      orderedPairSide s (groundSubsetName (CouplingBA W V) a)
        (groundSubsetName (CouplingBA W V) (fromPositive b)) ∈ᴮ genericCouplingGraph W V := by
  cases s
  · simpa only [orderedPairSide,genericCouplingPair,from_toPositive_r187,
      Bool.false_eq_true,ite_false,ite_true,genericCouplingGraph,familyName]
      using bSet.mem_mk (genericCouplingPair W V) (pairValue (W := W) (V := V)) (toPositive a,b)
  · simpa only [orderedPairSide,genericCouplingPair,from_toPositive_r187,
      Bool.false_eq_true,ite_false,ite_true,genericCouplingGraph,familyName]
      using bSet.mem_mk (genericCouplingPair W V) (pairValue (W := W) (V := V)) (b,toPositive a)

theorem orderedPairSide_congr_first_r187 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (s : Bool) {a a' b : bSet B} {p : B} (h : p ≤ a =ᴮ a') :
    p ≤ orderedPairSide s a b =ᴮ orderedPairSide s a' b := by
  cases s
  · exact bSet.pair_congr h (bSet.bv_refl (x := b))
  · exact bSet.pair_congr (bSet.bv_refl (x := b)) h

theorem generic_graph_totalSide_r187 (hW : BlockStructure W) (hV : BlockStructure V) (s : Bool) :
    (⊤ : CouplingBA W V) ≤ graphTotalSideValue (genericCouplingGraph W V) s := by
  apply le_iInf
  intro x
  rw [← _root_.deduction,top_inf_eq]
  apply (omegaSubset_le_iSup_ground_r186 coupling_countablyClosed_r186 x).trans
  apply iSup_le
  intro a
  let B := CouplingBA W V
  let g (b : Set ℕ) : B := pairValue (W := W) (V := V)
    (if s then (b,toPositive a) else (toPositive a,b))
  have hg : (⨆ b, g b) = (⊤ : B) := by
    cases s
    · simpa [g] using pairValue_left_total_r184 hW hV (toPositive a)
    · simpa [g] using pairValue_right_total_r184 hW hV (toPositive a)
  let p := x =ᴮ groundSubsetName B a
  have hp : p ≤ p ⊓ ⨆ b, g b := by rw [hg,inf_top_eq]
  apply hp.trans
  apply Lattice.bv_cases_right
  intro b
  let y := groundSubsetName B (fromPositive b)
  apply le_iSup_of_le y
  refine le_inf (le_top.trans (realBitsName_subset_r103 _)) ?_
  have he := orderedPairSide_congr_first_r187 (b := y) s (show p ≤ x =ᴮ groundSubsetName B a from le_rfl)
  exact bSet.subst_congr_mem_left'
    ((inf_le_left.trans he).trans_eq bSet.bv_eq_symm)
    (inf_le_right.trans (pairValue_canonicalSide_r187 W V s a b))

end PositiveForcing
end JSP000933
