import JSP000933ActualQuotientPreorder

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]
variable {I : Type}

inductive SetBitExpr (I : Type)
  | var : I → SetBitExpr I
  | const : Bool → SetBitExpr I
  | meet : SetBitExpr I → SetBitExpr I → SetBitExpr I
  | neg : SetBitExpr I → SetBitExpr I

def SetBitExpr.evalProp : SetBitExpr I → (I → Prop) → Prop
  | .var i, P => P i
  | .const b, _ => b=true
  | .meet f g, P => f.evalProp P ∧ g.evalProp P
  | .neg f, P => ¬ f.evalProp P

def SetBitExpr.evalB : SetBitExpr I → (I → B) → B
  | .var i, A => A i
  | .const b, _ => truthBit b
  | .meet f g, A => f.evalB A ⊓ g.evalB A
  | .neg f, A => (f.evalB A)ᶜ

def SetBitExpr.groundSet (e : SetBitExpr I) (A : I → Set ℕ) : Set ℕ :=
  {n | e.evalProp (fun i => n∈A i)}

def SetBitExpr.namedSet (e : SetBitExpr I) (A : I → bSet B) : bSet B :=
  realBitsName (fun n => e.evalB (fun i => membershipBits (A i) n))

theorem SetBitExpr.membership_namedSet_r230 (e : SetBitExpr I) (A : I → bSet B) (n : ℕ) :
    membershipBits (e.namedSet A) n = e.evalB (fun i => membershipBits (A i) n) :=
  congrFun (membershipBits_realBitsName_r128 _) n

theorem SetBitExpr.eval_maskCongr_r230 (e : SetBitExpr I) {A C : I → B} {q : B}
    (h : ∀ i, q ⊓ A i = q ⊓ C i) :
    q ⊓ e.evalB A = q ⊓ e.evalB C := by
  induction e with
  | var i => exact h i
  | const b => rfl
  | meet a b ha hb => exact mask_inf_congr_r126 ha hb
  | neg a ha => exact mask_compl_congr_r126 ha

theorem SetBitExpr.eval_crisp_r230 (e : SetBitExpr I) (P : I → Prop) :
    e.evalB (fun i => crispTruth B (P i)) = crispTruth B (e.evalProp P) := by
  induction e with
  | var i => rfl
  | const b => cases b <;> simp [SetBitExpr.evalB,SetBitExpr.evalProp,truthBit,crispTruth]
  | meet a b ha hb => exact (congrArg₂ (· ⊓ ·) ha hb).trans (crisp_and_r190 _ _).symm
  | neg a ha => exact (congrArg (fun b : B => bᶜ) ha).trans (crisp_not_r197 _).symm

theorem SetBitExpr.named_groundBit_r230 (e : SetBitExpr I) (a : I → Set ℕ) (n : ℕ) :
    membershipBits (e.namedSet (fun i => groundSubsetName B (a i))) n =
      membershipBits (groundSubsetName B (e.groundSet a)) n := by
  rw [e.membership_namedSet_r230]
  change e.evalB (fun i => ((bSet.of_nat n : bSet B) ∈ᴮ groundSubsetName B (a i))) =
    ((bSet.of_nat n : bSet B) ∈ᴮ groundSubsetName B (e.groundSet a))
  simp only [checkedNat_ground_mem_r197,SetBitExpr.eval_crisp_r230,SetBitExpr.groundSet,Set.mem_ofPred_eq]

theorem SetBitExpr.named_maskGround_r230 (e : SetBitExpr I) (A : I → bSet B) (a : I → Set ℕ)
    (n : ℕ) (q : B)
    (h : ∀ i j, j<n →
      q ⊓ membershipBits (A i) j = q ⊓ membershipBits (groundSubsetName B (a i)) j) :
    ∀ j<n, q ⊓ membershipBits (e.namedSet A) j =
      q ⊓ membershipBits (groundSubsetName B (e.groundSet a)) j := by
  intro j hj
  rw [e.membership_namedSet_r230,← e.named_groundBit_r230 a j,e.membership_namedSet_r230]
  exact e.eval_maskCongr_r230 (fun i => h i j hj)

end SetLanguage
end JSP000933
