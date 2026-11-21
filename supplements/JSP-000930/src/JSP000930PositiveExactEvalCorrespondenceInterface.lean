import JSP000930PositiveNativeDataForLiteralFamilyMember

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure LiteralTaylorEvalCorrespondence (B : Type) [NontrivialCompleteBooleanAlgebra B] : Prop where
  agrees : ∀ {n : ℕ} (v : DVec (V B) n) (A Z Y : STerm n)
    (z : ComplexBits B) (p : B),
    bTerm v Z = z.name →
    z.CutOn p →
    p ≤ bTruth v (isEntireCode_f A) →
    (p ≤ bTruth v (evalAt_f A Z Y) ↔
      p ≤ bTerm v Y =ᴮ (taylorLimitBits (sequenceBits (bTerm v A)) z).name)

theorem force_complex_at_eq_of_native_name {n : ℕ} (v : DVec (V B) n)
    (y : bSet B) (u : ComplexBits B) (p : B)
    (hu : u.CutOn p) (hY : p ≤ y =ᴮ u.name) :
    p ≤ bTruth (DVec.cons y v) (complex_f (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  let Y : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let f : SForm (n+1) := complex_f Y
  have hv : p ≤ bTruth (DVec.cons u.name v) f :=
    weighted_complexName_forces_complex _ Y u p (bTerm_current_r181 v u.name) hu
  have h := bTruth_body_ext_r191 v f u.name y
  exact (le_inf (bv_symm hY) hv).trans h

theorem valueCertificate_iff_native_eval {n : ℕ}
    (E : LiteralTaylorEvalCorrespondence B) (v : DVec (V B) n)
    (z : ComplexBits B) (W a y : bSet B) (p : B)
    (hz : z.CutOn p)
    (hEntire : let w := DVec.cons a (DVec.cons y (DVec.cons W (DVec.cons z.name v)))
      p ≤ bTruth w (isEntireCode_f (bd_var ⟨0,Nat.succ_pos (n+3)⟩)))
    (ha : ∀ i,(sequenceBits a i).CutOn p)
    (hg : GrowthOn p (sequenceBits a)) :
    p ≤ valueCertificate v z.name W a y ↔
      p ≤ y =ᴮ (taylorLimitBits (sequenceBits a) z).name := by
  let vZ : DVec (V B) (n+1) := DVec.cons z.name v
  let vW : DVec (V B) (n+2) := DVec.cons W vZ
  let vY : DVec (V B) (n+3) := DVec.cons y vW
  let vA : DVec (V B) (n+4) := DVec.cons a vY
  let TZ : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let TY : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let TA : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  have hZ : bTerm vA (up2 (up TZ)) = z.name := by
    exact (bTerm_up2_r181 vW y a (up TZ)).trans
      ((bTerm_up_r181 vZ W TZ).trans (bTerm_current_r181 v z.name))
  have hY : bTerm vA (up TY) = y := by
    exact (bTerm_up_r181 vY a TY).trans (bTerm_current_r181 vW y)
  have hA : bTerm vA TA = a := bTerm_current_r181 vY a
  have hLit := E.agrees vA TA (up2 (up TZ)) (up TY) z p hZ hz hEntire
  rw [hA,hY] at hLit
  change p ≤ bTruth vY (complex_f TY) ⊓ bTruth vA (evalAt_f TA (up2 (up TZ)) (up TY)) ↔ _
  constructor
  · intro h
    exact hLit.1 (h.trans inf_le_right)
  · intro hy
    exact le_inf (force_complex_at_eq_of_native_name vW y (taylorLimitBits (sequenceBits a) z) p
      (taylorLimitBits_cutOn (sequenceBits a) z p ha hz hg) hy) (hLit.2 hy)

end JSP000930.Positive
