import JSP000930AnalyticComplexRecursion

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def ComplexBits.power (z : ComplexBits B) : ℕ → ComplexBits B
  | 0 => ComplexBits.ofNat 1
  | n+1 => (z.power n).mul z

theorem ComplexBits.power_cutOn {z : ComplexBits B} {p : B} (hz : z.CutOn p)
    (n : ℕ) : (z.power n).CutOn p := by
  induction n with
  | zero => exact ComplexBits.ofNat_cutOn 1 p
  | succ n ih => exact ComplexBits.mul_cutOn ih hz

noncomputable def taylorPrefixBits (a : ℕ → ComplexBits B) (z : ComplexBits B) :
    ℕ → ComplexBits B
  | 0 => ComplexBits.ofNat 0
  | n+1 => (taylorPrefixBits a z n).add ((a n).mul (z.power n))

theorem taylorPrefixBits_cutOn {a : ℕ → ComplexBits B} {z : ComplexBits B} {p : B}
    (hz : z.CutOn p) {m : ℕ} (ha : ∀ n < m, (a n).CutOn p) :
    ∀ n ≤ m, (taylorPrefixBits a z n).CutOn p := by
  intro n hn
  induction n with
  | zero => exact ComplexBits.ofNat_cutOn 0 p
  | succ n ih =>
    exact ComplexBits.add_cutOn (ih (Nat.le_of_succ_le hn))
      (ComplexBits.mul_cutOn (ha n (Nat.lt_of_succ_le hn)) (ComplexBits.power_cutOn hz n))

end JSP000930.BooleanAnalysis

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem forces_of_inf_eq_eqname {p t : B} {a : bSet B}
    (h : p ⊓ t = p ⊓ (a =ᴮ a)) : p ≤ t := by
  exact (le_inf le_rfl (le_top.trans bSet.bv_refl)).trans (h.symm.le.trans inf_le_right)

theorem forces_complexPow_weighted {n : ℕ} (v : DVec (V B) n)
    (Z M W : STerm n) (z : ComplexBits B) (m : ℕ) (p : B)
    (hZ : bTerm v Z = z.name) (hM : bTerm v M = bSet.of_nat m)
    (hW : bTerm v W = (z.power m).name) (hz : z.CutOn p) :
    p ≤ bTruth v (complexPow_f Z M W) := by
  let One : bSet B := bSet.of_nat 1
  let Base := (ComplexBits.ofNat (B := B) 1).name
  let v1 : DVec (V B) (n+1) := DVec.cons One v
  let v2 : DVec (V B) (n+2) := DVec.cons Base v1
  let U : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let S : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  unfold complexPow_f
  rw [bTruth_exOmega_r192]
  apply le_iSup_of_le 1
  rw [bTruth_and_eq]
  apply le_inf
  · rw [bTruth_successor_twoChecked_r192 v1 zero U 0 1
      (bTerm_zero_checked_r192 v1) (bTerm_current_r181 v One)]
    simp [crispTruth]
  · rw [bTruth_sEx_r181]
    apply le_iSup_of_le Base
    rw [bTruth_and_eq]
    apply le_inf
    · apply forces_of_inf_eq_eqname
      exact bTruth_complexNat_weighted v2 (up U) S (ComplexBits.ofNat 1) 1 p
        ((bTerm_up_r181 v1 Base U).trans (bTerm_current_r181 v One))
        (bTerm_current_r181 v1 Base) (ComplexBits.ofNat_cutOn 1 p)
    · apply forces_complexRecursion_graph v2 (up2 M) S (up2 W)
        (fun _ : Fin 1 => up2 Z) (fun prm _ cur next => complexMul_f cur (prm 0) next)
        m z.power p (fun _ => z.name)
      · exact (bTerm_up2_r181 v One Base M).trans hM
      · exact bTerm_current_r181 v1 Base
      · exact (bTerm_up2_r181 v One Base W).trans hW
      · intro j
        exact (bTerm_up2_r181 v One Base Z).trans hZ
      · intro j _
        exact ComplexBits.power_cutOn hz j
      · intro d w prm I C N i hi hprm hI hC hN
        apply forces_of_inf_eq_eqname
        exact bTruth_complexMul_weighted w C (prm 0) N (z.power i) z (z.power (i+1)) p hC
          (hprm 0) hN (ComplexBits.power_cutOn hz i) hz (ComplexBits.power_cutOn hz (i+1))

end JSP000930.AnalyticSyntax
