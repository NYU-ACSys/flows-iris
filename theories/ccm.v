From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype choice tuple finfun bigop finset.

Set Implicit Arguments.

(** Commutative Cancellative Monoids *)
Module CCM.
  Import Monoid.
  Import Exports.
  
  Section Definitions.
    Variables (T : Type) (idm: T).
        
    Definition cancellative (op: T -> T -> T) :=
      forall x y z, op x y = op x z -> y = z.

    Definition partial_inverse (op: T -> T -> T) (op_inv: T -> T -> T) :=
      forall x y, op_inv (op x y) x = y.
    
    Structure ccm :=
      CanLaw {
          can_operator: com_law idm;
          can_operator_inv: T -> T -> T;
          _ : cancellative can_operator;
          _ : partial_inverse can_operator can_operator_inv;
        }.

    Local Coercion can_operator : ccm >-> com_law.

    Let op_id (op1 op2 : T -> T -> T) := phant_id op1 op2.
    
    Definition clone_ccm op :=
      fun (opL : com_law idm) (opC : ccm) & op_id opL op & op_id opC op =>
        fun opmC (opC' := @CanLaw opL opmC) & phant_id opC' opC => opC'.
    
  End Definitions.


  Module Import Exports.
    Coercion can_operator : ccm >-> com_law.
    Notation "[ 'ccm' 'of' f ]" :=
      (@clone_ccm _ _ f _ _ id id _ id)
        (at level 0, format "[ 'ccm' 'of' f ]") : form_scope.
  End Exports.

  Module Theory.
  
    Section Theory.
      Variables (T : Type) (idm : T).
      Variable can : ccm idm.

      Lemma canmC : cancellative can.
      Proof. by case can. Qed.

      Lemma canmPInv : partial_inverse can (can_operator_inv can).
      Proof. by case can. Qed.

    End Theory.

  End Theory.

  Include Theory.
  
End CCM.
Export CCM.Exports.

Section PervasiveCCMs.
  Import CCM.

  Lemma addnCC : cancellative addn.
  Proof.
    move=> x y z /eqnP.
    rewrite eqnE.
    rewrite eqn_add2l.
    move=> H.
    apply /eqnP.
    rewrite eqnE.
    exact.
  Qed.

  Lemma addnCPinv : partial_inverse addn subn.
  Proof.
    move=> x y.
    rewrite addnC.
    pose (leqnn x).
    rewrite <-addnBA.
    pose (subn_eq0 x x).
    apply Coq.Bool.Bool.eq_bool_prop_elim in e.
    apply iff_and in e.
    elim e.
    intro h1.
    intro h2.
    rewrite i in h2.
    unfold Bool.Is_true in h2.
    pose (h3 := h2 I).
    simpl h3.
    rewrite <-eqnE in h3.
    admit.
    - exact.
  Admitted.
  
  Canonical addn_ccm := CanLaw addn_comoid addnCC addnCPinv.
  
End PervasiveCCMs.

Export CCM.
