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

    Definition partial_sub (op_add: T -> T -> T) (op_sub: T -> T -> T) :=
      forall x y, op_sub (op_add x y) x = y.
    
    Structure ccm :=
      CanLaw {
          can_add_operator: com_law idm;
          can_sub_operator: T -> T -> T;
          _ : cancellative can_add_operator;
          _ : partial_sub can_add_operator can_sub_operator;
        }.

    Local Coercion can_add_operator : ccm >-> com_law.

    Let op_id (op1 op2 : T -> T -> T) := phant_id op1 op2.
    
    Definition clone_ccm op :=
      fun (opL : com_law idm) (opC : ccm) & op_id opL op & op_id opC op =>
        fun opmC (opC' := @CanLaw opL opmC) & phant_id opC' opC => opC'.
    
  End Definitions.


  Module Import Exports.
    Coercion can_add_operator : ccm >-> com_law.
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

      Lemma canmPInv : partial_sub can (can_sub_operator can).
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

  Lemma addnCPsub : partial_sub addn subn.
  Proof.
    move=> x y.
    rewrite addKn.
    exact.
  Qed.
   
  Canonical addn_ccm := CanLaw addn_comoid addnCC addnCPsub.
  
End PervasiveCCMs.

Export CCM.
