From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.

Set Implicit Arguments.

(** Commutative Cancellative Monoids *)
Module CCM.
  Import Monoid.
  Import Exports.
  
  Section Definitions.
    Variables (T : Type) (idm: T).
        
    Definition cancellative (op: T -> T -> T) :=
      forall x y z, op x y = op x z -> y = z.

    Structure ccm :=
      CanLaw {
          can_operator: com_law idm;
          _ : cancellative can_operator;
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

    End Theory.

  End Theory.

  Include Theory.
  
End CCM.
Export CCM.Exports.

Section PervasiveCCMs.
  Import CCM.

  Lemma addnCC : cancellative addn.
  Proof.
    move=> x y z /= /eqnP.
    rewrite /= eqnE.
    rewrite [_ == _] eqn_add2l.
    move=> H.
    apply/eqnP.
    rewrite eqnE.
    exact.
  Qed.

  Canonical addn_ccm := CanLaw addn_comoid addnCC.
  
End PervasiveCCMs.

(** Flow graphs *)
Module FlowGraph.

End FlowGraph.
