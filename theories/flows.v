Require Import util ccm.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype choice tuple finfun bigop finset.

Set Implicit Arguments.

(** Flow graphs *)
Module FlowGraph.
  Section Definitions.
    Variable M : Type.

    Variable idx : M.
    Local Notation "0" := idx.

    Variable op : CCM.ccm 0.

    Local Notation "+%M" := op (at level 0).
    Local Notation "x + y" := (op x y).
    Local Notation "x - y" := (CCM.can_operator_inv op x y).
    

    Definition E := M -> M.
    
    Variable N : choiceType.

    Notation "x |> f" := (f x) (at level 60, right associativity, only parsing).
    
    Structure graph :=
      Graph {
          nodes: seq N;
          edges: N -> N -> E;
          flow: N -> M;
        }.

    Definition inflow G n :=
      flow G n - \big[+%M/0]_(n' <- nodes G) (flow G n' |> edges G n' n).
      
    Definition disjoint H1 H2 := uniq (nodes H1 ++ nodes H2).

    Definition flowEqn G :=
      forall n, n \in nodes G -> flow G n = inflow G n + \big[+%M/0]_(n' <- nodes G) (flow G n' |> edges G n' n).
                      
    Structure flowGraph :=
      FlowGraph {
          fgraph: graph;
          _ : flowEqn fgraph;
        }.

    Coercion fgraph : flowGraph >-> graph.
      
    Definition fgAlg := option flowGraph.
    
    Definition fcomp (A : Type) (s1 : seq N) (f1 : N -> A) (s2 : seq N) (f2 : N -> A) (z : A) :=
      fun n : N =>
        if n \in s1 then f1 n
        else if n \in s2 then f2 n
             else z.
    
    Definition gcomp (G1 G2 : graph) : option graph :=
      if disjoint G1 G2 then
        let nodes1 := nodes G1 in
        let nodes2 := nodes G2 in
        let nodes12 := nodes G1 ++ nodes G2 in
        let flow12 := fcomp nodes1 (flow G1) nodes2 (flow G2) 0 in
        let edges12 := fcomp nodes1 (edges G1) nodes2 (edges G2) (fun _ _ => 0) in
        let G12 := Graph nodes12 edges12 flow12 in
        Some G12
      else None.

    Lemma gcomp_flowEqn (G1 G2 G12 : graph) :
      Some G12 = gcomp G1 G2 -> flowEqn G12.
    Proof.
    Admitted.

    
    (* Definition fcomp (H1o : fgAlg) (H2o : fgAlg) : fgAlg :=
      do H1 <- H1o ;
        do H2 <- H2o ;
        do G12 <- gcomp H1 H2 ;
        FlowGraph (gcomp_flowEqn H1 H2 G12) G12.*)
        
  End Definitions.
End FlowGraph.
