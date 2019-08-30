Module Util.
  Definition ret {A : Type} (x : A) := Some x.
  
  Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
    match a with
    | Some x => f x
    | None => None
    end.

  Notation "'do' X_0 <- A_0 ; B" :=
    (bind A_0 (fun X_0 => B)) (at level 200, X_0 ident, A_0 at level 100, B at level 200).
    (*Notation "'do' X_0 <- A_0 ; X_1 <- A_1 ; .. ; X_n <- A_n ; B" :=
      (bind A_0 (fun X_0 => bind A_1 (fun X_1 => .. bind A_n (fun X_n => B) .. ))) (at level 200). (*,  X ident, A at level 100, B at level 200).*)*)
End Util.

Export Util.

