From hahn Require Import Hahn.
Require Import String.

Definition vertex    := nat.
Definition edge      := nat.
Definition label     := string.
Definition attribute := string.

Module Property.
  Inductive t := 
  | p_int (i : nat)
  | p_string (s : string)
  | p_empty
  .
  
  Definition name := string.
End Property.

Module Relation.

Record t :=
  { (* sch *)
    scheme : list attribute;
    data   : list (list Property.t);
  }.

Record wf (r : Relation.t) :=
  { scheme_len : forall l (IN : In l (data r)),
      List.length l = List.length (scheme r);
  }.

End Relation.

Module PropertyGraph.
  
Record t :=
  { (* V *)
    vertices : list vertex;
    (* E *)
    edges    : list edge;
    (* st *)
    st       : edge -> vertex * vertex;

    (* \mathcal{L}*)
    vlab     : list (vertex * label);
    (* \mathcal{T}*)
    elab     : edge -> label;
    
    (* Pᵥ *)
    vprop    : list (Property.name * (vertex -> Property.t)); 
    (* Pₑ *)
    eprop    : list (Property.name * (edge   -> Property.t)); 
  }.

End PropertyGraph.
