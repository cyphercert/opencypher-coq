From hahn Require Import Hahn.
Require Import String.

Definition vertex    := nat.
Definition edge      := nat.
Definition label     := string.
Definition property  := string.
Definition attribute := string.
Definition pindex    := nat.

Module Relation.

Record t :=
  { (* sch *)
  scheme : list attribute;
  data   : list (list (option property));
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
    vlab     : vertex -> label -> Prop;
    (* \mathcal{T}*)
    elab     : edge   -> label;
    
    (* Pᵥ *)
    vprop    : pindex -> vertex -> option property; 
    (* Pₑ *)
    eprop    : pindex -> edge   -> option property; 
  }.

End PropertyGraph.
