Require Import String.
From hahn Require Import Hahn.

Module Property.
  Inductive t := 
  | p_int (i : nat)
  | p_string (s : string)
  | p_empty
  .
  
  Definition name := string.
  
  Definition eqb (p p' : t) : bool :=
    match p, p' with
    | p_int i, p_int i' => Nat.eqb i i'
    | p_string s, p_string s' => String.eqb s s'
    | p_empty, p_empty => true
    | _, _ => false
    end.

  Lemma eqP : Equality.axiom eqb.
  Proof.
    unfold eqb. red. ins. desf; try constructor; desf.
    all: apply Bool.iff_reflect.
    all: symmetry; etransitivity.
    all: try apply PeanoNat.Nat.eqb_eq; try apply String.eqb_eq.
    all: split; intros AA; subst; auto.
    all: inv AA.
  Qed.
End Property.

Module PropertyGraph.
  Definition vertex    := nat.
  Definition edge      := nat.
  Definition label     := string.

  Record t :=
    mk { vertices : list vertex;
         edges    : list edge;
         st       : edge -> vertex * vertex;
         vlab     : vertex -> list label;
         elab     : edge -> label;
         vprops   : list (Property.name * (vertex -> Property.t)); 
         eprops   : list (Property.name * (edge   -> Property.t)); 
      }.
End PropertyGraph.

Fixpoint get_vertex_properties (v : vertex) (vprops : list (Property.name * (vertex -> Property.t))) : 
  list (Property.name * Property.t) :=
  match vprops with
  | [] => []
  | head :: tail => app [(fst head) * ((snd head) v)] [get_vertex_properties v tail]
  end.
(*If we can use "v" in map:
fun get_vertex_properties (p : Property.name * (vertex -> Property.t)) : Property.name * Property.t := (fst p) * ((snd p) v).*)
fun get_vertex_info (v : PropertyGraph.vertex) : data := drec [("id", v) ; ("vertex", mk v (vlab v) (get_vertex_properties v))].
(*Here we use "get_vertex_info" as Variable "f" for mapping.*)
Definition graph_to_vertices_relation (graph : PropertyGraph.t) : data := dcol (map graph.(vertices)).

Fixpoint get_edge_properties (e : edge) (eprops : list (Property.name * (edge -> Property.t))) : 
  list (Property.name * Property.t) :=
  match eprops with
  | [] => []
  | head :: tail => app [(fst head) * ((snd head) e)] [get_edge_properties e tail]
  end.
fun get_edge_info (e : PropertyGraph.edge) : data := drec [("id", e) ; ("edge", mk e (elab e) (get_edge_properties e))].
Definition graph_to_edges_relation (graph : PropertyGraph.t) : data := dcol (map graph.(edges)).