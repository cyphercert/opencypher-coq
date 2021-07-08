Require Import String.
From hahn Require Import Hahn.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Aux.
Variable T : eqType.

Fixpoint list_eqb (l l' : list T) : bool :=
  match l, l' with
  | [], [] => true
  | a::l, b::l' =>
    eq_op a b && (list_eqb l l')
  | _, _ => false
  end.

Lemma list_eqP : Equality.axiom list_eqb.
Proof using T.
  red. induction x.
  { ins. destruct y; constructor; desf. }
  ins. desf.
  { constructor. desf. }
  destruct (eq_op a s) eqn:HH; subst; ins.
  2: { constructor. intros AA. inv AA. rewrite beq_refl in HH. inv HH. }
  specialize (IHx l).
  apply Bool.reflect_iff in IHx.
  apply Bool.iff_reflect.
  etransitivity; eauto.
  split; intros AA; desf.
  apply hahn__beq_rewrite in HH. desf.
Qed.

Canonical Structure list_eqMixin := EqMixin list_eqP.
Canonical Structure list_eqType := Eval hnf in EqType (list T) list_eqMixin.

Fixpoint list_inb {T : eqType} x (l : list T) : bool :=
  match l with
  | [] => false
  | a::l => eq_op x a || list_inb x l
  end.
End Aux.

Definition vertex    := nat.
Definition edge      := nat.
Definition label     := string.
Definition attribute := string.

Module Attribute.
  Definition t := string.
  
  Definition eqb (s s' : t) := String.eqb s s'.

  Lemma eqP : Equality.axiom eqb.
  Proof. unfold eqb. red. apply eqb_spec. Qed.
End Attribute.

Canonical Structure attribute_eqMixin := EqMixin Attribute.eqP.
Canonical Structure attribute_eqType := Eval hnf in EqType Attribute.t attribute_eqMixin.

Module Scheme.
  Definition t := list Attribute.t.
  
  Definition eqb (s s' : t) : bool := list_eqb _ s s'.

  Lemma eqP : Equality.axiom eqb.
  Proof. apply list_eqP. Qed.
End Scheme.

Canonical Structure scheme_eqMixin := EqMixin Scheme.eqP.
Canonical Structure scheme_eqType := Eval hnf in EqType Scheme.t scheme_eqMixin.

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

Canonical Structure property_eqMixin := EqMixin Property.eqP.
Canonical Structure property_eqType := Eval hnf in EqType Property.t property_eqMixin.

Module Relation.
  Record t :=
    mk { (* sch *)
        scheme : Scheme.t;
        data   : list (list Property.t);
      }.
  
  Record wf (r : Relation.t) :=
    { scheme_len : forall l (IN : List.In l (data r)),
        List.length l = List.length (scheme r);
    }.

  Definition bag_union r r' : option t :=
    if Scheme.eqb (scheme r) (scheme r')
    then Some (mk (scheme r) 
                  (app (data r) (data r')))
    else None.

  Definition union r r' : option t :=
    if Scheme.eqb (scheme r) (scheme r')
    then Some (mk (scheme r) 
                  (app (data r)
                       (filter
                          (fun l => negb (list_inb l (data r)))
                          (data r'))))
    else None.
  
  (* Definition natural_join r r' : option t := *)
  (*   None *)
End Relation.

Module PropertyGraph.
  Record t :=
    mk { (* V *)
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



Module Pattern.
  Inductive direction := 
  | OUT
  | IN
  | BOTH
  .

  Inductive t :=
  | vertex     (vname : attribute) (vlabels : list label)

  | edge       (pattern : t) 
               (ename : attribute) (etype : label) (edirection : direction) 
               (wname : attribute) (wlabels : list label)

  | multiedge  (pattern : t) 
               (enames : list attribute) (etype : label) (low : nat) (up : nat) 
               (vnames : list attribute) (wname : attribute) (vlabels : list label)
  .
End Pattern.

Module Query.
  Inductive sorting_order :=
  | ASC
  | DESC
  .
  (* MATCH .. 
     MATCH ..
     RETURN ...... *)
  (*Match (Where ())*)
  Inductive t :=
  | MATCH           (patterns : list Pattern.t)
  | OPTIONAL_MATCH  (query : option t) (pattern : Pattern.t)
  | WHERE           (query : t) (pattern : Pattern.t)
  | WHERE_NOT       (query : t) (pattern : Pattern.t)
  | RETURN          (query : t) (anames : list (attribute * attribute))
  | RETURN_DISTINCT (query : t) (anames : list (attribute * attribute))
  .
End Query.

Module RelationOperation. 
  Inductive t :=
  (*Maybe we need other shema.*)
  | relation                (*(relation : Relation.t)*)
  | select_vertices         (aname : attribute) (vlabels : list label) (vrelation : t)
  | select_edges            (aname : attribute) (etype : label) (erelation : t)
  | projection              (anames : list (attribute * attribute)) (relation : t)
  | eq_join                 (relation1 : t) (aname1 : attribute) (relation2 : t) (aname2 : attribute)
  | natural_join            (relation1 : t) (relation2 : t)
  | left_outer_join         (relation1 : t) (relation2 : t)
  | semijoin                (relation1 : t) (relation2 : t)
  | anti_semijoin           (relation1 : t) (relation2 : t)
  | transitive_natural_join (relation1 : t) (relation2 : t) (low : nat) (up : nat)
  | all_different           (relation : t)
  .
End RelationOperation.

Definition graph_to_vertices_relation (graph : PropertyGraph.t) : RelationOperation.t := RelationOperation.relation.
Definition graph_to_edges_relation (graph : PropertyGraph.t) : RelationOperation.t := RelationOperation.relation.

Fixpoint compute_pattern (pattern : Pattern.t) (graph : PropertyGraph.t) : RelationOperation.t :=
  match pattern with
  | Pattern.vertex vname vlabels => GraphRelationOperation.get_vertices vname vlabels graph
  | Pattern.edge pattern ename etype edirection wname wlabels => GraphRelationOperation.get_edges pattern ename etype edirection wname wlabels graph
  | Pattern.multiedge pattern enames etype low up vnames wname vlabels => GraphRelationOperation.transitive_get_edges pattern enames etype low up vnames wname vlabels graph
  end.

Fixpoint compute_query (query : Query.t) (graph : PropertyGraph.t) : RelationOperation.t :=
  match query with
  | MATCH patterns => match patterns with
                      | [] => (*Empty relation*)
                      | head :: tail => RelationOperation.natural_join (compute_pattern head graph) (compute_query (MATCH tail) graph)
                      .
  | OPTIONAL_MATCH query' pattern => RelationOperation.left_outer_join (compute_query query' graph) (compute_pattern pattern graph)
  | WHERE query' pattern => match pattern with
                            | vertex vname vlabels => RelationOperation.select_vertices vname vlabels (compute_query query' graph)
                            | _ => RelationOperation.semijoin (compute_query query' graph) (compute_pattern pattern graph)
                            .
  | WHERE_NOT query' pattern => RelationOperation.anti_semijoin (compute_query query' graph) (compute_pattern pattern graph)
  | RETURN query' anames => RelationOperation.projection anames (compute_query query' graph)
  | RETURN_DISTINCT query' anames => all_different (projection anames (compute_query query' graph))
  end.

Module GraphRelationOperation.
  Definition get_vertices (vname : attribute) (vlabels : list label) 
                          (graph : PropertyGraph.t) : RelationOperation.t :=
    RelationOperation.projection [(vname, vname)] (RelationOperation.select_vertices vname vlabels (graph_to_vertices_relation graph)).
  
  Fixpoint get_edges (pattern : Pattern.t) 
                     (ename : attribute) (etype : label) (edirection : Pattern.direction) 
                     (wname : attribute) (wlabels : list label) 
                     (graph : PropertyGraph.t) : RelationOperation.t := 
    match pattern with 
    | Pattern.vertex vname vlabels => 
      RelationOperation.natural_join (compute_pattern pattern graph) 
                                     (RelationOperation.eq_join (RelationOperation.eq_join (get_vertices vname vlabels graph) 
                                                                                           "id" 
                                                                                           (RelationOperation.select_edges ename 
                                                                                                                           etype
                                                                                                                           (graph_to_edges_relation graph)) 
                                                                                           "src") 
                                                                "trg" 
                                                                (get_vertices wname wlabels graph) 
                                                                "id")

    | Pattern.edge pattern' ename' etype' edirection' wname' wlabels' =>
      RelationOperation.natural_join (compute_pattern pattern graph) 
                                     (RelationOperation.eq_join (RelationOperation.eq_join (get_vertices wname' wlabels' graph) 
                                                                                           "id" 
                                                                                           (RelationOperation.select_edges ename 
                                                                                                                           etype
                                                                                                                           (graph_to_edges_relation graph)) 
                                                                                           "src") 
                                                                "trg" 
                                                                (get_vertices wname wlabels graph) 
                                                                "id")

    | Pattern.multiedge pattern' enames etype' low up vnames wname' vlabels => 
      RelationOperation.natural_join (compute_pattern pattern graph) 
                                     (RelationOperation.eq_join (RelationOperation.eq_join (get_vertices wname' vlabels graph) 
                                                                                           "id" 
                                                                                           (RelationOperation.select_edges ename 
                                                                                                                           etype
                                                                                                                           (graph_to_edges_relation graph)) 
                                                                                           "src") 
                                                                "trg" 
                                                                (get_vertices wname wlabels graph) 
                                                                "id")
    end.

  (*ENAME ???*)
  Fixpoint transitive_get_edges (pattern : Pattern.t) 
                                (enames : list attribute) (etype : label) (low : nat) (up : nat) 
                                (vnames : list attribute) (wname : attribute) (vlabels : list label) 
                                (graph : PropertyGraph.t) : RelationOperation.t :=
    match p with 
    | Pattern.vertex vname vlabels' => 
    RelationOperation.natural_join
    (RelationOperation.transitive_natural_join
       (compute_pattern pattern graph) 
       (RelationOperation.eq_join
          (RelationOperation.eq_join
             (get_vertices vname vlabels' graph) "id" 
             (RelationOperation.select_edges ename etype (graph_to_edges_relation graph)) 
             "src") 
          "trg" 
          (get_vertices wname vlabels graph)
          "id") 
       low up) 
    (get_vertices wname vlabels graph)

    | Pattern.edge pattern' ename etype' edirection' wname' wlabels =>
      RelationOperation.natural_join 
      (RelationOperation.transitive_natural_join 
        (compute_pattern pattern graph) 
        (RelationOperation.eq_join (RelationOperation.eq_join (get_vertices wname' wlabels graph) 
                                                                                                                                      "id" 
                                                                                                                                      (RelationOperation.select_edges ename 
                                                                                                                                                                      etype 
                                                                                                                                                                      (graph_to_edges_relation graph)) 
                                                                                                                                      "src")
                                                                                                           "trg" 
                                                                                                           (get_vertices wname vlabels graph) 
                                                                                                           "id") 
                                                                                low 
                                                                                up) 
                                     (get_vertices wname vlabels graph)

    | Pattern.multiedge pattern' enames' etype' low' up' vnames' wname' vlabels' => 
      RelationOperation.natural_join (RelationOperation.transitive_natural_join (compute_pattern pattern) 
                                                                                (RelationOperation.eq_join (RelationOperation.eq_join (get_vertices wname' vlabels' graph) 
                                                                                                                                      "id" 
                                                                                                                                      (RelationOperation.select_edges ename etype (graph_to_edges_relation graph)) 
                                                                                                                                      "src") 
                                                                                                           "trg" 
                                                                                                           (get_vertices wname vlabels graph) 
                                                                                                           "id") 
                                                                                low 
                                                                                up) 
                                     (get_vertices wname vlabels graph)
    end.
End GraphRelationOperation.
