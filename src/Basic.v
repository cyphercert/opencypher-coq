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
  | vertex (name : string) (labels : list label)
  | edge (name : string) (types : list Property.t) (dir : direction) (p : t) (wname : string) (wlabels : list label)
  | multiedge (enames : list string) (etypes : list Property.t) (vnames : list string) (vlabels : list label) (low : nat) (up : nat)
  .
End Pattern.

Module Query.
  Inductive sorting_order :=
  | ASC
  | DESC
  .

  Inductive t :=
  | MATCH (ps : list Pattern.t)
  | OPTIONAL_MATCH (q : option t) (p : Pattern.t)
  | WHERE (q : t) (p : Pattern.t)
  | WHERE_NOT (q : t) (p : Pattern.t)
  | RETURN (q : t) (attrs : list (attribute * string))
  | RETURN_DISTINCT (q : t) (attrs : list (attribute * string))
  | ORDER_SKIP_LIMIT (q : t) (attrs : list (attribute * sorting_order)) (s : nat) (l : nat)
  .
End Query.

Module RelationOperation. 
  Inductive t :=
  | relation (r : Relation.t)
  | select_vertices (attr_name : string) (labels : list label) (vr : t)
  | select_edges (attr_name : string) (type : Property.t) (er : t)
  | projection (attrs : list (string * string)) (r : t)
  | eq_join (r1 : t) (attr1 : string) (r2 : t) (attr2 : string)
  | natural_join (r1 : t) (r2 : t)
  | left_outer_join (r1 : t) (r2 : t)
  | semijoin (r1 : t) (r2 : t)
  | anti_semijoin (r1 : t) (r2 : t)
  | all_different (r : t)
  .
End RelationOperation.

Fixpoint graph_to_vertices_relation (pg : PropertyGraph.t) := .
Fixpoint graph_to_edges_relation (pg : PropertyGraph.t) := .

Module GraphRelationOperation.
  Fixpoint get_vertices (attr_name : string) (labels : list label) (g : PropertyGraph.t) :=
    projection [attr_name, attr_name] (select_vertices attr_name labels (graph_to_vertices_relation g))
  
  Fixpoint get_edges (name : string) (types : list Property.t) (dir : direction) (p : t) (wname : name) (wlabels : list label) 
  (g : PropertyGraph.t) :=
    (**)

  Fixpoint transitive_get_edges (enames : list string) (etypes : list Property.t) (vnames : list string) (vlabels : list label) 
  (low : nat) (up : nat) (g : PropertyGraph.t) :=
    (**)

End GraphRelationOperation.

Fixpoint computePattern (p : Pattern.t) (g : PropertyGraph.t) :=
  match p with
  | vertex name labels => get_vertices name labels g
  | edge name types dir p wname wlabels => get_edges name types dir p wname wlabels g
  | multiedge enames etypes vnames vlabels low up => transitive_get_edges enames etypes vnames vlabels low up g
  .

Fixpoint computeQuery (q : Query.t) (g : PropertyGraph.t) :=
  match q with
  | MATCH ps => 
  match ps with
  | [] => (*Empty relation*)
  | h :: tl => natural_join (computePattern h g) (computeQuery (MATCH tl) g)
  .
  | OPTIONAL_MATCH q p => left_outer_join (computeQuery q g) (computePattern p g)
  | WHERE q p => 
  match p with
  | vertex name labels => select condition (computeQuery q g)
  | _ => semijoin (computeQuery q g) (computePattern p g) 
  .
  | WHERE_NOT q p => anti_semijoin (computeQuery q g) (computePattern p g)
  | RETURN q attrs => projection attrs (computeQuery q g)
  | RETURN_DISTINCT q attrs => all_different (projection attrs (computeQuery q g))
  (*| ORDER_SKIP_LIMIT q attrs s l => order_and_sort attrs s l (computeQuery q g)*)
  .