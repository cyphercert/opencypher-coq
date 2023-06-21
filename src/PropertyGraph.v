Require Import Utils.

Module Property.

  (** Supported types in the graph database **)

  Inductive t := 
  | p_int (i : Z)
  | p_string (s : string)
  .

  Definition eq_property_dec (a b : t) : {a = b} + {a <> b}.
    refine (
      match a, b with
      | p_int a,          p_int b          => if a == b then left _ else right _
      | p_string a,       p_string b       => if a == b then left _ else right _
      | _,                _                => right _
      end
    ).
    all: try discriminate. (* Solve goals with different constructors *)
    all: try now f_equal.  (* Solve goals when underlying values are equal *)
    all: injection as H; contradiction. (* Solve goals when underlying values are not equal *)
  Defined.

  #[global]
  Program Instance property_eqdec : EqDec t eq := eq_property_dec.
  
  Definition name := string.

End Property.

(** Property Graph structure **)

Module PropertyGraph.

  (** Types are used for indexing vertices and edges **)

  Definition vertex    := nat.
  Definition edge      := nat.
  Definition label     := string.

  (** Graph database model **)

  (** vertices : vertices of the graph **)

  (** edges    : edges of the graph **)

  (** ends     : maps an edge to a pair of its ends **)

  (** vlab     : maps a vertex to a list of its labels **)

  (** elab     : maps an edge to its relationship type **)

  (** vprops   : maps a vertex to key-value pairs of its properties **)

  (** eprops   : maps an edge to key-value pairs of its properties **)
  
  Record t :=
    mk { vertices : list vertex;
         edges    : list edge;
         ends     : edge -> vertex * vertex;
         vlabels  : vertex -> list label;
         elabel   : edge   -> label;
         vprops   : vertex -> list (Property.name * Property.t); 
         eprops   : edge   -> list (Property.name * Property.t); 
      }.

  Fixpoint get_prop (k : Property.name) (props : list (Property.name * Property.t)) : option Property.t :=
    match props with
    | (k', v) :: props => if k ==b k' then Some v else get_prop k props
    | nil => None
    end.
  
  Definition get_vprop (g : PropertyGraph.t) (k : Property.name) (v : vertex) : option Property.t :=
    get_prop k (vprops g v).

  Definition get_eprop (g : PropertyGraph.t) (k : Property.name) (e : edge) : option Property.t :=
    get_prop k (eprops g e).

  Definition e_from (g : t) (e : edge) := fst (ends g e).
  Definition e_to   (g : t) (e : edge) := snd (ends g e).

  Theorem e_from_to g e : ends g e = (e_from g e, e_to g e).
  Proof using.
    unfold e_from, e_to. destruct (ends g e); auto.
  Qed.

  Definition out_edges (g : t) (v : vertex) :=
    filter_map (fun e => if e_from g e ==b v then Some (e, e_to g e) else None) (edges g).

  Definition in_edges (g : t) (v : vertex) :=
    filter_map (fun e => if e_to g e ==b v then Some (e, e_from g e) else None) (edges g).

  Definition edges_between (g : t) (from to : vertex) :=
    filter (fun e => (e_from g e ==b from) && (e_to g e ==b to)) (edges g).

  Theorem out_in_between_edges_In g e v v' :
    (In (e, v') (out_edges g v) <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v') /\
    (In (e, v') (in_edges g v) <-> In e (edges g) /\ e_to g e = v /\ e_from g e = v') /\
    (In e (edges_between g v v') <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v').
  Proof using.
    split; [|split].
    
    all: unfold out_edges, in_edges, edges_between, e_from, e_to.
    all: try rewrite filter_map_In.
    all: try rewrite filter_In.
    all: split; ins; desf.
    all: try exists e.
    all: try erewrite equiv_decb_true.
    all: try match goal with 
         | Heq : (_ && _ = true) |- _ => apply Bool.andb_true_iff in Heq; destruct Heq
         end.
    all: repeat match goal with 
         | Heq : (_ = true) |- _ => apply equiv_decb_true' in Heq
         end.
    all: edestruct (ends g _); desf.
    { rewrite Bool.andb_true_iff. rewrite equiv_decb_true_iff. auto. }
  Qed.

  Lemma out_edges_In g e v v' :
    In (e, v') (out_edges g v) <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v'.
  Proof using.
    edestruct out_in_between_edges_In as [? [? ?]]; eassumption.
  Qed.

  Lemma in_edges_In g e v v' :
    In (e, v') (in_edges g v) <-> In e (edges g) /\ e_to g e = v /\ e_from g e = v'.
  Proof using.
    edestruct out_in_between_edges_In as [? [? ?]]; eassumption.
  Qed.

  Lemma edges_between_In g e v v' :
    In e (edges_between g v v') <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v'.
  Proof using.
    edestruct out_in_between_edges_In as [? [? ?]]; eassumption.
  Qed.

  Definition list_is_map {A B} (xs : list (A * B)) :=
    forall k val1 val2, In (k, val1) xs -> In (k, val2) xs -> val1 = val2.

  Theorem list_is_map_tail (A B : Type) (x : A * B) (xs : list (A * B))
    (H : list_is_map (x :: xs)) :
      list_is_map xs.
  Proof.
    unfold list_is_map in *; ins; eauto.
  Qed.

  Record wf (g : t) := mk_wf {
    vertices_NoDup : NoDup (vertices g);
    edges_NoDup : NoDup (edges g);

    ends_In : forall v v' e,
      In e (edges g) -> ends g e = (v, v') -> In v (vertices g) /\ In v' (vertices g);

    vlabels_In : forall v, vlabels g v <> nil -> In v (vertices g);

    vprops_In : forall v, vprops g v <> nil -> In v (vertices g);
    eprops_In : forall e, eprops g e <> nil -> In e (edges g);

    vprops_unique: forall v, list_is_map (vprops g v);
    eprops_unique: forall e, list_is_map (eprops g e);
  }.

  Lemma wf_get_prop_In props k val
    (Hval : get_prop k props = Some val) :
      In (k, val) props.
  Proof.
    induction props as [| [k' val'] props]; simpls.
    destruct (equiv_decbP k k'); subst.
    { left. desf. }
    right. now apply IHprops.
  Qed.

  Lemma wf_In_get_prop props k val
    (Hunique : list_is_map props)
    (HIn : In (k, val) props) :
      get_prop k props = Some val.
  Proof.
    induction props as [| [k' val'] props]; simpls.
    destruct HIn as [HIn | HIn], (equiv_decbP k k'); desf.
    { unfold list_is_map in Hunique.
      f_equal. eapply Hunique; [ now left | now right ]. }
    eauto using list_is_map_tail.
  Qed.

  Theorem wf_get_prop_In_iff props k val
    (Hunique : list_is_map props) :
      get_prop k props = Some val <-> In (k, val) props.
  Proof.
    split; auto using wf_get_prop_In, wf_In_get_prop.
  Qed.

  Corollary wf_get_vprop_In_iff g v k val (Hwf : wf g) :
    get_vprop g k v = Some val <-> In (k, val) (vprops g v).
  Proof.
    unfold get_vprop. destruct Hwf.
    now apply wf_get_prop_In_iff.
  Qed.
    
  Corollary wf_get_eprop_In_iff g e k val (Hwf : wf g) :
    get_eprop g k e = Some val <-> In (k, val) (eprops g e).
  Proof.
    unfold get_eprop. destruct Hwf.
    now apply wf_get_prop_In_iff.
  Qed.

  Lemma wf_e_from_In g e
    (Hwf : wf g)
    (HIn : In e (edges g)) :
      In (e_from g e) (vertices g).
  Proof using.
    unfold e_from, fst. desf.
    edestruct ends_In; eauto.
  Qed.

  Lemma wf_e_to_In g e
    (Hwf : wf g)
    (HIn : In e (edges g)) :
      In (e_to g e) (vertices g).
  Proof using.
    unfold e_to, snd. desf.
    edestruct ends_In; eauto.
  Qed.

End PropertyGraph.
