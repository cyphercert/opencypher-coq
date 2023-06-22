Require Import Utils.
Require Import Maps.
Require Import PropertyGraph.
Require Import Cypher.
Require Import BindingTable.
Require Import Semantics.
Require Import PatternE.

Import PartialMap.Notations.
Import PropertyGraph.

Module FilterMode.
  Inductive t : Type :=
  | Vertices
  | Edges
  .
End FilterMode.

Module ExpandMode .
  Inductive t : Type :=
  | All
  | Into
  .
End ExpandMode.

(* r' is expanded from r by traversing one edge *)
Definition expansion_of' (g : PropertyGraph.t) (r' r : Rcd.t)
                         (mode : ExpandMode.t)
                         (v_from : vertex) (e : edge) (v_to : vertex)
                         (n_from n_edge n_to : Name.t)
                         (d : Pattern.direction) :=
  << HIn_e : In e (edges g) >> /\
  << Hdir : Path.matches_direction g v_from v_to e d >> /\
  << Hval_from : r n_from = Some (Value.GVertex v_from) >> /\
  << Hval_edge : r n_edge = None >> /\
  << Hval' : r' = (n_to |-> Value.GVertex v_to; n_edge |-> Value.GEdge e; r) >> /\
  match mode with
  | ExpandMode.All =>
    << Hval_to : r n_to = None >>
  | ExpandMode.Into =>
    << Hval_to : r n_to = Some (Value.GVertex v_to) >>
  end.

(* r' is expanded from r by traversing one edge *)
Definition expansion_of (g : PropertyGraph.t) (r' r : Rcd.t)
                        (mode : ExpandMode.t)
                        (n_from n_edge n_to : Name.t)
                        (d : Pattern.direction) :=
  exists v_from e v_to,
    expansion_of' g r' r mode v_from e v_to n_from n_edge n_to d.

Import FilterMode.
Import ExpandMode.

Module ExecutionPlan.
  Definition step0 := PropertyGraph.t -> option BindingTable.t.
  Definition step1 := PropertyGraph.t -> BindingTable.t -> option BindingTable.t.

  Module Type Spec.
    (* scan_vertices (n : Name.t) : step0 *)
    Parameter scan_vertices : Name.t -> step0.

    (* filter_by_label (mode : FilterMode.t) (n : Name.t) (l : label) : step1 *)
    Parameter filter_by_label : FilterMode.t -> Name.t -> label -> step1.

    (* filter_by_property (mode : FilterMode.t) (n : Name.t) (key : Property.name) (value : Property.t) : step1 *)
    Parameter filter_by_property : FilterMode.t -> Name.t -> Property.name -> Property.t -> step1.

    (* expand (mode : ExpandMode.t) (n_from n_edge n_to : Name.t) (d : Pattern.direction) : step1 *)
    Parameter expand : ExpandMode.t -> Name.t -> Name.t -> Name.t -> Pattern.direction -> step1.

    (* return_all : step1 *)
    Parameter return_all : step1.

    (* traverse (slice : PatternSlice.t) (n_from : Name.t) : step1 *)
    Parameter traverse : PatternSlice.t -> Name.t -> step1.

    Section axioms.
      Variable graph : PropertyGraph.t.
      Variable table : BindingTable.t.
      Variable table' : BindingTable.t.
      Variable ty : BindingTable.T.

      (** If the inputs are well-formed then the operation will return the result *)

      Axiom scan_vertices_wf : forall n,
        PropertyGraph.wf graph ->
          exists table', scan_vertices n graph = Some table'.

      Axiom filter_vertices_by_label_wf : forall n l,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n = Some Value.GVertexT ->
            exists table', filter_by_label Vertices n l graph table = Some table'.

      Axiom filter_edges_by_label_wf : forall n l,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n = Some Value.GEdgeT ->
            exists table', filter_by_label Edges n l graph table = Some table'.

      Axiom filter_vertices_by_property_wf : forall n k val,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n = Some Value.GVertexT ->
            exists table', filter_by_property Vertices n k val graph table = Some table'.

      Axiom filter_edges_by_property_wf : forall n k val,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n = Some Value.GEdgeT ->
            exists table', filter_by_property Edges n k val graph table = Some table'.

      Axiom expand_all_wf : forall n_from n_edge n_to d,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n_from = Some Value.GVertexT -> ty n_edge = None -> ty n_to = None ->
              exists table', expand All n_from n_edge n_to d graph table = Some table'.
      
      Axiom expand_into_wf : forall n_from n_edge n_to d,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n_from = Some Value.GVertexT -> ty n_edge = None -> ty n_to = Some Value.GVertexT ->
            exists table', expand Into n_from n_edge n_to d graph table = Some table'.

      Axiom return_all_wf :
        exists table', return_all graph table = Some table'.

      Axiom traverse_wf : forall slice n_from,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          PatternSlice.wf ty slice -> ty n_from = Some Value.GVertexT ->
            exists table', traverse slice n_from graph table = Some table'.

      (** If the operation returned some table then the type of the table is correct *)

      Axiom scan_vertices_type : forall n,
        scan_vertices n graph = Some table' ->
          BindingTable.of_type table' (n |-> Value.GVertexT).
      
      Axiom filter_by_label_type : forall mode n l,
        filter_by_label mode n l graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table' ty.

      Axiom filter_by_property_type : forall mode n k val,
        filter_by_property mode n k val graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table' ty.

      Axiom expand_type : forall mode n_from n_edge n_to d,
        expand mode n_from n_edge n_to d graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table'
              (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; ty).

      Axiom return_all_type :
        return_all graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table' (Rcd.explicit_projT ty).

      Axiom traverse_type : forall slice n_from,
        traverse slice n_from graph table = Some table' ->
          BindingTable.of_type table ty -> PatternSlice.wf ty slice ->
            BindingTable.of_type table' (PatternSlice.type_of ty slice).

      (** scan_vertices specification *)

      Axiom scan_vertices_spec : forall n v,
        scan_vertices n graph = Some table' ->
          In v (vertices graph) ->
            In (n |-> Value.GVertex v) table'.

      Axiom scan_vertices_spec' : forall n r',
        scan_vertices n graph = Some table' ->
          In r' table' -> exists v,
            r' = (n |-> Value.GVertex v) /\ In v (vertices graph).

      (** filter_by_label specification *)

      Axiom filter_vertices_by_label_spec : forall n l v r,
        filter_by_label Vertices n l graph table = Some table' ->
          r n = Some (Value.GVertex v) -> In l (vlabels graph v) ->
            In r table -> In r table'.
      
      Axiom filter_vertices_by_label_spec' : forall n l r',
        filter_by_label Vertices n l graph table = Some table' ->
           In r' table' -> In r' table /\
            exists v, r' n = Some (Value.GVertex v) /\ In l (vlabels graph v).

      Axiom filter_edges_by_label_spec : forall n l e r,
        filter_by_label Edges n l graph table = Some table' ->
          r n = Some (Value.GEdge e) -> elabel graph e = l ->
            In r table -> In r table'.

      Axiom filter_edges_by_label_spec' : forall n l r',
        filter_by_label Edges n l graph table = Some table' ->
          In r' table' -> In r' table /\
            exists e, r' n = Some (Value.GEdge e) /\ elabel graph e = l.

      (** filter_by_property specification *)

      Axiom filter_vertices_by_property_spec : forall n k val v r,
        filter_by_property Vertices n k val graph table = Some table' ->
          r n = Some (Value.GVertex v) -> get_vprop graph k v = Some val ->
            In r table -> In r table'.
      
      Axiom filter_vertices_by_property_spec' : forall n k val r',
        filter_by_property Vertices n k val graph table = Some table' ->
           In r' table' -> In r' table /\
            exists v, r' n = Some (Value.GVertex v) /\
              get_vprop graph k v = Some val.

      Axiom filter_edges_by_property_spec : forall n k val e r,
        filter_by_property Edges n k val graph table = Some table' ->
          r n = Some (Value.GEdge e) -> get_eprop graph k e = Some val ->
            In r table -> In r table'.

      Axiom filter_edges_by_property_spec' : forall n k val r',
        filter_by_property Edges n k val graph table = Some table' ->
          In r' table' -> In r' table /\
            exists e, r' n = Some (Value.GEdge e) /\
              get_eprop graph k e = Some val.

      (** expand specification *)

      Axiom expand_spec : forall r r' mode n_from n_edge n_to d,
        expand mode n_from n_edge n_to d graph table = Some table' ->
          expansion_of graph r' r mode n_from n_edge n_to d ->
            In r table -> In r' table'.

      Axiom expand_spec' : forall r' mode n_from n_edge n_to d,
        expand mode n_from n_edge n_to d graph table = Some table' -> In r' table' ->
            exists r, In r table /\ expansion_of graph r' r mode n_from n_edge n_to d.

      (** return_all specification *)

      Axiom return_all_spec : forall r,
        return_all graph table = Some table' ->
          In r table -> In (Rcd.explicit_proj r) table'.

      Axiom return_all_spec' : forall r',
        return_all graph table = Some table' ->
          In r' table' -> exists r, In r table /\ r' = Rcd.explicit_proj r.

      (** traverse specification *)

      Axiom traverse_spec : forall path r r' slice n_from,
        PropertyGraph.wf graph -> PatternSlice.wf (Rcd.type_of r) slice ->
          traverse slice n_from graph table = Some table' ->
            PathSlice.matches graph r n_from r' path slice ->
              In r table -> In r' table'.

      Axiom traverse_spec' : forall r' slice n_from,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          PatternSlice.wf ty slice ->
            traverse slice n_from graph table = Some table' ->
              In r' table' -> exists r path, In r table /\
                PathSlice.matches graph r n_from r' path slice.
    End axioms.
  End Spec.

  Inductive t :=
  | ScanVertices (n : Name.t)
  | FilterByLabel (mode : FilterMode.t) (n : Name.t) (l : label) (plan : t) 
  | FilterByProperty (mode : FilterMode.t) (n : Name.t) (k : Property.name) (val : Property.t) (plan : t) 
  | Expand (mode : ExpandMode.t) (n_from n_edge n_to : Name.t) (d : Pattern.direction) (plan : t)
  | ReturnAll (plan : t)
  | Traverse (slice : PatternSlice.t) (n_from : Name.t) (plan : t)
  .

  Fixpoint type_of (plan : t) : BindingTable.T :=
    match plan with
    | ScanVertices n => n |-> Value.GVertexT
    | FilterByLabel mode n l plan => type_of plan
    | FilterByProperty mode n k val plan => type_of plan
    | Expand mode n_from n_edge n_to d plan => n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; type_of plan
    | ReturnAll plan => Rcd.explicit_projT (type_of plan)
    | Traverse slice n_from plan => PatternSlice.type_of (type_of plan) slice
    end.

  Lemma type_of_types plan k :
    type_of plan k = Some Value.GVertexT \/
    type_of plan k = Some Value.GEdgeT \/
    type_of plan k = None.
  Proof using.
    induction plan; simpl in *.
    all: unfold Rcd.explicit_projT.
    all: autounfold with unfold_pat.
    all: desf.
    all: auto using PatternSlice.type_of__types.
  Qed.

  Fixpoint wf (plan : t) :=
    match plan with
    | ScanVertices n => True
    | FilterByLabel Vertices n l plan =>
      << Htype : type_of plan n = Some Value.GVertexT >> /\
      << Hwf : wf plan >>
    | FilterByLabel Edges n l plan =>
      << Htype : type_of plan n = Some Value.GEdgeT >> /\
      << Hwf : wf plan >>
    | FilterByProperty Vertices n k val plan =>
      << Htype : type_of plan n = Some Value.GVertexT >> /\
      << Hwf : wf plan >>
    | FilterByProperty Edges n k val plan =>
      << Htype : type_of plan n = Some Value.GEdgeT >> /\
      << Hwf : wf plan >>
    | Expand All n_from n_edge n_to d plan =>
      << Htype_from : type_of plan n_from = Some Value.GVertexT >> /\
      << Htype_edge : type_of plan n_edge = None >> /\
      << Htype_to : type_of plan n_to = None >> /\
      << Hneq_from : n_from =/= n_edge >> /\
      << Hneq_to : n_to =/= n_edge >> /\
      << Hwf : wf plan >>
    | Expand Into n_from n_edge n_to d plan =>
      << Htype_from : type_of plan n_from = Some Value.GVertexT >> /\
      << Htype_edge : type_of plan n_edge = None >> /\
      << Htype_to : type_of plan n_to = Some Value.GVertexT >> /\
      << Hneq_from : n_from =/= n_edge >> /\
      << Hneq_to : n_to =/= n_edge >> /\
      << Hwf : wf plan >>
    | ReturnAll plan =>
      << Hwf : wf plan >>
    | Traverse slice n_from plan =>
      << Htype : type_of plan n_from = Some Value.GVertexT >> /\
      << Hwf_slice : PatternSlice.wf (type_of plan) slice >> /\
      << Hwf : wf plan >>
    end.

  Module EvalPlan (S : Spec).
    Import S.

    #[local]
    Hint Resolve scan_vertices_type filter_by_label_type filter_by_property_type
                expand_type return_all_type traverse_type : type_axioms.

    #[local]
    Hint Resolve scan_vertices_wf
                 filter_vertices_by_label_wf filter_edges_by_label_wf
                 filter_vertices_by_property_wf filter_edges_by_property_wf
                 expand_all_wf expand_into_wf
                 return_all_wf traverse_wf : wf_axioms.

    Section eval.
      Variable graph : PropertyGraph.t.
      Fixpoint eval (plan : ExecutionPlan.t) :=
        match plan with
        | ScanVertices n => scan_vertices n graph
        | FilterByLabel mode n l plan =>
          eval plan >>= filter_by_label mode n l graph
        | FilterByProperty mode n k val plan =>
          eval plan >>= filter_by_property mode n k val graph
        | Expand mode n_from n_edge n_to d plan => 
          eval plan >>= expand mode n_from n_edge n_to d graph
        | ReturnAll plan => eval plan >>= return_all graph
        | Traverse slice n_from plan =>
          eval plan >>= traverse slice n_from graph
        end.
    End eval.

    (* TODO: generalize the following for just the option_bind *)
    Local Ltac eval_operation_reduce_aux Hres :=
      simpl in Hres; unfold option_bind in Hres; desf; eauto.

    Lemma eval_filter_by_label_reduce plan graph mode n l table'
      (Hres : eval graph plan >>= filter_by_label mode n l graph = Some table') :
        exists table, eval graph plan = Some table /\
          filter_by_label mode n l graph table = Some table'.
    Proof. eval_operation_reduce_aux Hres. Qed.

    Lemma eval_filter_by_property_reduce plan graph mode n k val table'
      (Hres : eval graph plan >>= filter_by_property mode n k val graph = Some table') :
        exists table, eval graph plan = Some table /\
          filter_by_property mode n k val graph table = Some table'.
    Proof. eval_operation_reduce_aux Hres. Qed.

    Lemma eval_expand_reduce plan graph mode n_from n_edge n_to d table'
      (Hres : eval graph plan >>= expand mode n_from n_edge n_to d graph = Some table') :
        exists table, eval graph plan = Some table /\
          expand mode n_from n_edge n_to d graph table = Some table'.
    Proof. eval_operation_reduce_aux Hres. Qed.

    Lemma eval_traverse_reduce plan graph slice n_from table'
      (Hres : eval graph plan >>= traverse slice n_from graph = Some table') :
        exists table, eval graph plan = Some table /\
          traverse slice n_from graph table = Some table'.
    Proof. eval_operation_reduce_aux Hres. Qed.

    Lemma eval_return_all_reduce plan graph table'
      (Hres : eval graph plan >>= return_all graph = Some table') :
        exists table, eval graph plan = Some table /\
          return_all graph table = Some table'.
    Proof. eval_operation_reduce_aux Hres. Qed.

    Ltac eval_operation_reduce_impl Hres Hres' :=
      let table := fresh "table" in
        match type of Hres with
        | eval _ _ >>= filter_by_label _ _ _ _ = Some _ =>
          apply eval_filter_by_label_reduce in Hres as [table [Hres Hres']]
        | eval _ _ >>= filter_by_property _ _ _ _ _ = Some _ =>
          apply eval_filter_by_property_reduce in Hres as [table [Hres Hres']]
        | eval _ _ >>= expand _ _ _ _ _ _ = Some _ =>
          apply eval_expand_reduce in Hres as [table [Hres Hres']]
        | eval _ _ >>= traverse _ _ _ = Some _ =>
          apply eval_traverse_reduce in Hres as [table [Hres Hres']]
        | eval _ _ >>= return_all _ = Some _ =>
          apply eval_return_all_reduce in Hres as [table [Hres Hres']]
        | _ => fail "the hypothesis is of the wrong form"
        end.

    Tactic Notation "eval_operation_reduce" "in" hyp(Hres) :=
      let Hres' := fresh "Hres'" in
        eval_operation_reduce_impl Hres Hres'.

    Tactic Notation "eval_operation_reduce" "in" hyp(Hres) "eqn:" ident(Hres') :=
      eval_operation_reduce_impl Hres Hres'.

    Theorem eval_type_of plan graph table'
                         (Heval : eval graph plan = Some table')
                         (Hwf : wf plan) :
        BindingTable.of_type table' (type_of plan).
    Proof using.
      generalize dependent table'.
      induction plan; intros; simpl in *.
      { apply scan_vertices_type with graph. assumption. }
      all: destruct (eval graph plan); try discriminate.

      all: try destruct mode; desc.
      all: eauto with type_axioms.
    Qed.

    Theorem eval_wf plan graph (Hwf : wf plan) (Hwf' : PropertyGraph.wf graph) :
        exists table', eval graph plan = Some table'.
    Proof with (try eassumption).
      induction plan. all: simpl in *; desf; desf.
      { apply scan_vertices_wf... }
      all: destruct IHplan as [table IH]...
      all: rewrite IH; simpl.
      all: eauto using eval_type_of with wf_axioms.
    Qed.
  End EvalPlan.
End ExecutionPlan.
