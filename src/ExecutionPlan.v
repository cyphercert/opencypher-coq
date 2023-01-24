Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From hahn Require Import HahnBase.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Classes.RelationClasses.

Require Import Cypher.
Require Import Semantics.
Require Import PropertyGraph.
Require Import Maps.
Require Import Utils.
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
Definition expansion_of (g : PropertyGraph.t) (r' r : Rcd.t)
                        (mode : ExpandMode.t)
                        (n_from n_edge n_to : Pattern.name)
                        (d : Pattern.direction) :=
  exists v_from e v_to,
    << HIn_e : In e (edges g) >> /\
    << Hdir : Path.matches_direction g v_from v_to e d >> /\
    << Hval_from : r n_from = Some (Value.GVertex v_from) >> /\
    match mode with
    | ExpandMode.All =>
      << Hval_to : r n_to = None >> /\
      << Hval' : r' = (n_to |-> Value.GVertex v_to; n_edge |-> Value.GEdge e; r) >>
    | ExpandMode.Into =>
      << Hval_to : r n_to = Some (Value.GVertex v_to) >> /\
      << Hval' : r' = (n_edge |-> Value.GEdge e; r) >>
    end.

Import FilterMode.
Import ExpandMode.

Module ExecutionPlan.
  Definition step0 := PropertyGraph.t -> option BindingTable.t.
  Definition step1 := PropertyGraph.t -> BindingTable.t -> option BindingTable.t.

  Module Type Spec.
    (* scan_vertices (n : Pattern.name) : step0 *)
    Parameter scan_vertices : Pattern.name -> step0.

    (* filter_by_label (mode : FilterMode.t) (n : Pattern.name) (l : label) : step1 *)
    Parameter filter_by_label : FilterMode.t -> Pattern.name -> label -> step1.

    (* expand (mode : ExpandMode.t) (n_from n_edge n_to : Pattern.name) (d : Pattern.direction) : step1 *)
    Parameter expand : ExpandMode.t -> Pattern.name -> Pattern.name -> Pattern.name -> Pattern.direction -> step1.

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

      Axiom expand_all_wf : forall n_from n_edge n_to d,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n_from = Some Value.GVertexT -> ty n_edge = None -> ty n_to = None ->
              exists table', expand All n_from n_edge n_to d graph table = Some table'.
      
      Axiom expand_into_wf : forall n_from n_edge n_to d,
        PropertyGraph.wf graph -> BindingTable.of_type table ty ->
          ty n_from = Some Value.GVertexT -> ty n_edge = None -> ty n_to = Some Value.GVertexT ->
            exists table', expand Into n_from n_edge n_to d graph table = Some table'.


      (** If the operation returned some table then the type of the table is correct *)

      Axiom scan_vertices_type : forall n,
        scan_vertices n graph = Some table' ->
          BindingTable.of_type table' (n |-> Value.GVertexT).
      
      Axiom filter_by_label_type : forall mode n l,
        filter_by_label mode n l graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table' ty.

      Axiom expand_all_type : forall n_from n_edge n_to d,
        expand All n_from n_edge n_to d graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table'
              (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; ty).

      Axiom expand_into_type : forall n_from n_edge n_to d,
        expand Into n_from n_edge n_to d graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table' (n_edge |-> Value.GEdgeT; ty).

      (** scan_vertices specification *)

      Axiom scan_vertices_spec : forall n v,
        scan_vertices n graph = Some table' ->
          (exists r, In r table' /\ r n = Some (Value.GVertex v)) <->
              In v (vertices graph).

      (** filter_by_label specification *)

      Axiom filter_vertices_by_label_spec : forall n l v r,
        filter_by_label Vertices n l graph table = Some table' ->
          r n = Some (Value.GVertex v) -> In r table' <->
            (In l (vlabels graph v) /\ In r table).

      Axiom filter_edges_by_label_spec : forall n l e r,
        filter_by_label Edges n l graph table = Some table' ->
          r n = Some (Value.GEdge e) -> In r table' <->
            (elabel graph e = l /\ In r table).

      (** expand specification *)

      Axiom expand_spec : forall r r' mode n_from n_edge n_to d,
        expand mode n_from n_edge n_to d graph table = Some table' ->
          expansion_of graph r' r mode n_from n_edge n_to d ->
            In r table -> In r' table'.

      Axiom expand_spec' : forall r' mode n_from n_edge n_to d,
        expand mode n_from n_edge n_to d graph table = Some table' -> In r' table' ->
            exists r, In r table /\ expansion_of graph r' r mode n_from n_edge n_to d.
    End axioms.
  End Spec.

  Inductive t :=
  | ScanVertices (n : Pattern.name)
  | FilterByLabel (mode : FilterMode.t) (n : Pattern.name) (l : label) (plan : t) 
  | Expand (mode : ExpandMode.t) (n_from n_edge n_to : Pattern.name) (d : Pattern.direction) (plan : t)
  .

  Fixpoint dom (plan : t) : list Pattern.name := 
    match plan with
    | ScanVertices n => [ n ]
    | FilterByLabel mode n l plan => dom plan
    | Expand All n_from n_edge n_to d plan => n_edge :: n_to :: dom plan
    | Expand Into n_from n_edge n_to d plan => n_edge :: dom plan
    end.

  Fixpoint type_of (plan : t) : BindingTable.T :=
    match plan with
    | ScanVertices n => n |-> Value.GVertexT
    | FilterByLabel mode n l plan => type_of plan
    | Expand All n_from n_edge n_to d plan => n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; type_of plan
    | Expand Into n_from n_edge n_to d plan => n_edge |-> Value.GEdgeT; type_of plan
    end.

  Fixpoint wf (plan : t) :=
    match plan with
    | ScanVertices n => True
    | FilterByLabel Vertices n l plan =>
      << Htype : type_of plan n = Some Value.GVertexT >> /\
      << Hwf : wf plan >>
    | FilterByLabel Edges n l plan =>
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
    end.

  Module EvalPlan (S : Spec).
    Import S.

    #[local]
    Hint Resolve scan_vertices_type filter_by_label_type
                expand_all_type expand_into_type : type_axioms.

    #[local]
    Hint Resolve scan_vertices_wf filter_vertices_by_label_wf filter_edges_by_label_wf
                 expand_all_wf expand_into_wf : wf_axioms.

    Section eval.
      Variable graph : PropertyGraph.t.
      Fixpoint eval (plan : ExecutionPlan.t) :=
        match plan with
        | ScanVertices n => scan_vertices n graph
        | FilterByLabel mode n l plan =>
          eval plan >>= filter_by_label mode n l graph
        | Expand mode n_from n_edge n_to d plan => 
          eval plan >>= expand mode n_from n_edge n_to d graph
        end.
    End eval.

    Theorem eval_type_of plan graph table'
                         (Heval : eval graph plan = Some table') :
        BindingTable.of_type table' (type_of plan).
    Proof.
      generalize dependent table'.
      induction plan; intros; simpl in *.
      { apply scan_vertices_type with graph. assumption. }
      all: destruct (eval graph plan); try discriminate.

      2: destruct mode.
      all: eauto with type_axioms.
    Qed.

    Lemma type_of_types plan k :
      type_of plan k = Some Value.GVertexT \/
      type_of plan k = Some Value.GEdgeT \/
      type_of plan k = None.
    Proof.
      induction plan; simpl in *.
      all: try unfold update, t_update, Pattern.name in *.
      all: desf.
      all: auto.
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

Module ExecutionPlanImpl : ExecutionPlan.Spec.

  Definition scan_vertices (n : Pattern.name)
                           (graph : PropertyGraph.t) :
    option BindingTable.t :=
    Some (map (fun v => n |-> Value.GVertex v) (vertices graph)).

  Section filter_by_label.
    Variable mode : FilterMode.t.
    Variable n : Pattern.name.
    Variable l : PropertyGraph.label.
    Variable graph : PropertyGraph.t.
    Variable table : BindingTable.t.

    Definition vertex_has_label (r : Rcd.t) : bool :=
      match r n with
      | Some (Value.GVertex v) => In_decb l (vlabels graph v)
      | _ => false
      end.

    Definition edge_has_label (r : Rcd.t) : bool :=
      match r n with
      | Some (Value.GEdge e) => elabel graph e ==b l
      | _ => false
      end.

    Definition has_label : Rcd.t -> bool :=
      match mode with
      | Vertices => vertex_has_label
      | Edges => edge_has_label
      end.

    Definition filter_by_label : option BindingTable.t :=
      Some (filter has_label table).
  End filter_by_label.

  #[local]
  Hint Unfold filter_by_label has_label vertex_has_label edge_has_label : filter_by_label_db.

  Section expand.
    Variable mode : ExpandMode.t.
    Variable n_from n_edge n_to : Pattern.name.
    Variable d : Pattern.direction.
    Variable graph : PropertyGraph.t.
    Variable table : BindingTable.t.

    Definition expand_all_single (r : Rcd.t) : option BindingTable.t :=
      match r n_from, r n_to with
      | Some (Value.GVertex v_from), None =>
        Some (map (fun '(e, v_to) => n_to   |-> Value.GVertex v_to;
                                     n_edge |-> Value.GEdge e; r)
          match d with
          | Pattern.OUT  => out_edges graph v_from
          | Pattern.IN   => in_edges  graph v_from
          | Pattern.BOTH => out_edges graph v_from ++
                            in_edges  graph v_from
          end)
      | _, _ => None
      end.

    Definition expand_into_single (r : Rcd.t) : option BindingTable.t :=
      match r n_from, r n_to with
      | Some (Value.GVertex v_from), Some (Value.GVertex v_to) =>
          Some (map (fun e => n_edge |-> Value.GEdge e; r)
          match d with
          | Pattern.OUT  => edges_between graph v_from v_to
          | Pattern.IN   => edges_between graph v_to   v_from
          | Pattern.BOTH => edges_between graph v_from v_to ++
                            edges_between graph v_to   v_from
          end)
      | _, _ => None
      end.

    Definition expand_single (r : Rcd.t) : option BindingTable.t :=
      match mode with
      | All => expand_all_single r
      | Into => expand_into_single r
      end.

    Definition expand : option BindingTable.t :=
      option_map (@List.concat Rcd.t) (fold_option (map expand_single table)).
  End expand.

  #[local]
  Hint Unfold expand expand_single expand_all_single expand_into_single : expand_db.

  (** If the inputs are well-formed then the operation will return the result *)

  Theorem scan_vertices_wf graph n (Hwf : PropertyGraph.wf graph) :
    exists table', scan_vertices n graph = Some table'.
  Proof.
    now eexists.
  Qed.

  Theorem filter_by_label_wf graph table ty mode n l
                             (Hwf : PropertyGraph.wf graph)
                             (Htype : BindingTable.of_type table ty)
                             (Hty : match mode with
                                    | Vertices => ty n = Some Value.GVertexT
                                    | Edges    => ty n = Some Value.GEdgeT
                                    end) :
    exists table', filter_by_label mode n l graph table = Some table'.
  Proof.
    autounfold with filter_by_label_db.
    all: induction table as [| r table IH]; ins; eauto.
  Qed.

  Theorem filter_vertices_by_label_wf graph table ty n l
                                    (Hwf : PropertyGraph.wf graph)
                                    (Htype : BindingTable.of_type table ty)
                                    (Hty : ty n = Some Value.GVertexT) :
    exists table', filter_by_label Vertices n l graph table = Some table'.
  Proof. eapply filter_by_label_wf with (mode := Vertices); eassumption. Qed.

  Theorem filter_edges_by_label_wf graph table ty n l
                                 (Hwf : PropertyGraph.wf graph)
                                 (Htype : BindingTable.of_type table ty)
                                 (Hty : ty n = Some Value.GEdgeT) :
    exists table', filter_by_label Edges n l graph table = Some table'.
  Proof. eapply filter_by_label_wf with (mode := Edges); eassumption. Qed.

  Theorem expand_wf graph table ty mode n_from n_edge n_to d
                    (Hwf : PropertyGraph.wf graph)
                    (Htype : BindingTable.of_type table ty)
                    (Hty_from : ty n_from = Some Value.GVertexT)
                    (Hty_edge : ty n_edge = None)
                    (Hty_to   : match mode with
                                | All => ty n_to = None
                                | Into => ty n_to = Some Value.GVertexT 
                                end) :
    exists table', expand mode n_from n_edge n_to d graph table = Some table'.
  Proof.
    all: autounfold with expand_db.
    
    eenough (exists t, fold_option _ = Some t) as [t Hfold]
      by (rewrite Hfold; now eexists).

    apply fold_option_some; intros a HIn; simpls.
    apply in_map_iff in HIn as [r [? ?]]; subst.

    edestruct BindingTable.type_of_GVertexT with (k := n_from) as [v_from Hv_from];
      try eassumption.
    rewrite Hv_from.

    destruct mode.
    2: edestruct BindingTable.type_of_GVertexT with (k := n_to)   as [v_to   Hv_to];
        try eassumption.
    2: rewrite Hv_to.
    1: erewrite BindingTable.type_of_None; try eassumption.
    all: now eexists.
  Qed.

  Theorem expand_all_wf graph table ty n_from n_edge n_to d
                  (Hwf : PropertyGraph.wf graph)
                  (Htype : BindingTable.of_type table ty)
                  (Hty_from : ty n_from = Some Value.GVertexT)
                  (Hty_edge : ty n_edge = None)
                  (Hty_to   : ty n_to   = None) :
    exists table', expand All n_from n_edge n_to d graph table = Some table'.
  Proof. eapply expand_wf with (mode := All); eassumption. Qed.

  Theorem expand_into_wf graph table ty n_from n_edge n_to d
                  (Hwf : PropertyGraph.wf graph)
                  (Htype : BindingTable.of_type table ty)
                  (Hty_from : ty n_from = Some Value.GVertexT)
                  (Hty_edge : ty n_edge = None)
                  (Hty_to   : ty n_to   = Some Value.GVertexT) :
    exists table', expand Into n_from n_edge n_to d graph table = Some table'.
  Proof. eapply expand_wf with (mode := Into); eassumption. Qed.

  (** If the operation returned some table then the type of the table is correct *)

  #[local]
  Hint Unfold update t_update Pattern.name equiv_decb
    BindingTable.of_type Rcd.type_of : unfold_pat.

  Ltac solve_type_of := now (
    extensionality k;
    autounfold with unfold_pat in *;
    desf).

  Ltac solve_type_of_extension r ty :=
    eenough (Rcd.type_of r = ty);
    [ solve_type_of | auto ].
  
  Theorem scan_vertices_type graph table' n 
                           (Hres : scan_vertices n graph = Some table') :
    BindingTable.of_type table' (n |-> Value.GVertexT).
  Proof.
    unfold scan_vertices in Hres.
    injection Hres as Hres. subst. intros r' HIn.
    apply in_map_iff in HIn as [r [Heq HIn]].
    subst.

    solve_type_of.
  Qed.
  
  Theorem filter_by_label_type graph table table' ty mode n l
                             (Hres : filter_by_label mode n l graph table = Some table')
                             (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table' ty.
  Proof.
    generalize dependent table'.
    destruct mode.
    all: autounfold with filter_by_label_db.
    all: induction table; ins; desf; eauto with type_of_db.
  Qed.

  Ltac inj_subst :=
    repeat match goal with
    | [ H : Some ?x = Some ?y |- _ ] => injection H as H; try subst y; try subst x
    end.

  Theorem expand_single_type graph r table' mode n_from n_edge n_to d
                          (Hres : expand_single mode n_from n_edge n_to d graph r = Some table') :
    match mode with
    | All => BindingTable.of_type table'
        (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; Rcd.type_of r)
    | Into => BindingTable.of_type table'
        (n_edge |-> Value.GEdgeT; Rcd.type_of r)
    end.
  Proof.
    autounfold with expand_db in *.
    desf.
    all: intros r' HIn'.
    all: apply in_map_iff in HIn'; desf.
    all: solve_type_of_extension r (Rcd.type_of r).
  Qed.

  Theorem expand_type graph table table' mode ty n_from n_edge n_to d
                          (Hres : expand mode n_from n_edge n_to d graph table = Some table')
                          (Htype : BindingTable.of_type table ty) :
    match mode with
    | All => BindingTable.of_type table' (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; ty)
    | Into => BindingTable.of_type table' (n_edge |-> Value.GEdgeT; ty)
    end.
  Proof.
    unfold expand in *.

    edestruct (fold_option _) as [tables' | ] eqn:Hfold; [ eauto | inv Hres ].
    simpls; inj_subst.

    destruct mode.
    all: apply BindingTable.of_type_concat; intros table' HIn_tables'.
    all: eassert (Hmap : In (Some table') (map _ table));
         [ eapply fold_option_In; eassumption | clear Hfold; clear HIn_tables' ].

    all: apply in_map_iff in Hmap as [r ?]; desf.
    all: assert (Rcd.type_of r = ty) as Hty by auto; subst.
    { eapply expand_single_type with (mode := All); eassumption. }
    { eapply expand_single_type with (mode := Into); eassumption. }
  Qed.

  Theorem expand_all_type graph table table' ty n_from n_edge n_to d
                          (Hres : expand All n_from n_edge n_to d graph table = Some table')
                          (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table' (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; ty).
  Proof. eapply expand_type with (mode := All); eassumption. Qed.

  Theorem expand_into_type graph table table' ty n_from n_edge n_to d
                          (Hres : expand Into n_from n_edge n_to d graph table = Some table')
                          (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table' (n_edge |-> Value.GEdgeT; ty).
  Proof. eapply expand_type with (mode := Into); eassumption. Qed.

  (** scan_vertices specification *)

  Definition scan_vertices_spec graph table' n v 
                                (Hres : scan_vertices n graph = Some table') :
    (exists r, In r table' /\ r n = Some (Value.GVertex v)) <-> In v (vertices graph).
  Proof.
    injection Hres as Hres. subst.
    split.
    { intros [r [HIn Hval]].
      apply in_map_iff in HIn as [v' [Heq HIn]]. subst.
      rewrite update_eq in Hval. inv Hval. }
    intros HIn. eexists. split.
    apply in_map; eauto.
    apply update_eq.
  Qed.

  (** filter_by_label specification *)

  Theorem vertex_has_label_true_iff graph n l v r
                                    (Hval : r n = Some (Value.GVertex v)) :
    vertex_has_label n l graph r = true <-> In l (vlabels graph v).
  Proof.
    unfold vertex_has_label.
    rewrite Hval.
    now rewrite <- In_decb_true_iff.
  Qed.

  Theorem edge_has_label_true_iff graph n l e r
                                  (Hval : r n = Some (Value.GEdge e)) :
    edge_has_label n l graph r = true <-> elabel graph e = l.
  Proof.
    unfold edge_has_label.
    rewrite Hval.
    now rewrite -> equiv_decb_true_iff.
  Qed.

  Theorem filter_by_label_spec graph table table' mode n l r 
    (Hres : filter_by_label mode n l graph table = Some table') :
      match mode with
      | Vertices => forall v, r n = Some (Value.GVertex v) ->
          In r table' <-> (In l (vlabels graph v) /\ In r table)
      | Edges    => forall e, r n = Some (Value.GEdge e) ->
          In r table' <-> (elabel graph e = l /\ In r table)
      end.
  Proof.
    unfold filter_by_label, has_label in Hres.
    inj_subst.
    destruct mode; ins.
    1: rewrite <- vertex_has_label_true_iff; try eassumption.
    2: rewrite <- edge_has_label_true_iff;   try eassumption.
    all: rewrite and_comm.
    all: apply filter_In.
  Qed.

  Theorem filter_vertices_by_label_spec graph table table' n l v r 
    (Hres : filter_by_label Vertices n l graph table = Some table')
    (Hval : r n = Some (Value.GVertex v)) :
      In r table' <-> (In l (vlabels graph v) /\ In r table).
  Proof.
    generalize dependent v.
    eapply filter_by_label_spec with (mode := Vertices); eassumption.
  Qed.

  Theorem filter_edges_by_label_spec graph table table' n l e r 
    (Hres : filter_by_label Edges n l graph table = Some table')
    (Hval : r n = Some (Value.GEdge e)) :
      In r table' <-> (elabel graph e = l /\ In r table).
  Proof.
    generalize dependent e.
    eapply filter_by_label_spec with (mode := Edges); eassumption.
  Qed.
  
  (** expand specification *)

  Theorem expand_single_spec graph table' r r' mode n_from n_edge n_to d
    (Hres : expand_single mode n_from n_edge n_to d graph r = Some table') :
      expansion_of graph r' r mode n_from n_edge n_to d <-> In r' table'.
  Proof.
    split; ins.
    all: unfold expansion_of, Path.matches_direction in *.

    - destruct mode; desf.
      all: autounfold with expand_db in Hres.
      all: rewrite Hval_from, Hval_to in Hres; desf.
      all: apply in_map_iff.
      all: try exists (e, v_to).
      all: try exists e.
      all: split; [ now reflexivity | ].
      all: try apply in_or_app.
      all: try rewrite -> in_edges_In.
      all: try rewrite -> out_edges_In.
      all: repeat rewrite -> edges_between_In.
      all: unfold e_from, e_to; destruct (ends graph e); desf.
      all: auto.

    - all: autounfold with expand_db in Hres.
      destruct mode; desf.
      all: match goal with
           | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; desf
           end.
      all: try match goal with
           | [ H : In _ (_ ++ _) |- _ ] => apply in_app_or in H
           end; desf.
      all: match goal with
           | [ H : In _ (out_edges _ _) |- _ ] => apply out_edges_In in H
           | [ H : In _ (in_edges _ _) |- _ ] => apply in_edges_In in H
           | [ H : In _ (edges_between _ _ _) |- _ ] => apply edges_between_In in H
           end; desf.
      all: eexists; eexists; eexists.
      all: repeat split.
      all: try assumption.

      all: unfold e_from, e_to in *; edestruct (ends graph _); desf; simpls.
      all: auto.
  Qed.

  Theorem expand_spec graph table table' r r' mode n_from n_edge n_to d
      (Hres : expand mode n_from n_edge n_to d graph table = Some table')
      (Hexp : expansion_of graph r' r mode n_from n_edge n_to d)
      (HIn : In r table) : In r' table'.
  Proof.
    unfold expand in *.
    edestruct (fold_option _) as [tables' | ] eqn:Hfold; [ eauto | inv Hres ].
    simpls; inj_subst.

    eassert (Hmap : In (_ r) (map _ table)).
    { now eapply in_map. }

    eassert (exists table', _ r = Some table') as [table' Hres].
    { eapply fold_option_some_inv in Hfold as [table' Heq].
      exists table'. all: eassumption. }

    apply in_concat. exists table'. split.
    { eapply fold_option_In. eassumption. unfold BindingTable.t in *.
      now rewrite <- Hres. }
    eapply expand_single_spec; eauto.
  Qed.

  Theorem expand_spec' graph table table' r' mode n_from n_edge n_to d
    (Hres : expand mode n_from n_edge n_to d graph table = Some table')
    (HIn : In r' table') :
      exists r, In r table /\ expansion_of graph r' r mode n_from n_edge n_to d.
  Proof.
    unfold expand in *.
    edestruct (fold_option _) as [tables' | ] eqn:?; [ eauto | inv Hres ].
    simpls; inj_subst.

    apply in_concat in HIn as [table' ?]; desf.
    eassert (Hmap : In (Some table') (map _ table)).
    { eapply fold_option_In; eassumption. }

    apply in_map_iff in Hmap as [r ?]; desf.
    exists r. split. { assumption. }
    eapply expand_single_spec; eassumption.
  Qed.
End ExecutionPlanImpl.

