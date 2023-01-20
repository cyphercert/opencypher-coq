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

      (** expand_all specification *)

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
      - eapply filter_by_label_type; eauto.
      - eapply expand_all_type; eauto.
      - eapply expand_into_type; eauto.
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
      all: rewrite IH.
      1: eapply filter_vertices_by_label_wf...
      2: eapply filter_edges_by_label_wf...
      3: eapply expand_all_wf...
      4: eapply expand_into_wf...
      all: eapply eval_type_of...
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

    Definition filter_vertices_by_label :  option BindingTable.t :=
      let f (r : Rcd.t) :=
        match r n with
        | Some (Value.GVertex v) => In_decb l (vlabels graph v)
        | _ => false
        end
      in Some (filter f table).

    Definition filter_edges_by_label : option BindingTable.t :=
      let f (r : Rcd.t) :=
        match r n with
        | Some (Value.GEdge e) => elabel graph e ==b l
        | _ => false
        end
      in Some (filter f table).

    Definition filter_by_label : option BindingTable.t :=
      match mode with
      | Vertices => filter_vertices_by_label
      | Edges => filter_edges_by_label
      end.
  End filter_by_label.

  #[local]
  Hint Unfold filter_by_label filter_vertices_by_label filter_edges_by_label : filter_by_label_db.

  Section expand.
    Variable mode : ExpandMode.t.
    Variable n_from n_edge n_to : Pattern.name.
    Variable d : Pattern.direction.
    Variable graph : PropertyGraph.t.
    Variable table : BindingTable.t.

    Definition expand_all_single (r : Rcd.t) : option BindingTable.t :=
      match r n_from, r n_to with
      | Some (Value.GVertex v_from), None =>
        Some (map (fun e => n_to   |-> Value.GVertex (e_to graph e);
                           n_edge |-> Value.GEdge e)
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
          Some (map (fun e => n_edge |-> Value.GEdge e)
          match d with
          | Pattern.OUT  => edges_between graph v_from v_to
          | Pattern.IN   => edges_between graph v_to   v_from
          | Pattern.BOTH => edges_between graph v_from v_to ++
                            edges_between graph v_to   v_from
          end)
      | _, _ => None
      end.

    Definition expand_base (expand_single : Rcd.t -> option BindingTable.t) :=
      option_map (@List.concat Rcd.t) (fold_option (map expand_single table)).

    Definition expand_all := expand_base expand_all_single.

    Definition expand_into := expand_base expand_into_single.

    Definition expand : option BindingTable.t :=
      match mode with
      | All => expand_all
      | Into => expand_into
      end.
  End expand.

  #[local]
  Hint Unfold expand expand_all expand_into expand_base expand_all_single expand_into_single : expand_db.

  (** If the inputs are well-formed then the operation will return the result *)

  Theorem scan_vertices_wf graph n (Hwf : PropertyGraph.wf graph) :
    exists table', scan_vertices n graph = Some table'.
  Proof.
    now eexists.
  Qed.

  Theorem filter_vertices_by_label_wf graph table ty n l
                                    (Hwf : PropertyGraph.wf graph)
                                    (Htype : BindingTable.of_type table ty)
                                    (Hty : ty n = Some Value.GVertexT) :
    exists table', filter_vertices_by_label n l graph table = Some table'.
  Proof.
    autounfold with filter_by_label_db.
    induction table as [| r table IH]; ins; eauto.
  Qed.

  Theorem filter_edges_by_label_wf graph table ty n l
                                 (Hwf : PropertyGraph.wf graph)
                                 (Htype : BindingTable.of_type table ty)
                                 (Hty : ty n = Some Value.GEdgeT) :
    exists table', filter_edges_by_label n l graph table = Some table'.
  Proof.
    autounfold with filter_by_label_db.
    induction table as [| r table IH]; ins; eauto.
  Qed.

  Theorem expand_all_wf graph table ty n_from n_edge n_to d
                  (Hwf : PropertyGraph.wf graph)
                  (Htype : BindingTable.of_type table ty)
                  (Hty_from : ty n_from = Some Value.GVertexT)
                  (Hty_edge : ty n_edge = None)
                  (Hty_to   : ty n_to   = None) :
    exists table', expand All n_from n_edge n_to d graph table = Some table'.
  Proof.
    autounfold with expand_db.
    
    eenough (exists t, fold_option _ = Some t) as [t Hfold].
    { rewrite Hfold. now eexists. }

    apply fold_option_some; intros a HIn; simpls.
    apply in_map_iff in HIn as [r [? ?]]; subst.

    edestruct BindingTable.type_of_GVertexT as [v_from Hv_from]; try eassumption.
    rewrite Hv_from.
    erewrite BindingTable.type_of_None; try eassumption.
    now eexists.
  Qed.

  Theorem expand_into_wf graph table ty n_from n_edge n_to d
                  (Hwf : PropertyGraph.wf graph)
                  (Htype : BindingTable.of_type table ty)
                  (Hty_from : ty n_from = Some Value.GVertexT)
                  (Hty_edge : ty n_edge = None)
                  (Hty_to   : ty n_to   = Some Value.GVertexT) :
    exists table', expand Into n_from n_edge n_to d graph table = Some table'.
  Proof.
    autounfold with expand_db.
    
    eenough (exists t, fold_option _ = Some t) as [t Hfold].
    { rewrite Hfold. now eexists. }

    apply fold_option_some; intros a HIn; simpls.
    apply in_map_iff in HIn as [r [? ?]]; subst.

    edestruct BindingTable.type_of_GVertexT with (k := n_from) as [v_from Hv_from],
              BindingTable.type_of_GVertexT with (k := n_to) as [v_to Hv_to];
              try eassumption.
    rewrite Hv_from. rewrite Hv_to.
    now eexists.
  Qed.

  (** If the operation returned some table then the type of the table is correct *)

  #[local]
  Hint Unfold update t_update Pattern.name equiv_decb
    BindingTable.of_type Rcd.type_of : unfold_pat.
  
  Theorem scan_vertices_type graph table' n 
                           (Hres : scan_vertices n graph = Some table') :
    BindingTable.of_type table' (n |-> Value.GVertexT).
  Proof.
    unfold scan_vertices in Hres.
    autounfold with unfold_pat in *.
    injection Hres as Hres. subst. intros r' HIn.
    apply in_map_iff in HIn as [r [Heq HIn]].
    subst. extensionality k.
    desf.
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

  Theorem expand_all_type graph table table' ty n_from n_edge n_to d
                          (Hres : expand All n_from n_edge n_to d graph table = Some table')
                          (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table' (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; ty).
  Proof.
  Admitted.


  Theorem expand_into_type graph table table' ty n_from n_edge n_to d
                          (Hres : expand Into n_from n_edge n_to d graph table = Some table')
                          (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table' (n_edge |-> Value.GEdgeT; ty).
  Proof.
  Admitted.


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

  Theorem filter_vertices_by_label_spec graph table table' n l v r 
                                      (Hres : filter_by_label Vertices n l graph table = Some table')
                                      (Hval : r n = Some (Value.GVertex v)) :
    In r table' <-> (In l (vlabels graph v) /\ In r table).
  Proof.
    autounfold with filter_by_label_db in Hres; desf.
    rewrite <- In_decb_true_iff.
    split; intros H.
    1: apply filter_In in H.
    2: apply filter_In; split.
    all: desf.
  Qed.

  Theorem filter_edges_by_label_spec graph table table' n l e r 
                                   (Hres : filter_by_label Edges n l graph table = Some table')
                                   (Hval : r n = Some (Value.GEdge e)) :
    In r table' <-> (elabel graph e = l /\ In r table).
  Proof.
    autounfold with filter_by_label_db in Hres; desf.
    rewrite <- equiv_decb_true_iff.
    split; intros H.
    1: apply filter_In in H.
    2: apply filter_In; split.
    all: desf.
  Qed.
End ExecutionPlanImpl.

