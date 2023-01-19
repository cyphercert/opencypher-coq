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
              (n_edge |-> Value.GEdgeT; n_to |-> Value.GVertexT; ty).

      Axiom expand_into_type : forall n_from n_edge n_to d,
        expand Into n_from n_edge n_to d graph table = Some table' ->
          BindingTable.of_type table ty ->
            BindingTable.of_type table'
              (n_edge |-> Value.GEdgeT; ty).

      (** scan_vertices specification *)

      Axiom scan_vertices_spec : forall n v,
        scan_vertices n graph = Some table' ->
          (exists r, In r table' /\ r n = Some (Value.GVertex v)) <->
              In v (vertices graph).

      (** filter_by_label specification *)

      Axiom filter_vertices_by_label_spec : forall n l v r,
        filter_by_label Vertices n l graph table = Some table' ->
          In l (vlabels graph v) -> In r table -> r n = Some (Value.GVertex v) ->
            (exists r', In r' table' /\ r' n = Some (Value.GVertex v)).

      Axiom filter_vertices_by_label_spec' : forall n l v r',
        filter_by_label Edges n l graph table = Some table' ->
          In r' table' -> r' n = Some (Value.GVertex v) ->
            In l (vlabels graph v) /\ exists r, In r table /\ r n = Some (Value.GVertex v).

      Axiom filter_edges_by_label_spec : forall n l e r,
        filter_by_label Edges n l graph table = Some table' ->
          In r table -> elabel graph e = l -> r n = Some (Value.GEdge e) ->
            (exists r', In r' table' /\ r' n = Some (Value.GEdge e)).

      Axiom filter_edges_by_label_spec' : forall n l e r',
        filter_by_label Edges n l graph table = Some table' ->
          In r' table' -> r' n = Some (Value.GEdge e) ->
            elabel graph e = l /\ exists r, In r table /\ r n = Some (Value.GEdge e).

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
    | Expand All n_from n_edge n_to d plan => n_edge |-> Value.GEdgeT; n_to |-> Value.GVertexT; type_of plan
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
                        (graph : PropertyGraph.t)
                        : option BindingTable.t :=
    Some (map (fun v => n |-> Value.GVertex v) (vertices graph)).

  Section filter_vertices_by_label.
    Variable n : Pattern.name.
    Variable l : PropertyGraph.label.
    Variable graph : PropertyGraph.t.

    Fixpoint filter_vertices_by_label (table : BindingTable.t)
      : option BindingTable.t :=
      match table with
      | nil => Some nil
      | r :: table =>
        match r n, filter_vertices_by_label table with
        | Some (Value.GVertex v), Some table' =>
            if In_dec l (vlabels graph v)
            then Some (r :: table') else Some table'
        | _, _ => None
        end
      end.
  End filter_vertices_by_label.

  Section filter_edges_by_label.
    Variable n : Pattern.name.
    Variable l : PropertyGraph.label.
    Variable graph : PropertyGraph.t.

    Fixpoint filter_edges_by_label (table : BindingTable.t)
      : option BindingTable.t :=
      match table with
      | nil => Some nil
      | r :: table =>
        match r n, filter_edges_by_label table with
        | Some (Value.GEdge e), Some table' =>
            if elabel graph e == l
            then Some (r :: table') else Some table'
        | _, _ => None
        end
      end.
  End filter_edges_by_label.

  Definition filter_by_label (mode : FilterMode.t)
                             (n : Pattern.name)
                             (l : PropertyGraph.label)
                             (graph : PropertyGraph.t)
                             (table : BindingTable.t)
                             : option BindingTable.t :=
    match mode with
    | Vertices => filter_vertices_by_label n l graph table
    | Edges => filter_edges_by_label n l graph table
    end.

  Definition expand_all (n_from n_edge n_to : Pattern.name)
                        (d : Pattern.direction)
                        (graph : PropertyGraph.t)
                        (table : BindingTable.t)
                        : option BindingTable.t.
  Admitted.

  Definition expand_into (n_from n_edge n_to : Pattern.name)
                         (d : Pattern.direction)
                         (graph : PropertyGraph.t)
                         (table : BindingTable.t)
                         : option BindingTable.t :=
    expand_all n_from n_edge n_to d graph table.

  Definition expand (mode : ExpandMode.t)
                    (n_from n_edge n_to : Pattern.name)
                    (d : Pattern.direction)
                    (graph : PropertyGraph.t)
                    (table : BindingTable.t)
                    : option BindingTable.t :=
    match mode with
    | All => expand_all n_from n_edge n_to d graph table
    | Into => expand_into n_from n_edge n_to d graph table
    end.

  (** If the inputs are well-formed then the operation will return the result *)

  Lemma scan_vertices_wf graph n (Hwf : PropertyGraph.wf graph) :
    exists table', scan_vertices n graph = Some table'.
  Proof.
    now eexists.
  Qed.

  Lemma filter_vertices_by_label_wf graph table ty n l
                                    (Hwf : PropertyGraph.wf graph)
                                    (Htype : BindingTable.of_type table ty)
                                    (Hty : ty n = Some Value.GVertexT) :
    exists table', filter_vertices_by_label n l graph table = Some table'.
  Proof.
    induction table as [| r table IH]; ins; eauto.
    assert (exists v, r n = Some (Value.GVertex v)) as [v Hval].
    { apply Rcd.type_of_GVertexT; rewrite Htype; auto. now left. }
    rewrite Hval.
    destruct IH as [table' IH]; eauto.
    rewrite IH. desf; eauto.
  Qed.

  Lemma filter_edges_by_label_wf graph table ty n l
                                 (Hwf : PropertyGraph.wf graph)
                                 (Htype : BindingTable.of_type table ty)
                                 (Hty : ty n = Some Value.GEdgeT) :
    exists table', filter_edges_by_label n l graph table = Some table'.
  Proof.
    induction table as [| r table IH]; ins; eauto.
    assert (exists e, r n = Some (Value.GEdge e)) as [e Hval].
    { apply Rcd.type_of_GEdgeT; rewrite Htype; auto; now left. }
    rewrite Hval.
    destruct IH as [table' IH]; eauto.
    rewrite IH. desf; eauto.
  Qed.

  (** If the operation returned some table then the type of the table is correct *)

  #[local]
  Hint Unfold update t_update Pattern.name equiv_decb
    BindingTable.of_type Rcd.type_of : unfold_pat.
  
  Lemma scan_vertices_type graph table' n 
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
  
  Lemma filter_by_label_type graph table table' ty mode n l
                             (Hres : filter_by_label mode n l graph table = Some table')
                             (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table' ty.
  Proof.
    generalize dependent table'.
    destruct mode.
    all: induction table; ins; desf; eauto.
  Qed.

  (** scan_vertices specification *)

  Definition scan_vertices_spec graph table' n v 
                                (Hres : scan_vertices n graph = Some table') :
    (exists r, In r table' /\ r n = Some (Value.GVertex v)) <->
      In v (vertices graph).
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

  Lemma filter_vertices_by_label_spec graph table table' n l v r 
                                      (Hres : filter_by_label Vertices n l graph table = Some table')
                                      (HIn_l : In l (vlabels graph v)) (HIn : In r table)
                                      (Hval : r n = Some (Value.GVertex v)) :
    exists r', In r' table' /\ r' n = Some (Value.GVertex v).
  Proof.
    generalize dependent table'.
    all: induction table as [| r0 table IH];
           simpls; intros table' Hres; desf.

    (* r = r0 *)
    { exists r. split; eauto. now left. }

    (* r <> r0 *)
    all: edestruct IH as [r' [HIn' Hval']]; eauto.
    eexists; split; eauto. now right.
  Qed.

  Lemma filter_edges_by_label_spec graph table table' n l e r 
                                   (Hres : filter_by_label Edges n l graph table = Some table')
                                   (HIn_l : elabel graph e = l) (HIn : In r table)
                                   (Hval : r n = Some (Value.GEdge e)) :
    exists r', In r' table' /\ r' n = Some (Value.GEdge e).
  Proof.
    generalize dependent table'.
    all: induction table as [| r0 table IH];
           simpl in *; intros table' Hres; desf.

    (* r = r0 *)
    { exists r. split; [now left | assumption]. }

    (* r <> r0 *)
    all: edestruct IH as [r' [HIn' Hval']]; eauto.
  (*   all: eexists; split; [ right; eassumption | assumption ]. *)
  (* Qed. *)
  Admitted.

  Lemma filter_by_label_spec_v' graph table table' n l v r'
                               (Hres : filter_by_label n l graph table = Some table')
                               (HIn' : In r' table')
                               (Hval' : r' n = Some (Value.GVertex v)) :
    In l (vlabels graph v) /\ exists r, In r table /\ r n = Some (Value.GVertex v).
  Proof.
    generalize dependent table'.
    induction table as [| r0 table IH];
      simpl in *; intros table' Hres; desf.
    all: split; try assumption.
    all: unfold equiv in *; subst.

    (* Solve goals of the form (In l _) *)
    all: try match goal with
             |- In _ _ =>
                try destruct HIn';
                try subst; try congruence;
                edestruct IH; auto
             end.

    { destruct HIn'; subst. exists r'.
      - split; [now left | assumption].
      - edestruct IH as [? [? [? ?]]]; auto. eexists.
       split; [right; eassumption | assumption]. }
    all: try destruct HIn'; subst.
    all: try congruence.
    all: try edestruct IH as [? [? [? ?]]]; auto.
    all: eexists; split; auto.
    2: {}

    (* r <> r0 *)
    all: edestruct IH as [r' [HIn' Hval']]; eauto.
    all: eexists; split; [ right; eassumption | assumption ].
  Qed.
(* 
  Lemma filter_by_label_spec_e graph table table' n l e
                               (Hres : filter_by_label n l graph table = Some table') :
      (exists r', In r' table' /\ r' n = Some (Value.GEdge e)) <->
        (exists r, In r table /\ r n = Some (Value.GEdge e)) /\ elabel graph e = l.
  Admitted. *)
End ExecutionPlanImpl.

