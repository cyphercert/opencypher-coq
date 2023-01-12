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

Module ExecutionPlan.
  Definition step0 := PropertyGraph.t -> option BindingTable.t.
  Definition step1 := PropertyGraph.t -> BindingTable.t -> option BindingTable.t.

  Module Type Spec.
    (* scan_vertices (n : Pattern.name) : step0 *)
    Parameter scan_vertices : Pattern.name -> step0.

    (* filter_by_label (n : Pattern.name) (l : label) : step1 *)
    Parameter filter_by_label : Pattern.name -> label -> step1.

    (* expand_all (n_from n_edge n_to : Pattern.name) (d : Pattern.direction) : step1 *)
    Parameter expand_all : Pattern.name -> Pattern.name -> Pattern.name -> Pattern.direction -> step1.

    (* expand_into (n_from n_edge n_to : Pattern.name) (d : Pattern.direction) : step1 *)
    Parameter expand_into : Pattern.name -> Pattern.name -> Pattern.name -> Pattern.direction -> step1.


    (** If the inputs are well-formed then the operation will return the result *)

    Axiom scan_vertices_wf : forall n graph,
      PropertyGraph.wf graph ->
        exists table', scan_vertices n graph = Some table'.

    Axiom filter_by_label_wf : forall n l graph table ty,
      PropertyGraph.wf graph -> BindingTable.of_type table ty ->
        (ty n = Some Value.GVertexT \/ ty n = Some Value.GEdgeT) ->
          exists table', filter_by_label n l graph table = Some table'.

    Axiom expand_all_wf : forall n_from n_edge n_to d graph table ty,
      PropertyGraph.wf graph -> BindingTable.of_type table ty ->
        ty n_from = Some Value.GVertexT -> ty n_edge = None -> ty n_to = None ->
            exists table', expand_all n_from n_edge n_to d graph table = Some table'.
    
    Axiom expand_into_wf : forall n_from n_edge n_to d graph table ty,
      PropertyGraph.wf graph -> BindingTable.of_type table ty ->
        ty n_from = Some Value.GVertexT -> ty n_edge = None -> ty n_to = Some Value.GVertexT ->
          exists table', expand_into n_from n_edge n_to d graph table = Some table'.


    (** If the operation returned some table then the type of the table is correct *)

    Axiom scan_vertices_type : forall n graph table',
      scan_vertices n graph = Some table' ->
        BindingTable.of_type table' (n |-> Value.GVertexT).
    
    Axiom filter_by_label_type : forall n l graph table table' ty,
      filter_by_label n l graph table = Some table' ->
        BindingTable.of_type table ty ->
          BindingTable.of_type table' ty.

    Axiom expand_all_type : forall n_from n_edge n_to d graph table table' ty,
      expand_all n_from n_edge n_to d graph table = Some table' ->
        BindingTable.of_type table ty ->
          BindingTable.of_type table'
            (n_edge |-> Value.GEdgeT; n_to |-> Value.GVertexT; ty).

    Axiom expand_into_type : forall n_from n_edge n_to d graph table table' ty,
      expand_into n_from n_edge n_to d graph table = Some table' ->
        BindingTable.of_type table ty ->
          BindingTable.of_type table'
            (n_edge |-> Value.GEdgeT; ty).
  End Spec.

  Inductive t :=
  | ScanVertices (n : Pattern.name)
  | FilterByLabel (plan : t) (n : Pattern.name) (l : label)
  | ExpandAll (plan : t) (n_from n_edge n_to : Pattern.name) (d : Pattern.direction)
  | ExpandInto (plan : t) (n_from n_edge n_to : Pattern.name) (d : Pattern.direction)
  .

  Fixpoint dom (plan : t) : list Pattern.name := 
    match plan with
    | ScanVertices n => [ n ]
    | FilterByLabel plan n l => dom plan
    | ExpandAll plan n_from n_edge n_to d => n_edge :: n_to :: dom plan
    | ExpandInto plan n_from n_edge n_to d => n_edge :: dom plan
    end.

  Fixpoint type_of (plan : t) : BindingTable.T :=
    match plan with
    | ScanVertices n => n |-> Value.GVertexT
    | FilterByLabel plan n l => type_of plan
    | ExpandAll plan n_from n_edge n_to d => n_edge |-> Value.GEdgeT; n_to |-> Value.GVertexT; type_of plan
    | ExpandInto plan n_from n_edge n_to d => n_edge |-> Value.GEdgeT; type_of plan
    end.

  Fixpoint wf (plan : t) :=
    match plan with
    | ScanVertices n => True
    | FilterByLabel plan n l =>
      << Htype : type_of plan n = Some Value.GVertexT >> /\
      << Hwf : wf plan >>
    | ExpandAll plan n_from n_edge n_to d =>
      << Htype_from : type_of plan n_from = Some Value.GVertexT >> /\
      << Htype_edge : type_of plan n_edge = None >> /\
      << Htype_to : type_of plan n_to = None >> /\
      << Hneq_from : n_from =/= n_edge >> /\
      << Hneq_to : n_to =/= n_edge >> /\
      << Hwf : wf plan >>
    | ExpandInto plan n_from n_edge n_to d =>
      << Htype_from : type_of plan n_from = Some Value.GVertexT >> /\
      << Htype_edge : type_of plan n_edge = None >> /\
      << Htype_to : type_of plan n_to = Some Value.GVertexT >> /\
      << Hneq_from : n_from =/= n_edge >> /\
      << Hneq_to : n_to =/= n_edge >> /\
      << Hwf : wf plan >>
    end.

  (* Domain of the plan is the domain of resulting binding table *)
  Lemma dom__type_of (plan : t) (Hwf : wf plan) (n : Pattern.name) :
    In n (dom plan) <-> exists ty, type_of plan n = Some ty.
  Proof.
    induction plan; simpl in *.
    2: now apply IHplan.
    all: split; intros H; desf.
    - subst. rewrite update_eq. now exists (Value.GVertexT).
    - unfold update, t_update, Pattern.name in *.
      destruct (equiv_decbP n0 n); try discriminate H.
      now left.
    - rewrite update_eq. now exists (Value.GEdgeT).
    - rewrite update_neq; [| now symmetry ].
      rewrite update_eq. now exists (Value.GVertexT).
    - rewrite update_neq. rewrite update_neq.
      { now apply IHplan. }
      all: intros ?; rewrite IHplan in H; [| now assumption ]; desf.
    - unfold update, t_update, Pattern.name in *.
      destruct (equiv_decbP n_edge n), (equiv_decbP n_to n); subst; auto.
      right. right. apply IHplan; [ assumption | now exists ty ].
      - rewrite update_eq. now exists (Value.GEdgeT).
      - rewrite update_neq.
        { now apply IHplan. }
        intros ?; rewrite IHplan in H; [| now assumption ]; desf.
      - unfold update, t_update, Pattern.name in *.
        destruct (equiv_decbP n_edge n); subst; auto.
        right. apply IHplan; [ assumption | now exists ty ].
  Qed.
      

  Module EvalPlan (S : Spec).
    Import S.

    Section eval.
      Variable graph : PropertyGraph.t.
      Fixpoint eval (plan : ExecutionPlan.t) :=
        match plan with
        | ScanVertices n => scan_vertices n graph
        | FilterByLabel plan n l =>
          eval plan >>= filter_by_label n l graph
        | ExpandAll plan n_from n_edge n_to d => 
          eval plan >>= expand_all n_from n_edge n_to d graph
        | ExpandInto plan n_from n_edge n_to d => 
          eval plan >>= expand_into n_from n_edge n_to d graph
        end.
    End eval.

    Theorem eval_type_of plan graph table'
                         (Heval : eval graph plan = Some table') :
        BindingTable.of_type table' (type_of plan).
    Proof.
      generalize dependent table'.
      induction plan; intros table' Heval; simpl in *.
      { apply scan_vertices_type with graph. assumption. }
      all: destruct (eval graph plan) as [table |]; try discriminate Heval.
      - apply filter_by_label_type with n l graph table; auto.
      - apply expand_all_type with n_from d graph table; auto.
      - apply expand_into_type with n_from n_to d graph table; auto.
    Qed.

    Lemma type_of_types plan k :
      type_of plan k = Some Value.GVertexT \/
      type_of plan k = Some Value.GEdgeT \/
      type_of plan k = None.
    Proof.
      induction plan; simpl in *.
      all: try unfold update, t_update, Pattern.name in *.
      all: try (destruct (n ==b k)).
      all: try (destruct (n_edge ==b k)).
      all: try (destruct (n_to ==b k)).
      all: auto.
    Qed.

    Theorem eval_wf plan graph (Hwf : wf plan) (Hwf' : PropertyGraph.wf graph) :
        exists table', eval graph plan = Some table'.
    Proof.
      induction plan. all: simpl in *; desf.
      { apply scan_vertices_wf. assumption. }
      all: destruct IHplan as [table IH]; [ now assumption | ].
      all: rewrite IH.
      { 
        apply filter_by_label_wf with (type_of plan); try assumption. 
        - apply eval_type_of in IH. assumption.
        - assert (H' := type_of_types plan n). desf. auto.
      }
      1: apply expand_all_wf with (type_of plan); try assumption.
      2: apply expand_into_wf with (type_of plan); try assumption.
      all: apply eval_type_of in IH; assumption.
    Qed.
  End EvalPlan.
End ExecutionPlan.

Module ExecutionPlanImpl : ExecutionPlan.Spec.
  Definition scan_vertices (n : Pattern.name)
                        (graph : PropertyGraph.t)
                        : option BindingTable.t :=
    Some (map (fun v => n |-> Value.GVertex v) (vertices graph)).

  Definition filter_by_label (n : Pattern.name)
                             (l : PropertyGraph.label)
                             (graph : PropertyGraph.t)
                             (table : BindingTable.t)
                             : option BindingTable.t.
  Admitted.

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
End ExecutionPlanImpl.

