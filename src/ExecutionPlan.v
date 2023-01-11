Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Require Import Cypher.
Require Import Semantics.
Require Import PropertyGraph.
Require Import Maps.
Import PropertyGraph.

Module ExecutionPlan.
  Inductive t :=
  | ScanNodes (n : Pattern.name)
  | FilterByLabel (plan : t) (go : gobj) (l : label)
  | ExpandAll (plan : t) (n_from n_edge n_to : Pattern.name) (d : Pattern.direction)
  | ExpandInto (plan : t) (n_from n_edge n_to : Pattern.name) (d : Pattern.direction)
  .

  (* Domain of the plan is the domain of resulting binding table *)
  Fixpoint dom (plan : t) : list Pattern.name := 
    match plan with
    | ScanNodes n => [ n ]
    | FilterByLabel plan go l => dom plan
    | ExpandAll plan n_from n_edge n_to d => n_from :: n_edge :: n_to :: dom plan
    | ExpandInto plan n_from n_edge n_to d => n_from :: n_edge :: n_to :: dom plan
    end.

  Fixpoint wf (plan : t) :=
    match plan with
    | ScanNodes n => True
    | FilterByLabel plan go l => wf plan
    | ExpandAll plan n_from n_edge n_to d =>
      In n_from (dom plan) /\ ~(In n_edge (dom plan)) /\ ~(In n_to (dom plan)) /\ wf plan
    | ExpandInto plan n_from n_edge n_to d =>
      In n_from (dom plan) /\ ~(In n_edge (dom plan)) /\ In n_to (dom plan) /\ wf plan
    end.

  Record spec := mk_spec {
    eval : ExecutionPlan.t -> PropertyGraph.t -> option BindingTable.t;

    eval_wf : forall plan graph,
      wf plan -> exists table, eval plan graph = Some table /\ BindingTable.wf table;

    eval_ScanNodes_spec : forall graph n,
      exists table, eval (ScanNodes n) graph = Some table /\
        table = map (fun v => n |-> Value.GObj (gvertex v)) (vertices graph);

    eval_FilterByLabel_spec : forall graph plan go l table,
      let plan' := FilterByLabel plan go l in
        wf plan' -> eval plan graph = Some table ->
            exists table', eval plan' graph = Some table' /\
              forall r, In r table' <->
                (In r table /\ In l (get_gobj_labels graph go));

    eval_ExpandAll_spec : forall graph plan n_from n_edge n_to d table,
      let plan' := ExpandAll plan n_from n_edge n_to d in
        PropertyGraph.wf graph -> wf plan' ->
          eval plan graph = Some table ->
            exists table', eval plan' graph = Some table' /\
              forall r', In r' table' <-> (exists r,
                In r table /\ Path.expansion_of graph r' r n_from n_edge n_to d);

    eval_ExpandInto_spec : forall graph plan n_from n_edge n_to d table,
      let plan' := ExpandInto plan n_from n_edge n_to d in
        PropertyGraph.wf graph -> wf plan' ->
          eval plan graph = Some table ->
            exists table', eval plan' graph = Some table' /\
              forall r', In r' table' <-> (exists r,
                In r table /\ Path.expansion_of graph r' r n_from n_edge n_to d);
  }.
End ExecutionPlan.

Module ExecutionPlanImpl.
  Definition scan_nodes (n : Pattern.name)
                        (graph : PropertyGraph.t)
                        (table : BindingTable.t)
                        : option BindingTable.t :=
    Some (map (fun v => n |-> Value.GObj (gvertex v)) (vertices graph)).

  Definition filter_by_label (plan : ExecutionPlan.t)
                             (go : gobj) (l : PropertyGraph.label)
                             (graph : PropertyGraph.t)
                             (table : BindingTable.t)
                             : option BindingTable.t.
  Admitted.

  Definition expand_all (plan : ExecutionPlan.t)
                        (n_from n_edge n_to : Pattern.name)
                        (d : Pattern.direction)
                        (graph : PropertyGraph.t)
                        (table : BindingTable.t)
                        : option BindingTable.t.
  Admitted.

  Definition expand_into (plan : ExecutionPlan.t)
                         (n_from n_edge n_to : Pattern.name)
                         (d : Pattern.direction)
                         (graph : PropertyGraph.t)
                         (table : BindingTable.t)
                         : option BindingTable.t :=
    expand_all plan n_from n_edge n_to d graph table.
End ExecutionPlanImpl.

