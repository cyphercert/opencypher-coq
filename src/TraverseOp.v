Require Import Utils.
Require Import Maps.
Require Import PropertyGraph.
Require Import Cypher.
Require Import BindingTable.
Require Import Semantics.
Require Import PatternE.
Require Import ExecutionPlan.

Import PartialMap.Notations.
Import TotalMap.Notations.
Import PropertyGraph.
Import ExecutionPlan.
Import FilterMode.
Import ExpandMode.
Import MatchMode.
Import UpdateNotations.

Module TraverseOpImpl.
  Definition traverse : PatternSlice.t -> Name.t -> step1.
  Admitted.

  Theorem traverse_wf : forall graph table ty slice n_from,
    PropertyGraph.wf graph -> BindingTable.of_type table ty ->
      PatternSlice.wf ty slice -> ty n_from = Some Value.GVertexT ->
        exists table', traverse slice n_from graph table = Some table'.
  Admitted.

  Theorem traverse_type : forall graph table table' ty slice n_from,
    traverse slice n_from graph table = Some table' ->
      BindingTable.of_type table ty ->
        BindingTable.of_type table' (PatternSlice.type_of ty slice).
  Admitted.

  Theorem traverse_spec : forall graph table table' path r r' slice n_from,
    traverse slice n_from graph table = Some table' ->
      PathSlice.matches graph r n_from r' path slice ->
        In r table -> In r' table'.
  Admitted.

  Theorem traverse_spec' : forall graph table table' r' slice n_from,
    traverse slice n_from graph table = Some table' ->
      In r' table' -> exists r path, In r table /\
        PathSlice.matches graph r n_from r' path slice.
  Admitted.
End TraverseOpImpl.