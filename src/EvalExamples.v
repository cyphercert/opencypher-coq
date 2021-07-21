From Coq Require Import String.
From Coq Require Import List.
Import ListNotations.

From OpencypherCoq Require Import ForeignGraphRuntime.
From OpencypherCoq Require Import Cypher.
From OpencypherCoq Require Import PropertyGraph.
From OpencypherCoq Require Import PGTableExtraction.
From OpencypherCoq Require Import NRATranslation.

From Qcert Require Import Data.Model.Data.
From Qcert Require Import Lang.NRAEnv.

Open Scope string_scope.

Definition mk_const_env (pg : PropertyGraph.t) : bindings :=
  [ ("vertices", pg_extract_vtable pg)
  ; ("edges", pg_extract_etable pg)
  ].

Definition eval_pattern (p : Pattern.t) (pg : PropertyGraph.t) : option data :=
  nraenv_eval_top nil (pattern_to_nraenv p) (mk_const_env pg).

Definition evals_to_sem (p : Pattern.t) (pg : PropertyGraph.t) : data -> Prop :=
  nraenv_sem nil (mk_const_env pg) (pattern_to_nraenv p) (drec nil) dunit.

Lemma sem : evals_to_sem Pattern.pattern1 PropertyGraph.property_graph1 dunit.
(* Proof. *)
(*   red. *)
(*   vm_compute. *)

(* Lemma kek : (eval_pattern Pattern.pattern1 PropertyGraph.property_graph1) = Some dunit. *)
(* Proof. *)
(*   unfold eval_pattern. *)
(*   vm_compute (pg_extract_vtable _). *)
(*   vm_compute (pattern_to_nraenv _). *)
(*   assert (pattern_to_nraenv Pattern.pattern1 = NRAEnvID). *)
(*   cbv. *)
(*   (* Definition kek := pattern_to_nraenv Pattern.pattern1. *) *)
(*   remember (pattern_to_nraenv Pattern.pattern1) as expr. *)
(*   . *)
(*   vm_compute in Heqexpr. *)
(*   . *)
