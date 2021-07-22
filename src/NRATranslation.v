From Coq Require Import String.
From Coq Require Import List.
Import ListNotations.

From OpencypherCoq Require Import Cypher.
From OpencypherCoq Require Import ForeignGraphRuntime.

From Qcert Require Import NRAEnv.Lang.NRAEnv.
From Qcert Require Import Data.Model.Data.
From Qcert Require Import Operators.UnaryOperators.
From Qcert Require Import Operators.BinaryOperators.

Import Pattern.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nraenv_scope.

Definition dot (s : string) : nraenv -> nraenv := NRAEnvUnop (OpDot s).

Definition const_coll : list data -> nraenv :=
  fold_right (fun x => NRAEnvBinop OpBagUnion (NRAEnvUnop OpBag (NRAEnvConst x))) (NRAEnvConst (dcoll nil)).

Definition const_tcoll (cname : string) (ds : list data) : nraenv := Eval hnf in
  const_coll (map (fun d => drec [(cname, d)]) ds).

(* Definition const_nat (n : nat) : nraenv := *)
(*   NRAEnvConst (dnat (BinInt.Z.of_nat n)). *)

Definition map_rename_rec (s1 s2:string) (e:nraenv) : nraenv :=
  NRAEnvMap ((NRAEnvBinop OpRecConcat)
                ((NRAEnvUnop (OpRec s2)) ((NRAEnvUnop (OpDot s1)) NRAEnvID))
                ((NRAEnvUnop (OpRecRemove s1)) NRAEnvID)) e.

Definition get_last_vname (p : Pattern.t) : string :=
  match p with
  | pvertex name _ => name
  | pedge _ _ _ _ name _ => name
  | pmultiedge _ _ _ _ _ _ name _ => name
  end.

Module NRAEnvNotations.

  Notation "x =% y" := (NRAEnvBinop OpEqual x y) (at level 70, no associativity) : nraenv_scope.
  Notation "x .% y" := (dot y x) (at level 30) : nraenv_scope.
  Notation "x 'elem%' y" := (NRAEnvBinop OpContains x y) (at level 70, no associativity) : nraenv_scope.
  (* Notation "'$E$'" := (NRAEnvGetConstant "edges"). *)
  (* Notation "'$V$'" := (NRAEnvGetConstant "vertices"). *)

End NRAEnvNotations.
Import NRAEnvNotations.

Definition vertex_to_nraenv (vname : string) (vlabels : list string) : nraenv :=
  map_rename_rec "vertex" vname
    (NRAEnvSelect
      (NRAEnvBinop OpEqual
        (const_coll nil)
        ((NRAEnvBinop OpBagDiff
          (const_tcoll "label" (map dstring vlabels))
          (NRAEnvID.%"vertex".%"labels"))))
      (NRAEnvGetConstant "vertices")).

(* Definition out_edge_to_nraenv (vvar : string) *)
(*                               (evar : string) (etypes : list string) *)
(*                               (wvar : string) (wlabels : list string) := *)
(*   NRAEnvNaturalJoin . *)

Definition expand (vname : string) (src : nraenv) (ename : string) (etype : list string)
  (wname : string) (trg : nraenv) : nraenv :=
  NRAEnvSelect (NRAEnvID.%ename.%"src" =% NRAEnvID.%vname.%"id")
    (NRAEnvNaturalJoin
      src
      (NRAEnvSelect (NRAEnvID.%ename.%"trg" =% NRAEnvID.%wname.%"id")
        (NRAEnvNaturalJoin
          (map_rename_rec "edge" ename
            (NRAEnvSelect
              (NRAEnvID.%"edge".%"type" elem% const_coll (map dstring etype))
              (NRAEnvGetConstant "edges")))
          trg))).

(* Maybe this will work for no repeated edge semantics. *)
(* Definition unique_expand (vname : string) (src : nraenv) (ename : string) (etype : list string) *)
(*   (wname : string) (trg : nraenv) (enames : list string) : nraenv := *)
(*   let rel := expand vname src ename etype wname trg in  *)
(*   NRAEnvSelect *)
(*     ((NRAEnvProject enames rel) =% (NRAEnvUnop OpDistinct (NRAEnvProject enames rel))) *)
(*     rel. *)

(* Fixpoint get_enames (p : Pattern.t) : list string := *)
(*   match p with  *)
(*   | Pattern.vertex _ _=> nil *)
(*   | Pattern.edge p ename _ _ _ _ => (ename :: get_enames (pattern)) *)
(*   | Pattern.multiedge p enames _ _ _ _ _ _ => *)
(*     (app enames (get_enames (pattern))) *)
(*   end. *)

Fixpoint pattern_to_nraenv (p : Pattern.t) : nraenv :=
  match p with
  | pvertex vvar vlabels => vertex_to_nraenv vvar vlabels
  (* No repeated edge semantics. *)
  | pedge p evar etypes edir wname wlabels =>
      let vname := get_last_vname p in
      match edir with
      | Pattern.OUT => expand vname (pattern_to_nraenv p) evar etypes wname (vertex_to_nraenv wname wlabels)
        (*unique_expand vname (pattern_to_nraenv pattern) evar etypes wname (vertex_to_nraenv wname wlabels) (evar :: (get_evars pattern))*)
      | Pattern.IN => expand wname (vertex_to_nraenv wname wlabels) evar etypes vname (pattern_to_nraenv p)
        (*unique_expand wname (vertex_to_nraenv wname wlabels) evar etypes vname (pattern_to_nraenv pattern) (evar :: (get_evars pattern))*)
      | Pattern.BOTH =>
        (NRAEnvBinop OpBagUnion
          (expand vname (pattern_to_nraenv p) evar etypes wname (vertex_to_nraenv wname wlabels))
          (*(unique_expand vname (pattern_to_nraenv pattern) evar etypes wname (vertex_to_nraenv wname wlabels) (evar :: (get_evars pattern)))*)
          (expand wname (vertex_to_nraenv wname wlabels) evar etypes vname (pattern_to_nraenv p)))
          (*(unique_expand wname (vertex_to_nraenv wname wlabels) evar etypes vname (pattern_to_nraenv pattern) (evar :: (get_evars pattern))))*)
      end
  | _ => NRAEnvConst dunit
  end.

Close Scope nraenv_scope.
Close Scope list_scope.
Close Scope string_scope.

(* Fixpoint clause_to_nraenv (clause : Clause.t) : nraenv := *)
(*   match clause with *)
(*   | MATCH patterns => match patterns with *)
(*     | [] => NRAEnvConst dcoll (dunit) *)
(*     | head :: tail => NRAEnvNaturalJoin (pattern_to_nraenv head) (clause_to_nraenv (MATCH tail)) *)
(*     end *)
(*   | WITH pexpr => (*Where is relation?*) *)
(*   end. *)

(* Fixpoint query_to_nraenv (query : Query.t) : nraenv := *)
(*   match query.(clauses) with *)
(*   | [] => NRAEnvConst dcoll (dunit) *)
(*   | head :: tail => NRAEnvNaturalJoin (clause_to_nraenv head) (query_to_nraenv tail) *)
(*   end. *)
