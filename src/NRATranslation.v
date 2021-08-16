Require Import String.
Require Import List.
Import ListNotations.

Require Import Cypher.
Require Import ForeignGraphRuntime.

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

Definition get_last_vvar (p : Pattern.t) : string :=
  match p with
  | pvertex vvar _ => vvar
  | pedge _ _ _ _ vvar _ => vvar
  | pmultiedge _ _ _ _ _ _ vvar _ => vvar
  end.

Module NRAEnvNotations.

  Notation "x =% y" := (NRAEnvBinop OpEqual x y) (at level 70, no associativity) : nraenv_scope.
  Notation "x .% y" := (dot y x) (at level 30) : nraenv_scope.
  Notation "x 'elem%' y" := (NRAEnvBinop OpContains x y) (at level 70, no associativity) : nraenv_scope.
  (* Notation "'$E$'" := (NRAEnvGetConstant "edges"). *)
  (* Notation "'$V$'" := (NRAEnvGetConstant "vertices"). *)

End NRAEnvNotations.
Import NRAEnvNotations.

Definition vertex_to_nraenv (vvar : string) (vlabels : list string) : nraenv :=
  map_rename_rec "vertex" vvar
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

Definition expand (vvar : string) (src : nraenv) (evar : string) (etypes : list string)
  (wvar : string) (trg : nraenv) : nraenv :=
  NRAEnvSelect (NRAEnvID.%evar.%"src" =% NRAEnvID.%vvar.%"id")
    (NRAEnvNaturalJoin
      src
      (NRAEnvSelect (NRAEnvID.%evar.%"trg" =% NRAEnvID.%wvar.%"id")
        (NRAEnvNaturalJoin
          (map_rename_rec "edge" evar
            (NRAEnvSelect
              (NRAEnvID.%"edge".%"type" elem% const_coll (map dstring etypes))
              (NRAEnvGetConstant "edges")))
          trg))).

(* Maybe this will work for no repeated edge semantics. *)
(* Definition unique_expand (vvar : string) (src : nraenv) (evar : string) (etypes : list string) *)
(*   (wvar : string) (trg : nraenv) (enames : list string) : nraenv := *)
(*   let rel := expand vvar src evar etypes wvar trg in  *)
(*   NRAEnvSelect *)
(*     ((NRAEnvProject enames rel) =% (NRAEnvUnop OpDistinct (NRAEnvProject enames rel))) *)
(*     rel. *)

(* Fixpoint get_enames (p : Pattern.t) : list string := *)
(*   match p with  *)
(*   | Pattern.vertex _ _=> nil *)
(*   | Pattern.edge p evar _ _ _ _ => (evar :: get_enames (pattern)) *)
(*   | Pattern.multiedge p enames _ _ _ _ _ _ => *)
(*     (app enames (get_enames (pattern))) *)
(*   end. *)

Fixpoint pattern_to_nraenv (p : Pattern.t) : nraenv :=
  match p with
  | pvertex vvar vlabels => vertex_to_nraenv vvar vlabels
  (* No repeated edge semantics. *)
  | pedge p evar etypes edir wvar wlabels =>
      let vvar := get_last_vvar p in
      match edir with
      | Pattern.OUT => expand vvar (pattern_to_nraenv p) evar etypes wvar (vertex_to_nraenv wvar wlabels)
        (*unique_expand vvar (pattern_to_nraenv pattern) evar etypes wvar (vertex_to_nraenv wvar wlabels) (evar :: (get_evars pattern))*)
      | Pattern.IN => expand wvar (vertex_to_nraenv wvar wlabels) evar etypes vvar (pattern_to_nraenv p)
        (*unique_expand wvar (vertex_to_nraenv wvar wlabels) evar etypes vvar (pattern_to_nraenv pattern) (evar :: (get_evars pattern))*)
      | Pattern.BOTH =>
        (NRAEnvBinop OpBagUnion
          (expand vvar (pattern_to_nraenv p) evar etypes wvar (vertex_to_nraenv wvar wlabels))
          (*(unique_expand vvar (pattern_to_nraenv pattern) evar etypes wvar (vertex_to_nraenv wvar wlabels) (evar :: (get_evars pattern)))*)
          (expand wvar (vertex_to_nraenv wvar wlabels) evar etypes vvar (pattern_to_nraenv p)))
          (*(unique_expand wvar (vertex_to_nraenv wvar wlabels) evar etypes vvar (pattern_to_nraenv pattern) (evar :: (get_evars pattern))))*)
      end
  | pmultiedge p evar etypes edir low up wvar wlabels => NRAEnvConst dunit
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
