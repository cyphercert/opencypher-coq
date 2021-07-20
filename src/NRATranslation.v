From Coq Require Import String.
From Coq Require Import List.

From OpencypherCoq Require Import Cypher.
From OpencypherCoq Require Import ForeignGraphRuntime.

From Qcert Require Import NRAEnv.Lang.NRAEnv.
From Qcert Require Import Data.Model.Data.
From Qcert Require Import Operators.UnaryOperators.
From Qcert Require Import Operators.BinaryOperators.

Definition dot (s : string) : nraenv -> nraenv := NRAEnvUnop (OpDot s).

(* Definition all (bs : nraenv) : nraenv := *)

Open Scope string_scope.

Definition const_coll : list data -> nraenv :=
  fold_right (fun x => NRAEnvBinop OpBagUnion (NRAEnvConst x)) (NRAEnvConst (dcoll nil)).

(* Definition const_nat (n : nat) : nraenv := *)
(*   NRAEnvConst (dnat (BinInt.Z.of_nat n)). *)

Definition map_rename_rec (s1 s2:string) (e:nraenv) : nraenv :=
  NRAEnvMap ((NRAEnvBinop OpRecConcat)
                ((NRAEnvUnop (OpRec s2)) ((NRAEnvUnop (OpDot s1)) NRAEnvID))
                ((NRAEnvUnop (OpRecRemove s1)) NRAEnvID)) e.

 Definition get_vname (pattern : Pattern.t) : string := 
   match pattern with
   | Pattern.vertex vname _ => vname
   | Pattern.edge _ _ _ _ wname _=> wname 
   | Pattern.multiedge _ _ _ _ _ _ wname _ => wname
   end.

Notation "x '==' y" := (NRAEnvBinop OpEqual x y) (at level 70, no associativity). 

Definition vertex_to_nraenv (vname : string) (vlabels : list label) := 
  map_rename_rec "vertex" vname
        (NRAEnvSelect
          (NRAEnvBinop OpEqual
            (const_coll nil)
            ((NRAEnvBinop OpBagDiff
              (const_coll (map (fun l => drec (("label", dstring l) :: nil)) vlabels))
              (dot "labels" (dot "vertex" NRAEnvID)))))
          (NRAEnvGetConstant "vertices")).

Fixpoint pattern_to_nraenv (p : Pattern.t) : nraenv :=
  match p with
  | Pattern.vertex vname vlabels =>
      vertex_to_nraenv vname vlabels
  (*No repeated edge semantics.*)
  | Pattern.edge pattern ename etype edirection wname wlabels =>
      let vname := get_vname pattern in
      NRAEnvJoin 
        (match edirection with
        | Pattern.OUT => dot "src" (dot ename NRAEnvID) == dot "id" (dot vname NRAEnvID)
        | Pattern.IN => dot "trg" (dot ename NRAEnvID) == dot "id" (dot vname NRAEnvID)
        | Pattern.BOTH => NRAEnvConst dunit
        end)
        (pattern_to_nraenv pattern)
        (NRAEnvJoin 
          (match edirection with
          | Pattern.OUT => dot "trg" (dot ename NRAEnvID) == dot "id" (dot wname NRAEnvID)
          | Pattern.IN => dot "src" (dot ename NRAEnvID) == dot "id" (dot wname NRAEnvID)
          | Pattern.BOTH => NRAEnvBinop OpOr (dot "src" (dot ename NRAEnvID) == dot "id" (dot wname NRAEnvID))
            (dot "trg" (dot ename NRAEnvID) == dot "id" (dot wname NRAEnvID))
          end)
          (map_rename_rec "edge" ename
            (NRAEnvSelect
              (NRAEnvBinop 
                OpContains (const_coll (map dstring etype)) (dot "type" (dot "edge" NRAEnvID)))
              (NRAEnvGetConstant "edges")))
          (vertex_to_nraenv wname wlabels))
  | _ => NRAEnvConst dunit
  end.

Fixpoint clause_to_nraenv (clause : Clause.t) : nraenv :=
  match clause with
  | MATCH patterns => match patterns with
    | [] => NRAEnvConst dcoll (dunit)
    | head :: tail => NRAEnvNaturalJoin (pattern_to_nraenv head) (clause_to_nraenv (MATCH tail))
    end
  | WITH pexpr => (*Where is relation?*)
  end.

Fixpoint query_to_nraenv (query : Query.t) : nraenv :=
  match query.(clauses) with
  | [] => NRAEnvConst dcoll (dunit)
  | head :: tail => NRAEnvNaturalJoin (clause_to_nraenv head) (query_to_nraenv tail)
  end.
