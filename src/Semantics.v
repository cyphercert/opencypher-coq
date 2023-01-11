Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Require Import Maps.
Require Import Cypher.
Require Import PropertyGraph.
Import PropertyGraph.

Module Value.
  Inductive t :=
  | Unknown
  | Bool (b : bool)
  | Int (i : Z)
  | Str (s : string)
  | GObj (go : gobj)
  .

  Search ({?x = ?y} + {?x <> ?y}).

  #[global]
  Program Instance int_eq_eqdec : EqDec Z eq := BinInt.Z.eq_dec.

  #[global]
  Program Instance string_eqdec : EqDec string eq := String.string_dec.

  Definition eq_value_dec (a b : t) : {a = b} + {a <> b}.
    refine (
      match a, b with
      | Unknown,          Unknown          => left _
      | Bool a,           Bool b           => if a == b then left _ else right _
      | Int a,            Int b            => if a == b then left _ else right _
      | Str a,            Str b            => if a == b then left _ else right _
      | GObj (gvertex a), GObj (gvertex b) => if a == b then left _ else right _
      | GObj (gedge a),   GObj (gedge b)   => if a == b then left _ else right _
      | _,                _                => right _
      end
    );
    try reflexivity; (* Solve Unknown = Unknown *)
    try discriminate; (* Solve goals with different constructors *)
    repeat f_equal; try assumption;  (* Solve goals when underlying values are equal *)
    intros H; injection H as H; contradiction. (* Solve goals when underlying values are not equal *)
  Defined.

  #[global]
  Program Instance value_eqdec : EqDec t eq := eq_value_dec.

  Definition eqb (a b : t) : bool := a ==b b.
End Value.

(* Record / Assignment *)
Module Rcd.
  Definition t := string -> option Value.t.

  (* Predicate that defines the domain of a record *)
  Definition in_dom (k : string) (r : t) :=
    exists v, r k = Some v.

  Definition disjoint (r1 r2 : t) : Prop := 
    forall k, r1 k = None \/ r2 k = None.

  Definition matches_pattern_dom (r : t) (pattern : Pattern.t) :=
    forall k, in_dom k r <-> In k (Pattern.dom pattern).

  Section join.
    Definition join (r1 r2 : t) : t := fun k =>
      match r1 k with
      | Some val => Some val
      | None     => r2 k
      end.


    Lemma join_comm' : forall r1 r2,
      disjoint r1 r2 -> forall k, (join r1 r2) k = (join r2 r1) k.
    Proof.
      intros r1 r2 H k.
      unfold join.
      destruct (H k) as [H1 | H2].
      - rewrite H1. destruct (r2 k); reflexivity.
      - rewrite H2. destruct (r1 k); reflexivity.
    Qed.

    Lemma join_comm : forall r1 r2,
      disjoint r1 r2 -> join r1 r2 = join r2 r1.
    Proof.
      intros r1 r2 H.
      extensionality k.
      apply join_comm'. apply H.
    Qed.
  End join.
End Rcd.

Module BindingTable.
  Definition t := list Rcd.t.

  Definition empty : t := nil.
  Definition add (r : Rcd.t) (T : t) := r :: T.

  (* Binding table is well-formed iff all the records have the same domain *)
  Definition wf (T : t) := forall r1 r2,
    In r1 T -> In r2 T -> forall k, Rcd.in_dom k r1 <-> Rcd.in_dom k r2.

  (* Predicate that defines the domain of a table *)
  Definition in_dom (k : string) (T : t) :=
    match T with
    | r :: _ => Rcd.in_dom k r
    | nil => False
    end.

  (* The domain of a well-formed table is the same as
     the domain of any of its records *)
  Lemma in_dom_wf : forall T r,
    wf T -> In r T -> forall k, in_dom k T <-> Rcd.in_dom k r.
  Proof.
    intros T r Hwf HIn k.
    destruct T as [| r1 ?].
    - inversion HIn.
    - apply Hwf.
      + left. reflexivity.
      + apply HIn.
  Qed.
End BindingTable.

Module Path.

  Inductive t :=
  | start (v : vertex)
  | hop (p : t) (e : edge) (v : vertex).

  Definition hd (p : t) :=
    match p with
    | hop _ _ v => v
    | start v => v
    end.

  Section matches.
    Import Pattern.

    Variable g : PropertyGraph.t.
    Variable u : Rcd.t.

    Record matches_pvertex (v : vertex) (p : pvertex) : Prop := {
        matches_vname : u (Pattern.vname p) = Some (Value.GObj (gvertex v));
        matches_vlabels : Pattern.vlabels p = nil \/ exists l, In l (Pattern.vlabels p) /\ In l (PropertyGraph.vlabels g v);
        matches_vprops : forall prop, In prop (Pattern.vprops p) -> In prop (PropertyGraph.vprops g v);
      }.

    Record matches_pedge (e : edge) (p : pedge) : Prop := {
        matches_ename : u (Pattern.ename p) = Some (Value.GObj (gedge e));
        matches_elabels : Pattern.elabels p = nil \/ In (PropertyGraph.elabel g e) (Pattern.elabels p);
        matches_eprops : forall prop, In prop (Pattern.eprops p) -> In prop (PropertyGraph.eprops g e);
      }.

    Definition matches_direction (s t : vertex) (e : edge) (d : direction) : Prop :=
        match d with
        | OUT  => ends g e = (s, t)
        | IN   => ends g e = (t, s)
        | BOTH => ends g e = (s, t) \/ ends g e = (t, s)
        end.

    Inductive matches : Path.t -> Pattern.t -> Prop :=
    | matches_nil (pv : pvertex) (v : vertex) 
      : matches_pvertex v pv -> 
        matches (Path.start v) (Pattern.start pv) 
    | matches_cons (v : vertex) (e : edge) (p : Path.t)
                  (pv : pvertex) (pe : pedge) (pi : Pattern.t) 
      : matches p pi ->
        matches_pedge e pe ->
        matches_direction v (Path.hd p) e (Pattern.edir pe) ->
        matches_pvertex v pv ->
        matches (Path.hop p e v) (Pattern.hop pi pe pv)
    .
  End matches.
  
  (* r' is expanded from r by traversing one edge *)
  Definition expansion_of (g : PropertyGraph.t) (r' r : Rcd.t)
                          (n_from n_edge n_to : Pattern.name)
                          (d : Pattern.direction) :=
    exists v_from e v_to, In e (edges g) /\
      r n_from = Some (Value.GObj (gvertex v_to)) /\
      matches_direction g v_from v_to e d /\
      r' = (n_to |-> Value.GObj (gvertex v_to); n_edge |-> Value.GObj (gedge e); r).

End Path.

(* Notation "g , u , p '|=' pi" := (Path.matches g u p pi) (at level 80, p at next level, u at next level, pi at next level, no associativity) : type_scope. *)

Section QueryExpr.
  Import QueryExpr.
  Import Value.

  Section eval_qexpr.
    Variable g : PropertyGraph.t.
    Variable u : Rcd.t.

    Fixpoint eval_qexpr (a : QueryExpr.t) : option Value.t :=
      match a with
      | QEGObj go => Some (GObj go)

      | QEVar n => u n

      | QEProj a k =>
        match eval_qexpr a with
        | Some (GObj go) =>
            match get_gobj_prop g k go with
            | Some val =>
              match val with
              | Property.p_int i => Some (Int i)
              | Property.p_string s => Some (Str s)
              end
            | None => Some Unknown
            end
        | _       => None
        end

      | QEEq a1 a2  =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (b1 ==b b2))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (i1 ==b i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (s1 ==b s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QENe a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (b1 <>b b2))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (i1 <>b i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (s1 <>b s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QELe a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (implb b1 b2))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.leb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.leb s1 s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QEGe a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (implb b2 b1))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.geb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.leb s2 s1))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QELt a1 a2  =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (negb (implb b2 b1)))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.ltb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.ltb s1 s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QEGt a1 a2  =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (negb (implb b1 b2)))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.gtb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.ltb s2 s1))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end
      
      | QETrue    => Some (Bool true)
      | QEFalse   => Some (Bool false)
      | QEUnknown => Some Unknown

      | QEOr a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool true),  Some (Bool true)  => Some (Bool true)
        | Some (Bool true),  Some (Bool false) => Some (Bool true)
        | Some (Bool false), Some (Bool true)  => Some (Bool true)
        | Some (Bool false), Some (Bool false) => Some (Bool false)

        | Some (Bool true),  Some Unknown      => Some (Bool true)
        | Some (Bool false), Some Unknown      => Some Unknown
        | Some Unknown,      Some (Bool true)  => Some (Bool true)
        | Some Unknown,      Some (Bool false) => Some Unknown
        | Some Unknown,      Some Unknown      => Some Unknown

        | _, _ => None
        end

      | QEAnd a1 a2 => 
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool true),  Some (Bool true)  => Some (Bool true)
        | Some (Bool true),  Some (Bool false) => Some (Bool false)
        | Some (Bool false), Some (Bool true)  => Some (Bool false)
        | Some (Bool false), Some (Bool false) => Some (Bool false)

        | Some (Bool true),  Some Unknown      => Some Unknown
        | Some (Bool false), Some Unknown      => Some (Bool false)
        | Some Unknown,      Some (Bool true)  => Some Unknown
        | Some Unknown,      Some (Bool false) => Some (Bool false)
        | Some Unknown,      Some Unknown      => Some Unknown
        
        | _, _ => None
        end

      | QEXor a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool true),  Some (Bool true)  => Some (Bool false)
        | Some (Bool true),  Some (Bool false) => Some (Bool true)
        | Some (Bool false), Some (Bool true)  => Some (Bool true)
        | Some (Bool false), Some (Bool false) => Some (Bool false)

        | Some (Bool true),  Some Unknown      => Some Unknown
        | Some (Bool false), Some Unknown      => Some Unknown
        | Some Unknown,      Some (Bool true)  => Some Unknown
        | Some Unknown,      Some (Bool false) => Some Unknown
        | Some Unknown,      Some Unknown      => Some Unknown
        
        | _, _ => None
        end

      | QENot a => 
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some Unknown
        | _                 => None
        end

      | QEIsUnknown a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool false)
        | Some Unknown      => Some (Bool true)
        | _                 => None
        end

      | QEIsNotUnknown a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool true)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some (Bool false)
        | _                 => None
        end

      | QEIsTrue a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool true)
        | Some (Bool false) => Some (Bool false)
        | Some Unknown      => Some (Bool false)
        | _                 => None
        end

      | QEIsNotTrue a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some (Bool true)
        | _                 => None
        end

      | QEIsFalse a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some (Bool false)
        | _                 => None
        end

      | QEIsNotFalse a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool true)
        | Some (Bool false) => Some (Bool false)
        | Some Unknown      => Some (Bool true)
        | _                 => None
        end
      end.
  End eval_qexpr.
End QueryExpr.

Module EvalQuerySpec.
  Record t := mk_spec {
    eval_clause : PropertyGraph.t -> Clause.t -> BindingTable.t -> option BindingTable.t;
    eval_query : PropertyGraph.t -> Query.t -> option BindingTable.t;

    match_clause_eval : forall g path pattern table r,
      BindingTable.wf table ->
        exists table', eval_clause g (Clause.MATCH pattern) table = Some table' /\
          In r table' <->
            Path.matches g r path pattern /\
            Rcd.matches_pattern_dom r pattern /\
            exists r1 r2,
              r = Rcd.join r1 r2 /\ 
              Rcd.disjoint r1 r2 /\
              In r1 table;

    query_eval : forall g q,
      Query.wf q ->
        eval_query g q = eval_clause g (Query.clause q) (BindingTable.empty);
  }.
End EvalQuerySpec.