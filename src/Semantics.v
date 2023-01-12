Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From hahn Require Import HahnBase.

Require Import Maps.
Require Import Utils.
Require Import Cypher.
Require Import PropertyGraph.
Import PropertyGraph.

Module Value.
  Inductive t :=
  | Unknown
  | Bool (b : bool)
  | Int (i : Z)
  | Str (s : string)
  | GVertex (v : vertex)
  | GEdge (e : edge)
  .

  Inductive T :=
  | UnknownT
  | BoolT
  | IntT
  | StrT 
  | GVertexT
  | GEdgeT
  .

  Definition type_of (v : t) : T :=
    match v with
    | Unknown   => UnknownT
    | Bool _    => BoolT
    | Int _     => IntT
    | Str _     => StrT
    | GVertex _ => GVertexT
    | GEdge _   => GEdgeT
    end.

  Lemma type_of_UnknownT v (H : type_of v = UnknownT) : 
    v = Unknown.
  Proof. destruct v; try discriminate. reflexivity. Qed.

  Lemma type_of_BoolT : forall v,
    type_of v = BoolT -> exists b, v = Bool b.
  Proof. intros v H. destruct v; try discriminate. exists b. reflexivity. Qed.

  Lemma type_of_IntT : forall v,
    type_of v = IntT -> exists i, v = Int i.
  Proof. intros v H. destruct v; try discriminate. exists i. reflexivity. Qed.

  Lemma type_of_StrT : forall v,
    type_of v = StrT -> exists s, v = Str s.
  Proof. intros v H. destruct v; try discriminate. exists s. reflexivity. Qed.

  Lemma type_of_GVertexT : forall v,
    type_of v = GVertexT -> exists v', v = GVertex v'.
  Proof. intros v H. destruct v; try discriminate. exists v. reflexivity. Qed.

  Lemma type_of_GEdgeT : forall v,
    type_of v = GEdgeT -> exists e, v = GEdge e.
  Proof. intros v H. destruct v; try discriminate. exists e. reflexivity. Qed.

  Definition from_property (x : Property.t) : Value.t :=
    match x with
    | Property.p_int i => Int i
    | Property.p_string s => Str s
    end.

  Definition eq_value_dec (a b : t) : {a = b} + {a <> b}.
    refine (
      match a, b with
      | Unknown,          Unknown          => left _
      | Bool a,           Bool b           => if a == b then left _ else right _
      | Int a,            Int b            => if a == b then left _ else right _
      | Str a,            Str b            => if a == b then left _ else right _
      | GVertex a,        GVertex b        => if a == b then left _ else right _
      | GEdge a,          GEdge b          => if a == b then left _ else right _
      | _,                _                => right _
      end
    );
    try reflexivity; (* Solve Unknown = Unknown *)
    try discriminate; (* Solve goals with different constructors *)
    try f_equal; try assumption;  (* Solve goals when underlying values are equal *)
    injection as H; contradiction. (* Solve goals when underlying values are not equal *)
  Defined.

  #[global]
  Program Instance value_eqdec : EqDec t eq := eq_value_dec.

  Definition eqb (a b : t) : bool := a ==b b.
End Value.

(* Record / Assignment *)
Module Rcd.
  Definition t := Pattern.name -> option Value.t.
  Definition T := Pattern.name -> option Value.T.

  Definition empty : t := fun _ => None.
  Definition emptyT : T := fun _ => None.

  Definition type_of (r : t) : T :=
    fun k => option_map Value.type_of (r k).

  Lemma type_of_empty : type_of empty = emptyT.
  Proof. reflexivity. Qed.

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
      destruct (H k); desf.
    Qed.

    Lemma join_comm : forall r1 r2,
      disjoint r1 r2 -> join r1 r2 = join r2 r1.
    Proof.
      intros r1 r2 ?.
      extensionality k.
      now apply join_comm'.
    Qed.
  End join.
End Rcd.

Module BindingTable.
  Definition t := list Rcd.t.
  Definition T := Rcd.T.

  Definition empty : t := nil.
  Definition add (r : Rcd.t) (T : t) := r :: T.

  (* Binding table is well-formed iff all the records have the same type *)
  Definition wf (table : t) := forall r1 r2,
    In r1 table -> In r2 table -> Rcd.type_of r1 = Rcd.type_of r2.

  (* Predicate that defines the type of a table *)
  (* If a table if not-empty its type is defined *)
  Definition of_type (table : t) (ty : Rcd.T) :=
    forall r, In r table -> Rcd.type_of r = ty.

  (* The type of a well-formed table is the same as
    the type of any of its records *)
  Lemma wf_of_type (table : t) (Hwf : wf table) r (HIn : In r table) :
    of_type table (Rcd.type_of r).
  Proof.
    intros r' HIn'.
    unfold wf in Hwf. apply Hwf. apply HIn'. apply HIn.
  Qed.

  (* A type exists if the table is well-formed *)
  Lemma of_type_exists (table : t) (Hwf : wf table) :
    exists ty, of_type table ty.
  Proof.
    destruct table as [| r ?].
    - exists Rcd.emptyT. intros r' HIn. inversion HIn.
    - exists (Rcd.type_of r). apply wf_of_type. apply Hwf.
      left. reflexivity.
  Qed.

  (* If a type exists, the table is well-formed *)
  Lemma of_type_wf table ty (Htype : of_type table ty) : wf table.
  Proof.
    intros r1 r2 HIn1 HIn2.
    transitivity ty; [| symmetry].
    all: apply Htype.
    all: assumption.
  Qed.

  (* If a table is not empty, the type is unique *)
  Lemma of_type_unique (table : t) ty1 ty2 (Hneq : table <> nil)
                       (Htype1 : of_type table ty1) (Htype2 : of_type table ty2) :
    ty1 = ty2.
  Proof.
    destruct table as [| r].
    { contradiction. }
    transitivity (Rcd.type_of r).
    1: symmetry; apply Htype1.
    2: apply Htype2.
    all: left; reflexivity.
  Qed.

  (* The empty table is of any type *)
  Lemma empty_of_type ty : of_type empty ty.
  Proof. intros r HIn. inv HIn. Qed.

  (* The empty table is well-formed *)
  Lemma empty_wf : wf empty.
  Proof. intros r1 r2 HIn1 HIn2. inv HIn1. Qed.

  (* Predicate that defines the domain of a table *)
  Definition in_dom (k : string) (T : t) :=
    match T with
    | r :: _ => Rcd.in_dom k r
    | nil => False
    end.

  (* (* The domain of a well-formed table is the same as
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
  Qed. *)
End BindingTable.

Module Path.

  Inductive t :=
  | start (v : vertex)
  | hop (p : t) (e : edge) (v : vertex).

  Definition last (p : t) :=
    match p with
    | hop _ _ v => v
    | start v => v
    end.

  Section matches.
    Import Pattern.

    Variable g : PropertyGraph.t.
    Variable r : Rcd.t.

    Record matches_pvertex (v : vertex) (p : pvertex) : Prop := {
        matches_vname : r (Pattern.vname p) = Some (Value.GVertex v);
        matches_vlabels : << Hnil : Pattern.vlabels p = nil >> \/
          exists l, << HIn_pattern : In l (Pattern.vlabels p) >> /\
                    << HIn_graph : In l (PropertyGraph.vlabels g v) >>;
        matches_vprops : forall prop (HIn : In prop (Pattern.vprops p)),
          In prop (PropertyGraph.vprops g v);
      }.

    Record matches_pedge (e : edge) (p : pedge) : Prop := {
        matches_ename : r (Pattern.ename p) = Some (Value.GEdge e);
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
                  (Hpv : matches_pvertex v pv) :
        matches (Path.start v) (Pattern.start pv) 
    | matches_cons (v : vertex) (e : edge) (p : Path.t)
                   (pv : pvertex) (pe : pedge) (pi : Pattern.t) 
                   (Hpi : matches p pi) (Hpe : matches_pedge e pe)
                   (Hdir : matches_direction (Path.last p) v e (Pattern.edir pe))
                   (Hpv : matches_pvertex v pv) :
        matches (Path.hop p e v) (Pattern.hop pi pe pv)
    .
  End matches.
  
  (* r' is expanded from r by traversing one edge *)
  Definition expansion_of (g : PropertyGraph.t) (r' r : Rcd.t)
                          (n_from n_edge n_to : Pattern.name)
                          (d : Pattern.direction) :=
    exists v_from e v_to, In e (edges g) /\
      r n_from = Some (Value.GVertex v_to) /\
      matches_direction g v_from v_to e d /\
      r' = (n_to |-> Value.GVertex v_to; n_edge |-> Value.GEdge e; r).

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
      | QEGObj go =>
        match go with
        | gvertex v => Some (GVertex v)
        | gedge e => Some (GEdge e)
        end

      | QEVar n => u n

      | QEProj a k => option_map Value.from_property
        match eval_qexpr a with
        | Some (GVertex v) => get_vprop g k v
        | Some (GEdge e) => get_eprop g k e
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