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

  
  Lemma type_of_UnknownT r k (Htype : type_of r k = Some Value.UnknownT) : 
    r k = Some Value.Unknown.
  Proof.
    unfold type_of in Htype.
    destruct (r k); try discriminate.
    f_equal. apply Value.type_of_UnknownT.
    now injection Htype as Htype.
  Qed.

  Ltac solve_type_of_T f :=
    match goal with
      Htype : type_of ?r ?k = Some ?T
      |- _ =>
        unfold type_of in Htype;
        destruct (r k) as [v |]; try discriminate;
        destruct (f v);
        [ now injection Htype as Htype |
        eexists; f_equal; eassumption ]
    end.
    
  Lemma type_of_BoolT r k (Htype : type_of r k = Some Value.BoolT) :
    exists b, r k = Some (Value.Bool b).
  Proof. solve_type_of_T Value.type_of_BoolT. Qed.

  Lemma type_of_IntT r k (Htype : type_of r k = Some Value.IntT) :
    exists i, r k = Some (Value.Int i).
  Proof. solve_type_of_T Value.type_of_IntT. Qed.

  Lemma type_of_StrT r k (Htype : type_of r k = Some Value.StrT) :
    exists s, r k = Some (Value.Str s).
  Proof. solve_type_of_T Value.type_of_StrT. Qed.

  Lemma type_of_GVertexT r k (Htype : type_of r k = Some Value.GVertexT) :
    exists v, r k = Some (Value.GVertex v).
  Proof. solve_type_of_T Value.type_of_GVertexT. Qed.

  Lemma type_of_GEdgeT r k (Htype : type_of r k = Some Value.GEdgeT) :
    exists e, r k = Some (Value.GEdge e).
  Proof. solve_type_of_T Value.type_of_GEdgeT. Qed.

  Lemma type_of_None r k (Htype : type_of r k = None) :
    r k = None.
  Proof.
    unfold type_of in Htype.
    destruct (r k); now try discriminate.
  Qed.

  #[global]
  Hint Rewrite type_of_BoolT type_of_IntT type_of_StrT type_of_GVertexT type_of_GEdgeT type_of_None : type_of_db.

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

  (* Predicate that defines the type of a table *)
  (* If a table if not-empty its type is defined *)
  Definition of_type (table : t) (ty : Rcd.T) :=
    forall r, In r table -> Rcd.type_of r = ty.

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

  Lemma of_type_cons_l (table : t) ty r (Htype : of_type (r :: table) ty) :
    Rcd.type_of r = ty.
  Proof.
    apply Htype. now left.
  Qed.

  Lemma of_type_cons_r (table : t) ty r (Htype : of_type (r :: table) ty) :
    of_type table ty.
  Proof.
    intros r' HIn. apply Htype.
    right. assumption.
  Qed.

  Lemma of_type_cons (table : t) ty r (Htype_r : Rcd.type_of r = ty)
                     (Htype_table : of_type table ty) :
    of_type (r :: table) ty.
  Proof.
    intros r' HIn. destruct HIn as [Heq | HIn].
    - now subst.
    - now apply Htype_table.
  Qed.

  Lemma of_type_concat (tables : list t) ty
                       (Htype : forall table, In table tables -> of_type table ty) :
    of_type (List.concat tables) ty.
  Proof.
    intros r HIn. apply in_concat in HIn. desf.
    eapply Htype; eassumption.
  Qed.

  (* The empty table is of any type *)
  Lemma empty_of_type ty : of_type empty ty.
  Proof. intros r HIn. inv HIn. Qed.

  Section type_ofT.
    Variable table : t.
    Variable ty : Rcd.T.
    Variable r : Rcd.t.
    Variable k : Pattern.name.
    Variable Htype : of_type table ty.
    Variable HIn : In r table.

    Lemma type_of_BoolT (Hty : ty k = Some Value.BoolT) :
      exists b, r k = Some (Value.Bool b).
    Proof using Htype HIn. apply Rcd.type_of_BoolT. rewrite Htype; assumption. Qed.

    Lemma type_of_IntT (Hty : ty k = Some Value.IntT) :
      exists i, r k = Some (Value.Int i).
    Proof using Htype HIn. apply Rcd.type_of_IntT. rewrite Htype; assumption. Qed.

    Lemma type_of_StrT (Hty : ty k = Some Value.StrT) :
      exists s, r k = Some (Value.Str s).
    Proof using Htype HIn. apply Rcd.type_of_StrT. rewrite Htype; assumption. Qed.

    Lemma type_of_GVertexT (Hty : ty k = Some Value.GVertexT) :
      exists v, r k = Some (Value.GVertex v).
    Proof using Htype HIn. apply Rcd.type_of_GVertexT. rewrite Htype; assumption. Qed.

    Lemma type_of_GEdgeT (Hty : ty k = Some Value.GEdgeT) :
      exists e, r k = Some (Value.GEdge e).
    Proof using Htype HIn. apply Rcd.type_of_GEdgeT. rewrite Htype; assumption. Qed.

    Lemma type_of_None (Hty : ty k = None) :
      r k = None.
    Proof using Htype HIn. apply Rcd.type_of_None. rewrite Htype; assumption. Qed.
  End type_ofT.

  #[global]
  Hint Unfold of_type : type_of_db.

  #[global]
  Hint Resolve of_type_cons of_type_cons_l of_type_cons_r empty_of_type : type_of_db.

  #[global]
  Hint Rewrite of_type_unique : type_of_db.

  #[global]
  Hint Rewrite type_of_BoolT type_of_IntT type_of_StrT type_of_GVertexT type_of_GEdgeT type_of_None : type_of_db.
End BindingTable.

#[global]
Hint Unfold update t_update Pattern.name equiv_decb
  BindingTable.of_type Rcd.type_of : unfold_pat.

Ltac solve_type_of := now (
  extensionality k;
  autounfold with unfold_pat in *;
  desf).

Ltac solve_type_of_extension r ty :=
  eenough (Rcd.type_of r = ty);
  [ solve_type_of | auto ].

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
        matches_vlabel : forall l, Pattern.vlabel p = Some l ->
          In l (PropertyGraph.vlabels g v);
      }.

    Record matches_pedge (e : edge) (p : pedge) : Prop := {
        matches_ename : r (Pattern.ename p) = Some (Value.GEdge e);
        matches_elabel : forall l, Pattern.elabel p = Some l ->
          PropertyGraph.elabel g e = l;
      }.

    Definition matches_direction (from to : vertex) (e : edge) (d : direction) : Prop :=
        match d with
        | OUT  => ends g e = (from, to)
        | IN   => ends g e = (to, from)
        | BOTH => ends g e = (from, to) \/ ends g e = (to, from)
        end.

    Definition matches_direction_dec (from to : vertex) (e : edge) (d : direction) :
      {matches_direction from to e d} + {~ matches_direction from to e d}.
    Proof.
      refine (
        match d with
        | OUT  => if (e_from g e == from) then
                    if (e_to g e == to)
                    then left _ else right _
                  else right _
        | IN   => if (e_from g e == to) then
                    if (e_to g e == from)
                    then left _ else right _
                  else right _
        | BOTH => if (e_from g e == from) then
                    if (e_to g e == to)
                    then left _ else right _
                  else
                    if (e_from g e == to) then
                      if (e_to g e == from)
                      then left _ else right _
                    else right _
        end
      ).
      all: unfold matches_direction, equiv, e_from, e_to in *.
      all: destruct (ends g e) as [from' to']; simpls.
      all: try by desf.
      all: try by intro; desf.
      all: auto.
    Defined.

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