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
Import PartialMap.Notations.
Import TotalMap.Notations.

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
  Proof using. destruct v; try discriminate. reflexivity. Qed.

  Lemma type_of_BoolT : forall v,
    type_of v = BoolT -> exists b, v = Bool b.
  Proof using. intros v H. destruct v; try discriminate. exists b. reflexivity. Qed.

  Lemma type_of_IntT : forall v,
    type_of v = IntT -> exists i, v = Int i.
  Proof using. intros v H. destruct v; try discriminate. exists i. reflexivity. Qed.

  Lemma type_of_StrT : forall v,
    type_of v = StrT -> exists s, v = Str s.
  Proof using. intros v H. destruct v; try discriminate. exists s. reflexivity. Qed.

  Lemma type_of_GVertexT : forall v,
    type_of v = GVertexT -> exists v', v = GVertex v'.
  Proof using. intros v H. destruct v; try discriminate. exists v. reflexivity. Qed.

  Lemma type_of_GEdgeT : forall v,
    type_of v = GEdgeT -> exists e, v = GEdge e.
  Proof using. intros v H. destruct v; try discriminate. exists e. reflexivity. Qed.

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
    ).
    all: try reflexivity. (* Solve Unknown = Unknown *)
    all: try discriminate. (* Solve goals with different constructors *)
    all: try now f_equal.  (* Solve goals when underlying values are equal *)
    all: injection as H; contradiction. (* Solve goals when underlying values are not equal *)
  Defined.

  Definition eq_type_dec (a b : T) : {a = b} + {a <> b}.
    destruct a, b.
    all: try now left.
    all: now right.
  Defined.

  Definition eq_opt_type_dec (a b : option T) : {a = b} + {a <> b}.
    destruct a, b.
    all: try now left.
    all: try now right.
    edestruct eq_type_dec.
    { left. f_equal. eassumption. }
    right. congruence.
  Defined.

  #[global]
  Program Instance value_eqdec : EqDec t eq := eq_value_dec.

  #[global]
  Program Instance type_eqdec : EqDec T eq := eq_type_dec.

  #[global]
  Program Instance opt_type_eqdec : EqDec (option T) eq := eq_opt_type_dec.

  Definition eqb (a b : t) : bool := a ==b b.
End Value.

(* Record / Assignment *)
Module Rcd.
  Definition t := PartialMap.t Name.t Value.t.
  Definition T := PartialMap.t Name.t Value.T.

  Definition empty : t := fun _ => None.
  Definition emptyT : T := fun _ => None.

  Definition type_of (r : t) : T :=
    fun k => option_map Value.type_of (r k).

  Lemma type_of_empty : type_of empty = emptyT.
  Proof using. reflexivity. Qed.

  Lemma type_of_t_update r k v :
    type_of (k !-> v; r) = (k !-> option_map Value.type_of v; type_of r).
  Proof using.
    extensionality k'.
    unfold type_of, TotalMap.update, equiv_decb.
    desf.
  Qed.

  Lemma type_of_update r k v :
    type_of (k |-> v; r) = (k |-> Value.type_of v; type_of r).
  Proof using.
    unfold PartialMap.update.
    now rewrite type_of_t_update.
  Qed.

  Lemma type_of_singleton k v :
    type_of (k |-> v) = (k |-> Value.type_of v).
  Proof using.
    unfold PartialMap.update.
    now rewrite type_of_t_update.
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

  Lemma type_of_UnknownT r k (Htype : type_of r k = Some Value.UnknownT) : 
    r k = Some Value.Unknown.
  Proof using. solve_type_of_T Value.type_of_UnknownT. Qed.
    
  Lemma type_of_BoolT r k (Htype : type_of r k = Some Value.BoolT) :
    exists b, r k = Some (Value.Bool b).
  Proof using. solve_type_of_T Value.type_of_BoolT. Qed.

  Lemma type_of_IntT r k (Htype : type_of r k = Some Value.IntT) :
    exists i, r k = Some (Value.Int i).
  Proof using. solve_type_of_T Value.type_of_IntT. Qed.

  Lemma type_of_StrT r k (Htype : type_of r k = Some Value.StrT) :
    exists s, r k = Some (Value.Str s).
  Proof using. solve_type_of_T Value.type_of_StrT. Qed.

  Lemma type_of_GVertexT r k (Htype : type_of r k = Some Value.GVertexT) :
    exists v, r k = Some (Value.GVertex v).
  Proof using. solve_type_of_T Value.type_of_GVertexT. Qed.

  Lemma type_of_GEdgeT r k (Htype : type_of r k = Some Value.GEdgeT) :
    exists e, r k = Some (Value.GEdge e).
  Proof using. solve_type_of_T Value.type_of_GEdgeT. Qed.

  Lemma type_of_None r k (Htype : type_of r k = None) :
    r k = None.
  Proof using.
    unfold type_of in Htype.
    destruct (r k); now try discriminate.
  Qed.

  #[global]
  Hint Rewrite type_of_BoolT type_of_IntT type_of_StrT type_of_GVertexT type_of_GEdgeT type_of_None : type_of_db.

  Lemma in_dom_iff k r :
    PartialMap.in_dom k r <-> PartialMap.in_dom k (type_of r).
  Proof using.
    unfold PartialMap.in_dom, type_of.
    split.
    { intros [v H]. eexists. now rewrite H. }
    { intros [x H]. destruct (r k); try inv H. now eexists. }
  Qed.

  Section join.
    Lemma type_of_join r1 r2 :
      type_of (PartialMap.join r1 r2) = PartialMap.join (type_of r1) (type_of r2).
    Proof using.
      extensionality k.
      unfold PartialMap.join, type_of, option_map.
      desf.
    Qed.

    Lemma type_of_disjoint_iff r1 r2 :
      PartialMap.disjoint (type_of r1) (type_of r2) <-> PartialMap.disjoint r1 r2.
    Proof using.
      unfold PartialMap.disjoint, type_of, option_map.
      split.
      all: intros Hdisj k.
      all: specialize Hdisj with k.
      all: desf; auto.
    Qed.

    Lemma type_of_disjoint (r1 r2 : t) (Hdisj : PartialMap.disjoint r1 r2) :
      PartialMap.disjoint (type_of r1) (type_of r2).
    Proof using. now apply type_of_disjoint_iff. Qed.
  End join.

  Definition explicit_proj (r : t) : t := fun k =>
    match k with
    | Name.explicit _ => r k
    | _ => None
    end.

  Definition explicit_projT (r : T) : T := fun k =>
    match k with
    | Name.explicit _ => r k
    | _ => None
    end.

  Theorem explicit_proj_empty : explicit_proj empty = empty.
  Proof.
    extensionality k.
    unfold explicit_proj, empty.
    desf.
  Qed.

  Theorem explicit_projT_emptyT : explicit_projT emptyT = emptyT.
  Proof.
    extensionality k.
    unfold explicit_projT, emptyT.
    desf.
  Qed.

  Theorem type_of_explicit_proj r :
    type_of (explicit_proj r) = explicit_projT (type_of r).
  Proof using.
    extensionality k.
    unfold explicit_proj, explicit_projT.
    desf.
  Qed.
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
  Proof using.
    destruct table as [| r].
    { contradiction. }
    transitivity (Rcd.type_of r).
    1: symmetry; apply Htype1.
    2: apply Htype2.
    all: left; reflexivity.
  Qed.

  Lemma of_type_cons_l (table : t) ty r (Htype : of_type (r :: table) ty) :
    Rcd.type_of r = ty.
  Proof using.
    apply Htype. now left.
  Qed.

  Lemma of_type_cons_r (table : t) ty r (Htype : of_type (r :: table) ty) :
    of_type table ty.
  Proof using.
    intros r' HIn. apply Htype.
    right. assumption.
  Qed.

  Lemma of_type_cons (table : t) ty r (Htype_r : Rcd.type_of r = ty)
                     (Htype_table : of_type table ty) :
    of_type (r :: table) ty.
  Proof using.
    intros r' HIn. destruct HIn as [Heq | HIn].
    - now subst.
    - now apply Htype_table.
  Qed.

  Lemma of_type_concat (tables : list t) ty
                       (Htype : forall table, In table tables -> of_type table ty) :
    of_type (List.concat tables) ty.
  Proof using.
    intros r HIn. apply in_concat in HIn. desf.
    eapply Htype; eassumption.
  Qed.

  (* The empty table is of any type *)
  Lemma empty_of_type ty : of_type empty ty.
  Proof using. intros r HIn. inv HIn. Qed.

  Section type_ofT.
    Variable table : t.
    Variable ty : Rcd.T.
    Variable r : Rcd.t.
    Variable k : Name.t.
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

  Definition equiv (table1 table2 : t) :=
    forall r, In r table1 <-> In r table2.

  #[global]
  Instance equiv_Equivalence : Equivalence equiv.
  Proof using.
    constructor; red; intros.
    all: unfold equiv; firstorder.
  Qed.

  Module Notations.
    Notation "t1 ~~ t2" := (equiv t1 t2) (at level 70).
  End Notations.
End BindingTable.

#[global]
Hint Unfold PartialMap.update TotalMap.update equiv_decb
  BindingTable.of_type Rcd.type_of : unfold_pat.

Ltac desf_unfold_pat :=
  autounfold with unfold_pat in *; desf; simpls;
  unfold complement, equiv in *; subst; auto.

Ltac solve_type_of := now (
  extensionality k;
  autounfold with unfold_pat in *;
  desf).

Ltac solve_type_of_extension r ty :=
  eenough (Rcd.type_of r = ty);
  [ solve_type_of | auto ].