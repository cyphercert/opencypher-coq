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
    ).
    all: try reflexivity. (* Solve Unknown = Unknown *)
    all: try discriminate. (* Solve goals with different constructors *)
    all: try now f_equal.  (* Solve goals when underlying values are equal *)
    all: injection as H; contradiction. (* Solve goals when underlying values are not equal *)
  Defined.

  #[global]
  Program Instance value_eqdec : EqDec t eq := eq_value_dec.

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
  Proof. reflexivity. Qed.

  Lemma type_of_t_update r k v :
    type_of (k !-> v; r) = (k !-> option_map Value.type_of v; type_of r).
  Proof.
    extensionality k'.
    unfold type_of, TotalMap.update, equiv_decb.
    desf.
  Qed.

  Lemma type_of_update r k v :
    type_of (k |-> v; r) = (k |-> Value.type_of v; type_of r).
  Proof.
    unfold PartialMap.update.
    now rewrite type_of_t_update.
  Qed.

  Lemma type_of_singleton k v :
    type_of (k |-> v) = (k |-> Value.type_of v).
  Proof.
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
  Proof. solve_type_of_T Value.type_of_UnknownT. Qed.
    
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

  Lemma in_dom_iff k r :
    PartialMap.in_dom k r <-> PartialMap.in_dom k (type_of r).
  Proof.
    unfold PartialMap.in_dom, type_of.
    split.
    { intros [v H]. eexists. now rewrite H. }
    { intros [x H]. destruct (r k); try inv H. now eexists. }
  Qed.

  Definition matches_pattern_dom (r : t) (pattern : Pattern.t) :=
    forall k, PartialMap.in_dom k r <-> In k (Pattern.dom pattern).

  Section join.
    Lemma type_of_join r1 r2 :
      type_of (PartialMap.join r1 r2) = PartialMap.join (type_of r1) (type_of r2).
    Proof.
      extensionality k.
      unfold PartialMap.join, type_of, option_map.
      desf.
    Qed.

    Lemma type_of_disjoint_iff r1 r2 :
      PartialMap.disjoint (type_of r1) (type_of r2) <-> PartialMap.disjoint r1 r2.
    Proof.
      unfold PartialMap.disjoint, type_of, option_map.
      split.
      all: intros Hdisj k.
      all: specialize Hdisj with k.
      all: desf; auto.
    Qed.

    Lemma type_of_disjoint (r1 r2 : t) (Hdisj : PartialMap.disjoint r1 r2) :
      PartialMap.disjoint (type_of r1) (type_of r2).
    Proof. now apply type_of_disjoint_iff. Qed.
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

Module PatternT.
  Definition T := Rcd.T.

  Fixpoint type_of (pi : Pattern.t) : T :=
    match pi with
    | Pattern.start pv =>
        (Pattern.vname pv |-> Value.GVertexT)
    | Pattern.hop pi pe pv =>
        (Pattern.vname pv |-> Value.GVertexT; Pattern.ename pe |-> Value.GEdgeT; type_of pi)
    end.

  Lemma type_of__dom_vertices (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi)
    (HIn : In nv (Pattern.dom_vertices pi)) :
      type_of pi nv = Some Value.GVertexT.
  Proof.
    induction pi; simpls.
    all: desf.
    all: try apply PartialMap.update_eq.

    desf_unfold_pat.
    { exfalso; eapply Pattern.wf__pe__dom_vertices; eauto. }
    eauto with pattern_wf_db.
  Qed.

  Lemma type_of__dom_edges (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi)
    (HIn : In ne (Pattern.dom_edges pi)) :
      type_of pi ne = Some Value.GEdgeT.
  Proof.
    induction pi; simpls.
    all: desf.
    all: rewrite PartialMap.update_neq.
    all: try apply PartialMap.update_eq.
    all: try rewrite PartialMap.update_neq.
    all: eauto with pattern_wf_db.
    
    all: intro; subst.
    { eapply Pattern.wf__pe__dom_edges; eauto. }
    { eapply Pattern.wf__pv__dom_edges; eauto. }
  Qed.

  Lemma dom_vertices__type_of (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi)
    (Htype : type_of pi nv = Some Value.GVertexT) :
      In nv (Pattern.dom_vertices pi).
  Proof.
    induction pi; simpls.
    all: desf_unfold_pat.
    all: eauto with pattern_wf_db.
  Qed.

  Lemma dom_edges__type_of (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi)
    (Htype : type_of pi ne = Some Value.GEdgeT) :
      In ne (Pattern.dom_edges pi).
  Proof.
    induction pi; simpls.
    all: desf_unfold_pat.
    all: eauto with pattern_wf_db.
  Qed.

  Theorem In_dom_vertices__iff (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi) :
      In nv (Pattern.dom_vertices pi) <-> type_of pi nv = Some Value.GVertexT.
  Proof.
    split; eauto using type_of__dom_vertices, dom_vertices__type_of.
  Qed.

  Theorem In_dom_edges__iff (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi) :
      In ne (Pattern.dom_edges pi) <-> type_of pi ne = Some Value.GEdgeT.
  Proof.
    split; eauto using type_of__dom_edges, dom_edges__type_of.
  Qed.

  Theorem type_of__types (pi : Pattern.t) k :
      type_of pi k = Some Value.GVertexT \/
      type_of pi k = Some Value.GEdgeT \/
      type_of pi k = None.
  Proof.
    induction pi; simpls.
    all: desf_unfold_pat.
    all: eauto with pattern_wf_db.
  Qed.

  Theorem In_dom__iff (pi : Pattern.t) k
    (Hwf : Pattern.wf pi) :
      In k (Pattern.dom pi) <-> PartialMap.in_dom k (type_of pi).
  Proof.
    rewrite Pattern.In_dom.
    rewrite In_dom_vertices__iff, In_dom_edges__iff; auto.
    unfold PartialMap.in_dom.
    split; ins.
    all: desf; eauto.
    edestruct type_of__types as [? | [? | ?]]; eauto.
    congruence.
  Qed.

  Corollary not_In_dom__iff (pi : Pattern.t) k
    (Hwf : Pattern.wf pi) :
      ~ (In k (Pattern.dom pi)) <-> type_of pi k = None.
  Proof.
    rewrite In_dom__iff; auto.
    now rewrite PartialMap.not_in_dom_iff.
  Qed.

  Corollary matches_pattern_dom__if (pi : Pattern.t) r
    (Hwf : Pattern.wf pi)
    (Htype : Rcd.type_of r = type_of pi) :
      Rcd.matches_pattern_dom r pi.
  Proof.
    unfold Rcd.matches_pattern_dom; ins.
    rewrite Rcd.in_dom_iff, Htype.
    now rewrite In_dom__iff.
  Qed.

  Lemma wf__type_of_pe pi pe pv
    (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
      type_of pi (Pattern.ename pe) = None.
  Proof.
    rewrite <- not_In_dom__iff. 
    all: eauto with pattern_wf_db.
  Qed.

  Lemma wf__type_of_pv__None pi pe pv
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (HIn : ~ In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      type_of pi (Pattern.vname pv) = None.
  Proof.
    rewrite <- not_In_dom__iff. 
    all: eauto with pattern_wf_db.
  Qed.

  Lemma wf__type_of_pv__Some pi pe pv
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (HIn : In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      type_of pi (Pattern.vname pv) = Some Value.GVertexT.
  Proof.
    rewrite <- In_dom_vertices__iff. 
    all: eauto with pattern_wf_db.
  Qed.

  #[global]
  Hint Resolve wf__type_of_pe wf__type_of_pv__None wf__type_of_pv__Some : patternT_wf_db.

End PatternT.

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
        vertex_in_g : In v (PropertyGraph.vertices g);
        matches_vname : r (Pattern.vname p) = Some (Value.GVertex v);
        matches_vlabel : forall l, Pattern.vlabel p = Some l ->
          In l (PropertyGraph.vlabels g v);
      }.

    Record matches_pedge (e : edge) (p : pedge) : Prop := {
        edge_in_g : In e (PropertyGraph.edges g);
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

    Definition ends_match_decb (e : edge) (from to : vertex) : bool :=
      ends g e ==b (from, to).

    Definition matches_direction_decb (from to : vertex) (e : edge) (d : direction) : bool :=
        match d with
        | OUT   => ends_match_decb e from to
        | IN    => ends_match_decb e to from
        | BOTH  => ends_match_decb e from to || ends_match_decb e to from
        end.

    Definition matches_direction_dec (from to : vertex) (e : edge) (d : direction) :
      {matches_direction from to e d} + {~ matches_direction from to e d}.
    Proof.
      refine (
        if matches_direction_decb from to e d == true
        then left _ else right _
      ).
      all: unfold matches_direction_decb, matches_direction,
                  ends_match_decb, equiv, complement in *.
      all: desf.
      all: try rewrite -> orb_true_iff in e0.
      all: try rewrite -> orb_true_iff in c.
      all: repeat rewrite -> equiv_decb_true_iff in e0.
      all: repeat rewrite -> equiv_decb_true_iff in c.
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

  Lemma matches_in_dom graph path pi r' n
    (Hmatch : matches graph r' path pi)
    (HIn : In n (Pattern.dom pi)) :
      PartialMap.in_dom n r'.
  Proof.
    unfold PartialMap.in_dom.
    induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: simpls; desf.
    all: eauto.
  Qed.

  Lemma matches_in_dom_contra graph path pi r' n
    (Hmatch : matches graph r' path pi)
    (Hval : r' n = None) :
      ~ In n (Pattern.dom pi).
  Proof.
    intro contra.
    eapply matches_in_dom in contra; eauto.
    unfold PartialMap.in_dom in contra.
    desf.
  Qed.

  Lemma matches_last graph path pi r'
    (Hmatch : matches graph r' path pi) :
      r' (Pattern.vname (Pattern.last pi)) = Some (Value.GVertex (Path.last path)).
  Proof.
    destruct pi. 
    all: inv Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: eauto.
  Qed.

  Lemma matches_exclude graph path pi r' n x
    (Hmatch : matches graph r' path pi)
    (HIn : ~ In n (Pattern.dom pi)) :
      matches graph (n !-> x; r') path pi.
  Proof.
    induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    1: apply matches_nil.
    2: apply matches_cons.
    all: try apply IHHmatch.
    all: try (intro; apply HIn; right; now right).
    all: try apply Path.Build_matches_pvertex.
    all: try apply Path.Build_matches_pedge.
    all: auto.
    all: desf_unfold_pat.
    all: exfalso; auto.
  Qed.
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

      | QEVar n => u (Name.explicit n)

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

Module EvalQuery.
  Module Type Spec.
    Parameter eval_match_clause : PropertyGraph.t -> Pattern.t -> option BindingTable.t.

    Axiom match_clause_wf : forall graph pattern,
      PropertyGraph.wf graph -> Pattern.wf pattern ->
        exists table', eval_match_clause graph pattern = Some table'.

    Axiom match_clause_type : forall graph pattern table' r',
      eval_match_clause graph pattern = Some table' ->
        Pattern.wf pattern -> In r' table' ->
          Rcd.type_of r' = PatternT.type_of pattern.

    Axiom match_clause_spec : forall graph path pattern table' r',
      eval_match_clause graph pattern = Some table' ->
        Pattern.wf pattern -> Rcd.type_of r' = PatternT.type_of pattern ->
          Path.matches graph r' path pattern -> In r' table'.

    Axiom match_clause_spec' : forall graph pattern table' r',
      eval_match_clause graph pattern = Some table' ->
        PropertyGraph.wf graph -> Pattern.wf pattern -> In r' table' ->
          exists path, Path.matches graph r' path pattern /\
            Rcd.type_of r' = PatternT.type_of pattern.
  End Spec.
End EvalQuery.