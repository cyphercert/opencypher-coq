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

Require Import RAUtils.
From RelationAlgebra Require Import matrix bmx monoid boolean.
Open Scope ra_terms.

Section translate.
  Variable G : PropertyGraph.t.
  Notation V := (PropertyGraph.vertices G).
  Notation E := (PropertyGraph.edges G).

  Hypothesis Hwf_G : PropertyGraph.wf G.

  Definition vertices_sup := S (\sup_(v \in V) v).

  Definition edges_sup := S (\sup_(e \in E) e).

  Definition adj_mat_ty := bmx vertices_sup vertices_sup.

  Lemma vertex_ltb_vertices_sub v
    (HIn : In v V) : v < vertices_sup.
  Proof.
    unfold vertices_sup.
    apply ltb_succ.
    change (v <= \sup_(v0 \in V) v0) with
      (leq (id v) (sup id V)).
    now apply leq_xsup.
  Qed.

  Lemma edge_ltb_edges_sub e
    (HIn : In e E) : e < edges_sup.
  Proof.
    unfold edges_sup.
    apply ltb_succ.
    change (e <= \sup_(e0\in E) e0) with
      (leq (id e) (sup id E)).
    now apply leq_xsup.
  Qed.

  Definition ord_of_vertex (v : vertex)
    (HIn : In v V) :
      ord vertices_sup :=
    Ord v (vertex_ltb_vertices_sub v HIn).

  Definition ord_of_edge (e : edge)
    (HIn : In e E) :
      ord edges_sup :=
    Ord e (edge_ltb_edges_sub e HIn).

  Definition adj_matrix_of_edge (l : option label) (e : edge) : adj_mat_ty :=
    fun i j => (e_from G e ==b i) &&
               (e_to G e ==b j) &&
               match l with
               | Some l => (elabel G e ==b l)
               | None => true
               end.

  Theorem adj_matrix_of_edge_spec e l i j :
    adj_matrix_of_edge l e i j <->
      Path.matches_direction G i j e Pattern.OUT /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end.
  Proof.
    unfold adj_matrix_of_edge.
    unfold is_true; desf.
    all: repeat rewrite Bool.andb_true_iff.
    all: repeat rewrite equiv_decb_true_iff.
    all: simpl; unfold e_from, e_to; destruct (ends G e); simpl.
    all: split; ins; desf.
  Qed.

  Definition adj_matrix (l : option label) : adj_mat_ty :=
    (\sum_(e \in E) (adj_matrix_of_edge l e)).

  Theorem adj_matrix_spec_OUT l i j :
    adj_matrix l i j <-> exists e, In e E /\
      Path.matches_direction G i j e Pattern.OUT /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end.
  Proof.
    unfold adj_matrix.
    setoid_rewrite <- adj_matrix_of_edge_spec.
    rewrite <- is_true_sup.
    now rewrite <- mx_sup.
  Qed.

  Theorem adj_matrix_spec_IN l i j :
    adj_matrix l j i <-> exists e, In e E /\
      Path.matches_direction G i j e Pattern.IN /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end.
  Proof.
    simpl. apply adj_matrix_spec_OUT.
  Qed.

  Theorem adj_matrix_spec_BOTH l i j :
    adj_matrix l i j || adj_matrix l j i <->
      exists e, In e E /\
        Path.matches_direction G i j e Pattern.BOTH /\
        match l with
        | Some l => elabel G e = l
        | None => True
        end.
  Proof.
    unfold is_true.
    rewrite Bool.orb_true_iff.
    change (?b = true) with (is_true b).
    rewrite adj_matrix_spec_OUT.
    rewrite adj_matrix_spec_IN.
    split; ins; desf; eauto.
  Qed.

  Definition inc_mat_ty := bmx vertices_sup edges_sup.

  Definition inc_matrix : inc_mat_ty :=
    fun i j => (e_from G j ==b i).

  Definition inc_matrix_inv : inc_mat_ty :=
    fun i j => (e_to G j ==b i).

  Theorem inc_matrix_spec i j :
    inc_matrix i j <->
      e_from G j = i.
  Proof.
    unfold inc_matrix.
    unfold is_true.
    now rewrite equiv_decb_true_iff.
  Qed.

  Theorem inc_matrix_inv_spec i j :
    inc_matrix_inv i j <->
      e_to G j = i.
  Proof.
    unfold inc_matrix_inv.
    unfold is_true.
    now rewrite equiv_decb_true_iff.
  Qed.

  Theorem inc_matrix_spec_OUT i j :
    inc_matrix i j <->
      Path.matches_direction G i (e_to G j) j Pattern.OUT.
  Proof.
    rewrite inc_matrix_spec.
    simpl; unfold e_from, e_to; destruct (ends G j); simpl.
    split; ins; desf.
  Qed.

  Theorem inc_matrix_inv_spec_IN i j :
    inc_matrix_inv i j <->
      Path.matches_direction G i (e_from G j) j Pattern.IN.
  Proof.
    rewrite inc_matrix_inv_spec.
    simpl; unfold e_from, e_to; destruct (ends G j); simpl.
    split; ins; desf.
  Qed.

  Definition label_matrix (l : label) : adj_mat_ty :=
    fun i j => eqb i j && In_decb l (vlabels G i).

  Theorem label_matrix_spec l i j :
    label_matrix l i j <-> i = j /\ In l (vlabels G i).
  Proof.
    unfold label_matrix, is_true.
    rewrite Bool.andb_true_iff, In_decb_true_iff.
    case eqb_spec; split; ins; desf.
  Qed.

  Fixpoint translate_slice' (pi' : PatternSlice.t) : adj_mat_ty :=
    match pi' with
    | PatternSlice.empty => 1
    | PatternSlice.hop pi' pe pv =>
      let mpi' := translate_slice' pi' in
      let mpe :=
        let l := Pattern.elabel pe in
          match Pattern.edir pe with
          | Pattern.OUT => adj_matrix l
          | Pattern.IN => (adj_matrix l)°
          | Pattern.BOTH => (adj_matrix l) + (adj_matrix l)°
          end
      in
      let mpv := 
        let l := Pattern.vlabel pv in
          match l with
          | Some l => label_matrix l
          | None => 1 (* identity matrix *)
          end
      in mpi' ⋅ mpe ⋅ mpv
    end.

  Theorem translate_slice'_spec' pi' i j r n_from
    (Hwf' : PatternSlice.wf' (Rcd.type_of r) pi')
    (Hij : translate_slice' pi' i j)
    (Hprev : r n_from = Some (Value.GVertex i)) :
      exists p', PathSlice.matches G r n_from r p' pi' /\
                  PathSlice.last r n_from p' = j.
  Proof using Hwf_G.
    gen_dep j.
    induction pi'; ins.
    { exists PathSlice.empty. split.
      { constructor. eexists; eassumption. }
      rewrite bmx_one_spec in Hij. simpl. desf. }

    inv Hwf'. inv Hwf_G.

    repeat setoid_rewrite bmx_dot_spec in Hij.
    destruct Hij as [j' [[k [Hik Hkj]] Hj'j]].
    apply IHpi' in Hik; clear IHpi'; auto.

    destruct (Pattern.vlabel pv) as [l |] eqn:Heq_v.
    1: rewrite label_matrix_spec in Hj'j;
        destruct Hj'j as [? Hvlabel].
    2: rewrite bmx_one_spec in Hj'j.
    all: subst j'.

    all: destruct (Pattern.edir pe) eqn:Heq_edir; simpls.
    all: try rewrite adj_matrix_spec_OUT in Hkj.
    all: try rewrite adj_matrix_spec_IN in Hkj.
    all: try rewrite adj_matrix_spec_BOTH in Hkj.
    all: desf.

    all: exists (PathSlice.hop p' e j); split; [| reflexivity].
    all: replace r with ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
                          (Value.GVertex j, Value.GEdge e); r) at 2
                    by (simpl; unfold Name.is_implicit in *; desf).
    all: constructor; auto.
    all: try (left; apply Rcd.type_of_None;
                eauto using PatternSlice.type_of_None).
    all: try constructor.
    all: try (ins; congruence).
    all: try now rewrite Hik0, Heq_edir.

    all: unfold Path.matches_direction in Hkj0; desf.
    all: edestruct ends_In0; eauto.
  Qed.

  Theorem translate_slice'_spec r r' n_from p' pi' (i j : ord _) 
    (Hwf' : PatternSlice.wf' (Rcd.type_of r) pi')
    (Hprev : r n_from = Some (Value.GVertex i))
    (HIn_prev : In (i : vertex) (vertices G))
    (Hlast : PathSlice.last r n_from p' = j)
    (Hmatch : PathSlice.matches G r n_from r' p' pi') :
      translate_slice' pi' i j.
  Proof.
    gen_dep j; induction Hmatch; ins; subst.
    { simpl. rewrite bmx_one_spec. desf. now apply eq_ord. }

    assert (exists k : ord vertices_sup, PathSlice.last r n_from p = k) as [k Hk].
    { enough (HIn : In (PathSlice.last r n_from p) (vertices G)).
      now eexists (ord_of_vertex _ HIn).
      eapply PathSlice.matches_last_In; eauto. }

    assert (IH : translate_slice' pi i k).
    { apply IHHmatch; auto. inv Hwf'. }
    clear IHHmatch.

    repeat setoid_rewrite bmx_dot_spec.
    desf.

    all: exists j.
    all: try rewrite bmx_one_spec.
    all: try rewrite label_matrix_spec.
    all: destruct Hpv.
    all: splits; auto.

    all: exists k.
    all: split; [ assumption | ].

    all: simpl.
    all: match goal with
          | [ _ : _ = Pattern.OUT |- _ ] =>
              rewrite adj_matrix_spec_OUT
          | [ _ : _ = Pattern.IN |- _ ] =>
              rewrite adj_matrix_spec_IN
          | [ _ : _ = Pattern.BOTH |- _ ] =>
              rewrite adj_matrix_spec_BOTH
          end.
    all: exists e.
    all: destruct Hpe.
    all: rewrite Hk in Hdir.
    all: splits; auto.
    all: desf; eauto.
  Qed.
End translate.


Definition traverse : PatternSlice.t -> Name.t -> step1.
Admitted.

Theorem traverse_wf : forall G table ty slice n_from,
  PropertyGraph.wf G -> BindingTable.of_type table ty ->
    PatternSlice.wf ty slice -> ty n_from = Some Value.GVertexT ->
      exists table', traverse slice n_from G table = Some table'.
Admitted.

Theorem traverse_type : forall G table table' ty slice n_from,
  traverse slice n_from G table = Some table' ->
    BindingTable.of_type table ty ->
      BindingTable.of_type table' (PatternSlice.type_of ty slice).
Admitted.

Theorem traverse_spec : forall G table table' path r r' slice n_from,
  traverse slice n_from G table = Some table' ->
    PathSlice.matches G r n_from r' path slice ->
      In r table -> In r' table'.
Admitted.

Theorem traverse_spec' : forall G table table' r' slice n_from,
  traverse slice n_from G table = Some table' ->
    In r' table' -> exists r path, In r table /\
      PathSlice.matches G r n_from r' path slice.
Admitted.