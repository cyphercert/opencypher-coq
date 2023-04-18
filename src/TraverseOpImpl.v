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
  Proof using.
    unfold vertices_sup.
    apply ltb_succ.
    change (v <= \sup_(v0 \in V) v0) with
      (leq (id v) (sup id V)).
    now apply leq_xsup.
  Qed.

  Lemma edge_ltb_edges_sub e
    (HIn : In e E) : e < edges_sup.
  Proof using.
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

  Lemma adj_matrix_of_edge_spec e l i j :
    adj_matrix_of_edge l e i j <->
      Path.matches_direction G i j e Pattern.OUT /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end.
  Proof using.
    unfold adj_matrix_of_edge.
    unfold is_true; desf.
    all: repeat rewrite Bool.andb_true_iff.
    all: repeat rewrite equiv_decb_true_iff.
    all: simpl; unfold e_from, e_to; destruct (ends G e); simpl.
    all: split; ins; desf.
  Qed.

  Definition adj_matrix (l : option label) : adj_mat_ty :=
    (\sum_(e \in E) (adj_matrix_of_edge l e)).

  Lemma adj_matrix_spec_OUT l i j :
    adj_matrix l i j <-> exists e, In e E /\
      Path.matches_direction G i j e Pattern.OUT /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end.
  Proof using.
    unfold adj_matrix.
    setoid_rewrite <- adj_matrix_of_edge_spec.
    rewrite <- is_true_sup.
    now rewrite <- mx_sup.
  Qed.

  Lemma adj_matrix_spec_IN l i j :
    adj_matrix l j i <-> exists e, In e E /\
      Path.matches_direction G i j e Pattern.IN /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end.
  Proof using.
    simpl. apply adj_matrix_spec_OUT.
  Qed.

  Lemma adj_matrix_spec_BOTH l i j :
    adj_matrix l i j || adj_matrix l j i <->
      exists e, In e E /\
        Path.matches_direction G i j e Pattern.BOTH /\
        match l with
        | Some l => elabel G e = l
        | None => True
        end.
  Proof using.
    unfold is_true.
    rewrite Bool.orb_true_iff.
    change (?b = true) with (is_true b).
    rewrite adj_matrix_spec_OUT.
    rewrite adj_matrix_spec_IN.
    split; ins; desf; eauto.
  Qed.

  Definition label_matrix (l : label) : adj_mat_ty :=
    fun i j => eqb i j && In_decb l (vlabels G i).

  Lemma label_matrix_spec l i j :
    label_matrix l i j <-> i = j /\ In l (vlabels G i).
  Proof using.
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

  Lemma end_In_V e u v
    (HIn : In e E)
    (Hends : ends G e = (u, v) \/ ends G e = (v, u)) :
      In v V.
  Proof using Hwf_G.
    destruct Hwf_G. desf.
    all: edestruct ends_In0; eauto.
  Qed.

  Lemma translate_slice'_hop_spec pi' pe pv i j :
    translate_slice' (PatternSlice.hop pi' pe pv) i j <->
      << HInV : In (j : vertex) V >> /\
      exists k e,
        << HInE : In e E >> /\
        << Hik : translate_slice' pi' i k >> /\
        << Hkj : Path.matches_direction G k j e (Pattern.edir pe) >> /\
        << Helabel : match Pattern.elabel pe with
                     | Some l => elabel G e = l
                     | None => True
                     end >> /\
        << Hvlabel : match Pattern.vlabel pv with
                     | Some l => In l (vlabels G j)
                     | None => True
                     end >>.
  Proof using Hwf_G.
    simpls.
    repeat setoid_rewrite bmx_dot_spec.
    destruct (Pattern.edir pe).
    1: setoid_rewrite adj_matrix_spec_OUT.
    2: setoid_rewrite adj_matrix_spec_IN.
    3: setoid_rewrite adj_matrix_spec_BOTH.
    all: destruct (Pattern.vlabel pv).
    all: try setoid_rewrite label_matrix_spec.
    all: try setoid_rewrite bmx_one_spec.
    all: split; ins; desf; unnw; eauto 11 using end_In_V.
  Qed.

  Theorem translate_slice'_spec' pi' i j r n_from
    (Hwf' : PatternSlice.wf' (Rcd.type_of r) pi')
    (Hij : translate_slice' pi' i j)
    (Hprev : r n_from = Some (Value.GVertex i)) :
      exists p', << Hmatch : PathSlice.matches G r n_from r p' pi' >> /\
                 << Hlast : PathSlice.last r n_from p' = j >>.
  Proof using Hwf_G.
    gen_dep j.
    induction pi'; intros.
    { simpls. exists PathSlice.empty. split.
      { constructor. eexists; eassumption. }
      rewrite bmx_one_spec in Hij. simpl. desf. }

    inv Hwf'. inv Hwf_G.

    rewrite translate_slice'_hop_spec in Hij; desc.
    apply IHpi' in Hik; clear IHpi'; auto.
    desf; unnw.

    all: exists (PathSlice.hop p' e j); split; [| reflexivity].
    all: replace r with ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
                          (Value.GVertex j, Value.GEdge e); r) at 2
                    by (simpl; unfold Name.is_implicit in *; desf).
    all: constructor; auto.
    all: try (left; apply Rcd.type_of_None;
                eauto using PatternSlice.type_of_None).
    all: try constructor.
    all: try (ins; congruence).
  Qed.

  Theorem translate_slice'_spec r r' n_from p' pi' (i j : ord _) 
    (Hwf' : PatternSlice.wf' (Rcd.type_of r) pi')
    (Hprev : r n_from = Some (Value.GVertex i))
    (HIn_prev : In (i : vertex) (vertices G))
    (Hlast : PathSlice.last r n_from p' = j)
    (Hmatch : PathSlice.matches G r n_from r' p' pi') :
      translate_slice' pi' i j.
  Proof using Hwf_G.
    gen_dep j; induction Hmatch; intros; subst.
    { simpls. rewrite bmx_one_spec. desf. now apply eq_ord. }

    assert (exists k : ord vertices_sup, PathSlice.last r n_from p = k) as [k Hk].
    { enough (HIn : In (PathSlice.last r n_from p) (vertices G)).
      now eexists (ord_of_vertex _ HIn).
      eapply PathSlice.matches_last_In; eauto. }

    assert (IH : translate_slice' pi i k).
    { apply IHHmatch; auto. inv Hwf'. }
    clear IHHmatch.

    rewrite translate_slice'_hop_spec.
    destruct Hpv, Hpe. simpls. subst.
    split; auto.

    exists k. exists e.
    splits; auto.
    { now rewrite <- Hk. }
    all: desf; auto.
  Qed.

  Definition translate_slice (pi' : PatternSlice.t) : adj_mat_ty :=
    translate_slice' pi'.

  Theorem translate_slice_spec' pi' pe pv i j r n_from
    (Hwf : PatternSlice.wf (Rcd.type_of r) (PatternSlice.hop pi' pe pv))
    (Hij : translate_slice (PatternSlice.hop pi' pe pv) i j)
    (Hprev_pv : r (Pattern.vname pv) = None \/
                r (Pattern.vname pv) = Some (Value.GVertex j))
    (Hprev : r n_from = Some (Value.GVertex i)) :
      exists p' e, PathSlice.matches G r n_from
                    ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
                     (Value.GVertex j, Value.GEdge e); r)
                    (PathSlice.hop p' e j) (PatternSlice.hop pi' pe pv).
  Proof using Hwf_G.
    inv Hwf.
    unfold translate_slice in Hij.
    rewrite translate_slice'_hop_spec in Hij; desc.
    eapply translate_slice'_spec' in Hik; eauto; desc.
    rewrite <- Hlast in Hkj.

    do 2 eexists.
    econstructor; eauto.
    all: constructor; ins; desf; auto.
  Qed.

  Theorem translate_slice_spec r r' n_from p' pi' (i j : ord _) 
    (Hwf : PatternSlice.wf (Rcd.type_of r) pi')
    (Hprev : r n_from = Some (Value.GVertex i))
    (HIn_prev : In (i : vertex) (vertices G))
    (Hlast : PathSlice.last r n_from p' = j)
    (Hmatch : PathSlice.matches G r n_from r' p' pi') :
      translate_slice pi' i j.
  Proof using Hwf_G.
    destruct Hmatch.
    { simpls. rewrite bmx_one_spec. desf. now apply eq_ord. }

    inv Hwf. destruct Hpv, Hpe.
    unfold translate_slice.
    rewrite translate_slice'_hop_spec; unnw.
    simpls. subst.
    split; [ assumption |].

    assert (exists k : ord vertices_sup, PathSlice.last r n_from p = k) as [k Hk].
    { enough (HIn : In (PathSlice.last r n_from p) (vertices G)).
      now eexists (ord_of_vertex _ HIn).
      eapply PathSlice.matches_last_In; eauto. }
    rewrite Hk in Hdir.

    exists k. exists e.
    splits; auto.
    { eapply translate_slice'_spec; eauto. }
    all: desf; auto.
  Qed.
  Opaque translate_slice.

  Definition inc_mat_ty := bmx vertices_sup edges_sup.

  Definition inc_matrix (l : option label) : inc_mat_ty :=
    fun i j => (e_from G j ==b i) &&
               match l with
               | Some l => (elabel G j ==b l)
               | None => true
               end.

  Definition inc_matrix_inv (l : option label) : inc_mat_ty :=
    fun i j => (e_to G j ==b i) &&
               match l with
               | Some l => (elabel G j ==b l)
               | None => true
               end.

  Theorem inc_matrix_spec l i j :
    inc_matrix l i j <->
      e_from G j = i /\
      match l with
      | Some l => (elabel G j = l)
      | None => True
      end.
  Proof using.
    unfold inc_matrix, is_true.
    rewrite Bool.andb_true_iff.
    desf.
    all: now repeat rewrite equiv_decb_true_iff.
  Qed.

  Theorem inc_matrix_inv_spec l i j :
    inc_matrix_inv l i j <->
      e_to G j = i /\
      match l with
      | Some l => (elabel G j = l)
      | None => True
      end.
  Proof using.
    unfold inc_matrix_inv, is_true.
    rewrite Bool.andb_true_iff.
    desf.
    all: now repeat rewrite equiv_decb_true_iff.
  Qed.

  Theorem inc_matrix_spec_OUT l i j :
    inc_matrix l i j <->
      Path.matches_direction G i (e_to G j) j Pattern.OUT /\
      match l with
      | Some l => (elabel G j = l)
      | None => True
      end.
  Proof using.
    rewrite inc_matrix_spec.
    simpl; unfold e_from, e_to; destruct (ends G j); simpl.
    split; ins; desf.
  Qed.

  Theorem inc_matrix_inv_spec_IN l i j :
    inc_matrix_inv l i j <->
      Path.matches_direction G i (e_from G j) j Pattern.IN /\
      match l with
      | Some l => (elabel G j = l)
      | None => True
      end.
  Proof using.
    rewrite inc_matrix_inv_spec.
    simpl; unfold e_from, e_to; destruct (ends G j); simpl.
    split; ins; desf.
  Qed.

  Definition e_from_dir (d : Pattern.direction) (e : edge) : vertex :=
    match d with
    | Pattern.OUT => e_to G e
    | Pattern.IN => e_from G e
    | Pattern.BOTH => 0%nat (* should not be used *)
    end.
  
  Definition inc_label_matrix l d : bmx edges_sup edges_sup :=
    fun e e' => eqb e e' && In_decb l (vlabels G (e_from_dir d e)).

  Lemma inc_label_matrix_spec l (e e' : ord _) d :
    let j := e_from_dir d e in
      inc_label_matrix l d e e' <->
        e = e' /\ In l (vlabels G (e_from_dir d e)).
  Proof using.
    unfold inc_label_matrix, is_true.
    rewrite Bool.andb_true_iff, In_decb_true_iff.
    case eqb_spec; split; ins; desf.
  Qed.

  Definition translate_slice_inc (pi' : PatternSlice.t) : inc_mat_ty :=
    match pi' with
    | PatternSlice.empty => 0
    | PatternSlice.hop pi' pe pv =>
      let mpi' := translate_slice' pi' in
      let mpe :=
        let l := Pattern.elabel pe in
          match Pattern.edir pe with
          | Pattern.OUT => inc_matrix l
          | Pattern.IN => inc_matrix_inv l
          | Pattern.BOTH => 0 (* should not be used *)
          end
      in
      let mpv := 
        match Pattern.vlabel pv with
        | Some l => inc_label_matrix l (Pattern.edir pe)
        | None => 1 (* identity matrix *)
        end
      in mpi' ⋅ mpe ⋅ mpv
    end.

  Lemma translate_slice_inc_hop_spec pi' pe pv i (e : ord _) :
    let j := e_from_dir (Pattern.edir pe) e in
      translate_slice_inc (PatternSlice.hop pi' pe pv) i e <->
        exists k,
          << Hik : translate_slice' pi' i k >> /\
          << Hkj : match Pattern.edir pe with
                   | Pattern.OUT => Path.matches_direction G k j e Pattern.OUT
                   | Pattern.IN => Path.matches_direction G k j e Pattern.IN
                   | Pattern.BOTH => False
                   end >> /\
          << Helabel : match Pattern.elabel pe with
                       | Some l => elabel G e = l
                       | None => True
                       end >> /\
          << Hvlabel : match Pattern.vlabel pv with
                       | Some l => In l (vlabels G j)
                       | None => True
                       end >>.
  Proof using.
    simpl.
    repeat setoid_rewrite bmx_dot_spec.
    destruct (Pattern.edir pe), (Pattern.vlabel pv).
    all: try setoid_rewrite inc_matrix_spec_OUT.
    all: try setoid_rewrite inc_matrix_inv_spec_IN.
    all: try setoid_rewrite bmx_one_spec.
    all: try setoid_rewrite label_matrix_spec.
    all: try setoid_rewrite inc_label_matrix_spec.
    all: simpls.
    all: split; ins; desf; eauto 12.
  Qed.

  Section translate_slice_inc_spec.
    Variable pi' : PatternSlice.t.
    Variable pe : Pattern.pedge.
    Variable pv : Pattern.pvertex.
    Variable i : ord vertices_sup.
    Variable e : ord edges_sup.
    Variable r : Rcd.t.
    Variable n_from : Name.t.

    Notation j := (e_from_dir (Pattern.edir pe) e).

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) (PatternSlice.hop pi' pe pv).
    Hypothesis HIn_e : In (e : edge) (edges G).
    
    Theorem translate_slice_inc_spec'
      (Hij : translate_slice_inc (PatternSlice.hop pi' pe pv) i e)
      (Hprev_pv : r (Pattern.vname pv) = None \/
                  r (Pattern.vname pv) =
                    Some (Value.GVertex j))
      (Hprev : r n_from = Some (Value.GVertex i)) :
        exists p', PathSlice.matches G r n_from
                    ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
                      (Value.GVertex j, Value.GEdge e); r)
                    (PathSlice.hop p' e j) (PatternSlice.hop pi' pe pv).
    Proof using Hwf_G Hwf HIn_e.
      inv Hwf.
      apply translate_slice_inc_hop_spec in Hij; desc.
      eapply translate_slice'_spec' in Hik; eauto; desc.
      rewrite <- Hlast in Hkj.
      exists p'; constructor; auto.
      all: destruct (Pattern.edir pe); simpls.
      all: constructor; auto using wf_e_from_In, wf_e_to_In.
      all: ins; desf; auto 2.
    Qed.

    Theorem translate_slice_inc_spec p' r'
      (Hprev : r n_from = Some (Value.GVertex i))
      (HIn_prev : In (i : vertex) (vertices G))
      (Hdir : Pattern.edir pe = Pattern.OUT \/ Pattern.edir pe = Pattern.IN)
      (Hmatch : PathSlice.matches G r n_from r'
                  (PathSlice.hop p' e j) (PatternSlice.hop pi' pe pv)) :
        translate_slice_inc (PatternSlice.hop pi' pe pv) i e.
    Proof using Hwf_G Hwf.
      apply translate_slice_inc_hop_spec; unnw.
      inv Hwf. inv Hmatch.

      assert (exists k : ord vertices_sup, PathSlice.last r n_from p' = k) as [k Hk].
      { enough (HIn : In (PathSlice.last r n_from p') (vertices G)).
        now eexists (ord_of_vertex _ HIn).
        eapply PathSlice.matches_last_In; eauto. }
      do 2 eexists; splits.
      { erewrite translate_slice'_spec; eauto. }
      all: destruct Hpv, Hpe.
      all: try rewrite <- Hk.
      all: desf; auto.
    Qed.
  End translate_slice_inc_spec.
  Opaque translate_slice_inc.

  Definition ord_of_vertex_err v : option (ord vertices_sup) :=
    match @In_dec nat _ nat_eqdec v (vertices G) with
    | left HInV => Some (ord_of_vertex v HInV)
    | right _ => None
    end.

  Lemma ord_of_vertex_err_value v i
    (Hres : ord_of_vertex_err v = Some i) :
      v = i.
  Proof using.
    unfold ord_of_vertex_err in Hres. desf.
  Qed.

  Lemma ord_of_vertex_In v :
    In v V <-> exists i, ord_of_vertex_err v = Some i.
  Proof using.
    unfold ord_of_vertex_err.
    split; ins; desf; eauto.
  Qed.

  Ltac subst_ord_of_vertex :=
    match goal with
    | [ H : ord_of_vertex_err ?v = Some ?i |- _ ] =>
      let Heq := fresh "Heq" in
      let HInV := fresh "HInV" in
      assert (Heq := H);
      assert (HInV : In v V) by (apply ord_of_vertex_In; exists i; apply H);
      apply ord_of_vertex_err_value in Heq; subst v
    | [ |- _ ] =>
      fail "Hypothesis of the form 'ord_of_vertex_err ?v = Some ?i' not found"
    end.

  Definition r_from (r : Rcd.t) (n_from : Name.t) : option (ord vertices_sup) :=
    match r n_from with
    | Some (Value.GVertex i) => ord_of_vertex_err i
    | _ => None
    end.

  Definition ords_of_vertices : list (ord vertices_sup) :=
    filter_map ord_of_vertex_err (vertices G).
  
  Lemma ords_of_vertices_In v :
    In v (vertices G) <->
      exists (i : ord _), v = i /\ In i ords_of_vertices.
  Proof using.
    unfold ords_of_vertices.
    setoid_rewrite filter_map_In.
    split.
    { setoid_rewrite ord_of_vertex_In.
      ins; desf; eauto 10 using ord_of_vertex_err_value. }
    ins; desf. now subst_ord_of_vertex.
  Qed.

  Definition candidate_ends (r : Rcd.t) (nv : Name.t) : option (list (ord _)) :=
    match r nv with
    | Some (Value.GVertex i) => ord_of_vertex_err i >>= fun i => Some [i]
    | None => Some ords_of_vertices
    | _ => None
    end.

  Lemma candidate_ends_In r nv js j
    (Hres : candidate_ends r nv = Some js)
    (HIn : In j js) :
      r nv = None \/ r nv = Some (Value.GVertex j).
  Proof using.
    unfold candidate_ends, option_bind in Hres. desf.
    { inv HIn. subst_ord_of_vertex. eauto. }
    now left.
  Qed.

  Lemma candidate_ends_In' r nv js v
    (Hres : candidate_ends r nv = Some js)
    (HIn : In v V)
    (Hprev : r nv = Some (Value.GVertex v) \/ r nv = None) :
      exists (j : ord _), v = j /\ In j js.
  Proof.
    unfold candidate_ends, option_bind in Hres. desf.
    { eexists. split.
      { now subst_ord_of_vertex. }
      simpl. left. now apply eq_ord. }
    now apply ords_of_vertices_In.
  Qed.

  Definition traverse_adj_single (pi' : PatternSlice.t) (n_from : Name.t)
             (r : Rcd.t) : option BindingTable.t :=
    r_from r n_from >>= fun i =>
      match pi' with
      | PatternSlice.hop pi0' pe pv =>
        candidate_ends r (Pattern.vname pv) >>= fun js =>
          let js := filter (translate_slice pi' i) js in
          let update_rcd (j : ord _) :=
              PartialMap.join (Pattern.vname pv |-[Explicit]-> Value.GVertex j) r
            in Some (map update_rcd js)
      | _ => Some [r]
      end.

  Section traverse_adj_single_spec.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r r' : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hres : traverse_adj_single pi' n_from r = Some table'.
    Hypothesis Hpe_imp :
      match pi' with
      | PatternSlice.hop _ pe _ => Name.is_implicit (Pattern.ename pe)
      | PatternSlice.empty => True
      end.

    Theorem traverse_adj_single_spec'
      (HIn : In r' table') :
        exists p', PathSlice.matches G r n_from r' p' pi'.
    Proof using Hwf_G Hres Hpe_imp Hwf.
      unfold traverse_adj_single, option_bind, r_from in Hres.
      Opaque update_with_mode_start.
      desf.

      { exists PathSlice.empty. inv HIn. constructor. eauto 2. }

      rewrite in_map_iff in HIn; setoid_rewrite filter_In in HIn; desf.
      change (?x = true) with (is_true x) in *.
      repeat subst_ord_of_vertex.
      match goal with
      | [ H : is_true (translate_slice _ _ _) |- _ ] =>
        eapply translate_slice_spec' in H;
        eauto using candidate_ends_In; desf
      end.

      Transparent update_with_mode_start.
      simpls. unfold Name.is_implicit in *. desf.
      all: try rewrite PartialMap.join_empty_l.
      all: try rewrite PartialMap.join_singleton.
      all: eexists; eassumption.
    Qed.

    Theorem traverse_adj_single_spec p'
      (Hmatch : PathSlice.matches G r n_from r' p' pi') :
        In r' table'.
    Proof using Hwf_G Hres Hpe_imp Hwf.
      unfold traverse_adj_single, option_bind, r_from in Hres.
      Opaque update_with_mode_start.
      desf; inv Hmatch.
      { now left. }
      subst_ord_of_vertex. inv Hwf.
      apply PathSlice.matches_wf'_eq in Hpi; auto; subst.
      rewrite in_map_iff; setoid_rewrite filter_In. destruct Hpv.
      eapply candidate_ends_In' in vertex_in_g; eauto.
      2: { desf; auto. }
      desc; subst.

      eexists. splits.
      Transparent update_with_mode_start.
      { simpls. unfold Name.is_implicit in *. desf.
        all: try rewrite PartialMap.join_empty_l.
        all: try rewrite PartialMap.join_singleton.
        all: eauto. }
      { assumption. }
      change (?x = true) with (is_true x) in *.
      eapply translate_slice_spec; eauto; auto.
    Qed.
  End traverse_adj_single_spec.

  Definition traverse_adj (pi' : PatternSlice.t) (n_from : Name.t)
             (table : BindingTable.t) : option BindingTable.t :=
    option_map (@List.concat Rcd.t)
               (fold_option (map (traverse_adj_single pi' n_from) table)).
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