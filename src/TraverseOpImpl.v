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
  Definition eadj_mat_ty := bmx edges_sup edges_sup.
  Definition inc_mat_ty := bmx vertices_sup edges_sup.

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

  Definition adj_matrix_of_edge (l : option label) (props : list (Property.name * Property.t)) (e : edge) : adj_mat_ty :=
    fun i j => (e_from G e ==b i) &&
               (e_to G e ==b j) &&
               match l with
               | Some l => (elabel G e ==b l)
               | None => true
               end &&
               forallb (fun '(k, val) => get_eprop G k e ==b Some val) props.

  Lemma adj_matrix_of_edge_spec e l props i j :
    adj_matrix_of_edge l props e i j <->
      Path.matches_direction G i j e Pattern.OUT /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end /\
      Forall (fun '(k, val) => get_eprop G k e = Some val) props.
  Proof using.
    unfold adj_matrix_of_edge, is_true.
    repeat rewrite Bool.andb_true_iff.
    unfold Path.matches_direction.
    rewrite e_from_to, forallb_forall, Forall_forall.
    assert (Hlem : forall x,
      (let '(k, val) := x in get_eprop G k e ==b Some val) = true <->
        (let '(k, val) := x in get_eprop G k e = Some val)).
    { intros []. now rewrite equiv_decb_true_iff. }
    setoid_rewrite Hlem.
    destruct l.
    all: repeat rewrite equiv_decb_true_iff.
    all: intuition; desf.
  Qed.

  Definition adj_matrix
    (l : option label)
    (props : list (Property.name * Property.t)) 
      : adj_mat_ty :=
        (\sum_(e \in E) (adj_matrix_of_edge l props e)).

  Lemma adj_matrix_spec_OUT l props i j :
    adj_matrix l props i j <-> exists e, In e E /\
      Path.matches_direction G i j e Pattern.OUT /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end /\
      Forall (fun '(k, val) => get_eprop G k e = Some val) props.
  Proof using.
    unfold adj_matrix.
    setoid_rewrite <- adj_matrix_of_edge_spec.
    rewrite <- is_true_sup.
    now rewrite <- mx_sup.
  Qed.

  Lemma adj_matrix_spec_IN l props i j :
    adj_matrix l props j i <-> exists e, In e E /\
      Path.matches_direction G i j e Pattern.IN /\
      match l with
      | Some l => elabel G e = l
      | None => True
      end /\
      Forall (fun '(k, val) => get_eprop G k e = Some val) props.
  Proof using.
    simpl. apply adj_matrix_spec_OUT.
  Qed.

  Lemma adj_matrix_spec_BOTH l props i j :
    adj_matrix l props i j || adj_matrix l props j i <->
      exists e, In e E /\
        Path.matches_direction G i j e Pattern.BOTH /\
        match l with
        | Some l => elabel G e = l
        | None => True
        end /\
        Forall (fun '(k, val) => get_eprop G k e = Some val) props.
  Proof using.
    unfold is_true.
    rewrite Bool.orb_true_iff.
    change (?b = true) with (is_true b).
    rewrite adj_matrix_spec_OUT.
    rewrite adj_matrix_spec_IN.
    split; ins; desf; eauto 10.
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

  Definition prop_matrix (k : Property.name) (val : Property.t) : adj_mat_ty :=
    fun i j => eqb i j && (get_vprop G k (i : vertex) ==b Some val).

  Lemma prop_matrix_spec k val i j :
    prop_matrix k val i j <-> i = j /\ get_vprop G k i = Some val.
  Proof.
    unfold prop_matrix, is_true.
    rewrite Bool.andb_true_iff, equiv_decb_true_iff.
    case eqb_spec; split; ins; desf.
  Qed.

  Fixpoint big_product {n} (xs : list (bmx n n)) : bmx n n :=
    match xs with
    | nil => 1
    | x :: xs => x ⋅ big_product xs
    end.

  Definition props_matrix (props : list (Property.name * Property.t)) : adj_mat_ty :=
    big_product (map (fun '(k, val) => prop_matrix k val) props).
  
  Lemma props_matrix_spec props i j :
    props_matrix props i j <-> i = j /\
      Forall (fun '(k, val) => get_vprop G k i = Some val) props.
  Proof.
    unfold props_matrix.
    gen_dep j i.
    induction props; simpl; ins.
    - rewrite Forall_nil_iff.
      rewrite bmx_one_spec.
      intuition.
    - rewrite Forall_cons_iff.
      rewrite bmx_dot_spec.
      destruct a.
      setoid_rewrite IHprops.
      setoid_rewrite prop_matrix_spec.
      intuition; desf; eauto.
  Qed.

  Fixpoint translate_slice' (pi' : PatternSlice.t) : adj_mat_ty :=
    match pi' with
    | PatternSlice.empty => 1
    | PatternSlice.hop pi' pe pv =>
      let mpi' := translate_slice' pi' in
      let mpe :=
        let l := Pattern.elabel pe in
        let props := Pattern.eprops pe in
          match Pattern.edir pe with
          | Pattern.OUT => adj_matrix l props
          | Pattern.IN => (adj_matrix l props)°
          | Pattern.BOTH => (adj_matrix l props) + (adj_matrix l props)°
          end
      in
      let mpv_label := 
        match Pattern.vlabel pv with
        | Some l => label_matrix l
        | None => 1 (* identity matrix *)
        end
      in
      let mpv_props :=
        props_matrix (Pattern.vprops pv)
      in
      let mpv := mpv_label ∩ mpv_props in
      mpi' ⋅ mpe ⋅ mpv
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
                     end >> /\
        << Heprops : Forall (fun '(k, val) => get_eprop G k e = Some val)
                      (Pattern.eprops pe) >> /\
        << Hvprops : Forall (fun '(k, val) => get_vprop G k j = Some val)
                      (Pattern.vprops pv) >>.
  Proof using Hwf_G.
    simpls.
    repeat setoid_rewrite bmx_dot_spec.
    repeat setoid_rewrite bmx_cap_spec.
    setoid_rewrite props_matrix_spec.
    destruct (Pattern.edir pe).
    1: setoid_rewrite adj_matrix_spec_OUT.
    2: setoid_rewrite adj_matrix_spec_IN.
    3: setoid_rewrite adj_matrix_spec_BOTH.
    all: destruct (Pattern.vlabel pv).
    all: try setoid_rewrite label_matrix_spec.
    all: try setoid_rewrite bmx_one_spec.
    all: split; ins; desf; unnw; eauto 14 using end_In_V.
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

  Definition e_to_dir (d : Pattern.direction) (e : edge) : vertex :=
    match d with
    | Pattern.OUT => e_to G e
    | Pattern.IN => e_from G e
    | Pattern.BOTH => 0%nat (* should not be used *)
    end.

  Theorem e_to_dir_In (d : Pattern.direction) (e : edge)
    (Hedir : d <> Pattern.BOTH)
    (HIn : In e (edges G)) :
      In (e_to_dir d e) (vertices G).
  Proof using Hwf_G.
    destruct d; simpls.
    all: now (apply wf_e_to_In || apply wf_e_from_In).
  Qed.

  Theorem matches_last_e_to_dir pi' pe pv p' e v n_from r r'
    (Hedir : Pattern.edir pe <> Pattern.BOTH)
    (Hmatch : PathSlice.matches G r n_from r'
                (PathSlice.hop p' e v)
                (PatternSlice.hop pi' pe pv)) :
      v = e_to_dir (Pattern.edir pe) e.
  Proof using.
    inv Hmatch.
    destruct (Pattern.edir pe); simpls.
    all: rewrite e_from_to in Hdir.
    all: injection Hdir; ins.
  Qed.
  
  Definition inc_label_matrix l d : eadj_mat_ty :=
    fun e e' => (e ==b e') && In_decb l (vlabels G (e_to_dir d e)).

  Lemma inc_label_matrix_spec l (e e' : ord _) d :
    let j := e_to_dir d e in
      inc_label_matrix l d e e' <->
        e = e' /\ In l (vlabels G (e_to_dir d e)).
  Proof using.
    unfold inc_label_matrix, is_true.
    now rewrite Bool.andb_true_iff, In_decb_true_iff, equiv_decb_true_iff.
  Qed.

  Definition inc_prop_matrix d k val : eadj_mat_ty :=
    fun e e' => (e ==b e') && (get_vprop G k (e_to_dir d e) ==b Some val).

  Lemma inc_prop_matrix_spec (e e' : ord _) d k val :
    let j := e_to_dir d e in
      (inc_prop_matrix d k val) e e' <->
        e = e' /\ get_vprop G k j = Some val.
  Proof using.
    unfold inc_prop_matrix, is_true.
    rewrite Bool.andb_true_iff.
    now repeat rewrite equiv_decb_true_iff.
  Qed.

  Definition inc_props_matrix d props : eadj_mat_ty :=
    big_product (map (fun '(k, val) => inc_prop_matrix d k val) props).

  Lemma inc_props_matrix_spec (e e' : ord _) d props :
    let j := e_to_dir d e in
      (inc_props_matrix d props) e e' <->
        e = e' /\ Forall (fun '(k, val) => get_vprop G k j = Some val) props.
  Proof.
    unfold inc_props_matrix.
    gen_dep e e'.
    induction props as [| [k' val'] props]; simpls; ins.
    - rewrite Forall_nil_iff.
      rewrite bmx_one_spec.
      intuition.
    - rewrite Forall_cons_iff.
      rewrite bmx_dot_spec.
      setoid_rewrite IHprops.
      setoid_rewrite inc_prop_matrix_spec.
      intuition; desf; eauto.
  Qed.

  Definition eprop_matrix_inc (k : Property.name) (val : Property.t) : eadj_mat_ty :=
    fun i j => (i ==b j) && (get_eprop G k (i : edge) ==b Some val).

  Lemma eprop_matrix_inc_spec k val i j :
    eprop_matrix_inc k val i j <-> i = j /\ get_eprop G k i = Some val.
  Proof.
    unfold eprop_matrix_inc, is_true.
    rewrite Bool.andb_true_iff.
    now repeat rewrite equiv_decb_true_iff.
  Qed.

  Definition eprops_matrix_inc (props : list (Property.name * Property.t)) : eadj_mat_ty :=
    big_product (map (fun '(k, val) => eprop_matrix_inc k val) props).

  Lemma eprops_matrix_inc_spec props i j :
    eprops_matrix_inc props i j <-> i = j /\
      Forall (fun '(k, val) => get_eprop G k i = Some val) props.
  Proof.
    unfold eprops_matrix_inc.
    gen_dep j i.
    induction props; simpl; ins.
    - rewrite Forall_nil_iff.
      rewrite bmx_one_spec.
      intuition.
    - rewrite Forall_cons_iff.
      rewrite bmx_dot_spec.
      destruct a.
      setoid_rewrite IHprops.
      setoid_rewrite eprop_matrix_inc_spec.
      intuition; desf; eauto.
  Qed.

  Definition translate_slice_inc (pi' : PatternSlice.t) : inc_mat_ty :=
    match pi' with
    | PatternSlice.empty => 0
    | PatternSlice.hop pi' pe pv =>
      let mpi' := translate_slice' pi' in
      let mpe_label :=
        let l := Pattern.elabel pe in
          match Pattern.edir pe with
          | Pattern.OUT => inc_matrix l
          | Pattern.IN => inc_matrix_inv l
          | Pattern.BOTH => 0 (* should not be used *)
          end
      in
      let mpe_props := eprops_matrix_inc (Pattern.eprops pe) in
      let mpe := mpe_label ⋅ mpe_props in
      let mpv_label := 
        match Pattern.vlabel pv with
        | Some l => inc_label_matrix l (Pattern.edir pe)
        | None => 1 (* identity matrix *)
        end
      in
      let mpv_props :=
        inc_props_matrix (Pattern.edir pe) (Pattern.vprops pv)
      in
      let mpv := mpv_label ⋅ mpv_props in
      mpi' ⋅ mpe ⋅ mpv
    end.

  Lemma translate_slice_inc_hop_spec pi' pe pv i (e : ord _) :
    let j := e_to_dir (Pattern.edir pe) e in
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
                       end >> /\
        << Heprops : Forall (fun '(k, val) => get_eprop G k e = Some val)
                      (Pattern.eprops pe) >> /\
        << Hvprops : Forall (fun '(k, val) => get_vprop G k j = Some val)
                      (Pattern.vprops pv) >>.
  Proof using.
    simpl.
    repeat setoid_rewrite bmx_dot_spec.
    destruct (Pattern.edir pe), (Pattern.vlabel pv).
    all: try setoid_rewrite inc_matrix_spec_OUT.
    all: try setoid_rewrite inc_matrix_inv_spec_IN.
    all: try setoid_rewrite bmx_one_spec.
    all: try setoid_rewrite label_matrix_spec.
    all: try setoid_rewrite inc_label_matrix_spec.
    all: try setoid_rewrite eprops_matrix_inc_spec.
    all: try setoid_rewrite inc_props_matrix_spec.
    all: simpls.
    all: split; ins; desf; eauto 15.
  Qed.

  Section translate_slice_inc_spec.
    Variable pi' : PatternSlice.t.
    Variable pe : Pattern.pedge.
    Variable pv : Pattern.pvertex.
    Variable i : ord vertices_sup.
    Variable e : ord edges_sup.
    Variable r : Rcd.t.
    Variable n_from : Name.t.

    Notation j := (e_to_dir (Pattern.edir pe) e).

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
      apply ord_of_vertex_err_value in Heq; try (subst v || subst i)
    | [ |- _ ] =>
      fail "Hypothesis of the form 'ord_of_vertex_err ?v = Some ?i' not found"
    end.

  Definition r_from (r : Rcd.t) (n_from : Name.t) : option (option (ord vertices_sup)) :=
    match r n_from with
    | Some (Value.GVertex i) => Some (ord_of_vertex_err i)
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
    | Some (Value.GVertex i) =>
      match ord_of_vertex_err i with
      | Some i => Some [i]
      | None => Some []
      end
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
  Proof using.
    unfold candidate_ends, option_bind in Hres. desf.
    { eexists. split.
      { now subst_ord_of_vertex. }
      simpl. left. now apply eq_ord. }
    { rewrite ord_of_vertex_In in HIn. desf. }
    now apply ords_of_vertices_In.
  Qed.
  
  Definition traverse_adj_single (pi' : PatternSlice.t) (n_from : Name.t)
             (r : Rcd.t) : option BindingTable.t :=
    r_from r n_from >>= fun i =>
      match pi' with
      | PatternSlice.hop pi0' pe pv =>
        match i with
        | None => Some []
        | Some i =>
          candidate_ends r (Pattern.vname pv) >>= fun js =>
            let js := filter (translate_slice pi' i) js in
            let update_rcd (j : ord _) :=
                PartialMap.join (Pattern.vname pv |-[Explicit]-> Value.GVertex j) r
              in Some (map update_rcd js)
        end
      | _ => Some [r]
      end.

  Section traverse_adj_single_type.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hres : traverse_adj_single pi' n_from r = Some table'.
    Hypothesis Hpe_imp :
      match pi' with
      | PatternSlice.hop _ pe _ => Name.is_implicit (Pattern.ename pe)
      | PatternSlice.empty => True
      end.

    Lemma traverse_adj_single_type :
      BindingTable.of_type table' (PatternSlice.type_of (Rcd.type_of r) pi').
    Proof using Hwf Hres Hpe_imp.
      unfold traverse_adj_single, option_bind, r_from in Hres.
      desf; intros r' HIn.
      { simpls. desf. }
      rewrite PatternSlice.type_of_wf by auto.
      rewrite in_map_iff in HIn. desf.
      rewrite Rcd.type_of_join.
      rewrite type_of_update_with_mode_start.
      unfold Name.is_implicit in Hpe_imp; desf.
      unfold_update_with_mode. desf.
      now rewrite PartialMap.join_singleton.
    Qed.
  End traverse_adj_single_type.

  Section traverse_adj_single_wf.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hpe_imp :
      match pi' with
      | PatternSlice.hop _ pe _ => Name.is_implicit (Pattern.ename pe)
      | PatternSlice.empty => True
      end.
    Hypothesis Hfrom_type : Rcd.type_of r n_from = Some Value.GVertexT.

    Lemma traverse_adj_single_wf :
      exists table', traverse_adj_single pi' n_from r = Some table'.
    Proof using Hwf_G Hwf Hpe_imp Hfrom_type.
      unfold traverse_adj_single, option_bind, r_from.
      desf.
      all: eauto.
      all: unfold candidate_ends in *; desf.
      all: repeat Rcd.apply_type_of_Value.
      all: inv Hwf; desf.
      all: try rewrite PatternSlice.type_of_wf' in * by auto.
      all: try congruence.
      all: rewrite <- Rcd.type_of_None in *.
      all: congruence.
    Qed.
  End traverse_adj_single_wf.

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
      desf.

      { exists PathSlice.empty. inv HIn. constructor. eauto 2. }

      rewrite in_map_iff in HIn; setoid_rewrite filter_In in HIn; desf.
      change (?x = true) with (is_true x) in *.
      subst_ord_of_vertex.
      match goal with
      | [ H : is_true (translate_slice _ _ _) |- _ ] =>
        eapply translate_slice_spec' in H;
        eauto using candidate_ends_In; desf
      end.

      unfold_update_with_mode.
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
      desf; inv Hmatch.
      { now left. }
      2: { assert (exists x, ord_of_vertex_err v = Some x) as [? ?].
           { rewrite <- ord_of_vertex_In.
             eauto using PathSlice.matches_n_from_In. }
           congruence. }
      subst_ord_of_vertex. inv Hwf.
      apply PathSlice.matches_wf'_eq in Hpi; auto; subst.
      rewrite in_map_iff; setoid_rewrite filter_In. destruct Hpv.
      eapply candidate_ends_In' in vertex_in_g; eauto.
      2: { desf; auto. }
      desc; subst.

      eexists. splits.
      { unfold_update_with_mode.
        simpls. unfold Name.is_implicit in *. desf.
        all: try rewrite PartialMap.join_empty_l.
        all: try rewrite PartialMap.join_singleton.
        all: eauto. }
      { assumption. }
      change (?x = true) with (is_true x) in *.
      eapply translate_slice_spec; eauto; auto.
    Qed.
  End traverse_adj_single_spec.

  Definition ord_of_edge_err e : option (ord edges_sup) :=
    match @In_dec nat _ nat_eqdec e (edges G) with
    | left HInE => Some (ord_of_edge e HInE)
    | right _ => None
    end.

  Lemma ord_of_edge_err_value e i
    (Hres : ord_of_edge_err e = Some i) :
      e = i.
  Proof using.
    unfold ord_of_edge_err in Hres. desf.
  Qed.

  Lemma ord_of_edge_In e :
    In e E <-> exists i, ord_of_edge_err e = Some i.
  Proof using.
    unfold ord_of_edge_err.
    split; ins; desf; eauto.
  Qed.

  Lemma ord_of_edge_In' (e : ord _) :
    In (e : edge) E <-> ord_of_edge_err e = Some e.
  Proof using.
    split; ins.
    { unfold ord_of_edge_err. desf.
      f_equal. now apply eq_ord. }
    apply ord_of_edge_In. eauto.
  Qed.

  Ltac subst_ord_of_edge :=
    match goal with
    | [ H : ord_of_edge_err ?e = Some ?i |- _ ] =>
      let Heq := fresh "Heq" in
      let HInE := fresh "HInE" in
      assert (Heq := H);
      assert (HInE : In e E) by (apply ord_of_edge_In; exists i; apply H);
      apply ord_of_edge_err_value in Heq; try subst e
    | [ |- _ ] =>
      fail "Hypothesis of the form 'ord_of_edge_err ?e = Some ?i' not found"
    end.

  Definition ords_of_edges : list (ord edges_sup) :=
    filter_map ord_of_edge_err (edges G).
  
  Lemma ords_of_edges_In e :
    In e (edges G) <->
      exists (i : ord _), e = i /\ In i ords_of_edges.
  Proof using.
    unfold ords_of_edges.
    setoid_rewrite filter_map_In.
    split.
    { setoid_rewrite ord_of_edge_In.
      ins; desf; eauto 10 using ord_of_edge_err_value. }
    ins; desf. now subst_ord_of_edge.
  Qed.

  Lemma ords_of_edges_In' (e : ord _) :
    In e ords_of_edges <-> In (e : edge) (edges G).
  Proof using.
    rewrite ords_of_edges_In.
    split; ins; desf; eauto.
    assert (e = i) by now apply eq_ord.
    now subst.
  Qed.

  Definition ords_of_edges_to_dir (v : ord vertices_sup) (d : Pattern.direction) : list (ord edges_sup) :=
    let f '(e, u) := ord_of_edge_err e in
      match d with
      | Pattern.OUT => filter_map f (in_edges G v)
      | Pattern.IN => filter_map f (out_edges G v)
      | Pattern.BOTH => [] (* Should not be used *)
      end.

  Lemma ords_of_edges_to_dir_In v d e
    (Hdir : d <> Pattern.BOTH) :
      In e (ords_of_edges_to_dir v d) <->
        e_to_dir d e = v /\
        In (e : edge) E.
  Proof using.
    unfold ords_of_edges_to_dir, e_to_dir.
    split; intros H.
    { destruct d; simpls.
      all: rewrite filter_map_In in H.
      all: destruct H as [[? ?] [? HIn]].
      all: apply in_edges_In in HIn || apply out_edges_In in HIn.
      all: subst_ord_of_edge.
      all: now desc. }
    { destruct d; simpls; desc.
      all: rewrite filter_map_In.
      all: eexists ((e : edge), _).
      all: rewrite in_edges_In || rewrite out_edges_In.
      all: rewrite <- ord_of_edge_In'.
      all: eauto. }
  Qed.

  Definition candidate_edges (r : Rcd.t) (nv : Name.t) (d : Pattern.direction) : option (list (ord edges_sup)) :=
    match r nv with
    | Some (Value.GVertex i) =>
      match ord_of_vertex_err i with
      | Some i => Some (ords_of_edges_to_dir i d)
      | None => Some []
      end
    | None => Some ords_of_edges
    | _ => None
    end.

  Lemma candidate_edges_In r nv d es e
    (Hdir : d <> Pattern.BOTH)
    (Hres : candidate_edges r nv d = Some es)
    (HIn : In e es) :
      r nv = None \/ r nv = Some (Value.GVertex (e_to_dir d e)).
  Proof using.
    unfold candidate_edges, option_bind in Hres. desf.
    { subst_ord_of_vertex.
      eapply ords_of_edges_to_dir_In in HIn; auto; desc.
      right. congruence. }
    now left.
  Qed.

  Lemma candidate_edges_InE r nv d es e
    (Hdir : d <> Pattern.BOTH)
    (Hres : candidate_edges r nv d = Some es)
    (HIn : In e es) :
      In (e : edge) E.
  Proof using.
    unfold candidate_edges, option_bind in Hres. desf.
    { now eapply ords_of_edges_to_dir_In in HIn; auto; desc. }
    now eapply ords_of_edges_In' in HIn.
  Qed.

  Lemma candidate_edges_In' r nv d es e
    (Hres : candidate_edges r nv d = Some es)
    (HIn : In e E)
    (Hdir : d <> Pattern.BOTH)
    (Hprev : r nv = None \/ r nv = Some (Value.GVertex (e_to_dir d e))) :
      exists (e' : ord _), e = e' /\ In e' es.
  Proof using Hwf_G.
    unfold candidate_edges, option_bind in Hres. desf.
    rewrite ords_of_edges_In in HIn. desc.
    { eexists. eauto. }
    { setoid_rewrite ords_of_edges_to_dir_In; auto.
      subst_ord_of_vertex.
      setoid_rewrite ords_of_edges_In in HIn. desc.
      setoid_rewrite <- ords_of_edges_In'.
      eexists; splits; eauto.
      congruence. }
    { assert (exists x, ord_of_vertex_err (e_to_dir d e) = Some x) as [? ?].
      { rewrite <- ord_of_vertex_In.
        auto using e_to_dir_In. }
      congruence. }
  Qed.

  Definition traverse_inc_single' (pi' : PatternSlice.t) (n_from : Name.t)
             (r : Rcd.t) : option BindingTable.t :=
    r_from r n_from >>= fun i =>
      match pi' with
      | PatternSlice.hop pi0' pe pv =>
        match i with
        | Some i =>
          candidate_edges r (Pattern.vname pv) (Pattern.edir pe) >>= fun es =>
            let es := filter (translate_slice_inc pi' i) es in
            let update_rcd (e : ord _) :=
              let j := e_to_dir (Pattern.edir pe) e in
                ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
                  (Value.GVertex j, Value.GEdge e); r)
              in Some (map update_rcd es)
        | None => Some []
        end
      | _ => Some [r]
      end.

  Section traverse_inc_single'_spec.
    Variable pi' : PatternSlice.t.
    Variable pe : Pattern.pedge.
    Variable pv : Pattern.pvertex.
    Variable n_from : Name.t.
    Variable r r' : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) (PatternSlice.hop pi' pe pv).
    Hypothesis Hres : traverse_inc_single' (PatternSlice.hop pi' pe pv) n_from r = Some table'.
    Hypothesis Hedir : Pattern.edir pe <> Pattern.BOTH.

    Theorem traverse_inc_single'_spec'
      (HIn : In r' table') :
        exists p' e, PathSlice.matches G r n_from r'
          (PathSlice.hop p' e (e_to_dir (Pattern.edir pe) e))
          (PatternSlice.hop pi' pe pv).
    Proof using Hwf_G Hres Hwf Hedir.
      unfold traverse_inc_single', option_bind, r_from in Hres.
      desf.

      subst_ord_of_vertex.
      rewrite in_map_iff in HIn; setoid_rewrite filter_In in HIn; desf.
      change (?x = true) with (is_true x) in *.
      match goal with
      | [ H : is_true (translate_slice_inc _ _ _) |- _ ] =>
        eapply translate_slice_inc_spec' in H
      end.
      all: desf; eauto using candidate_edges_In, candidate_edges_InE.
    Qed.

    Theorem traverse_inc_single'_spec p' e
      (Hmatch : PathSlice.matches G r n_from r'
                  (PathSlice.hop p' e (e_to_dir (Pattern.edir pe) e))
                  (PatternSlice.hop pi' pe pv)) :
        In r' table'.
    Proof using Hwf_G Hres Hedir Hwf.
      unfold traverse_inc_single', option_bind, r_from in Hres.
      desf; inv Hmatch.

      2: { assert (exists x, ord_of_vertex_err v = Some x) as [? ?].
           { rewrite <- ord_of_vertex_In.
             eauto using PathSlice.matches_n_from_In. }
           congruence. }

      subst_ord_of_vertex. inv Hwf.
      apply PathSlice.matches_wf'_eq in Hpi; auto; subst.
      rewrite in_map_iff; setoid_rewrite filter_In. destruct Hpe.
      eapply candidate_edges_In' in edge_in_g; eauto.
      desc; subst.

      eexists. splits; eauto.
      change (?x = true) with (is_true x) in *.
      eapply translate_slice_inc_spec; eauto.
      destruct (Pattern.edir pe); simpl in *; auto; contradiction.
    Qed.
  End traverse_inc_single'_spec.

  Section traverse_inc_single'_type.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hres : traverse_inc_single' pi' n_from r = Some table'.

    Lemma traverse_inc_single'_type :
      BindingTable.of_type table' (PatternSlice.type_of (Rcd.type_of r) pi').
    Proof using Hwf Hres.
      unfold traverse_inc_single', option_bind, r_from in Hres.
      desf; intros r' HIn.
      { simpls. desf. }
      rewrite PatternSlice.type_of_wf by auto.
      rewrite in_map_iff in HIn. desf.
      now rewrite type_of_update_with_mode_hop.
    Qed.
  End traverse_inc_single'_type.

  Section traverse_inc_single'_wf.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hfrom_type : Rcd.type_of r n_from = Some Value.GVertexT.

    Lemma traverse_inc_single'_wf :
      exists table', traverse_inc_single' pi' n_from r = Some table'.
    Proof using Hwf_G Hwf Hfrom_type.
      unfold traverse_inc_single', option_bind, r_from.
      desf.
      all: eauto.
      all: unfold candidate_edges in *; desf.
      all: repeat Rcd.apply_type_of_Value.
      all: inv Hwf; desf.
      all: try rewrite PatternSlice.type_of_wf' in * by auto.
      all: try congruence.
      all: rewrite <- Rcd.type_of_None in *.
      all: congruence.
    Qed.
  End traverse_inc_single'_wf.

  Definition set_pedge_dir (pe : Pattern.pedge) (d : Pattern.direction) : Pattern.pedge :=
    Pattern.Build_pedge (Pattern.ename pe) (Pattern.elabel pe) (Pattern.eprops pe) d.
  
  Lemma edir_set_pedge_dir pe d :
    Pattern.edir (set_pedge_dir pe d) = d.
  Proof using. now destruct pe. Qed.

  Definition set_last_pedge_dir (pi' : PatternSlice.t) (d : Pattern.direction) : PatternSlice.t :=
    match pi' with
    | PatternSlice.hop pi0' pe pv =>
      PatternSlice.hop pi0' (set_pedge_dir pe d) pv
    | PatternSlice.empty => PatternSlice.empty
    end.

  Lemma matches_edir_BOTH pi' pe pv p' n_from r r'
    (Hedir : Pattern.edir pe = Pattern.BOTH) :
      PathSlice.matches G r n_from r' p'
        (PatternSlice.hop pi' pe pv) <->
      PathSlice.matches G r n_from r' p'
        (PatternSlice.hop pi' (set_pedge_dir pe Pattern.OUT) pv) \/
      PathSlice.matches G r n_from r' p'
        (PatternSlice.hop pi' (set_pedge_dir pe Pattern.IN) pv).
  Proof using.
    split.
    { intros Hmatch. inv Hmatch.
      rewrite Hedir in Hdir. simpl in Hdir.
      destruct Hdir; [ left | right ].
      1: change (Pattern.ename pe) with (Pattern.ename (set_pedge_dir pe Pattern.OUT)).
      2: change (Pattern.ename pe) with (Pattern.ename (set_pedge_dir pe Pattern.IN)).
      all: constructor; eauto.
      all: destruct Hpe; constructor; auto. }
    intros [Hmatch | Hmatch]; inv Hmatch.
    all: change (Pattern.ename (set_pedge_dir pe _)) with (Pattern.ename pe).
    all: constructor; auto.
    all: try now (destruct Hpe; constructor).
    all: rewrite edir_set_pedge_dir in Hdir; rewrite Hedir.
    all: simpls; auto.
  Qed.

  Lemma set_pedge_dir_wf rT pi' pe pv d
    (Hwf : PatternSlice.wf rT (PatternSlice.hop pi' pe pv)) :
      PatternSlice.wf rT (PatternSlice.hop pi' (set_pedge_dir pe d) pv).
  Proof using. inv Hwf. constructor; auto. Qed.

  Definition traverse_inc_single (pi' : PatternSlice.t) (n_from : Name.t)
             (r : Rcd.t) : option BindingTable.t :=
    match pi' with
    | PatternSlice.hop pi0' pe pv =>
        match Pattern.edir pe with
        | Pattern.BOTH => 
          let pi'_out := set_last_pedge_dir pi' Pattern.OUT in
          let pi'_in := set_last_pedge_dir pi' Pattern.IN in
          let table_out := traverse_inc_single' pi'_out n_from r in
          let table_in := traverse_inc_single' pi'_in n_from r in
          concat_option [table_out; table_in]
        | _ => traverse_inc_single' pi' n_from r
        end
    | _ => Some [r]
    end.
  
  Section traverse_inc_single_spec.
    Variable pi' : PatternSlice.t.
    Variable pe : Pattern.pedge.
    Variable pv : Pattern.pvertex.
    Variable n_from : Name.t.
    Variable r r' : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) (PatternSlice.hop pi' pe pv).
    Hypothesis Hres : traverse_inc_single (PatternSlice.hop pi' pe pv) n_from r = Some table'.

    Theorem traverse_inc_single_spec'
      (HIn : In r' table') :
        exists p' e v, PathSlice.matches G r n_from r'
          (PathSlice.hop p' e v)
          (PatternSlice.hop pi' pe pv).
    Proof using Hwf_G Hres Hwf.
      unfold traverse_inc_single in Hres.
      desf.
      1-2: eapply traverse_inc_single'_spec' in Hres; eauto; try congruence.
      1-2: destruct Hres as [? [? ?]]; eauto.
      apply_concat_option_some_inv_cons.
      destruct Hres as [? [? [? [? Hres']]]]; clear Hres.
      apply_concat_option_some_inv_cons. subst.
      repeat rewrite in_app_iff in HIn.
      rewrite concat_option_nil in *. desf.
      
      all: match goal with
           | [ Hres : (traverse_inc_single' _ _ _) = Some ?x,
               HIn : In _ ?x |- _ ] =>
             eapply traverse_inc_single'_spec' in Hres; desf;
             try rewrite edir_set_pedge_dir in Hres
           end.
      all: eauto.
      all: try now apply set_pedge_dir_wf.
      all: do 3 eexists.
      all: eapply matches_edir_BOTH; eauto.
    Qed.

    Theorem traverse_inc_single_spec p' e v
      (Hmatch : PathSlice.matches G r n_from r'
                  (PathSlice.hop p' e v)
                  (PatternSlice.hop pi' pe pv)) :
        In r' table'.
    Proof using Hwf_G Hres Hwf.
      unfold traverse_inc_single in Hres.
      desf.
      1-2: eapply traverse_inc_single'_spec; eauto; try congruence.
      1-2: erewrite <- matches_last_e_to_dir; eauto; try congruence.

      apply_concat_option_some_inv_cons.
      destruct Hres as [? [? [? [? Hres']]]]; clear Hres.
      apply_concat_option_some_inv_cons. subst.
      repeat rewrite in_app_iff.

      rewrite matches_edir_BOTH in Hmatch; desf; [ left | right; left ].
      all: erewrite matches_last_e_to_dir with (v := v) in Hmatch; eauto.
      all: try now (rewrite edir_set_pedge_dir; simpls).
      all: eapply traverse_inc_single'_spec in Hmatch; eauto.
      all: try now eapply set_pedge_dir_wf.
      all: now rewrite edir_set_pedge_dir.
    Qed.
  End traverse_inc_single_spec.

  Section traverse_inc_single_type.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hres : traverse_inc_single pi' n_from r = Some table'.

    Lemma traverse_inc_single_type :
      BindingTable.of_type table' (PatternSlice.type_of (Rcd.type_of r) pi').
    Proof using Hwf Hres.
      unfold traverse_inc_single in Hres.
      desf; intros r' HIn.
      { simpls. desf. }
      1-2: apply traverse_inc_single'_type in Hres; auto.
      rewrite in_concat_option_iff in HIn; eauto 1; simpls; desf.
      all: apply traverse_inc_single'_type in HIn; auto.
      all: apply set_pedge_dir_wf; auto.
    Qed.
  End traverse_inc_single_type.

  Section traverse_inc_single_wf.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hfrom_type : Rcd.type_of r n_from = Some Value.GVertexT.

    Lemma traverse_inc_single_wf :
      exists table', traverse_inc_single pi' n_from r = Some table'.
    Proof using Hwf_G Hwf Hfrom_type.
      unfold traverse_inc_single.
      desf.
      all: eauto.
      1-2: eapply traverse_inc_single'_wf; eauto.
      simpl.
      apply concat_option_some; intros ? HIn.
      simpls; desf.
      all: eapply traverse_inc_single'_wf; eauto.
      all: apply set_pedge_dir_wf; auto.
    Qed.
  End traverse_inc_single_wf.

  Definition traverse_single (pi' : PatternSlice.t) (n_from : Name.t)
             (r : Rcd.t) : option BindingTable.t :=
    match pi' with
    | PatternSlice.hop pi0' {| Pattern.ename := Name.explicit _ |} pv =>
        traverse_inc_single pi' n_from r
    | _ => traverse_adj_single pi' n_from r
    end.

  Section traverse_single_spec.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r r' : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hres : traverse_single pi' n_from r = Some table'.

    Theorem traverse_single_spec'
      (HIn : In r' table') :
        exists p', PathSlice.matches G r n_from r' p' pi'.
    Proof using Hwf_G Hres Hwf.
      unfold traverse_single in Hres.
      desf.
      1, 3: eapply traverse_adj_single_spec' in Hres; eauto.
      { unfold Name.is_implicit; simpls. }
      eapply traverse_inc_single_spec' in Hres; eauto.
      all: destruct Hres as [? [? [? ?]]]; eauto.
    Qed.

    Theorem traverse_single_spec p'
      (Hmatch : PathSlice.matches G r n_from r' p' pi') :
        In r' table'.
    Proof using Hwf_G Hres Hwf.
      unfold traverse_single in Hres.
      desf.
      1, 3: eapply traverse_adj_single_spec; eauto; simpls.
      inv Hmatch.
      eapply traverse_inc_single_spec; eauto.
    Qed.
  End traverse_single_spec.

  Section traverse_single_type.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.
    Variable table' : BindingTable.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hres : traverse_single pi' n_from r = Some table'.

    Lemma traverse_single_type :
      BindingTable.of_type table' (PatternSlice.type_of (Rcd.type_of r) pi').
    Proof using Hwf Hres.
      unfold traverse_single in Hres.
      desf; intros r' HIn.
      1,3: eapply traverse_adj_single_type; eauto; simpls.
      eapply traverse_inc_single_type; eauto.
    Qed.
  End traverse_single_type.

  Section traverse_single_wf.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable r : Rcd.t.

    Hypothesis Hwf : PatternSlice.wf (Rcd.type_of r) pi'.
    Hypothesis Hfrom_type : Rcd.type_of r n_from = Some Value.GVertexT.

    Lemma traverse_single_wf :
      exists table', traverse_single pi' n_from r = Some table'.
    Proof using Hwf_G Hwf Hfrom_type.
      unfold traverse_single.
      desf.
      all: try now (eapply traverse_adj_single_wf; eauto; simpls).
      all: try now (eapply traverse_inc_single_wf; eauto).
    Qed.
  End traverse_single_wf.

  Definition traverse_impl (pi' : PatternSlice.t) (n_from : Name.t)
             (table : BindingTable.t) : option BindingTable.t :=
    concat_option_map (traverse_single pi' n_from) table.

  Section traverse_impl_spec.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable table table' : BindingTable.t.
    Variable ty : Rcd.T.

    Hypothesis Hwf : PatternSlice.wf ty pi'.
    Hypothesis Hres : traverse_impl pi' n_from table = Some table'.

    Theorem traverse_impl_spec' r'
      (Htype : BindingTable.of_type table ty)
      (HIn : In r' table') :
        exists r p', In r table /\ PathSlice.matches G r n_from r' p' pi'.
    Proof using Hwf_G Hres Hwf.
      unfold traverse_impl in Hres.
      erewrite in_concat_option_map_iff in HIn; eauto 1; desc.
      edestruct traverse_single_spec'; eauto.
      now rewrite Htype.
    Qed.

    Theorem traverse_impl_spec p' r r'
      (Htype : Rcd.type_of r = ty)
      (HIn : In r table)
      (Hmatch : PathSlice.matches G r n_from r' p' pi') :
        In r' table'.
    Proof using Hwf_G Hres Hwf.
      unfold traverse_impl in Hres.
      assert (Hres' := Hres).
      eapply concat_option_map_some_inv in Hres; eauto 1.
      destruct Hres.
      erewrite in_concat_option_map_iff; eauto 1.
      do 2 eexists; splits; eauto 1.
      eapply traverse_single_spec; eauto.
      now rewrite Htype.
    Qed.
  End traverse_impl_spec.

  Lemma type_of_concat_option ty
    (tables : list (option BindingTable.t))
    (table' : BindingTable.t)
    (Hres : concat_option tables = Some table')
    (Htype : forall table, In (Some table) tables ->
              BindingTable.of_type table ty) :
      BindingTable.of_type table' ty.
  Proof using.
    intros r' HIn.
    erewrite in_concat_option_iff in HIn; eauto 1; desc.
    rewrite Htype; eauto 1.
  Qed.

  Lemma type_of_concat_option_map {A} ty
    (xs : list A) (f : A -> option BindingTable.t)
    (table' : BindingTable.t)
    (Hres : concat_option_map f xs = Some table')
    (Htype : forall x table, In x xs -> f x = Some table ->
              BindingTable.of_type table ty) :
      BindingTable.of_type table' ty.
  Proof using.
    intros r' HIn.
    erewrite in_concat_option_map_iff in HIn; eauto 1; desc.
    erewrite Htype; eauto 1.
  Qed.

  Section traverse_impl_type.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable table table' : BindingTable.t.
    Variable ty : Rcd.T.

    Hypothesis Htype : BindingTable.of_type table ty.
    Hypothesis Hwf : PatternSlice.wf ty pi'.
    Hypothesis Hres : traverse_impl pi' n_from table = Some table'.

    Lemma traverse_impl_type :
      BindingTable.of_type table' (PatternSlice.type_of ty pi').
    Proof using Hwf Hres Htype.
      unfold traverse_impl in Hres.
      eapply type_of_concat_option_map; eauto 1.
      ins.
      rewrite <- Htype in * by eauto 1.
      eapply traverse_single_type; eauto 1.
    Qed.
  End traverse_impl_type.

  Section traverse_impl_wf.
    Variable pi' : PatternSlice.t.
    Variable n_from : Name.t.
    Variable table : BindingTable.t.
    Variable ty : Rcd.T.

    Hypothesis Htype : BindingTable.of_type table ty.
    Hypothesis Hwf : PatternSlice.wf ty pi'.
    Hypothesis Hfrom_type : ty n_from = Some Value.GVertexT.

    Lemma traverse_impl_wf :
      exists table', traverse_impl pi' n_from table = Some table'.
    Proof using Hwf_G Htype Hwf Hfrom_type.
      unfold traverse_impl.
      eapply concat_option_map_some; ins.
      rewrite <- Htype in * by eauto 1.
      eapply traverse_single_wf; eauto 1.
      now rewrite Htype by eauto 1.
    Qed.
  End traverse_impl_wf.
End translate.

Definition traverse (pi' : PatternSlice.t) (n_from : Name.t)
  (G : PropertyGraph.t) (table : BindingTable.t) : option BindingTable.t :=
    traverse_impl G pi' n_from table.

Theorem traverse_wf : forall G table ty slice n_from,
  PropertyGraph.wf G -> BindingTable.of_type table ty ->
    PatternSlice.wf ty slice -> ty n_from = Some Value.GVertexT ->
      exists table', traverse slice n_from G table = Some table'.
Proof using. eauto using traverse_impl_wf. Qed.

Theorem traverse_type G table table' ty slice n_from
  (Hres : traverse slice n_from G table = Some table')
  (Htype : BindingTable.of_type table ty)
  (Hwf : PatternSlice.wf ty slice) :
    BindingTable.of_type table' (PatternSlice.type_of ty slice).
Proof using. eauto using traverse_impl_type. Qed.

Theorem traverse_spec G table table' path r r' slice n_from
  (Hwf : PropertyGraph.wf G)
  (Hwf_slice : PatternSlice.wf (Rcd.type_of r) slice)
  (Hres : traverse slice n_from G table = Some table')
  (Hmatch : PathSlice.matches G r n_from r' path slice)
  (HIn : In r table) :
    In r' table'.
Proof using. eauto using traverse_impl_spec. Qed.

Theorem traverse_spec' G table table' ty r' slice n_from
  (Hwf : PropertyGraph.wf G)
  (Htype : BindingTable.of_type table ty)
  (Hwf_slice : PatternSlice.wf ty slice)
  (Hres : traverse slice n_from G table = Some table')
  (HIn : In r' table') :
    exists r path, In r table /\
      PathSlice.matches G r n_from r' path slice.
Proof using. eauto using traverse_impl_spec'. Qed.
