Require Import Utils.
Require Import Maps.
Require Import PropertyGraph.
Require Import Cypher.
Require Import BindingTable.
Require Import Semantics.
Require Import PatternE.
Require Import ExecutionPlan.
Require TraverseOpImpl.

Import PartialMap.Notations.
Import TotalMap.Notations.
Import PropertyGraph.
Import ExecutionPlan.
Import FilterMode.
Import ExpandMode.
Import MatchMode.
Import UpdateNotations.

Module ExecutionPlanImpl : ExecutionPlan.Spec.

  Definition scan_vertices (n : Name.t)
                           (graph : PropertyGraph.t) :
    option BindingTable.t :=
    Some (map (fun v => n |-> Value.GVertex v) (vertices graph)).

  Section filter_by_label.
    Variable mode : FilterMode.t.
    Variable n : Name.t.
    Variable l : PropertyGraph.label.
    Variable graph : PropertyGraph.t.
    Variable table : BindingTable.t.

    Definition vertex_has_label (r : Rcd.t) : bool :=
      match r n with
      | Some (Value.GVertex v) => In_decb l (vlabels graph v)
      | _ => false
      end.

    Definition edge_has_label (r : Rcd.t) : bool :=
      match r n with
      | Some (Value.GEdge e) => elabel graph e ==b l
      | _ => false
      end.

    Definition has_label : Rcd.t -> bool :=
      match mode with
      | Vertices => vertex_has_label
      | Edges => edge_has_label
      end.

    Definition filter_by_label : option BindingTable.t :=
      Some (filter has_label table).
  End filter_by_label.

  #[local]
  Hint Unfold filter_by_label has_label vertex_has_label edge_has_label : filter_by_label_db.

  Section filter_by_property.
    Variable mode : FilterMode.t.
    Variable n : Name.t.
    Variable k : Property.name.
    Variable val : Property.t.
    Variable graph : PropertyGraph.t.
    Variable table : BindingTable.t.

    Definition vertex_has_prop (r : Rcd.t) : bool :=
      match r n with
      | Some (Value.GVertex v) => get_vprop graph k v ==b Some val
      | _ => false
      end.

    Definition edge_has_prop (r : Rcd.t) : bool :=
      match r n with
      | Some (Value.GEdge e) => get_eprop graph k e ==b Some val
      | _ => false
      end.

    Definition has_prop : Rcd.t -> bool :=
      match mode with
      | Vertices => vertex_has_prop
      | Edges => edge_has_prop
      end.

    Definition filter_by_property : option BindingTable.t :=
      Some (filter has_prop table).
  End filter_by_property.

  #[local]
  Hint Unfold filter_by_property has_prop vertex_has_prop edge_has_prop : filter_by_property_db.

  Section expand.
    Variable mode : ExpandMode.t.
    Variable n_from n_edge n_to : Name.t.
    Variable d : Pattern.direction.
    Variable graph : PropertyGraph.t.
    Variable table : BindingTable.t.

    Definition expand_all_single (r : Rcd.t) : option BindingTable.t :=
      match r n_from, r n_edge, r n_to with
      | Some (Value.GVertex v_from), None, None =>
        Some (map (fun '(e, v_to) => n_to   |-> Value.GVertex v_to;
                                     n_edge |-> Value.GEdge e; r)
          match d with
          | Pattern.OUT  => out_edges graph v_from
          | Pattern.IN   => in_edges  graph v_from
          | Pattern.BOTH => out_edges graph v_from ++
                            in_edges  graph v_from
          end)
      | _, _, _ => None
      end.

    Definition expand_into_single (r : Rcd.t) : option BindingTable.t :=
      match r n_from, r n_edge, r n_to with
      | Some (Value.GVertex v_from), None, Some (Value.GVertex v_to) =>
          Some (map (fun e => n_to   |-> Value.GVertex v_to;
                              n_edge |-> Value.GEdge e; r)
          match d with
          | Pattern.OUT  => edges_between graph v_from v_to
          | Pattern.IN   => edges_between graph v_to   v_from
          | Pattern.BOTH => edges_between graph v_from v_to ++
                            edges_between graph v_to   v_from
          end)
      | _, _, _ => None
      end.

    Definition expand_single (r : Rcd.t) : option BindingTable.t :=
      match mode with
      | All => expand_all_single r
      | Into => expand_into_single r
      end.

    Definition expand : option BindingTable.t :=
      option_map (@List.concat Rcd.t) (fold_option (map expand_single table)).
  End expand.

  #[local]
  Hint Unfold expand expand_single expand_all_single expand_into_single : expand_db.

  Definition return_all (graph : PropertyGraph.t) (table : BindingTable.t) :=
    Some (map Rcd.explicit_proj table).

  (** If the inputs are well-formed then the operation will return the result *)

  Theorem scan_vertices_wf graph n (Hwf : PropertyGraph.wf graph) :
    exists table', scan_vertices n graph = Some table'.
  Proof using. now eexists. Qed.

  Theorem filter_by_label_wf graph table ty mode n l
                             (Hwf : PropertyGraph.wf graph)
                             (Htype : BindingTable.of_type table ty)
                             (Hty : match mode with
                                    | Vertices => ty n = Some Value.GVertexT
                                    | Edges    => ty n = Some Value.GEdgeT
                                    end) :
    exists table', filter_by_label mode n l graph table = Some table'.
  Proof using.
    autounfold with filter_by_label_db.
    all: induction table as [| r table IH]; ins; eauto.
  Qed.

  Theorem filter_vertices_by_label_wf graph table ty n l
                                    (Hwf : PropertyGraph.wf graph)
                                    (Htype : BindingTable.of_type table ty)
                                    (Hty : ty n = Some Value.GVertexT) :
    exists table', filter_by_label Vertices n l graph table = Some table'.
  Proof using. eapply filter_by_label_wf with (mode := Vertices); eassumption. Qed.

  Theorem filter_edges_by_label_wf graph table ty n l
                                 (Hwf : PropertyGraph.wf graph)
                                 (Htype : BindingTable.of_type table ty)
                                 (Hty : ty n = Some Value.GEdgeT) :
    exists table', filter_by_label Edges n l graph table = Some table'.
  Proof using. eapply filter_by_label_wf with (mode := Edges); eassumption. Qed.

  Theorem filter_by_property_wf graph table ty mode n k val
                                (Hwf : PropertyGraph.wf graph)
                                (Htype : BindingTable.of_type table ty)
                                (Hty : match mode with
                                       | Vertices => ty n = Some Value.GVertexT
                                       | Edges    => ty n = Some Value.GEdgeT
                                       end) :
    exists table', filter_by_property mode n k val graph table = Some table'.
  Proof using.
    autounfold with filter_by_property_db.
    all: induction table as [| r table IH]; ins; eauto.
  Qed.

  Theorem filter_vertices_by_property_wf graph table ty n k val
                                    (Hwf : PropertyGraph.wf graph)
                                    (Htype : BindingTable.of_type table ty)
                                    (Hty : ty n = Some Value.GVertexT) :
    exists table', filter_by_property Vertices n k val graph table = Some table'.
  Proof using. eapply filter_by_property_wf with (mode := Vertices); eassumption. Qed.

  Theorem filter_edges_by_property_wf graph table ty n k val
                                 (Hwf : PropertyGraph.wf graph)
                                 (Htype : BindingTable.of_type table ty)
                                 (Hty : ty n = Some Value.GEdgeT) :
    exists table', filter_by_property Edges n k val graph table = Some table'.
  Proof using. eapply filter_by_property_wf with (mode := Edges); eassumption. Qed.

  Theorem expand_wf graph table ty mode n_from n_edge n_to d
                    (Hwf : PropertyGraph.wf graph)
                    (Htype : BindingTable.of_type table ty)
                    (Hty_from : ty n_from = Some Value.GVertexT)
                    (Hty_edge : ty n_edge = None)
                    (Hty_to   : match mode with
                                | All => ty n_to = None
                                | Into => ty n_to = Some Value.GVertexT 
                                end) :
    exists table', expand mode n_from n_edge n_to d graph table = Some table'.
  Proof using.
    all: autounfold with expand_db.
    
    eenough (exists t, fold_option _ = Some t) as [t Hfold].
    { rewrite Hfold. now eexists. }

    apply fold_option_some; intros a HIn; simpls.
    apply in_map_iff in HIn as [r [? ?]]; subst.

    edestruct BindingTable.type_of_GVertexT with (k := n_from) as [v_from Hv_from];
      try eassumption.
    rewrite Hv_from.

    destruct mode.
    2: edestruct BindingTable.type_of_GVertexT with (k := n_to) as [v_to Hv_to];
        try eassumption.
    2: rewrite Hv_to.
    all: repeat erewrite BindingTable.type_of_None; try eassumption.
    all: now eexists.
  Qed.

  Theorem expand_all_wf graph table ty n_from n_edge n_to d
                  (Hwf : PropertyGraph.wf graph)
                  (Htype : BindingTable.of_type table ty)
                  (Hty_from : ty n_from = Some Value.GVertexT)
                  (Hty_edge : ty n_edge = None)
                  (Hty_to   : ty n_to   = None) :
    exists table', expand All n_from n_edge n_to d graph table = Some table'.
  Proof using. eapply expand_wf with (mode := All); eassumption. Qed.

  Theorem expand_into_wf graph table ty n_from n_edge n_to d
                  (Hwf : PropertyGraph.wf graph)
                  (Htype : BindingTable.of_type table ty)
                  (Hty_from : ty n_from = Some Value.GVertexT)
                  (Hty_edge : ty n_edge = None)
                  (Hty_to   : ty n_to   = Some Value.GVertexT) :
    exists table', expand Into n_from n_edge n_to d graph table = Some table'.
  Proof using. eapply expand_wf with (mode := Into); eassumption. Qed.

  Theorem return_all_wf graph table :
    exists table', return_all graph table = Some table'.
  Proof using. now eexists. Qed.

  (** If the operation returned some table then the type of the table is correct *)
  
  Theorem scan_vertices_type graph table' n 
                           (Hres : scan_vertices n graph = Some table') :
    BindingTable.of_type table' (n |-> Value.GVertexT).
  Proof using.
    unfold scan_vertices in Hres.
    injection Hres as Hres. subst. intros r' HIn.
    apply in_map_iff in HIn as [r [Heq HIn]].
    subst.
    solve_type_of.
  Qed.
  
  Theorem filter_by_label_type graph table table' ty mode n l
    (Hres : filter_by_label mode n l graph table = Some table')
    (Htype : BindingTable.of_type table ty) :
      BindingTable.of_type table' ty.
  Proof using.
    generalize dependent table'.
    destruct mode.
    all: autounfold with filter_by_label_db.
    all: induction table; ins; desf; eauto with type_of_db.
  Qed.

  Theorem filter_by_property_type graph table table' ty mode n k val
    (Hres : filter_by_property mode n k val graph table = Some table')
    (Htype : BindingTable.of_type table ty) :
      BindingTable.of_type table' ty.
  Proof using.
    generalize dependent table'.
    destruct mode.
    all: autounfold with filter_by_property_db.
    all: induction table; ins; desf; eauto with type_of_db.
  Qed.

  Theorem expand_single_type graph r table' mode n_from n_edge n_to d
    (Hres : expand_single mode n_from n_edge n_to d graph r = Some table') :
      BindingTable.of_type table'
        (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; Rcd.type_of r).
  Proof using.
    autounfold with expand_db in *.
    desf.
    all: intros r' HIn'.
    all: apply in_map_iff in HIn'; desf.
    all: solve_type_of_extension r (Rcd.type_of r).
  Qed.

  Theorem expand_type graph table table' ty mode n_from n_edge n_to d
                          (Hres : expand mode n_from n_edge n_to d graph table = Some table')
                          (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table'
      (n_to |-> Value.GVertexT; n_edge |-> Value.GEdgeT; ty).
  Proof using.
    unfold expand in *.
    unfold option_map in Hres; desf.
    destruct mode.

    all: apply BindingTable.of_type_concat; intros table' HIn_tables'.
    all: eassert (Hmap : In (Some table') (map _ table))
          by (eapply fold_option_In; eauto).

    all: apply in_map_iff in Hmap as [r ?]; desf.
    all: assert (Rcd.type_of r = ty) as Hty by auto; subst.
    all: eauto using expand_single_type.
  Qed.

  Theorem return_all_type graph table table' ty
                          (Hres : return_all graph table = Some table')
                          (Htype : BindingTable.of_type table ty) :
    BindingTable.of_type table' (Rcd.explicit_projT ty).
  Proof using.
    intros r' HIn.
    unfold return_all in Hres.
    injection Hres as ?; subst.
    apply in_map_iff in HIn as [r [? HIn]]; subst.
    rewrite Rcd.type_of_explicit_proj.
    now rewrite Htype with r.
  Qed.

  (** scan_vertices specification *)

  
  Theorem scan_vertices_spec graph table' n v
    (Hres : scan_vertices n graph = Some table')
    (HIn : In v (vertices graph)) :
      In (n |-> Value.GVertex v) table'.
  Proof using.
    unfold scan_vertices in Hres.
    inj_subst.
    apply in_map_iff.
    exists v. auto.
  Qed.

  Theorem scan_vertices_spec' graph table' n r'
    (Hres : scan_vertices n graph = Some table')
    (HIn : In r' table') :
      exists v, r' = (n |-> Value.GVertex v) /\ In v (vertices graph).
  Proof using.
    unfold scan_vertices in Hres.
    inj_subst.
    apply in_map_iff in HIn as [v [Heq HIn]].
    subst. exists v. auto.
  Qed.

  (** filter_by_label specification *)

  Theorem vertex_has_label_true_iff graph n l r :
    vertex_has_label n l graph r = true <->
      exists v, r n = Some (Value.GVertex v) /\ In l (vlabels graph v).
  Proof using.
    split; ins.
    all: unfold vertex_has_label in *.
    all: desf; normalize_bool.
    { eexists. split; eauto. }
    now rewrite -> In_decb_true_iff.
  Qed.

  Theorem edge_has_label_true_iff graph n l r :
    edge_has_label n l graph r = true <->
      exists e, r n = Some (Value.GEdge e) /\ elabel graph e = l.
  Proof using.
    split; ins.
    all: unfold edge_has_label in *.
    all: desf.
    { eexists. split. { eauto. }
      now rewrite <- equiv_decb_true_iff. }
    now rewrite -> equiv_decb_true_iff.
  Qed.

  Theorem filter_by_label_spec graph table table' mode n l r 
    (Hres : filter_by_label mode n l graph table = Some table') :
      match mode with
      | Vertices => In r table' <-> In r table /\
          (exists v, r n = Some (Value.GVertex v) /\ In l (vlabels graph v))
      | Edges    => In r table' <-> In r table /\
          (exists e, r n = Some (Value.GEdge e) /\ elabel graph e = l)
      end.
  Proof using.
    unfold filter_by_label, has_label in Hres.
    inj_subst.
    destruct mode; ins.
    all: rewrite filter_In.
    1: rewrite -> vertex_has_label_true_iff; try eassumption.
    2: rewrite -> edge_has_label_true_iff; try eassumption.
    all: reflexivity.
  Qed.

  Theorem filter_vertices_by_label_spec graph table table' n l v r 
    (Hres : filter_by_label Vertices n l graph table = Some table')
    (Hval : r n = Some (Value.GVertex v)) (Hlabel : In l (vlabels graph v))
    (HIn : In r table) : In r table'.
  Proof using.
    rewrite -> filter_by_label_spec with (mode := Vertices); eauto.
  Qed.
  
  Theorem filter_vertices_by_label_spec' graph table table' n l r' 
    (Hres : filter_by_label Vertices n l graph table = Some table')
    (HIn : In r' table') : In r' table /\
        exists v, r' n = Some (Value.GVertex v) /\ In l (vlabels graph v).
  Proof using.
    rewrite <- filter_by_label_spec with (mode := Vertices); eauto.
  Qed.

  Theorem filter_edges_by_label_spec graph table table' n l e r 
    (Hres : filter_by_label Edges n l graph table = Some table')
    (Hval : r n = Some (Value.GEdge e)) (Hlabel : elabel graph e = l)
    (HIn : In r table) : In r table'.
  Proof using.
    rewrite -> filter_by_label_spec with (mode := Edges); eauto.
  Qed.
  
  Theorem filter_edges_by_label_spec' graph table table' n l r' 
    (Hres : filter_by_label Edges n l graph table = Some table')
    (HIn : In r' table') : In r' table /\
        exists e, r' n = Some (Value.GEdge e) /\ elabel graph e = l.
  Proof using.
    rewrite <- filter_by_label_spec with (mode := Edges); eauto.
  Qed.

  (** filter_by_property specification *)

  Theorem vertex_has_prop_true_iff graph n k val r :
    vertex_has_prop n k val graph r = true <->
      exists v, r n = Some (Value.GVertex v) /\ get_vprop graph k v = Some val.
  Proof using.
    split; ins.
    all: unfold vertex_has_prop in *.
    all: desf; normalize_bool.
    { eexists. split; eauto. }
    now rewrite -> equiv_decb_true_iff.
  Qed.

  Theorem edge_has_prop_true_iff graph n k val r :
    edge_has_prop n k val graph r = true <->
      exists e, r n = Some (Value.GEdge e) /\ get_eprop graph k e = Some val.
  Proof using.
    split; ins.
    all: unfold edge_has_prop in *.
    all: desf; normalize_bool.
    { eexists. split; eauto. }
    now rewrite -> equiv_decb_true_iff.
  Qed.

  Theorem filter_by_property_spec graph table table' mode n k val r 
    (Hres : filter_by_property mode n k val graph table = Some table') :
      match mode with
      | Vertices => In r table' <-> In r table /\
          (exists v, r n = Some (Value.GVertex v) /\ get_vprop graph k v = Some val)
      | Edges    => In r table' <-> In r table /\
          (exists e, r n = Some (Value.GEdge e) /\ get_eprop graph k e = Some val)
      end.
  Proof using.
    unfold filter_by_property, has_prop in Hres.
    inj_subst.
    destruct mode; ins.
    all: rewrite filter_In.
    1: rewrite -> vertex_has_prop_true_iff; try eassumption.
    2: rewrite -> edge_has_prop_true_iff; try eassumption.
    all: reflexivity.
  Qed.

  Theorem filter_vertices_by_property_spec graph table table' n k val v r 
    (Hres : filter_by_property Vertices n k val graph table = Some table')
    (Hval : r n = Some (Value.GVertex v)) (Hprop : get_vprop graph k v = Some val)
    (HIn : In r table) : In r table'.
  Proof using.
    rewrite -> filter_by_property_spec with (mode := Vertices); eauto.
  Qed.
  
  Theorem filter_vertices_by_property_spec' graph table table' n k val r' 
    (Hres : filter_by_property Vertices n k val graph table = Some table')
    (HIn : In r' table') : In r' table /\
      exists v, r' n = Some (Value.GVertex v) /\ get_vprop graph k v = Some val.
  Proof using.
    rewrite <- filter_by_property_spec with (mode := Vertices); eauto.
  Qed.

  Theorem filter_edges_by_property_spec graph table table' n k val e r 
    (Hres : filter_by_property Edges n k val graph table = Some table')
    (Hval : r n = Some (Value.GEdge e)) (Hprop : get_eprop graph k e = Some val)
    (HIn : In r table) : In r table'.
  Proof using.
    rewrite -> filter_by_property_spec with (mode := Edges); eauto.
  Qed.
  
  Theorem filter_edges_by_property_spec' graph table table' n k val r' 
    (Hres : filter_by_property Edges n k val graph table = Some table')
    (HIn : In r' table') : In r' table /\
      exists e, r' n = Some (Value.GEdge e) /\ get_eprop graph k e = Some val.
  Proof using.
    rewrite <- filter_by_property_spec with (mode := Edges); eauto.
  Qed.
  
  (** expand specification *)

  Theorem expand_single_spec graph table' r r' mode n_from n_edge n_to d
    (Hres : expand_single mode n_from n_edge n_to d graph r = Some table') :
      expansion_of graph r' r mode n_from n_edge n_to d <-> In r' table'.
  Proof using.
    split; ins.
    all: unfold expansion_of, expansion_of', Path.matches_direction in *.

    - destruct mode; desf.
      all: autounfold with expand_db in Hres.
      all: rewrite Hval_from, Hval_to in Hres; desf.
      all: apply in_map_iff.
      all: try exists (e, v_to).
      all: try exists e.
      all: split; [ reflexivity | ].
      all: try apply in_or_app.
      all: try rewrite -> in_edges_In.
      all: try rewrite -> out_edges_In.
      all: repeat rewrite -> edges_between_In.
      all: unfold e_from, e_to; destruct (ends graph e); desf.
      all: auto.

    - all: autounfold with expand_db in Hres.
      destruct mode; desf.
      all: match goal with
           | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; desf
           end.
      all: try match goal with
           | [ H : In _ (_ ++ _) |- _ ] => apply in_app_or in H
           end; desf.
      all: match goal with
           | [ H : In _ (out_edges       _ _) |- _ ] =>
               apply out_edges_In in H
           | [ H : In _ (in_edges        _ _) |- _ ] =>
               apply in_edges_In in H
           | [ H : In _ (edges_between _ _ _) |- _ ] =>
               apply edges_between_In in H
           end; desf.
      all: do 3 eexists.
      all: splits; eauto.

      all: unfold e_from, e_to in *; edestruct (ends graph _); desf; simpls.
      all: auto.
  Qed.

  Theorem expand_spec graph table table' r r' mode n_from n_edge n_to d
      (Hres : expand mode n_from n_edge n_to d graph table = Some table')
      (Hexp : expansion_of graph r' r mode n_from n_edge n_to d)
      (HIn : In r table) : In r' table'.
  Proof using.
    unfold expand in *.

    edestruct (fold_option _) as [tables' | ] eqn:Hfold.
    2: now inv Hres.
    simpls; inj_subst.

    eassert (Hmap : In (_ r) (map _ table)) by (now eapply in_map).

    eassert (exists table', _ r = Some table') as [table' Hres].
    { eapply fold_option_some_inv in Hfold as [table' Heq]; eauto. }

    apply in_concat. exists table'. split.
    2: now eapply expand_single_spec; eauto.
    eapply fold_option_In; eauto.
    unfold BindingTable.t in *.
    now rewrite <- Hres.
  Qed.

  Theorem expand_spec' graph table table' r' mode n_from n_edge n_to d
    (Hres : expand mode n_from n_edge n_to d graph table = Some table')
    (HIn : In r' table') :
      exists r, In r table /\
                expansion_of graph r' r mode n_from n_edge n_to d.
  Proof using.
    unfold expand in *.
    edestruct (fold_option _) as [tables' | ] eqn:?.
    2: now inv Hres.
    simpls; inj_subst.

    apply in_concat in HIn as [table' ?]; desf.
    eassert (Hmap : In (Some table') (map _ table)).
    { eapply fold_option_In; eassumption. }

    apply in_map_iff in Hmap as [r ?]; desf.
    exists r. split.
    { assumption. }
    eapply expand_single_spec; eassumption.
  Qed.

  (* return_all specification *)

  Theorem return_all_spec graph table table' r
    (Hres : return_all graph table = Some table')
    (HIn : In r table) :
      In (Rcd.explicit_proj r) table'.
  Proof using.
    unfold return_all in *.
    injection Hres as ?; subst.
    eapply in_map in HIn.
    eassumption.
  Qed.

  Theorem return_all_spec' graph table table' r'
    (Hres : return_all graph table = Some table')
    (HIn : In r' table') :
      exists r, In r table /\ r' = Rcd.explicit_proj r.
  Proof using.
    unfold return_all in *.
    injection Hres as ?; subst.
    apply in_map_iff in HIn as [r ?]; desf.
    eauto.
  Qed.

  (* traversion *)

  Definition traverse := TraverseOpImpl.traverse.
  Definition traverse_wf := TraverseOpImpl.traverse_wf.
  Definition traverse_type := TraverseOpImpl.traverse_type.
  Definition traverse_spec := TraverseOpImpl.traverse_spec.
  Definition traverse_spec' := TraverseOpImpl.traverse_spec'.
End ExecutionPlanImpl.
