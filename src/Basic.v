Require Import String.
From hahn Require Import Hahn.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Aux.
Variable T : eqType.

Fixpoint list_eqb (l l' : list T) : bool :=
  match l, l' with
  | [], [] => true
  | a::l, b::l' =>
    eq_op a b && (list_eqb l l')
  | _, _ => false
  end.

Lemma list_eqP : Equality.axiom list_eqb.
Proof using T.
  red. induction x.
  { ins. destruct y; constructor; desf. }
  ins. desf.
  { constructor. desf. }
  destruct (eq_op a s) eqn:HH; subst; ins.
  2: { constructor. intros AA. inv AA. rewrite beq_refl in HH. inv HH. }
  specialize (IHx l).
  apply Bool.reflect_iff in IHx.
  apply Bool.iff_reflect.
  etransitivity; eauto.
  split; intros AA; desf.
  apply hahn__beq_rewrite in HH. desf.
Qed.

Canonical Structure list_eqMixin := EqMixin list_eqP.
Canonical Structure list_eqType := Eval hnf in EqType (list T) list_eqMixin.

Fixpoint list_inb {T : eqType} x (l : list T) : bool :=
  match l with
  | [] => false
  | a::l => eq_op x a || list_inb x l
  end.
End Aux.

Definition vertex    := nat.
Definition edge      := nat.
Definition label     := string.
Definition attribute := string.

Module Attribute.
  Definition t := string.
  
  Definition eqb (s s' : t) := String.eqb s s'.

  Lemma eqP : Equality.axiom eqb.
  Proof. unfold eqb. red. apply eqb_spec. Qed.
End Attribute.

Canonical Structure attribute_eqMixin := EqMixin Attribute.eqP.
Canonical Structure attribute_eqType := Eval hnf in EqType Attribute.t attribute_eqMixin.

Module Scheme.
  Definition t := list Attribute.t.
  
  Definition eqb (s s' : t) : bool := list_eqb _ s s'.

  Lemma eqP : Equality.axiom eqb.
  Proof. apply list_eqP. Qed.
End Scheme.

Canonical Structure scheme_eqMixin := EqMixin Scheme.eqP.
Canonical Structure scheme_eqType := Eval hnf in EqType Scheme.t scheme_eqMixin.

Module Property.
  Inductive t := 
  | p_int (i : nat)
  | p_string (s : string)
  | p_empty
  .
  
  Definition name := string.
  
  Definition eqb (p p' : t) : bool :=
    match p, p' with
    | p_int i, p_int i' => Nat.eqb i i'
    | p_string s, p_string s' => String.eqb s s'
    | p_empty, p_empty => true
    | _, _ => false
    end.

  Lemma eqP : Equality.axiom eqb.
  Proof.
    unfold eqb. red. ins. desf; try constructor; desf.
    all: apply Bool.iff_reflect.
    all: symmetry; etransitivity.
    all: try apply PeanoNat.Nat.eqb_eq; try apply String.eqb_eq.
    all: split; intros AA; subst; auto.
    all: inv AA.
  Qed.
End Property.

Canonical Structure property_eqMixin := EqMixin Property.eqP.
Canonical Structure property_eqType := Eval hnf in EqType Property.t property_eqMixin.

Module Relation.
  Record t :=
    mk { (* sch *)
        scheme : Scheme.t;
        data   : list (list Property.t);
      }.
  
  Record wf (r : Relation.t) :=
    { scheme_len : forall l (IN : List.In l (data r)),
        List.length l = List.length (scheme r);
    }.

  Definition bag_union r r' : option t :=
    if Scheme.eqb (scheme r) (scheme r')
    then Some (mk (scheme r) 
                  (app (data r) (data r')))
    else None.

  Definition union r r' : option t :=
    if Scheme.eqb (scheme r) (scheme r')
    then Some (mk (scheme r) 
                  (app (data r)
                       (filter
                          (fun l => negb (list_inb l (data r)))
                          (data r'))))
    else None.
End Relation.

Module PropertyGraph.
  Record t :=
    mk { (* V *)
        vertices : list vertex;
        (* E *)
        edges    : list edge;
        (* st *)
        st       : edge -> vertex * vertex;

        (* \mathcal{L}*)
        vlab     : list (vertex * label);
        (* \mathcal{T}*)
        elab     : edge -> label;
        
        (* Pᵥ *)
        vprop    : list (Property.name * (vertex -> Property.t)); 
        (* Pₑ *)
        eprop    : list (Property.name * (edge   -> Property.t)); 
      }.
End PropertyGraph.
