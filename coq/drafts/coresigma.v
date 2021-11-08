From Coq Require Import Arith List Omega Program.
From Equations Require Import Equations.

(* dependent destruction, see https://jamesrwilcox.com/dep-destruct.html *)
Require Import Program.
(* === index spaces definition utils === *)
From Coq Require Import Lia.

Require Import Coq.Vectors.Fin.

(* transport in HoTT, maybe useful looking at these libraries *)
Definition transport {T: Type} {x y: T} {P: T -> Type} (u: P x)
  (pf: x = y): P y := match pf with | eq_refl => u end.

Module Array.
Section Array.
  Context {E: Type}.

  Definition Fin n := { i: nat | i < n }.
  Definition Shape dim := { s: list nat | length s = dim }.

  Program Definition tail_shape {dim} (shape: Shape (S dim)) : Shape dim := exist _ (tl (` shape)) _.
  Next Obligation. (* length (tl (` shape)) = dim *)
  destruct shape as [shape_list shape_list_has_length_Sdim].
  destruct shape_list as [|shape_list_O shape_list']; simpl.
  (* 0 = dim *)
  + simpl in shape_list_has_length_Sdim. exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
  (* length shape_list' = dim *)
  + simpl in shape_list_has_length_Sdim. apply (eq_add_S _ _ shape_list_has_length_Sdim).
  Defined.

  Definition get (l: list nat) (i: nat) := nth i l 0.

  Definition Index {dim} (shape: Shape dim) :=
    { ix : list nat |  length ix = dim
                    /\ forall (i: Fin dim), get ix (` i) < get (` shape) (` i) }.

  Program Definition tail_ix {dim} {shape: Shape (S dim)} (ix: Index shape) : Index (tail_shape shape) :=
    exist _ (tl (` ix)) _.
  Next Obligation. split.
  (* length (tl (` ix)) = dim *)
  + destruct ix as [ix_list ix_list_properties]; simpl.
    destruct ix_list_properties as [ix_list_has_length_Sdim junk].
    destruct ix_list as [|ix_list_O ix_list'].
    (* absurd *)
    - simpl in ix_list_has_length_Sdim. exfalso; apply (Nat.neq_0_succ _ ix_list_has_length_Sdim).
    (* length ix_list' = dim *)
    - simpl; simpl in ix_list_has_length_Sdim. apply (eq_add_S _ _ ix_list_has_length_Sdim).
  (* forall i : Fin dim, get (tl (` ix)) (` i) < get (tl (` shape)) (` i) *)
  + intro i. destruct ix as [ix_list ix_list_properties]; simpl.
    destruct ix_list_properties as [ix_list_has_length_Sdim ix_list_is_in_shape].
    destruct ix_list as [|ix_list_O ix_list']; simpl.
    (* absurd *)
    - simpl in ix_list_has_length_Sdim. exfalso; apply (Nat.neq_0_succ _ ix_list_has_length_Sdim).
    (* get ix_list' (` i) < get (tl (` shape)) (` i) *)
    - destruct shape as [shape_list shape_list_has_length_Sdim]; simpl.
      destruct shape_list as [|shape_list_O shape_list'].
      (* absurd *)
      * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
      (* get ix_list' (` i) < get shape_list' (` i) *)
      * simpl; simpl in ix_list_is_in_shape.
        destruct i as [i_val i_val_lt_dim]; simpl. Search (S ?x <= S ?y).
        apply (ix_list_is_in_shape (exist _ (S i_val) (le_n_S _ _ i_val_lt_dim))).
  Defined.

  Definition Array {dim} E (shape : Shape dim) :=
    Index shape -> E.

  Definition pi {dim} (shape: Shape dim) : nat :=
    fold_right (fun x y => x * y) 1 (` shape).

  Program Fixpoint to_lin {dim} {shape: Shape (S dim)} (ix: Index shape) : nat :=
    match dim with | O => hd O ix
                   | S dim' => let shape_tail := exist _ (tl (` shape)) _ in
                               let ix_tail : Index shape_tail := exist _ (tl (` ix)) _ in
                               hd O ix * (pi shape_tail) + (to_lin (dim:=dim') ix_tail)
    end.
  Next Obligation. (* length (tl (` shape)) = S dim' *)
  destruct shape as [shape_list shape_list_has_length_SSdim']; simpl.
  destruct shape_list as [|shape_list_O shape_list'].
  (* length (tl nil) = S dim' *)
  + simpl in shape_list_has_length_SSdim'. exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_SSdim').
  (* length (tl (shape_list_O :: shape_list')) = S dim' *)
  + simpl; simpl in shape_list_has_length_SSdim'. apply (eq_add_S _ _ shape_list_has_length_SSdim').
  Defined.
  Next Obligation. split.
  (* length (tl (` ix)) = S dim' *)
  + destruct ix as [ix_list ix_list_properties]; destruct ix_list_properties as [length_ix_is_SSdim' ix_is_in_shape]; simpl.
    destruct ix_list as [|ix_list_O ix_list'].
    (* length (tl nil) = S dim' *)
    - simpl; simpl in length_ix_is_SSdim'. exfalso; apply (Nat.neq_0_succ _ length_ix_is_SSdim').
    (* length (tl (ix_list_O :: ix_list')) = S dim' *)
    - simpl; simpl in length_ix_is_SSdim'. apply (eq_add_S _ _ length_ix_is_SSdim').
  (* forall i : Fin (S dim'), get (tl (` ix)) (` i) < get (tl (` shape)) (` i) *)
  + destruct ix as [ix_list ix_list_properties]; destruct ix_list_properties as [length_ix_is_SSdim' ix_is_in_shape]; simpl.
    (**)
    intro i.
    destruct ix_list as [|ix_list_O ix_list'].
    destruct shape as [shape_list shape_list_has_length_SSdim'].
    destruct shape_list as [|shape_list_O shape_list']; simpl; simpl in ix_is_in_shape.
    (* get nil (` i) < get nil (` i) *)
    - simpl; simpl in length_ix_is_SSdim'. exfalso; apply (Nat.neq_0_succ _ length_ix_is_SSdim').
    (* get nil (` i) < get shape_list' (` i) *)
    - simpl in length_ix_is_SSdim'. exfalso; apply (Nat.neq_0_succ _ length_ix_is_SSdim').
    (* get (tl (ix_list_O :: ix_list')) (` i) < get (tl (` shape)) (` i) *)
    - destruct shape as [shape_list shape_list_has_length_SSdim'].
      destruct shape_list as [|shape_list_O shape_list']; simpl; simpl in ix_is_in_shape.
      (* get ix_list' (` i) < get nil (` i) *)
      * simpl in shape_list_has_length_SSdim'. exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_SSdim').
      (* get ix_list' (` i) < get shape_list' (` i) *)
      * destruct i as [i_val i_lt_Sdim']; simpl.
        Search (?x < ?y -> S ?x < S ?y).
        pose proof (ix_is_in_shape (exist _ (S i_val) (lt_n_S _ _ i_lt_Sdim'))) as proof;
        unfold get in proof; simpl in proof. unfold get; simpl. exact proof.
  Defined.

  Program Fixpoint from_lin {dim} (ix_lin: nat) (shape: Shape dim) (ix_lin_lt_pi_shape: ix_lin < pi shape)
      : Index shape :=
    match dim with | O => exist _ nil _
                   | S dim' => let shape_tail := exist _ (tl (` shape)) _ in
                               let ix_tail := from_lin (ix_lin mod pi (shape_tail)) shape_tail _ in
                               let ix_lin_head := ix_lin / (pi shape_tail) in
                               exist _ (ix_lin_head :: ix_tail) _ end.
  Next Obligation. split.
  (* 0 = 0 *)
  + reflexivity.
  (* forall i : Fin 0, get nil (` i) < get (` shape) (` i) *)
  + intro i; destruct i as [i_val i_lt_O]. exfalso; apply (Nat.nlt_0_r _ i_lt_O).
  Defined.
  Next Obligation. unfold from_lin_obligation_2; simpl.
  (* length (tl (` shape)) = dim' *)
  destruct shape as [shape_list shape_list_has_length_Sdim']; simpl.
  destruct shape_list as [|shape_list_O shape_list'].
  (* length (tl nil) = dim' *)
  + simpl in shape_list_has_length_Sdim'. exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim').
  (* length (tl (shape_list_O :: shape_list')) = dim' *)
  + simpl; simpl in shape_list_has_length_Sdim'. apply (eq_add_S _ _ shape_list_has_length_Sdim').
  Defined.
  Next Obligation. unfold from_lin_obligation_2; simpl.
  destruct shape as [shape_list shape_list_has_length_Sdim'];
  destruct shape_list as [|shape_list_O shape_list']; simpl.
  (* fst (Nat.divmod ix_lin 0 0 0) <
     pi
       (exist (fun s : list nat => length s = dim') nil
          (False_ind (0 = dim') (Nat.neq_0_succ dim' shape_list_has_length_Sdim'))) *)
  + simpl in shape_list_has_length_Sdim'. exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim').
  (*
    ix_lin /
    pi
      (exist (fun s : list nat => length s = dim') shape_list'
         (eq_add_S (length shape_list') dim' shape_list_has_length_Sdim')) <
    pi
      (exist (fun s : list nat => length s = dim') shape_list'
         (eq_add_S (length shape_list') dim' shape_list_has_length_Sdim'))
  *)
  + unfold pi; simpl. unfold pi in ix_lin_lt_pi_shape; simpl in ix_lin_lt_pi_shape.
    destruct (fold_right (fun x y : nat => x * y) 1 shape_list').
    (* ix_lin mod 0 < 0 *)
    - rewrite Nat.mul_0_r in ix_lin_lt_pi_shape. exfalso; apply (Nat.nlt_0_r _ ix_lin_lt_pi_shape).
    (* ix_lin mod S n < S n *)
    - apply (Nat.mod_upper_bound _ _). apply Nat.neq_succ_0.
  Defined.
  Next Obligation. unfold from_lin_obligation_2 in e; simpl in e. split.
  (* S (length x) = S dim' *)
  - apply (eq_S _ _ e).
  - intro i. unfold from_lin_obligation_2 in l; simpl in l.
    destruct shape as [shape_list shape_list_has_length_Sdim'].
    destruct shape_list as [|shape_list_O shape_list']. simpl.
    (* get (fst (Nat.divmod ix_lin 0 0 0) :: x) (` i) < get nil (` i) *)
    + simpl in shape_list_has_length_Sdim'. exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim').
    + destruct i as [i_val i_lt_Sdim']; destruct i_val as [|i_val]. unfold get; simpl.
      (* 
        ix_lin /
        pi
          (exist (fun s : list nat => length s = dim') shape_list'
             (eq_add_S (length shape_list') dim' shape_list_has_length_Sdim')) < shape_list_O
       *)
      * unfold pi; unfold pi in ix_lin_lt_pi_shape; simpl; simpl in ix_lin_lt_pi_shape.
        apply Nat.div_lt_upper_bound.
        (* fold_right (fun x0 y : nat => x0 * y) 1 shape_list' <> 0 *)
        ** unfold lt in ix_lin_lt_pi_shape. pose proof (Nat.lt_0_succ ix_lin) as O_lt_Six_lin.
           pose proof (Nat.le_trans _ _ _ O_lt_Six_lin ix_lin_lt_pi_shape) as O_lt_shape_list_O_times_pi_shape_list'.
           Search (?O < ?x * ?y).
           pose proof (Nat.lt_0_mul' shape_list_O (fold_right (fun x y : nat => x * y) 1 shape_list')) as equiv.
           destruct equiv as [O_lt_mul_a_b_imp_O_lt_a_and_O_lt_b junk].
           pose proof (O_lt_mul_a_b_imp_O_lt_a_and_O_lt_b O_lt_shape_list_O_times_pi_shape_list') as O_lt_factors.
           destruct O_lt_factors as [O_lt_shape_list_O O_lt_pi_shape_list'].
           apply (Nat.neq_sym _ _ (Nat.lt_neq _ _ O_lt_pi_shape_list')).
        (* ix_lin < fold_right (fun x0 y : nat => x0 * y) 1 shape_list' * shape_list_O *)
        ** rewrite Nat.mul_comm in ix_lin_lt_pi_shape. exact ix_lin_lt_pi_shape.
      (* nth i_val x 0 < nth i_val shape_list' 0 *)
      * unfold get; simpl.
        pose proof (l (exist _ i_val (lt_S_n _ _ i_lt_Sdim'))) as proof.
        apply proof.
  Defined.

  Lemma to_lin_ix_lt_pi_shape {dim}: forall (shape: Shape (S dim)) (ix: Index shape), to_lin ix < pi shape.
  Proof.
    induction dim as [|dim'].
    (* forall (shape : Shape 1) (ix : Index shape), to_lin ix < pi shape *)
    + intros. unfold to_lin. destruct ix as [ix_list ix_list_properties]; simpl.
      destruct ix_list_properties as [ix_list_has_length_dim ix_list_is_in_shape].
      destruct ix_list as [|ix_list_O ix_list'].
      (* hd 0 nil < pi shape *)
      * unfold length in ix_list_has_length_dim. exfalso; apply (Nat.neq_0_succ _ ix_list_has_length_dim).
      (* hd 0 (ix_list_O :: ix_list') < pi shape *)
      * destruct shape as [shape_list shape_has_length_dim].
        destruct shape_list as [|shape_list_O shape_list']. unfold hd; unfold pi. simpl.
        (* ix_list_O < 1 *)
        - unfold length in shape_has_length_dim. exfalso; apply (Nat.neq_0_succ _ shape_has_length_dim).
        (* ix_list_O < shape_list_O * fold_right (fun x y : nat => x * y) 1 shape_list' *)
        - simpl. unfold pi. simpl; simpl in ix_list_is_in_shape. destruct shape_list' as [|absurd_hd absurd_tl]; simpl.
          (* ix_list_O < shape_list_O * 1 *)
          -- rewrite Nat.mul_1_r. apply (ix_list_is_in_shape (exist _ O Nat.lt_0_1)).
          (* absurd *)
          -- simpl in shape_has_length_dim. apply eq_add_S in shape_has_length_dim. exfalso; apply (Nat.neq_succ_0 _ shape_has_length_dim).
    (* forall (shape : Shape (S (S dim'))) (ix : Index shape), to_lin ix < pi shape *)
    + intros shape ix.
      (**)
      pose (tail_shape shape) as subshape.
      destruct shape as [shape_list shape_list_has_length_dim].
      destruct shape_list as [|shape_list_O shape_list'].
      (* absurd *)
      * simpl in shape_list_has_length_dim. exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_dim).
      (* to_lin ix < fold_right (fun x y : nat => x * y) 1 (shape_list_O :: shape_list') *)
      * unfold tail_shape in subshape; simpl in subshape.
        destruct ix as [ix_list ix_list_properties]. simpl in ix_list_properties.
        destruct ix_list_properties as [ix_list_has_length_SSdim' ix_list_is_in_shape].
        destruct ix_list as [|ix_list_O ix_list'].
        (* absurd *)
        - exfalso; apply (Nat.neq_0_succ _ ix_list_has_length_SSdim').
        - unfold pi; simpl. unfold tail_shape. unfold pi; simpl.
          simpl in shape_list_has_length_dim.
          remember (fold_right (fun x y : nat => x * y) 1 shape_list') as pi_subshape.
          remember (exist (fun ix : list nat => length ix = S dim' /\ (forall i : Fin (S dim'), get ix (` i) < get shape_list' (` i)))
     ix_list'
     (conj (eq_add_S (length ix_list') (S dim') ix_list_has_length_SSdim')
        (fun i : Fin (S dim') =>
         let (i_val, i_lt_Sdim') as s return (get ix_list' (` s) < get shape_list' (` s)) := i in
         ix_list_is_in_shape (exist (fun i0 : nat => i0 < S (S dim')) (S i_val) (lt_n_S i_val (S dim') i_lt_Sdim')))) : Index subshape) as subix.
          pose proof (IHdim' subshape subix) as lin_subix_lt_pi_subshape.
          pose proof (plus_lt_compat_l _ _ (ix_list_O * pi_subshape) lin_subix_lt_pi_subshape) as H.
          pose proof (ix_list_is_in_shape (exist (fun i => i < S (S dim')) O (Nat.lt_0_succ (S dim')))) as ix_O_lt_shape_O.
          unfold get in ix_O_lt_shape_O; simpl in ix_O_lt_shape_O.
          apply ((fun z x y => Nat.mul_le_mono_r x y z) pi_subshape) in ix_O_lt_shape_O.
          rewrite Nat.mul_succ_l in ix_O_lt_shape_O.
          unfold pi in H; simpl in H.
          rewrite <- Heqpi_subshape in H.
          apply (Nat.le_trans _ _ _ H ix_O_lt_shape_O).
    Qed.

  (* === MoA operations === *)

  (* === array projections === *)

  Definition rho {dim} {shape: Shape dim}
    (array : Array E shape) : Shape dim := shape.
  Definition total_ix {dim} {shape: Shape dim}
                      (i: Index shape) (array: Array E shape) : E :=
    array i.

  (* === reshaping utils === *)

  Program Definition cast_ix {dim_in dim_out} {shape_in: Shape (S dim_in)}
      (ix: Index shape_in) (shape_out: Shape dim_out)
      (eq_pi_shapes: pi shape_in = pi shape_out): Index shape_out :=
    from_lin (to_lin ix) shape_out (to_lin_ix_lt_pi_shape shape_in ix).

  Definition reshape {dim_in dim_out} {shape_in: Shape (S dim_in)}
      (array: Array E shape_in) (shape_out: Shape (S dim_out))
      (eq_pi_shapes: pi shape_in = pi shape_out): Array E shape_out :=
    fun ix => array (cast_ix ix shape_in (eq_sym eq_pi_shapes)).

  Program Definition expand_dim_shape {dim} (shape: Shape dim)
      (axis: Fin (S dim)) : Shape (S dim) :=
    exist _ (firstn axis (` shape) ++ (1 :: skipn axis (` shape))) _.
  Next Obligation. (* length (firstn (` axis) (` shape) ++ 1 :: skipn (` axis) (` shape)) = S dim *)
    destruct shape as [shape_list shape_list_has_length_dim]; simpl.
    destruct axis as [axis_val axis_lt_Sdim]; simpl.
    rewrite app_length; simpl.
    pose proof (le_S_n _ _ axis_lt_Sdim) as axis_le_dim.
    rewrite <- shape_list_has_length_dim in axis_le_dim.
    rewrite (firstn_length_le _ axis_le_dim).
    rewrite skipn_length. rewrite (minus_Sn_m _ _ axis_le_dim).
    rewrite (le_plus_minus_r _ _  (le_S _ _ axis_le_dim)).
    rewrite shape_list_has_length_dim; reflexivity.
  Defined.

  (* === take / drop / cat === *)
  Program Definition take_shape {dim} (shape: Shape (S dim)) (n: Fin (hd 0 (` shape))): Shape (S dim) :=
    exist _ (n :: tl (` shape)) _.
  Next Obligation. (* S (length (tl (` shape))) = S dim *)
    destruct shape as [shape_list shape_list_has_length_Sdim].
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    * simpl; exact shape_list_has_length_Sdim.
  Defined.

  Program Definition take {dim} {shape: Shape (S dim)} (n: Fin (hd 0 (` shape))) (array: Array E shape)
      : Array E (take_shape shape n) :=
    fun ix => array ix.
  Next Obligation. split.
    (* length (` ix) = S dim *)
    + destruct ix as [ix_list ix_list_properties]; simpl. apply (proj1 ix_list_properties).
    (* forall i : Fin (S dim), get (` ix) (` i) < get (` shape) (` i) *)
    + destruct ix as [ix_list ix_list_properties]; simpl.
      unfold take_shape in ix_list_properties; simpl in ix_list_properties.
      destruct shape as [shape_list shape_list_has_length_Sdim]; simpl in ix_list_properties; simpl.
      intro axis.
      destruct axis as [axis_val axis_lt_Sdim]; simpl.
      destruct axis_val as [|axis_val'].
      (* get ix_list 0 < get shape_list 0 *)
      - destruct shape_list as [|shape_list_O shape_list']; simpl.
        (* absurd *)
        * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
        * pose proof (proj2 ix_list_properties (exist _ O axis_lt_Sdim)) as proof.
          simpl in proof; simpl in n.
          destruct n as [n n_lt_shape_list_O]; simpl in proof.
          unfold get in proof; unfold get; simpl; simpl in proof.
          apply (Nat.lt_trans _ _ _ proof n_lt_shape_list_O).
      (* get ix_list (S axis_val') < get shape_list (S axis_val') *)
      - destruct shape_list as [|shape_list_O shape_list']; simpl.
        (* absurd *)
        * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
        * pose proof (proj2 ix_list_properties (exist _ (S axis_val') axis_lt_Sdim)) as proof; simpl in proof.
          unfold get; unfold get in proof; simpl; simpl in proof. exact proof.
  Defined.

    (* TODO: here *)

  Program Fixpoint drop_vec {n : nat} (k : Fin (S n)) (v : Vect E n) {struct n} 
      : Vect E (n - (` k)) :=
    match k with
      | O => v
      | S k' =>
      match n, v in list _ with
        | O, _ => _ (* absurd *)
        | S n', e :: v' => exist _ (` (drop_vec (n:=n') (exist _ k' _) (exist _ v' _))) _
        | S _, _ => _ (* absurd *)
      end end.
  Next Obligation. (* absurd *)
    destruct v as [v length_v_is_n]. simpl.
    rewrite Nat.sub_0_r. apply length_v_is_n.
  Defined.
  Next Obligation. (* k' < S n' *)
    destruct k as [k k_lt_SSn']. simpl in Heq_k.
    rewrite <- Heq_k in k_lt_SSn'.
    apply (le_S_n _ _ k_lt_SSn').
  Defined.
  Next Obligation. (* length v' = n' *)
    destruct v as [v length_v_is_n]. simpl in Heq_v.
    rewrite <- Heq_v in length_v_is_n. simpl in length_v_is_n.
    apply (eq_add_S _ _ length_v_is_n).
  Defined.
  Next Obligation. (* absurd, H : forall (n' : nat) (e : E) (v' : list E), ~ (S n' = S wildcard' /\ e :: v' = ` v) *)
    destruct v as [v length_v_is_n].
    destruct v as [|e v'].
      (* v = vnil *)
      + simpl in length_v_is_n. exfalso. apply (Nat.neq_0_succ _ length_v_is_n).
      (* v = e :: v' *)
      + specialize (H wildcard' e v').
        simpl in H. unfold not in H.
        exfalso. apply (H (conj eq_refl eq_refl)).
  Defined.

  Program Definition drop_shape {dim : nat} (s : Shape dim) (k : Fin (hd 0 (` s)))
      : Shape dim :=
    exist _ (((hd 0 (` s)) - (` k)) :: tl (` s)) _.
  Next Obligation. (* S (length (tl (` s))) = dim *)
    destruct s as [s length_s_is_dim].
    simpl in k. simpl.
    destruct dim as [|dim'].
      (* dim = O *)
      - destruct s as [|s_O s'].
        (* s = nil *)
        * simpl in k. destruct k as [k k_lt_O].
          exfalso. apply (Nat.nlt_0_r _ k_lt_O).
        (* s = s_O :: s' *)
        * simpl in length_s_is_dim. discriminate.
      (* dim = S dim' *)
      - destruct s as [|s_O s'].
        (* s = nil *)
        * simpl in length_s_is_dim. discriminate.
        (* s = s_O :: s' *)
        * apply length_s_is_dim.
  Defined.

  Program Definition drop {dim : nat} {s : Shape (S dim)} (k : Fin (hd 0 (` s)))
        (a : Array E s) : Array E (drop_shape s k) :=
    exist _ (drop_vec (n:=pi s) (k * pi (dim:=dim) (tl (` s))) (` a)) _.
  Next Obligation.
    destruct s as [s length_s_is_Sdim].
    simpl in k. simpl.
    destruct s as [|s_O s'].
      (* s = nil *)
      - simpl in length_s_is_Sdim. discriminate.
      (* s = s_O :: s' *)
      - apply (eq_add_S _ _ length_s_is_Sdim).
  Defined.
  Next Obligation.
    destruct s as [s length_s_is_Sdim].
    generalize (take_obligation_1 dim (exist (fun s0 : list nat => length s0 = S dim) s length_s_is_Sdim) k a).
    simpl.
    destruct s as [|s_O s'].
      (* s = nil *)
      - simpl in length_s_is_Sdim. discriminate.
      (* s = s_O :: s' *)
      - simpl. intro e. simpl in k.
        destruct k as [k k_lt_s_O].
        simpl. unfold pi. unfold proj1_sig. unfold fold_right.
        apply le_n_S. apply Nat.mul_le_mono_r.
        apply (le_Sn_le _ _ k_lt_s_O).
  Defined.
  Next Obligation. (* length (` a) = pi s *)
    apply (proj2_sig a).
  Defined.
  Next Obligation. (* length (` v) = pi (drop_shape s k) *)
    generalize (drop_vec
      (exist (fun i : nat => i < S (pi s))
         (` k * pi (exist (fun s0 : list nat => length s0 = dim) (tl (` s)) (drop_obligation_1 dim s k a)))
         (drop_obligation_2 dim s k a)) (exist (fun v : list E => length v = pi s) (` a) (drop_obligation_3 dim s a))).
    simpl.
    intro v. destruct v as [v length_v_is_ktls].
    simpl. unfold take_shape. unfold pi.
    simpl.
    destruct s as [s length_s_is_sdim].
    destruct s as [|s_O s'].
      (* s = nil, absurd *)
      - destruct k as [k k_lt_O]. exfalso. apply (Nat.nlt_0_r _ k_lt_O).
      - simpl. unfold pi in length_v_is_ktls.
        simpl in length_v_is_ktls.
        rewrite Nat.mul_sub_distr_r.
        apply length_v_is_ktls.
  Defined.

  Program Definition take_neg {dim : nat} {s : Shape (S dim)} (k : Fin (hd 0 (` s)))
        (a : Array E s) : Array E (take_shape s k) :=
    exist _ (drop_vec (n:=pi s) (((hd 0 (` s)) - (` k)) * pi (dim:=dim) (tl (` s))) (` a)) _.
  Next Obligation. (* length (tl (` s)) = dim *)
    destruct s as [s length_s_is_sdim].
    simpl in k. simpl.
    destruct s as [|s_O s'].
    (* s = nil *)
    - simpl in k. destruct k as [k k_lt_O].
      exfalso. apply (Nat.nlt_0_r _ k_lt_O).
    (* s = s_O :: s' *)
    - apply (eq_add_S _ _ length_s_is_sdim).
  Defined.
  Next Obligation. simpl.
    destruct s as [s length_s_is_sdim].
    destruct s as [|s_O s'].
      (* s = nil *)
      - simpl in length_s_is_sdim. discriminate.
      (* s = s_O :: s' *)
      - simpl. unfold pi. simpl.
        apply Peano.le_n_S.
        apply Nat.mul_le_mono_r.
        apply Nat.le_sub_l.
  Defined.
  Admit Obligations. (* TODO: finish *)
*)
  (* TODO: finish core *)
End Array.
  (* TODO: expand *)
End Array.
