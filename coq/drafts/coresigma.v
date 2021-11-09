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
  Program Definition take_shape {dim} (shape: Shape (S dim)) (n: Fin (S (hd 0 (` shape)))): Shape (S dim) :=
    exist _ (n :: tl (` shape)) _.
  Next Obligation. (* S (length (tl (` shape))) = S dim *)
    destruct shape as [shape_list shape_list_has_length_Sdim].
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    * simpl; exact shape_list_has_length_Sdim.
  Defined.

  Program Definition take {dim} {shape: Shape (S dim)} (n: Fin (S (hd 0 (` shape)))) (array: Array E shape)
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
          destruct n as [n n_lt_Sshape_list_O]; simpl in proof.
          unfold get in proof; unfold get; simpl; simpl in proof.
          apply (Nat.lt_le_trans _ _ _ proof (le_S_n _ _ n_lt_Sshape_list_O)).
      (* get ix_list (S axis_val') < get shape_list (S axis_val') *)
      - destruct shape_list as [|shape_list_O shape_list']; simpl.
        (* absurd *)
        * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
        * pose proof (proj2 ix_list_properties (exist _ (S axis_val') axis_lt_Sdim)) as proof; simpl in proof.
          unfold get; unfold get in proof; simpl; simpl in proof. exact proof.
  Defined.

  Program Definition drop_shape {dim} (shape: Shape (S dim)) (n: Fin (S (hd 0 (` shape)))): Shape (S dim) :=
    exist _ ((hd 0 (` shape) - n) :: tl (` shape)) _.
  Next Obligation. (* S (length (tl (` shape))) = S dim *)
    destruct shape as [shape_list shape_list_has_length_Sdim].
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    * simpl; exact shape_list_has_length_Sdim.
  Defined.

  Program Definition drop {dim} {shape: Shape (S dim)} (n: Fin (S (hd 0 (` shape)))) (array: Array E shape)
      : Array E (drop_shape shape n) :=
    fun ix => let ix' := from_lin (to_lin ix + n * pi (tail_shape shape)) shape _ in
              array ix'.
  Next Obligation. (* to_lin ix + ` n * pi (tail_shape shape) < pi shape *)
    destruct shape as [shape_list shape_list_has_length_Sdim].
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    (*
      to_lin ix + ` n * fold_right (fun x y : nat => x * y) 1 shape_list' <
      shape_list_O * fold_right (fun x y : nat => x * y) 1 shape_list'
     *)
    * unfold pi; simpl. simpl in n. unfold drop_shape in ix; simpl in ix.
      destruct n as [n_val n_lt_Sshape_list_O].
      destruct n_val as [|n_val']; simpl.
      (* to_lin ix < shape_list_O * fold_right (fun x y : nat => x * y) 1 shape_list' *)
      - simpl in ix. rewrite Nat.add_0_r.
        pose proof (to_lin_ix_lt_pi_shape (exist _ ((shape_list_O - O) :: shape_list') shape_list_has_length_Sdim) ix) as proof.
        assert (pi (exist (fun s : list nat => length s = S dim) (shape_list_O - 0 :: shape_list') shape_list_has_length_Sdim) =
                pi (exist (fun s : list nat => length s = S dim) (shape_list_O :: shape_list') shape_list_has_length_Sdim)) as pi_rewrite.
        + rewrite Nat.sub_0_r; reflexivity.
        + rewrite pi_rewrite in proof; unfold pi in proof; simpl in proof. exact proof.
      - simpl in ix.
        pose proof (to_lin_ix_lt_pi_shape (exist _ ((shape_list_O - S n_val') :: shape_list') shape_list_has_length_Sdim) ix) as proof. 
        destruct ix as [ix_list ix_list_properties]; simpl.
        destruct ix_list_properties as [ix_list_has_length_Sdim ix_list_is_in_shape].
        destruct ix_list as [|ix_list_O ix_list'].
        (* absurd *)
        + exfalso; apply (Nat.neq_0_succ _ ix_list_has_length_Sdim).
        + simpl in proof.
          assert (fold_right (fun x y : nat => x * y) 1 shape_list' + n_val' * fold_right (fun x y : nat => x * y) 1 shape_list' +
                  pi (exist (fun s : list nat => length s = S dim) (shape_list_O - S n_val' :: shape_list')
                        shape_list_has_length_Sdim) =
                  shape_list_O * fold_right (fun x y : nat => x * y) 1 shape_list') as pi_eq.
          -- unfold pi; simpl. remember (fold_right (fun x y : nat => x * y) 1 shape_list') as pi_shape_list'.
             pattern pi_shape_list' at 1.
             rewrite <- (Nat.mul_1_l pi_shape_list').
             rewrite <- Nat.mul_add_distr_r; rewrite <- Nat.mul_add_distr_r.
             rewrite Nat.add_1_l. rewrite le_plus_minus_r. reflexivity.
             (* S n_val' <= shape_list_O *)
             ++ apply (le_S_n _ _ n_lt_Sshape_list_O).
          -- rewrite <- pi_eq; simpl. rewrite Nat.add_comm. apply plus_lt_compat_l.
             exact proof.
  Defined.

  Program Definition take_neg {dim} {shape: Shape (S dim)} (n: Fin (S (hd 0 (` shape)))) (array: Array E shape)
      : Array E (take_shape shape n) :=
    drop (exist _ (hd 0 (` shape) - n) _) array.
  Next Obligation. (* hd 0 (` shape) - ` n < S (hd 0 (` shape)) *)
    lia.
  Defined.
  Next Obligation. split.
    (* length (` x) = S dim *)
    + destruct x as [ix_list ix_list_properties]; apply (proj1 ix_list_properties).
    (* forall i : Fin (S dim), get (` x) (` i) < get (hd 0 (` shape) - (hd 0 (` shape) - ` n) :: tl (` shape)) (` i) *)
    + destruct x as [ix_list ix_list_properties]; simpl.
      destruct ix_list_properties as [ix_list_has_length_Sdim ix_list_is_in_shape].
      unfold take_shape in ix_list_is_in_shape; simpl in ix_list_is_in_shape.
      intro i.
      destruct i as [i_val i_lt_Sdim].
      destruct i_val as [|i_val'].
      (* get ix_list 0 < get (hd 0 (` shape) - (hd 0 (` shape) - ` n) :: tl (` shape)) 0 *)
      - unfold get; simpl.
        unfold get in ix_list_is_in_shape.
        pose proof (ix_list_is_in_shape (exist _ 0 i_lt_Sdim)) as ix_list_O_lt_n; simpl in ix_list_O_lt_n.
        Search (?y + ?z <= ?x + ?z).
        apply ((fun m n p rel => proj2 (Nat.add_le_mono_r m n p) rel) _ _ (hd 0 (` shape) - ` n)); simpl.
        destruct n as [n_val n_lt_Sshape_list_O]; simpl.
        rewrite (Nat.sub_add _ _ (Nat.le_sub_l _ _)).
        rewrite (Nat.add_sub_assoc _ _ _ (le_S_n _ _ n_lt_Sshape_list_O)); simpl.
        Search (?x <= ?y -> ?x <= ?z + ?y).
        rewrite minus_Sn_m.
        (* S (nth 0 ix_list 0 + hd 0 (` shape)) - n_val <= hd 0 (` shape) *)
        * rewrite <- Nat.add_succ_l. simpl in ix_list_O_lt_n.
          pose proof (proj2 (Nat.sub_0_le (S (nth 0 ix_list 0)) n_val) (ix_list_is_in_shape (exist _ 0 i_lt_Sdim))) as proof_eq_helper.
          pose proof (Nat.le_refl 0) as proof.
          pattern 0 at 1 in proof.
          rewrite <- proof_eq_helper in proof.
          apply (fun n m pf => plus_le_compat_r n m (hd 0 (` shape)) pf) in proof.
          assert (S (nth 0 ix_list 0) + hd 0 (` shape) - n_val <= S (nth 0 ix_list 0) - n_val + hd 0 (` shape)) as proof_ord.
          -- lia.
          -- apply (Nat.le_trans _ _ _ proof_ord proof).
        (* n_val <= nth 0 ix_list 0 + hd 0 (` shape) *)
        * lia.
     (* nth (S i_val') ix_list 0 < nth i_val' (tl (` shape)) 0 *)
     - apply (ix_list_is_in_shape (exist _ (S i_val') i_lt_Sdim)).
  Defined.
  (* TODO: drop_neg *)

  (* TODO: finish core *)
End Array.
  (* TODO: expand *)
End Array.
