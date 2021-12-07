From Coq Require Import Arith List Omega Program.
From Coq.Logic Require Import FunctionalExtensionality.
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
    fun ix => let ix' := exist _ (hd O (` ix) + n :: tail_ix ix) _ in
              array ix'.
    Next Obligation. split.
      (* S (length (tl (` ix))) = S dim *)
      * destruct ix as [ix_list ix_list_properties].
        destruct ix_list as [|ix_list_O ix_list'].
        (* absurd *)
        - exfalso; apply (Nat.neq_0_succ _ (proj1 ix_list_properties)).
        (* S (length ix_list') = S dim *)
        - simpl. exact (proj1 ix_list_properties).
      (* forall i : Fin (S dim), get (hd 0 (` ix) + ` n :: tl (` ix)) (` i) < get (` shape) (` i) *)
      * intro i. destruct i as [i_val i_val_lt_Sdim].
        simpl.
        destruct ix as [ix_list ix_list_properties]; simpl; simpl in ix_list_properties.
        destruct n as [n_val n_val_lt_Sshape_list_O]; simpl.
        destruct shape as [shape_list shape_list_has_length_Sdim]; simpl.
        destruct ix_list as [|ix_list_O ix_list'].
        (* absurd *)
        - exfalso; apply (Nat.neq_0_succ _ (proj1 ix_list_properties)).
        (* get (ix_list_O + n_val :: ix_list') i_val < get shape_list i_val *)
        - simpl. destruct shape_list as [|shape_list_O shape_list'].
          (* absurd *)
          + exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
          (* get (ix_list_O + n_val :: ix_list') i_val < get (shape_list_O :: shape_list') i_val *)
          + simpl in ix_list_properties. destruct i_val as [|i_val'].
            (* i_val = 0 *)
            ** unfold get; simpl.
               pose proof (proj2 ix_list_properties (exist _ 0 i_val_lt_Sdim)) as proof.
               unfold get in proof; simpl in proof.
               Search (?x <= ?y -> ?x + ?z <= ?y + ?z).
               apply (plus_le_compat_r _ _ n_val) in proof.
               simpl in n_val_lt_Sshape_list_O.
               rewrite (Nat.sub_add _ _ (le_S_n _ _ n_val_lt_Sshape_list_O)) in proof.
               exact proof.
            (* i_val = S i_val' *)
            ** apply (proj2 ix_list_properties (exist _ (S i_val') i_val_lt_Sdim)).
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

  Program Definition drop_neg {dim} {shape: Shape (S dim)} (n: Fin (S (hd 0 (` shape)))) (array: Array E shape)
      : Array E (drop_shape shape n) :=
    take (exist _ (hd 0 (` shape) - n) _) array.
  Next Obligation. (* hd 0 (` shape) - ` n < S (hd 0 (` shape)) *)
    lia.
  Defined.

  Definition A : E. Admitted.
  Definition B : E. Admitted.
  Definition C : E. Admitted.
  Definition D : E. Admitted.

  Definition shape_list_4 := 4 :: nil.
  Theorem shape_list_4_has_length_1 : length shape_list_4 = 1. Proof. auto. Qed. 
  Definition Shape4 : Shape 1 := exist _ (4 :: nil) shape_list_4_has_length_1.

  Program Definition test_array : Array (dim:=1) E Shape4 :=
    fun ix => match (` ix) with | 0 :: nil => A
                                | 1 :: nil => B
                                | 2 :: nil => C
                                | 3 :: nil => D
                                | _ => (* absurd *) _ end.
  Next Obligation. (* absurd *)
    destruct ix as [ix_list ix_list_properties]; simpl in H; simpl in H0; simpl in H1; simpl in H2.
    destruct ix_list_properties as [ix_list_has_length_1 ix_list_is_in_shape].
    pose proof (ix_list_is_in_shape (exist _ 0 Nat.lt_0_1)) as ix_ord.
    destruct ix_list as [|ix_list_O ix_list'].
    + exfalso; apply (Nat.neq_0_succ _ ix_list_has_length_1).
    + destruct ix_list' as [|ix_list_1 ix_list''].
      - unfold get in ix_ord; simpl in ix_ord.
        assert (4 <= ix_list_O) as inconsistent_proof.
        * destruct ix_list_O as [|ix_list_O].
          -- exfalso; apply H2; reflexivity.
          -- destruct ix_list_O as [|ix_list_O].
             ++ exfalso; apply H; reflexivity.
             ++ destruct ix_list_O as [|ix_list_O].
                ** exfalso; apply H0; reflexivity.
                ** destruct ix_list_O as [|ix_list_O].
                   --- exfalso; apply H1; reflexivity.
                   --- repeat (apply le_S_n in ix_ord). exfalso; apply (Nat.nle_succ_0 _ ix_ord).
        * exfalso; apply (Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ ix_ord inconsistent_proof)).
      - simpl in ix_list_has_length_1. apply eq_add_S in ix_list_has_length_1.
        exfalso; apply (Nat.neq_succ_0 _ ix_list_has_length_1).
  Defined.
  Next Obligation. (* 1 :: nil <> nil /\ 2 :: nil <> nil /\ 3 :: nil <> nil /\ 0 :: nil <> nil *)
    split.
    + unfold not; intro disc_H; discriminate disc_H.
    + split. - unfold not; intro disc_H; discriminate disc_H.
             - split. * unfold not; intro disc_H; discriminate disc_H.
                      * unfold not; intro disc_H; discriminate disc_H.
  Defined.
  Next Obligation. (* 1 :: nil <> 0 :: H1 :: H2 /\ 2 :: nil <> 0 :: H1 :: H2 /\ 3 :: nil <> 0 :: H1 :: H2 /\ 0 :: nil <> 0 :: H1 :: H2 *)
    split.
    + unfold not; intro disc_H; discriminate disc_H.
    + split. - unfold not; intro disc_H; discriminate disc_H.
             - split. * unfold not; intro disc_H; discriminate disc_H.
                      * unfold not; intro disc_H; discriminate disc_H.
  Defined.
  Next Obligation. (* 1 :: nil <> 1 :: H2 :: H3 /\ 2 :: nil <> 1 :: H2 :: H3 /\ 3 :: nil <> 1 :: H2 :: H3 /\ 0 :: nil <> 1 :: H2 :: H3 *)
    split.
    + unfold not; intro disc_H; discriminate disc_H.
    + split. - unfold not; intro disc_H; discriminate disc_H.
             - split. * unfold not; intro disc_H; discriminate disc_H.
                      * unfold not; intro disc_H; discriminate disc_H.
  Defined.
  Next Obligation. (* 1 :: nil <> 2 :: H3 :: H4 /\ 2 :: nil <> 2 :: H3 :: H4 /\ 3 :: nil <> 2 :: H3 :: H4 /\ 0 :: nil <> 2 :: H3 :: H4 *)
    split.
    + unfold not; intro disc_H; discriminate disc_H.
    + split. - unfold not; intro disc_H; discriminate disc_H.
             - split. * unfold not; intro disc_H; discriminate disc_H.
                      * unfold not; intro disc_H; discriminate disc_H.
  Defined.
  Next Obligation. (* 1 :: nil <> 3 :: H4 :: H5 /\ 2 :: nil <> 3 :: H4 :: H5 /\ 3 :: nil <> 3 :: H4 :: H5 /\ 0 :: nil <> 3 :: H4 :: H5 *)
    split.
    + unfold not; intro disc_H; discriminate disc_H.
    + split. - unfold not; intro disc_H; discriminate disc_H.
             - split. * unfold not; intro disc_H; discriminate disc_H.
                      * unfold not; intro disc_H; discriminate disc_H.
  Defined.
  Next Obligation. (* 1 :: nil <> S (S (S (S H4))) :: H0 /\
                      2 :: nil <> S (S (S (S H4))) :: H0 /\ 3 :: nil <> S (S (S (S H4))) :: H0 /\ 0 :: nil <> S (S (S (S H4))) :: H0 *)
    split.
    + unfold not; intro disc_H; discriminate disc_H.
    + split. - unfold not; intro disc_H; discriminate disc_H.
             - split. * unfold not; intro disc_H; discriminate disc_H.
                      * unfold not; intro disc_H; discriminate disc_H.
  Defined.

  Program Definition ix_1_Shape4 : Index Shape4 := exist _ (1 :: nil) _.
  Next Obligation. split. reflexivity.
    intro i; destruct i as [i_val i_lt_1]; simpl.
    destruct i_val as [|i_val].
    + unfold get; simpl. apply lt_n_S. apply Nat.lt_0_succ.
    + exfalso; apply lt_S_n in i_lt_1; apply (Nat.nlt_0_r _ i_lt_1).
  Defined.

  Compute test_array ix_1_Shape4.

  Definition shape_list_2_2 := 2 :: 2 :: nil.
  Lemma shape_list_2_2_has_length_2 : length shape_list_2_2 = 2. Proof. auto. Qed. 
  Definition Shape2_2 : Shape 2 := exist _ shape_list_2_2 shape_list_2_2_has_length_2.
  Lemma pi_shape4_eq_pi_shape2_2 : pi Shape4 = pi Shape2_2. Proof. auto. Qed.

  Program Definition ix_0_1_Shape2_2 : Index Shape2_2 := exist _ (0 :: 1 :: nil) _.
  Next Obligation. split. reflexivity.
    intro i; destruct i as [i_val i_lt_2]; simpl.
    destruct i_val as [|i_val].
    + unfold get; simpl. exact i_lt_2.
    + destruct i_val as [|i_val].
      - unfold get; simpl. apply lt_n_S. apply Nat.lt_0_succ.
      - exfalso; repeat (apply lt_S_n in i_lt_2); apply (Nat.nlt_0_r _ i_lt_2).
  Defined.

  Compute (reshape test_array Shape2_2 pi_shape4_eq_pi_shape2_2) ix_0_1_Shape2_2.

  Definition psi {dim} {shape: Shape dim} := total_ix (dim:=dim) (shape:=shape).

  Program Definition cat_shape {dim} (shape1: Shape (S dim)) (shape2: Shape (S dim))
        (eq_tl_shapes: tail_shape shape1 = tail_shape shape2) : Shape (S dim) :=
    exist _ (hd O (` shape1) + hd O (` shape2) :: tl (` shape1)) _.
  Next Obligation. (* S (length (tl (` shape1))) = S dim *)
    destruct shape1 as [shape1_list shape1_list_has_length_Sdim]; simpl.
    destruct shape1_list as [|shape1_list_O shape_1_list'].
    (* absurd *)
    - exfalso; apply (Nat.neq_0_succ _ shape1_list_has_length_Sdim).
    (* S (length shape_1_list') = S dim *)
    - apply shape1_list_has_length_Sdim.
  Defined.

  Program Definition cat {dim} {shape1 shape2: Shape (S dim)} (array1: Array E shape1)
        (array2: Array E shape2) (eq_tl_shapes: tail_shape shape1 = tail_shape shape2)
      : Array E (cat_shape shape1 shape2 eq_tl_shapes) :=
    fun ix => let shape1_first_axis := hd O (` shape1) in
              let ix_first_axis := hd O (` ix) in
              match ix_first_axis <? shape1_first_axis with
                | true => array1 (exist _ (` ix) _)
                | false => array2 (exist _ (ix_first_axis - shape1_first_axis :: (tl (` ix))) _) end.
  Next Obligation. split.
    (* length (` ix) = S dim *)
    + destruct ix as [ix_list ix_list_properties]; simpl.
      apply (proj1 ix_list_properties).
    (* forall i : Fin (S dim), get (` ix) (` i) < get (` shape1) (` i) *)
    + intro i. destruct i as [i_val i_val_lt_Sdim].
      pose proof (proj1 (Nat.ltb_lt _ _) (eq_sym Heq_anonymous)) as hd_ix_lt_hd_shape1.
      destruct i_val as [|i_val]; simpl.
      (* get (` ix) 0 < get (` shape1) 0 *)
      - unfold cat_shape in ix; simpl in ix; simpl in Heq_anonymous.
        destruct ix as [ix_list ix_list_properties]; destruct shape1 as [shape_list shape_list_has_length_Sdim].
        simpl in ix_list_properties; simpl; simpl in hd_ix_lt_hd_shape1; simpl in Heq_anonymous.
        destruct ix_list as [|ix_list_0 ix_list'].
        (* absurd *)
        * exfalso; apply (Nat.neq_0_succ _ (proj1 ix_list_properties)).
        (* get (ix_list_0 :: ix_list') 0 < get shape_list 0 *)
        * destruct shape_list as [|shape_list_0 shape_list'].
          (* absurd *)
          ++ exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
          (* get (ix_list_0 :: ix_list') 0 < get (shape_list_0 :: shape_list') 0 *)
          ++ simpl in hd_ix_lt_hd_shape1. unfold get; unfold nth; simpl. exact hd_ix_lt_hd_shape1.
      (* get (` ix) (S i_val) < get (` shape1) (S i_val) *)
      - destruct ix as [ix_list ix_list_properties].
        simpl in ix_list_properties; simpl; simpl in hd_ix_lt_hd_shape1; simpl in Heq_anonymous.
        pose proof (proj2 ix_list_properties (exist _ (S i_val) i_val_lt_Sdim)) as proof.
        unfold get; unfold get in proof; simpl; simpl in proof.
        destruct shape1 as [shape_list shape_list_has_length_Sdim];
        destruct shape_list as [|shape_list_O shape_list'].
        simpl in ix_list_properties; simpl; simpl in hd_ix_lt_hd_shape1; simpl in Heq_anonymous.
        (* absurd *)
        * exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
        (* nth (S i_val) ix_list 0 < nth i_val shape_list' 0 *)
        * simpl; simpl in proof. exact proof.
  Defined.
  Next Obligation. split.
    (* S (length (tl ix_list)) = S dim *)
    + destruct ix as [ix_list ix_list_properties]; destruct ix_list as [|ix_list_O ix_list']; simpl.
      (* absurd *)
      - exfalso; apply (Nat.neq_0_succ _ (proj1 ix_list_properties)).
      (* S (length ix_list') = S dim *)
      - exact (proj1 ix_list_properties).
    (* forall i : Fin (S dim), get (hd 0 (` ix) - hd 0 (` shape1) :: tl (` ix)) (` i) < get (` shape2) (` i) *)
    + intro i; destruct i as [i_val i_val_lt_Sdim]; destruct i_val as [|i_val]; simpl.
      (* get (hd 0 (` ix) - hd 0 (` shape1) :: tl (` ix)) 0 < get (` shape2) 0 *)
      - unfold get; simpl.
        destruct ix as [ix_list ix_list_properties]; simpl.
        pose proof (proj2 ix_list_properties (exist _ 0 i_val_lt_Sdim)) as proof; unfold get in proof; simpl in proof.
        destruct ix_list as [|ix_list_O ix_list'].
        (* absurd *)
        * exfalso; apply (Nat.neq_0_succ _ (proj1 ix_list_properties)).
        (* ix_list_O - hd 0 (` shape1) < nth 0 (` shape2) 0 *)
        * simpl; simpl in proof. destruct shape2 as [shape_list2 shape_list2_has_length_Sdim].
          destruct shape_list2 as [|shape_list2_O shape_list2']; simpl; simpl in proof.
          (* absurd *)
          ++ exfalso; apply (Nat.neq_0_succ _ shape_list2_has_length_Sdim).
          (* ix_list_O - hd 0 (` shape1) < shape_list2_O *)
          ++ simpl; simpl in Heq_anonymous; simpl in ix_list_properties.
             apply (proj2 (Nat.add_le_mono_r (S (ix_list_O - hd 0 (` shape1))) shape_list2_O (hd 0 (` shape1)))); simpl.
             rewrite Nat.sub_add.
             (* S ix_list_O <= shape_list2_O + hd 0 (` shape1) *)
             -- rewrite Nat.add_comm.
                exact proof.
             (* hd 0 (` shape1) <= ix_list_O *)
             -- apply (not_lt _ _ (proj1 (Nat.ltb_nlt _ _) (eq_sym Heq_anonymous))).
      (* get (hd 0 (` ix) - hd 0 (` shape1) :: tl (` ix)) (S i_val) < get (` shape2) (S i_val) *)
      - unfold get; simpl.
        destruct ix as [ix_list ix_list_properties]; simpl.
        simpl in Heq_anonymous.
        unfold cat_shape in ix_list_properties; simpl in ix_list_properties.
        pose proof (proj2 ix_list_properties (exist _ (S i_val) i_val_lt_Sdim)) as proof.
        unfold get in proof; simpl in proof.
        destruct shape2 as [shape_list2 shape_list2_has_length_Sdim].
        destruct shape_list2 as [|shape_list2_O shape_list2'].
        (* absurd *)
        * exfalso; apply (Nat.neq_0_succ _ shape_list2_has_length_Sdim).
        (* nth i_val (tl ix_list) 0 < nth i_val shape_list2' 0 *)
        * simpl. injection eq_tl_shapes as tl_shape1_eq_shape_list2'.
          destruct ix_list as [|ix_list_O ix_list'].
          (* absurd *)
          ++ exfalso; apply (Nat.neq_0_succ _ (proj1 ix_list_properties)).
          (* nth i_val (tl (ix_list_O :: ix_list')) 0 < nth i_val shape_list2' 0 *)
          ++ rewrite tl_shape1_eq_shape_list2' in proof. exact proof.
  Defined.

  (* Properties about cat *)
  (* 1. cat (take n A) (drop n A) = A *)
  Lemma tail_shape_take_is_tail_shape {dim} : forall (shape: Shape (S dim)) (n: Fin (S (hd 0 (` shape)))),
    tail_shape (take_shape shape n) = tail_shape shape.
  Proof.
    intros shape n.
    unfold tail_shape.
    f_equal.
    destruct shape as [shape_list shape_list_has_length_Sdim].
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    - exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    (*
      eq_add_S (length shape_list') dim shape_list_has_length_Sdim =
      eq_add_S (length shape_list') dim shape_list_has_length_Sdim
     *)
    - simpl. reflexivity.
  Qed.

  Lemma tail_shape_drop_is_tail_shape {dim} : forall (shape: Shape (S dim)) (n: Fin (S (hd 0 (` shape)))),
    tail_shape (drop_shape shape n) = tail_shape shape.
  Proof.
    intros shape n.
    unfold tail_shape.
    f_equal.
    destruct shape as [shape_list shape_list_has_length_Sdim].
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    - exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    (*
      eq_add_S (length shape_list') dim shape_list_has_length_Sdim =
      eq_add_S (length shape_list') dim shape_list_has_length_Sdim
     *)
    - simpl. reflexivity.
  Qed.

  Print eq_trans.
  Theorem cat_take_drop_shape {dim} : forall (shape: Shape (S dim)) (n: Fin (S (hd 0 (` shape)))),
    cat_shape (take_shape shape n) (drop_shape shape n)
      (eq_trans (tail_shape_take_is_tail_shape shape n) (eq_sym (tail_shape_drop_is_tail_shape shape n)))
    = shape.
  Proof.
    intros shape n.
    destruct shape as [shape_list shape_list_has_length_Sdim].
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    - exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    - unfold take_shape; unfold drop_shape; unfold cat_shape. simpl.
      rewrite (UIP_refl _ _ _); simpl.
      simpl in n. destruct n as [n_val n_lt_Sshape_list_O]; simpl.
      assert (n_val + (shape_list_O - n_val) = shape_list_O) as n_plus_shape_list_O_minus_n_is_shape_list_O.
      (* n_val + (shape_list_O - n_val) *)
      + apply le_plus_minus_r.
        apply (le_S_n _ _ n_lt_Sshape_list_O).
      + rewrite n_plus_shape_list_O_minus_n_is_shape_list_O. reflexivity.
  Qed.

  (* From http://adam.chlipala.net/cpdt/html/Match.html *)
  Ltac find_if_inside :=
    match goal with
      | [ |- context[if ?X then _ else _] ] => destruct X
    end.


  Theorem cat_take_drop {dim} {shape: Shape (S dim)} :
    forall (array: Array E shape) (n: Fin (S (hd 0 (` shape)))),
      transport
        (cat (take n array) (drop n array) (eq_trans (tail_shape_take_is_tail_shape shape n)
             (eq_sym (tail_shape_drop_is_tail_shape shape n))))
        (cat_take_drop_shape shape n)
      = array.
  Proof.
    intros array n.
    remember (take n array) as t_array.
    remember (drop n array) as d_array.
    destruct shape as [shape_list shape_list_has_length_Sdim].
    simpl in n.
    destruct shape_list as [|shape_list_O shape_list'].
    (* absurd *)
    - exfalso; apply (Nat.neq_0_succ _ shape_list_has_length_Sdim).
    (* *)
    - simpl in n; destruct n as [n_val n_val_lt_Sshape_list_O].
        unfold transport.
        generalize dependent (cat_take_drop_shape
          (exist (fun s : list nat => length s = S dim) (shape_list_O :: shape_list') shape_list_has_length_Sdim)
          (exist (fun i : nat => i < S shape_list_O) n_val n_val_lt_Sshape_list_O)).
        unfold cat_shape; simpl. unfold take_shape; unfold drop_shape; simpl.
        assert (n_val + (shape_list_O - n_val) = shape_list_O) as rew_proof.
        (* n_val + (shape_list_O - n_val) *)
        * apply le_plus_minus_r.
          apply (le_S_n _ _ n_val_lt_Sshape_list_O).
        * rewrite (UIP_refl _ _ _); simpl.
          generalize dependent t_array.
          unfold take_shape; simpl. intros t_array t_array_value.
          generalize dependent d_array.
          unfold drop_shape; simpl. intros d_array d_array_value.
          remember (cat t_array d_array eq_refl) as cat_array.
          unfold cat_shape in cat_array; simpl in cat_array.
          generalize dependent cat_array.
          unfold cat; simpl.
          unfold cat_shape; simpl.
          unfold eq_ind_r; unfold eq_sym; unfold eq_ind; simpl.
          generalize dependent (cat_obligation_1 dim
           (exist (fun s : list nat => length s = S dim) (n_val :: shape_list') shape_list_has_length_Sdim)
           (exist (fun s : list nat => length s = S dim) (shape_list_O - n_val :: shape_list')
              shape_list_has_length_Sdim) t_array eq_refl).
          generalize dependent (cat_obligation_2 dim
           (exist (fun s : list nat => length s = S dim) (n_val :: shape_list') shape_list_has_length_Sdim)
           (exist (fun s : list nat => length s = S dim) (shape_list_O - n_val :: shape_list')
              shape_list_has_length_Sdim) d_array eq_refl).
          unfold cat_shape; simpl.
          rewrite rew_proof; simpl.
          intros oblig2 oblig1 cat_array Heq_cat_array e_refl.
          rewrite (UIP_refl _ _ _).
          assert (forall ix, cat_array ix = array ix) as pointwise_proof.
          (* *)
          -- intro ix.
             rewrite Heq_cat_array; simpl.
             clear e_refl; clear rew_proof.
             generalize (oblig1 ix); generalize (oblig2 ix).
             generalize (@eq_refl bool
              (Nat.ltb
                 (@hd nat O
                    (@proj1_sig (list nat)
                       (fun ix0 : list nat =>
                        and (@eq nat (@length nat ix0) (S dim))
                          (forall i : Fin (S dim),
                           lt (get ix0 (@proj1_sig nat (fun i0 : nat => lt i0 (S dim)) i))
                             (get (@cons nat shape_list_O shape_list') (@proj1_sig nat (fun i0 : nat => lt i0 (S dim)) i))))
                       ix)) n_val)).
             case_eq (Nat.ltb
               (@hd nat O
                  (@proj1_sig (list nat)
                     (fun ix0 : list nat =>
                      and (@eq nat (@length nat ix0) (S dim))
                        (forall i : Fin (S dim),
                         lt (get ix0 (@proj1_sig nat (fun i0 : nat => lt i0 (S dim)) i))
                           (get (@cons nat shape_list_O shape_list') (@proj1_sig nat (fun i0 : nat => lt i0 (S dim)) i)))) ix))
               n_val).
             (* (hd 0 (` ix) <? n_val) = true *)
             ++ intros hd_ix_O_lt_n_val_bool eq_refl' junk take_ix_proof_fn.
                rewrite t_array_value; unfold take; simpl.
                f_equal.
                destruct ix as [ix_list ix_list_properties]; simpl.
                rewrite (proof_irrelevance _ _ ix_list_properties).
                reflexivity.
             (* (hd 0 (` ix) <? n_val) = true *)
             ++ intros hd_ix_O_lt_n_val_bool eq_refl' drop_ix_proof_fn junk.
                rewrite d_array_value.
                destruct ix as [ix_list ix_list_properties]. simpl.
                clear junk cat_array Heq_cat_array oblig1 oblig2.
                simpl in drop_ix_proof_fn; simpl in hd_ix_O_lt_n_val_bool.
                unfold drop; simpl.
                pose proof (proj1 (Nat.ltb_ge _ _) hd_ix_O_lt_n_val_bool) as n_val_lt_hd_ix_O.
                generalize (drop_obligation_1 dim
                  (exist (fun s : list nat => length s = S dim) (shape_list_O :: shape_list') shape_list_has_length_Sdim)
                  (exist (fun i : nat => i < S shape_list_O) n_val n_val_lt_Sshape_list_O) array
                  (exist
                     (fun ix : list nat =>
                      length ix = S dim /\
                      (forall i : Fin (S dim), get ix (` i) < get (shape_list_O - n_val :: shape_list') (` i)))
                     (hd 0 ix_list - n_val :: tl ix_list) (drop_ix_proof_fn eq_refl'))); simpl.
                rewrite (Nat.sub_add _ _ n_val_lt_hd_ix_O).
                destruct ix_list as [|ix_list_O ix_list'].
                (* absurd *)
                ** contradiction (Nat.neq_0_succ _ (proj1 ix_list_properties)).
                ** intro junk_proof; rewrite (proof_irrelevance _ _ ix_list_properties).
                   reflexivity.
          -- apply (functional_extensionality _ _ pointwise_proof).
  Defined.

  Program Fixpoint replace_nth {A: Type} (n: nat) (l: list A) (new: A): list A :=
    match n, l with
      | O, nil => nil
      | O, l_O :: l' => new :: l'
      | S n', l_O :: l' => l_O :: replace_nth n' l' new
      | S n', nil => nil
    end.

  Lemma replace_nth_length_invariant {A: Type} : forall (n: nat) (l: list A) (new: A),
    length (replace_nth n l new) = length l.
  Proof.
    intros n.
    induction n as [|n'].
    (* length (replace_nth 0 l new) = length l *)
    + intros l new. destruct l as [|l_O l'].
      (* length (replace_nth 0 nil new) = length nil *)
      - unfold replace_nth. reflexivity.
      (* length (replace_nth 0 (l_O :: l') new) = length (l_O :: l') *)
      - unfold replace_nth. reflexivity.
    (* length (replace_nth (S n') l new) = length l *)
    + intros l new. destruct l as [|l_O l'].
      (* length (replace_nth (S n') nil new) = length nil *)
      - unfold replace_nth. reflexivity.
      (* length (replace_nth (S n') (l_O :: l') new) = length (l_O :: l') *)
      - simpl. rewrite (IHn' l' new); reflexivity.
  Qed.

  Lemma replace_nth_only_modifies_nth_component : forall (n: nat) (l: list nat) (new: nat) (k: nat),
    ~ k = n -> get (replace_nth n l new) k = get l k.
  Proof.
    intros n l new k neq_k_n.
    generalize dependent n. generalize dependent l.
    induction k as [|k' IHk].
    (* get (replace_nth n l new) 0 = get l 0 *)
    * intros l n neq_k_n. destruct l as [|l_O l'].
      (* get (replace_nth n nil new) 0 = get nil 0 *)
      + destruct n as [|n'].
        - simpl; reflexivity.
        - simpl; reflexivity.
      (* get (replace_nth n (l_O :: l') new) 0 = get (l_O :: l') 0 *)
      + destruct n as [|n'].
        - contradiction (neq_k_n eq_refl).
        - unfold get; reflexivity.
    (* get (replace_nth n l new) (S k') = get l (S k') *)
    * intros l n neq_k_n. destruct l as [|l_O l'].
      (* get (replace_nth n nil new) (S k') = get nil (S k') *)
      + destruct n as [|n'].
        - simpl; reflexivity.
        - simpl; reflexivity.
      (* get (replace_nth n (l_O :: l') new) (S k') = get (l_O :: l') (S k') *)
      + destruct n as [|n'].
        - unfold get; reflexivity.
        - unfold not in neq_k_n.
          assert (k' <> n') as neq_k'_n'.
          -- intro eq_k'_n'. apply (neq_k_n (eq_S _ _ eq_k'_n')).
          -- unfold get in IHk. unfold get; simpl.
             apply (IHk l' n' neq_k'_n').
  Qed.

  Lemma contraposition : forall (P Q: Prop), (P -> Q) -> (~Q -> ~P).
  Proof.
    intros P Q P_implies_Q Q_implies_False wit_P. apply (Q_implies_False (P_implies_Q wit_P)).
  Qed.

  Program Definition rot_i_right {dim} {shape: Shape (S dim)} (axis: Fin (S dim))
      (offset: Fin (S (get (` shape) (` axis)))) (array: Array E shape): Array E shape :=
    let shape_axis := get (` shape) (` axis) in
    fun ix => array (exist _ (replace_nth (` axis) (` ix)
                                          ((get (` ix) (` axis) + shape_axis - offset) mod shape_axis)) _).
  Next Obligation. split.
    (*
      length
        (replace_nth (` axis) (` ix) ((get (` ix) (` axis) + get (` shape) (` axis) - ` offset) mod get (` shape) (` axis))) =
      S dim
     *)
    * rewrite replace_nth_length_invariant. destruct ix as [ix_list ix_list_properties]; simpl.
      exact (proj1 ix_list_properties).
    (* *)
    * intro i.
      clear array.
      remember (tail_ix ix) as wit_tail_ix.
      destruct ix as [ix_list ix_list_properties]; simpl.
      destruct axis as [axis_val axis_lt_Sdim]; simpl.
      destruct i as [i_val i_lt_Sdim]; simpl; simpl in ix_list_properties.
      case_eq (i_val ?= axis_val).
      (* *)
      + intro wit_eq_i_val_axis_val. pose proof (Nat.compare_eq _ _ wit_eq_i_val_axis_val) as eq_i_val_axis_val.
        rewrite eq_i_val_axis_val.
        clear i_val i_lt_Sdim eq_i_val_axis_val wit_eq_i_val_axis_val.
        generalize dependent ix_list. generalize dependent dim.
        induction axis_val.
        (* *)
        - intros dim shape axis_lt_Sdim offset wit_tail_ix ix_list ix_list_properties wit_tail_ix_is_tail_ix.
          destruct shape as [shape_list shape_list_has_length_Sdim]; simpl; simpl in offset.
          destruct shape_list as [|shape_list_O shape_list'].
          (* absurd *)
          -- contradiction (Nat.neq_0_succ _ shape_list_has_length_Sdim).
          -- destruct ix_list as [|ix_list_O ix_list'].
            (* absurd *)
            ++ contradiction (Nat.neq_0_succ _ (proj1 ix_list_properties)).
            ++ unfold get; simpl. apply Nat.mod_upper_bound.
               intro eq_shape_list_O_O. unfold tail_ix in wit_tail_ix_is_tail_ix;
               simpl in wit_tail_ix_is_tail_ix.
               generalize ((tail_ix_obligation_1 dim
                              (exist (fun s : list nat => length s = S dim) (shape_list_O :: shape_list')
                                 shape_list_has_length_Sdim)
                              (exist
                                 (fun ix : list nat =>
                                  length ix = S dim /\
                                  (forall i : Fin (S dim), get ix (` i) < get (shape_list_O :: shape_list') (` i)))
                                 (ix_list_O :: ix_list') ix_list_properties))). simpl.
               intro proof. rewrite (proof_irrelevance _ _ proof) in wit_tail_ix_is_tail_ix.
               rewrite eq_shape_list_O_O in ix_list_properties.
               pose proof (proj2 ix_list_properties (exist _ O axis_lt_Sdim)) as inconsistent.
               unfold get in inconsistent; simpl in inconsistent.
               contradiction (Nat.nle_succ_0 _ inconsistent).
        - intros dim shape axis_lt_Sdim offset wit_tail_ix ix_list ix_list_properties.
          destruct shape as [shape_list shape_list_has_length_Sdim]; simpl; simpl in offset.
          destruct shape_list as [|shape_list_O shape_list'].
          (* absurd *)
          -- contradiction (Nat.neq_0_succ _ shape_list_has_length_Sdim).
          -- destruct ix_list as [|ix_list_O ix_list'].
            (* absurd *)
            ++ contradiction (Nat.neq_0_succ _ (proj1 ix_list_properties)).
            ++ unfold get; simpl; simpl in ix_list_properties.
               destruct dim as [|dim'].
               (* absurd *)
               ** contradiction (Nat.nle_succ_0 _ (le_S_n _ _ axis_lt_Sdim)).
               ** destruct shape_list' as [|shape_list'_O shape_list''].
                 (* absurd *)
                 --- contradiction (Nat.neq_0_succ _ (eq_add_S _ _ shape_list_has_length_Sdim)).
                 --- assert (length (shape_list'_O :: shape_list'') = S dim') as shape_list_has_length_Sdim_simpl.
                     +++ simpl; simpl in shape_list_has_length_Sdim.
                         apply (eq_add_S _ _ shape_list_has_length_Sdim).
                     +++ intro wit_tail_ix_is_tail_ix.
                         unfold tail_ix in wit_tail_ix_is_tail_ix; simpl in wit_tail_ix_is_tail_ix.
                         generalize (tail_ix_obligation_1 (S dim')
                              (exist (fun s : list nat => length s = S (S dim'))
                                 (shape_list_O :: shape_list'_O :: shape_list'') shape_list_has_length_Sdim)
                              (exist
                                 (fun ix : list nat =>
                                  length ix = S (S dim') /\
                                  (forall i : Fin (S (S dim')),
                                   nth (` i) ix 0 <
                                   match ` i with
                                   | 0 => shape_list_O
                                   | 1 => shape_list'_O
                                   | S (S m0) => nth m0 shape_list'' 0
                                   end)) (ix_list_O :: ix_list') ix_list_properties)). simpl.
                         intro ix_list'_properties. rewrite (proof_irrelevance _ _ ix_list'_properties) in wit_tail_ix_is_tail_ix.
                         remember (tail_ix wit_tail_ix) as wit_tail_tail_ix.
                         rewrite wit_tail_ix_is_tail_ix in Heqwit_tail_tail_ix.
                         unfold tail_ix in Heqwit_tail_tail_ix.
                         simpl in Heqwit_tail_tail_ix.
                         generalize (tail_ix_obligation_1 dim'
                           (tail_shape
                              (exist (fun s : list nat => length s = S (S dim'))
                                 (shape_list_O :: shape_list'_O :: shape_list'') shape_list_has_length_Sdim))
                           (exist
                              (fun ix : list nat =>
                               length ix = S dim' /\
                               (forall i : Fin (S dim'), get ix (` i) < get (shape_list'_O :: shape_list'') (` i)))
                              ix_list' ix_list'_properties)).
                         simpl. intro tl_ix_list'_properties.
                         rewrite (proof_irrelevance _ _ tl_ix_list'_properties) in Heqwit_tail_tail_ix.
                         pose proof (IHaxis_val dim'
                                                (exist _ (shape_list'_O :: shape_list'') shape_list_has_length_Sdim_simpl)
                                                (le_S_n _ _ axis_lt_Sdim)
                                                offset
                                                wit_tail_tail_ix
                                                ix_list' 
                                                ix_list'_properties
                                                ) as f_result.
                         unfold tail_ix in f_result. simpl in f_result.
                         rewrite (proof_irrelevance _ _ tl_ix_list'_properties) in f_result.
                         pose proof (f_result Heqwit_tail_tail_ix) as proof.
                         unfold get in proof. exact proof.
      + intro wit_i_val_lt_axis_val.
        assert ((i_val ?= axis_val) <> Eq) as wit_i_val_neq_axis_val.
        - rewrite wit_i_val_lt_axis_val; discriminate.
        - Search ((?x ?= ?y)). Search (((?y -> False) -> (?x -> False)) <-> (?x -> ?y)).
          Check Nat.compare_eq_iff.
          pose proof ((fun n m => contraposition _ _ (proj2 (Nat.compare_eq_iff n m))) _ _ wit_i_val_neq_axis_val) as i_val_neq_axis_val.
          rewrite (replace_nth_only_modifies_nth_component _ _ _ _ i_val_neq_axis_val).
          apply (proj2 ix_list_properties (exist _ i_val i_lt_Sdim)).
      + intro wit_i_val_lt_axis_val.
        assert ((i_val ?= axis_val) <> Eq) as wit_i_val_neq_axis_val.
        - rewrite wit_i_val_lt_axis_val; discriminate.
        - Search ((?x ?= ?y)). Search (((?y -> False) -> (?x -> False)) <-> (?x -> ?y)).
          Check Nat.compare_eq_iff.
          pose proof ((fun n m => contraposition _ _ (proj2 (Nat.compare_eq_iff n m))) _ _ wit_i_val_neq_axis_val) as i_val_neq_axis_val.
          rewrite (replace_nth_only_modifies_nth_component _ _ _ _ i_val_neq_axis_val).
          apply (proj2 ix_list_properties (exist _ i_val i_lt_Sdim)).
  Qed.

  (* Content from the paper *)

  (* The definitions below are implemented from the text of the paper at <> *)

  (* 5.1 *)

  (* Definition 2 *)

  (* For our purposes, we need to define a new type of arrays ("PaddedArray"s) that carry shape information of
     one of their slices. To use our previously defined operations, we also define two projection functions:
      - inner, that returns the annotated array slice
      - outer, that returns the whole array stripped of its additional inner shape information
  *)

  (* An inner shape consists of a list of pairs (s_i, e_i), as described in the paper. *)
  Definition InnerShape {dim} (outer_shape: Shape dim) :=
    { s_e: list (nat * nat)
      |  length s_e = dim
      /\ forall (i: Fin dim), (  fst (nth (` i) s_e (0, 0)) <= snd (nth (` i) s_e (0, 0))
                              /\ snd (nth (` i) s_e (0, 0)) <= get (` outer_shape) (` i)) }.

  Definition PaddedArray {dim} E (outer_shape: Shape dim) :=
    prod (Array E outer_shape) (InnerShape outer_shape).

  Definition outer {dim} {outer_shape: Shape dim} (padded_array: PaddedArray E outer_shape)
      : Array E outer_shape :=
    fst padded_array.

  Program Definition inner_shape_to_shape {dim} {outer_shape: Shape dim} (inner_shape: InnerShape outer_shape)
      : Shape dim :=
    map (fun start_and_end => snd start_and_end - fst start_and_end) inner_shape.
  Next Obligation. (* length (map (fun start_and_end : nat * nat => snd start_and_end - fst start_and_end) (` inner_shape)) = dim *)
    rewrite map_length.
    destruct inner_shape as [inner_shape_list inner_shape_list_properties].
    simpl. exact (proj1 inner_shape_list_properties).
  Defined.

  (* Helper functions *)

  Fixpoint zip {A B} (l1: list A) (l2: list B): list (A * B) :=
    match l1, l2 with | nil, _ => nil
                      | _, nil => nil
                      | a :: l1', b :: l2' => (a, b) :: zip l1' l2' end.

  Lemma eq_zip_length_l {A B} : forall (l1: list A) (l2: list B),
    length l1 = length l2 -> length (zip l1 l2) = length l1.
  Proof.
    intro l1.
    induction l1 as [|a l1' IHl1].
    (* length (zip nil l2) = length nil *)
    * unfold zip. reflexivity.
    (* length (zip (a :: l1) l2) = length (a :: l1) *)
    * intros l2 eq_length_l1_l2.
      destruct l2 as [|b l2'].
      (* absurd *)
      + simpl in eq_length_l1_l2. contradiction (Nat.neq_succ_0 _ eq_length_l1_l2).
      (* length (zip (a :: l1') (b :: l2')) = length (a :: l1') *)
      + simpl; simpl in eq_length_l1_l2.
        rewrite (IHl1 l2' (eq_add_S _ _ eq_length_l1_l2)).
        reflexivity.
  Defined.

  Program Definition tail_inner_shape {dim} {outer_shape: Shape (S dim)} (inner_shape: InnerShape outer_shape)
      : InnerShape (tail_shape outer_shape) :=
    exist _ (tl (` inner_shape)) _.
  Next Obligation. split.
    (* length (tl (` inner_shape)) = dim *)
    * destruct inner_shape as [inner_shape_list inner_shape_list_properties]; simpl.
      destruct inner_shape_list as [|inner_shape_list_O inner_shape_list'].
      (* absurd *)
      - contradiction (Nat.neq_0_succ _ (proj1 inner_shape_list_properties)).
      (* inner_shape_list = inner_shape_list_O :: inner_shape_list' *)
      - simpl. apply (Nat.succ_inj _ _ (proj1 inner_shape_list_properties)).
      (*
        forall i : Fin dim,
        fst (nth (` i) (tl (` inner_shape)) (0, 0)) <= snd (nth (` i) (tl (` inner_shape)) (0, 0)) <=
        get (tl (` outer_shape)) (` i)
      *)
    * intro i.
      destruct inner_shape as [inner_shape_list inner_shape_list_properties]. simpl. 
      destruct inner_shape_list as [|inner_shape_list_O inner_shape_list'].
      (* absurd *)
      - contradiction (Nat.neq_0_succ _ (proj1 inner_shape_list_properties)).
      (* inner_shape_list = inner_shape_list_O :: inner_shape_list' *)
      - destruct i as [i_val ival_lt_dim]; simpl.
        apply le_n_S in ival_lt_dim.
        pose proof (proj2 inner_shape_list_properties (exist _ (S i_val) ival_lt_dim)) as proof.
        destruct outer_shape as [outer_shape_list outer_shape_has_length_Sdim]; simpl.
        destruct outer_shape_list as [|outer_shape_list_O outer_shape_list'].
        (* absurd *)
        + contradiction (Nat.neq_0_succ _ outer_shape_has_length_Sdim).
        (* outer_shape_list = outer_shape_list_O :: outer_shape_list' *)
        + exact proof.
  Defined.

  Program Definition inner {dim} {outer_shape: Shape dim} (padded_array: PaddedArray E outer_shape)
      : Array E (inner_shape_to_shape (snd padded_array)) :=
    let outer_array := fst padded_array in
    let starts := map fst (snd padded_array) in
    let add_all := map (fun tx => fst tx + snd tx) in
    fun ix => outer_array (exist _ (add_all (zip starts ix)) _).
  Next Obligation. split.
    (* length (map (fun tx : nat * nat => fst tx + snd tx) (zip (map fst (` (snd padded_array))) (` ix))) = dim *)
    * rewrite map_length.
      destruct padded_array as [outer_array inner_shape]; simpl.
      destruct inner_shape as [inner_shape_list inner_shape_list_properties].
      destruct ix as [ix_list ix_list_properties].
      simpl; simpl in ix_list_properties.
      pose proof (eq_trans (eq_trans (map_length fst inner_shape_list) (proj1 inner_shape_list_properties))
                           (eq_sym (proj1 ix_list_properties))) as inner_helper.
      rewrite (eq_zip_length_l _ _ inner_helper).
      rewrite map_length.
      exact (proj1 inner_shape_list_properties).
    * intro i.
      unfold get.
      Check map_nth.
      remember (fun tx : nat * nat => fst tx + snd tx) as add_tup.
      assert (0 = add_tup (0, 0)) as eq_O_add_tup_OO.
      (* 0 = add_tup (0, 0) *)
      + rewrite Heqadd_tup; simpl. reflexivity.
      + destruct padded_array as [array inner_shape]. simpl.
        simpl in ix.
        clear array.
        destruct i as [i_val i_lt_dim]. simpl.
        generalize dependent dim.
        generalize dependent i_val. induction i_val.
        ** intros dim outer_shape inner_shape ix O_lt_dim.
           destruct inner_shape as [inner_shape_list inner_shape_list_properties]; simpl.
           destruct ix as [ix_list ix_list_properties]; simpl.
           simpl in ix_list_properties.
           rewrite eq_O_add_tup_OO.
           rewrite map_nth.
           rewrite Heqadd_tup. simpl.
           pose proof (proj2 ix_list_properties (exist _ O O_lt_dim)) as proof. simpl in proof.
           remember (nth O (zip (map fst inner_shape_list) ix_list) (0, 0)) as nth_tuple.
           destruct inner_shape_list as [|inner_shape_list_O inner_shape_list']; simpl.
           (* absurd *)
           - rewrite <- (proj1 inner_shape_list_properties) in O_lt_dim; simpl in O_lt_dim.
             contradiction (Nat.nlt_0_r _ O_lt_dim).
           (* inner_shape_list = inner_shape_list_O :: inner_shape_list' *)
           - destruct ix_list as [|ix_list_O ix_list'].
             (* absurd *)
             -- rewrite <- (proj1 ix_list_properties) in O_lt_dim; simpl in O_lt_dim.
                contradiction (Nat.nlt_0_r _ O_lt_dim).
             (* ix_list = ix_list_O :: ix_list_' *)
             -- destruct inner_shape_list_O as [inner_shape_list_O_l inner_shape_list_O_r].
                simpl in Heqnth_tuple. rewrite Heqnth_tuple; simpl.
                unfold get in proof; simpl in proof.
                destruct outer_shape as [outer_shape_list outer_shape_list_has_length_dim]; simpl.
                destruct outer_shape_list as [|outer_shape_list_O outer_shape_list'].
                (* absurd *)
                ++ rewrite <- outer_shape_list_has_length_dim in O_lt_dim; simpl in O_lt_dim.
                   contradiction (Nat.nlt_0_r _ O_lt_dim).
                (* outer_shape_list = outer_shape_list_O :: outer_shape_list' *)
                ++ simpl.
                   pose proof (proj2 inner_shape_list_properties (exist _ O O_lt_dim)) as bounds_order.
                   unfold get in bounds_order; simpl in bounds_order.
                   apply (plus_le_compat_r _ _ inner_shape_list_O_l) in proof.
                   rewrite (Nat.sub_add _ _ (proj1 bounds_order)) in proof.
                   unfold get in bounds_order; simpl in bounds_order.
                   rewrite Nat.add_succ_l in proof.
                   rewrite Nat.add_comm in proof.
                   exact (le_trans _ _ _ proof (proj2 bounds_order)).
        ** intros dim outer_shape inner_shape ix S_ival_lt_dim. simpl in ix.
           destruct dim as [|dim'].
           (* absurd *)
           - contradiction (Nat.nle_succ_0 _ S_ival_lt_dim).
           (* dim = S dim' *)
           - pose (tail_inner_shape inner_shape) as tl_inner_shape.
             pose (tail_shape outer_shape) as tl_outer_shape.
             pose (tail_ix ix) as tl_ix.
             destruct inner_shape as [inner_shape_list inner_shape_list_properties]; simpl.
             destruct ix as [ix_list ix_list_properties]; simpl.
             destruct inner_shape_list as [|inner_shape_list_O inner_shape_list'].
             (* absurd *)
             -- contradiction (Nat.neq_0_succ _ (proj1 inner_shape_list_properties)).
             (* inner_shape_list = inner_shape_list_O :: inner_shape_list' *)
             -- rewrite eq_O_add_tup_OO. rewrite map_nth.
                destruct ix_list as [|ix_list_O ix_list'].
                (* absurd *)
                ++ contradiction (Nat.neq_0_succ _ (proj1 ix_list_properties)).
                (* ix_list = ix_list_O :: ix_list' *)
                ++ simpl.
                   rewrite <- (map_nth add_tup _ _ i_val).
                   pose proof (IHi_val dim' tl_outer_shape tl_inner_shape tl_ix (le_S_n _ _ S_ival_lt_dim)) as proof.
                   unfold tail_ix in tl_ix. simpl in tl_ix. simpl in proof.
                   destruct outer_shape as [outer_shape_list outer_shape_list_has_length_Sdim'].
                   destruct outer_shape_list as [|outer_shape_list_O outer_shape_list'].
                   (* absurd *)
                   +++ contradiction (Nat.neq_0_succ _ outer_shape_list_has_length_Sdim').
                   (* outer_shape_list = outer_shape_list_O :: outer_shape_list' *)
                   +++ simpl; simpl in proof. rewrite <- eq_O_add_tup_OO.
                       exact proof.
  Defined.
  Next Obligation.
                   
                   rewrite <- map_nth.  simpl.
 Check map_nth. rewrite <- map_nth. simpl. Search (0 = S ?x).
             simpl in ix_list_properties.
pose proof (IHi_val dim' (tail_shape outer_shape)
           pose (tail_ix ix) as tl_ix. proof Heqnth_tuple.
        
                exact H.
                Search (S ?x + ?y = S (?x + ?y)).
                Search (?x - ?m + ?m). Search (?x <= ?y -> ?x + ?z <= ?y + ?z).
        unfold fst.
        simpl.
        pattern 0 at 2. rewrite H. simpl.
      pose proof ((fun tx : nat * nat => fst tx + snd tx)fst (0, 0) + 0 = 0).
      rewrite map_nth.

  Defined.
  Definition PaddedShape {dim}
  Definition PaddedArray {dim} E (padded_shape: PaddedShape (S dim)) 

  Definition Shape dim := { s: list nat | length s = dim }.
Definition Array {dim} E (shape : Shape dim) :=
    Index shape -> E.
(*
  Program Definition rot0_right {dim} {shape: Shape (S dim)} (offset: Fin (S (hd 0 (` shape))))
      (array: Array E shape): Array E shape :=
    cat (take_neg offset array) (drop_neg offset array) _.
  Next Obligation. split.
    (* length (` x) = S dim *)
    * destruct x as [ix_list ix_list_properties]. exact (proj1 ix_list_properties).
    (* forall i : Fin (S dim), get (` x) (` i) < get (` offset + (hd 0 (` shape) - ` offset) :: tl (` shape)) (` i) *)
    * intro i. destruct i as [i_val i_val_lt_Sdim]; simpl.
      destruct shape as [shape_list shape_list_has_length_Sdim].
      destruct shape_list as [|shape_list_O shape_list'].
      (* absurd *)
      - contradiction (Nat.neq_0_succ _ shape_list_has_length_Sdim). 
      (* get (` x) i_val < get (` offset + (shape_list_O - ` offset) :: shape_list') i_val *)
      - simpl. destruct x as [ix_list ix_list_properties]; simpl. 
        destruct ix_list as [|ix_list_O ix_list'].
        (* absurd *)
        + contradiction (Nat.neq_0_succ _ (proj1 ix_list_properties)).
        (* get (ix_list_O :: ix_list') i_val < get (` offset + (shape_list_O - ` offset) :: shape_list') i_val *)
        + destruct offset as [offset_val offset_val_lt_hd_O_shape]; simpl; simpl in offset_val_lt_hd_O_shape.
          rewrite (Nat.add_sub_assoc _ _ _ (le_S_n _ _ offset_val_lt_hd_O_shape)).
          rewrite (Nat.add_sub_swap offset_val _ offset_val (le_refl offset_val)).
          rewrite Nat.sub_diag.
          rewrite Nat.add_0_l.
          apply (proj2 ix_list_properties (exist _ i_val i_val_lt_Sdim)).
  Defined.
*)


  (* TODO: finish core *)
End Array.
  (* TODO: expand *)
End Array.
