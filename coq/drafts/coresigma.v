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

  Definition get (l: list nat) (i: nat) := nth i l 0.

  Definition Index {dim} (shape: Shape dim) :=
    { ix : list nat |  length ix = dim
                    /\ forall (i: Fin dim), get ix (` i) < get (` shape) (` i) }.

  Definition Array {dim} E (shape : Shape dim) :=
    Index shape -> E.

  Definition pi {dim} (shape: Shape dim) : nat :=
    fold_right (fun x y => x * y) 1 (` shape).

  (* === MoA operations === *)

  (* === array projections === *)

  Definition rho {dim} {shape: Shape dim}
    (array : Array E shape) : Shape dim := shape.
  Definition total_ix {dim} {shape: Shape dim}
                      (i: Index shape) (array: Array E shape) : E :=
    array i.

  (* TODO: the below must be rewritten according to the new definitions *)
  (*
  (* === reshaping utils === *)

  Definition reshape {dim1 dim2} {shape1: Shape dim1}
      (array: Array E shape1) (shape2: Shape dim2)
      (eq_pi_shapes: pi shape1 = pi shape2) : Array E shape2 :=
    

  (* === reshaping utils === *)

  Definition reshape {dim1 dim2 : nat} {shape1 : Shape dim1}
      (array : Array E shape1) (shape2 : Shape dim2)
      (eq_pi_shapes : pi shape1 = pi shape2) : Array E shape2 :=
    let (vec, eq_length_pi_shape1) := array in
    exist _ vec (eq_trans eq_length_pi_shape1 eq_pi_shapes).

  Show Obligation Tactic.
  Obligation Tactic := idtac.
  Program Fixpoint expand_dim_shape {dim} (shape : Shape dim)
      (axis : Fin (S dim)) : Shape (S dim) :=
    match axis, dim, shape with
    | O, _, _ => 1 :: shape
    | S axis', S dim', s_O :: s' =>
        s_O :: expand_dim_shape (dim:=dim') (exist _ s' _)
                                            (exist _ axis' _)
    | _, _, _ => _ (* absurd *)
    end.
  Next Obligation. (* S (length (` shape)) = S dim *)
    program_simpl.
    destruct shape as [shape_list length_is_dim]. simpl.
    rewrite length_is_dim. reflexivity.
  Defined.
  Next Obligation. (* length s' = dim' *)
    program_simpl.
    apply (f_equal (length (A:=nat))) in Heq_shape. simpl in Heq_shape.
    destruct shape as [shape_list length_is_dim]. simpl in Heq_shape.
    rewrite length_is_dim in Heq_shape.
    apply (eq_add_S _ _ Heq_shape)...
  Defined.
  Next Obligation. (* axis' < S dim') *)
    program_simpl.
    destruct axis as [axis axis_lt_SS_dim'].
    simpl in Heq_axis.
    rewrite <- Heq_axis in axis_lt_SS_dim'.
    apply (Le.le_S_n _ _ axis_lt_SS_dim')...
  Defined.
  Next Obligation. (* forall s : Shape dim', S (length (` s)) = S dim' *)
    program_simpl.
  Defined.
  Next Obligation. (* absurd *)
    program_simpl.
    destruct dim as [|dim'].
    (* Shape 1 *)
    - specialize (H0 0 (` shape)).
      destruct axis as [axis axis_le_1]. simpl in H0. simpl in H.
      apply Nat.lt_1_r in axis_le_1.
      rewrite axis_le_1 in H0.
      exfalso.
      apply (H0 (conj eq_refl (conj eq_refl eq_refl)))...
    (* Shape S (S dim') *)
    - destruct axis as [axis axis_le_SS_dim']. simpl in H0. simpl in H.
      destruct axis as [|axis'].
      (* axis = O *)
      + specialize (H0 (S dim') (` shape)). exfalso.
        apply (H0 (conj eq_refl (conj eq_refl eq_refl)))...
      (* axis = S axis' *)
      + destruct shape as [shape_list length_is_S_dim']. simpl in H0.
        simpl in H.
        destruct shape_list as [|s_O s_list'].
        (* shape_list = nil *) Search (0 = S ?x).
        * exfalso. apply (Nat.neq_0_succ _ length_is_S_dim')...
        (* shape_list = s_O :: s_list' *)
        * specialize (H axis' dim' s_O s_list'). exfalso.
          apply (H (conj eq_refl (conj eq_refl eq_refl)))...
  Defined.
  Next Obligation. program_simpl. split.
    (* (forall (axis' dim' s_O : nat) (s' : list nat),
          ~ (S dim' = 0 /\ S axis' = S H /\ s_O :: s' = ` shape)) *)
    - intros. intro broken_conj. destruct broken_conj as [inconsistent _].
      apply (Nat.neq_succ_0 _ inconsistent)...
    (* (forall (wildcard' : nat) (wildcard'0 : list nat),
          ~ (wildcard' = 0 /\ 0 = S H /\ wildcard'0 = ` shape)) *)
    - intros. intro broken_conj. destruct broken_conj as [_ broken_conj].
      destruct broken_conj as [inconsistent _].
      apply (Nat.neq_0_succ _ inconsistent)...
  Defined.
  Next Obligation. program_simpl. split.
    (* (forall (axis' dim' s_O : nat) (s' : list nat),
          ~ (S dim' = S H0 /\ S axis' = S H /\ s_O :: s' = nil)) *)
    - intros. intro broken_conj. destruct broken_conj as [_ broken_conj].
      destruct broken_conj as [_ inconsistent]. symmetry in inconsistent.
      apply (nil_cons inconsistent)...
    (* forall (wildcard' : nat) (wildcard'0 : list nat),
         ~ (wildcard' = S H0 /\ 0 = S H /\ wildcard'0 = nil) *)
    - intros. intro broken_conj. destruct broken_conj as [_ broken_conj].
      destruct broken_conj as [inconsistent _].
      apply (Nat.neq_0_succ _ inconsistent)...
  Defined.

  (* === take / drop / cat === *)
  (* TODO: rewrite all with Fin *)

  Obligation Tactic := program_simpl.
  Program Fixpoint take_vec {n : nat} (k : Fin (S n)) (v : Vect E n) {struct n} 
      : Vect E (` k) :=
    match k with
      | O => exist _ nil _
      | S k' =>
      match n, v in list _ with
        | O, _ => _ (* absurd *)
        | S n', e :: v' => exist _ (e :: (` (take_vec (n:=n') (exist _ k' _) (exist _ v' _)))) _
        | S _, _ => _ (* absurd *)
      end end.
  Next Obligation. (* absurd *)
    destruct v as [v length_v_is_O].
    destruct k as [k k_lt_1].
    simpl in Heq_k. rewrite <- Heq_k in k_lt_1.
    apply le_S_n in k_lt_1.
    exfalso. apply (Nat.nlt_0_r _ k_lt_1).
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

  Program Definition take_shape {dim : nat} (s : Shape dim) (k : Fin (hd 0 (` s)))
      : Shape dim :=
    exist _ (` k :: tl (` s)) _.
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

  Program Definition take {dim : nat} {s : Shape (S dim)} (k : Fin (hd 0 (` s)))
        (a : Array E s) : Array E (take_shape s k) :=
    exist _ (take_vec (n:=pi s) (k * pi (dim:=dim) (tl (` s))) (` a)) _.
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
  Next Obligation. (* length (` v) = pi (take_shape s k) *)
    generalize (take_vec
      (exist (fun i : nat => i < S (pi s))
         (` k * pi (exist (fun s0 : list nat => length s0 = dim) (tl (` s)) (take_obligation_1 dim s k a)))
         (take_obligation_2 dim s k a)) (exist (fun v : list E => length v = pi s) (` a) (take_obligation_3 dim s a))).
    simpl.
    intro v. destruct v as [v length_v_is_ktls].
    simpl. unfold take_shape. unfold pi.
    simpl. unfold pi in length_v_is_ktls.
    apply length_v_is_ktls.
  Defined.

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
