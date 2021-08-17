From Coq Require Import Arith List Omega Program.
From Equations Require Import Equations.

Require Import Coq.Arith.Le.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Logic.
Require Import Coq.Init.Peano.
(* dependent destruction, see https://jamesrwilcox.com/dep-destruct.html *)
Require Import Program.
(* === index spaces definition utils === *)

Require Import Coq.Vectors.Fin.

(* transport in HoTT, maybe useful looking at these libraries *)
Definition transport {T : Type} {x y : T} {P : T -> Type} (u : P x)
  (pf : x = y) : P y := match pf with | eq_refl => u end.

Module Array.
Variable E : Type.

Section Core.
(* === array definition utils === *)
Inductive shape : nat -> Type :=
  | snil : shape O
  | scons {dim} : nat -> shape dim -> shape (S dim).

Compute snil.
Compute scons 4 snil.

Inductive vect : nat -> Type :=
  | vnil : vect O
  | vcons {dim} : E -> vect dim -> vect (S dim).

Fixpoint pi {dim : nat} (s : shape dim) : nat := match s with
  | snil => 1
  | scons s_O s' => s_O * (pi s')
  end.

Inductive array {dim : nat} (s : shape dim) : Type :=
  mkarr : vect (pi s) -> array s.

(* === vect destructuring === *)
Definition hd_vect {length : nat} (v : vect (S length)) : E :=
  match v with | vcons e _ => e end.
Definition tl_vect {length : nat} (v : vect (S length)) : vect length :=
  match v with | vcons _ v' => v' end.

(* === shape destructuring === *)
(* TODO: make typeclass for this destructuring *)
Definition hd_shape {dim : nat} (s : shape (S dim)) : nat :=
  match s with | scons s_O _ => s_O end.
Definition tl_shape {dim : nat} (s : shape (S dim)) : shape dim :=
  match s with | scons _ s' => s' end.

Lemma hd_tl_id (dim : nat) (s : shape (S dim)) :
  s = scons (hd_shape s) (tl_shape s).
Proof.
  dependent destruction s. reflexivity.
Qed.

Lemma pi_hd_tl (dim : nat) (s : shape (S dim)) :
  pi s = hd_shape s * (pi (tl_shape s)).
Proof.
  dependent destruction s.
    (* scons n s *) simpl. reflexivity...
Qed.

(* === MoA operations === *)

(* === array projections === *)
Definition rho {dim : nat} {s : shape dim} (a : array s) : shape dim := s.
Definition elems {dim : nat} {s : shape dim} (a : array s) : vect (pi s) :=
  let (v) := a in v.

(* === reshaping utils === *)

Program Definition reshape {dim1 dim2 : nat} {s1 : shape dim1}
    (a : array s1) (s2 : shape dim2) (p : pi s1 = pi s2) : array s2 :=
  let vec := elems a in mkarr s2 vec.

Program Fixpoint expand_dim_shape {dim} (s : shape dim) (axis : nat)
    (axis_le_dim : axis <= dim) := match axis with
  | O => scons 1 s
  | S axis' => match s with
    | snil => _ (* absurd *)
    | scons s_k s' => scons s_k (expand_dim_shape s' axis' _)
    end
  end.
Next Obligation. (* shape 1 *)
  pose proof (le_Sn_0 axis') as p_inconsistent.
  apply p_inconsistent in axis_le_dim.
  exfalso. apply axis_le_dim.
Defined.
Next Obligation. (* axis' <= wildcard' *)
  apply (le_S_n axis' wildcard' axis_le_dim).
Defined.

Lemma pi_expand_s_pi_s : forall {dim : nat} (s : shape dim) axis axis_le_dim,
  pi (expand_dim_shape s axis axis_le_dim) = pi s.
Proof.
  intros dim s.
  induction s as [|dim s_O s' IHs].
    (* s = snil *) intros. destruct axis as [|axis'].
      (* axis = 0 *) reflexivity...
      (* axis = S axis' *) exfalso; apply (Nat.nle_succ_0 _ axis_le_dim)...
    (* s = scons s_O s' *) intros. destruct axis as [|axis'].
      (* axis = 0 *) apply Nat.add_comm...
      (* axis = S axis' *) simpl. rewrite IHs. reflexivity...
Qed.

Program Definition expand_dim_O {dim : nat} {s : shape dim} (a : array s)
    : array (expand_dim_shape s 0 _) := reshape a (expand_dim_shape s 0 _) _.
Next Obligation. (* 0 <= dim *) apply Nat.le_0_l. Qed.
Next Obligation. (* pi s = pi (expand_dim_shape s 0 (expand_dim_O_obligation_1 dim)) *)
  symmetry. apply pi_expand_s_pi_s.
Qed.

(** Counts the number of dimensions set to 1 in the shape. *)
Fixpoint count_squeezable_dims {dim : nat} (s : shape dim) : nat :=
  match s with
    | snil => O
    | scons s_O s' => match s_O with
      | O => count_squeezable_dims s'
      | S s_O' => match s_O' with
        | O => S (count_squeezable_dims s')
        | _ => count_squeezable_dims s'
        end
      end
    end.

Lemma le_squeezable_dims_dims {dim : nat} : forall (s : shape dim),
  count_squeezable_dims s <= dim.
Proof.
  induction dim as [|dim' IHdim].
    (* dim = 0 *) intro s. dependent destruction s. trivial...
    (* dim = S dim' *)
     intro s. dependent destruction s.
     pose proof (IHdim s) as Hdim.
     destruct n as [|n'].
      (* n = 0 *) simpl; apply (Nat.le_le_succ_r _ _ Hdim)...
      (* n = S n' *) destruct n' as [|n''].
        (* n' = 0 *) apply (Le.le_n_S _ _ Hdim)...
        (* n' = S n'' *) apply (Nat.le_le_succ_r _ _ Hdim)...
Qed.

(** Removes all the dimensions set to 1 from the shape. *)
Program Fixpoint squeeze_shape {dim : nat} (s : shape dim)
    : shape (dim - (count_squeezable_dims s)) := match s with
  | snil => snil
  | scons s_O s' =>
    match count_squeezable_dims s - count_squeezable_dims s' with
      | O => scons s_O (squeeze_shape s')
      | S _ => squeeze_shape s'
      end
  end.
Next Obligation.
  destruct s_O as [|s_O'].
    (* s_O = 0 *) rewrite (minus_Sn_m _ _ (le_squeezable_dims_dims s')).
     reflexivity...
    (* s_O = S s_O' *) destruct s_O' as [|s_O''].
      (* s_O' = 0 *)
       rewrite <- Heq_s in Heq_anonymous.
       assert (forall d (sd : shape d),
                      count_squeezable_dims (scons 1 sd) =
                      S (count_squeezable_dims sd)) as csd_cons1_S_id.
        (* csd_cons1_S_id *) intros. simpl. reflexivity...
       rewrite (csd_cons1_S_id _ s') in Heq_anonymous.
       rewrite <- (minus_Sn_m _ _ (Nat.le_refl _)) in Heq_anonymous.
       rewrite Nat.sub_diag in Heq_anonymous.
       apply Nat.neq_0_succ in Heq_anonymous. exfalso. apply Heq_anonymous...
      (* s_O' = S s_O'' *)
       rewrite (minus_Sn_m _ _ (le_squeezable_dims_dims s')).
       reflexivity.
Qed.
Next Obligation.
  destruct s_O as [|s_O'].
    (* s_O = 0 *)
     rewrite <- Heq_s in Heq_anonymous.
     simpl in Heq_anonymous.
     rewrite Nat.sub_diag in Heq_anonymous.
     symmetry in Heq_anonymous.
     apply Nat.neq_0_succ in Heq_anonymous. exfalso. apply Heq_anonymous.
    (* s_O = S s_O' *) destruct s_O' as [|s_O''].
      (* s_O' = 0 *) reflexivity.
      (* s_O' = S s_O'' *) rewrite <- Heq_s in Heq_anonymous.
       simpl in Heq_anonymous.
       rewrite Nat.sub_diag in Heq_anonymous.
       symmetry in Heq_anonymous.
      apply Nat.neq_0_succ in Heq_anonymous. exfalso. apply Heq_anonymous.
Qed.

(* === take / drop / cat === *)
(* TODO: rewrite all with Fin *)

Program Fixpoint take_vect {length : nat} (n : nat) (v : vect length)
    (le_n_length : n <= length) : vect n := match n with
  | O => vnil
  | S n' => match v with
    | vnil => _
    | vcons e v' => vcons e (take_vect n' v' _)
    end
  end.
Solve All Obligations.
Next Obligation.
  exfalso; pose proof le_Sn_0 n' as le_Sn'_0.
  apply (le_Sn'_0 le_n_length).
Defined.
Next Obligation. apply (le_S_n _ _ le_n_length). Defined.

Program Fixpoint drop_vect {length : nat} (n : nat) (v : vect length)
    (le_n_length : n <= length) : vect (length - n) := match n with
  | O => v
  | S n' => match v with
    | vnil => _
    | vcons e v' => drop_vect n' v' _
    end
  end.
Next Obligation. rewrite <- minus_n_O. reflexivity. Defined.
Next Obligation. apply (le_S_n _ _ le_n_length). Defined.

Program Definition take_neg_vect {length : nat} (n : nat) (v : vect length)
  (le_n_length : n <= length) : vect n := drop_vect (length - n) v _.
Next Obligation. apply Nat.le_sub_l. Qed.
Next Obligation.
  generalize dependent n.
  induction length as [|length' IHlength].
    (* length = 0 *) intros. rewrite <- (le_n_0_eq n le_n_length). trivial...
    (* length = S length' *)
     intros.
     generalize dependent n.
     induction n as [|n' IHn].
      (* n = 0 *)
       intros.
       rewrite <- minus_n_O.
       symmetry.
       apply minus_diag_reverse...
      (* n = S n' *)
       intros.
       simpl (S length' - S n').
       rewrite <- (minus_Sn_m length' _).
        (* S (length' - (length' - n')) = S n' *)
         apply eq_S.
         pose proof (le_Sn_le _ _ le_n_length) as le_n_S_length'.
         pose proof (IHn le_n_S_length') as S_goal.
         rewrite <- (minus_Sn_m _ n') in S_goal.
          (* length' - (length' - n') = n' *) apply S_goal.
          (* n' <= length' *) apply (le_S_n _ _ le_n_length).
        (* length' - n' <= length' *) apply Nat.le_sub_l.
Defined.

Program Definition drop_neg_vect {length : nat} (n : nat) (v : vect length)
    (le_n_length : n <= length) : vect (length - n) :=
  take_vect (length - n) v _.
Next Obligation. apply Nat.le_sub_l. Defined.

Definition take_shape {dim : nat} (n : nat) (s : shape (S dim))
    (le_n_hdshape : n <= hd_shape s) : shape (S dim) := scons n (tl_shape s).
Definition drop_shape {dim : nat} (n : nat) (s : shape (S dim))
    (le_n_length : n <= hd_shape s) : shape (S dim) :=
  scons (hd_shape s - n) (tl_shape s).

Lemma eq_take_tlshape {dim : nat} (n : nat) (s : shape (S dim))
    (le_n_hdshape : n <= hd_shape s) :
  tl_shape s = tl_shape (take_shape n s le_n_hdshape).
Proof. unfold take_shape. unfold tl_shape. reflexivity. Qed.

Lemma eq_drop_tlshape {dim : nat} (n : nat) (s : shape (S dim))
    (le_n_hdshape : n <= hd_shape s) :
  tl_shape s = tl_shape (drop_shape n s le_n_hdshape).
Proof. unfold drop_shape. unfold tl_shape. reflexivity. Qed.

Lemma le_pi_slice_s {dim : nat} (n : nat) (s : shape (S dim))
  (le_n_hdshape : n <= hd_shape s) : n * pi (tl_shape s) <= pi s.
Proof.
  dependent destruction s.
  unfold tl_shape.
  unfold pi.
  unfold hd_shape in le_n_hdshape.
  apply (Mult.mult_le_compat_r n n0 _ le_n_hdshape).
Qed.

Program Definition take {dim : nat} {s : shape (S dim)} (n : nat)
      (a : array s) (le_n_hdshape : n <= hd_shape s)
    : array (take_shape n s le_n_hdshape) :=
  let (v) := a in mkarr _ (take_vect (n * pi (tl_shape s)) v _).
Next Obligation. apply le_pi_slice_s. apply le_n_hdshape. Qed.

Program Definition drop {dim : nat} {s : shape (S dim)} (n : nat)
      (a : array s) (le_n_hdshape : n <= hd_shape s)
    : array (drop_shape n s le_n_hdshape) :=
  let (v) := a in mkarr _ (drop_vect (n * pi (tl_shape s)) v _).
Next Obligation. apply le_pi_slice_s. apply le_n_hdshape. Qed.
Next Obligation.
  dependent destruction s.
  rewrite pi_hd_tl.
  unfold hd_shape. symmetry.
  apply (Mult.mult_minus_distr_r n n0 _).
Qed.

Program Definition take_neg {dim : nat} {s : shape (S dim)} (n : nat)
      (a : array s) (le_n_hdshape : n <= hd_shape s)
    : array (take_shape n s le_n_hdshape) :=
  let (v) := a in mkarr _ (drop_vect ((hd_shape s - n) * pi (tl_shape s)) v _).
Next Obligation. (* (hd_shape s - n) * pi (tl_shape s) <= pi s *)
  rewrite pi_hd_tl.
  apply Nat.mul_le_mono_r.
  apply Nat.le_sub_l.
Qed.
Next Obligation. (* pi s - (hd_shape s - n) * pi (tl_shape s) = n * pi (tl_shape s) *)
  rewrite pi_hd_tl.
  rewrite <- Nat.mul_sub_distr_r.
  rewrite (minus_plus_simpl_l_reverse _ _ n).
  rewrite <- (le_plus_minus _ _ le_n_hdshape).
  rewrite <- (Nat.add_sub_assoc _ _ _ (le_refl _)).
  rewrite Nat.sub_diag. rewrite Nat.add_0_r. reflexivity.
Qed.

Program Definition drop_neg {dim : nat} {s : shape (S dim)} (n : nat)
      (a : array s) (le_n_hdshape : n <= hd_shape s)
    : array (drop_shape n s le_n_hdshape) :=
  let (v) := a in mkarr _ (take_vect ((hd_shape s - n) * pi (tl_shape s)) v _).
Next Obligation. (* (hd_shape s - n) * pi (tl_shape s) <= pi s *)
  rewrite pi_hd_tl.
  apply Nat.mul_le_mono_r.
  apply Nat.le_sub_l.
Qed.

Program Fixpoint psi {dim : nat} {s : shape (S dim)}
    (idx : Fin.t (hd_shape s)) (a : array s) : array (tl_shape s) :=
  match idx with | F1 => reshape (take 1 a _) (tl_shape s) _
                 | FS pp => psi pp (drop 1 a _) end.
Next Obligation. apply le_n_S. apply Nat.le_0_l. Qed.
Next Obligation. apply le_n_S. apply Nat.le_0_l. Qed.
Next Obligation. simpl. symmetry. apply Nat.sub_0_r. Qed.
End Core.

(* Concatenation utils *)

Fixpoint cat_vect {length1 length2 : nat} (vec1 : vect length1)
    (vec2 : vect length2) : vect (length1 + length2) := match vec1 with
  | vnil => vec2
  | vcons e vec1' => vcons e (cat_vect vec1' vec2)
  end.

Definition add_hd_shapes {dim : nat} (s1 : shape (S dim)) (s2 : shape (S dim))
    (eq_tl_shapes : tl_shape s1 = tl_shape s2) : shape (S dim) :=
  scons (hd_shape s1 + hd_shape s2) (tl_shape s1).

Program Definition cat {dim : nat} {s1 s2 : shape (S dim)} (a1 : array s1)
      (a2 : array s2) (eq_tl_shapes : tl_shape s1 = tl_shape s2)
    : array (add_hd_shapes s1 s2 eq_tl_shapes) :=
  mkarr _ (cat_vect (elems a1) (elems a2)).
Next Obligation. (* pi s1 + pi s2 = (hd_shape s1 + hd_shape s2) * pi (tl_shape s1) *)
  dependent destruction s1.
  dependent destruction s2.
  rewrite (pi_hd_tl _ (scons n s1)).
  rewrite (pi_hd_tl _ (scons n0 s2)).
  unfold hd_shape.
  rewrite eq_tl_shapes. symmetry.
  apply (Mult.mult_plus_distr_r n n0 _).
Qed.

(* Useful properties *)
(* TODO: cleanup properties *)
Lemma take_drop_add_hdshapes {dim : nat} (n : nat) (s : shape (S dim))
  (le_n_hdshape : n <= hd_shape s) :
    add_hd_shapes (take_shape n s le_n_hdshape) (drop_shape n s le_n_hdshape)
                  (eq_trans (eq_take_tlshape n s le_n_hdshape) (eq_take_tlshape n s le_n_hdshape)) = s.
Proof.
  dependent destruction s.
  unfold add_hd_shapes.
  unfold take_shape. unfold drop_shape.
  unfold hd_shape. unfold tl_shape.
  unfold hd_shape in le_n_hdshape.
  rewrite (Minus.le_plus_minus_r _ _ le_n_hdshape).
  reflexivity.
Qed.

Lemma take_vect_elems_take : forall {dim : nat} {s : shape (S dim)} (n : nat) (a : array s)
  (le_n_hdshape : n <= hd_shape s),
    take_vect (n * pi (tl_shape s)) (elems a)
              (le_pi_slice_s n s le_n_hdshape) = elems (take n a le_n_hdshape).
Proof.
  intros. destruct a. unfold take. unfold elems.
  rewrite (proof_irrelevance (n * pi (tl_shape s) <= pi s) (take_obligation_1 dim s n _) (le_pi_slice_s n s le_n_hdshape)).
  reflexivity.
Qed.

Lemma pi_drop_n_pi_minus_n : forall {dim} (n : nat) (s : shape (S dim)) (le_n_hdshape : n <= hd_shape s),
  pi (drop_shape n s le_n_hdshape) = pi s - n * pi (tl_shape s).
Proof.
  intros.
  dependent destruction s. simpl.
  apply (Mult.mult_minus_distr_r n0 n _).
Qed.

Lemma drop_vect_elems_drop : forall {dim : nat} {s : shape (S dim)} (n : nat) (a : array s)
  (le_n_hdshape : n <= hd_shape s),
    transport (drop_vect (n * pi (tl_shape s)) (elems a) (le_pi_slice_s n s le_n_hdshape)) (eq_sym (pi_drop_n_pi_minus_n n s le_n_hdshape))
  = elems (drop n a le_n_hdshape) .
Proof.
  intros.
  destruct a.
  unfold transport. unfold drop. unfold elems. unfold eq_rect.
  rewrite (proof_irrelevance (n * pi (tl_shape s) <= pi s) ((drop_obligation_1 dim s n le_n_hdshape)) (le_pi_slice_s n s le_n_hdshape)).
  rewrite (proof_irrelevance (pi s - n * pi (tl_shape s) = pi (drop_shape n s le_n_hdshape))
                             (drop_obligation_2 dim s n (mkarr s v) le_n_hdshape v)
                             (eq_sym (pi_drop_n_pi_minus_n n s le_n_hdshape))).
  reflexivity.
Qed.

Lemma take_Sv_cons_vect : forall {length : nat} (n : nat) (e : E) (v : vect length)
    (p : n <= length), vcons e (take_vect n v p) = take_vect (S n) (vcons e v) (le_n_S n length p).
  Proof. intros. unfold take_vect. simpl.
  rewrite (proof_irrelevance (n <= length) (le_S_n n length (le_n_S n length p)) p). reflexivity.
  Qed.

  Lemma cat_vcons_vcons_cat : forall {l1 l2 : nat} (v1 : vect (S l1))
    (v2 : vect l2), vcons (hd_vect v1) (cat_vect (tl_vect v1) v2) = cat_vect v1 v2.
  Proof. intros. dependent destruction v1. unfold hd_vect. unfold tl_vect. unfold cat_vect. reflexivity. Qed.

  Theorem take_drop_cat_vect : forall {length : nat} (n : nat) (v : vect length) (p : n <= length),
    v = transport (cat_vect (take_vect n v p) (drop_vect n v p)) (le_plus_minus_r n length p).
  Proof. intros. unfold transport. generalize dependent n. induction v.
    - intros. destruct n.
      * simpl. unfold eq_rect. rewrite (UIP_refl _ _ (eq_ind 0 (fun n : nat => 0 = n) eq_refl 0 (minus_n_O 0))).
        rewrite (UIP_refl _ _ (le_plus_minus_r 0 0 p)). reflexivity.
      * pose proof le_Sn_0 n as Hp. exfalso. apply Hp in p. apply p. (* TODO: make ltac? *)
    - intros. destruct n.
      * simpl. unfold eq_rect.
        rewrite (UIP_refl _ _ (eq_ind (S dim) (fun n : nat => S dim = n) eq_refl (S dim) (minus_n_O (S dim)))).
        rewrite (UIP_refl _ _ (le_plus_minus_r 0 (S dim) p)). reflexivity.
      * rewrite (proof_irrelevance (S n <= S dim) p (le_n_S n dim (le_S_n n dim p))). rewrite <- take_Sv_cons_vect.
        rewrite (proof_irrelevance (S n <= S dim) (le_n_S n dim (le_S_n n dim p)) p).
        rewrite <- cat_vcons_vcons_cat. simpl. pattern v at 1. rewrite (IHv n (le_S_n n dim p)).
        generalize (cat_vect (take_vect n v (le_S_n n dim p)) (drop_vect n v (le_S_n n dim p))) as vec.
        generalize (le_plus_minus_r n dim (le_S_n n dim p)) as refl_dim.
        generalize (le_plus_minus_r (S n) (S dim) p) as refl_Sdim. simpl.
        rewrite (le_plus_minus_r n dim (le_S_n n dim p)). intros.
        rewrite (UIP_refl _ _ refl_Sdim). rewrite (UIP_refl _ _ refl_dim). reflexivity.
  Qed.

Theorem take_drop_cat : forall {dim : nat} {s : shape (S dim)} (n : nat)
    (a : array s) (le_n_hdshape : n <= hd_shape s),
      transport a (eq_sym (take_drop_add_hdshapes n s le_n_hdshape))
    = cat (take n a le_n_hdshape) (drop n a le_n_hdshape) (eq_trans (eq_sym (eq_take_tlshape n s le_n_hdshape)) (eq_drop_tlshape n s le_n_hdshape)).
Proof.
  intros.
  rewrite (UIP_refl _ (tl_shape s) (eq_trans (eq_sym (eq_take_tlshape n s le_n_hdshape)) (eq_drop_tlshape n s le_n_hdshape))).
  unfold cat.
  unfold eq_rect.
  rewrite <- take_vect_elems_take.
  rewrite <- drop_vect_elems_drop.
  unfold transport.
  remember (le_pi_slice_s n s le_n_hdshape) as p_order.
  generalize (eq_sym (pi_drop_n_pi_minus_n n s le_n_hdshape))
             (cat_obligation_1 dim (take_shape n s le_n_hdshape) (drop_shape n s le_n_hdshape) (take n a le_n_hdshape) (drop n a le_n_hdshape) (eq_refl (x:=tl_shape s)))
             (eq_sym (take_drop_add_hdshapes n s le_n_hdshape)).
  destruct a. simpl. generalize dependent v.
  dependent destruction s. simpl.
  rewrite (Mult.mult_minus_distr_r n n0 _).
  intros v e e0. rewrite (UIP_refl _ _ e).
  fold (transport (cat_vect (take_vect (n0 * pi s) v p_order) (drop_vect (n0 * pi s) v p_order)) e0).
  pattern v at 1.
  rewrite (take_drop_cat_vect (n0 * pi s) v p_order).
  generalize (le_plus_minus_r (n0 * pi s) (n * pi s) p_order)
             (cat_vect (take_vect (n0 * pi s) v p_order) (drop_vect (n0 * pi s) v p_order)).
  generalize dependent e0.
  rewrite <- (Mult.mult_minus_distr_r n n0 (pi s)).
  rewrite <- (Mult.mult_plus_distr_r n0 (n - n0) (pi s)).
  intros e0 e1 v0. unfold transport.
  rewrite (UIP_refl _ _ e0).
  fold (transport v0 e1).
  generalize dependent v0. generalize dependent e1.
  unfold add_hd_shapes. simpl.
  rewrite (le_plus_minus_r n0 n le_n_hdshape).
  intros e1 v0 e2. rewrite (UIP_refl _ _ e2).
  unfold transport.
  rewrite (UIP_refl _ _ e1).
  reflexivity.
Qed.

(* Additional utils *)

From Equations Require Import Equations.
Set Equations Transparent.
Equations get_axis_size {dim : nat} (s : shape dim) (axis : Fin.t dim) : nat :=
  get_axis_size (scons n s') F1 := n ;
  get_axis_size (scons n s') (FS axis') := get_axis_size s' axis' ;
  get_axis_size snil _ := _.
Next Obligation. dependent destruction axis. Defined.

(* This is an alternate representation for vectors using Sigma Types.
   It turns out that previous definitions were more complicated to prove when
   using Sigma Types. This will be unified/improved.
*)
Definition SigmaVec t n := {l : list t | length l = n}.

Definition sigma_map {A B : Type} {n : nat} (f : A -> B) (sv : SigmaVec A n)
    : SigmaVec B n :=
  let (l, length_l_is_n) := sv in
  exist _ (map f l) (eq_trans (map_length f l) length_l_is_n).

Program Fixpoint indexing_range (bound : nat) : SigmaVec (Fin.t bound) bound :=
  (fix indexing_range_aux (counter : nat) (le_counter_bound : counter <= bound)
      : SigmaVec (Fin.t bound) counter :=
    match counter with
      | O => exist _ nil _
      | S counter' => exist _ (` (indexing_range_aux counter' (le_Sn_le _ _ le_counter_bound)) ++
                              ((Fin.of_nat_lt (p:=counter') _) :: nil)) _
    end) bound (le_refl bound).
Next Obligation.
  generalize (indexing_range_aux counter' (le_Sn_le counter' bound le_counter_bound)).
  intro sigma_sublist.
  destruct sigma_sublist as [l eq_length_l_counter'].
  rewrite app_length. simpl.
  rewrite Nat.add_comm.
  rewrite eq_length_l_counter'.
  reflexivity.
Defined. (* Interestingly, Qed fails here? *)


Program Definition split_slices {dim : nat} {s : shape (S dim)} (a : array s)
    : SigmaVec (array (tl_shape s)) (hd_shape s) :=
  let idxs := indexing_range (hd_shape s) in
  exist _ (map (fun idx => psi idx a) (` idxs)) (proj2_sig idxs).
Next Obligation. rewrite map_length. reflexivity. Qed.

Program Fixpoint join_slices {dim length : nat} {s : shape dim}
    (slices : SigmaVec (array s) length) : array (scons length s) :=
  match slices with
    | nil => mkarr (scons O s) vnil
    | slice_O :: slices' => cat (expand_dim_O slice_O) (join_slices (length:=_) slices') _
  end.
Next Obligation. (* scons 0 s = scons length s *)
  destruct slices as [l eq_length_O]. simpl in Heq_slices.
  rewrite <- Heq_slices in eq_length_O. simpl in eq_length_O.
  rewrite <- eq_length_O. reflexivity.
Qed.
Next Obligation. (* set length of join_slices in inductive case *)
  destruct slices as [l eq_length_l_length]. simpl in Heq_slices.
  rewrite <- Heq_slices in eq_length_l_length. simpl in eq_length_l_length.
  destruct length as [|l'].
    (* length = 0 *)
    - discriminate.
    (* length = S l' *)
    - apply l'.
Defined.
Next Obligation. (* Datatypes.length slices' = join_slices_obligation_2 dim length s slices slice_O slices' Heq_anonymous *)
  destruct slices as [l eq_length_l_length]. simpl in Heq_slices.
  generalize dependent length. rewrite <- Heq_slices. simpl.
  unfold eq_ind_r. unfold eq_ind. simpl.
  intros. rewrite <- eq_length_l_length. reflexivity.
Defined.
Next Obligation. (* tl_shape (expand_dim_shape s 0 (expand_dim_O_obligation_1 dim)) = s *)
  destruct s as [|dim' s_O s'].
    (* s = snil *)
    - simpl. reflexivity.
    (* s = scons s_O s' *)
    - simpl. reflexivity.
Defined.
Next Obligation.
  (* add_hd_shapes (expand_dim_shape s 0 (expand_dim_O_obligation_1 dim))
       (scons (join_slices_obligation_2 dim length s slices slice_O slices' Heq_slices) s)
       (join_slices_obligation_4 dim length s slices slice_O slices' Heq_slices) = scons length s *)
  destruct slices as [l eq_length_l_length]. simpl in Heq_slices.
  unfold join_slices_obligation_2. unfold eq_ind_r. unfold eq_ind.
  generalize dependent length.
  unfold add_hd_shapes. simpl.
  destruct length as [|length'].
    (* length = O *)
    - rewrite <- Heq_slices. intros. discriminate.
    (* length = S length' *)
    - intros. destruct s as [|dim' s_O s'].
      (* s = snil *)
      * reflexivity.
      (* s = scons s_O s' *)
      * reflexivity.
Defined.

Program Definition rot0_right {dim : nat} {s : shape (S dim)} (o : nat)
      (a : array s) (le_o_hdshape : o <= hd_shape s)
    : array s :=
  cat (take_neg o a le_o_hdshape) (drop_neg o a le_o_hdshape) eq_refl.
Next Obligation. (* add_hd_shapes (take_shape o s le_o_hdshape) (drop_shape o s le_o_hdshape) eq_refl = s *)
  dependent destruction s.
  unfold take_shape. unfold drop_shape. unfold add_hd_shapes.
  unfold hd_shape. unfold tl_shape.
  unfold hd_shape in le_o_hdshape.
  rewrite <- (le_plus_minus _ _ le_o_hdshape).
  reflexivity.
Qed.

Program Fixpoint roti_right {dim : nat} {s : shape (S dim)} (axis : Fin.t (S dim)) (o : nat)
    (a : array s) (le_o_axis_size : o <= get_axis_size s axis) {struct dim} : array s :=
  (match dim as mdim return dim = mdim -> _ with
    | O => fun ddim => rot0_right o _ _
    | S dim' => fun ddim => (fun recursive_call => let res_arr := (_ : array _) in
        (* res_arr = join_slices (exist _ (map (fun arr => roti_right axis' o arr _) (` (split_slices _))) _) *)
        transport res_arr (eq_sym (hd_tl_id _ s)) (* TODO *)) (roti_right (dim:=dim') (s:=tl_shape s))
   end) eq_refl.
Next Obligation. (* o <= hd_shape s *)
  dependent destruction s. simpl.
  dependent destruction axis.
    (* axis = F1 *)
    * apply le_o_axis_size.
    (* axis = FS axis *)
    * apply (case0 _ axis). (* absurd *)
Defined.
Next Obligation. (* array (scons (hd_shape s) (tl_shape s)) *)
  (* get axis in (t (S dim')) *)
  dependent destruction axis.
    (* axis = F1, in this case we rotate on the 0th axis *)
    * dependent destruction s. apply (rot0_right o a le_o_axis_size).
    (* axis = FS axis, in this case we perform the recursive call *)
    * dependent destruction s. specialize (recursive_call axis o).
      (* 1. slice a along the first axis *)
      pose proof (split_slices a) as slices.
      (* 2. perform recursive call *)
      pose proof (sigma_map (fun arr => recursive_call arr le_o_axis_size) slices)
      as rotated_slices.
      (* 3. join the obtained slices *)
      apply (join_slices rotated_slices).
Defined.

Program Definition roti_left {dim : nat} {s : shape (S dim)} (axis : Fin.t (S dim)) (o : nat)
    (a : array s) (le_o_axis_size : o <= get_axis_size s axis) : array s :=
  roti_right axis (get_axis_size s axis - o) a _.
Next Obligation. (* get_axis_size s axis - o <= get_axis_size s axis *)
  apply Nat.le_sub_l.
Defined.

(* Content from the paper *)

(* The definitions below are implemented from the text of the paper at <> *)

(* 5.1 *)

(* Definition 2 *)

(* For our purposes, we need to define a new type of arrays ("sliceannarray"s) that carry shape information of
   one of their slices. To use our previously defined operations, we also define two projection functions:
    - innerarray, that returns the annotated array slice
    - outerarray, that returns the whole array stripped of its additional inner shape information
*)

(* TODO: use Fin? Annoying because want ordering... *)
Inductive sliceanndim (bound : nat) : Type :=
  sadim (abeg : nat) (aend : nat) : abeg <= aend -> aend <= bound -> sliceanndim bound.

Inductive sliceannshape : nat -> Type :=
  | sasnil : sliceannshape O
  | sascons {dim} {bound : nat} : sliceanndim bound -> sliceannshape dim -> sliceannshape (S dim).

Definition sliceanndimbound {bound : nat} (sad : sliceanndim bound) : nat := bound.
Definition sliceanndimbeg {bound : nat} (sad : sliceanndim bound) : nat :=
  let (abeg, _, _, _) := sad in abeg.
Definition sliceanndimend {bound : nat} (sad : sliceanndim bound) : nat :=
  let (_, aend, _, _) := sad in aend.

Definition hd_sliceannshapebeg {dim} (sas : sliceannshape (S dim)) : nat :=
  match sas with | sascons sd_O _ => sliceanndimbeg sd_O end.
Definition hd_sliceannshapeend {dim} (sas : sliceannshape (S dim)) : nat :=
  match sas with | sascons sd_O _ => sliceanndimend sd_O end.
Definition hd_sliceannshapebound {dim} (sas : sliceannshape (S dim)) : nat :=
  match sas with | sascons sd_O _ => sliceanndimbound sd_O end.
Program Definition hd_sliceannshape {dim} (sas : sliceannshape (S dim))
    : sliceanndim (hd_sliceannshapebound sas) :=
  (match sas as msas in sliceannshape sdim return forall (ddim : sdim = S dim), sas = transport msas ddim -> _ with
    | sasnil => _ (* absurd *) | sascons sd_O _ => fun ddim dsas => transport sd_O _
   end) eq_refl eq_refl.

Definition tl_sliceannshape {dim} (sas : sliceannshape (S dim)) : sliceannshape dim :=
  match sas with | sascons _ sas' => sas' end.

Fixpoint outershape {dim : nat} (sas : sliceannshape dim) : shape dim :=
  match sas with | sasnil => snil
                 | sascons anndim subannshape => scons (sliceanndimbound anndim) (outershape subannshape) end.

Fixpoint innershape {dim : nat} (sas : sliceannshape dim) : shape dim :=
  match sas with | sasnil => snil
                 | sascons anndim subannshape => scons (sliceanndimend anndim - sliceanndimbeg anndim)
                                                       (innershape subannshape) end.

Lemma pi_S_hd_shape_end {dim : nat} (sas : sliceannshape (S dim)) :
  0 < pi (innershape sas) -> 0 < hd_sliceannshapeend sas.
Proof.
  dependent destruction sas.
  destruct s. simpl.
  destruct aend.
  - simpl. apply iff_refl.
  - intro H. apply Nat.lt_0_succ.
Qed.

Lemma pi_S_hd_shape {dim : nat} (sas : sliceannshape (S dim)) :
  0 < pi (innershape sas) -> 0 < hd_sliceannshapeend sas - hd_sliceannshapebeg sas.
Proof.
  dependent destruction sas.
  destruct s. simpl.
  destruct (aend - abeg).
  - simpl. apply iff_refl.
  - intro. apply Nat.lt_0_succ.
Qed.

Inductive sliceannarray {dim : nat} (sas : sliceannshape dim) : Type :=
  mksaarr : vect (pi (outershape sas)) -> sliceannarray sas.

Definition outerarray {dim} {sas : sliceannshape dim} (saa : sliceannarray sas)
    : array (outershape sas) := let (v) := saa in mkarr (outershape sas) v.

(* preliminaries utils *)
Program Definition inc_sliceanndimbound {bound : nat} (sd : sliceanndim bound) : sliceanndim (S bound) :=
  let (abeg, aend, pbegend, pendbound) := sd in sadim (S bound) abeg aend _ _.

Program Definition carve_sliceanndimbound_left {bound : nat} (sd : sliceanndim bound)
    : sliceanndim (bound - sliceanndimbeg sd) :=
  let abeg := sliceanndimbeg sd in
  let aend := sliceanndimend sd in sadim (bound - abeg) O (aend - abeg) _ _.
Next Obligation. (* 0 <= sliceanndimend sd - sliceanndimbeg sd *)
  apply Nat.le_0_l.
Defined.
Next Obligation. (* sliceanndimend sd - sliceanndimbeg sd <= bound - sliceanndimbeg sd *)
  apply Nat.sub_le_mono_r.
  destruct sd as [abeg aend pbeg pend].
  apply pend.
Defined.

Program Definition carve_sliceanndimbound_right {bound : nat} (sd : sliceanndim bound)
    : sliceanndim (sliceanndimend sd) :=
  let abeg := sliceanndimbeg sd in
  let aend := sliceanndimend sd in sadim aend abeg aend _ _.
Next Obligation. (* sliceanndimbeg sd <= sliceanndimend sd *)
  destruct sd as [abeg aend pbeg pend].
  apply pbeg.
Defined.

Program Fixpoint get_sliceanndimbound {dim} (sas : sliceannshape dim) (i : nat)
    (p : i < dim) : nat :=
  match sas with | sasnil => _ (* absurd *)
                 | sascons sd_O sas' => match i with | O => sliceanndimbound sd_O
                                                     | S i' => get_sliceanndimbound sas' i' (le_S_n _ _ p) end end.
Next Obligation. exfalso. apply (Nat.nlt_0_r _ p). Defined.

Program Fixpoint get_sliceanndim {dim} (sas : sliceannshape dim) (i : nat) (p : i < dim)
    : sliceanndim (get_sliceanndimbound sas i p) :=
  match sas with | sasnil => _ (* absurd *)
                 | sascons sd_O sas' => match i with | O => sd_O
                                                     | S i' => get_sliceanndim sas' i' (le_S_n _ _ p) end end.
Next Obligation. exfalso. apply (Nat.nlt_0_r _ p). Defined.
Next Obligation. (* wildcard'0 = get_sliceanndimbound sas 0 p *)
  simpl_one_JMeq. rewrite <- Heq_sas.
  simpl. unfold sliceanndimbound.
  reflexivity.
Defined.
Next Obligation.
  simpl_one_JMeq. rewrite <- Heq_sas.
  simpl. reflexivity.
Defined.

Program Fixpoint set_sliceanndim {dim bound} (sas : sliceannshape dim) (i : nat) (p : i < dim)
    (sd_new : sliceanndim bound) : sliceannshape dim :=
  match sas with
   | sasnil => _ (* absurd *)
   | sascons sd_O sas' => match i with
      | O => sascons sd_new sas'
      | S i' => sascons sd_O (set_sliceanndim sas' i' (le_S_n _ _ p) sd_new) end end.
Next Obligation. exfalso. apply (Nat.nlt_0_r _ p). Defined.

Definition carve_sliceanndimbound {bound : nat} (sd : sliceanndim bound)
    : sliceanndim (sliceanndimend sd - sliceanndimbeg sd) :=
  carve_sliceanndimbound_right (carve_sliceanndimbound_left sd).

Definition inc_sliceannshapedim {dim} (sas : sliceannshape dim) (i : nat) (p : i < dim) : sliceannshape dim :=
  set_sliceanndim sas i p (inc_sliceanndimbound (get_sliceanndim sas i p)).

Lemma innershape_id_inc_sliceannshapedim :
  forall {dim} (sas : sliceannshape dim) (axis : nat) (axis_lt_dim : axis < dim),
    innershape (inc_sliceannshapedim sas axis axis_lt_dim) = innershape sas.
Proof.
  intros. generalize dependent dim. induction axis as [|axis'].
    (* axis = 0 *)
    - intros. destruct sas as [|dim' bound sd_O sas'].
      + (* absurd *) exfalso. apply (Nat.nlt_0_r _ axis_lt_dim).
      + simpl. generalize (eq_ind (sascons sd_O sas')
              (fun sas : sliceannshape (S dim') => bound = get_sliceanndimbound sas 0 axis_lt_dim) eq_refl
              (sascons sd_O sas') (JMeq_eq JMeq_refl)).
        destruct sd_O as [abeg aend pbeg pend]. unfold get_sliceanndimbound. unfold sliceanndimbound.
        intro e. rewrite (proof_irrelevance _ _ eq_refl). simpl.
        reflexivity.
    (* axis = S axis' *)
    - intros. destruct dim as [|dim'].
      (* dim = 0 *)
      + (* absurd *) exfalso. apply (Nat.nlt_0_r _ axis_lt_dim).
      + dependent destruction sas. simpl.
        generalize (eq_ind (sascons s sas)
                 (fun sas0 : sliceannshape (S dim') =>
                  get_sliceanndimbound sas axis' (le_S_n (S axis') dim' axis_lt_dim) =
                  get_sliceanndimbound sas0 (S axis') axis_lt_dim) eq_refl (sascons s sas) 
                 (JMeq_eq JMeq_refl)).
        simpl. intro e. rewrite (proof_irrelevance _ _ eq_refl). simpl. clear e.
        specialize (IHaxis' dim' sas (le_S_n _ _ axis_lt_dim)). simpl.
        fold (inc_sliceannshapedim sas axis' (le_S_n (S axis') dim' axis_lt_dim)).
        rewrite <- IHaxis'. reflexivity.
Qed.

Program Fixpoint inc_sliceannshapedim_n {dim} (s : sliceannshape dim) (i : nat)
    (n : nat) (p : i < dim) : sliceannshape dim :=
  match n with
    | O => s
    | S n' => (inc_sliceannshapedim (inc_sliceannshapedim_n s i n' _) i p)
  end.

Lemma innershape_id_inc_sliceannshapedim_n :
  forall {dim} {sas : sliceannshape dim} (axis : nat) (n : nat) (axis_lt_dim : axis < dim),
    innershape (inc_sliceannshapedim_n sas axis n axis_lt_dim) = innershape sas.
Proof.
  intros. generalize dependent dim. generalize dependent axis. induction n as [|n'].
    (* n = 0 *)
    - intros. reflexivity.
    (* n = S n' *)
    - intros. destruct dim as [|dim'].
      (* dim = 0 *)
      + (* absurd *) exfalso. apply (Nat.nlt_0_r _ axis_lt_dim).
      (* dim = S dim' *)
      + specialize (IHn' axis (S dim') sas axis_lt_dim).
        unfold inc_sliceannshapedim_n.
        Set Printing All.
        rewrite (proof_irrelevance _ (inc_sliceannshapedim_n_obligation_1 (S dim') axis axis_lt_dim) axis_lt_dim).
        fold (inc_sliceannshapedim_n sas axis n' axis_lt_dim).
        rewrite innershape_id_inc_sliceannshapedim.
        apply IHn'.
Qed.

Program Fixpoint carve_sliceannshapedim_left {dim} (sas : sliceannshape dim) (i : nat) (p : i < dim)
    : sliceannshape dim :=
  match sas with
    | sasnil => sas
    | sascons sd_O sas' =>
    match i with
      | O => sascons (carve_sliceanndimbound_left sd_O) sas'
      | S i' => sascons sd_O (carve_sliceannshapedim_left sas' i' _)
    end
  end.
Next Obligation. apply (Le.le_S_n _ _ p). Qed.

Program Fixpoint carve_sliceannshapedim_right {dim} (sas : sliceannshape dim) (i : nat) (p : i < dim)
    : sliceannshape dim :=
  match sas with
    | sasnil => sas
    | sascons sd_O sas' =>
    match i with
      | O => sascons (carve_sliceanndimbound_right sd_O) sas'
      | S i' => sascons sd_O (carve_sliceannshapedim_right sas' i' _)
    end
  end.
Next Obligation. apply (Le.le_S_n _ _ p). Defined.

Definition carve_sliceannshapedim {dim} (sas : sliceannshape dim) (i : nat) (p : i < dim)
    : sliceannshape dim :=
  carve_sliceannshapedim_right (carve_sliceannshapedim_left sas i p) i p.

(* Definition 2, rho' *)
Definition rho' {dim} {sas : sliceannshape dim} (saa : sliceannarray sas) : sliceannshape dim := sas.

(* By default, as stated in definition 2, we assume that each axis i of a shape without annotation in an array
   implicitly carries an annotation b_i = 0 and e_i = s_i, where s_i is the coefficient of the shape at index i.
   This gives rise to the following conversion functions from unannotated shapes to annotated shapes, and thus
   from arrays to annotated arrays:
*)
Program Fixpoint to_sliceannshape {dim : nat} (s : shape dim) : sliceannshape dim :=
  match s with | snil => sasnil
               | scons s_i subshape => sascons (sadim s_i 0 s_i _ _) (to_sliceannshape subshape) end.
Next Obligation. (* 0 <= s_i *) apply Nat.le_0_l. Qed.
Solve All Obligations.

(* more utils *)
Program Fixpoint carve_array_axis_right {dim} {sas : sliceannshape dim} (a : array (outershape sas))
    (i : nat) (pf : i < dim) {struct i} : array (outershape (carve_sliceannshapedim_right sas i pf)) :=
  (match i as mi, sas as msas in sliceannshape sdim
        return forall (ddim : sdim = dim), i = mi
                                        -> sas = transport msas ddim
                                        -> array (outershape (carve_sliceannshapedim_right sas i pf)) with
    | O, @sascons idim bound sad sas' => fun ddim di dsas => _
        (* (1) take (sliceanndimend sad) _(*=a*) _ *)
    | S i', @sascons idim bound sad sas' => fun ddim di dsas =>
        let sigma_map_fn := sigma_map (n:=bound) (fun arr => carve_array_axis_right (dim:=pred dim) (sas:=sas') arr i' _) in
        (fun map_fn => _) sigma_map_fn
        (* (2) join_slices (mapvect (fun arr => carve_array_axis_right arr _ _) (split_slices a)) *)
    | _, _ => _ (* can not happen *)
  end) eq_refl eq_refl eq_refl.
Next Obligation. (* array (scons (sliceanndimbound (carve_sliceanndimbound_right sad)) (outershape sas')) *)
  destruct sad as [abeg aend pbeg pend].
  (* 1. get rid of the padding *)
  pose proof (take aend a pend) as a_no_rpad.
  (* 2. fix types *)
  unfold sliceanndimbound. simpl.
  unfold sliceanndimbound in a_no_rpad.
  unfold take_shape in a_no_rpad.
  unfold drop_shape in a_no_rpad.
  simpl in a_no_rpad.
  apply a_no_rpad.
Defined.
Next Obligation. apply (le_S_n _ _ pf). Defined.
Next Obligation. (* array
  (scons (sliceanndimbound sad)
     (outershape
        (carve_sliceannshapedim_right sas' i'
           (carve_sliceannshapedim_right_obligation_2 (S idim) (sascons sad sas') (S i') pf idim bound sad sas'
              eq_refl JMeq_refl i' eq_refl)))) *)
  destruct sad.
  assert (aend <= hd_shape (outershape (sascons (sadim bound abeg aend l l0) sas'))) as ord1.
    * unfold hd_shape. unfold outershape. unfold sliceanndimbound. apply l0.
    * assert (abeg <= hd_shape (take_shape aend (outershape (sascons (sadim bound abeg aend l l0) sas')) ord1)) as ord2.
        - unfold hd_shape. unfold take_shape. apply l.
          (* slices : SigmaVec (@array idim (@outershape idim sas')) (@sliceanndimbound bound (sadim bound abeg aend l l0)) *)
        - pose proof (split_slices a) as slices. simpl in slices.
          (* carved_subarrays : SigmaVec _ _ *)
          pose proof map_fn slices as carved_subarrays.
          pose proof (join_slices carved_subarrays) as final_array.
          unfold sliceanndimbound.
          rewrite (proof_irrelevance _ _
                     (carve_array_axis_right_obligation_5 (S idim)
                            (sascons (sadim bound abeg aend l l0) sas') a (S i') pf i' idim bound
                            (sadim bound abeg aend l l0) sas' eq_refl eq_refl eq_refl)).
          apply final_array.
Defined.

Program Fixpoint carve_array_axis_left {dim} {sas : sliceannshape dim} (a : array (outershape sas))
    (i : nat) (pf : i < dim) {struct i} : array (outershape (carve_sliceannshapedim_left sas i pf)) :=
  (match i as mi, sas as msas in sliceannshape sdim
        return forall (ddim : sdim = dim), i = mi
                                        -> sas = transport msas ddim
                                        -> array (outershape (carve_sliceannshapedim_left sas i pf)) with
    | O, @sascons idim bound sad sas' => fun ddim di dsas => _
        (* (1) drop (sliceanndimbeg sad) _(*=a*) _ *)
    | S i', @sascons idim bound sad sas' => fun ddim di dsas =>
        let sigma_map_fn := sigma_map (n:=bound) (fun arr => carve_array_axis_left (dim:=pred dim) (sas:=sas') arr i' _) in
        (fun map_fn => _) sigma_map_fn
        (* (2) join_slices (mapvect (fun arr => carve_array_axis_left arr _ _) (split_slices a)) *)
    | _, _ => _ (* can not happen *)
  end) eq_refl eq_refl eq_refl.
Next Obligation. (* array (scons (sliceanndimbound (carve_sliceanndimbound_left sad)) (outershape sas')) *)
  destruct sad as [abeg aend pbeg pend].
  (* 1. get rid of the padding *)
  pose proof (drop abeg a (Nat.le_trans _ _ _ pbeg pend)) as a_no_lpad.
  (* 2. fix types *)
  unfold sliceanndimbound. simpl.
  unfold sliceanndimbound in a_no_lpad.
  unfold take_shape in a_no_lpad.
  unfold drop_shape in a_no_lpad.
  simpl in a_no_lpad.
  apply a_no_lpad.
Defined.
Next Obligation. apply (le_S_n _ _ pf). Defined.
Next Obligation. (* array
  (scons (sliceanndimbound sad)
     (outershape
        (carve_sliceannshapedim_left sas' i'
           (carve_sliceannshapedim_left_obligation_2 (S idim) (sascons sad sas') (S i') pf idim bound sad sas'
              eq_refl JMeq_refl i' eq_refl)))) *)
  destruct sad.
  assert (aend <= hd_shape (outershape (sascons (sadim bound abeg aend l l0) sas'))) as ord1.
    * unfold hd_shape. unfold outershape. unfold sliceanndimbound. apply l0.
    * assert (abeg <= hd_shape (take_shape aend (outershape (sascons (sadim bound abeg aend l l0) sas')) ord1)) as ord2.
        - unfold hd_shape. unfold take_shape. apply l.
          (* slices : SigmaVec (@array idim (@outershape idim sas')) (@sliceanndimbound bound (sadim bound abeg aend l l0)) *)
        - pose proof (split_slices a) as slices. simpl in slices.
          (* carved_subarrays : SigmaVec _ _ *)
          pose proof map_fn slices as carved_subarrays.
          pose proof (join_slices carved_subarrays) as final_array.
          unfold sliceanndimbound.
          rewrite (proof_irrelevance _ _
                     (carve_array_axis_left_obligation_5 (S idim)
                            (sascons (sadim bound abeg aend l l0) sas') a (S i') pf i' idim bound
                            (sadim bound abeg aend l l0) sas' eq_refl eq_refl eq_refl)).
          apply final_array.
Defined.

Definition carve_array_axis {dim} {sas : sliceannshape dim} (a : array (outershape sas))
    (i : nat) (pf : i < dim) : array (outershape (carve_sliceannshapedim sas i pf)) :=
  carve_array_axis_right (carve_array_axis_left a i pf) i pf.

Program Fixpoint carve_array {dim} (sas : sliceannshape dim) (a : array (outershape sas))
    {struct sas} : array (innershape sas) :=
  (match sas as msas in sliceannshape sdim return forall (ddim : sdim = dim), sas = transport msas ddim -> _ with
      | sasnil => fun _ _ => _ (* (1) a *)
      | @sascons idim bound sad sas' => fun ddim dsas =>
          let sigma_map_fn := sigma_map (n:=sliceanndimend sad - sliceanndimbeg sad) (fun arr => carve_array sas' arr) in
          (fun map_fn => _) sigma_map_fn (*
         (2) let inner_array := drop (sliceanndimbeg sad) (take (sliceanndimend sad) a _) _ in
          join_slices (map_fn (split_slices inner_array)) *)
  end) eq_refl eq_refl.
Next Obligation.
  destruct sad. simpl.
  assert (aend <= hd_shape (outershape (sascons (sadim bound abeg aend l l0) sas'))) as ord1.
    * unfold hd_shape. unfold outershape. unfold sliceanndimbound. apply l0.
    * pose proof (take aend a ord1) as slice1.
      assert (abeg <= hd_shape (take_shape aend (outershape (sascons (sadim bound abeg aend l l0) sas')) ord1)) as ord2.
        - unfold hd_shape. unfold take_shape. apply l.
          (* inner_array = drop abeg (take aend a) *)
        - pose proof (drop abeg slice1 ord2) as inner_array. simpl in inner_array.
          (* slices : SigmaVec (@array idim (@outershape idim sas')) (Init.Nat.sub aend abeg) *)
          pose proof (split_slices inner_array) as slices. simpl in slices.
          (* carved_subarrays : @vect (@array et idim (@innershape idim sas')) (Init.Nat.sub aend abeg) *)
          pose proof (map_fn slices) as carved_subarrays.
          pose proof (join_slices (length:=aend - abeg) carved_subarrays) as carved_array.
          apply carved_array.
Qed.
Solve All Obligations.

Program Definition to_sliceannarray {dim} {s : shape dim} (a : array s)
    : sliceannarray (to_sliceannshape s) :=
  mksaarr (to_sliceannshape (rho a)) (elems a).
Next Obligation. unfold rho. induction s.
  - simpl. reflexivity.
  - simpl. unfold sliceanndimbound.
    destruct n.
      * simpl. reflexivity.
      * pose proof (Nat.le_0_l n) as order_n.
        apply Le.le_n_S in order_n.
        pose proof (take 1 a order_n) as slice_a.
        unfold take_shape in slice_a. simpl in slice_a.
        pose proof (reshape slice_a s) as sub_a. simpl in sub_a.
        rewrite Nat.add_0_r in sub_a.
        apply IHs in sub_a.
        ** rewrite sub_a. reflexivity.
        ** apply eq_refl.
Qed.
Solve All Obligations.

(* Definition 3, padl and padr *) (* TODO: rename cpadl/cpadr for circular? *)

Program Fixpoint psi_slice {dim} {sas : sliceannshape (S dim)} (i : Fin.t (hd_sliceannshapebound sas))
    (saa : sliceannarray sas)
    : sliceannarray (tl_sliceannshape sas) :=
  let subarray := psi i (outerarray saa) in mksaarr _ (elems subarray).
Next Obligation. (* hd_sliceannshapebound sas = hd_shape (outershape sas) *)
  dependent destruction sas. simpl. reflexivity.
Defined.
Next Obligation. (* pi (tl_shape (outershape sas)) = pi (outershape (tl_sliceannshape sas)) *)
  dependent destruction sas. simpl. reflexivity.
Defined.
Solve All Obligations.

Program Fixpoint cpadrO {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas)
  (pf : 0 < pi (innershape sas))
    : sliceannarray (inc_sliceannshapedim sas O (Nat.lt_0_succ dim)) :=
  (match sas as msas in sliceannshape sdim return forall (ddim : sdim = S dim), sas = transport msas ddim -> _  with
      | sasnil => fun _ _ => _ (* absurd case *)
      | sascons sd_O sas' => fun ddim dsas => let a_O_unlpadded := carve_array_axis_left (outerarray saa) O _ in
    let pad_element := psi (Fin.of_nat_lt (p:=sliceanndimbound sd_O - sliceanndimend sd_O) _) a_O_unlpadded in
    mksaarr _ (elems (cat (outerarray saa) (reshape pad_element (expand_dim_shape (rho pad_element) O _) _) _))
  end) eq_refl eq_refl.
Next Obligation. (* 0 < S dim *) apply Nat.lt_0_succ. Defined.
Next Obligation.
  (* sliceanndimbound sd_O - sliceanndimend sd_O < hd_shape
  (outershape (carve_shape_axis s 0 (cpadrO_obligation_2 dim s wildcard' wildcard'0 sd_O s' Heq_anonymous Heq_s))) *)
  (*unfold hd_shape. unfold outershape. *)
  pose proof (pi_S_hd_shape _ pf) as hd_gt_O. Check pi_S_hd_shape.
  unfold cpadrO_obligation_2.
  unfold eq_ind_r. unfold eq_ind. simpl.
  simpl in hd_gt_O.
  dependent destruction sd_O. unfold sliceanndimbound. simpl.
  simpl in hd_gt_O.
  apply (plus_lt_compat_r _ _ abeg) in hd_gt_O. simpl in hd_gt_O.
  rewrite (Nat.sub_add _ _ l) in hd_gt_O.
  destruct aend as [|aend'].
    (* aend = O *)
    - exfalso. apply (Nat.nlt_0_r _ hd_gt_O).
    (* aend = S aend' *)
    - unfold lt. rewrite <- (Nat.sub_succ_l _ _ l0). simpl.
      unfold lt in hd_gt_O. apply le_S_n in hd_gt_O.
      apply (Nat.sub_le_mono_l _ _ _ hd_gt_O).
Defined.
Next Obligation. (* 0 <= dim *) apply Nat.le_0_l. Defined.
Next Obligation. (* pi (outershape sas') = pi (expand_dim_shape (outershape sas') 0 _)*)
  unfold rho.
  symmetry. apply pi_expand_s_pi_s.
Defined.
Next Obligation. (* tl_shape (outershape sas) = tl_shape (expand_dim_shape (psi O sas)) *)
  destruct sas'.
    - simpl. reflexivity.
    - simpl. reflexivity.
Defined.
Next Obligation. (*
    (n0 + 1) * (sliceanndimbound s * pi (outershape sas'))
  = sliceanndimbound s * pi (outershape sas') + n0 * (sliceanndimbound s * pi (outershape sas'))
  with n0 = sliceanndimbound hd_shape sas *)
  unfold rho.
  destruct sd_O.
  unfold sliceanndimbound.
  destruct sas'.
    - simpl.
      rewrite Nat.mul_1_r. rewrite Nat.mul_1_r.
      rewrite Nat.add_comm.
      reflexivity.
    - simpl.
      pattern (sliceanndimbound s * pi (outershape sas')) at 2.
      rewrite <- Nat.mul_1_l.
      unfold sliceanndimbound.
      rewrite (Nat.add_comm n0 1).
      rewrite <- Nat.mul_add_distr_r.
      reflexivity.
Defined.

Program Definition split_slices_saa {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas)
    : SigmaVec (sliceannarray (tl_sliceannshape sas)) (hd_sliceannshapebound sas) :=
  let subshape := tl_sliceannshape sas in
  let subarrays := split_slices (outerarray saa) in
    (fun subarrays => sigma_map (fun arr => mksaarr subshape (elems arr)) _(*= subarrays*)) subarrays.
Next Obligation. (* SigmaVec (array (outershape (tl_sliceannshape sas))) (hd_sliceannshapebound sas) *)
  dependent destruction sas. simpl. simpl in subarrays.
  apply subarrays.
Defined.
Solve All Obligations.

Program Fixpoint cpadr {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas) (axis : nat)
  (axis_lt_sdim : axis < S dim) (pi_gt_O : 0 < pi (innershape sas)) {struct axis}
    : sliceannarray (inc_sliceannshapedim sas axis axis_lt_sdim) :=
  let result_shape := inc_sliceannshapedim sas axis axis_lt_sdim in
  (match axis as maxis, sas as msas in sliceannshape sdim
         return forall (ddim : sdim = S dim), axis = maxis -> sas = transport msas ddim -> sliceannarray result_shape with
    | _, sasnil => fun _ _ _ => _ (* absurd case *)
    | O, sascons _ _ => fun ddim daxis _ => cpadrO saa pi_gt_O
    | S axis', sascons sd_O sas' => fun ddim daxis dsas =>
        let subsliceannarrays := split_slices_saa saa in
        let sigma_map_fn := sigma_map (n:=sliceanndimbound sd_O) (fun arr => cpadr (dim:=pred dim) (sas:=sas') arr axis' _ _) in
        (fun map_fn subsliceannarrays =>
          mksaarr result_shape _(*=hole*))
          (* hole = elems (join_slices (mapvect (fun subarr => outerarray (cpadr subarr i' _ _)) subarrays)) *)
          sigma_map_fn subsliceannarrays
   end) eq_refl eq_refl eq_refl.
Next Obligation. (*
    inc_sliceannshapedim (transport (sascons s s0) (noConfusion eq_refl)) 0 (Nat.lt_0_succ dim) =
    inc_sliceannshapedim (transport (sascons s s0) (noConfusion eq_refl)) 0 axis_lt_sdim
*)
  rewrite (proof_irrelevance _ (Nat.lt_0_succ dim) axis_lt_sdim). reflexivity.
Defined.
Next Obligation. (* dim = S (Init.Nat.pred dim) *)
  dependent destruction dim.
    (* dim = 0 *)
    - exfalso. apply le_S_n in axis_lt_sdim.  apply (Nat.nle_succ_0 _ axis_lt_sdim).
    (* dim = S dim *)
    - reflexivity.
Defined.
Next Obligation. (* 0 < pi (innershape sas') *)
  clear dependent arr.
  dependent destruction dim.
    (* dim = 0 *)
    - exfalso. apply le_S_n in axis_lt_sdim. apply (Nat.nle_succ_0 _ axis_lt_sdim).
    (* dim = S dim *)
    - simpl. simpl in pi_gt_O. destruct (pi (innershape sas')).
      (* 0 < 0 *)
      * exfalso. rewrite Nat.mul_comm in pi_gt_O. apply (Nat.nlt_0_r _ pi_gt_O).
      (* 0 < S n *)
      * apply Nat.lt_0_succ.
Defined.
Next Obligation. (* axis' < S (Init.Nat.pred dim) *)
  destruct dim as [|dim'].
    (* dim = 0 *)
    - apply (Nat.lt_succ_l _ _ axis_lt_sdim).
    (* dim = S dim' *)
    - simpl. apply (lt_S_n _ _ axis_lt_sdim).
Defined.
Next Obligation. (* vect (pi (outershape (inc_sliceannshapedim (transport (sascons sd_O sas') ddim) (S i') axis_lt_sdim))) *)
  unfold transport in pi_gt_O. simpl in pi_gt_O.
  unfold lt in map_fn.
  destruct dim.
  * pose proof (lt_S_n _ _ axis_lt_sdim) as axis_lt_O. exfalso. apply (Nat.nlt_0_r _ axis_lt_O).
  * pose proof (le_S_n _ _ axis_lt_sdim) as pred_axis_le_sdim.
    assert (0 < pi (innershape sas')) as pi_innershape_gt_O.
    - clear map_fn. apply neq_0_lt. intro pi_is_O.
      rewrite <- pi_is_O in pi_gt_O.
      rewrite Nat.mul_comm in pi_gt_O. simpl in pi_gt_O.
      apply (Nat.nlt_0_r _ pi_gt_O).
    - (* 1. pad subsliceannarrays *)
      pose proof (map_fn
                          subsliceannarrays) as padded_subsliceannarrays.
      (* 2. join slices of the padded sliceannarrays & extract the vector. This is our target. *)
      pose proof (elems (join_slices (sigma_map outerarray padded_subsliceannarrays))) as array_vect.
      simpl in array_vect.
      simpl.
      generalize (eq_ind (sascons sd_O sas')
                    (fun sas : sliceannshape (S (S dim)) =>
                     get_sliceanndimbound sas' axis' (le_S_n (S axis') (S dim) axis_lt_sdim) =
                     get_sliceanndimbound sas (S axis') axis_lt_sdim) eq_refl (sascons sd_O sas')
                    (JMeq_eq JMeq_refl)).
      simpl. intro e. rewrite (proof_irrelevance _ _ eq_refl). clear e. simpl.
      rewrite (proof_irrelevance _ _ pred_axis_le_sdim).
      rewrite (proof_irrelevance _ _ pred_axis_le_sdim) in array_vect.
      apply array_vect.
Defined.

(* We skip cpadl for now, as it is similar to cpadr. We will have to come back to it later *)

(* We do not define exactly the left inverse of cpadr but define instead
   inv_cpadr_all as the function that removes all right padding for a given
   axis. We do this to simplify the definition; this particular definition is
   enough for the proofs of the paper.
*)
Check carve_array_axis.
Program Definition inv_cpadr_allO {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas)
      (pi_gt_O : 0 < pi (innershape sas))
    : sliceannarray (carve_sliceannshapedim_right sas O (Nat.lt_0_succ dim)) :=
  (match sas as msas in sliceannshape sdim return forall (ddim : sdim = S dim), sas = transport msas ddim -> _ with
    | sasnil => fun _ _ => _ (* absurd case *)
    | sascons sd_O sas' => fun ddim dsas => let a_O_unpadded := carve_array_axis_right (outerarray saa) O _ in
    mksaarr _ (elems a_O_unpadded)
   end) eq_refl eq_refl.

Program Fixpoint inv_cpadr_all {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas) (axis : nat)
      (axis_lt_sdim : axis < S dim) (pi_gt_O : 0 < pi (innershape sas)) {struct axis}
    : sliceannarray (carve_sliceannshapedim_right sas axis axis_lt_sdim) :=
  let result_shape := carve_sliceannshapedim_right sas axis axis_lt_sdim in
  (match axis as maxis, sas as msas in sliceannshape sdim
         return forall (ddim : sdim = S dim), axis = maxis -> sas = transport msas ddim -> sliceannarray result_shape with
    | _, sasnil => fun _ _ _ => _ (* absurd case *)
    | O, sascons _ _ => fun ddim daxis _ => inv_cpadr_allO saa pi_gt_O
    | S axis', sascons sd_O sas' => fun ddim daxis dsas =>
        let subsliceannarrays := split_slices_saa saa in
        let sigma_map_fn := sigma_map (n:=sliceanndimbound sd_O) (fun arr => inv_cpadr_all (dim:=pred dim) (sas:=sas') arr axis' _ _) in
        (fun map_fn subsliceannarrays =>
          mksaarr result_shape _(*=hole*))
          (* hole = elems (join_slices (mapvect (fun subarr => outerarray (cpadr subarr i' _ _)) subarrays)) *)
          sigma_map_fn subsliceannarrays
   end) eq_refl eq_refl eq_refl.
Next Obligation. (* dim = S (Init.Nat.pred dim) *)
  destruct dim as [|dim'].
    (* dim = 0 *)
    - exfalso. unfold lt in axis_lt_sdim. apply le_S_n in axis_lt_sdim.
      apply (Nat.nle_succ_0 _ axis_lt_sdim).
    (* dim = S dim' *)
    - reflexivity.
Defined.
Next Obligation. (* 0 < pi (innershape sas') *)
  clear dependent arr.
  dependent destruction dim.
    (* dim = 0 *)
    - exfalso. apply le_S_n in axis_lt_sdim. apply (Nat.nle_succ_0 _ axis_lt_sdim).
    (* dim = S dim *)
    - simpl. simpl in pi_gt_O. destruct (pi (innershape sas')).
      (* 0 < 0 *)
      * exfalso. rewrite Nat.mul_comm in pi_gt_O. apply (Nat.nlt_0_r _ pi_gt_O).
      (* 0 < S n *)
      * apply Nat.lt_0_succ.
Defined.
Next Obligation. (* axis' < S (Init.Nat.pred dim) *)
  destruct dim as [|dim'].
    (* dim = 0 *)
    - apply (Nat.lt_succ_l _ _ axis_lt_sdim).
    (* dim = S dim' *)
    - simpl. apply (lt_S_n _ _ axis_lt_sdim).
Defined.
Next Obligation. (* vect (pi
     (outershape
        (carve_sliceannshapedim_right (transport (sascons sd_O sas') (noConfusion eq_refl)) 
           (S axis') axis_lt_sdim))) *)
  unfold transport in pi_gt_O. simpl in pi_gt_O.
  unfold lt in map_fn.
  destruct dim.
  * pose proof (lt_S_n _ _ axis_lt_sdim) as axis_lt_O. exfalso. apply (Nat.nlt_0_r _ axis_lt_O).
  * pose proof (le_S_n _ _ axis_lt_sdim) as pred_axis_le_sdim.
    assert (0 < pi (innershape sas')) as pi_innershape_gt_O.
    - clear map_fn. apply neq_0_lt. intro pi_is_O.
      rewrite <- pi_is_O in pi_gt_O.
      rewrite Nat.mul_comm in pi_gt_O. simpl in pi_gt_O.
      apply (Nat.nlt_0_r _ pi_gt_O).
    - (* 1. unpad subsliceannarrays *)
      pose proof (map_fn subsliceannarrays) as unpadded_subsliceannarrays.
      (* 2. join slices of the unpadded sliceannarrays & extract the vector. This is our target. *)
      pose proof (elems (join_slices (sigma_map outerarray unpadded_subsliceannarrays))) as array_vect.
      simpl in array_vect.
      simpl.
      rewrite (proof_irrelevance _ _ (inv_cpadr_all_obligation_6 (S dim) (sascons sd_O sas') saa 
                           (S axis') axis_lt_sdim pi_gt_O axis' (S dim) H0 sd_O sas' eq_refl eq_refl eq_refl)).
      apply array_vect.
Defined.

(* loop utils *)
Program Fixpoint cpadr_n {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas) (axis : nat)
      (n : nat) (axis_lt_sdim : axis < S dim) (pi_gt_O : 0 < pi (innershape sas)) {struct n}
    : sliceannarray (inc_sliceannshapedim_n sas axis n axis_lt_sdim) :=
  match n with
    | O => saa
    | S n' => cpadr_n (cpadr saa axis axis_lt_sdim pi_gt_O) axis n' axis_lt_sdim _
  end.
Next Obligation. (* 0 < pi (innershape (inc_sliceannshapedim sas axis axis_lt_sdim)) *)
  clear saa.
  rewrite innershape_id_inc_sliceannshapedim.
  apply pi_gt_O.
Defined.
Next Obligation.
  (* inc_sliceannshapedim_n (inc_sliceannshapedim sas axis axis_lt_sdim) axis n' axis_lt_sdim =
inc_sliceannshapedim
  (inc_sliceannshapedim_n sas axis n' (inc_sliceannshapedim_n_obligation_1 (S dim) axis axis_lt_sdim)) axis
  axis_lt_sdim *)
  clear saa.
  rewrite (proof_irrelevance _ (inc_sliceannshapedim_n_obligation_1 (S dim) axis axis_lt_sdim) axis_lt_sdim).
  generalize dependent dim. generalize dependent axis. induction n' as [|n'].
    (* n' = 0 *)
    - reflexivity.
    (* n' = S n' *)
    - intros.
      specialize (IHn' axis dim sas axis_lt_sdim pi_gt_O).
      unfold inc_sliceannshapedim_n.
      rewrite (proof_irrelevance _ (inc_sliceannshapedim_n_obligation_1 (S dim) axis axis_lt_sdim) axis_lt_sdim).
      fold (inc_sliceannshapedim_n sas axis n' axis_lt_sdim).
      fold (inc_sliceannshapedim_n (inc_sliceannshapedim sas axis axis_lt_sdim) axis n').
      rewrite <- IHn'. reflexivity.
Defined.


Lemma carve_sliceannshapedim_right_is_inc_sliceannshapedim_right_inverse :
  forall {dim} (sas : sliceannshape (S dim)) (axis : nat) (axis_lt_sdim : axis < S dim)
               (sas_has_no_rpad : sas = carve_sliceannshapedim_right sas axis axis_lt_sdim),
    sas = carve_sliceannshapedim_right (inc_sliceannshapedim sas axis axis_lt_sdim) axis axis_lt_sdim.
Proof.
  intros.
  pattern sas at 1. rewrite sas_has_no_rpad.
  unfold inc_sliceannshapedim.
  generalize dependent dim.
  induction axis as [|axis' IHaxis'].
    (* axis = O *)
    - intros. dependent destruction sas.
      unfold inc_sliceannshapedim.
      destruct s as [abeg aend pbeg pend].
      unfold set_sliceanndim. simpl.
      generalize (eq_ind (sascons (sadim bound abeg aend pbeg pend) sas)
              (fun sas0 : sliceannshape (S dim) => bound = get_sliceanndimbound sas0 0 axis_lt_sdim) eq_refl
              (sascons (sadim bound abeg aend pbeg pend) sas) (JMeq_eq JMeq_refl)).
      simpl. unfold sliceanndimbound. intro e. rewrite (proof_irrelevance _ _ eq_refl). clear e.
      simpl.
      unfold carve_sliceanndimbound_right. unfold sliceanndimend.
      unfold sliceanndimbeg. rewrite (proof_irrelevance _ _ pbeg).
      rewrite (proof_irrelevance _ _ (le_refl aend)).
      rewrite (proof_irrelevance _ (carve_sliceanndimbound_right_obligation_1 (S bound)
        (sadim (S bound) abeg aend (inc_sliceanndimbound_obligation_1 abeg aend pbeg)
           (inc_sliceanndimbound_obligation_2 bound aend pend))) pbeg).
      rewrite (proof_irrelevance _ (carve_sliceanndimbound_right_obligation_2 (S bound)
        (sadim (S bound) abeg aend (inc_sliceanndimbound_obligation_1 abeg aend pbeg)
           (inc_sliceanndimbound_obligation_2 bound aend pend))) (le_refl aend)).
      reflexivity...
    (* axis = S axis' *)
    - intros. dependent destruction sas. simpl.
      rewrite (proof_irrelevance _ _ (le_S_n _ _ axis_lt_sdim)).
      generalize (eq_ind (sascons s sas)
                    (fun sas0 : sliceannshape (S dim) =>
                     get_sliceanndimbound sas axis' (le_S_n (S axis') dim axis_lt_sdim) =
                     get_sliceanndimbound sas0 (S axis') axis_lt_sdim) eq_refl (sascons s sas)
                    (JMeq_eq JMeq_refl)).
      simpl. intro e. rewrite (proof_irrelevance _ _ eq_refl). clear e. simpl.
      destruct dim as [|dim']. apply f_equal.
        (* dim = O *)
        * exfalso. clear sas_has_no_rpad. apply le_S_n in axis_lt_sdim. apply (Nat.nle_succ_0 _ axis_lt_sdim)...
        (* dim = S dim' *)
        * simpl in sas_has_no_rpad.
          rewrite (proof_irrelevance _ _ (le_S_n _ _ axis_lt_sdim)) in sas_has_no_rpad.
          dependent destruction sas_has_no_rpad.
          specialize (IHaxis' dim' sas(le_S_n _ _ axis_lt_sdim) x).
          f_equal. apply IHaxis'.
Defined.

Lemma carve_pad_surjective :
  forall {dim} (sas : sliceannshape (S dim)) (axis : nat) (axis_lt_sdim : axis < S dim),
    carve_sliceannshapedim_right sas axis axis_lt_sdim =
    carve_sliceannshapedim_right (inc_sliceannshapedim sas axis axis_lt_sdim) axis axis_lt_sdim.
Proof.
  intros.
  unfold inc_sliceannshapedim.
  generalize dependent dim.
  induction axis as [|axis' IHaxis'].
    (* axis = O *)
    - intros. dependent destruction sas.
      unfold inc_sliceannshapedim.
      destruct s as [abeg aend pbeg pend].
      unfold set_sliceanndim. simpl.
      generalize (eq_ind (sascons (sadim bound abeg aend pbeg pend) sas)
              (fun sas0 : sliceannshape (S dim) => bound = get_sliceanndimbound sas0 0 axis_lt_sdim) eq_refl
              (sascons (sadim bound abeg aend pbeg pend) sas) (JMeq_eq JMeq_refl)).
      simpl. unfold sliceanndimbound. intro e. rewrite (proof_irrelevance _ _ eq_refl). clear e.
      simpl.
      unfold carve_sliceanndimbound_right. unfold sliceanndimend.
      unfold sliceanndimbeg. rewrite (proof_irrelevance _ _ pbeg).
      rewrite (proof_irrelevance _ _ (le_refl aend)).
      rewrite (proof_irrelevance _ (carve_sliceanndimbound_right_obligation_1 (S bound)
        (sadim (S bound) abeg aend (inc_sliceanndimbound_obligation_1 abeg aend pbeg)
           (inc_sliceanndimbound_obligation_2 bound aend pend))) pbeg).
      rewrite (proof_irrelevance _ (carve_sliceanndimbound_right_obligation_2 (S bound)
        (sadim (S bound) abeg aend (inc_sliceanndimbound_obligation_1 abeg aend pbeg)
           (inc_sliceanndimbound_obligation_2 bound aend pend))) (le_refl aend)).
      reflexivity...
    (* axis = S axis' *)
    - intros. dependent destruction sas. simpl. f_equal.
      rewrite (proof_irrelevance _ _ (le_S_n _ _ axis_lt_sdim)). simpl.
      generalize (eq_ind (sascons s sas)
                    (fun sas0 : sliceannshape (S dim) =>
                     get_sliceanndimbound sas axis' (le_S_n (S axis') dim axis_lt_sdim) =
                     get_sliceanndimbound sas0 (S axis') axis_lt_sdim) eq_refl (sascons s sas)
                    (JMeq_eq JMeq_refl)).
      simpl. intro e. rewrite (proof_irrelevance _ e eq_refl). clear e. simpl.
      destruct dim as [|dim'].
        (* dim = O *)
        * exfalso. apply le_S_n in axis_lt_sdim. apply (Nat.nle_succ_0 _ axis_lt_sdim)...
        (* dim = S dim' *)
        * specialize (IHaxis' dim' sas (le_S_n _ _ axis_lt_sdim) ).
          apply IHaxis'.
Defined.

Lemma carve_sliceannshapedim_right_is_inc_sliceannshapedim_n_right_inverse :
  forall {dim} (sas : sliceannshape (S dim)) (axis : nat) (n : nat) (axis_lt_sdim : axis < S dim)
               (sas_has_no_rpad : sas = carve_sliceannshapedim_right sas axis axis_lt_sdim),
    sas = carve_sliceannshapedim_right (inc_sliceannshapedim_n sas axis n axis_lt_sdim) axis axis_lt_sdim.
Proof.
  intros. generalize dependent dim. generalize dependent axis.
  induction n as [|n' IHn'].
    (* n = O *)
    - intros. simpl. dependent destruction sas.
      destruct s as [abeg aend pbeg pend].
      simpl in sas_has_no_rpad.
      simpl.
      apply sas_has_no_rpad.
    (* n = S n' *)
    - intros. specialize (IHn' axis dim sas axis_lt_sdim sas_has_no_rpad).
      simpl.
      rewrite <- carve_pad_surjective.
      rewrite (proof_irrelevance _ (inc_sliceannshapedim_n_obligation_1 (S dim) axis axis_lt_sdim) axis_lt_sdim).
      apply IHn'.
Qed.

Lemma inv_cpadr_all_is_cpadr_right_inverse :
  forall {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas) (axis : nat) (n : nat)
         (axis_lt_sdim : axis < S dim) (sas_has_no_rpad : sas = carve_sliceannshapedim_right sas axis axis_lt_sdim)
         (pi_gt_O : 0 < pi (innershape sas)),
    saa
    = transport (inv_cpadr_all
       (cpadr_n saa axis n axis_lt_sdim pi_gt_O) axis axis_lt_sdim
          (transport (P:=fun x => 0 < pi x) pi_gt_O (eq_sym (innershape_id_inc_sliceannshapedim_n _ _ _))))
       (eq_sym  (carve_sliceannshapedim_right_is_inc_sliceannshapedim_n_right_inverse sas axis n axis_lt_sdim sas_has_no_rpad)).
Admitted. (* TODO: prove *)

(* The proofs for Proposition 7 are given based on right rotation. Left
   rotation can be expressed as a right rotation, so there is no need to
   rewrite the proofs using left rotation specifically.
*)
(* Proposition 7.i, ii. *)
Check of_nat_lt.

(* TODO: reformulate this *)
(*Theorem rot_pad_id_i_ii :
  forall {dim} {sas : sliceannshape (S dim)} (saa : sliceannarray sas)
         (i j : nat) (m2 r : nat) (i_lt_sdim : i < S dim) (j_lt_sdim : j < S dim)
         (le_r_j_axis_size : r <= get_axis_size (outershape sas) (of_nat_lt j_lt_sdim))
         (sas_has_no_rpad : forall (axis : nat) (axis_lt_sdim : axis < S dim),
                            sas = carve_sliceannshapedim_right sas axis axis_lt_sdim),
  (j <> i) \/ (r = O) ->
    roti_right (of_nat_lt j_lt_sdim) r (outerarray saa) le_r_j_axis_size =
    inv_cpadr_all (roti_right (of_nat_lt j_lt_sdim) r (outerarray saa) le_r_j_axis_size).
*)

End Array.










































