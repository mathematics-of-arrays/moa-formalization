From Coq Require Import Arith Fin Init Omega Program.

(* transport in HoTT, maybe useful looking at these libraries *)
Definition transport {T : Type} {x y : T} {P : T -> Type} (u : P x)
  (pf : x = y) : P y := match pf with | eq_refl => u end.

Section Array.
  Variable E : Type.

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

  Program Fixpoint psi {dim : nat} {s : shape (S dim)}
      (idx : Fin.t (hd_shape s)) (a : array s) : array (tl_shape s) :=
    match idx with | F1 => reshape (take 1 a _) (tl_shape s) _
                   | FS pp => psi pp (drop 1 a _) end.
  Next Obligation. apply le_n_S. apply Nat.le_0_l. Qed.
  Next Obligation. apply le_n_S. apply Nat.le_0_l. Qed.
  Next Obligation. simpl. symmetry. apply Nat.sub_0_r. Qed.
End Array.
