From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba entropy jensen num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope num_occ_scope.
Local Open Scope entropy_scope.
Local Coercion INR : nat >-> R.

Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Local Notation "n %:R" := (INR n).

Definition simplR := (add0R, addR0, subR0, mul0R, mulR0, mul1R, mulR1).

Definition big_morph_plus_INR := big_morph INR morph_plus_INR (erefl 0%:R).

Local Hint Resolve leRR.
Local Hint Resolve leR0n.

Lemma log_concave_gt0 x y t :
  0 < x -> 0 < y -> 0 <= t <= 1 -> concave_leq log x y t.
Admitted.

Section seq_nat_dist.

Variable A : finType.
Variable f : A -> nat.
Variable total : nat.
Hypothesis sum_f_total : \sum_(a in A) f a = total.
Hypothesis total_gt0 : total != O.

Let f_div_total (a : A) := f a / total.

Lemma f_div_total_pos c : 0 <= f_div_total c.
Proof.
apply mulR_ge0 => //.
apply /Rlt_le /invR_gt0 /ltR0n.
by rewrite lt0n.
Qed.

Lemma f_div_total_1 : \rsum_(a in A) (mkPosFun f_div_total_pos) a = 1.
Proof.
rewrite /f_div_total -big_distrl -big_morph_plus_INR.
by rewrite sum_f_total /= mulRV // INR_eq0'.
Qed.

Definition seq_nat_dist := mkDist f_div_total_1.

End seq_nat_dist.

Section string.

Variable A : finType.

Section num_occ.

Lemma sum_num_occ s : \sum_(a in A) N(a|s) = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ rewrite big_split /= IH -big_mkcond /= (big_pred1 a) //.
  by move=> i; rewrite eq_sym.
Qed.

Lemma num_occ_flatten (a:A) ss :
  N(a|flatten ss) = \sum_(s <- ss) N(a|s).
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=; first by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

End num_occ.

Section entropy.
Variable S : seq A.
Hypothesis S_nonempty : size S != O.

Definition pchar c := N(c|S) / size S.

Definition num_occ_dist := seq_nat_dist (sum_num_occ S) S_nonempty.

Definition Hs0 := `H num_occ_dist.
End entropy.

Section string_concat.

(*
Definition Hs (s : seq A) :=
 \rsum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) / size s * log (size s / N(a|s)).
*)

Definition nHs (s : seq A) :=
 \rsum_(a in A)
  N(a|s) * log (size s / N(a|s)).

Lemma szHs_is_nHs s (H : size s != O) :
  size s * `H (@num_occ_dist s H) = nHs s.
Proof.
rewrite /entropy /nHs /num_occ_dist /=.
rewrite -mulRN1 big_distrl big_distrr /=.
apply eq_bigr => a _ /=.
rewrite /Rdiv (mulRC N(a|s)) 3!(mulRA _%:R) !mulRV ?mul1R // ?INR_eq0' //.
case /boolP: (N(a|s) == 0)%N => Hnum.
  by rewrite (eqP Hnum) !mul0R.
rewrite -mulRA mulRN1 /log /Log -mulNR -ln_Rinv.
  rewrite invRM ?invRK //; apply /eqP.
  + by rewrite INR_eq0'.
  + by apply /invR_neq0; rewrite INR_eq0'.
  + by rewrite INR_eq0' Hnum.
apply mulR_gt0.
  by apply /invR_gt0 /ltR0n; rewrite lt0n.
by apply /ltR0n; rewrite lt0n Hnum.
Qed.

Definition mulnRdep (x : nat) (y : x != O -> R) : R.
case/boolP: (x == O) => Hx.
+ exact 0.
+ exact (x * y Hx).
Defined.
Arguments mulnRdep x y : clear implicits.

Lemma mulnRdep_0 y : mulnRdep 0 y = 0.
Proof. rewrite /mulnRdep /=. by destruct boolP. Qed.

Lemma mulnRdep_nz x y (Hx : x != O) : mulnRdep x y = x * y Hx.
Proof.
rewrite /mulnRdep /=.
destruct boolP.
  by elimtype False; rewrite i in Hx.
do 2!f_equal; apply eq_irrelevance.
Qed.

Lemma szHs_is_nHs_full s : mulnRdep (size s) (fun H => Hs0 H) = nHs s.
Proof.
rewrite /mulnRdep; destruct boolP; last by apply szHs_is_nHs.
rewrite /nHs (eq_bigr (fun a => 0)); first by rewrite big1.
move=> a _; suff: N(a|s) == O; first by move /eqP ->; rewrite mul0R.
by rewrite /num_occ -leqn0 -(eqP i) count_size.
Qed.

Lemma Rpos_convex : convex_interval (fun x =>  0 < x).
Proof.
move=> x y t Hx Hy Ht.
case Ht0: (t == 0); first by rewrite (eqP Ht0) !simplR.
apply addR_gt0wl.
  apply mulR_gt0 => //.
  case/proj1: Ht Ht0 => // ->; by rewrite eqxx.
apply mulR_ge0; last exact: ltRW.
rewrite leR_subr_addr add0R; by case: Ht.
Qed.

Definition Rpos_interval := mkInterval Rpos_convex.

Lemma log_concave : concave_in Rpos_interval log.
Proof. by move=> x; apply log_concave_gt0. Qed.

Theorem concats_entropy ss :
(*  \rsum_(s <- ss) size s * Hs s
       <= size (flatten ss) * Hs (flatten ss). *)
(* \rsum_(s <- ss) mulnRdep (size s) (fun H => Hs0 H)
       <= mulnRdep (size (flatten ss)) (fun H => Hs0 H). *)
  \rsum_(s <- ss) nHs s <= nHs (flatten ss).
Proof.
(* (1) First simplify formula *)
(*rewrite szHs_is_nHs.
rewrite (eq_bigr _ (fun i _ => szHs_is_nHs i)).*)
rewrite exchange_big /nHs /=.
(* (2) Move to per-character inequalities *)
apply ler_rsum=> a _.
case/boolP: (ss == [::]) => Hss.
  by rewrite (eqP Hss) /= !big_nil mul0R.
case/boolP : (N(a|flatten ss) == O) => Hnum.
  rewrite (eqP Hnum) mul0R big_seq big1 // => s.
  rewrite -(in_tupleE ss) => /tnthP [i ->].
  move: Hnum; rewrite num_occ_flatten big_tnth sum_nat_eq0.
  move /forallP /(_ i) /implyP /(_ isT) /eqP ->.
  by rewrite mul0R.
case/boolP: (size (flatten ss) == 0)%N => Hsz.
  by move: Hnum; rewrite (nilP Hsz).
(* (4) Prepare to use jensen_dist_concave *)
have Htotal := esym (num_occ_flatten a ss).
rewrite big_tnth in Htotal.
set d := seq_nat_dist Htotal Hnum.
set r := fun i =>
  (size (tnth (in_tuple ss) i)) / N(a|tnth (in_tuple ss) i).
have Hr: forall i, i \in dist_supp d -> Rpos_interval (r i).
  rewrite /r /= => i Hi.
  case/boolP: (N(a | tnth (in_tuple ss) i) == O) => Ha.
    by move: Hi; rewrite inE /d /= (eqP Ha) /Rdiv mul0R eqxx.
  rewrite -lt0n in Ha.
  apply Rlt_mult_inv_pos; apply /ltR0n => //.
  by apply (leq_trans Ha), count_size.
(* (5) Apply Jensen *)
move: (jensen_dist_concave log_concave Hr).
rewrite /d /r /=.
rewrite -(big_tnth _ _ _ xpredT
  (fun s =>
     log ((size s) / N(a|s)) *
     (N(a|s) / N(a|flatten ss)))).
rewrite -(big_tnth _ _ _ xpredT
  (fun s =>
     (size s) / N(a|s) *
     (N(a|s) / N(a|flatten ss)))).
(* (6) Transform the statement to match the goal *)
move/(@leR_wpmul2r N(a|flatten ss) _ _ (leR0n _)).
rewrite !big_distrl /=.
rewrite (eq_bigr
     (fun i => N(a|i) * log (size i / N(a|i))));
  last first.
  move=> i _; rewrite -[RHS]mulRC !mulRA.
  by rewrite -mulRA mulVR ?mulR1 // ?INR_eq0'.
move/leR_trans; apply. (* LHS matches *)
rewrite mulRC; apply leR_wpmul2l => //.
apply Log_increasing_le => //.
  rewrite (bigID (fun i => N(a|i) == O)) /=.
  rewrite big1; last first.
    by move=> i /eqP -> /=; rewrite div0R mulR0.
  rewrite {d r Hr} add0R -big_filter big_tnth.
  set ss' := filter _ _.
  move: (Hnum); rewrite num_occ_flatten.
  rewrite [in X in X -> _](bigID (fun i => N(a|i) == 0)%nat) /=.
  rewrite big1 ?add0n; last by move=> i /eqP.
  rewrite -big_filter -/ss' => Hnum2.
  apply rsumr_gt0 => /= [|i].
    rewrite card_ord; move: ss' Hnum2 => [] //.
    by rewrite big_nil eqxx.
  have Hi: (N(a|tnth (in_tuple ss') i) > 0)%nat.
    move: (mem_tnth i (in_tuple ss')).
    by rewrite lt0n memtE /= mem_filter => /andP [].
  do! apply mulR_gt0; try apply invR_gt0; try apply ltR0n => //.
  + by move: Hi; case: (tnth _ _).
  + by rewrite big_tnth Htotal lt0n.
rewrite size_flatten /shape sumn_big_addn big_map.
rewrite big_morph_plus_INR /Rdiv big_distrl /=.
rewrite 2!big_tnth; apply ler_rsum => i _.
case/boolP: (N(a|tnth (in_tuple ss) i) == O) => Ha.
  rewrite (eqP Ha) mul0R mulR0.
  apply divR_ge0 => //; by rewrite ltR0n lt0n.
by rewrite -mulRA (mulRA (/ _)) mulVR ?mul1R // INR_eq0'.
Qed.

End string_concat.

End string.

(* tentative definition *)
Section higher_order_empirical_entropy.

Variables (A : finType) (l : seq A).
Hypothesis A0 : (O < #|A|)%nat.
Let n := size l.
Let def : A. Proof. move/card_gt0P : A0 => /sigW[def _]; exact def. Defined.
Hypothesis l0 : n != O.

(* the string consisting of the concatenation of the symbols following w in s *)
Fixpoint takes {k : nat} (w : k.-tuple A) (s : seq A) {struct s} : seq A :=
  if s is _ :: t then
    let s' := takes w t in
    if take k s == w then nth def (drop k s) O :: s' else s'
  else
    [::].

Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Local Notation "n %:R" := (INR n).

(* sample ref: https://www.dcc.uchile.cl/~gnavarro/ps/jea08.2.pdf *)
Definition hoH (k : nat) := / n%:R *
  \rsum_(w in {: k.-tuple A}) #|takes w l|%:R *
    match Bool.bool_dec (size w != O) true with
      | left H => `H (num_occ_dist H)
      | _ => 0
    end.

Lemma hoH_decr (k : nat) : hoH k.+1 <= hoH k.
Proof.
rewrite /hoH; apply/leRP; rewrite leR_pmul2l'; last first.
  by apply/ltRP/invR_gt0/ltRP; rewrite ltR0n' lt0n.
(* TODO *)
Abort.

End higher_order_empirical_entropy.
