From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Rssr Reals_ext ssr_ext ssralg_ext log2 Rbigop.
Require Import proba jensen num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section string_concat.

Variable A : finType.

Definition minlen (s : seq A) :=
  \rsum_(c <- s) log (INR (size s) / INR (num_occ c s)).

Definition Hs0 (s : seq A) :=
  / INR (size s) * minlen s.

Lemma sum_num_occ (s : seq A) : \sum_(a in A) num_occ a s = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ rewrite big_split /= IH -big_mkcond /= (big_pred1 a) //.
  by move=> i; rewrite eq_sym.
Qed.

Definition Hs (s : seq A) :=
 \rsum_(a in A)
  INR (num_occ a s) / INR (size s) * log (INR (size s) / INR (num_occ a s)).

Definition nHs (s : seq A) :=
 \rsum_(a in A)
  INR (num_occ a s) * log (INR (size s) / INR (num_occ a s)).

Lemma szHs_is_nHs s : INR (size s) * Hs s = nHs s.
Proof.
rewrite /Hs /nHs big_distrr.
apply eq_bigr => i _ /=.
case Hnum: (num_occ i s == O).
  by rewrite (eqP Hnum) /Rdiv mulRA mulRC !mul0R !mulR0.
rewrite /Rdiv (mulRC (INR (num_occ i s))) 2!(mulRA (INR _)).
rewrite !mulRV ?mul1R // ?INR_eq0.
apply/eqP => Hsz.
move: (count_size (pred1 i) s).
by rewrite Hsz leqn0 Hnum.
Qed.

Lemma log_concave : concave_in (fun x => 0 < x) log.
Proof.
move=> x y t Hx Hy Ht.
split; last first.
case Ht1: (t == 1).
  rewrite (eqP Ht1).
Search (0 < _ + _).
  apply Rplus_lt_le_0_compat.
    by rewrite mul1R.
  rewrite subRR mul0R.
  by apply Rle_refl.
apply Rplus_le_lt_0_compat.
  apply Rmult_le_pos.
    exact/(proj1 Ht).
  by apply Rlt_le.
apply mulR_gt0 => //.
apply (Rplus_lt_reg_l t).
rewrite addR0 Rplus_minus.
apply/RltP; rewrite ltR_neqAle Ht1 /=; apply/RleP; by case: Ht.
Admitted.

Lemma a_eq_true : Set2.a card_bool = true.
Proof.
rewrite /Set2.a /enum_val /enum_mem.
by rewrite Finite.EnumDef.enumDef /=.
Qed.

Theorem concat_entropy s1 s2 :
  INR (size s1) * Hs s1 + INR (size s2) * Hs s2
  <= INR (size (s1 ++ s2)) * Hs (s1 ++ s2).
Proof.
rewrite !szHs_is_nHs.
rewrite /nHs -big_split /=.
apply ler_rsum => i _.
rewrite /num_occ count_cat size_cat.
case Hs1: (count_mem i s1 == O).
  rewrite (eqP Hs1) !mul0R !add0n add0R.
  case Hs2: (count_mem i s2 == O).
    by rewrite (eqP Hs2) !mul0R; apply Rle_refl.
  have cnt_s2_gt0: 0 < INR (count_mem i s2).
    apply lt_0_INR.
    apply /leP.
    by rewrite lt0n Hs2.
  have cnt_lt_size t: INR ((count_mem i) t) <= INR (size t).
    apply le_INR.
    apply/leP.
    by apply count_size.
  have sz_s2_gt0: 0 < INR (size s2).
    apply (Rlt_le_trans _ _ _ cnt_s2_gt0).
    by apply cnt_lt_size.
  apply Rmult_le_compat_l.
    by apply Rlt_le.
  apply Log_increasing_le.
      by apply Rlt_1_2.
    by apply Rlt_mult_inv_pos.
  apply Rmult_le_compat_r.
    by apply Rlt_le, invR_gt0, cnt_s2_gt0.
  apply le_INR.
  apply /leP.
  by apply leq_addl.
have cnt_s1_gt0: 0 < INR (count_mem i s1).
  apply lt_0_INR.
  apply /leP.
  by rewrite lt0n Hs1.
have cnt_lt_size t: INR ((count_mem i) t) <= INR (size t).
  apply le_INR.
  apply/leP.
  by apply count_size.
have sz_s1_gt0: 0 < INR (size s1).
  apply (Rlt_le_trans _ _ _ cnt_s1_gt0).
  by apply cnt_lt_size.
case Hs2: (count_mem i s2 == O).
  rewrite (eqP Hs2) !mul0R !addn0 addR0.
  apply Rmult_le_compat_l.
    by apply Rlt_le.
  apply Log_increasing_le.
      by apply Rlt_1_2.
    by apply Rlt_mult_inv_pos.
  apply Rmult_le_compat_r.
    by apply Rlt_le, invR_gt0, cnt_s1_gt0.
  apply le_INR.
  apply /leP.
  by apply leq_addr.
have cnt_s2_gt0: 0 < INR (count_mem i s2).
  apply lt_0_INR.
  apply /leP.
  by rewrite lt0n Hs2.
have cnt_12_gt0: 0 < INR (count_mem i s1 + count_mem i s2).
  apply (Rlt_le_trans _ _ _ cnt_s1_gt0).
  apply le_INR.
  apply/leP.
  by apply leq_addr.
(* Then we should use jensen_dist *)
have Hp: 0 <= INR (count_mem i s2) / INR (count_mem i (s1 ++ s2)) <= 1.
  rewrite count_cat.
  split.
    apply Rlt_le.
    apply mulR_gt0 => //.
    by apply invR_gt0.
  apply (Rmult_le_reg_r _ _ _ cnt_12_gt0).
  rewrite -mulRA (mulRC (/ _)) mulRV ?(mulR1,mul1R).
    apply le_INR.
    apply/leP.
    by apply leq_addl.
  rewrite INR_eq0 -lt0n -ltR0n; exact/RltP.
have H1m: 1 - INR (count_mem i s2) / INR (count_mem i (s1 ++ s2)) =
          INR (count_mem i s1) / INR (count_mem i (s1 ++ s2)).
  rewrite count_cat -(divRR (INR (count_mem i s1 + count_mem i s2))).
    rewrite -Rdiv_minus_distr -minus_INR.
      by rewrite minusE addnK.
    apply/leP.
    by apply leq_addl.
  rewrite INR_eq0 -lt0n -ltR0n; exact/RltP.
have Hdist: (0 < #|dist_supp (Binary.d card_bool Hp)|)%nat.
  rewrite /dist_supp card_gt0.
  apply/eqP => /setP /(_ true).
  rewrite !inE /= a_eq_true /= /Binary.f eqxx.
  rewrite H1m.
  move/eqP.
  apply Rmult_integral_contrapositive.
  split.
    by apply Rgt_not_eq.
  apply Rinv_neq_0_compat.
  apply Rgt_not_eq.
  by rewrite count_cat.
set r := (fun b => if b then INR (size s1) / INR (count_mem i s1)
                   else INR (size s2) / INR (count_mem i s2)).
have Hr: dist_covered (fun x => 0 < x) r (Binary.d card_bool Hp).
  move=> [|] _ /=.
    by apply Rdiv_lt_0_compat.
  apply Rdiv_lt_0_compat => //.
  apply lt_0_INR.
  apply/leP.
  apply (@leq_trans (count_mem i s2)).
    by rewrite lt0n Hs2.
  by apply count_size.
move: (jensen_dist_concave log_concave Hdist Hr).
rewrite (bigD1 true) ?inE // (bigD1 false) ?inE // big_pred0 /=;
  last by move=> j /=; case: j.
rewrite (bigD1 true) ?inE // (bigD1 false) ?inE // big_pred0 /Binary.f /=;
  last by move=> j /=; case: j.
rewrite a_eq_true eqxx eqb_id /=.
rewrite H1m !addR0.
rewrite /Rdiv 4!mulRA -2![_ * / _ * _]mulRA.
rewrite mulVR ?mulR1; last first.
  by rewrite INR_eq0 Hs2.
rewrite mulVR ?mulR1; last first.
  by rewrite INR_eq0 Hs1.
rewrite -2!Rmult_plus_distr_r.
rewrite mulRC.
move/(Rmult_le_compat_l (INR ((count_mem i) (s1 ++ s2)))).
rewrite mulRA mulRV ?INR_eq0 ?mul1R; last first.
  rewrite -?lt0n count_cat -ltR0n; exact/RltP.
rewrite -count_cat plus_INR.
rewrite ![_ * INR (count_mem _ _)]mulRC.
apply.
apply Rlt_le.
by rewrite count_cat.
Qed.

Lemma num_occ_flatten (a:A) ss :
  num_occ a (flatten ss) = \sum_(s <- ss) num_occ a s.
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=.
  by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

Theorem concats_entropy ss :
  \rsum_(s <- ss) INR (size s) * Hs s
  <= INR (size (flatten ss)) * Hs (flatten ss).
Proof.
rewrite szHs_is_nHs.
rewrite (eq_bigr _ (fun i _ => szHs_is_nHs i)).
rewrite exchange_big /=.
apply ler_rsum=> a _.
rewrite (bigID (fun s => num_occ a s == O)) /=.
rewrite big1; last by move=> i /eqP ->; rewrite !mul0R.
rewrite num_occ_flatten.
rewrite [in X in _ <= X](bigID (fun s => num_occ a s == O)) /=.
rewrite [in X in _ <= X]big1 ?add0R //; last by move=> i /eqP.
rewrite -big_filter -[in X in _ <= X]big_filter add0n.
set ss' := [seq s <- ss | num_occ a s != O].
(*case Hsz: (ss' == [::]).
  rewrite (eqP Hsz) !big_nil mul0R.
  by apply Rle_refl.*)
apply (Rle_trans _ (INR (\sum_(i <- ss') num_occ a i) *
    log (INR (size (flatten ss')) / INR (\sum_(i <- ss') num_occ a i))));
  last first.
  case Hsum: (\sum_(i <- ss') num_occ a i == O).
    rewrite (eqP Hsum) !mul0R.
    by apply Rle_refl.
  apply Rmult_le_compat_l.
    by apply pos_INR.
  apply Log_increasing_le.
      by apply Rlt_1_2.
    apply Rlt_mult_inv_pos.
      apply /lt_0_INR /leP.
      clearbody ss'.
      clear -Hsum.
      elim: ss' Hsum => [|s ss IH] /=.
        by rewrite big_nil eqxx.
      rewrite big_cons size_cat.
      case Hocc: (num_occ a s == O).
        rewrite (eqP Hocc) => /IH.
        apply ltn_addl.
      move=> _.
      apply /ltn_addr /(@leq_trans (num_occ a s)).
        by rewrite lt0n Hocc.
      by apply count_size.
    apply/lt_0_INR/ltP.
    by rewrite lt0n Hsum.
  apply Rmult_le_compat_r.
    apply /Rlt_le /invR_gt0 /lt_0_INR /ltP.
    by rewrite lt0n Hsum.
  apply /le_INR /leP.
  subst ss'; clear.
  elim: ss => [|s ss IH] //=.
  case: ifP => Hnum /=.
    by rewrite !size_cat leq_add2l.
  rewrite size_cat.
  by apply /(leq_trans IH) /leq_addl.
Abort.
    
End string_concat.