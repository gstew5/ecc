Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Omega.

Definition odd := PeanoNat.Nat.Odd.

Section ecc.
  Variable N : nat.
  Hypothesis N_odd : odd N.

  (* codes: finite functions mapping {0..N-1} to bool *)
  Definition code := {ffun 'I_N -> bool}.
  Definition code0 : code := finfun (fun i : 'I_N => false).
  Definition code1 : code := finfun (fun i : 'I_N => true).  

  (* encode *)
  Variable encode : bool -> code.
  Hypothesis encode_ok :
    forall (b:bool) (i:'I_N), (encode b) i = b.

  (* hamming distance *)
  Definition hamming (c1 c2 : code) : nat :=
    \sum_(i : 'I_N | c1 i != c2 i) 1.

  Lemma hamming_comm c1 c2 : hamming c1 c2 = hamming c2 c1.
  Proof. by apply: congr_big => // i; rewrite eq_sym. Qed.

  (* decode *)
  Variable decode : code -> bool.
  Hypothesis decode_ok :
    forall c : code,
      (hamming c code0 < hamming c code1 -> decode c = false) /\
      (hamming c code1 < hamming c code0 -> decode c = true).

  (* syndrome *)
  Variable syndrome : code -> code.
  Hypothesis syndrome_ok :
    forall c : code,
      hamming c (syndrome c) <= Nat.div2 N.

  Lemma odd_decomp :
    forall n : nat, odd n -> exists n', n = 2 * n' + 1.
  Proof. move => n []n' ->; exists n' => //. Qed. (* by defn. of odd *)

  Lemma count_P_nP T :
    forall P (l : seq T),
      count P l + count (fun x => ~~P x) l = size l.
  Proof.
    move => P l; rewrite -count_predUI addnC.
    rewrite (eq_count (a2:=pred0)); last first.
    { by move => x /=; rewrite Bool.andb_negb_r. }
    rewrite count_pred0 add0n.
    rewrite (eq_count (a2:=predT)); last first.
    { by move => x /=; rewrite Bool.orb_negb_r. }
    by rewrite count_predT.
  Qed.

  Lemma count_P_nP' T :
    forall P Q (l : seq T),
      Q =1 (fun x => ~~P x) ->
      count P l + count Q l = size l.
  Proof. move => P Q l H; rewrite (eq_count H); apply: count_P_nP. Qed.
  
  Lemma hamming_code0_code1_N :
    forall c : code,
      hamming c code0 + hamming c code1 = N.
  Proof.
    rewrite /hamming /code0 /code1 => c; clear - c. 
    rewrite 2!sum1_count; set (X := index_enum _).
    rewrite count_P_nP'.
    { rewrite /X.
      have ->: index_enum (ordinal_finType N) = enum 'I_N by rewrite enumT.
      by rewrite -cardT card_ord. }
    by move => x; rewrite !ffunE negbK; case: (c x).
  Qed.

  Lemma encode_range :
    forall b,
      (b=false /\ encode b = code0) \/
      (b=true /\ encode b = code1).
  Proof.
    case; [right|left]; split => //;  
    by apply/ffunP => x; rewrite encode_ok ffunE.
  Qed.
  
  Theorem decode_encode_id :
    forall b : bool, decode (syndrome (encode b)) = b.
  Proof.
    move => b; move: (syndrome_ok (encode b)).
    case: (decode_ok (syndrome (encode b))).    
    case: (encode_range b) => [][]-> ->.
    { move => H _ => H2; rewrite H => //; clear H.
      move: (hamming_code0_code1_N (syndrome code0)) => H3.
      case: N_odd => N' H4; rewrite H4 in H2, H3; clear H4.
      rewrite Nat.add_1_r in H2, H3; rewrite Nat.div2_succ_double in H2.
      move: (leP H2) => H2'; apply/ltP; rewrite -plusE in H3.
      rewrite hamming_comm in H2'; omega. }
    move => _ H => H2; rewrite H => //; clear H.
    move: (hamming_code0_code1_N (syndrome code1)) => H3.
    case: N_odd => N' H4; rewrite H4 in H2, H3; clear H4.
    rewrite Nat.add_1_r in H2, H3; rewrite Nat.div2_succ_double in H2.
    move: (leP H2) => H2'; apply/ltP; rewrite -plusE in H3.
    rewrite hamming_comm in H2'; omega.
  Qed.
      
  Lemma syndrome_hamming_neq :
    forall c : code,
      hamming (syndrome c) code0 != hamming (syndrome c) code1.
  Proof.
    case: (odd_decomp N_odd) => N' H c.
    move: (hamming_code0_code1_N (syndrome c)); rewrite H.
    set (X := hamming _ _); set (Y := hamming _ _).
    have ->: (2*N'+1 = (2*N'+1)%coq_nat) by [].
    have ->: (X + Y = (X+Y)%coq_nat) by [].
    move => H2; apply/eqP => H3; rewrite H3 in H2; clear - H2.
    have H3: (Y + Y = 2*Y)%coq_nat by rewrite /= plus_0_r.
    rewrite H3 in H2.
    have H4: (Nat.Even (2*Y)%coq_nat) by exists Y.
    have H5: (Nat.Odd (2*N'+1)%coq_nat) by exists N'.
    rewrite -H2 in H5.
    apply: (Nat.Even_Odd_False _ H4 H5).
  Qed.

  Lemma hamming_syndrome_code0_code1_range :
    forall c : code,
      hamming (syndrome c) code0 < hamming (syndrome c) code1 \/
      hamming (syndrome c) code1 < hamming (syndrome c) code0.
  Proof.
    move => c; move: (syndrome_hamming_neq c).
    move: (hamming _ _) => X; move: (hamming _ _) => Y H.
    have H2: X <> Y by move => H2; rewrite H2 in H; move: (negP H).
    by case: (not_eq X Y H2); move/ltP; [left|right].
  Qed.    
End ecc.
Check decode_encode_id.