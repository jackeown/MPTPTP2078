%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tHW0pWcvIb

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:13 EST 2020

% Result     : Theorem 44.44s
% Output     : Refutation 44.44s
% Verified   : 
% Statistics : Number of formulae       :  169 (1607 expanded)
%              Number of leaves         :   32 ( 493 expanded)
%              Depth                    :   24
%              Number of atoms          : 1387 (14180 expanded)
%              Number of equality atoms :  143 (1245 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X30 @ X31 ) @ X32 )
      = ( k3_xboole_0 @ X30 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','35'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','32'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','45'])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_enumset1 @ X50 @ X50 @ X51 )
      = ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 )
      | ( r2_hidden @ X38 @ X42 )
      | ( X42
       != ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X38 @ ( k1_enumset1 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X34 != X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X33 @ X35 @ X36 @ X33 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','65','66'])).

thf('68',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','67'])).

thf('69',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('70',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('71',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('72',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( X34 = X35 )
      | ( X34 = X36 )
      | ( X34 = X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('74',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('75',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_enumset1 @ X50 @ X50 @ X51 )
      = ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('76',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ~ ( zip_tseitin_0 @ X43 @ X39 @ X40 @ X41 )
      | ( X42
       != ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('77',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X39 @ X40 @ X41 )
      | ~ ( r2_hidden @ X43 @ ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( X34 = X35 )
      | ( X34 = X36 )
      | ( X34 = X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['71','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('101',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X17 ) )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(t60_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( ( r2_hidden @ C @ B )
          & ( A != C ) )
        | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k1_tarski @ A ) ) ) ) )).

thf('103',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ~ ( r2_hidden @ X77 @ X78 )
      | ( X77 != X79 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X77 @ X79 ) @ X78 )
        = ( k1_tarski @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t60_zfmisc_1])).

thf('104',plain,(
    ! [X78: $i,X79: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X79 @ X79 ) @ X78 )
        = ( k1_tarski @ X79 ) )
      | ~ ( r2_hidden @ X79 @ X78 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X0 ) ) @ ( k5_xboole_0 @ X1 @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k5_xboole_0 @ X1 @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','107'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('109',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('110',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('111',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['108','117','118','119'])).

thf('121',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','67'])).

thf('122',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('125',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','65'])).

thf('126',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('129',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['123','126'])).

thf('134',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['68','127','132','133'])).

thf('135',plain,(
    $false ),
    inference(simplify,[status(thm)],['134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tHW0pWcvIb
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:07:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 44.44/44.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 44.44/44.66  % Solved by: fo/fo7.sh
% 44.44/44.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.44/44.66  % done 16350 iterations in 44.211s
% 44.44/44.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 44.44/44.66  % SZS output start Refutation
% 44.44/44.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 44.44/44.66  thf(sk_B_type, type, sk_B: $i > $i).
% 44.44/44.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 44.44/44.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 44.44/44.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 44.44/44.66  thf(sk_A_type, type, sk_A: $i).
% 44.44/44.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 44.44/44.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 44.44/44.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.44/44.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 44.44/44.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 44.44/44.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 44.44/44.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 44.44/44.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.44/44.66  thf(t67_zfmisc_1, conjecture,
% 44.44/44.66    (![A:$i,B:$i]:
% 44.44/44.66     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 44.44/44.66       ( ~( r2_hidden @ A @ B ) ) ))).
% 44.44/44.66  thf(zf_stmt_0, negated_conjecture,
% 44.44/44.66    (~( ![A:$i,B:$i]:
% 44.44/44.66        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 44.44/44.66          ( ~( r2_hidden @ A @ B ) ) ) )),
% 44.44/44.66    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 44.44/44.66  thf('0', plain,
% 44.44/44.66      (((r2_hidden @ sk_A @ sk_B_1)
% 44.44/44.66        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 44.44/44.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.44/44.66  thf('1', plain,
% 44.44/44.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 44.44/44.66         <= (~
% 44.44/44.66             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 44.44/44.66      inference('split', [status(esa)], ['0'])).
% 44.44/44.66  thf('2', plain,
% 44.44/44.66      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 44.44/44.66        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 44.44/44.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.44/44.66  thf('3', plain,
% 44.44/44.66      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 44.44/44.66       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 44.44/44.66      inference('split', [status(esa)], ['2'])).
% 44.44/44.66  thf('4', plain,
% 44.44/44.66      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 44.44/44.66      inference('split', [status(esa)], ['0'])).
% 44.44/44.66  thf('5', plain,
% 44.44/44.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 44.44/44.66         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 44.44/44.66      inference('split', [status(esa)], ['2'])).
% 44.44/44.66  thf(t100_xboole_1, axiom,
% 44.44/44.66    (![A:$i,B:$i]:
% 44.44/44.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 44.44/44.66  thf('6', plain,
% 44.44/44.66      (![X25 : $i, X26 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X25 @ X26)
% 44.44/44.66           = (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.44/44.66  thf(t112_xboole_1, axiom,
% 44.44/44.66    (![A:$i,B:$i,C:$i]:
% 44.44/44.66     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 44.44/44.66       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 44.44/44.66  thf('7', plain,
% 44.44/44.66      (![X27 : $i, X28 : $i, X29 : $i]:
% 44.44/44.66         ((k5_xboole_0 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X29))
% 44.44/44.66           = (k3_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29))),
% 44.44/44.66      inference('cnf', [status(esa)], [t112_xboole_1])).
% 44.44/44.66  thf('8', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 44.44/44.66           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['6', '7'])).
% 44.44/44.66  thf('9', plain,
% 44.44/44.66      (![X25 : $i, X26 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X25 @ X26)
% 44.44/44.66           = (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.44/44.66  thf(commutativity_k3_xboole_0, axiom,
% 44.44/44.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 44.44/44.66  thf('10', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.44/44.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.44/44.66  thf('11', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 44.44/44.66           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.44/44.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 44.44/44.66  thf('12', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.44/44.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.44/44.66  thf(idempotence_k3_xboole_0, axiom,
% 44.44/44.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 44.44/44.66  thf('13', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 44.44/44.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 44.44/44.66  thf(t16_xboole_1, axiom,
% 44.44/44.66    (![A:$i,B:$i,C:$i]:
% 44.44/44.66     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 44.44/44.66       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 44.44/44.66  thf('14', plain,
% 44.44/44.66      (![X30 : $i, X31 : $i, X32 : $i]:
% 44.44/44.66         ((k3_xboole_0 @ (k3_xboole_0 @ X30 @ X31) @ X32)
% 44.44/44.66           = (k3_xboole_0 @ X30 @ (k3_xboole_0 @ X31 @ X32)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t16_xboole_1])).
% 44.44/44.66  thf('15', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k3_xboole_0 @ X0 @ X1)
% 44.44/44.66           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['13', '14'])).
% 44.44/44.66  thf('16', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.44/44.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.44/44.66  thf('17', plain,
% 44.44/44.66      (![X25 : $i, X26 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X25 @ X26)
% 44.44/44.66           = (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.44/44.66  thf('18', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X0 @ X1)
% 44.44/44.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['16', '17'])).
% 44.44/44.66  thf('19', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 44.44/44.66           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['15', '18'])).
% 44.44/44.66  thf('20', plain,
% 44.44/44.66      (![X27 : $i, X28 : $i, X29 : $i]:
% 44.44/44.66         ((k5_xboole_0 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X29))
% 44.44/44.66           = (k3_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29))),
% 44.44/44.66      inference('cnf', [status(esa)], [t112_xboole_1])).
% 44.44/44.66  thf('21', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 44.44/44.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 44.44/44.66  thf('22', plain,
% 44.44/44.66      (![X25 : $i, X26 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X25 @ X26)
% 44.44/44.66           = (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.44/44.66  thf('23', plain,
% 44.44/44.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['21', '22'])).
% 44.44/44.66  thf(t7_xboole_0, axiom,
% 44.44/44.66    (![A:$i]:
% 44.44/44.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 44.44/44.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 44.44/44.66  thf('24', plain,
% 44.44/44.66      (![X22 : $i]:
% 44.44/44.66         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 44.44/44.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 44.44/44.66  thf('25', plain,
% 44.44/44.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['21', '22'])).
% 44.44/44.66  thf(t1_xboole_0, axiom,
% 44.44/44.66    (![A:$i,B:$i,C:$i]:
% 44.44/44.66     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 44.44/44.66       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 44.44/44.66  thf('26', plain,
% 44.44/44.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 44.44/44.66         ((r2_hidden @ X14 @ X15)
% 44.44/44.66          | (r2_hidden @ X14 @ X16)
% 44.44/44.66          | ~ (r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t1_xboole_0])).
% 44.44/44.66  thf('27', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 44.44/44.66          | (r2_hidden @ X1 @ X0)
% 44.44/44.66          | (r2_hidden @ X1 @ X0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['25', '26'])).
% 44.44/44.66  thf('28', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 44.44/44.66      inference('simplify', [status(thm)], ['27'])).
% 44.44/44.66  thf('29', plain,
% 44.44/44.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['21', '22'])).
% 44.44/44.66  thf('30', plain,
% 44.44/44.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X14 @ X15)
% 44.44/44.66          | ~ (r2_hidden @ X14 @ X16)
% 44.44/44.66          | ~ (r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t1_xboole_0])).
% 44.44/44.66  thf('31', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 44.44/44.66          | ~ (r2_hidden @ X1 @ X0)
% 44.44/44.66          | ~ (r2_hidden @ X1 @ X0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['29', '30'])).
% 44.44/44.66  thf('32', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X1 @ X0)
% 44.44/44.66          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 44.44/44.66      inference('simplify', [status(thm)], ['31'])).
% 44.44/44.66  thf('33', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 44.44/44.66      inference('clc', [status(thm)], ['28', '32'])).
% 44.44/44.66  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['24', '33'])).
% 44.44/44.66  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.44/44.66      inference('demod', [status(thm)], ['23', '34'])).
% 44.44/44.66  thf('36', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 44.44/44.66           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 44.44/44.66      inference('demod', [status(thm)], ['19', '20', '35'])).
% 44.44/44.66  thf(t3_xboole_0, axiom,
% 44.44/44.66    (![A:$i,B:$i]:
% 44.44/44.66     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 44.44/44.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 44.44/44.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 44.44/44.66            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 44.44/44.66  thf('37', plain,
% 44.44/44.66      (![X18 : $i, X19 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ X18 @ X19) | (r2_hidden @ (sk_C @ X19 @ X18) @ X18))),
% 44.44/44.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 44.44/44.66  thf('38', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 44.44/44.66      inference('clc', [status(thm)], ['28', '32'])).
% 44.44/44.66  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['24', '33'])).
% 44.44/44.66  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 44.44/44.66      inference('demod', [status(thm)], ['38', '39'])).
% 44.44/44.66  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 44.44/44.66      inference('sup-', [status(thm)], ['37', '40'])).
% 44.44/44.66  thf(d7_xboole_0, axiom,
% 44.44/44.66    (![A:$i,B:$i]:
% 44.44/44.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 44.44/44.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 44.44/44.66  thf('42', plain,
% 44.44/44.66      (![X10 : $i, X11 : $i]:
% 44.44/44.66         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 44.44/44.66          | ~ (r1_xboole_0 @ X10 @ X11))),
% 44.44/44.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 44.44/44.66  thf('43', plain,
% 44.44/44.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['41', '42'])).
% 44.44/44.66  thf('44', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 44.44/44.66      inference('demod', [status(thm)], ['36', '43'])).
% 44.44/44.66  thf('45', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['12', '44'])).
% 44.44/44.66  thf('46', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['11', '45'])).
% 44.44/44.66  thf('47', plain,
% 44.44/44.66      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 44.44/44.66         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 44.44/44.66      inference('sup+', [status(thm)], ['5', '46'])).
% 44.44/44.66  thf('48', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.44/44.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.44/44.66  thf('49', plain,
% 44.44/44.66      (![X10 : $i, X12 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ X10 @ X12)
% 44.44/44.66          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 44.44/44.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 44.44/44.66  thf('50', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['48', '49'])).
% 44.44/44.66  thf('51', plain,
% 44.44/44.66      (((((k1_xboole_0) != (k1_xboole_0))
% 44.44/44.66         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 44.44/44.66         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 44.44/44.66      inference('sup-', [status(thm)], ['47', '50'])).
% 44.44/44.66  thf('52', plain,
% 44.44/44.66      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 44.44/44.66         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 44.44/44.66      inference('simplify', [status(thm)], ['51'])).
% 44.44/44.66  thf(t69_enumset1, axiom,
% 44.44/44.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 44.44/44.66  thf('53', plain,
% 44.44/44.66      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 44.44/44.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 44.44/44.66  thf(t70_enumset1, axiom,
% 44.44/44.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 44.44/44.66  thf('54', plain,
% 44.44/44.66      (![X50 : $i, X51 : $i]:
% 44.44/44.66         ((k1_enumset1 @ X50 @ X50 @ X51) = (k2_tarski @ X50 @ X51))),
% 44.44/44.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 44.44/44.66  thf(d1_enumset1, axiom,
% 44.44/44.66    (![A:$i,B:$i,C:$i,D:$i]:
% 44.44/44.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 44.44/44.66       ( ![E:$i]:
% 44.44/44.66         ( ( r2_hidden @ E @ D ) <=>
% 44.44/44.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 44.44/44.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 44.44/44.66  thf(zf_stmt_2, axiom,
% 44.44/44.66    (![E:$i,C:$i,B:$i,A:$i]:
% 44.44/44.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 44.44/44.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 44.44/44.66  thf(zf_stmt_3, axiom,
% 44.44/44.66    (![A:$i,B:$i,C:$i,D:$i]:
% 44.44/44.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 44.44/44.66       ( ![E:$i]:
% 44.44/44.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 44.44/44.66  thf('55', plain,
% 44.44/44.66      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 44.44/44.66         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41)
% 44.44/44.66          | (r2_hidden @ X38 @ X42)
% 44.44/44.66          | ((X42) != (k1_enumset1 @ X41 @ X40 @ X39)))),
% 44.44/44.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 44.44/44.66  thf('56', plain,
% 44.44/44.66      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 44.44/44.66         ((r2_hidden @ X38 @ (k1_enumset1 @ X41 @ X40 @ X39))
% 44.44/44.66          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41))),
% 44.44/44.66      inference('simplify', [status(thm)], ['55'])).
% 44.44/44.66  thf('57', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.44/44.66         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 44.44/44.66          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 44.44/44.66      inference('sup+', [status(thm)], ['54', '56'])).
% 44.44/44.66  thf('58', plain,
% 44.44/44.66      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 44.44/44.66         (((X34) != (X33)) | ~ (zip_tseitin_0 @ X34 @ X35 @ X36 @ X33))),
% 44.44/44.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 44.44/44.66  thf('59', plain,
% 44.44/44.66      (![X33 : $i, X35 : $i, X36 : $i]:
% 44.44/44.66         ~ (zip_tseitin_0 @ X33 @ X35 @ X36 @ X33)),
% 44.44/44.66      inference('simplify', [status(thm)], ['58'])).
% 44.44/44.66  thf('60', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['57', '59'])).
% 44.44/44.66  thf('61', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['53', '60'])).
% 44.44/44.66  thf('62', plain,
% 44.44/44.66      (![X18 : $i, X20 : $i, X21 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X20 @ X18)
% 44.44/44.66          | ~ (r2_hidden @ X20 @ X21)
% 44.44/44.66          | ~ (r1_xboole_0 @ X18 @ X21))),
% 44.44/44.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 44.44/44.66  thf('63', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['61', '62'])).
% 44.44/44.66  thf('64', plain,
% 44.44/44.66      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 44.44/44.66         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 44.44/44.66      inference('sup-', [status(thm)], ['52', '63'])).
% 44.44/44.66  thf('65', plain,
% 44.44/44.66      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 44.44/44.66       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['4', '64'])).
% 44.44/44.66  thf('66', plain,
% 44.44/44.66      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 44.44/44.66       ((r2_hidden @ sk_A @ sk_B_1))),
% 44.44/44.66      inference('split', [status(esa)], ['0'])).
% 44.44/44.66  thf('67', plain,
% 44.44/44.66      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 44.44/44.66      inference('sat_resolution*', [status(thm)], ['3', '65', '66'])).
% 44.44/44.66  thf('68', plain,
% 44.44/44.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 44.44/44.66      inference('simpl_trail', [status(thm)], ['1', '67'])).
% 44.44/44.66  thf('69', plain,
% 44.44/44.66      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 44.44/44.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 44.44/44.66  thf('70', plain,
% 44.44/44.66      (![X22 : $i]:
% 44.44/44.66         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 44.44/44.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 44.44/44.66  thf('71', plain,
% 44.44/44.66      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 44.44/44.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 44.44/44.66  thf('72', plain,
% 44.44/44.66      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 44.44/44.66         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 44.44/44.66          | ((X34) = (X35))
% 44.44/44.66          | ((X34) = (X36))
% 44.44/44.66          | ((X34) = (X37)))),
% 44.44/44.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 44.44/44.66  thf('73', plain,
% 44.44/44.66      (![X18 : $i, X19 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ X18 @ X19) | (r2_hidden @ (sk_C @ X19 @ X18) @ X18))),
% 44.44/44.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 44.44/44.66  thf('74', plain,
% 44.44/44.66      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 44.44/44.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 44.44/44.66  thf('75', plain,
% 44.44/44.66      (![X50 : $i, X51 : $i]:
% 44.44/44.66         ((k1_enumset1 @ X50 @ X50 @ X51) = (k2_tarski @ X50 @ X51))),
% 44.44/44.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 44.44/44.66  thf('76', plain,
% 44.44/44.66      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X43 @ X42)
% 44.44/44.66          | ~ (zip_tseitin_0 @ X43 @ X39 @ X40 @ X41)
% 44.44/44.66          | ((X42) != (k1_enumset1 @ X41 @ X40 @ X39)))),
% 44.44/44.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 44.44/44.66  thf('77', plain,
% 44.44/44.66      (![X39 : $i, X40 : $i, X41 : $i, X43 : $i]:
% 44.44/44.66         (~ (zip_tseitin_0 @ X43 @ X39 @ X40 @ X41)
% 44.44/44.66          | ~ (r2_hidden @ X43 @ (k1_enumset1 @ X41 @ X40 @ X39)))),
% 44.44/44.66      inference('simplify', [status(thm)], ['76'])).
% 44.44/44.66  thf('78', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 44.44/44.66          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['75', '77'])).
% 44.44/44.66  thf('79', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 44.44/44.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['74', '78'])).
% 44.44/44.66  thf('80', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 44.44/44.66          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['73', '79'])).
% 44.44/44.66  thf('81', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 44.44/44.66          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 44.44/44.66          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 44.44/44.66          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['72', '80'])).
% 44.44/44.66  thf('82', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 44.44/44.66          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 44.44/44.66      inference('simplify', [status(thm)], ['81'])).
% 44.44/44.66  thf('83', plain,
% 44.44/44.66      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 44.44/44.66         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 44.44/44.66          | ((X34) = (X35))
% 44.44/44.66          | ((X34) = (X36))
% 44.44/44.66          | ((X34) = (X37)))),
% 44.44/44.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 44.44/44.66  thf('84', plain,
% 44.44/44.66      (![X18 : $i, X19 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ X18 @ X19) | (r2_hidden @ (sk_C @ X19 @ X18) @ X19))),
% 44.44/44.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 44.44/44.66  thf('85', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 44.44/44.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['74', '78'])).
% 44.44/44.66  thf('86', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 44.44/44.66          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['84', '85'])).
% 44.44/44.66  thf('87', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 44.44/44.66          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 44.44/44.66          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 44.44/44.66          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 44.44/44.66      inference('sup-', [status(thm)], ['83', '86'])).
% 44.44/44.66  thf('88', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 44.44/44.66          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 44.44/44.66      inference('simplify', [status(thm)], ['87'])).
% 44.44/44.66  thf('89', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((X0) = (X1))
% 44.44/44.66          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 44.44/44.66          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['82', '88'])).
% 44.44/44.66  thf('90', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 44.44/44.66      inference('simplify', [status(thm)], ['89'])).
% 44.44/44.66  thf('91', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['61', '62'])).
% 44.44/44.66  thf('92', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 44.44/44.66      inference('sup-', [status(thm)], ['90', '91'])).
% 44.44/44.66  thf('93', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 44.44/44.66      inference('sup-', [status(thm)], ['71', '92'])).
% 44.44/44.66  thf('94', plain,
% 44.44/44.66      (![X0 : $i]:
% 44.44/44.66         (((k2_tarski @ X0 @ X0) = (k1_xboole_0))
% 44.44/44.66          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0)))),
% 44.44/44.66      inference('sup-', [status(thm)], ['70', '93'])).
% 44.44/44.66  thf('95', plain,
% 44.44/44.66      (![X0 : $i]:
% 44.44/44.66         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 44.44/44.66          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['69', '94'])).
% 44.44/44.66  thf('96', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 44.44/44.66      inference('sup-', [status(thm)], ['57', '59'])).
% 44.44/44.66  thf('97', plain,
% 44.44/44.66      (![X0 : $i]:
% 44.44/44.66         ((r2_hidden @ X0 @ k1_xboole_0) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['95', '96'])).
% 44.44/44.66  thf('98', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 44.44/44.66      inference('demod', [status(thm)], ['38', '39'])).
% 44.44/44.66  thf('99', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 44.44/44.66      inference('clc', [status(thm)], ['97', '98'])).
% 44.44/44.66  thf('100', plain,
% 44.44/44.66      (![X22 : $i]:
% 44.44/44.66         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 44.44/44.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 44.44/44.66  thf('101', plain,
% 44.44/44.66      (![X14 : $i, X15 : $i, X17 : $i]:
% 44.44/44.66         ((r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X17))
% 44.44/44.66          | (r2_hidden @ X14 @ X15)
% 44.44/44.66          | ~ (r2_hidden @ X14 @ X17))),
% 44.44/44.66      inference('cnf', [status(esa)], [t1_xboole_0])).
% 44.44/44.66  thf('102', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((X0) = (k1_xboole_0))
% 44.44/44.66          | (r2_hidden @ (sk_B @ X0) @ X1)
% 44.44/44.66          | (r2_hidden @ (sk_B @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 44.44/44.66      inference('sup-', [status(thm)], ['100', '101'])).
% 44.44/44.66  thf(t60_zfmisc_1, axiom,
% 44.44/44.66    (![A:$i,B:$i,C:$i]:
% 44.44/44.66     ( ( r2_hidden @ A @ B ) =>
% 44.44/44.66       ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 44.44/44.66         ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ))).
% 44.44/44.66  thf('103', plain,
% 44.44/44.66      (![X77 : $i, X78 : $i, X79 : $i]:
% 44.44/44.66         (~ (r2_hidden @ X77 @ X78)
% 44.44/44.66          | ((X77) != (X79))
% 44.44/44.66          | ((k3_xboole_0 @ (k2_tarski @ X77 @ X79) @ X78) = (k1_tarski @ X77)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t60_zfmisc_1])).
% 44.44/44.66  thf('104', plain,
% 44.44/44.66      (![X78 : $i, X79 : $i]:
% 44.44/44.66         (((k3_xboole_0 @ (k2_tarski @ X79 @ X79) @ X78) = (k1_tarski @ X79))
% 44.44/44.66          | ~ (r2_hidden @ X79 @ X78))),
% 44.44/44.66      inference('simplify', [status(thm)], ['103'])).
% 44.44/44.66  thf('105', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r2_hidden @ (sk_B @ X0) @ X1)
% 44.44/44.66          | ((X0) = (k1_xboole_0))
% 44.44/44.66          | ((k3_xboole_0 @ (k2_tarski @ (sk_B @ X0) @ (sk_B @ X0)) @ 
% 44.44/44.66              (k5_xboole_0 @ X1 @ X0)) = (k1_tarski @ (sk_B @ X0))))),
% 44.44/44.66      inference('sup-', [status(thm)], ['102', '104'])).
% 44.44/44.66  thf('106', plain,
% 44.44/44.66      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 44.44/44.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 44.44/44.66  thf('107', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((r2_hidden @ (sk_B @ X0) @ X1)
% 44.44/44.66          | ((X0) = (k1_xboole_0))
% 44.44/44.66          | ((k3_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ (k5_xboole_0 @ X1 @ X0))
% 44.44/44.66              = (k1_tarski @ (sk_B @ X0))))),
% 44.44/44.66      inference('demod', [status(thm)], ['105', '106'])).
% 44.44/44.66  thf('108', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((k3_xboole_0 @ (k1_tarski @ X0) @ 
% 44.44/44.66            (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 44.44/44.66            = (k1_tarski @ (sk_B @ (k1_tarski @ X0))))
% 44.44/44.66          | ((k1_tarski @ X0) = (k1_xboole_0))
% 44.44/44.66          | (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ X1))),
% 44.44/44.66      inference('sup+', [status(thm)], ['99', '107'])).
% 44.44/44.66  thf(commutativity_k5_xboole_0, axiom,
% 44.44/44.66    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 44.44/44.66  thf('109', plain,
% 44.44/44.66      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 44.44/44.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.44/44.66  thf('110', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 44.44/44.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 44.44/44.66  thf('111', plain,
% 44.44/44.66      (![X27 : $i, X28 : $i, X29 : $i]:
% 44.44/44.66         ((k5_xboole_0 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X29))
% 44.44/44.66           = (k3_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29))),
% 44.44/44.66      inference('cnf', [status(esa)], [t112_xboole_1])).
% 44.44/44.66  thf('112', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 44.44/44.66           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['110', '111'])).
% 44.44/44.66  thf('113', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.44/44.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.44/44.66  thf('114', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 44.44/44.66           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 44.44/44.66      inference('demod', [status(thm)], ['112', '113'])).
% 44.44/44.66  thf('115', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X0 @ X1)
% 44.44/44.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['16', '17'])).
% 44.44/44.66  thf('116', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X1 @ X0)
% 44.44/44.66           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['114', '115'])).
% 44.44/44.66  thf('117', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X0 @ X1)
% 44.44/44.66           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.44/44.66      inference('sup+', [status(thm)], ['109', '116'])).
% 44.44/44.66  thf('118', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 44.44/44.66      inference('clc', [status(thm)], ['97', '98'])).
% 44.44/44.66  thf('119', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 44.44/44.66      inference('clc', [status(thm)], ['97', '98'])).
% 44.44/44.66  thf('120', plain,
% 44.44/44.66      (![X0 : $i, X1 : $i]:
% 44.44/44.66         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 44.44/44.66          | ((k1_tarski @ X0) = (k1_xboole_0))
% 44.44/44.66          | (r2_hidden @ X0 @ X1))),
% 44.44/44.66      inference('demod', [status(thm)], ['108', '117', '118', '119'])).
% 44.44/44.66  thf('121', plain,
% 44.44/44.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 44.44/44.66      inference('simpl_trail', [status(thm)], ['1', '67'])).
% 44.44/44.66  thf('122', plain,
% 44.44/44.66      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 44.44/44.66        | (r2_hidden @ sk_A @ sk_B_1)
% 44.44/44.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 44.44/44.66      inference('sup-', [status(thm)], ['120', '121'])).
% 44.44/44.66  thf('123', plain,
% 44.44/44.66      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 44.44/44.66      inference('simplify', [status(thm)], ['122'])).
% 44.44/44.66  thf('124', plain,
% 44.44/44.66      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 44.44/44.66      inference('split', [status(esa)], ['2'])).
% 44.44/44.66  thf('125', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 44.44/44.66      inference('sat_resolution*', [status(thm)], ['3', '65'])).
% 44.44/44.66  thf('126', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 44.44/44.66      inference('simpl_trail', [status(thm)], ['124', '125'])).
% 44.44/44.66  thf('127', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 44.44/44.66      inference('clc', [status(thm)], ['123', '126'])).
% 44.44/44.66  thf('128', plain,
% 44.44/44.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.44/44.66      inference('sup-', [status(thm)], ['41', '42'])).
% 44.44/44.66  thf('129', plain,
% 44.44/44.66      (![X25 : $i, X26 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ X25 @ X26)
% 44.44/44.66           = (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X25 @ X26)))),
% 44.44/44.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.44/44.66  thf('130', plain,
% 44.44/44.66      (![X0 : $i]:
% 44.44/44.66         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 44.44/44.66           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 44.44/44.66      inference('sup+', [status(thm)], ['128', '129'])).
% 44.44/44.66  thf('131', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.44/44.66      inference('demod', [status(thm)], ['23', '34'])).
% 44.44/44.66  thf('132', plain,
% 44.44/44.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.44/44.66      inference('demod', [status(thm)], ['130', '131'])).
% 44.44/44.66  thf('133', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 44.44/44.66      inference('clc', [status(thm)], ['123', '126'])).
% 44.44/44.66  thf('134', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 44.44/44.66      inference('demod', [status(thm)], ['68', '127', '132', '133'])).
% 44.44/44.66  thf('135', plain, ($false), inference('simplify', [status(thm)], ['134'])).
% 44.44/44.66  
% 44.44/44.66  % SZS output end Refutation
% 44.44/44.66  
% 44.44/44.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
