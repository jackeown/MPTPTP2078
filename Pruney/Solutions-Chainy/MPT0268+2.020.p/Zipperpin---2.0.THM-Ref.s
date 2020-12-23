%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fk09w30QXI

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:54 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 412 expanded)
%              Number of leaves         :   30 ( 137 expanded)
%              Depth                    :   21
%              Number of atoms          :  959 (3242 expanded)
%              Number of equality atoms :   87 ( 315 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
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

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('34',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','84'])).

thf('86',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('93',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','66'])).

thf('95',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('99',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','92','93','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fk09w30QXI
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.80/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.03  % Solved by: fo/fo7.sh
% 0.80/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.03  % done 1330 iterations in 0.570s
% 0.80/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.03  % SZS output start Refutation
% 0.80/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.80/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.80/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.80/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.80/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.80/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.80/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.80/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.80/1.03  thf(t65_zfmisc_1, conjecture,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.80/1.03       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.80/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.03    (~( ![A:$i,B:$i]:
% 0.80/1.03        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.80/1.03          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.80/1.03    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.80/1.03  thf('0', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)
% 0.80/1.03        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('1', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['0'])).
% 0.80/1.03  thf('2', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['0'])).
% 0.80/1.03  thf(l27_zfmisc_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.80/1.03  thf('3', plain,
% 0.80/1.03      (![X53 : $i, X54 : $i]:
% 0.80/1.03         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 0.80/1.03      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.80/1.03  thf(t7_xboole_0, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.80/1.03          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.80/1.03  thf('4', plain,
% 0.80/1.03      (![X13 : $i]:
% 0.80/1.03         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.80/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.80/1.03  thf(idempotence_k3_xboole_0, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.80/1.03  thf('5', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.80/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/1.03  thf(t4_xboole_0, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.80/1.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.80/1.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.80/1.03            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.80/1.03  thf('6', plain,
% 0.80/1.03      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.80/1.03          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf('7', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['5', '6'])).
% 0.80/1.03  thf('8', plain,
% 0.80/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['4', '7'])).
% 0.80/1.03  thf('9', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.80/1.03          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['3', '8'])).
% 0.80/1.03  thf('10', plain,
% 0.80/1.03      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.80/1.03        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('11', plain,
% 0.80/1.03      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('split', [status(esa)], ['10'])).
% 0.80/1.03  thf(d5_xboole_0, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i]:
% 0.80/1.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.80/1.03       ( ![D:$i]:
% 0.80/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.80/1.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.80/1.03  thf('12', plain,
% 0.80/1.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X6 @ X5)
% 0.80/1.03          | ~ (r2_hidden @ X6 @ X4)
% 0.80/1.03          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.80/1.03  thf('13', plain,
% 0.80/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X6 @ X4)
% 0.80/1.03          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['12'])).
% 0.80/1.03  thf('14', plain,
% 0.80/1.03      ((![X0 : $i]:
% 0.80/1.03          (~ (r2_hidden @ X0 @ sk_A)
% 0.80/1.03           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1))))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['11', '13'])).
% 0.80/1.03  thf('15', plain,
% 0.80/1.03      (((((k1_tarski @ sk_B_1) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B_1 @ sk_A)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['9', '14'])).
% 0.80/1.03  thf('16', plain,
% 0.80/1.03      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 0.80/1.03             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['2', '15'])).
% 0.80/1.03  thf(t70_enumset1, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.80/1.03  thf('17', plain,
% 0.80/1.03      (![X33 : $i, X34 : $i]:
% 0.80/1.03         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.80/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.80/1.03  thf(d1_enumset1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.80/1.03       ( ![E:$i]:
% 0.80/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.80/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.80/1.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.80/1.03  thf(zf_stmt_2, axiom,
% 0.80/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.80/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.80/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.80/1.03  thf(zf_stmt_3, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.80/1.03       ( ![E:$i]:
% 0.80/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.80/1.03  thf('18', plain,
% 0.80/1.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.80/1.03         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.80/1.03          | (r2_hidden @ X25 @ X29)
% 0.80/1.03          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.80/1.03  thf('19', plain,
% 0.80/1.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.80/1.03         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 0.80/1.03          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 0.80/1.03      inference('simplify', [status(thm)], ['18'])).
% 0.80/1.03  thf('20', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.80/1.03          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.80/1.03      inference('sup+', [status(thm)], ['17', '19'])).
% 0.80/1.03  thf('21', plain,
% 0.80/1.03      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.80/1.03         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.80/1.03  thf('22', plain,
% 0.80/1.03      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.80/1.03         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 0.80/1.03      inference('simplify', [status(thm)], ['21'])).
% 0.80/1.03  thf('23', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '22'])).
% 0.80/1.03  thf(t69_enumset1, axiom,
% 0.80/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.80/1.03  thf('24', plain,
% 0.80/1.03      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.80/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/1.03  thf('25', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.80/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/1.03  thf('26', plain,
% 0.80/1.03      (![X53 : $i, X54 : $i]:
% 0.80/1.03         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 0.80/1.03      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.80/1.03  thf('27', plain,
% 0.80/1.03      (![X9 : $i, X10 : $i]:
% 0.80/1.03         ((r1_xboole_0 @ X9 @ X10)
% 0.80/1.03          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.80/1.03  thf('28', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.03  thf('29', plain,
% 0.80/1.03      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.80/1.03          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf('30', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.80/1.03          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['28', '29'])).
% 0.80/1.03  thf('31', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['27', '30'])).
% 0.80/1.03  thf('32', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['26', '31'])).
% 0.80/1.03  thf('33', plain,
% 0.80/1.03      (![X13 : $i]:
% 0.80/1.03         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.80/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.80/1.03  thf('34', plain,
% 0.80/1.03      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.80/1.03          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf('35', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.80/1.03  thf('36', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r2_hidden @ X0 @ X1)
% 0.80/1.03          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['32', '35'])).
% 0.80/1.03  thf(t100_xboole_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/1.03  thf('37', plain,
% 0.80/1.03      (![X14 : $i, X15 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X14 @ X15)
% 0.80/1.03           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.03  thf('38', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.80/1.03            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.80/1.03          | (r2_hidden @ X0 @ X1))),
% 0.80/1.03      inference('sup+', [status(thm)], ['36', '37'])).
% 0.80/1.03  thf('39', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.80/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/1.03  thf('40', plain,
% 0.80/1.03      (![X14 : $i, X15 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X14 @ X15)
% 0.80/1.03           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.03  thf('41', plain,
% 0.80/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['39', '40'])).
% 0.80/1.03  thf(t48_xboole_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.80/1.03  thf('42', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.80/1.03           = (k3_xboole_0 @ X16 @ X17))),
% 0.80/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/1.03  thf('43', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.80/1.03           = (k3_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['41', '42'])).
% 0.80/1.03  thf('44', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.80/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/1.03  thf('45', plain,
% 0.80/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['43', '44'])).
% 0.80/1.03  thf('46', plain,
% 0.80/1.03      (![X13 : $i]:
% 0.80/1.03         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.80/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.80/1.03  thf('47', plain,
% 0.80/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['39', '40'])).
% 0.80/1.03  thf('48', plain,
% 0.80/1.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X6 @ X5)
% 0.80/1.03          | (r2_hidden @ X6 @ X3)
% 0.80/1.03          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.80/1.03  thf('49', plain,
% 0.80/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.80/1.03         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['48'])).
% 0.80/1.03  thf('50', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['47', '49'])).
% 0.80/1.03  thf('51', plain,
% 0.80/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['39', '40'])).
% 0.80/1.03  thf('52', plain,
% 0.80/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X6 @ X4)
% 0.80/1.03          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['12'])).
% 0.80/1.03  thf('53', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.80/1.03          | ~ (r2_hidden @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['51', '52'])).
% 0.80/1.03  thf('54', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('clc', [status(thm)], ['50', '53'])).
% 0.80/1.03  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['46', '54'])).
% 0.80/1.03  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['45', '55'])).
% 0.80/1.03  thf('57', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.80/1.03           = (k3_xboole_0 @ X16 @ X17))),
% 0.80/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/1.03  thf('58', plain,
% 0.80/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['56', '57'])).
% 0.80/1.03  thf('59', plain,
% 0.80/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['39', '40'])).
% 0.80/1.03  thf('60', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['46', '54'])).
% 0.80/1.03  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.03      inference('demod', [status(thm)], ['59', '60'])).
% 0.80/1.03  thf('62', plain,
% 0.80/1.03      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.03      inference('demod', [status(thm)], ['58', '61'])).
% 0.80/1.03  thf('63', plain,
% 0.80/1.03      (![X14 : $i, X15 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X14 @ X15)
% 0.80/1.03           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.03  thf('64', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['62', '63'])).
% 0.80/1.03  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['45', '55'])).
% 0.80/1.03  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['64', '65'])).
% 0.80/1.03  thf('67', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.80/1.03          | (r2_hidden @ X0 @ X1))),
% 0.80/1.03      inference('demod', [status(thm)], ['38', '66'])).
% 0.80/1.03  thf('68', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.80/1.03           = (k3_xboole_0 @ X16 @ X17))),
% 0.80/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/1.03  thf('69', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.80/1.03           = (k3_xboole_0 @ X16 @ X17))),
% 0.80/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/1.03  thf('70', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.80/1.03           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['68', '69'])).
% 0.80/1.03  thf('71', plain,
% 0.80/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X6 @ X4)
% 0.80/1.03          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['12'])).
% 0.80/1.03  thf('72', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.80/1.03          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['70', '71'])).
% 0.80/1.03  thf('73', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X0))
% 0.80/1.03          | (r2_hidden @ X1 @ X0)
% 0.80/1.03          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['67', '72'])).
% 0.80/1.03  thf('74', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.80/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/1.03  thf('75', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ X0)
% 0.80/1.03          | (r2_hidden @ X1 @ X0)
% 0.80/1.03          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.80/1.03      inference('demod', [status(thm)], ['73', '74'])).
% 0.80/1.03  thf('76', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.80/1.03           = (k3_xboole_0 @ X16 @ X17))),
% 0.80/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/1.03  thf('77', plain,
% 0.80/1.03      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.80/1.03         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['48'])).
% 0.80/1.03  thf('78', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['76', '77'])).
% 0.80/1.03  thf('79', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.80/1.03          | (r2_hidden @ X1 @ X0))),
% 0.80/1.03      inference('clc', [status(thm)], ['75', '78'])).
% 0.80/1.03  thf('80', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.80/1.03          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['25', '79'])).
% 0.80/1.03  thf('81', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.80/1.03          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['24', '80'])).
% 0.80/1.03  thf('82', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['23', '81'])).
% 0.80/1.03  thf('83', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['5', '6'])).
% 0.80/1.03  thf('84', plain,
% 0.80/1.03      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['82', '83'])).
% 0.80/1.03  thf('85', plain,
% 0.80/1.03      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 0.80/1.03             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['16', '84'])).
% 0.80/1.03  thf('86', plain,
% 0.80/1.03      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 0.80/1.03             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['2', '15'])).
% 0.80/1.03  thf('87', plain,
% 0.80/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['39', '40'])).
% 0.80/1.03  thf(t79_xboole_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.80/1.03  thf('88', plain,
% 0.80/1.03      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.80/1.03      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.80/1.03  thf('89', plain, (![X0 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.80/1.03      inference('sup+', [status(thm)], ['87', '88'])).
% 0.80/1.03  thf('90', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['46', '54'])).
% 0.80/1.03  thf('91', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.80/1.03      inference('demod', [status(thm)], ['89', '90'])).
% 0.80/1.03  thf('92', plain,
% 0.80/1.03      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('demod', [status(thm)], ['85', '86', '91'])).
% 0.80/1.03  thf('93', plain,
% 0.80/1.03      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['10'])).
% 0.80/1.03  thf('94', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.80/1.03          | (r2_hidden @ X0 @ X1))),
% 0.80/1.03      inference('demod', [status(thm)], ['38', '66'])).
% 0.80/1.03  thf('95', plain,
% 0.80/1.03      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 0.80/1.03         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('split', [status(esa)], ['0'])).
% 0.80/1.03  thf('96', plain,
% 0.80/1.03      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A)))
% 0.80/1.03         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['94', '95'])).
% 0.80/1.03  thf('97', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A))
% 0.80/1.03         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('simplify', [status(thm)], ['96'])).
% 0.80/1.03  thf('98', plain,
% 0.80/1.03      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['10'])).
% 0.80/1.03  thf('99', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['97', '98'])).
% 0.80/1.03  thf('100', plain, ($false),
% 0.80/1.03      inference('sat_resolution*', [status(thm)], ['1', '92', '93', '99'])).
% 0.80/1.03  
% 0.80/1.03  % SZS output end Refutation
% 0.80/1.03  
% 0.80/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
