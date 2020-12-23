%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Om0PvYPti6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:30 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 861 expanded)
%              Number of leaves         :   30 ( 268 expanded)
%              Depth                    :   34
%              Number of atoms          : 1547 (8012 expanded)
%              Number of equality atoms :  223 (1268 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( r1_xboole_0 @ X12 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('21',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

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

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','40'])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('45',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('50',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('57',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['44','46','58'])).

thf('60',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['43','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['41','60'])).

thf('62',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('64',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('65',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('74',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('76',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('79',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('91',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('99',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('100',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','67'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['89','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','123'])).

thf('125',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k5_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['89','117'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('131',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['126','129','130'])).

thf('132',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','131'])).

thf('133',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('135',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','139'])).

thf('141',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','140'])).

thf('142',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('143',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('145',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['43','59'])).

thf('150',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('151',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('152',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_B )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('157',plain,
    ( ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('159',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('160',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('161',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','67'])).

thf('162',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158','159','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('165',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( ( k1_tarski @ sk_A )
        = sk_C_1 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['43','59'])).

thf('167',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('169',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('170',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf('171',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('173',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('175',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('177',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('179',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ X0 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ! [X0: $i] :
        ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','179'])).

thf('181',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['167','180'])).

thf('182',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('183',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['181','182'])).

thf('184',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['150','183'])).

thf('185',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['148','149','184'])).

thf('186',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['68','185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['61','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Om0PvYPti6
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.11  % Solved by: fo/fo7.sh
% 0.92/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.11  % done 1884 iterations in 0.651s
% 0.92/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.11  % SZS output start Refutation
% 0.92/1.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.92/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.92/1.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.92/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.92/1.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.92/1.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.92/1.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.92/1.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.92/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.92/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.11  thf(t43_zfmisc_1, conjecture,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.92/1.11          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.11          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.11          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.92/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.11        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.92/1.11             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.11             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.11             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.92/1.11    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.92/1.11  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(l13_xboole_0, axiom,
% 0.92/1.11    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.92/1.11  thf('1', plain,
% 0.92/1.11      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf(t95_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( k3_xboole_0 @ A @ B ) =
% 0.92/1.11       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.92/1.11  thf('2', plain,
% 0.92/1.11      (![X22 : $i, X23 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ X22 @ X23)
% 0.92/1.11           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.92/1.11              (k2_xboole_0 @ X22 @ X23)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.92/1.11  thf(t91_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.92/1.11       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.92/1.11  thf('3', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.92/1.11           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.92/1.11  thf('4', plain,
% 0.92/1.11      (![X22 : $i, X23 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ X22 @ X23)
% 0.92/1.11           = (k5_xboole_0 @ X22 @ 
% 0.92/1.11              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.92/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.92/1.11  thf(commutativity_k5_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.92/1.11  thf('5', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.92/1.11  thf(t5_boole, axiom,
% 0.92/1.11    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.92/1.11  thf('6', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.92/1.11      inference('cnf', [status(esa)], [t5_boole])).
% 0.92/1.11  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('8', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['4', '7'])).
% 0.92/1.11  thf(t92_xboole_1, axiom,
% 0.92/1.11    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.92/1.11  thf('9', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.92/1.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.92/1.11  thf('10', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.92/1.11           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.92/1.11  thf('11', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['9', '10'])).
% 0.92/1.11  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('13', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['11', '12'])).
% 0.92/1.11  thf('14', plain,
% 0.92/1.11      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf('15', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.92/1.11      inference('cnf', [status(esa)], [t5_boole])).
% 0.92/1.11  thf('16', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['14', '15'])).
% 0.92/1.11  thf('17', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((X0) = (X1)) | ~ (v1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['13', '16'])).
% 0.92/1.11  thf('18', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.92/1.11          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['8', '17'])).
% 0.92/1.11  thf(t17_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.92/1.11  thf('19', plain,
% 0.92/1.11      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.92/1.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.92/1.11  thf(t66_xboole_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.92/1.11       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.92/1.11  thf('20', plain,
% 0.92/1.11      (![X12 : $i]: ((r1_xboole_0 @ X12 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.92/1.11  thf('21', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('simplify', [status(thm)], ['20'])).
% 0.92/1.11  thf(t3_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.92/1.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.92/1.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.92/1.11            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.92/1.11  thf('22', plain,
% 0.92/1.11      (![X5 : $i, X6 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.92/1.11  thf('23', plain,
% 0.92/1.11      (![X5 : $i, X6 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.92/1.11  thf('24', plain,
% 0.92/1.11      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.92/1.11         (~ (r2_hidden @ X7 @ X5)
% 0.92/1.11          | ~ (r2_hidden @ X7 @ X8)
% 0.92/1.11          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.92/1.11  thf('25', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X0 @ X1)
% 0.92/1.11          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.92/1.11          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.92/1.11      inference('sup-', [status(thm)], ['23', '24'])).
% 0.92/1.11  thf('26', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X0 @ X1)
% 0.92/1.11          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.92/1.11          | (r1_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('sup-', [status(thm)], ['22', '25'])).
% 0.92/1.11  thf('27', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('simplify', [status(thm)], ['26'])).
% 0.92/1.11  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.92/1.11      inference('sup-', [status(thm)], ['21', '27'])).
% 0.92/1.11  thf('29', plain,
% 0.92/1.11      (![X5 : $i, X6 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.92/1.11  thf('30', plain,
% 0.92/1.11      (![X5 : $i, X6 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.92/1.11  thf('31', plain,
% 0.92/1.11      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.92/1.11         (~ (r2_hidden @ X7 @ X5)
% 0.92/1.11          | ~ (r2_hidden @ X7 @ X8)
% 0.92/1.11          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.92/1.11  thf('32', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X1 @ X0)
% 0.92/1.11          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.92/1.11          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.92/1.11      inference('sup-', [status(thm)], ['30', '31'])).
% 0.92/1.11  thf('33', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X0 @ X1)
% 0.92/1.11          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.92/1.11          | (r1_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('sup-', [status(thm)], ['29', '32'])).
% 0.92/1.11  thf('34', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('simplify', [status(thm)], ['33'])).
% 0.92/1.11  thf('35', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.92/1.11      inference('sup-', [status(thm)], ['28', '34'])).
% 0.92/1.11  thf(t69_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.92/1.11       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.92/1.11  thf('36', plain,
% 0.92/1.11      (![X14 : $i, X15 : $i]:
% 0.92/1.11         (~ (r1_xboole_0 @ X14 @ X15)
% 0.92/1.11          | ~ (r1_tarski @ X14 @ X15)
% 0.92/1.11          | (v1_xboole_0 @ X14))),
% 0.92/1.11      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.92/1.11  thf('37', plain,
% 0.92/1.11      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['35', '36'])).
% 0.92/1.11  thf('38', plain,
% 0.92/1.11      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['19', '37'])).
% 0.92/1.11  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('demod', [status(thm)], ['18', '38'])).
% 0.92/1.11  thf('40', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['1', '39'])).
% 0.92/1.11  thf('41', plain,
% 0.92/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B))),
% 0.92/1.11      inference('sup+', [status(thm)], ['0', '40'])).
% 0.92/1.11  thf('42', plain,
% 0.92/1.11      ((((sk_B) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('43', plain,
% 0.92/1.11      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.92/1.11         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('split', [status(esa)], ['42'])).
% 0.92/1.11  thf('44', plain,
% 0.92/1.11      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('split', [status(esa)], ['42'])).
% 0.92/1.11  thf('45', plain,
% 0.92/1.11      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('46', plain,
% 0.92/1.11      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('split', [status(esa)], ['45'])).
% 0.92/1.11  thf('47', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(t7_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.92/1.11  thf('48', plain,
% 0.92/1.11      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.92/1.11      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.92/1.11  thf('49', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.92/1.11      inference('sup+', [status(thm)], ['47', '48'])).
% 0.92/1.11  thf(l3_zfmisc_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.92/1.11       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.92/1.11  thf('50', plain,
% 0.92/1.11      (![X52 : $i, X53 : $i]:
% 0.92/1.11         (((X53) = (k1_tarski @ X52))
% 0.92/1.11          | ((X53) = (k1_xboole_0))
% 0.92/1.11          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.92/1.11      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.92/1.11  thf('51', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['49', '50'])).
% 0.92/1.11  thf('52', plain,
% 0.92/1.11      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('53', plain,
% 0.92/1.11      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('split', [status(esa)], ['52'])).
% 0.92/1.11  thf('54', plain,
% 0.92/1.11      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['51', '53'])).
% 0.92/1.11  thf('55', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('56', plain,
% 0.92/1.11      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.92/1.11      inference('split', [status(esa)], ['42'])).
% 0.92/1.11  thf('57', plain,
% 0.92/1.11      ((((sk_B) != (sk_B)))
% 0.92/1.11         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['55', '56'])).
% 0.92/1.11  thf('58', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('simplify', [status(thm)], ['57'])).
% 0.92/1.11  thf('59', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('sat_resolution*', [status(thm)], ['44', '46', '58'])).
% 0.92/1.11  thf('60', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.92/1.11      inference('simpl_trail', [status(thm)], ['43', '59'])).
% 0.92/1.11  thf('61', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.92/1.11      inference('simplify_reflect-', [status(thm)], ['41', '60'])).
% 0.92/1.11  thf('62', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('simplify', [status(thm)], ['20'])).
% 0.92/1.11  thf('63', plain,
% 0.92/1.11      (![X14 : $i, X15 : $i]:
% 0.92/1.11         (~ (r1_xboole_0 @ X14 @ X15)
% 0.92/1.11          | ~ (r1_tarski @ X14 @ X15)
% 0.92/1.11          | (v1_xboole_0 @ X14))),
% 0.92/1.11      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.92/1.11  thf('64', plain,
% 0.92/1.11      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['62', '63'])).
% 0.92/1.11  thf(idempotence_k2_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.92/1.11  thf('65', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.92/1.11      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.92/1.11  thf('66', plain,
% 0.92/1.11      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.92/1.11      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.92/1.11  thf('67', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.92/1.11      inference('sup+', [status(thm)], ['65', '66'])).
% 0.92/1.11  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('demod', [status(thm)], ['64', '67'])).
% 0.92/1.11  thf('69', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('70', plain,
% 0.92/1.11      (![X22 : $i, X23 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ X22 @ X23)
% 0.92/1.11           = (k5_xboole_0 @ X22 @ 
% 0.92/1.11              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.92/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.92/1.11  thf('71', plain,
% 0.92/1.11      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 0.92/1.11         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup+', [status(thm)], ['69', '70'])).
% 0.92/1.11  thf('72', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.92/1.11  thf('73', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['49', '50'])).
% 0.92/1.11  thf(t69_enumset1, axiom,
% 0.92/1.11    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.92/1.11  thf('74', plain,
% 0.92/1.11      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.92/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.92/1.11  thf('75', plain,
% 0.92/1.11      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.92/1.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.92/1.11  thf('76', plain,
% 0.92/1.11      (![X52 : $i, X53 : $i]:
% 0.92/1.11         (((X53) = (k1_tarski @ X52))
% 0.92/1.11          | ((X53) = (k1_xboole_0))
% 0.92/1.11          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.92/1.11      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.92/1.11  thf('77', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.92/1.11          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['75', '76'])).
% 0.92/1.11  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('79', plain,
% 0.92/1.11      (![X22 : $i, X23 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ X22 @ X23)
% 0.92/1.11           = (k5_xboole_0 @ X22 @ 
% 0.92/1.11              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.92/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.92/1.11  thf('80', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['78', '79'])).
% 0.92/1.11  thf('81', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['11', '12'])).
% 0.92/1.11  thf('82', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['80', '81'])).
% 0.92/1.11  thf('83', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.92/1.11            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.92/1.11          | ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['77', '82'])).
% 0.92/1.11  thf('84', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.92/1.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.92/1.11  thf('85', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.92/1.11          | ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['83', '84'])).
% 0.92/1.11  thf('86', plain,
% 0.92/1.11      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.92/1.11      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.92/1.11  thf('87', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.92/1.11          | ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['85', '86'])).
% 0.92/1.11  thf('88', plain,
% 0.92/1.11      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['35', '36'])).
% 0.92/1.11  thf('89', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.92/1.11          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['87', '88'])).
% 0.92/1.11  thf('90', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['78', '79'])).
% 0.92/1.11  thf('91', plain,
% 0.92/1.11      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('93', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((k5_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['91', '92'])).
% 0.92/1.11  thf('94', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['90', '93'])).
% 0.92/1.11  thf('95', plain,
% 0.92/1.11      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf('96', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['4', '7'])).
% 0.92/1.11  thf('97', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((k5_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['91', '92'])).
% 0.92/1.11  thf('98', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['96', '97'])).
% 0.92/1.11  thf(idempotence_k3_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.92/1.11  thf('99', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.92/1.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.92/1.11  thf('100', plain,
% 0.92/1.11      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf('101', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.92/1.11          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['8', '17'])).
% 0.92/1.11  thf('102', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0)
% 0.92/1.11          | ((k2_xboole_0 @ k1_xboole_0 @ X1) = (X1)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['100', '101'])).
% 0.92/1.11  thf('103', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v1_xboole_0 @ X0)
% 0.92/1.11          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['99', '102'])).
% 0.92/1.11  thf('104', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('simplify', [status(thm)], ['103'])).
% 0.92/1.11  thf('105', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (X0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0)
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['98', '104'])).
% 0.92/1.11  thf('106', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 0.92/1.11      inference('simplify', [status(thm)], ['105'])).
% 0.92/1.11  thf('107', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['4', '7'])).
% 0.92/1.11  thf('108', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['11', '12'])).
% 0.92/1.11  thf('109', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['107', '108'])).
% 0.92/1.11  thf('110', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['106', '109'])).
% 0.92/1.11  thf('111', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.92/1.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.92/1.11  thf('112', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('demod', [status(thm)], ['110', '111'])).
% 0.92/1.11  thf('113', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0)
% 0.92/1.11          | ~ (v1_xboole_0 @ X1))),
% 0.92/1.11      inference('sup+', [status(thm)], ['95', '112'])).
% 0.92/1.11  thf('114', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0)
% 0.92/1.11          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['94', '113'])).
% 0.92/1.11  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('demod', [status(thm)], ['64', '67'])).
% 0.92/1.11  thf('116', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.92/1.11          | ~ (v1_xboole_0 @ X0)
% 0.92/1.11          | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('demod', [status(thm)], ['114', '115'])).
% 0.92/1.11  thf('117', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v1_xboole_0 @ X0)
% 0.92/1.11          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.92/1.11      inference('simplify', [status(thm)], ['116'])).
% 0.92/1.11  thf('118', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('clc', [status(thm)], ['89', '117'])).
% 0.92/1.11  thf('119', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['80', '81'])).
% 0.92/1.11  thf('120', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.92/1.11           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['118', '119'])).
% 0.92/1.11  thf('121', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.92/1.11  thf('122', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('123', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_tarski @ X0))),
% 0.92/1.11      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.92/1.11  thf('124', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0)
% 0.92/1.11           = (k1_tarski @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['74', '123'])).
% 0.92/1.11  thf('125', plain,
% 0.92/1.11      (![X22 : $i, X23 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ X22 @ X23)
% 0.92/1.11           = (k5_xboole_0 @ X22 @ 
% 0.92/1.11              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.92/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.92/1.11  thf('126', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0)
% 0.92/1.11           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.92/1.11              (k5_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))))),
% 0.92/1.11      inference('sup+', [status(thm)], ['124', '125'])).
% 0.92/1.11  thf('127', plain,
% 0.92/1.11      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.92/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.92/1.11  thf('128', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('clc', [status(thm)], ['89', '117'])).
% 0.92/1.11  thf('129', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['127', '128'])).
% 0.92/1.11  thf('130', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('131', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k1_xboole_0)
% 0.92/1.11           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['126', '129', '130'])).
% 0.92/1.11  thf('132', plain,
% 0.92/1.11      ((((k1_xboole_0) = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B))
% 0.92/1.11        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['73', '131'])).
% 0.92/1.11  thf('133', plain,
% 0.92/1.11      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.92/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.92/1.11  thf('134', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.92/1.11  thf('135', plain,
% 0.92/1.11      ((((k1_xboole_0) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.92/1.11        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.92/1.11  thf('136', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.92/1.11           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.92/1.11  thf('137', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.11            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))
% 0.92/1.11          | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['135', '136'])).
% 0.92/1.11  thf('138', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('139', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((X0)
% 0.92/1.11            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))
% 0.92/1.11          | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['137', '138'])).
% 0.92/1.11  thf('140', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((X0)
% 0.92/1.11            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))))
% 0.92/1.11          | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['72', '139'])).
% 0.92/1.11  thf('141', plain,
% 0.92/1.11      ((((sk_C_1) = (k3_xboole_0 @ sk_B @ sk_C_1)) | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['71', '140'])).
% 0.92/1.11  thf('142', plain,
% 0.92/1.11      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.92/1.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.92/1.11  thf('143', plain, (((r1_tarski @ sk_C_1 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['141', '142'])).
% 0.92/1.11  thf('144', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['49', '50'])).
% 0.92/1.11  thf('145', plain,
% 0.92/1.11      (![X52 : $i, X53 : $i]:
% 0.92/1.11         (((X53) = (k1_tarski @ X52))
% 0.92/1.11          | ((X53) = (k1_xboole_0))
% 0.92/1.11          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.92/1.11      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.92/1.11  thf('146', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (r1_tarski @ X0 @ sk_B)
% 0.92/1.11          | ((sk_B) = (k1_xboole_0))
% 0.92/1.11          | ((X0) = (k1_xboole_0))
% 0.92/1.11          | ((X0) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['144', '145'])).
% 0.92/1.11  thf('147', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))
% 0.92/1.11        | ((sk_C_1) = (k1_tarski @ sk_A))
% 0.92/1.11        | ((sk_C_1) = (k1_xboole_0))
% 0.92/1.11        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['143', '146'])).
% 0.92/1.11  thf('148', plain,
% 0.92/1.11      ((((sk_C_1) = (k1_xboole_0))
% 0.92/1.11        | ((sk_C_1) = (k1_tarski @ sk_A))
% 0.92/1.11        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('simplify', [status(thm)], ['147'])).
% 0.92/1.11  thf('149', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.92/1.11      inference('simpl_trail', [status(thm)], ['43', '59'])).
% 0.92/1.11  thf('150', plain,
% 0.92/1.11      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.92/1.11      inference('split', [status(esa)], ['52'])).
% 0.92/1.11  thf('151', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('152', plain,
% 0.92/1.11      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf('153', plain,
% 0.92/1.11      ((![X0 : $i]: (((X0) = (sk_B)) | ~ (v1_xboole_0 @ X0)))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup+', [status(thm)], ['151', '152'])).
% 0.92/1.11  thf('154', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('155', plain,
% 0.92/1.11      ((![X0 : $i]:
% 0.92/1.11          (((k1_tarski @ sk_A) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.92/1.11           | ~ (v1_xboole_0 @ X0)))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup+', [status(thm)], ['153', '154'])).
% 0.92/1.11  thf('156', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['4', '7'])).
% 0.92/1.11  thf('157', plain,
% 0.92/1.11      (((((k3_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 0.92/1.11           = (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.92/1.11         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup+', [status(thm)], ['155', '156'])).
% 0.92/1.11  thf('158', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('159', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('160', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('161', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('demod', [status(thm)], ['64', '67'])).
% 0.92/1.11  thf('162', plain,
% 0.92/1.11      (((v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup+', [status(thm)], ['160', '161'])).
% 0.92/1.11  thf('163', plain,
% 0.92/1.11      ((((k3_xboole_0 @ sk_B @ sk_C_1)
% 0.92/1.11          = (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('demod', [status(thm)], ['157', '158', '159', '162'])).
% 0.92/1.11  thf('164', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (((X0) = (X1)) | ~ (v1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['13', '16'])).
% 0.92/1.11  thf('165', plain,
% 0.92/1.11      (((~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 0.92/1.11         | ((k1_tarski @ sk_A) = (sk_C_1))))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['163', '164'])).
% 0.92/1.11  thf('166', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.92/1.11      inference('simpl_trail', [status(thm)], ['43', '59'])).
% 0.92/1.11  thf('167', plain,
% 0.92/1.11      ((~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1)))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 0.92/1.11  thf('168', plain,
% 0.92/1.11      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.92/1.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.92/1.11  thf('169', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('170', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('simplify', [status(thm)], ['20'])).
% 0.92/1.11  thf('171', plain,
% 0.92/1.11      (((r1_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup+', [status(thm)], ['169', '170'])).
% 0.92/1.11  thf('172', plain,
% 0.92/1.11      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('173', plain,
% 0.92/1.11      (((r1_xboole_0 @ sk_B @ sk_B)) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('demod', [status(thm)], ['171', '172'])).
% 0.92/1.11  thf('174', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('simplify', [status(thm)], ['26'])).
% 0.92/1.11  thf('175', plain,
% 0.92/1.11      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ X0))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['173', '174'])).
% 0.92/1.11  thf('176', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('simplify', [status(thm)], ['33'])).
% 0.92/1.11  thf('177', plain,
% 0.92/1.11      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['175', '176'])).
% 0.92/1.11  thf('178', plain,
% 0.92/1.11      (![X14 : $i, X15 : $i]:
% 0.92/1.11         (~ (r1_xboole_0 @ X14 @ X15)
% 0.92/1.11          | ~ (r1_tarski @ X14 @ X15)
% 0.92/1.11          | (v1_xboole_0 @ X14))),
% 0.92/1.11      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.92/1.11  thf('179', plain,
% 0.92/1.11      ((![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ sk_B)))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['177', '178'])).
% 0.92/1.11  thf('180', plain,
% 0.92/1.11      ((![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0)))
% 0.92/1.11         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['168', '179'])).
% 0.92/1.11  thf('181', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('demod', [status(thm)], ['167', '180'])).
% 0.92/1.11  thf('182', plain,
% 0.92/1.11      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.92/1.11      inference('split', [status(esa)], ['52'])).
% 0.92/1.11  thf('183', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.92/1.11      inference('sat_resolution*', [status(thm)], ['181', '182'])).
% 0.92/1.11  thf('184', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.92/1.11      inference('simpl_trail', [status(thm)], ['150', '183'])).
% 0.92/1.11  thf('185', plain, (((sk_B) = (k1_xboole_0))),
% 0.92/1.11      inference('simplify_reflect-', [status(thm)], ['148', '149', '184'])).
% 0.92/1.11  thf('186', plain, ((v1_xboole_0 @ sk_B)),
% 0.92/1.11      inference('demod', [status(thm)], ['68', '185'])).
% 0.92/1.11  thf('187', plain, ($false), inference('demod', [status(thm)], ['61', '186'])).
% 0.92/1.11  
% 0.92/1.11  % SZS output end Refutation
% 0.92/1.11  
% 0.92/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
