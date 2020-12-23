%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oMRiYRO3dL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:37 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  179 (1869 expanded)
%              Number of leaves         :   28 ( 598 expanded)
%              Depth                    :   27
%              Number of atoms          : 1332 (17868 expanded)
%              Number of equality atoms :  229 (2904 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['18','30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('33',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54
        = ( k1_tarski @ X53 ) )
      | ( X54 = k1_xboole_0 )
      | ~ ( r1_tarski @ X54 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54
        = ( k1_tarski @ X53 ) )
      | ( X54 = k1_xboole_0 )
      | ~ ( r1_tarski @ X54 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('54',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54
        = ( k1_tarski @ X53 ) )
      | ( X54 = k1_xboole_0 )
      | ~ ( r1_tarski @ X54 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('64',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('71',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('72',plain,
    ( ( ( k5_xboole_0 @ sk_C_1 @ sk_B )
      = ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k5_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('78',plain,
    ( ( ( k5_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','78'])).

thf('80',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('84',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
      = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('95',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('97',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['98'])).

thf('101',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('104',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['98'])).

thf('109',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['100','102','110'])).

thf('112',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['99','111'])).

thf('113',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['97','112'])).

thf('114',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['104'])).

thf('115',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('128',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','128'])).

thf('130',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['117','129'])).

thf('131',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['99','111'])).

thf('132',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['104'])).

thf('134',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['132','133'])).

thf('135',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['116','134'])).

thf('136',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['116','134'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k4_xboole_0 @ sk_B @ X2 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['46','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = sk_B ) ),
    inference(condensation,[status(thm)],['137'])).

thf('139',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['17','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('141',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('143',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['132','133'])).

thf('146',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['141','146'])).

thf('148',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['99','111'])).

thf('149',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['147','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oMRiYRO3dL
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:20:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.97/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.17  % Solved by: fo/fo7.sh
% 0.97/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.17  % done 1483 iterations in 0.736s
% 0.97/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.17  % SZS output start Refutation
% 0.97/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.97/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.97/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.97/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.97/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.97/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.97/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.17  thf(t43_zfmisc_1, conjecture,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.97/1.17          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.97/1.17          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.97/1.17          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.97/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.97/1.17        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.97/1.17             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.97/1.17             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.97/1.17             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.97/1.17    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.97/1.17  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(t95_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( k3_xboole_0 @ A @ B ) =
% 0.97/1.17       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.97/1.17  thf('1', plain,
% 0.97/1.17      (![X23 : $i, X24 : $i]:
% 0.97/1.17         ((k3_xboole_0 @ X23 @ X24)
% 0.97/1.17           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.97/1.17              (k2_xboole_0 @ X23 @ X24)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.97/1.17  thf(t91_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.97/1.17       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.97/1.17  thf('2', plain,
% 0.97/1.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.97/1.17           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.97/1.17  thf('3', plain,
% 0.97/1.17      (![X23 : $i, X24 : $i]:
% 0.97/1.17         ((k3_xboole_0 @ X23 @ X24)
% 0.97/1.17           = (k5_xboole_0 @ X23 @ 
% 0.97/1.17              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.97/1.17      inference('demod', [status(thm)], ['1', '2'])).
% 0.97/1.17  thf('4', plain,
% 0.97/1.17      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 0.97/1.17         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('sup+', [status(thm)], ['0', '3'])).
% 0.97/1.17  thf(t92_xboole_1, axiom,
% 0.97/1.17    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.97/1.17  thf('5', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.97/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.97/1.17  thf('6', plain,
% 0.97/1.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.97/1.17           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.97/1.17  thf('7', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['5', '6'])).
% 0.97/1.17  thf('8', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['5', '6'])).
% 0.97/1.17  thf('9', plain,
% 0.97/1.17      (![X23 : $i, X24 : $i]:
% 0.97/1.17         ((k3_xboole_0 @ X23 @ X24)
% 0.97/1.17           = (k5_xboole_0 @ X23 @ 
% 0.97/1.17              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.97/1.17      inference('demod', [status(thm)], ['1', '2'])).
% 0.97/1.17  thf('10', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((k3_xboole_0 @ X0 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['8', '9'])).
% 0.97/1.17  thf(idempotence_k3_xboole_0, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.97/1.17  thf('11', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.97/1.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.97/1.17  thf(idempotence_k2_xboole_0, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.97/1.17  thf('12', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.97/1.17      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.97/1.17  thf('13', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.97/1.17  thf('14', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '13'])).
% 0.97/1.17  thf('15', plain,
% 0.97/1.17      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.97/1.17         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['4', '14'])).
% 0.97/1.17  thf(t100_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.97/1.17  thf('16', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ X10 @ X11)
% 0.97/1.17           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.97/1.17  thf('17', plain,
% 0.97/1.17      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.97/1.17         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.97/1.17      inference('demod', [status(thm)], ['15', '16'])).
% 0.97/1.17  thf(d3_tarski, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( r1_tarski @ A @ B ) <=>
% 0.97/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.97/1.17  thf('18', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('19', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.97/1.17  thf('20', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ X10 @ X11)
% 0.97/1.17           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.97/1.17  thf('21', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('22', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ X10 @ X11)
% 0.97/1.17           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.97/1.17  thf(t1_xboole_0, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.97/1.17       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.97/1.17  thf('23', plain,
% 0.97/1.17      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X6 @ X7)
% 0.97/1.17          | ~ (r2_hidden @ X6 @ X8)
% 0.97/1.17          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.97/1.17  thf('24', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.97/1.17          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.97/1.17          | ~ (r2_hidden @ X2 @ X1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['22', '23'])).
% 0.97/1.17  thf(t36_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.97/1.17  thf('25', plain,
% 0.97/1.17      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.97/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.97/1.17  thf('26', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | (r2_hidden @ X0 @ X2)
% 0.97/1.17          | ~ (r1_tarski @ X1 @ X2))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('27', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['25', '26'])).
% 0.97/1.17  thf('28', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.97/1.17          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('clc', [status(thm)], ['24', '27'])).
% 0.97/1.17  thf('29', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.97/1.17          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['21', '28'])).
% 0.97/1.17  thf('30', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.97/1.17      inference('simplify', [status(thm)], ['29'])).
% 0.97/1.17  thf('31', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X1)),
% 0.97/1.17      inference('sup-', [status(thm)], ['18', '30'])).
% 0.97/1.17  thf(t69_enumset1, axiom,
% 0.97/1.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.97/1.17  thf('32', plain,
% 0.97/1.17      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.97/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.17  thf(l3_zfmisc_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.97/1.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.97/1.17  thf('33', plain,
% 0.97/1.17      (![X53 : $i, X54 : $i]:
% 0.97/1.17         (((X54) = (k1_tarski @ X53))
% 0.97/1.17          | ((X54) = (k1_xboole_0))
% 0.97/1.17          | ~ (r1_tarski @ X54 @ (k1_tarski @ X53)))),
% 0.97/1.17      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.97/1.17  thf('34', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (r1_tarski @ X1 @ (k2_tarski @ X0 @ X0))
% 0.97/1.17          | ((X1) = (k1_xboole_0))
% 0.97/1.17          | ((X1) = (k1_tarski @ X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['32', '33'])).
% 0.97/1.17  thf('35', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_tarski @ X0))
% 0.97/1.17          | ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['31', '34'])).
% 0.97/1.17  thf('36', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_tarski @ X0))
% 0.97/1.17          | ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['31', '34'])).
% 0.97/1.17  thf('37', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((k1_tarski @ X0) = (k1_tarski @ X1))
% 0.97/1.17          | ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 0.97/1.17          | ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['35', '36'])).
% 0.97/1.17  thf('38', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 0.97/1.17          | ((k1_tarski @ X0) = (k1_tarski @ X1)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['37'])).
% 0.97/1.17  thf('39', plain,
% 0.97/1.17      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.97/1.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.17  thf(l51_zfmisc_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.97/1.17  thf('40', plain,
% 0.97/1.17      (![X56 : $i, X57 : $i]:
% 0.97/1.17         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.97/1.17      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.97/1.17  thf('41', plain,
% 0.97/1.17      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['39', '40'])).
% 0.97/1.17  thf('42', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.97/1.17      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.97/1.17  thf('43', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['41', '42'])).
% 0.97/1.17  thf('44', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((k3_tarski @ (k1_tarski @ X0)) = (X1))
% 0.97/1.17          | ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['38', '43'])).
% 0.97/1.17  thf('45', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['41', '42'])).
% 0.97/1.17  thf('46', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((X0) = (X1)) | ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['44', '45'])).
% 0.97/1.17  thf('47', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(t7_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.97/1.17  thf('48', plain,
% 0.97/1.17      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.97/1.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.97/1.17  thf('49', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.97/1.17      inference('sup+', [status(thm)], ['47', '48'])).
% 0.97/1.17  thf('50', plain,
% 0.97/1.17      (![X53 : $i, X54 : $i]:
% 0.97/1.17         (((X54) = (k1_tarski @ X53))
% 0.97/1.17          | ((X54) = (k1_xboole_0))
% 0.97/1.17          | ~ (r1_tarski @ X54 @ (k1_tarski @ X53)))),
% 0.97/1.17      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.97/1.17  thf('51', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['49', '50'])).
% 0.97/1.17  thf('52', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['49', '50'])).
% 0.97/1.17  thf('53', plain,
% 0.97/1.17      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.97/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.97/1.17  thf('54', plain,
% 0.97/1.17      (![X53 : $i, X54 : $i]:
% 0.97/1.17         (((X54) = (k1_tarski @ X53))
% 0.97/1.17          | ((X54) = (k1_xboole_0))
% 0.97/1.17          | ~ (r1_tarski @ X54 @ (k1_tarski @ X53)))),
% 0.97/1.17      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.97/1.17  thf('55', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.97/1.17          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['53', '54'])).
% 0.97/1.17  thf('56', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ X10 @ X11)
% 0.97/1.17           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.97/1.17  thf('57', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '13'])).
% 0.97/1.17  thf('58', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k3_xboole_0 @ X1 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['56', '57'])).
% 0.97/1.17  thf('59', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.97/1.17            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.97/1.17          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['55', '58'])).
% 0.97/1.17  thf('60', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.97/1.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.97/1.17  thf('61', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ X10 @ X11)
% 0.97/1.17           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.97/1.17  thf('62', plain,
% 0.97/1.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['60', '61'])).
% 0.97/1.17  thf('63', plain,
% 0.97/1.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['60', '61'])).
% 0.97/1.17  thf('64', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.97/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.97/1.17  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['63', '64'])).
% 0.97/1.17  thf('66', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.97/1.17          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['59', '62', '65'])).
% 0.97/1.17  thf('67', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.97/1.17          | ((sk_B) = (k1_xboole_0))
% 0.97/1.17          | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ X0) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['52', '66'])).
% 0.97/1.17  thf('68', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.97/1.17          | ((sk_B) = (k1_xboole_0))
% 0.97/1.17          | ((sk_B) = (k1_xboole_0))
% 0.97/1.17          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['51', '67'])).
% 0.97/1.17  thf('69', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.97/1.17          | ((sk_B) = (k1_xboole_0))
% 0.97/1.17          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['68'])).
% 0.97/1.17  thf('70', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['49', '50'])).
% 0.97/1.17  thf('71', plain,
% 0.97/1.17      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.97/1.17         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.97/1.17      inference('demod', [status(thm)], ['15', '16'])).
% 0.97/1.17  thf('72', plain,
% 0.97/1.17      ((((k5_xboole_0 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['70', '71'])).
% 0.97/1.17  thf('73', plain,
% 0.97/1.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.97/1.17           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.97/1.17  thf('74', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.97/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.97/1.17  thf('75', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.97/1.17           = (k1_xboole_0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['73', '74'])).
% 0.97/1.17  thf('76', plain,
% 0.97/1.17      ((((k5_xboole_0 @ sk_C_1 @ 
% 0.97/1.17          (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['72', '75'])).
% 0.97/1.17  thf('77', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k3_xboole_0 @ X1 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['56', '57'])).
% 0.97/1.17  thf('78', plain,
% 0.97/1.17      ((((k5_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.97/1.17  thf('79', plain,
% 0.97/1.17      ((((k5_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.97/1.17        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['69', '78'])).
% 0.97/1.17  thf('80', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.97/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.97/1.17  thf('81', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['5', '6'])).
% 0.97/1.17  thf('82', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['80', '81'])).
% 0.97/1.17  thf('83', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.97/1.17  thf('84', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.17      inference('demod', [status(thm)], ['82', '83'])).
% 0.97/1.17  thf('85', plain,
% 0.97/1.17      ((((sk_C_1) = (k1_xboole_0))
% 0.97/1.17        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['79', '84'])).
% 0.97/1.17  thf('86', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0))
% 0.97/1.17        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))
% 0.97/1.17        | ((sk_C_1) = (k1_xboole_0)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['85'])).
% 0.97/1.17  thf('87', plain,
% 0.97/1.17      (![X23 : $i, X24 : $i]:
% 0.97/1.17         ((k3_xboole_0 @ X23 @ X24)
% 0.97/1.17           = (k5_xboole_0 @ X23 @ 
% 0.97/1.17              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.97/1.17      inference('demod', [status(thm)], ['1', '2'])).
% 0.97/1.17  thf('88', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '13'])).
% 0.97/1.17  thf('89', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.97/1.17           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['87', '88'])).
% 0.97/1.17  thf('90', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((k4_xboole_0 @ X10 @ X11)
% 0.97/1.17           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.97/1.17  thf('91', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.97/1.17           = (k4_xboole_0 @ X1 @ X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['89', '90'])).
% 0.97/1.17  thf('92', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '13'])).
% 0.97/1.17  thf('93', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k2_xboole_0 @ X1 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['91', '92'])).
% 0.97/1.17  thf('94', plain,
% 0.97/1.17      ((((k2_xboole_0 @ sk_B @ sk_C_1) = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))
% 0.97/1.17        | ((sk_C_1) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['86', '93'])).
% 0.97/1.17  thf('95', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('96', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.17      inference('demod', [status(thm)], ['82', '83'])).
% 0.97/1.17  thf('97', plain,
% 0.97/1.17      ((((k1_tarski @ sk_A) = (sk_C_1))
% 0.97/1.17        | ((sk_C_1) = (k1_xboole_0))
% 0.97/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.97/1.17  thf('98', plain,
% 0.97/1.17      ((((sk_B) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('99', plain,
% 0.97/1.17      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.97/1.17         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('split', [status(esa)], ['98'])).
% 0.97/1.17  thf('100', plain,
% 0.97/1.17      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('split', [status(esa)], ['98'])).
% 0.97/1.17  thf('101', plain,
% 0.97/1.17      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('102', plain,
% 0.97/1.17      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('split', [status(esa)], ['101'])).
% 0.97/1.17  thf('103', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['49', '50'])).
% 0.97/1.17  thf('104', plain,
% 0.97/1.17      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('105', plain,
% 0.97/1.17      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('split', [status(esa)], ['104'])).
% 0.97/1.17  thf('106', plain,
% 0.97/1.17      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.97/1.17         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['103', '105'])).
% 0.97/1.17  thf('107', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['106'])).
% 0.97/1.17  thf('108', plain,
% 0.97/1.17      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.97/1.17      inference('split', [status(esa)], ['98'])).
% 0.97/1.17  thf('109', plain,
% 0.97/1.17      ((((sk_B) != (sk_B)))
% 0.97/1.17         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['107', '108'])).
% 0.97/1.17  thf('110', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['109'])).
% 0.97/1.17  thf('111', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['100', '102', '110'])).
% 0.97/1.17  thf('112', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['99', '111'])).
% 0.97/1.17  thf('113', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.97/1.17      inference('simplify_reflect-', [status(thm)], ['97', '112'])).
% 0.97/1.17  thf('114', plain,
% 0.97/1.17      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.97/1.17      inference('split', [status(esa)], ['104'])).
% 0.97/1.17  thf('115', plain,
% 0.97/1.17      (((((sk_C_1) != (sk_C_1)) | ((sk_B) = (k1_xboole_0))))
% 0.97/1.17         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['113', '114'])).
% 0.97/1.17  thf('116', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['115'])).
% 0.97/1.17  thf('117', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('118', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['106'])).
% 0.97/1.17  thf('119', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 0.97/1.17          | ((k1_tarski @ X0) = (k1_tarski @ X1)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['37'])).
% 0.97/1.17  thf('120', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['41', '42'])).
% 0.97/1.17  thf('121', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((k3_tarski @ (k1_tarski @ X0)) = (X1))
% 0.97/1.17          | ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['119', '120'])).
% 0.97/1.17  thf('122', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.97/1.17      inference('demod', [status(thm)], ['41', '42'])).
% 0.97/1.17  thf('123', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((X0) = (X1)) | ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['121', '122'])).
% 0.97/1.17  thf('124', plain,
% 0.97/1.17      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.97/1.17      inference('condensation', [status(thm)], ['123'])).
% 0.97/1.17  thf('125', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((k2_xboole_0 @ X1 @ X0)
% 0.97/1.17           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['91', '92'])).
% 0.97/1.17  thf('126', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['124', '125'])).
% 0.97/1.17  thf('127', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.17      inference('demod', [status(thm)], ['82', '83'])).
% 0.97/1.17  thf('128', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['126', '127'])).
% 0.97/1.17  thf('129', plain,
% 0.97/1.17      ((![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B @ X0)))
% 0.97/1.17         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('sup+', [status(thm)], ['118', '128'])).
% 0.97/1.17  thf('130', plain,
% 0.97/1.17      ((((sk_C_1) = (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.97/1.17      inference('sup+', [status(thm)], ['117', '129'])).
% 0.97/1.17  thf('131', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['99', '111'])).
% 0.97/1.17  thf('132', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 0.97/1.17  thf('133', plain,
% 0.97/1.17      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.97/1.17      inference('split', [status(esa)], ['104'])).
% 0.97/1.17  thf('134', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['132', '133'])).
% 0.97/1.17  thf('135', plain, (((sk_B) = (k1_xboole_0))),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['116', '134'])).
% 0.97/1.17  thf('136', plain, (((sk_B) = (k1_xboole_0))),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['116', '134'])).
% 0.97/1.17  thf('137', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((X0) = (X1)) | ((k4_xboole_0 @ sk_B @ X2) = (sk_B)))),
% 0.97/1.17      inference('demod', [status(thm)], ['46', '135', '136'])).
% 0.97/1.17  thf('138', plain, (![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B))),
% 0.97/1.17      inference('condensation', [status(thm)], ['137'])).
% 0.97/1.17  thf('139', plain, (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.97/1.17      inference('demod', [status(thm)], ['17', '138'])).
% 0.97/1.17  thf('140', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '13'])).
% 0.97/1.17  thf('141', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C_1 @ sk_B))),
% 0.97/1.17      inference('sup+', [status(thm)], ['139', '140'])).
% 0.97/1.17  thf('142', plain,
% 0.97/1.17      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['115'])).
% 0.97/1.17  thf('143', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.17      inference('demod', [status(thm)], ['82', '83'])).
% 0.97/1.17  thf('144', plain,
% 0.97/1.17      ((![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ sk_B)))
% 0.97/1.17         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.97/1.17      inference('sup+', [status(thm)], ['142', '143'])).
% 0.97/1.17  thf('145', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['132', '133'])).
% 0.97/1.17  thf('146', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ sk_B))),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['144', '145'])).
% 0.97/1.17  thf('147', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 0.97/1.17      inference('demod', [status(thm)], ['141', '146'])).
% 0.97/1.17  thf('148', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['99', '111'])).
% 0.97/1.17  thf('149', plain, ($false),
% 0.97/1.17      inference('simplify_reflect-', [status(thm)], ['147', '148'])).
% 0.97/1.17  
% 0.97/1.17  % SZS output end Refutation
% 0.97/1.17  
% 1.04/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
