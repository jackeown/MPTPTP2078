%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dS80GHNVzd

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:51 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 288 expanded)
%              Number of leaves         :   20 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  914 (2715 expanded)
%              Number of equality atoms :   56 ( 222 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t64_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( A != C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_zfmisc_1])).

thf('0',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 != X32 )
      | ( r2_hidden @ X33 @ X34 )
      | ( X34
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('31',plain,(
    ! [X32: $i] :
      ( r2_hidden @ X32 @ ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','19'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X11 ) )
      | ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','27'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('45',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X11 ) )
      | ( r2_hidden @ X8 @ X11 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('62',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','70'])).

thf('72',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ X34 )
      | ( X35 = X32 )
      | ( X34
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('73',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_A = sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','32','50','51','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dS80GHNVzd
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.72/1.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.72/1.95  % Solved by: fo/fo7.sh
% 1.72/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.95  % done 2287 iterations in 1.491s
% 1.72/1.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.72/1.95  % SZS output start Refutation
% 1.72/1.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.72/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.72/1.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.72/1.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.72/1.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.72/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.95  thf(t64_zfmisc_1, conjecture,
% 1.72/1.95    (![A:$i,B:$i,C:$i]:
% 1.72/1.95     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.72/1.95       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.72/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.95    (~( ![A:$i,B:$i,C:$i]:
% 1.72/1.95        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.72/1.95          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 1.72/1.95    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 1.72/1.95  thf('0', plain,
% 1.72/1.95      ((((sk_A) = (sk_C_1))
% 1.72/1.95        | ~ (r2_hidden @ sk_A @ sk_B)
% 1.72/1.95        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('1', plain,
% 1.72/1.95      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.72/1.95       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 1.72/1.95       (((sk_A) = (sk_C_1)))),
% 1.72/1.95      inference('split', [status(esa)], ['0'])).
% 1.72/1.95  thf('2', plain,
% 1.72/1.95      ((((sk_A) != (sk_C_1))
% 1.72/1.95        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('3', plain,
% 1.72/1.95      (~ (((sk_A) = (sk_C_1))) | 
% 1.72/1.95       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.72/1.95      inference('split', [status(esa)], ['2'])).
% 1.72/1.95  thf('4', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 1.72/1.95      inference('split', [status(esa)], ['0'])).
% 1.72/1.95  thf('5', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ sk_B)
% 1.72/1.95        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('6', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('split', [status(esa)], ['5'])).
% 1.72/1.95  thf('7', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             (((sk_A) = (sk_C_1))))),
% 1.72/1.95      inference('sup+', [status(thm)], ['4', '6'])).
% 1.72/1.95  thf(t95_xboole_1, axiom,
% 1.72/1.95    (![A:$i,B:$i]:
% 1.72/1.95     ( ( k3_xboole_0 @ A @ B ) =
% 1.72/1.95       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.72/1.95  thf('8', plain,
% 1.72/1.95      (![X18 : $i, X19 : $i]:
% 1.72/1.95         ((k3_xboole_0 @ X18 @ X19)
% 1.72/1.95           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.72/1.95              (k2_xboole_0 @ X18 @ X19)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.72/1.95  thf(t91_xboole_1, axiom,
% 1.72/1.95    (![A:$i,B:$i,C:$i]:
% 1.72/1.95     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.72/1.95       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.72/1.95  thf('9', plain,
% 1.72/1.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.72/1.95           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.72/1.95  thf('10', plain,
% 1.72/1.95      (![X18 : $i, X19 : $i]:
% 1.72/1.95         ((k3_xboole_0 @ X18 @ X19)
% 1.72/1.95           = (k5_xboole_0 @ X18 @ 
% 1.72/1.95              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 1.72/1.95      inference('demod', [status(thm)], ['8', '9'])).
% 1.72/1.95  thf(t92_xboole_1, axiom,
% 1.72/1.95    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.72/1.95  thf('11', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.72/1.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.72/1.95  thf('12', plain,
% 1.72/1.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.72/1.95           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.72/1.95  thf('13', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.72/1.95           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('sup+', [status(thm)], ['11', '12'])).
% 1.72/1.95  thf('14', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.72/1.95           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('sup+', [status(thm)], ['11', '12'])).
% 1.72/1.95  thf('15', plain,
% 1.72/1.95      (![X18 : $i, X19 : $i]:
% 1.72/1.95         ((k3_xboole_0 @ X18 @ X19)
% 1.72/1.95           = (k5_xboole_0 @ X18 @ 
% 1.72/1.95              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 1.72/1.95      inference('demod', [status(thm)], ['8', '9'])).
% 1.72/1.95  thf('16', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         ((k3_xboole_0 @ X0 @ X0)
% 1.72/1.95           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.72/1.95      inference('sup+', [status(thm)], ['14', '15'])).
% 1.72/1.95  thf(idempotence_k3_xboole_0, axiom,
% 1.72/1.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.72/1.95  thf('17', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 1.72/1.95      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.72/1.95  thf(idempotence_k2_xboole_0, axiom,
% 1.72/1.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.72/1.95  thf('18', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.72/1.95      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.72/1.95  thf('19', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.72/1.95      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.72/1.95  thf('20', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('demod', [status(thm)], ['13', '19'])).
% 1.72/1.95  thf('21', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.72/1.95           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('sup+', [status(thm)], ['10', '20'])).
% 1.72/1.95  thf(t100_xboole_1, axiom,
% 1.72/1.95    (![A:$i,B:$i]:
% 1.72/1.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.72/1.95  thf('22', plain,
% 1.72/1.95      (![X12 : $i, X13 : $i]:
% 1.72/1.95         ((k4_xboole_0 @ X12 @ X13)
% 1.72/1.95           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.72/1.95  thf('23', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.72/1.95           = (k4_xboole_0 @ X1 @ X0))),
% 1.72/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.72/1.95  thf(t1_xboole_0, axiom,
% 1.72/1.95    (![A:$i,B:$i,C:$i]:
% 1.72/1.95     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.72/1.95       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.72/1.95  thf('24', plain,
% 1.72/1.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X8 @ X9)
% 1.72/1.95          | ~ (r2_hidden @ X8 @ X10)
% 1.72/1.95          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.72/1.95  thf('25', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.72/1.95          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.72/1.95          | ~ (r2_hidden @ X2 @ X0))),
% 1.72/1.95      inference('sup-', [status(thm)], ['23', '24'])).
% 1.72/1.95  thf(d3_xboole_0, axiom,
% 1.72/1.95    (![A:$i,B:$i,C:$i]:
% 1.72/1.95     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.72/1.95       ( ![D:$i]:
% 1.72/1.95         ( ( r2_hidden @ D @ C ) <=>
% 1.72/1.95           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.72/1.95  thf('26', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X0 @ X1)
% 1.72/1.95          | (r2_hidden @ X0 @ X2)
% 1.72/1.95          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.72/1.95      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.72/1.95  thf('27', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.72/1.95         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.72/1.95      inference('simplify', [status(thm)], ['26'])).
% 1.72/1.95  thf('28', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X2 @ X0)
% 1.72/1.95          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('clc', [status(thm)], ['25', '27'])).
% 1.72/1.95  thf('29', plain,
% 1.72/1.95      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             (((sk_A) = (sk_C_1))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['7', '28'])).
% 1.72/1.95  thf(d1_tarski, axiom,
% 1.72/1.95    (![A:$i,B:$i]:
% 1.72/1.95     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.72/1.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.72/1.95  thf('30', plain,
% 1.72/1.95      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.72/1.95         (((X33) != (X32))
% 1.72/1.95          | (r2_hidden @ X33 @ X34)
% 1.72/1.95          | ((X34) != (k1_tarski @ X32)))),
% 1.72/1.95      inference('cnf', [status(esa)], [d1_tarski])).
% 1.72/1.95  thf('31', plain, (![X32 : $i]: (r2_hidden @ X32 @ (k1_tarski @ X32))),
% 1.72/1.95      inference('simplify', [status(thm)], ['30'])).
% 1.72/1.95  thf('32', plain,
% 1.72/1.95      (~ (((sk_A) = (sk_C_1))) | 
% 1.72/1.95       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.72/1.95      inference('demod', [status(thm)], ['29', '31'])).
% 1.72/1.95  thf('33', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.72/1.95           = (k4_xboole_0 @ X1 @ X0))),
% 1.72/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.72/1.95  thf('34', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('demod', [status(thm)], ['13', '19'])).
% 1.72/1.95  thf('35', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((k2_xboole_0 @ X1 @ X0)
% 1.72/1.95           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('sup+', [status(thm)], ['33', '34'])).
% 1.72/1.95  thf('36', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('split', [status(esa)], ['5'])).
% 1.72/1.95  thf('37', plain,
% 1.72/1.95      (![X8 : $i, X9 : $i, X11 : $i]:
% 1.72/1.95         ((r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X11))
% 1.72/1.95          | (r2_hidden @ X8 @ X9)
% 1.72/1.95          | ~ (r2_hidden @ X8 @ X11))),
% 1.72/1.95      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.72/1.95  thf('38', plain,
% 1.72/1.95      ((![X0 : $i]:
% 1.72/1.95          ((r2_hidden @ sk_A @ X0)
% 1.72/1.95           | (r2_hidden @ sk_A @ 
% 1.72/1.95              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['36', '37'])).
% 1.72/1.95  thf('39', plain,
% 1.72/1.95      ((((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))
% 1.72/1.95         | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('sup+', [status(thm)], ['35', '38'])).
% 1.72/1.95  thf('40', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('split', [status(esa)], ['5'])).
% 1.72/1.95  thf('41', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X2 @ X0)
% 1.72/1.95          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('clc', [status(thm)], ['25', '27'])).
% 1.72/1.95  thf('42', plain,
% 1.72/1.95      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['40', '41'])).
% 1.72/1.95  thf('43', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('clc', [status(thm)], ['39', '42'])).
% 1.72/1.95  thf('44', plain,
% 1.72/1.95      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X4 @ X2)
% 1.72/1.95          | (r2_hidden @ X4 @ X3)
% 1.72/1.95          | (r2_hidden @ X4 @ X1)
% 1.72/1.95          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.72/1.95      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.72/1.95  thf('45', plain,
% 1.72/1.95      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.72/1.95         ((r2_hidden @ X4 @ X1)
% 1.72/1.95          | (r2_hidden @ X4 @ X3)
% 1.72/1.95          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.72/1.95      inference('simplify', [status(thm)], ['44'])).
% 1.72/1.95  thf('46', plain,
% 1.72/1.95      ((((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['43', '45'])).
% 1.72/1.95  thf('47', plain,
% 1.72/1.95      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['40', '41'])).
% 1.72/1.95  thf('48', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ sk_B))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('clc', [status(thm)], ['46', '47'])).
% 1.72/1.95  thf('49', plain,
% 1.72/1.95      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('split', [status(esa)], ['0'])).
% 1.72/1.95  thf('50', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.72/1.95       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['48', '49'])).
% 1.72/1.95  thf('51', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.72/1.95       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.72/1.95      inference('split', [status(esa)], ['5'])).
% 1.72/1.95  thf('52', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('split', [status(esa)], ['5'])).
% 1.72/1.95  thf('53', plain,
% 1.72/1.95      (![X8 : $i, X9 : $i, X11 : $i]:
% 1.72/1.95         ((r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X11))
% 1.72/1.95          | (r2_hidden @ X8 @ X11)
% 1.72/1.95          | ~ (r2_hidden @ X8 @ X9))),
% 1.72/1.95      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.72/1.95  thf('54', plain,
% 1.72/1.95      ((![X0 : $i]:
% 1.72/1.95          ((r2_hidden @ sk_A @ X0)
% 1.72/1.95           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['52', '53'])).
% 1.72/1.95  thf('55', plain,
% 1.72/1.95      (![X12 : $i, X13 : $i]:
% 1.72/1.95         ((k4_xboole_0 @ X12 @ X13)
% 1.72/1.95           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.72/1.95  thf('56', plain,
% 1.72/1.95      ((![X0 : $i]:
% 1.72/1.95          ((r2_hidden @ sk_A @ X0)
% 1.72/1.95           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['52', '53'])).
% 1.72/1.95  thf('57', plain,
% 1.72/1.95      ((![X0 : $i]:
% 1.72/1.95          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.72/1.95           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup+', [status(thm)], ['55', '56'])).
% 1.72/1.95  thf('58', plain,
% 1.72/1.95      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (~
% 1.72/1.95             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.72/1.95      inference('split', [status(esa)], ['0'])).
% 1.72/1.95  thf('59', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (~
% 1.72/1.95             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             ((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['57', '58'])).
% 1.72/1.95  thf('60', plain,
% 1.72/1.95      (![X18 : $i, X19 : $i]:
% 1.72/1.95         ((k3_xboole_0 @ X18 @ X19)
% 1.72/1.95           = (k5_xboole_0 @ X18 @ 
% 1.72/1.95              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 1.72/1.95      inference('demod', [status(thm)], ['8', '9'])).
% 1.72/1.95  thf('61', plain,
% 1.72/1.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.72/1.95         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.72/1.95           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.72/1.95  thf('62', plain,
% 1.72/1.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X8 @ X9)
% 1.72/1.95          | ~ (r2_hidden @ X8 @ X10)
% 1.72/1.95          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.72/1.95  thf('63', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 1.72/1.95          | ~ (r2_hidden @ X3 @ X0)
% 1.72/1.95          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['61', '62'])).
% 1.72/1.95  thf('64', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.72/1.95          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 1.72/1.95          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['60', '63'])).
% 1.72/1.95  thf('65', plain,
% 1.72/1.95      (((~ (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))
% 1.72/1.95         | ~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))
% 1.72/1.95         <= (~
% 1.72/1.95             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             ((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['59', '64'])).
% 1.72/1.95  thf('66', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('split', [status(esa)], ['5'])).
% 1.72/1.95  thf('67', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X0 @ X3)
% 1.72/1.95          | (r2_hidden @ X0 @ X2)
% 1.72/1.95          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.72/1.95      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.72/1.95  thf('68', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.72/1.95         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.72/1.95      inference('simplify', [status(thm)], ['67'])).
% 1.72/1.95  thf('69', plain,
% 1.72/1.95      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))
% 1.72/1.95         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['66', '68'])).
% 1.72/1.95  thf('70', plain,
% 1.72/1.95      ((~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.72/1.95         <= (~
% 1.72/1.95             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             ((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('demod', [status(thm)], ['65', '69'])).
% 1.72/1.95  thf('71', plain,
% 1.72/1.95      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 1.72/1.95         <= (~
% 1.72/1.95             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             ((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['54', '70'])).
% 1.72/1.95  thf('72', plain,
% 1.72/1.95      (![X32 : $i, X34 : $i, X35 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X35 @ X34)
% 1.72/1.95          | ((X35) = (X32))
% 1.72/1.95          | ((X34) != (k1_tarski @ X32)))),
% 1.72/1.95      inference('cnf', [status(esa)], [d1_tarski])).
% 1.72/1.95  thf('73', plain,
% 1.72/1.95      (![X32 : $i, X35 : $i]:
% 1.72/1.95         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 1.72/1.95      inference('simplify', [status(thm)], ['72'])).
% 1.72/1.95  thf('74', plain,
% 1.72/1.95      ((((sk_A) = (sk_C_1)))
% 1.72/1.95         <= (~
% 1.72/1.95             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             ((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['71', '73'])).
% 1.72/1.95  thf('75', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 1.72/1.95      inference('split', [status(esa)], ['2'])).
% 1.72/1.95  thf('76', plain,
% 1.72/1.95      ((((sk_A) != (sk_A)))
% 1.72/1.95         <= (~ (((sk_A) = (sk_C_1))) & 
% 1.72/1.95             ~
% 1.72/1.95             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.72/1.95             ((r2_hidden @ sk_A @ sk_B)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.95  thf('77', plain,
% 1.72/1.95      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.72/1.95       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 1.72/1.95       (((sk_A) = (sk_C_1)))),
% 1.72/1.95      inference('simplify', [status(thm)], ['76'])).
% 1.72/1.95  thf('78', plain, ($false),
% 1.72/1.95      inference('sat_resolution*', [status(thm)],
% 1.72/1.95                ['1', '3', '32', '50', '51', '77'])).
% 1.72/1.95  
% 1.72/1.95  % SZS output end Refutation
% 1.72/1.95  
% 1.72/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
