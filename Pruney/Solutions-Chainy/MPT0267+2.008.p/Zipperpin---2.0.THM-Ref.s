%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y5SlUBx34n

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:51 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 320 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  953 (2910 expanded)
%              Number of equality atoms :   62 ( 252 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
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
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('19',plain,(
    ! [X66: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X32 != X31 )
      | ( r2_hidden @ X32 @ X33 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('35',plain,(
    ! [X31: $i] :
      ( r2_hidden @ X31 @ ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X10 ) )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','31'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('49',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('56',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('57',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X10 ) )
      | ( r2_hidden @ X7 @ X10 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('66',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','74'])).

thf('76',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('77',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( sk_A = sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('80',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','36','54','55','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y5SlUBx34n
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.74/1.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.74/1.94  % Solved by: fo/fo7.sh
% 1.74/1.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.94  % done 2229 iterations in 1.481s
% 1.74/1.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.74/1.94  % SZS output start Refutation
% 1.74/1.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.94  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.94  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.74/1.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.74/1.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.74/1.94  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.74/1.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.74/1.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.74/1.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.74/1.94  thf(t64_zfmisc_1, conjecture,
% 1.74/1.94    (![A:$i,B:$i,C:$i]:
% 1.74/1.94     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.74/1.94       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.74/1.94  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.94    (~( ![A:$i,B:$i,C:$i]:
% 1.74/1.94        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.74/1.94          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 1.74/1.94    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 1.74/1.94  thf('0', plain,
% 1.74/1.94      ((((sk_A) = (sk_C_1))
% 1.74/1.94        | ~ (r2_hidden @ sk_A @ sk_B)
% 1.74/1.94        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('1', plain,
% 1.74/1.94      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.74/1.94       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 1.74/1.94       (((sk_A) = (sk_C_1)))),
% 1.74/1.94      inference('split', [status(esa)], ['0'])).
% 1.74/1.94  thf('2', plain,
% 1.74/1.94      ((((sk_A) != (sk_C_1))
% 1.74/1.94        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('3', plain,
% 1.74/1.94      (~ (((sk_A) = (sk_C_1))) | 
% 1.74/1.94       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.74/1.94      inference('split', [status(esa)], ['2'])).
% 1.74/1.94  thf('4', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 1.74/1.94      inference('split', [status(esa)], ['0'])).
% 1.74/1.94  thf('5', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ sk_B)
% 1.74/1.94        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('6', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('split', [status(esa)], ['5'])).
% 1.74/1.94  thf('7', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             (((sk_A) = (sk_C_1))))),
% 1.74/1.94      inference('sup+', [status(thm)], ['4', '6'])).
% 1.74/1.94  thf(t95_xboole_1, axiom,
% 1.74/1.94    (![A:$i,B:$i]:
% 1.74/1.94     ( ( k3_xboole_0 @ A @ B ) =
% 1.74/1.94       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.74/1.94  thf('8', plain,
% 1.74/1.94      (![X17 : $i, X18 : $i]:
% 1.74/1.94         ((k3_xboole_0 @ X17 @ X18)
% 1.74/1.94           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 1.74/1.94              (k2_xboole_0 @ X17 @ X18)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.74/1.94  thf(t91_xboole_1, axiom,
% 1.74/1.94    (![A:$i,B:$i,C:$i]:
% 1.74/1.94     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.74/1.94       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.74/1.94  thf('9', plain,
% 1.74/1.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.74/1.94           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.74/1.94  thf('10', plain,
% 1.74/1.94      (![X17 : $i, X18 : $i]:
% 1.74/1.94         ((k3_xboole_0 @ X17 @ X18)
% 1.74/1.94           = (k5_xboole_0 @ X17 @ 
% 1.74/1.94              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 1.74/1.94      inference('demod', [status(thm)], ['8', '9'])).
% 1.74/1.94  thf(t92_xboole_1, axiom,
% 1.74/1.94    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.74/1.94  thf('11', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 1.74/1.94      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.74/1.94  thf('12', plain,
% 1.74/1.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.74/1.94           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.74/1.94  thf('13', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.74/1.94           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('sup+', [status(thm)], ['11', '12'])).
% 1.74/1.94  thf('14', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.74/1.94           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('sup+', [status(thm)], ['11', '12'])).
% 1.74/1.94  thf('15', plain,
% 1.74/1.94      (![X17 : $i, X18 : $i]:
% 1.74/1.94         ((k3_xboole_0 @ X17 @ X18)
% 1.74/1.94           = (k5_xboole_0 @ X17 @ 
% 1.74/1.94              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 1.74/1.94      inference('demod', [status(thm)], ['8', '9'])).
% 1.74/1.94  thf('16', plain,
% 1.74/1.94      (![X0 : $i]:
% 1.74/1.94         ((k3_xboole_0 @ X0 @ X0)
% 1.74/1.94           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.74/1.94      inference('sup+', [status(thm)], ['14', '15'])).
% 1.74/1.94  thf(idempotence_k3_xboole_0, axiom,
% 1.74/1.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.74/1.94  thf('17', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 1.74/1.94      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.74/1.94  thf(t69_enumset1, axiom,
% 1.74/1.94    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.74/1.94  thf('18', plain,
% 1.74/1.94      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.74/1.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.94  thf(t31_zfmisc_1, axiom,
% 1.74/1.94    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.74/1.94  thf('19', plain, (![X66 : $i]: ((k3_tarski @ (k1_tarski @ X66)) = (X66))),
% 1.74/1.94      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 1.74/1.94  thf('20', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.74/1.94      inference('sup+', [status(thm)], ['18', '19'])).
% 1.74/1.94  thf(l51_zfmisc_1, axiom,
% 1.74/1.94    (![A:$i,B:$i]:
% 1.74/1.94     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.74/1.94  thf('21', plain,
% 1.74/1.94      (![X64 : $i, X65 : $i]:
% 1.74/1.94         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 1.74/1.94      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.94  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.74/1.94      inference('demod', [status(thm)], ['20', '21'])).
% 1.74/1.94  thf('23', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.74/1.94      inference('demod', [status(thm)], ['16', '17', '22'])).
% 1.74/1.94  thf('24', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('demod', [status(thm)], ['13', '23'])).
% 1.74/1.94  thf('25', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.74/1.94           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('sup+', [status(thm)], ['10', '24'])).
% 1.74/1.94  thf(t100_xboole_1, axiom,
% 1.74/1.94    (![A:$i,B:$i]:
% 1.74/1.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.74/1.94  thf('26', plain,
% 1.74/1.94      (![X11 : $i, X12 : $i]:
% 1.74/1.94         ((k4_xboole_0 @ X11 @ X12)
% 1.74/1.94           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.94  thf('27', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.74/1.94           = (k4_xboole_0 @ X1 @ X0))),
% 1.74/1.94      inference('demod', [status(thm)], ['25', '26'])).
% 1.74/1.94  thf(t1_xboole_0, axiom,
% 1.74/1.94    (![A:$i,B:$i,C:$i]:
% 1.74/1.94     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.74/1.94       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.74/1.94  thf('28', plain,
% 1.74/1.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X7 @ X8)
% 1.74/1.94          | ~ (r2_hidden @ X7 @ X9)
% 1.74/1.94          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.74/1.94  thf('29', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.74/1.94          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.74/1.94          | ~ (r2_hidden @ X2 @ X0))),
% 1.74/1.94      inference('sup-', [status(thm)], ['27', '28'])).
% 1.74/1.94  thf(d3_xboole_0, axiom,
% 1.74/1.94    (![A:$i,B:$i,C:$i]:
% 1.74/1.94     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.74/1.94       ( ![D:$i]:
% 1.74/1.94         ( ( r2_hidden @ D @ C ) <=>
% 1.74/1.94           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.74/1.94  thf('30', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X0 @ X1)
% 1.74/1.94          | (r2_hidden @ X0 @ X2)
% 1.74/1.94          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.94      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.74/1.94  thf('31', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.74/1.94         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.74/1.94      inference('simplify', [status(thm)], ['30'])).
% 1.74/1.94  thf('32', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X2 @ X0)
% 1.74/1.94          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('clc', [status(thm)], ['29', '31'])).
% 1.74/1.94  thf('33', plain,
% 1.74/1.94      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             (((sk_A) = (sk_C_1))))),
% 1.74/1.94      inference('sup-', [status(thm)], ['7', '32'])).
% 1.74/1.94  thf(d1_tarski, axiom,
% 1.74/1.94    (![A:$i,B:$i]:
% 1.74/1.94     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.74/1.94       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.74/1.94  thf('34', plain,
% 1.74/1.94      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.74/1.94         (((X32) != (X31))
% 1.74/1.94          | (r2_hidden @ X32 @ X33)
% 1.74/1.94          | ((X33) != (k1_tarski @ X31)))),
% 1.74/1.94      inference('cnf', [status(esa)], [d1_tarski])).
% 1.74/1.94  thf('35', plain, (![X31 : $i]: (r2_hidden @ X31 @ (k1_tarski @ X31))),
% 1.74/1.94      inference('simplify', [status(thm)], ['34'])).
% 1.74/1.94  thf('36', plain,
% 1.74/1.94      (~ (((sk_A) = (sk_C_1))) | 
% 1.74/1.94       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.74/1.94      inference('demod', [status(thm)], ['33', '35'])).
% 1.74/1.94  thf('37', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.74/1.94           = (k4_xboole_0 @ X1 @ X0))),
% 1.74/1.94      inference('demod', [status(thm)], ['25', '26'])).
% 1.74/1.94  thf('38', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('demod', [status(thm)], ['13', '23'])).
% 1.74/1.94  thf('39', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]:
% 1.74/1.94         ((k2_xboole_0 @ X1 @ X0)
% 1.74/1.94           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('sup+', [status(thm)], ['37', '38'])).
% 1.74/1.94  thf('40', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('split', [status(esa)], ['5'])).
% 1.74/1.94  thf('41', plain,
% 1.74/1.94      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.74/1.94         ((r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X10))
% 1.74/1.94          | (r2_hidden @ X7 @ X8)
% 1.74/1.94          | ~ (r2_hidden @ X7 @ X10))),
% 1.74/1.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.74/1.94  thf('42', plain,
% 1.74/1.94      ((![X0 : $i]:
% 1.74/1.94          ((r2_hidden @ sk_A @ X0)
% 1.74/1.94           | (r2_hidden @ sk_A @ 
% 1.74/1.94              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('sup-', [status(thm)], ['40', '41'])).
% 1.74/1.94  thf('43', plain,
% 1.74/1.94      ((((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))
% 1.74/1.94         | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('sup+', [status(thm)], ['39', '42'])).
% 1.74/1.94  thf('44', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('split', [status(esa)], ['5'])).
% 1.74/1.94  thf('45', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X2 @ X0)
% 1.74/1.94          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('clc', [status(thm)], ['29', '31'])).
% 1.74/1.94  thf('46', plain,
% 1.74/1.94      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('sup-', [status(thm)], ['44', '45'])).
% 1.74/1.94  thf('47', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('clc', [status(thm)], ['43', '46'])).
% 1.74/1.94  thf('48', plain,
% 1.74/1.94      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X4 @ X2)
% 1.74/1.94          | (r2_hidden @ X4 @ X3)
% 1.74/1.94          | (r2_hidden @ X4 @ X1)
% 1.74/1.94          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.94      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.74/1.94  thf('49', plain,
% 1.74/1.94      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.74/1.94         ((r2_hidden @ X4 @ X1)
% 1.74/1.94          | (r2_hidden @ X4 @ X3)
% 1.74/1.94          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.94      inference('simplify', [status(thm)], ['48'])).
% 1.74/1.94  thf('50', plain,
% 1.74/1.94      ((((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('sup-', [status(thm)], ['47', '49'])).
% 1.74/1.94  thf('51', plain,
% 1.74/1.94      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('sup-', [status(thm)], ['44', '45'])).
% 1.74/1.94  thf('52', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ sk_B))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('clc', [status(thm)], ['50', '51'])).
% 1.74/1.94  thf('53', plain,
% 1.74/1.94      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('split', [status(esa)], ['0'])).
% 1.74/1.94  thf('54', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.74/1.94       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.74/1.94      inference('sup-', [status(thm)], ['52', '53'])).
% 1.74/1.94  thf('55', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.74/1.94       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 1.74/1.94      inference('split', [status(esa)], ['5'])).
% 1.74/1.94  thf('56', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('split', [status(esa)], ['5'])).
% 1.74/1.94  thf('57', plain,
% 1.74/1.94      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.74/1.94         ((r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X10))
% 1.74/1.94          | (r2_hidden @ X7 @ X10)
% 1.74/1.94          | ~ (r2_hidden @ X7 @ X8))),
% 1.74/1.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.74/1.94  thf('58', plain,
% 1.74/1.94      ((![X0 : $i]:
% 1.74/1.94          ((r2_hidden @ sk_A @ X0)
% 1.74/1.94           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['56', '57'])).
% 1.74/1.94  thf('59', plain,
% 1.74/1.94      (![X11 : $i, X12 : $i]:
% 1.74/1.94         ((k4_xboole_0 @ X11 @ X12)
% 1.74/1.94           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.94  thf('60', plain,
% 1.74/1.94      ((![X0 : $i]:
% 1.74/1.94          ((r2_hidden @ sk_A @ X0)
% 1.74/1.94           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['56', '57'])).
% 1.74/1.94  thf('61', plain,
% 1.74/1.94      ((![X0 : $i]:
% 1.74/1.94          ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.74/1.94           | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup+', [status(thm)], ['59', '60'])).
% 1.74/1.94  thf('62', plain,
% 1.74/1.94      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (~
% 1.74/1.94             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 1.74/1.94      inference('split', [status(esa)], ['0'])).
% 1.74/1.94  thf('63', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (~
% 1.74/1.94             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['61', '62'])).
% 1.74/1.94  thf('64', plain,
% 1.74/1.94      (![X17 : $i, X18 : $i]:
% 1.74/1.94         ((k3_xboole_0 @ X17 @ X18)
% 1.74/1.94           = (k5_xboole_0 @ X17 @ 
% 1.74/1.94              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 1.74/1.94      inference('demod', [status(thm)], ['8', '9'])).
% 1.74/1.94  thf('65', plain,
% 1.74/1.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.94         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.74/1.94           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.74/1.94  thf('66', plain,
% 1.74/1.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X7 @ X8)
% 1.74/1.94          | ~ (r2_hidden @ X7 @ X9)
% 1.74/1.94          | ~ (r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 1.74/1.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.74/1.94  thf('67', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 1.74/1.94          | ~ (r2_hidden @ X3 @ X0)
% 1.74/1.94          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['65', '66'])).
% 1.74/1.94  thf('68', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.74/1.94          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 1.74/1.94          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['64', '67'])).
% 1.74/1.94  thf('69', plain,
% 1.74/1.94      (((~ (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))
% 1.74/1.94         | ~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))
% 1.74/1.94         <= (~
% 1.74/1.94             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['63', '68'])).
% 1.74/1.94  thf('70', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('split', [status(esa)], ['5'])).
% 1.74/1.94  thf('71', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X0 @ X3)
% 1.74/1.94          | (r2_hidden @ X0 @ X2)
% 1.74/1.94          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.94      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.74/1.94  thf('72', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.74/1.94         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.74/1.94      inference('simplify', [status(thm)], ['71'])).
% 1.74/1.94  thf('73', plain,
% 1.74/1.94      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))
% 1.74/1.94         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['70', '72'])).
% 1.74/1.94  thf('74', plain,
% 1.74/1.94      ((~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 1.74/1.94         <= (~
% 1.74/1.94             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('demod', [status(thm)], ['69', '73'])).
% 1.74/1.94  thf('75', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 1.74/1.94         <= (~
% 1.74/1.94             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['58', '74'])).
% 1.74/1.94  thf('76', plain,
% 1.74/1.94      (![X31 : $i, X33 : $i, X34 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X34 @ X33)
% 1.74/1.94          | ((X34) = (X31))
% 1.74/1.94          | ((X33) != (k1_tarski @ X31)))),
% 1.74/1.94      inference('cnf', [status(esa)], [d1_tarski])).
% 1.74/1.94  thf('77', plain,
% 1.74/1.94      (![X31 : $i, X34 : $i]:
% 1.74/1.94         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 1.74/1.94      inference('simplify', [status(thm)], ['76'])).
% 1.74/1.94  thf('78', plain,
% 1.74/1.94      ((((sk_A) = (sk_C_1)))
% 1.74/1.94         <= (~
% 1.74/1.94             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['75', '77'])).
% 1.74/1.94  thf('79', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 1.74/1.94      inference('split', [status(esa)], ['2'])).
% 1.74/1.94  thf('80', plain,
% 1.74/1.94      ((((sk_A) != (sk_A)))
% 1.74/1.94         <= (~ (((sk_A) = (sk_C_1))) & 
% 1.74/1.94             ~
% 1.74/1.94             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 1.74/1.94             ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['78', '79'])).
% 1.74/1.94  thf('81', plain,
% 1.74/1.94      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.74/1.94       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 1.74/1.94       (((sk_A) = (sk_C_1)))),
% 1.74/1.94      inference('simplify', [status(thm)], ['80'])).
% 1.74/1.94  thf('82', plain, ($false),
% 1.74/1.94      inference('sat_resolution*', [status(thm)],
% 1.74/1.94                ['1', '3', '36', '54', '55', '81'])).
% 1.74/1.94  
% 1.74/1.94  % SZS output end Refutation
% 1.74/1.94  
% 1.74/1.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
