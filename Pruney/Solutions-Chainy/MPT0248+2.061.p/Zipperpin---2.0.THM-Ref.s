%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVBM1EAmBx

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:26 EST 2020

% Result     : Theorem 20.32s
% Output     : Refutation 20.32s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 351 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   23
%              Number of atoms          :  830 (4217 expanded)
%              Number of equality atoms :  140 ( 893 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X55
        = ( k1_tarski @ X54 ) )
      | ( X55 = k1_xboole_0 )
      | ~ ( r1_tarski @ X55 @ ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X22 )
      | ( X24 = X23 )
      | ( X24 = X20 )
      | ( X22
       != ( k2_tarski @ X23 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('27',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X24 = X20 )
      | ( X24 = X23 )
      | ~ ( r2_hidden @ X24 @ ( k2_tarski @ X23 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( sk_B @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('35',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('36',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('44',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('47',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('48',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','45','49'])).

thf('51',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','50'])).

thf('52',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['40','51'])).

thf('53',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('54',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','54'])).

thf('56',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['30','55'])).

thf('57',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','54'])).

thf('60',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('63',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('71',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( sk_C
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['60','75'])).

thf('77',plain,
    ( ( sk_C
      = ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','76'])).

thf('78',plain,
    ( ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','77'])).

thf('79',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','50'])).

thf('80',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','80'])).

thf('82',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','81'])).

thf('83',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','50'])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVBM1EAmBx
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 20.32/20.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.32/20.59  % Solved by: fo/fo7.sh
% 20.32/20.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.32/20.59  % done 11464 iterations in 20.130s
% 20.32/20.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.32/20.59  % SZS output start Refutation
% 20.32/20.59  thf(sk_A_type, type, sk_A: $i).
% 20.32/20.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 20.32/20.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 20.32/20.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 20.32/20.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.32/20.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.32/20.59  thf(sk_B_type, type, sk_B: $i > $i).
% 20.32/20.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 20.32/20.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 20.32/20.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 20.32/20.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.32/20.59  thf(sk_C_type, type, sk_C: $i).
% 20.32/20.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 20.32/20.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.32/20.59  thf(t43_zfmisc_1, conjecture,
% 20.32/20.59    (![A:$i,B:$i,C:$i]:
% 20.32/20.59     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 20.32/20.59          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 20.32/20.59          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 20.32/20.59          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 20.32/20.59  thf(zf_stmt_0, negated_conjecture,
% 20.32/20.59    (~( ![A:$i,B:$i,C:$i]:
% 20.32/20.59        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 20.32/20.59             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 20.32/20.59             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 20.32/20.59             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 20.32/20.59    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 20.32/20.59  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf(commutativity_k3_xboole_0, axiom,
% 20.32/20.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 20.32/20.59  thf('1', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.32/20.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 20.32/20.59  thf(t2_boole, axiom,
% 20.32/20.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 20.32/20.59  thf('2', plain,
% 20.32/20.59      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 20.32/20.59      inference('cnf', [status(esa)], [t2_boole])).
% 20.32/20.59  thf('3', plain,
% 20.32/20.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 20.32/20.59      inference('sup+', [status(thm)], ['1', '2'])).
% 20.32/20.59  thf(t100_xboole_1, axiom,
% 20.32/20.59    (![A:$i,B:$i]:
% 20.32/20.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 20.32/20.59  thf('4', plain,
% 20.32/20.59      (![X12 : $i, X13 : $i]:
% 20.32/20.59         ((k4_xboole_0 @ X12 @ X13)
% 20.32/20.59           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 20.32/20.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.32/20.59  thf('5', plain,
% 20.32/20.59      (![X0 : $i]:
% 20.32/20.59         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 20.32/20.59           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 20.32/20.59      inference('sup+', [status(thm)], ['3', '4'])).
% 20.32/20.59  thf(t5_boole, axiom,
% 20.32/20.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 20.32/20.59  thf('6', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 20.32/20.59      inference('cnf', [status(esa)], [t5_boole])).
% 20.32/20.59  thf('7', plain,
% 20.32/20.59      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 20.32/20.59      inference('demod', [status(thm)], ['5', '6'])).
% 20.32/20.59  thf(l32_xboole_1, axiom,
% 20.32/20.59    (![A:$i,B:$i]:
% 20.32/20.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 20.32/20.59  thf('8', plain,
% 20.32/20.59      (![X9 : $i, X10 : $i]:
% 20.32/20.59         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 20.32/20.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 20.32/20.59  thf('9', plain,
% 20.32/20.59      (![X0 : $i]:
% 20.32/20.59         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 20.32/20.59      inference('sup-', [status(thm)], ['7', '8'])).
% 20.32/20.59  thf('10', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 20.32/20.59      inference('simplify', [status(thm)], ['9'])).
% 20.32/20.59  thf(t12_xboole_1, axiom,
% 20.32/20.59    (![A:$i,B:$i]:
% 20.32/20.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 20.32/20.59  thf('11', plain,
% 20.32/20.59      (![X14 : $i, X15 : $i]:
% 20.32/20.59         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 20.32/20.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 20.32/20.59  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.32/20.59      inference('sup-', [status(thm)], ['10', '11'])).
% 20.32/20.59  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf(t7_xboole_1, axiom,
% 20.32/20.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 20.32/20.59  thf('15', plain,
% 20.32/20.59      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 20.32/20.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 20.32/20.59  thf('16', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 20.32/20.59      inference('sup+', [status(thm)], ['14', '15'])).
% 20.32/20.59  thf(l3_zfmisc_1, axiom,
% 20.32/20.59    (![A:$i,B:$i]:
% 20.32/20.59     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 20.32/20.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 20.32/20.59  thf('17', plain,
% 20.32/20.59      (![X54 : $i, X55 : $i]:
% 20.32/20.59         (((X55) = (k1_tarski @ X54))
% 20.32/20.59          | ((X55) = (k1_xboole_0))
% 20.32/20.59          | ~ (r1_tarski @ X55 @ (k1_tarski @ X54)))),
% 20.32/20.59      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 20.32/20.59  thf('18', plain,
% 20.32/20.59      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['16', '17'])).
% 20.32/20.59  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf(t7_xboole_0, axiom,
% 20.32/20.59    (![A:$i]:
% 20.32/20.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 20.32/20.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 20.32/20.59  thf('20', plain,
% 20.32/20.59      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 20.32/20.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 20.32/20.59  thf(d3_xboole_0, axiom,
% 20.32/20.59    (![A:$i,B:$i,C:$i]:
% 20.32/20.59     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 20.32/20.59       ( ![D:$i]:
% 20.32/20.59         ( ( r2_hidden @ D @ C ) <=>
% 20.32/20.59           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 20.32/20.59  thf('21', plain,
% 20.32/20.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 20.32/20.59         (~ (r2_hidden @ X2 @ X3)
% 20.32/20.59          | (r2_hidden @ X2 @ X4)
% 20.32/20.59          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 20.32/20.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 20.32/20.59  thf('22', plain,
% 20.32/20.59      (![X2 : $i, X3 : $i, X5 : $i]:
% 20.32/20.59         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 20.32/20.59      inference('simplify', [status(thm)], ['21'])).
% 20.32/20.59  thf('23', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X0) = (k1_xboole_0))
% 20.32/20.59          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['20', '22'])).
% 20.32/20.59  thf('24', plain,
% 20.32/20.59      (((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 20.32/20.59        | ((sk_C) = (k1_xboole_0)))),
% 20.32/20.59      inference('sup+', [status(thm)], ['19', '23'])).
% 20.32/20.59  thf(t69_enumset1, axiom,
% 20.32/20.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 20.32/20.59  thf('25', plain,
% 20.32/20.59      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 20.32/20.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 20.32/20.59  thf(d2_tarski, axiom,
% 20.32/20.59    (![A:$i,B:$i,C:$i]:
% 20.32/20.59     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 20.32/20.59       ( ![D:$i]:
% 20.32/20.59         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 20.32/20.59  thf('26', plain,
% 20.32/20.59      (![X20 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 20.32/20.59         (~ (r2_hidden @ X24 @ X22)
% 20.32/20.59          | ((X24) = (X23))
% 20.32/20.59          | ((X24) = (X20))
% 20.32/20.59          | ((X22) != (k2_tarski @ X23 @ X20)))),
% 20.32/20.59      inference('cnf', [status(esa)], [d2_tarski])).
% 20.32/20.59  thf('27', plain,
% 20.32/20.59      (![X20 : $i, X23 : $i, X24 : $i]:
% 20.32/20.59         (((X24) = (X20))
% 20.32/20.59          | ((X24) = (X23))
% 20.32/20.59          | ~ (r2_hidden @ X24 @ (k2_tarski @ X23 @ X20)))),
% 20.32/20.59      inference('simplify', [status(thm)], ['26'])).
% 20.32/20.59  thf('28', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['25', '27'])).
% 20.32/20.59  thf('29', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 20.32/20.59      inference('simplify', [status(thm)], ['28'])).
% 20.32/20.59  thf('30', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B @ sk_C) = (sk_A)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['24', '29'])).
% 20.32/20.59  thf('31', plain,
% 20.32/20.59      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf('32', plain,
% 20.32/20.59      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 20.32/20.59      inference('split', [status(esa)], ['31'])).
% 20.32/20.59  thf('33', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf('34', plain,
% 20.32/20.59      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['16', '17'])).
% 20.32/20.59  thf('35', plain,
% 20.32/20.59      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 20.32/20.59         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('split', [status(esa)], ['31'])).
% 20.32/20.59  thf('36', plain,
% 20.32/20.59      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 20.32/20.59         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('sup-', [status(thm)], ['34', '35'])).
% 20.32/20.59  thf('37', plain,
% 20.32/20.59      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('simplify', [status(thm)], ['36'])).
% 20.32/20.59  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.32/20.59      inference('sup-', [status(thm)], ['10', '11'])).
% 20.32/20.59  thf('39', plain,
% 20.32/20.59      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 20.32/20.59         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('sup+', [status(thm)], ['37', '38'])).
% 20.32/20.59  thf('40', plain,
% 20.32/20.59      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('sup+', [status(thm)], ['33', '39'])).
% 20.32/20.59  thf('41', plain,
% 20.32/20.59      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf('42', plain,
% 20.32/20.59      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('split', [status(esa)], ['41'])).
% 20.32/20.59  thf('43', plain,
% 20.32/20.59      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 20.32/20.59      inference('split', [status(esa)], ['41'])).
% 20.32/20.59  thf('44', plain,
% 20.32/20.59      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.59  thf('45', plain,
% 20.32/20.59      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('split', [status(esa)], ['44'])).
% 20.32/20.59  thf('46', plain,
% 20.32/20.59      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('simplify', [status(thm)], ['36'])).
% 20.32/20.59  thf('47', plain,
% 20.32/20.59      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 20.32/20.59      inference('split', [status(esa)], ['41'])).
% 20.32/20.59  thf('48', plain,
% 20.32/20.59      ((((sk_B_1) != (sk_B_1)))
% 20.32/20.59         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 20.32/20.59             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 20.32/20.59      inference('sup-', [status(thm)], ['46', '47'])).
% 20.32/20.59  thf('49', plain,
% 20.32/20.59      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('simplify', [status(thm)], ['48'])).
% 20.32/20.59  thf('50', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('sat_resolution*', [status(thm)], ['43', '45', '49'])).
% 20.32/20.59  thf('51', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 20.32/20.59      inference('simpl_trail', [status(thm)], ['42', '50'])).
% 20.32/20.59  thf('52', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('simplify_reflect-', [status(thm)], ['40', '51'])).
% 20.32/20.59  thf('53', plain,
% 20.32/20.59      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 20.32/20.59      inference('split', [status(esa)], ['31'])).
% 20.32/20.59  thf('54', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 20.32/20.59      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 20.32/20.59  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 20.32/20.59      inference('simpl_trail', [status(thm)], ['32', '54'])).
% 20.32/20.59  thf('56', plain, (((sk_B @ sk_C) = (sk_A))),
% 20.32/20.59      inference('simplify_reflect-', [status(thm)], ['30', '55'])).
% 20.32/20.59  thf('57', plain,
% 20.32/20.59      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 20.32/20.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 20.32/20.59  thf('58', plain, (((r2_hidden @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 20.32/20.59      inference('sup+', [status(thm)], ['56', '57'])).
% 20.32/20.59  thf('59', plain, (((sk_C) != (k1_xboole_0))),
% 20.32/20.59      inference('simpl_trail', [status(thm)], ['32', '54'])).
% 20.32/20.59  thf('60', plain, ((r2_hidden @ sk_A @ sk_C)),
% 20.32/20.59      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 20.32/20.59  thf('61', plain,
% 20.32/20.59      (![X3 : $i, X5 : $i, X7 : $i]:
% 20.32/20.59         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 20.32/20.59          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 20.32/20.59          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 20.32/20.59          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 20.32/20.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 20.32/20.59  thf('62', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 20.32/20.59          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 20.32/20.59          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 20.32/20.59      inference('eq_fact', [status(thm)], ['61'])).
% 20.32/20.59  thf('63', plain,
% 20.32/20.59      (![X3 : $i, X5 : $i, X7 : $i]:
% 20.32/20.59         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 20.32/20.59          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 20.32/20.59          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 20.32/20.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 20.32/20.59  thf('64', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 20.32/20.59          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 20.32/20.59          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 20.32/20.59          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['62', '63'])).
% 20.32/20.59  thf('65', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 20.32/20.59          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 20.32/20.59          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 20.32/20.59      inference('simplify', [status(thm)], ['64'])).
% 20.32/20.59  thf('66', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 20.32/20.59          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 20.32/20.59          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 20.32/20.59      inference('eq_fact', [status(thm)], ['61'])).
% 20.32/20.59  thf('67', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 20.32/20.59          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 20.32/20.59      inference('clc', [status(thm)], ['65', '66'])).
% 20.32/20.59  thf('68', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 20.32/20.59      inference('simplify', [status(thm)], ['28'])).
% 20.32/20.59  thf('69', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 20.32/20.59          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['67', '68'])).
% 20.32/20.59  thf('70', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 20.32/20.59          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 20.32/20.59      inference('clc', [status(thm)], ['65', '66'])).
% 20.32/20.59  thf('71', plain,
% 20.32/20.59      (![X3 : $i, X5 : $i, X7 : $i]:
% 20.32/20.59         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 20.32/20.59          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 20.32/20.59          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 20.32/20.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 20.32/20.59  thf('72', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 20.32/20.59          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 20.32/20.59          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['70', '71'])).
% 20.32/20.59  thf('73', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 20.32/20.59          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 20.32/20.59      inference('simplify', [status(thm)], ['72'])).
% 20.32/20.59  thf('74', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (~ (r2_hidden @ X0 @ X1)
% 20.32/20.59          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 20.32/20.59          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 20.32/20.59      inference('sup-', [status(thm)], ['69', '73'])).
% 20.32/20.59  thf('75', plain,
% 20.32/20.59      (![X0 : $i, X1 : $i]:
% 20.32/20.59         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 20.32/20.59          | ~ (r2_hidden @ X0 @ X1))),
% 20.32/20.59      inference('simplify', [status(thm)], ['74'])).
% 20.32/20.59  thf('76', plain, (((sk_C) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C))),
% 20.32/20.59      inference('sup-', [status(thm)], ['60', '75'])).
% 20.32/20.59  thf('77', plain,
% 20.32/20.59      ((((sk_C) = (k2_xboole_0 @ sk_B_1 @ sk_C)) | ((sk_B_1) = (k1_xboole_0)))),
% 20.32/20.59      inference('sup+', [status(thm)], ['18', '76'])).
% 20.32/20.59  thf('78', plain,
% 20.32/20.59      ((((sk_C) = (k1_tarski @ sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 20.32/20.59      inference('sup+', [status(thm)], ['13', '77'])).
% 20.32/20.59  thf('79', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 20.32/20.59      inference('simpl_trail', [status(thm)], ['42', '50'])).
% 20.32/20.59  thf('80', plain, (((sk_B_1) = (k1_xboole_0))),
% 20.32/20.59      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 20.32/20.59  thf('81', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0))),
% 20.32/20.59      inference('demod', [status(thm)], ['12', '80'])).
% 20.32/20.59  thf('82', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 20.32/20.59      inference('demod', [status(thm)], ['0', '81'])).
% 20.32/20.59  thf('83', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 20.32/20.59      inference('simpl_trail', [status(thm)], ['42', '50'])).
% 20.32/20.59  thf('84', plain, ($false),
% 20.32/20.59      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 20.32/20.59  
% 20.32/20.59  % SZS output end Refutation
% 20.32/20.59  
% 20.32/20.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
