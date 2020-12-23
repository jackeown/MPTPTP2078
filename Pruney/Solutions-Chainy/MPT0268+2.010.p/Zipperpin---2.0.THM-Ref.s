%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3d17vYCxLi

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:53 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 318 expanded)
%              Number of leaves         :   18 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  730 (2518 expanded)
%              Number of equality atoms :   74 ( 262 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_B @ k1_xboole_0 )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X38: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ X40 )
        = ( k1_tarski @ X38 ) )
      | ( r2_hidden @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ X0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X38: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ X40 )
        = ( k1_tarski @ X38 ) )
      | ( r2_hidden @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('74',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('75',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','40','74'])).

thf('76',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['73','75'])).

thf('77',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['42','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3d17vYCxLi
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:15:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 324 iterations in 0.171s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(t65_zfmisc_1, conjecture,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.44/0.66       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i,B:$i]:
% 0.44/0.66        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.44/0.66          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.44/0.66        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('split', [status(esa)], ['0'])).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.44/0.66       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.44/0.66      inference('split', [status(esa)], ['0'])).
% 0.44/0.66  thf(d10_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.66  thf('4', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.44/0.66      inference('simplify', [status(thm)], ['3'])).
% 0.44/0.66  thf(l32_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X11 : $i, X13 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.44/0.66          | ~ (r1_tarski @ X11 @ X13))),
% 0.44/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.66  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf(t48_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (![X18 : $i, X19 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.66           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (((r2_hidden @ sk_B @ sk_A)
% 0.44/0.66        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('split', [status(esa)], ['8'])).
% 0.44/0.66  thf(d5_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.44/0.66       ( ![D:$i]:
% 0.44/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.66           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X2 @ X3)
% 0.44/0.66          | (r2_hidden @ X2 @ X4)
% 0.44/0.66          | (r2_hidden @ X2 @ X5)
% 0.44/0.66          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.66         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.44/0.66          | (r2_hidden @ X2 @ X4)
% 0.44/0.66          | ~ (r2_hidden @ X2 @ X3))),
% 0.44/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      ((![X0 : $i]:
% 0.44/0.66          ((r2_hidden @ sk_B @ X0)
% 0.44/0.66           | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ X0))))
% 0.44/0.66         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['9', '11'])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      ((![X0 : $i]:
% 0.44/0.66          ((r2_hidden @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 0.44/0.66           | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ X0))))
% 0.44/0.66         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['7', '12'])).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      ((((r2_hidden @ sk_B @ k1_xboole_0)
% 0.44/0.66         | (r2_hidden @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A))))
% 0.44/0.66         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['6', '13'])).
% 0.44/0.66  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X6 @ X5)
% 0.44/0.66          | ~ (r2_hidden @ X6 @ X4)
% 0.44/0.66          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X6 @ X4)
% 0.44/0.66          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['15', '17'])).
% 0.44/0.66  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.66      inference('condensation', [status(thm)], ['18'])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (((r2_hidden @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A)))
% 0.44/0.66         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('clc', [status(thm)], ['14', '19'])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('split', [status(esa)], ['8'])).
% 0.44/0.66  thf(l33_zfmisc_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.66       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.44/0.66  thf('22', plain,
% 0.44/0.66      (![X38 : $i, X40 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ (k1_tarski @ X38) @ X40) = (k1_tarski @ X38))
% 0.44/0.66          | (r2_hidden @ X38 @ X40))),
% 0.44/0.66      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.44/0.66  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf('24', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.44/0.66          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['22', '23'])).
% 0.44/0.66  thf('25', plain,
% 0.44/0.66      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.44/0.66      inference('split', [status(esa)], ['0'])).
% 0.44/0.66  thf('26', plain,
% 0.44/0.66      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X6 @ X4)
% 0.44/0.66          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.66  thf('27', plain,
% 0.44/0.66      ((![X0 : $i]:
% 0.44/0.66          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.66  thf('28', plain,
% 0.44/0.66      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['24', '27'])).
% 0.44/0.66  thf('29', plain,
% 0.44/0.66      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.44/0.66             ((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['21', '28'])).
% 0.44/0.66  thf('30', plain,
% 0.44/0.66      (![X38 : $i, X39 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X38 @ X39)
% 0.44/0.66          | ((k4_xboole_0 @ (k1_tarski @ X38) @ X39) != (k1_tarski @ X38)))),
% 0.44/0.66      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.44/0.66  thf('31', plain,
% 0.44/0.66      ((![X0 : $i]:
% 0.44/0.66          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_B))
% 0.44/0.66           | ~ (r2_hidden @ sk_B @ X0)))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.44/0.66             ((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.66  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf(t36_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.66  thf('33', plain,
% 0.44/0.66      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.44/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.66  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.66      inference('sup+', [status(thm)], ['32', '33'])).
% 0.44/0.66  thf('35', plain,
% 0.44/0.66      (![X11 : $i, X13 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.44/0.66          | ~ (r1_tarski @ X11 @ X13))),
% 0.44/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.66  thf('36', plain,
% 0.44/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.66  thf('37', plain,
% 0.44/0.66      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.44/0.66             ((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['21', '28'])).
% 0.44/0.66  thf('38', plain,
% 0.44/0.66      ((![X0 : $i]:
% 0.44/0.66          (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_B @ X0)))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.44/0.66             ((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('demod', [status(thm)], ['31', '36', '37'])).
% 0.44/0.66  thf('39', plain,
% 0.44/0.66      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ X0))
% 0.44/0.66         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.44/0.66             ((r2_hidden @ sk_B @ sk_A)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.66  thf('40', plain,
% 0.44/0.66      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.44/0.66       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['20', '39'])).
% 0.44/0.66  thf('41', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.44/0.66      inference('sat_resolution*', [status(thm)], ['2', '40'])).
% 0.44/0.66  thf('42', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.44/0.66      inference('simpl_trail', [status(thm)], ['1', '41'])).
% 0.44/0.66  thf('43', plain,
% 0.44/0.66      (![X38 : $i, X40 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ (k1_tarski @ X38) @ X40) = (k1_tarski @ X38))
% 0.44/0.66          | (r2_hidden @ X38 @ X40))),
% 0.44/0.66      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.44/0.66  thf('44', plain,
% 0.44/0.66      (![X18 : $i, X19 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.66           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('45', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.44/0.66            = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.44/0.66          | (r2_hidden @ X0 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.44/0.66  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf('47', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.44/0.66          | (r2_hidden @ X0 @ X1))),
% 0.44/0.66      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.66  thf('48', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf(t100_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.66  thf('49', plain,
% 0.44/0.66      (![X14 : $i, X15 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X14 @ X15)
% 0.44/0.66           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.66  thf('50', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['48', '49'])).
% 0.44/0.66  thf('51', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.44/0.66            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.44/0.66          | (r2_hidden @ X1 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['47', '50'])).
% 0.44/0.66  thf('52', plain,
% 0.44/0.66      (![X18 : $i, X19 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.66           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('53', plain,
% 0.44/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.66  thf('54', plain,
% 0.44/0.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['52', '53'])).
% 0.44/0.66  thf('55', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf('56', plain,
% 0.44/0.66      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.66  thf('57', plain,
% 0.44/0.66      (![X14 : $i, X15 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X14 @ X15)
% 0.44/0.66           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.66  thf('58', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['56', '57'])).
% 0.44/0.66  thf('59', plain,
% 0.44/0.66      (![X18 : $i, X19 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.66           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('60', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.44/0.66           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['58', '59'])).
% 0.44/0.66  thf('61', plain,
% 0.44/0.66      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.66  thf('62', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['60', '61'])).
% 0.44/0.66  thf('63', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i]:
% 0.44/0.66         ((r1_tarski @ X11 @ X12)
% 0.44/0.66          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.66  thf('64', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.66          | (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('65', plain,
% 0.44/0.66      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.66      inference('simplify', [status(thm)], ['64'])).
% 0.44/0.66  thf('66', plain,
% 0.44/0.66      (![X8 : $i, X10 : $i]:
% 0.44/0.66         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.44/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.66  thf('67', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.44/0.66          | ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.66  thf('68', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['56', '57'])).
% 0.44/0.66  thf('69', plain,
% 0.44/0.66      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.44/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.66  thf('70', plain,
% 0.44/0.66      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.44/0.66      inference('sup+', [status(thm)], ['68', '69'])).
% 0.44/0.66  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['67', '70'])).
% 0.44/0.66  thf('72', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.44/0.66          | (r2_hidden @ X1 @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['51', '71'])).
% 0.44/0.66  thf('73', plain,
% 0.44/0.66      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.44/0.66         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.44/0.66      inference('split', [status(esa)], ['8'])).
% 0.44/0.66  thf('74', plain,
% 0.44/0.66      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.44/0.66       ((r2_hidden @ sk_B @ sk_A))),
% 0.44/0.66      inference('split', [status(esa)], ['8'])).
% 0.44/0.66  thf('75', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.44/0.66      inference('sat_resolution*', [status(thm)], ['2', '40', '74'])).
% 0.44/0.66  thf('76', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.44/0.66      inference('simpl_trail', [status(thm)], ['73', '75'])).
% 0.44/0.66  thf('77', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['72', '76'])).
% 0.44/0.66  thf('78', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.44/0.66      inference('simplify', [status(thm)], ['77'])).
% 0.44/0.66  thf('79', plain, ($false), inference('demod', [status(thm)], ['42', '78'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
