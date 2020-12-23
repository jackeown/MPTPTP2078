%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4psozeg4sB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:15 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 350 expanded)
%              Number of leaves         :   19 ( 106 expanded)
%              Depth                    :   22
%              Number of atoms          :  939 (3098 expanded)
%              Number of equality atoms :   90 ( 278 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k4_xboole_0 @ X42 @ ( k1_tarski @ X43 ) )
        = X42 )
      | ( r2_hidden @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('28',plain,
    ( ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('36',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_A ) )
        | ( X0
          = ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
        = ( k3_xboole_0 @ X0 @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
        = X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( ( k4_xboole_0 @ X42 @ ( k1_tarski @ X41 ) )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k4_xboole_0 @ X42 @ ( k1_tarski @ X43 ) )
        = X42 )
      | ( r2_hidden @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('73',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','81'])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('84',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('85',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','49','84'])).

thf('86',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['83','85'])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['51','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4psozeg4sB
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 593 iterations in 0.301s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(t67_zfmisc_1, conjecture,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.53/0.75       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i,B:$i]:
% 0.53/0.75        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.53/0.75          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.53/0.75  thf('0', plain,
% 0.53/0.75      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.53/0.75        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('1', plain,
% 0.53/0.75      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.75      inference('split', [status(esa)], ['0'])).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.53/0.75       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('split', [status(esa)], ['0'])).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      (((r2_hidden @ sk_A @ sk_B)
% 0.53/0.75        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.75      inference('split', [status(esa)], ['3'])).
% 0.53/0.75  thf(d3_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      (![X3 : $i, X5 : $i]:
% 0.53/0.75         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf(d10_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.75  thf('6', plain,
% 0.53/0.75      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('7', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.53/0.75      inference('simplify', [status(thm)], ['6'])).
% 0.53/0.75  thf(t28_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      (![X17 : $i, X18 : $i]:
% 0.53/0.75         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.53/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.75  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.75  thf(t48_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X21 : $i, X22 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.53/0.75           = (k3_xboole_0 @ X21 @ X22))),
% 0.53/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.75  thf(d5_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.53/0.75       ( ![D:$i]:
% 0.53/0.75         ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.75           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X10 @ X9)
% 0.53/0.75          | ~ (r2_hidden @ X10 @ X8)
% 0.53/0.75          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X10 @ X8)
% 0.53/0.75          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['11'])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.75          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['10', '12'])).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X1 @ X0)
% 0.53/0.75          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['9', '13'])).
% 0.53/0.75  thf(t36_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.75  thf('15', plain,
% 0.53/0.75      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 0.53/0.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X2 @ X3)
% 0.53/0.75          | (r2_hidden @ X2 @ X4)
% 0.53/0.75          | ~ (r1_tarski @ X3 @ X4))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.75  thf('18', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['14', '17'])).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.53/0.75      inference('sup-', [status(thm)], ['5', '18'])).
% 0.53/0.75  thf('20', plain,
% 0.53/0.75      (![X3 : $i, X5 : $i]:
% 0.53/0.75         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('21', plain,
% 0.53/0.75      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.75      inference('split', [status(esa)], ['3'])).
% 0.53/0.75  thf('22', plain,
% 0.53/0.75      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.53/0.75         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.75      inference('split', [status(esa)], ['0'])).
% 0.53/0.75  thf('23', plain,
% 0.53/0.75      (![X21 : $i, X22 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.53/0.75           = (k3_xboole_0 @ X21 @ X22))),
% 0.53/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.53/0.75          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.53/0.75         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.75      inference('sup+', [status(thm)], ['22', '23'])).
% 0.53/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.75  thf('26', plain,
% 0.53/0.75      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.53/0.75          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.53/0.75         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.75      inference('demod', [status(thm)], ['24', '25'])).
% 0.53/0.75  thf(t65_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.53/0.75       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.53/0.75  thf('27', plain,
% 0.53/0.75      (![X42 : $i, X43 : $i]:
% 0.53/0.75         (((k4_xboole_0 @ X42 @ (k1_tarski @ X43)) = (X42))
% 0.53/0.75          | (r2_hidden @ X43 @ X42))),
% 0.53/0.75      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))
% 0.53/0.76         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['26', '27'])).
% 0.53/0.76  thf('29', plain,
% 0.53/0.76      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.76      inference('split', [status(esa)], ['0'])).
% 0.53/0.76  thf('30', plain,
% 0.53/0.76      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.53/0.76         (~ (r2_hidden @ X10 @ X8)
% 0.53/0.76          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.53/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.53/0.76  thf('31', plain,
% 0.53/0.76      ((![X0 : $i]:
% 0.53/0.76          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.76  thf('32', plain,
% 0.53/0.76      (((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))
% 0.53/0.76         | ~ (r2_hidden @ sk_A @ sk_B)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['28', '31'])).
% 0.53/0.76  thf('33', plain,
% 0.53/0.76      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['21', '32'])).
% 0.53/0.76  thf('34', plain,
% 0.53/0.76      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.53/0.76          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.53/0.76  thf('35', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.76      inference('clc', [status(thm)], ['14', '17'])).
% 0.53/0.76  thf('36', plain,
% 0.53/0.76      ((![X0 : $i]:
% 0.53/0.76          ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.76  thf('37', plain,
% 0.53/0.76      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['33', '36'])).
% 0.53/0.76  thf('38', plain,
% 0.53/0.76      ((![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['20', '37'])).
% 0.53/0.76  thf('39', plain,
% 0.53/0.76      (![X12 : $i, X14 : $i]:
% 0.53/0.76         (((X12) = (X14))
% 0.53/0.76          | ~ (r1_tarski @ X14 @ X12)
% 0.53/0.76          | ~ (r1_tarski @ X12 @ X14))),
% 0.53/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.76  thf('40', plain,
% 0.53/0.76      ((![X0 : $i]:
% 0.53/0.76          (~ (r1_tarski @ X0 @ (k1_tarski @ sk_A))
% 0.53/0.76           | ((X0) = (k1_tarski @ sk_A))))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.76  thf('41', plain,
% 0.53/0.76      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ sk_A)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['19', '40'])).
% 0.53/0.76  thf('42', plain,
% 0.53/0.76      (![X21 : $i, X22 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.53/0.76           = (k3_xboole_0 @ X21 @ X22))),
% 0.53/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.76  thf('43', plain,
% 0.53/0.76      ((![X0 : $i]:
% 0.53/0.76          ((k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)) = (k3_xboole_0 @ X0 @ X0)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['41', '42'])).
% 0.53/0.76  thf('44', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.76  thf('45', plain,
% 0.53/0.76      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)) = (X0)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('demod', [status(thm)], ['43', '44'])).
% 0.53/0.76  thf('46', plain,
% 0.53/0.76      (![X41 : $i, X42 : $i]:
% 0.53/0.76         (~ (r2_hidden @ X41 @ X42)
% 0.53/0.76          | ((k4_xboole_0 @ X42 @ (k1_tarski @ X41)) != (X42)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.53/0.76  thf('47', plain,
% 0.53/0.76      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_A @ X0)))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.76  thf('48', plain,
% 0.53/0.76      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ X0))
% 0.53/0.76         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.53/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.53/0.76      inference('simplify', [status(thm)], ['47'])).
% 0.53/0.76  thf('49', plain,
% 0.53/0.76      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.53/0.76       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.53/0.76      inference('sup-', [status(thm)], ['4', '48'])).
% 0.53/0.76  thf('50', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.53/0.76      inference('sat_resolution*', [status(thm)], ['2', '49'])).
% 0.53/0.76  thf('51', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.53/0.76      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.53/0.76  thf('52', plain,
% 0.53/0.76      (![X42 : $i, X43 : $i]:
% 0.53/0.76         (((k4_xboole_0 @ X42 @ (k1_tarski @ X43)) = (X42))
% 0.53/0.76          | (r2_hidden @ X43 @ X42))),
% 0.53/0.76      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.53/0.76  thf('53', plain,
% 0.53/0.76      (![X21 : $i, X22 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.53/0.76           = (k3_xboole_0 @ X21 @ X22))),
% 0.53/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.76  thf('54', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['52', '53'])).
% 0.53/0.76  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.76  thf(t100_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.76  thf('56', plain,
% 0.53/0.76      (![X15 : $i, X16 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X15 @ X16)
% 0.53/0.76           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.76  thf('57', plain,
% 0.53/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['55', '56'])).
% 0.53/0.76  thf('58', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('demod', [status(thm)], ['54', '57'])).
% 0.53/0.76  thf('59', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.76  thf('60', plain,
% 0.53/0.76      (![X21 : $i, X22 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.53/0.76           = (k3_xboole_0 @ X21 @ X22))),
% 0.53/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.76  thf('61', plain,
% 0.53/0.76      (![X21 : $i, X22 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.53/0.76           = (k3_xboole_0 @ X21 @ X22))),
% 0.53/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.76  thf('62', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.76           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['60', '61'])).
% 0.53/0.76  thf('63', plain,
% 0.53/0.76      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 0.53/0.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.76  thf('64', plain,
% 0.53/0.76      (![X17 : $i, X18 : $i]:
% 0.53/0.76         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.53/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.76  thf('65', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.53/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('sup-', [status(thm)], ['63', '64'])).
% 0.53/0.76  thf('66', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.76  thf('67', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.53/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('demod', [status(thm)], ['65', '66'])).
% 0.53/0.76  thf('68', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.76           = (k4_xboole_0 @ X1 @ X0))),
% 0.53/0.76      inference('demod', [status(thm)], ['62', '67'])).
% 0.53/0.76  thf('69', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('sup+', [status(thm)], ['59', '68'])).
% 0.53/0.76  thf('70', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k4_xboole_0 @ (k1_tarski @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 0.53/0.76            = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['58', '69'])).
% 0.53/0.76  thf('71', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.53/0.76      inference('sup-', [status(thm)], ['5', '18'])).
% 0.53/0.76  thf('72', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.53/0.76      inference('sup-', [status(thm)], ['5', '18'])).
% 0.53/0.76  thf('73', plain,
% 0.53/0.76      (![X12 : $i, X14 : $i]:
% 0.53/0.76         (((X12) = (X14))
% 0.53/0.76          | ~ (r1_tarski @ X14 @ X12)
% 0.53/0.76          | ~ (r1_tarski @ X12 @ X14))),
% 0.53/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.76  thf('74', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.53/0.76          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['72', '73'])).
% 0.53/0.76  thf('75', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['71', '74'])).
% 0.53/0.76  thf('76', plain,
% 0.53/0.76      (![X21 : $i, X22 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.53/0.76           = (k3_xboole_0 @ X21 @ X22))),
% 0.53/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.76  thf('77', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.53/0.76           = (k3_xboole_0 @ X1 @ X1))),
% 0.53/0.76      inference('sup+', [status(thm)], ['75', '76'])).
% 0.53/0.76  thf('78', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.76  thf('79', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.53/0.76      inference('demod', [status(thm)], ['77', '78'])).
% 0.53/0.76  thf('80', plain,
% 0.53/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['55', '56'])).
% 0.53/0.76  thf('81', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.53/0.76      inference('demod', [status(thm)], ['79', '80'])).
% 0.53/0.76  thf('82', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('demod', [status(thm)], ['70', '81'])).
% 0.53/0.76  thf('83', plain,
% 0.53/0.76      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.53/0.76         <= (~
% 0.53/0.76             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.53/0.76      inference('split', [status(esa)], ['3'])).
% 0.53/0.76  thf('84', plain,
% 0.53/0.76      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.53/0.76       ((r2_hidden @ sk_A @ sk_B))),
% 0.53/0.76      inference('split', [status(esa)], ['3'])).
% 0.53/0.76  thf('85', plain,
% 0.53/0.76      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.53/0.76      inference('sat_resolution*', [status(thm)], ['2', '49', '84'])).
% 0.53/0.76  thf('86', plain,
% 0.53/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.53/0.76      inference('simpl_trail', [status(thm)], ['83', '85'])).
% 0.53/0.76  thf('87', plain,
% 0.53/0.76      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.53/0.76      inference('sup-', [status(thm)], ['82', '86'])).
% 0.53/0.76  thf('88', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.53/0.76      inference('simplify', [status(thm)], ['87'])).
% 0.53/0.76  thf('89', plain, ($false), inference('demod', [status(thm)], ['51', '88'])).
% 0.53/0.76  
% 0.53/0.76  % SZS output end Refutation
% 0.53/0.76  
% 0.62/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
