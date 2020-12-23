%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EJ0lz3Z0il

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:08 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 215 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  687 (1518 expanded)
%              Number of equality atoms :   75 ( 178 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('22',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['22','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','56','74'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EJ0lz3Z0il
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.04/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.24  % Solved by: fo/fo7.sh
% 1.04/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.24  % done 1008 iterations in 0.769s
% 1.04/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.24  % SZS output start Refutation
% 1.04/1.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.04/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.04/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.04/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.04/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.04/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.24  thf(t73_xboole_1, conjecture,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.04/1.24       ( r1_tarski @ A @ B ) ))).
% 1.04/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.24    (~( ![A:$i,B:$i,C:$i]:
% 1.04/1.24        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 1.04/1.24            ( r1_xboole_0 @ A @ C ) ) =>
% 1.04/1.24          ( r1_tarski @ A @ B ) ) )),
% 1.04/1.24    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 1.04/1.24  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(t40_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.04/1.24  thf('1', plain,
% 1.04/1.24      (![X11 : $i, X12 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 1.04/1.24           = (k4_xboole_0 @ X11 @ X12))),
% 1.04/1.24      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.04/1.24  thf(t3_boole, axiom,
% 1.04/1.24    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.04/1.24  thf('2', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.04/1.24      inference('cnf', [status(esa)], [t3_boole])).
% 1.04/1.24  thf('3', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['1', '2'])).
% 1.04/1.24  thf('4', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.04/1.24      inference('cnf', [status(esa)], [t3_boole])).
% 1.04/1.24  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['3', '4'])).
% 1.04/1.24  thf(t7_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.04/1.24  thf('6', plain,
% 1.04/1.24      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.04/1.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.04/1.24  thf(l32_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.04/1.24  thf('7', plain,
% 1.04/1.24      (![X5 : $i, X7 : $i]:
% 1.04/1.24         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.04/1.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.04/1.24  thf('8', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['6', '7'])).
% 1.04/1.24  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['5', '8'])).
% 1.04/1.24  thf(t39_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.04/1.24  thf('10', plain,
% 1.04/1.24      (![X8 : $i, X9 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.04/1.24           = (k2_xboole_0 @ X8 @ X9))),
% 1.04/1.24      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.04/1.24  thf('11', plain,
% 1.04/1.24      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['9', '10'])).
% 1.04/1.24  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['3', '4'])).
% 1.04/1.24  thf('13', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.04/1.24      inference('demod', [status(thm)], ['11', '12'])).
% 1.04/1.24  thf('14', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('15', plain,
% 1.04/1.24      (![X5 : $i, X7 : $i]:
% 1.04/1.24         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.04/1.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.04/1.24  thf('16', plain,
% 1.04/1.24      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['14', '15'])).
% 1.04/1.24  thf(t41_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.04/1.24       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.04/1.24  thf('17', plain,
% 1.04/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.04/1.24           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.04/1.24  thf('18', plain,
% 1.04/1.24      (![X8 : $i, X9 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.04/1.24           = (k2_xboole_0 @ X8 @ X9))),
% 1.04/1.24      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.04/1.24  thf('19', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.04/1.24           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['17', '18'])).
% 1.04/1.24  thf('20', plain,
% 1.04/1.24      (((k2_xboole_0 @ sk_C @ k1_xboole_0)
% 1.04/1.24         = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['16', '19'])).
% 1.04/1.24  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['3', '4'])).
% 1.04/1.24  thf('22', plain,
% 1.04/1.24      (((sk_C) = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('demod', [status(thm)], ['20', '21'])).
% 1.04/1.24  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['5', '8'])).
% 1.04/1.24  thf('24', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.04/1.24           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['17', '18'])).
% 1.04/1.24  thf('25', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.04/1.24           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['23', '24'])).
% 1.04/1.24  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['3', '4'])).
% 1.04/1.24  thf(commutativity_k2_xboole_0, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.04/1.24  thf('27', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('28', plain,
% 1.04/1.24      (![X11 : $i, X12 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 1.04/1.24           = (k4_xboole_0 @ X11 @ X12))),
% 1.04/1.24      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.04/1.24  thf('29', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.04/1.24           = (k4_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('sup+', [status(thm)], ['27', '28'])).
% 1.04/1.24  thf('30', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['25', '26', '29'])).
% 1.04/1.24  thf('31', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('32', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('33', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['6', '7'])).
% 1.04/1.24  thf('34', plain,
% 1.04/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.04/1.24           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.04/1.24  thf('35', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.04/1.24           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['33', '34'])).
% 1.04/1.24  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['3', '4'])).
% 1.04/1.24  thf('37', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('38', plain,
% 1.04/1.24      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.04/1.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.04/1.24  thf('39', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.04/1.24  thf('40', plain,
% 1.04/1.24      (![X5 : $i, X7 : $i]:
% 1.04/1.24         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.04/1.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.04/1.24  thf('41', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['39', '40'])).
% 1.04/1.24  thf('42', plain,
% 1.04/1.24      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['36', '41'])).
% 1.04/1.24  thf('43', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         ((k1_xboole_0)
% 1.04/1.24           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['35', '42'])).
% 1.04/1.24  thf('44', plain,
% 1.04/1.24      (![X5 : $i, X6 : $i]:
% 1.04/1.24         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.04/1.24  thf('45', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.04/1.24          | (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['43', '44'])).
% 1.04/1.24  thf('46', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['45'])).
% 1.04/1.24  thf('47', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['32', '46'])).
% 1.04/1.24  thf('48', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['31', '47'])).
% 1.04/1.24  thf('49', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['30', '48'])).
% 1.04/1.24  thf('50', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) @ sk_C)),
% 1.04/1.24      inference('sup+', [status(thm)], ['22', '49'])).
% 1.04/1.24  thf('51', plain,
% 1.04/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.04/1.24           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.04/1.24  thf('52', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)) @ sk_C)),
% 1.04/1.24      inference('demod', [status(thm)], ['50', '51'])).
% 1.04/1.24  thf('53', plain,
% 1.04/1.24      (![X5 : $i, X7 : $i]:
% 1.04/1.24         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.04/1.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.04/1.24  thf('54', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)) @ 
% 1.04/1.24           sk_C) = (k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['52', '53'])).
% 1.04/1.24  thf('55', plain,
% 1.04/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.04/1.24           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.04/1.24  thf('56', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('57', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(d7_xboole_0, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.04/1.24       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.04/1.24  thf('58', plain,
% 1.04/1.24      (![X2 : $i, X3 : $i]:
% 1.04/1.24         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.04/1.24      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.04/1.24  thf('59', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['57', '58'])).
% 1.04/1.24  thf(t48_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.04/1.24  thf('60', plain,
% 1.04/1.24      (![X16 : $i, X17 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.04/1.24           = (k3_xboole_0 @ X16 @ X17))),
% 1.04/1.24      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.04/1.24  thf('61', plain,
% 1.04/1.24      (![X8 : $i, X9 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.04/1.24           = (k2_xboole_0 @ X8 @ X9))),
% 1.04/1.24      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.04/1.24  thf('62', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.04/1.24           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.04/1.24      inference('sup+', [status(thm)], ['60', '61'])).
% 1.04/1.24  thf('63', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('64', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('65', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.04/1.24           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.04/1.24  thf('66', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['25', '26', '29'])).
% 1.04/1.24  thf('67', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.04/1.24           = (X1))),
% 1.04/1.24      inference('demod', [status(thm)], ['65', '66'])).
% 1.04/1.24  thf('68', plain,
% 1.04/1.24      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 1.04/1.24      inference('sup+', [status(thm)], ['59', '67'])).
% 1.04/1.24  thf('69', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['3', '4'])).
% 1.04/1.24  thf('70', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['69', '70'])).
% 1.04/1.24  thf('72', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['68', '71'])).
% 1.04/1.24  thf('73', plain,
% 1.04/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.04/1.24           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.04/1.24  thf('74', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ sk_A @ X0)
% 1.04/1.24           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['72', '73'])).
% 1.04/1.24  thf('75', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 1.04/1.24      inference('demod', [status(thm)], ['54', '55', '56', '74'])).
% 1.04/1.24  thf('76', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['13', '75'])).
% 1.04/1.24  thf('77', plain,
% 1.04/1.24      (![X5 : $i, X6 : $i]:
% 1.04/1.24         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.04/1.24  thf('78', plain,
% 1.04/1.24      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 1.04/1.24      inference('sup-', [status(thm)], ['76', '77'])).
% 1.04/1.24  thf('79', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.04/1.24      inference('simplify', [status(thm)], ['78'])).
% 1.04/1.24  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 1.04/1.24  
% 1.04/1.24  % SZS output end Refutation
% 1.04/1.24  
% 1.04/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
