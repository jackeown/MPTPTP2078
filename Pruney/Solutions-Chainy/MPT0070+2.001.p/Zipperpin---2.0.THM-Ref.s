%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AWUfxFt6Dm

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:32 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 150 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   23
%              Number of atoms          :  662 (1083 expanded)
%              Number of equality atoms :   74 ( 116 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42','43','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['30','51','52'])).

thf('54',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['10','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62','63'])).

thf('65',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','68'])).

thf('70',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['7','69'])).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AWUfxFt6Dm
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:42:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 1297 iterations in 0.458s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.94  thf(t63_xboole_1, conjecture,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.76/0.94       ( r1_xboole_0 @ A @ C ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.94        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.76/0.94          ( r1_xboole_0 @ A @ C ) ) )),
% 0.76/0.94    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.76/0.94  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(l32_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.94  thf('2', plain,
% 0.76/0.94      (![X8 : $i, X10 : $i]:
% 0.76/0.94         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.76/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.94  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.94  thf(t48_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.94  thf('4', plain,
% 0.76/0.94      (![X17 : $i, X18 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.76/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('5', plain,
% 0.76/0.94      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['3', '4'])).
% 0.76/0.94  thf(t3_boole, axiom,
% 0.76/0.94    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.94  thf('6', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.94  thf('7', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['5', '6'])).
% 0.76/0.94  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.94  thf('8', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.94  thf('9', plain,
% 0.76/0.94      (![X17 : $i, X18 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.76/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf(commutativity_k2_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.76/0.94  thf('10', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.94  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(d7_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.76/0.94       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.94  thf('12', plain,
% 0.76/0.94      (![X4 : $i, X5 : $i]:
% 0.76/0.94         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.76/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.94  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.94  thf('14', plain,
% 0.76/0.94      (![X17 : $i, X18 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.76/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('15', plain,
% 0.76/0.94      (![X17 : $i, X18 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.76/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('16', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.94           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.94  thf('17', plain,
% 0.76/0.94      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.76/0.94         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['13', '16'])).
% 0.76/0.94  thf('18', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.94  thf('19', plain,
% 0.76/0.94      (((sk_B) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.76/0.94      inference('demod', [status(thm)], ['17', '18'])).
% 0.76/0.94  thf(t36_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.94  thf('20', plain,
% 0.76/0.94      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.76/0.94      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.76/0.94  thf('21', plain,
% 0.76/0.94      (![X8 : $i, X10 : $i]:
% 0.76/0.94         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.76/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.94  thf('22', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.94  thf(t41_xboole_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.94       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.76/0.94  thf('23', plain,
% 0.76/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.76/0.94           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.94  thf('24', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.76/0.94  thf('25', plain,
% 0.76/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.76/0.94           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.94  thf('26', plain,
% 0.76/0.94      (![X17 : $i, X18 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.76/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('27', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X2 @ 
% 0.76/0.94           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.76/0.94           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['25', '26'])).
% 0.76/0.94  thf('28', plain,
% 0.76/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.76/0.94           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.94  thf('29', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X2 @ 
% 0.76/0.94           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.76/0.94           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['27', '28'])).
% 0.76/0.94  thf('30', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0))
% 0.76/0.94           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['24', '29'])).
% 0.76/0.94  thf('31', plain,
% 0.76/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.76/0.94           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.94  thf('32', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.94  thf('33', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.76/0.94           = (k4_xboole_0 @ X1 @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['31', '32'])).
% 0.76/0.94  thf('34', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.94  thf('35', plain,
% 0.76/0.94      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.76/0.94      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.76/0.94  thf('36', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.94      inference('sup+', [status(thm)], ['34', '35'])).
% 0.76/0.94  thf('37', plain,
% 0.76/0.94      (![X8 : $i, X10 : $i]:
% 0.76/0.94         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.76/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.94  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.94  thf('39', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['33', '38'])).
% 0.76/0.94  thf('40', plain,
% 0.76/0.94      (![X17 : $i, X18 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.76/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('41', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.76/0.94           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['39', '40'])).
% 0.76/0.94  thf('42', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.94  thf('43', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.94  thf('44', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.94  thf('45', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.76/0.94  thf('46', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['44', '45'])).
% 0.76/0.94  thf('47', plain,
% 0.76/0.94      (![X17 : $i, X18 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.76/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('48', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.76/0.94           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['46', '47'])).
% 0.76/0.94  thf('49', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.76/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.94  thf('50', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['48', '49'])).
% 0.76/0.94  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['41', '42', '43', '50'])).
% 0.76/0.94  thf('52', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.94  thf('53', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X0 @ X1)
% 0.76/0.94           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.94      inference('demod', [status(thm)], ['30', '51', '52'])).
% 0.76/0.94  thf('54', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['19', '53'])).
% 0.76/0.94  thf('55', plain,
% 0.76/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.76/0.94           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.94  thf('56', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ sk_B @ X0)
% 0.76/0.94           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['54', '55'])).
% 0.76/0.94  thf('57', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ sk_B @ X0)
% 0.76/0.94           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['10', '56'])).
% 0.76/0.94  thf('58', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X2 @ 
% 0.76/0.94           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.76/0.94           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.76/0.94      inference('demod', [status(thm)], ['27', '28'])).
% 0.76/0.94  thf('59', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ X0)))
% 0.76/0.94           = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C))),
% 0.76/0.94      inference('sup+', [status(thm)], ['57', '58'])).
% 0.76/0.94  thf('60', plain,
% 0.76/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.76/0.94           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.94  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.94  thf('62', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.76/0.94           = (k1_xboole_0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['60', '61'])).
% 0.76/0.94  thf('63', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.94  thf('64', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['59', '62', '63'])).
% 0.76/0.94  thf('65', plain,
% 0.76/0.94      (![X4 : $i, X6 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.94  thf('66', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.94          | (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['64', '65'])).
% 0.76/0.94  thf('67', plain,
% 0.76/0.94      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0))),
% 0.76/0.94      inference('simplify', [status(thm)], ['66'])).
% 0.76/0.94  thf('68', plain,
% 0.76/0.94      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['9', '67'])).
% 0.76/0.94  thf('69', plain,
% 0.76/0.94      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['8', '68'])).
% 0.76/0.94  thf('70', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.76/0.94      inference('sup+', [status(thm)], ['7', '69'])).
% 0.76/0.94  thf('71', plain,
% 0.76/0.94      (![X4 : $i, X5 : $i]:
% 0.76/0.94         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.76/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.94  thf('72', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['70', '71'])).
% 0.76/0.94  thf('73', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.94  thf('74', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['72', '73'])).
% 0.76/0.94  thf('75', plain,
% 0.76/0.94      (![X4 : $i, X6 : $i]:
% 0.76/0.94         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.76/0.94  thf('76', plain,
% 0.76/0.94      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.76/0.94      inference('sup-', [status(thm)], ['74', '75'])).
% 0.76/0.94  thf('77', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.76/0.94      inference('simplify', [status(thm)], ['76'])).
% 0.76/0.94  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
