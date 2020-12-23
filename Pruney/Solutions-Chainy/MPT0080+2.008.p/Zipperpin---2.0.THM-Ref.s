%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNlViUXzdi

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:05 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 123 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  591 ( 892 expanded)
%              Number of equality atoms :   64 (  97 expanded)
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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','38','39','40','41'])).

thf('43',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['43','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','61'])).

thf('63',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNlViUXzdi
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 1235 iterations in 0.478s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(t73_xboole_1, conjecture,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.75/0.93       ( r1_tarski @ A @ B ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.93        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ C ) ) =>
% 0.75/0.93          ( r1_tarski @ A @ B ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.75/0.93  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(l32_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X7 : $i, X9 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.93  thf(t41_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.93       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.75/0.93           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i]:
% 0.75/0.93         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.75/0.93          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['5', '6'])).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.75/0.93          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['4', '7'])).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.93        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['3', '8'])).
% 0.75/0.93  thf('10', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(d7_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.93       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      (![X4 : $i, X5 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.75/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.93  thf('12', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.93  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf('14', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.75/0.93      inference('demod', [status(thm)], ['12', '13'])).
% 0.75/0.93  thf(t48_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.93           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.93           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['15', '16'])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.75/0.93         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['14', '17'])).
% 0.75/0.93  thf(t3_boole, axiom,
% 0.75/0.93    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.94  thf('19', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (((sk_C) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.94  thf(t40_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 0.75/0.94           = (k4_xboole_0 @ X11 @ X12))),
% 0.75/0.94      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.75/0.94  thf('22', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['21', '22'])).
% 0.75/0.94  thf('24', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf(t7_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.75/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.94  thf('27', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.75/0.94      inference('sup+', [status(thm)], ['25', '26'])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X7 : $i, X9 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.94  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['27', '28'])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X16 : $i, X17 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.94           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.75/0.94           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.75/0.94           = (k4_xboole_0 @ X2 @ 
% 0.75/0.94              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.75/0.94           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.75/0.94           = (k4_xboole_0 @ X2 @ 
% 0.75/0.94              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.75/0.94      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 0.75/0.94           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.75/0.94              (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['29', '34'])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 0.75/0.94           = (k4_xboole_0 @ X11 @ X12))),
% 0.75/0.94      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('demod', [status(thm)], ['35', '38', '39', '40', '41'])).
% 0.75/0.94  thf('43', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['20', '42'])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 0.75/0.94           = (k4_xboole_0 @ X11 @ X12))),
% 0.75/0.94      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      (![X16 : $i, X17 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.94           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['44', '45'])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('48', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['46', '47'])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.75/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['49', '50'])).
% 0.75/0.94  thf('52', plain,
% 0.75/0.94      (![X7 : $i, X9 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['51', '52'])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (![X16 : $i, X17 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.94           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.75/0.94           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['53', '54'])).
% 0.75/0.94  thf('56', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['55', '56'])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['48', '57'])).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_C) = (sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['43', '58'])).
% 0.75/0.94  thf('60', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('61', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['59', '60'])).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['9', '61'])).
% 0.75/0.94  thf('63', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.75/0.94      inference('simplify', [status(thm)], ['62'])).
% 0.75/0.94  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
