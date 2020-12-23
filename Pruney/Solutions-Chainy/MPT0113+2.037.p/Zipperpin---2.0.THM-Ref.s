%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NRWJ6rA6S2

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:33 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 170 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  551 (1174 expanded)
%              Number of equality atoms :   53 ( 112 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['4','24'])).

thf('26',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['39','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['31','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['30','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NRWJ6rA6S2
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.70/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.92  % Solved by: fo/fo7.sh
% 0.70/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.92  % done 952 iterations in 0.459s
% 0.70/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.92  % SZS output start Refutation
% 0.70/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(t106_xboole_1, conjecture,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.70/0.92       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.70/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.92        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.70/0.92          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.70/0.92    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.70/0.92  thf('0', plain,
% 0.70/0.92      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('1', plain,
% 0.70/0.92      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.70/0.92      inference('split', [status(esa)], ['0'])).
% 0.70/0.92  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(t28_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.92  thf('3', plain,
% 0.70/0.92      (![X13 : $i, X14 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.70/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.92  thf('4', plain,
% 0.70/0.92      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.92  thf('5', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf(t79_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.70/0.92  thf('6', plain,
% 0.70/0.92      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.70/0.92      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.70/0.92  thf(d7_xboole_0, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.70/0.92       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.92  thf('7', plain,
% 0.70/0.92      (![X2 : $i, X3 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.70/0.92      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.92  thf('8', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.92  thf('9', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf('10', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['8', '9'])).
% 0.70/0.92  thf(t16_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.92       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.70/0.92  thf('11', plain,
% 0.70/0.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.70/0.92           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.70/0.92  thf('12', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.92           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['10', '11'])).
% 0.70/0.92  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.70/0.92  thf('13', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.70/0.92  thf('14', plain,
% 0.70/0.92      (![X2 : $i, X3 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.70/0.92      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.92  thf('15', plain,
% 0.70/0.92      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.92  thf('16', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf('17', plain,
% 0.70/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['15', '16'])).
% 0.70/0.92  thf('18', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         ((k1_xboole_0)
% 0.70/0.92           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['12', '17'])).
% 0.70/0.92  thf('19', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf('20', plain,
% 0.70/0.92      (![X2 : $i, X4 : $i]:
% 0.70/0.92         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.92  thf('21', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['19', '20'])).
% 0.70/0.92  thf('22', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         (((k1_xboole_0) != (k1_xboole_0))
% 0.70/0.92          | (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['18', '21'])).
% 0.70/0.92  thf('23', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1)),
% 0.70/0.92      inference('simplify', [status(thm)], ['22'])).
% 0.70/0.92  thf('24', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.70/0.92      inference('sup+', [status(thm)], ['5', '23'])).
% 0.70/0.92  thf('25', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.70/0.92      inference('sup+', [status(thm)], ['4', '24'])).
% 0.70/0.92  thf('26', plain,
% 0.70/0.92      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.70/0.92      inference('split', [status(esa)], ['0'])).
% 0.70/0.92  thf('27', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.92      inference('sup-', [status(thm)], ['25', '26'])).
% 0.70/0.92  thf('28', plain,
% 0.70/0.92      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.92      inference('split', [status(esa)], ['0'])).
% 0.70/0.92  thf('29', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.70/0.92      inference('sat_resolution*', [status(thm)], ['27', '28'])).
% 0.70/0.92  thf('30', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.70/0.92      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.70/0.92  thf('31', plain,
% 0.70/0.92      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf('32', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf(t36_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.92  thf('33', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.70/0.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.92  thf('34', plain,
% 0.70/0.92      (![X13 : $i, X14 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.70/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.92  thf('35', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.70/0.92           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['33', '34'])).
% 0.70/0.92  thf('36', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf('37', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.92           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['35', '36'])).
% 0.70/0.92  thf('38', plain,
% 0.70/0.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.70/0.92           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.70/0.92  thf('39', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.70/0.92           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['37', '38'])).
% 0.70/0.92  thf('40', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.92           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['35', '36'])).
% 0.70/0.92  thf('41', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['8', '9'])).
% 0.70/0.92  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['40', '41'])).
% 0.70/0.92  thf(l32_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.92  thf('43', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i]:
% 0.70/0.92         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.70/0.92  thf('44', plain,
% 0.70/0.92      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['42', '43'])).
% 0.70/0.92  thf('45', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.70/0.92      inference('simplify', [status(thm)], ['44'])).
% 0.70/0.92  thf('46', plain,
% 0.70/0.92      (![X13 : $i, X14 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.70/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.92  thf('47', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['45', '46'])).
% 0.70/0.92  thf('48', plain,
% 0.70/0.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.70/0.92           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.70/0.92  thf('49', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k3_xboole_0 @ X0 @ X1)
% 0.70/0.92           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['47', '48'])).
% 0.70/0.92  thf('50', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf(t100_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.92  thf('51', plain,
% 0.70/0.92      (![X8 : $i, X9 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X8 @ X9)
% 0.70/0.92           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.92  thf('52', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X0 @ X1)
% 0.70/0.92           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['50', '51'])).
% 0.70/0.92  thf('53', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.70/0.92           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['49', '52'])).
% 0.70/0.92  thf('54', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['45', '46'])).
% 0.70/0.92  thf('55', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X0 @ X1)
% 0.70/0.92           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['50', '51'])).
% 0.70/0.92  thf('56', plain,
% 0.70/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['54', '55'])).
% 0.70/0.92  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['40', '41'])).
% 0.70/0.92  thf('58', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['56', '57'])).
% 0.70/0.92  thf('59', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['53', '58'])).
% 0.70/0.92  thf('60', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i]:
% 0.70/0.92         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.70/0.92  thf('61', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (((k1_xboole_0) != (k1_xboole_0))
% 0.70/0.92          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['59', '60'])).
% 0.70/0.92  thf('62', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.70/0.92      inference('simplify', [status(thm)], ['61'])).
% 0.70/0.92  thf('63', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         (r1_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 0.70/0.92      inference('sup+', [status(thm)], ['39', '62'])).
% 0.70/0.92  thf('64', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)),
% 0.70/0.92      inference('sup+', [status(thm)], ['32', '63'])).
% 0.70/0.92  thf('65', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.70/0.92      inference('sup+', [status(thm)], ['31', '64'])).
% 0.70/0.92  thf('66', plain, ($false), inference('demod', [status(thm)], ['30', '65'])).
% 0.70/0.92  
% 0.70/0.92  % SZS output end Refutation
% 0.70/0.92  
% 0.75/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
