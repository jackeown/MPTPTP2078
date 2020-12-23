%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UoNP7O4S9n

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:34 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 134 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  487 ( 981 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['18','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['13','35'])).

thf('37',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['41','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UoNP7O4S9n
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:28:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.70/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.90  % Solved by: fo/fo7.sh
% 0.70/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.90  % done 950 iterations in 0.441s
% 0.70/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.90  % SZS output start Refutation
% 0.70/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(t106_xboole_1, conjecture,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.70/0.90       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.70/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.90        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.70/0.90          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.70/0.90    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.70/0.90  thf('0', plain,
% 0.70/0.90      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('1', plain,
% 0.70/0.90      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(t28_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.90  thf('3', plain,
% 0.70/0.90      (![X10 : $i, X11 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.70/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.90  thf('4', plain,
% 0.70/0.90      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.90  thf('5', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf(t100_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.90  thf('6', plain,
% 0.70/0.90      (![X5 : $i, X6 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.90           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.90  thf('7', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X0 @ X1)
% 0.70/0.90           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.70/0.90  thf('8', plain,
% 0.70/0.90      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 0.70/0.90         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.70/0.90      inference('sup+', [status(thm)], ['4', '7'])).
% 0.70/0.90  thf(t48_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.90  thf('9', plain,
% 0.70/0.90      (![X15 : $i, X16 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.70/0.90           = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.90  thf('10', plain,
% 0.70/0.90      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 0.70/0.90         (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 0.70/0.90         = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.70/0.90      inference('sup+', [status(thm)], ['8', '9'])).
% 0.70/0.90  thf('11', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf('12', plain,
% 0.70/0.90      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.90  thf('13', plain,
% 0.70/0.90      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 0.70/0.90         (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)) = (sk_A))),
% 0.70/0.90      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.70/0.90  thf(t36_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.90  thf('14', plain,
% 0.70/0.90      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.70/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.90  thf('15', plain,
% 0.70/0.90      (![X10 : $i, X11 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.70/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.90  thf('16', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.70/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['14', '15'])).
% 0.70/0.90  thf('17', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf('18', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.90  thf(t79_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.70/0.90  thf('19', plain,
% 0.70/0.90      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.70/0.90      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.70/0.90  thf(d7_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.70/0.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.90  thf('20', plain,
% 0.70/0.90      (![X2 : $i, X3 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.70/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.90  thf('21', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.70/0.90      inference('sup-', [status(thm)], ['19', '20'])).
% 0.70/0.90  thf('22', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf('23', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.70/0.90      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.90  thf(t16_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.90       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.70/0.90  thf('24', plain,
% 0.70/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.70/0.90           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.70/0.90  thf('25', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.90           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['23', '24'])).
% 0.70/0.90  thf('26', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf(t2_boole, axiom,
% 0.70/0.90    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.70/0.90  thf('27', plain,
% 0.70/0.90      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.90      inference('cnf', [status(esa)], [t2_boole])).
% 0.70/0.90  thf('28', plain,
% 0.70/0.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['26', '27'])).
% 0.70/0.90  thf('29', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((k1_xboole_0)
% 0.70/0.90           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 0.70/0.90      inference('demod', [status(thm)], ['25', '28'])).
% 0.70/0.90  thf('30', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.90  thf('31', plain,
% 0.70/0.90      (![X2 : $i, X4 : $i]:
% 0.70/0.90         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.70/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.90  thf('32', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['30', '31'])).
% 0.70/0.90  thf('33', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (((k1_xboole_0) != (k1_xboole_0))
% 0.70/0.90          | (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['29', '32'])).
% 0.70/0.90  thf('34', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1)),
% 0.70/0.90      inference('simplify', [status(thm)], ['33'])).
% 0.70/0.90  thf('35', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1)),
% 0.70/0.90      inference('sup+', [status(thm)], ['18', '34'])).
% 0.70/0.90  thf('36', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.70/0.90      inference('sup+', [status(thm)], ['13', '35'])).
% 0.70/0.90  thf('37', plain,
% 0.70/0.90      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('38', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.90      inference('sup-', [status(thm)], ['36', '37'])).
% 0.70/0.90  thf('39', plain,
% 0.70/0.90      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('40', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.70/0.90  thf('41', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['1', '40'])).
% 0.70/0.90  thf('42', plain,
% 0.70/0.90      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 0.70/0.90         (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)) = (sk_A))),
% 0.70/0.90      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.70/0.90  thf('43', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.90  thf('44', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.90           = (k4_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.90  thf('45', plain,
% 0.70/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.70/0.90           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.70/0.90  thf('46', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.70/0.90           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['44', '45'])).
% 0.70/0.90  thf('47', plain,
% 0.70/0.90      (![X15 : $i, X16 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.70/0.90           = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.90  thf('48', plain,
% 0.70/0.90      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.70/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.90  thf('49', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.70/0.90      inference('sup+', [status(thm)], ['47', '48'])).
% 0.70/0.90  thf('50', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (r1_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 0.70/0.90      inference('sup+', [status(thm)], ['46', '49'])).
% 0.70/0.90  thf('51', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 0.70/0.90      inference('sup+', [status(thm)], ['43', '50'])).
% 0.70/0.90  thf('52', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.70/0.90      inference('sup+', [status(thm)], ['42', '51'])).
% 0.70/0.90  thf('53', plain, ($false), inference('demod', [status(thm)], ['41', '52'])).
% 0.70/0.90  
% 0.70/0.90  % SZS output end Refutation
% 0.70/0.90  
% 0.70/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
