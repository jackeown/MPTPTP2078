%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnmiTmxKNX

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:23 EST 2020

% Result     : Theorem 34.36s
% Output     : Refutation 34.36s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 107 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  406 ( 786 expanded)
%              Number of equality atoms :   47 (  99 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t101_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t101_xboole_1])).

thf('0',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','34'])).

thf('36',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnmiTmxKNX
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 34.36/34.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 34.36/34.62  % Solved by: fo/fo7.sh
% 34.36/34.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 34.36/34.62  % done 7787 iterations in 34.163s
% 34.36/34.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 34.36/34.62  % SZS output start Refutation
% 34.36/34.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 34.36/34.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 34.36/34.62  thf(sk_B_type, type, sk_B: $i).
% 34.36/34.62  thf(sk_A_type, type, sk_A: $i).
% 34.36/34.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 34.36/34.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 34.36/34.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 34.36/34.62  thf(t101_xboole_1, conjecture,
% 34.36/34.62    (![A:$i,B:$i]:
% 34.36/34.62     ( ( k5_xboole_0 @ A @ B ) =
% 34.36/34.62       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 34.36/34.62  thf(zf_stmt_0, negated_conjecture,
% 34.36/34.62    (~( ![A:$i,B:$i]:
% 34.36/34.62        ( ( k5_xboole_0 @ A @ B ) =
% 34.36/34.62          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 34.36/34.62    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 34.36/34.62  thf('0', plain,
% 34.36/34.62      (((k5_xboole_0 @ sk_A @ sk_B)
% 34.36/34.62         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 34.36/34.62             (k3_xboole_0 @ sk_A @ sk_B)))),
% 34.36/34.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.36/34.62  thf(commutativity_k3_xboole_0, axiom,
% 34.36/34.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 34.36/34.62  thf('1', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.36/34.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.36/34.62  thf(t100_xboole_1, axiom,
% 34.36/34.62    (![A:$i,B:$i]:
% 34.36/34.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 34.36/34.62  thf('2', plain,
% 34.36/34.62      (![X2 : $i, X3 : $i]:
% 34.36/34.62         ((k4_xboole_0 @ X2 @ X3)
% 34.36/34.62           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 34.36/34.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 34.36/34.62  thf(t91_xboole_1, axiom,
% 34.36/34.62    (![A:$i,B:$i,C:$i]:
% 34.36/34.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 34.36/34.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 34.36/34.62  thf('3', plain,
% 34.36/34.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 34.36/34.62           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 34.36/34.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 34.36/34.62  thf(t92_xboole_1, axiom,
% 34.36/34.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 34.36/34.62  thf('4', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 34.36/34.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 34.36/34.62  thf('5', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 34.36/34.62           = (k1_xboole_0))),
% 34.36/34.62      inference('sup+', [status(thm)], ['3', '4'])).
% 34.36/34.62  thf('6', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 34.36/34.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 34.36/34.62  thf('7', plain,
% 34.36/34.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 34.36/34.62           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 34.36/34.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 34.36/34.62  thf('8', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 34.36/34.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 34.36/34.62      inference('sup+', [status(thm)], ['6', '7'])).
% 34.36/34.62  thf('9', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 34.36/34.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 34.36/34.62  thf('10', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 34.36/34.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 34.36/34.62      inference('sup+', [status(thm)], ['6', '7'])).
% 34.36/34.62  thf('11', plain,
% 34.36/34.62      (![X0 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 34.36/34.62      inference('sup+', [status(thm)], ['9', '10'])).
% 34.36/34.62  thf(t5_boole, axiom,
% 34.36/34.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 34.36/34.62  thf('12', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 34.36/34.62      inference('cnf', [status(esa)], [t5_boole])).
% 34.36/34.62  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 34.36/34.62      inference('demod', [status(thm)], ['11', '12'])).
% 34.36/34.62  thf('14', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 34.36/34.62      inference('demod', [status(thm)], ['8', '13'])).
% 34.36/34.62  thf('15', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 34.36/34.62           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 34.36/34.62      inference('sup+', [status(thm)], ['5', '14'])).
% 34.36/34.62  thf('16', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 34.36/34.62      inference('cnf', [status(esa)], [t5_boole])).
% 34.36/34.62  thf('17', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 34.36/34.62      inference('demod', [status(thm)], ['15', '16'])).
% 34.36/34.62  thf('18', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 34.36/34.62           = (X1))),
% 34.36/34.62      inference('sup+', [status(thm)], ['2', '17'])).
% 34.36/34.62  thf('19', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 34.36/34.62      inference('demod', [status(thm)], ['15', '16'])).
% 34.36/34.62  thf('20', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 34.36/34.62      inference('demod', [status(thm)], ['8', '13'])).
% 34.36/34.62  thf('21', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 34.36/34.62      inference('sup+', [status(thm)], ['19', '20'])).
% 34.36/34.62  thf('22', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 34.36/34.62           = (X1))),
% 34.36/34.62      inference('demod', [status(thm)], ['18', '21'])).
% 34.36/34.62  thf(t98_xboole_1, axiom,
% 34.36/34.62    (![A:$i,B:$i]:
% 34.36/34.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 34.36/34.62  thf('23', plain,
% 34.36/34.62      (![X17 : $i, X18 : $i]:
% 34.36/34.62         ((k2_xboole_0 @ X17 @ X18)
% 34.36/34.62           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 34.36/34.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 34.36/34.62  thf('24', plain,
% 34.36/34.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 34.36/34.62           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 34.36/34.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 34.36/34.62  thf('25', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 34.36/34.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 34.36/34.62      inference('sup+', [status(thm)], ['23', '24'])).
% 34.36/34.62  thf('26', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 34.36/34.62           = (k5_xboole_0 @ X1 @ X0))),
% 34.36/34.62      inference('sup+', [status(thm)], ['22', '25'])).
% 34.36/34.62  thf(t21_xboole_1, axiom,
% 34.36/34.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 34.36/34.62  thf('27', plain,
% 34.36/34.62      (![X7 : $i, X8 : $i]:
% 34.36/34.62         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 34.36/34.62      inference('cnf', [status(esa)], [t21_xboole_1])).
% 34.36/34.62  thf(t16_xboole_1, axiom,
% 34.36/34.62    (![A:$i,B:$i,C:$i]:
% 34.36/34.62     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 34.36/34.62       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 34.36/34.62  thf('28', plain,
% 34.36/34.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 34.36/34.62         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 34.36/34.62           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 34.36/34.62      inference('cnf', [status(esa)], [t16_xboole_1])).
% 34.36/34.62  thf('29', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.36/34.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.36/34.62  thf('30', plain,
% 34.36/34.62      (![X2 : $i, X3 : $i]:
% 34.36/34.62         ((k4_xboole_0 @ X2 @ X3)
% 34.36/34.62           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 34.36/34.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 34.36/34.62  thf('31', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k4_xboole_0 @ X0 @ X1)
% 34.36/34.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 34.36/34.62      inference('sup+', [status(thm)], ['29', '30'])).
% 34.36/34.62  thf('32', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.36/34.62         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 34.36/34.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 34.36/34.62      inference('sup+', [status(thm)], ['28', '31'])).
% 34.36/34.62  thf('33', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.36/34.62         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 34.36/34.62           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 34.36/34.62      inference('sup+', [status(thm)], ['27', '32'])).
% 34.36/34.62  thf('34', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 34.36/34.62           = (k5_xboole_0 @ X1 @ X0))),
% 34.36/34.62      inference('demod', [status(thm)], ['26', '33'])).
% 34.36/34.62  thf('35', plain,
% 34.36/34.62      (![X0 : $i, X1 : $i]:
% 34.36/34.62         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 34.36/34.62           = (k5_xboole_0 @ X1 @ X0))),
% 34.36/34.62      inference('sup+', [status(thm)], ['1', '34'])).
% 34.36/34.62  thf('36', plain,
% 34.36/34.62      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 34.36/34.62      inference('demod', [status(thm)], ['0', '35'])).
% 34.36/34.62  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 34.36/34.62  
% 34.36/34.62  % SZS output end Refutation
% 34.36/34.62  
% 34.36/34.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
