%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXBloiKVZl

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:02 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  368 ( 533 expanded)
%              Number of equality atoms :   47 (  70 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ o_0_0_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ o_0_0_xboole_0 )
      = X2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ X4 ) )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ X4 ) )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ o_0_0_xboole_0 )
      = X2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','34'])).

thf('36',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXBloiKVZl
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 148 iterations in 0.150s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(t95_xboole_1, conjecture,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k3_xboole_0 @ A @ B ) =
% 0.36/0.62       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i,B:$i]:
% 0.36/0.62        ( ( k3_xboole_0 @ A @ B ) =
% 0.36/0.62          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 0.36/0.62  thf('0', plain,
% 0.36/0.62      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.36/0.62         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.36/0.62             (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(t91_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.62  thf('1', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.62           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.36/0.62         != (k5_xboole_0 @ sk_A @ 
% 0.36/0.62             (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.62  thf(t94_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ A @ B ) =
% 0.36/0.62       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      (![X9 : $i, X10 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X9 @ X10)
% 0.36/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.62           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.62  thf('5', plain,
% 0.36/0.62      (![X9 : $i, X10 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X9 @ X10)
% 0.36/0.62           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X9 @ X10))))),
% 0.36/0.62      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.62  thf('6', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.62           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.62  thf(t92_xboole_1, axiom,
% 0.36/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.62  thf('7', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.62  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.36/0.62  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.36/0.62  thf('9', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (o_0_0_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf('10', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.62           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ X2 @ 
% 0.36/0.62              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['6', '11'])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.62           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ X2 @ 
% 0.36/0.62              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 0.36/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      (![X9 : $i, X10 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X9 @ X10)
% 0.36/0.62           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X9 @ X10))))),
% 0.36/0.62      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X0 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ o_0_0_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf(idempotence_k2_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.62  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.36/0.62  thf(t3_boole, axiom,
% 0.36/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.62  thf('19', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.62  thf('20', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.36/0.62  thf('21', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ o_0_0_xboole_0) = (X2))),
% 0.36/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.62  thf(t48_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (![X3 : $i, X4 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X3 @ (k4_xboole_0 @ X3 @ X4))
% 0.36/0.62           = (k3_xboole_0 @ X3 @ X4))),
% 0.36/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.62  thf(t2_boole, axiom,
% 0.36/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.62  thf('25', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.36/0.62  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.36/0.62  thf('27', plain,
% 0.36/0.62      (![X1 : $i]: ((k3_xboole_0 @ X1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.36/0.62  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['23', '27'])).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      (![X3 : $i, X4 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X3 @ (k4_xboole_0 @ X3 @ X4))
% 0.36/0.62           = (k3_xboole_0 @ X3 @ X4))),
% 0.36/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.62  thf('30', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X0 @ o_0_0_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.62  thf('31', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ o_0_0_xboole_0) = (X2))),
% 0.36/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.62  thf('32', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.62  thf('33', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ o_0_0_xboole_0 @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['17', '18', '32'])).
% 0.36/0.62  thf('34', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         ((X0)
% 0.36/0.62           = (k5_xboole_0 @ X2 @ 
% 0.36/0.62              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 0.36/0.62      inference('demod', [status(thm)], ['14', '33'])).
% 0.36/0.62  thf('35', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k3_xboole_0 @ X1 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['5', '34'])).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['2', '35'])).
% 0.36/0.62  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
