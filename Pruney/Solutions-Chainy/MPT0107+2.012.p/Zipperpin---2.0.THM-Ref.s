%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IJYWFo1ruO

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:11 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  389 ( 524 expanded)
%              Number of equality atoms :   46 (  63 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7','20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IJYWFo1ruO
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.73  % Solved by: fo/fo7.sh
% 0.47/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.73  % done 482 iterations in 0.277s
% 0.47/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.73  % SZS output start Refutation
% 0.47/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.73  thf(t100_xboole_1, conjecture,
% 0.47/0.73    (![A:$i,B:$i]:
% 0.47/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.73    (~( ![A:$i,B:$i]:
% 0.47/0.73        ( ( k4_xboole_0 @ A @ B ) =
% 0.47/0.73          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.47/0.73    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.47/0.73  thf('0', plain,
% 0.47/0.73      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.47/0.73         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.47/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.73  thf(t48_xboole_1, axiom,
% 0.47/0.73    (![A:$i,B:$i]:
% 0.47/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.73  thf('1', plain,
% 0.47/0.73      (![X12 : $i, X13 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.73           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.73  thf('2', plain,
% 0.47/0.73      (![X12 : $i, X13 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.73           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.73  thf(d6_xboole_0, axiom,
% 0.47/0.73    (![A:$i,B:$i]:
% 0.47/0.73     ( ( k5_xboole_0 @ A @ B ) =
% 0.47/0.73       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.73  thf('3', plain,
% 0.47/0.73      (![X2 : $i, X3 : $i]:
% 0.47/0.73         ((k5_xboole_0 @ X2 @ X3)
% 0.47/0.73           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.47/0.73      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.47/0.73  thf(commutativity_k2_xboole_0, axiom,
% 0.47/0.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.47/0.73  thf('4', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.73  thf('5', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.47/0.73           = (k5_xboole_0 @ X1 @ X0))),
% 0.47/0.73      inference('sup+', [status(thm)], ['3', '4'])).
% 0.47/0.73  thf('6', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.47/0.73           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 0.47/0.73           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.47/0.73      inference('sup+', [status(thm)], ['2', '5'])).
% 0.47/0.73  thf(t41_xboole_1, axiom,
% 0.47/0.73    (![A:$i,B:$i,C:$i]:
% 0.47/0.73     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.73       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.47/0.73  thf('7', plain,
% 0.47/0.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.47/0.73           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.47/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.73  thf('8', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.73  thf('9', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.73  thf(t1_boole, axiom,
% 0.47/0.73    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.73  thf('10', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.47/0.73      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.73  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.73  thf(t40_xboole_1, axiom,
% 0.47/0.73    (![A:$i,B:$i]:
% 0.47/0.73     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.47/0.73  thf('12', plain,
% 0.47/0.73      (![X5 : $i, X6 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X6)
% 0.47/0.73           = (k4_xboole_0 @ X5 @ X6))),
% 0.47/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.47/0.73  thf('13', plain,
% 0.47/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.47/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.73  thf(t4_boole, axiom,
% 0.47/0.73    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.73  thf('14', plain,
% 0.47/0.73      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.47/0.73      inference('cnf', [status(esa)], [t4_boole])).
% 0.47/0.73  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.73  thf('16', plain,
% 0.47/0.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.47/0.73           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.47/0.73      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.73  thf('17', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.73           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.73  thf('18', plain,
% 0.47/0.73      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.47/0.73      inference('cnf', [status(esa)], [t4_boole])).
% 0.47/0.73  thf('19', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.73  thf('20', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('sup+', [status(thm)], ['8', '19'])).
% 0.47/0.73  thf('21', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.73  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.73  thf('23', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k3_xboole_0 @ X1 @ X0)
% 0.47/0.73           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.47/0.73      inference('demod', [status(thm)], ['6', '7', '20', '21', '22'])).
% 0.47/0.73  thf('24', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.47/0.73           = (k5_xboole_0 @ X1 @ X0))),
% 0.47/0.73      inference('sup+', [status(thm)], ['3', '4'])).
% 0.47/0.73  thf('25', plain,
% 0.47/0.73      (![X2 : $i, X3 : $i]:
% 0.47/0.73         ((k5_xboole_0 @ X2 @ X3)
% 0.47/0.73           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.47/0.73      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.47/0.73  thf('26', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.47/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.73  thf('27', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k3_xboole_0 @ X1 @ X0)
% 0.47/0.73           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('demod', [status(thm)], ['23', '26'])).
% 0.47/0.73  thf('28', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.47/0.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('sup+', [status(thm)], ['1', '27'])).
% 0.47/0.73  thf('29', plain,
% 0.47/0.73      (![X12 : $i, X13 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.73           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.73  thf('30', plain,
% 0.47/0.73      (![X12 : $i, X13 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.47/0.73           = (k3_xboole_0 @ X12 @ X13))),
% 0.47/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.73  thf('31', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.73           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('sup+', [status(thm)], ['29', '30'])).
% 0.47/0.73  thf(t47_xboole_1, axiom,
% 0.47/0.73    (![A:$i,B:$i]:
% 0.47/0.73     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.47/0.73  thf('32', plain,
% 0.47/0.73      (![X10 : $i, X11 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.47/0.73           = (k4_xboole_0 @ X10 @ X11))),
% 0.47/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.47/0.73  thf('33', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X1 @ X0)
% 0.47/0.73           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.73  thf('34', plain,
% 0.47/0.73      (![X0 : $i, X1 : $i]:
% 0.47/0.73         ((k4_xboole_0 @ X1 @ X0)
% 0.47/0.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.47/0.73      inference('sup+', [status(thm)], ['28', '33'])).
% 0.47/0.73  thf('35', plain,
% 0.47/0.73      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.73      inference('demod', [status(thm)], ['0', '34'])).
% 0.47/0.73  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.47/0.73  
% 0.47/0.73  % SZS output end Refutation
% 0.47/0.73  
% 0.57/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
