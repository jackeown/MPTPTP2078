%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JvaHJq4gFk

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:02 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  334 ( 452 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JvaHJq4gFk
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 251 iterations in 0.236s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.69  thf(t95_xboole_1, conjecture,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k3_xboole_0 @ A @ B ) =
% 0.50/0.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.50/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.69    (~( ![A:$i,B:$i]:
% 0.50/0.69        ( ( k3_xboole_0 @ A @ B ) =
% 0.50/0.69          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 0.50/0.69  thf('0', plain,
% 0.50/0.69      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.50/0.69         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.50/0.69             (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(commutativity_k5_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.50/0.69  thf('1', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.50/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.69  thf('2', plain,
% 0.50/0.69      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.50/0.69         != (k5_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.50/0.69             (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.50/0.69  thf(t91_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.50/0.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.50/0.69           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.69  thf('4', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.50/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.69  thf('5', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.50/0.69           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.69      inference('sup+', [status(thm)], ['3', '4'])).
% 0.50/0.69  thf('6', plain,
% 0.50/0.69      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.50/0.69         != (k5_xboole_0 @ sk_A @ 
% 0.50/0.69             (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.50/0.69      inference('demod', [status(thm)], ['2', '5'])).
% 0.50/0.69  thf(t94_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k2_xboole_0 @ A @ B ) =
% 0.50/0.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (![X10 : $i, X11 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ X10 @ X11)
% 0.50/0.69           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.50/0.69              (k3_xboole_0 @ X10 @ X11)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.50/0.69  thf('8', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.50/0.69           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.69  thf('9', plain,
% 0.50/0.69      (![X10 : $i, X11 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ X10 @ X11)
% 0.50/0.69           = (k5_xboole_0 @ X10 @ 
% 0.50/0.69              (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X10 @ X11))))),
% 0.50/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.50/0.69  thf('10', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.50/0.69           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.69  thf(t92_xboole_1, axiom,
% 0.50/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.50/0.69  thf('11', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.50/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.50/0.69           = (k1_xboole_0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['10', '11'])).
% 0.50/0.69  thf('13', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.50/0.69           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.69  thf('14', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.69           = (k5_xboole_0 @ X2 @ 
% 0.50/0.69              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ X1)) @ X0)))),
% 0.50/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.50/0.69  thf('15', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.50/0.69           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.69  thf('16', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.50/0.69           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.69  thf('17', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.69           = (k5_xboole_0 @ X2 @ 
% 0.50/0.69              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 0.50/0.69      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.50/0.69  thf(idempotence_k3_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.50/0.69  thf('18', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.50/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.50/0.69  thf('19', plain,
% 0.50/0.69      (![X10 : $i, X11 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ X10 @ X11)
% 0.50/0.69           = (k5_xboole_0 @ X10 @ 
% 0.50/0.69              (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X10 @ X11))))),
% 0.50/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.50/0.69  thf('20', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ X0 @ X0)
% 0.50/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.50/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.50/0.69  thf(idempotence_k2_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.50/0.69  thf('21', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.50/0.69      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.50/0.69  thf('22', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.50/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.69  thf('23', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.69      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.50/0.69  thf('24', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.50/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.69  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.50/0.69  thf('26', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((X0)
% 0.50/0.69           = (k5_xboole_0 @ X2 @ 
% 0.50/0.69              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 0.50/0.69      inference('demod', [status(thm)], ['17', '25'])).
% 0.50/0.69  thf('27', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         ((k3_xboole_0 @ X1 @ X0)
% 0.50/0.69           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.50/0.69      inference('sup+', [status(thm)], ['9', '26'])).
% 0.50/0.69  thf('28', plain,
% 0.50/0.69      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.69      inference('demod', [status(thm)], ['6', '27'])).
% 0.50/0.69  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
