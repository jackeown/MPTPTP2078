%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1v9wBcr5tU

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:05 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   53 (  95 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  421 ( 793 expanded)
%              Number of equality atoms :   46 (  88 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1v9wBcr5tU
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 221 iterations in 0.213s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(t98_xboole_1, conjecture,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i,B:$i]:
% 0.45/0.70        ( ( k2_xboole_0 @ A @ B ) =
% 0.45/0.70          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.45/0.70  thf('0', plain,
% 0.45/0.70      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.45/0.70         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.70  thf('1', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.45/0.70         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.70  thf(t48_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      (![X6 : $i, X7 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.70           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.70  thf(t39_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.45/0.70           = (k2_xboole_0 @ X4 @ X5))),
% 0.45/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.70  thf('5', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.70  thf('6', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.70           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.45/0.70  thf(t51_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.45/0.70       ( A ) ))).
% 0.45/0.70  thf('9', plain,
% 0.45/0.70      (![X8 : $i, X9 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X8 @ X9))
% 0.45/0.70           = (X8))),
% 0.45/0.70      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.45/0.70  thf('10', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.45/0.70           = (k2_xboole_0 @ X4 @ X5))),
% 0.45/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.70  thf('12', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.45/0.70      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.70  thf(d6_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k5_xboole_0 @ A @ B ) =
% 0.45/0.70       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (![X2 : $i, X3 : $i]:
% 0.45/0.70         ((k5_xboole_0 @ X2 @ X3)
% 0.45/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.70      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.70  thf('15', plain,
% 0.45/0.70      (![X8 : $i, X9 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X8 @ X9))
% 0.45/0.70           = (X8))),
% 0.45/0.70      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.45/0.70  thf('16', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 0.45/0.70           = (X0))),
% 0.45/0.70      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.45/0.70           = (X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.70      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.70  thf(t52_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.70       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.45/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 0.45/0.70              (k3_xboole_0 @ X10 @ X12)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.45/0.70           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      (![X6 : $i, X7 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.70           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.70  thf('23', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k3_xboole_0 @ X0 @ X1)
% 0.45/0.70           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.70  thf('24', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '23'])).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.45/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 0.45/0.70              (k3_xboole_0 @ X10 @ X12)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.45/0.70  thf('26', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.45/0.70      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.70  thf('29', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      (![X2 : $i, X3 : $i]:
% 0.45/0.70         ((k5_xboole_0 @ X2 @ X3)
% 0.45/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.45/0.70  thf('31', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.70           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.45/0.70           = (k2_xboole_0 @ X4 @ X5))),
% 0.45/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.70  thf('33', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.70           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.45/0.70           = (k2_xboole_0 @ X4 @ X5))),
% 0.45/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.70  thf('35', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.70           = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['33', '34'])).
% 0.45/0.70  thf('36', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.70  thf('37', plain,
% 0.45/0.70      (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.70      inference('demod', [status(thm)], ['2', '35', '36'])).
% 0.45/0.70  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
