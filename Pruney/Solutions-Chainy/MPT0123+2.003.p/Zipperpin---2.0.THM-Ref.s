%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYH0s3Lhx2

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:53 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   35 (  64 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  345 ( 666 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t116_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ) ),
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

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYH0s3Lhx2
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 88 iterations in 0.185s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(t116_xboole_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.45/0.63       ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.63        ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.45/0.63          ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t116_xboole_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.45/0.63         != (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.45/0.63             (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t16_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.63       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.45/0.63           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.45/0.63         != (k3_xboole_0 @ sk_A @ 
% 0.45/0.63             (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C))))),
% 0.45/0.63      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.63  thf(t48_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.63           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf(t52_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 0.45/0.63              (k3_xboole_0 @ X11 @ X13)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.63           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf(t41_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.63       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.45/0.63           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf(t49_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.63       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.45/0.63           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 0.45/0.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.45/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))
% 0.45/0.63           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['4', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.63           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))
% 0.45/0.63           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))
% 0.45/0.63           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X2 @ 
% 0.45/0.63           (k4_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 0.45/0.63           = (k3_xboole_0 @ X2 @ 
% 0.45/0.63              (k4_xboole_0 @ X3 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))
% 0.45/0.63           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ (k4_xboole_0 @ X1 @ X0)))
% 0.45/0.63           = (k3_xboole_0 @ X2 @ 
% 0.45/0.63              (k4_xboole_0 @ X3 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X0)))
% 0.45/0.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['3', '16'])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.63           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 0.45/0.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.45/0.63         != (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.45/0.63      inference('demod', [status(thm)], ['2', '19'])).
% 0.45/0.63  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
