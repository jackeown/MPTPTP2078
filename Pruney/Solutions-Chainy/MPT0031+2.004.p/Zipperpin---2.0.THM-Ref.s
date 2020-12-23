%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ErkI7zen4

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:52 EST 2020

% Result     : Theorem 5.09s
% Output     : Refutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  313 ( 404 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t24_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_C ) ) ),
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

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X3 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X3 ) @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','18','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ErkI7zen4
% 0.14/0.37  % Computer   : n018.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:58:42 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 5.09/5.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.09/5.34  % Solved by: fo/fo7.sh
% 5.09/5.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.09/5.34  % done 2955 iterations in 4.861s
% 5.09/5.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.09/5.34  % SZS output start Refutation
% 5.09/5.34  thf(sk_A_type, type, sk_A: $i).
% 5.09/5.34  thf(sk_C_type, type, sk_C: $i).
% 5.09/5.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.09/5.34  thf(sk_B_type, type, sk_B: $i).
% 5.09/5.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.09/5.34  thf(t24_xboole_1, conjecture,
% 5.09/5.34    (![A:$i,B:$i,C:$i]:
% 5.09/5.34     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 5.09/5.34       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 5.09/5.34  thf(zf_stmt_0, negated_conjecture,
% 5.09/5.34    (~( ![A:$i,B:$i,C:$i]:
% 5.09/5.34        ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 5.09/5.34          ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )),
% 5.09/5.34    inference('cnf.neg', [status(esa)], [t24_xboole_1])).
% 5.09/5.34  thf('0', plain,
% 5.09/5.34      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 5.09/5.34         != (k3_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 5.09/5.34             (k2_xboole_0 @ sk_A @ sk_C)))),
% 5.09/5.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.09/5.34  thf(commutativity_k3_xboole_0, axiom,
% 5.09/5.34    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.09/5.34  thf('1', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.09/5.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.09/5.34  thf('2', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.09/5.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.09/5.34  thf(t23_xboole_1, axiom,
% 5.09/5.34    (![A:$i,B:$i,C:$i]:
% 5.09/5.34     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 5.09/5.34       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 5.09/5.34  thf('3', plain,
% 5.09/5.34      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.09/5.34         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X7)))),
% 5.09/5.34      inference('cnf', [status(esa)], [t23_xboole_1])).
% 5.09/5.34  thf('4', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.09/5.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 5.09/5.34      inference('sup+', [status(thm)], ['2', '3'])).
% 5.09/5.34  thf('5', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.09/5.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 5.09/5.34      inference('sup+', [status(thm)], ['1', '4'])).
% 5.09/5.34  thf('6', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.09/5.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 5.09/5.34      inference('sup+', [status(thm)], ['2', '3'])).
% 5.09/5.34  thf('7', plain,
% 5.09/5.34      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.09/5.34         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X7)))),
% 5.09/5.34      inference('cnf', [status(esa)], [t23_xboole_1])).
% 5.09/5.34  thf(t4_xboole_1, axiom,
% 5.09/5.34    (![A:$i,B:$i,C:$i]:
% 5.09/5.34     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 5.09/5.34       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.09/5.34  thf('8', plain,
% 5.09/5.34      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.09/5.34         ((k2_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X10)
% 5.09/5.34           = (k2_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 5.09/5.34      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.09/5.34  thf('9', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.09/5.34         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 5.09/5.34              (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X3)))),
% 5.09/5.34      inference('sup+', [status(thm)], ['7', '8'])).
% 5.09/5.34  thf('10', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.09/5.34         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X3 @ X2)) @ 
% 5.09/5.34           (k3_xboole_0 @ X2 @ X0))
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X3) @ 
% 5.09/5.34              (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 5.09/5.34      inference('sup+', [status(thm)], ['6', '9'])).
% 5.09/5.34  thf('11', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.09/5.34         ((k2_xboole_0 @ 
% 5.09/5.34           (k3_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0)) @ 
% 5.09/5.34           (k3_xboole_0 @ X0 @ X2))
% 5.09/5.34           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 5.09/5.34      inference('sup+', [status(thm)], ['5', '10'])).
% 5.09/5.34  thf('12', plain,
% 5.09/5.34      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.09/5.34         ((k2_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X10)
% 5.09/5.34           = (k2_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 5.09/5.34      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.09/5.34  thf(idempotence_k3_xboole_0, axiom,
% 5.09/5.34    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 5.09/5.34  thf('13', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 5.09/5.34      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 5.09/5.34  thf('14', plain,
% 5.09/5.34      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.09/5.34         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 5.09/5.34           = (k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X7)))),
% 5.09/5.34      inference('cnf', [status(esa)], [t23_xboole_1])).
% 5.09/5.34  thf('15', plain,
% 5.09/5.34      (![X0 : $i, X1 : $i]:
% 5.09/5.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 5.09/5.34           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.09/5.35      inference('sup+', [status(thm)], ['13', '14'])).
% 5.09/5.35  thf(t22_xboole_1, axiom,
% 5.09/5.35    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 5.09/5.35  thf('16', plain,
% 5.09/5.35      (![X3 : $i, X4 : $i]:
% 5.09/5.35         ((k2_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)) = (X3))),
% 5.09/5.35      inference('cnf', [status(esa)], [t22_xboole_1])).
% 5.09/5.35  thf('17', plain,
% 5.09/5.35      (![X0 : $i, X1 : $i]:
% 5.09/5.35         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 5.09/5.35      inference('sup+', [status(thm)], ['15', '16'])).
% 5.09/5.35  thf('18', plain,
% 5.09/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.09/5.35         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))
% 5.09/5.35           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 5.09/5.35      inference('demod', [status(thm)], ['11', '12', '17'])).
% 5.09/5.35  thf('19', plain,
% 5.09/5.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.09/5.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.09/5.35  thf('20', plain,
% 5.09/5.35      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 5.09/5.35         != (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 5.09/5.35      inference('demod', [status(thm)], ['0', '18', '19'])).
% 5.09/5.35  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 5.09/5.35  
% 5.09/5.35  % SZS output end Refutation
% 5.09/5.35  
% 5.09/5.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
