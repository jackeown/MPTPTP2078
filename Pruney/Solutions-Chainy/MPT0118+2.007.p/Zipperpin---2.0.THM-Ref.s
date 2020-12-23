%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bUNNd7sgJI

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:50 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  220 ( 332 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t111_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t111_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
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

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('15',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bUNNd7sgJI
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.65/2.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.65/2.90  % Solved by: fo/fo7.sh
% 2.65/2.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.65/2.90  % done 1378 iterations in 2.446s
% 2.65/2.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.65/2.90  % SZS output start Refutation
% 2.65/2.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.65/2.90  thf(sk_C_type, type, sk_C: $i).
% 2.65/2.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.65/2.90  thf(sk_B_type, type, sk_B: $i).
% 2.65/2.90  thf(sk_A_type, type, sk_A: $i).
% 2.65/2.90  thf(t111_xboole_1, conjecture,
% 2.65/2.90    (![A:$i,B:$i,C:$i]:
% 2.65/2.90     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 2.65/2.90       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 2.65/2.90  thf(zf_stmt_0, negated_conjecture,
% 2.65/2.90    (~( ![A:$i,B:$i,C:$i]:
% 2.65/2.90        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 2.65/2.90          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 2.65/2.90    inference('cnf.neg', [status(esa)], [t111_xboole_1])).
% 2.65/2.90  thf('0', plain,
% 2.65/2.90      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 2.65/2.90         (k3_xboole_0 @ sk_C @ sk_B))
% 2.65/2.90         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 2.65/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.90  thf(commutativity_k3_xboole_0, axiom,
% 2.65/2.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.65/2.90  thf('1', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.90  thf('2', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.90  thf('3', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.90  thf('4', plain,
% 2.65/2.90      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 2.65/2.90         (k3_xboole_0 @ sk_B @ sk_C))
% 2.65/2.90         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 2.65/2.90      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 2.65/2.90  thf(t49_xboole_1, axiom,
% 2.65/2.90    (![A:$i,B:$i,C:$i]:
% 2.65/2.90     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.65/2.90       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 2.65/2.90  thf('5', plain,
% 2.65/2.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.65/2.90         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 2.65/2.90           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 2.65/2.90      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.65/2.90  thf('6', plain,
% 2.65/2.90      (((k3_xboole_0 @ sk_B @ 
% 2.65/2.90         (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 2.65/2.90         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 2.65/2.90      inference('demod', [status(thm)], ['4', '5'])).
% 2.65/2.90  thf(t47_xboole_1, axiom,
% 2.65/2.90    (![A:$i,B:$i]:
% 2.65/2.90     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.65/2.90  thf('7', plain,
% 2.65/2.90      (![X2 : $i, X3 : $i]:
% 2.65/2.90         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3))
% 2.65/2.90           = (k4_xboole_0 @ X2 @ X3))),
% 2.65/2.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.65/2.90  thf('8', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.90  thf('9', plain,
% 2.65/2.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.65/2.90         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 2.65/2.90           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 2.65/2.90      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.65/2.90  thf('10', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 2.65/2.90           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.65/2.90      inference('sup+', [status(thm)], ['8', '9'])).
% 2.65/2.90  thf('11', plain,
% 2.65/2.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.65/2.90         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 2.65/2.90           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 2.65/2.90      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.65/2.90  thf('12', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.90         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 2.65/2.90           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.65/2.90      inference('sup+', [status(thm)], ['10', '11'])).
% 2.65/2.90  thf('13', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.90         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 2.65/2.90           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.65/2.90      inference('sup+', [status(thm)], ['7', '12'])).
% 2.65/2.90  thf('14', plain,
% 2.65/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.90         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 2.65/2.90           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.65/2.90      inference('sup+', [status(thm)], ['10', '11'])).
% 2.65/2.90  thf('15', plain,
% 2.65/2.90      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 2.65/2.90         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 2.65/2.90      inference('demod', [status(thm)], ['6', '13', '14'])).
% 2.65/2.90  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 2.65/2.90  
% 2.65/2.90  % SZS output end Refutation
% 2.65/2.90  
% 2.65/2.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
