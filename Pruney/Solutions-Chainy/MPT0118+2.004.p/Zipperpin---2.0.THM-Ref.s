%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v191XN8NuU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:50 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v191XN8NuU
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 48 iterations in 0.124s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(t111_xboole_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.42/0.60       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.42/0.60          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t111_xboole_1])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.42/0.60         (k3_xboole_0 @ sk_C @ sk_B))
% 0.42/0.60         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.42/0.60         (k3_xboole_0 @ sk_B @ sk_C))
% 0.42/0.60         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.42/0.60  thf(t49_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.42/0.60       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.42/0.60           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (((k3_xboole_0 @ sk_B @ 
% 0.42/0.60         (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.42/0.60         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf(t47_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i]:
% 0.42/0.60         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5))
% 0.42/0.60           = (k4_xboole_0 @ X4 @ X5))),
% 0.42/0.60      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.42/0.60           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.42/0.60           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.42/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.42/0.60           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 0.42/0.60           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.42/0.60           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['7', '12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 0.42/0.60           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.42/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.42/0.60         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('demod', [status(thm)], ['6', '13', '14'])).
% 0.42/0.60  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
