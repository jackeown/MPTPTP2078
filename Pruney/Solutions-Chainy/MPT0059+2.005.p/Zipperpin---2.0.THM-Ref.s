%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnysc9XIpr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:20 EST 2020

% Result     : Theorem 6.41s
% Output     : Refutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  225 ( 236 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t52_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
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

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnysc9XIpr
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:55:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.41/6.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.41/6.62  % Solved by: fo/fo7.sh
% 6.41/6.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.41/6.62  % done 2460 iterations in 6.163s
% 6.41/6.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.41/6.62  % SZS output start Refutation
% 6.41/6.62  thf(sk_C_type, type, sk_C: $i).
% 6.41/6.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.41/6.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.41/6.62  thf(sk_B_type, type, sk_B: $i).
% 6.41/6.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.41/6.62  thf(sk_A_type, type, sk_A: $i).
% 6.41/6.62  thf(t52_xboole_1, conjecture,
% 6.41/6.62    (![A:$i,B:$i,C:$i]:
% 6.41/6.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.41/6.62       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 6.41/6.62  thf(zf_stmt_0, negated_conjecture,
% 6.41/6.62    (~( ![A:$i,B:$i,C:$i]:
% 6.41/6.62        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.41/6.62          ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )),
% 6.41/6.62    inference('cnf.neg', [status(esa)], [t52_xboole_1])).
% 6.41/6.62  thf('0', plain,
% 6.41/6.62      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 6.41/6.62         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 6.41/6.62             (k3_xboole_0 @ sk_A @ sk_C)))),
% 6.41/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.41/6.62  thf(commutativity_k3_xboole_0, axiom,
% 6.41/6.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.41/6.62  thf('1', plain,
% 6.41/6.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.41/6.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.41/6.62  thf(t49_xboole_1, axiom,
% 6.41/6.62    (![A:$i,B:$i,C:$i]:
% 6.41/6.62     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.41/6.62       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 6.41/6.62  thf('2', plain,
% 6.41/6.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.41/6.62         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 6.41/6.62           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 6.41/6.62      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.41/6.62  thf('3', plain,
% 6.41/6.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.41/6.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 6.41/6.62           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 6.41/6.62      inference('sup+', [status(thm)], ['1', '2'])).
% 6.41/6.62  thf('4', plain,
% 6.41/6.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.41/6.62         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 6.41/6.62           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 6.41/6.62      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.41/6.62  thf('5', plain,
% 6.41/6.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.41/6.62         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 6.41/6.62           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.41/6.62      inference('sup+', [status(thm)], ['3', '4'])).
% 6.41/6.62  thf(t48_xboole_1, axiom,
% 6.41/6.62    (![A:$i,B:$i]:
% 6.41/6.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.41/6.62  thf('6', plain,
% 6.41/6.62      (![X7 : $i, X8 : $i]:
% 6.41/6.62         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 6.41/6.62           = (k3_xboole_0 @ X7 @ X8))),
% 6.41/6.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.41/6.62  thf(l36_xboole_1, axiom,
% 6.41/6.62    (![A:$i,B:$i,C:$i]:
% 6.41/6.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 6.41/6.62       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 6.41/6.62  thf('7', plain,
% 6.41/6.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.41/6.62         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 6.41/6.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X2 @ X4)))),
% 6.41/6.62      inference('cnf', [status(esa)], [l36_xboole_1])).
% 6.41/6.62  thf('8', plain,
% 6.41/6.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.41/6.62         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 6.41/6.62           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.41/6.62      inference('sup+', [status(thm)], ['6', '7'])).
% 6.41/6.62  thf('9', plain,
% 6.41/6.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.41/6.62         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 6.41/6.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 6.41/6.62      inference('sup+', [status(thm)], ['5', '8'])).
% 6.41/6.62  thf(t47_xboole_1, axiom,
% 6.41/6.62    (![A:$i,B:$i]:
% 6.41/6.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 6.41/6.62  thf('10', plain,
% 6.41/6.62      (![X5 : $i, X6 : $i]:
% 6.41/6.62         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 6.41/6.62           = (k4_xboole_0 @ X5 @ X6))),
% 6.41/6.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 6.41/6.62  thf('11', plain,
% 6.41/6.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.41/6.62         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 6.41/6.62           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 6.41/6.62      inference('demod', [status(thm)], ['9', '10'])).
% 6.41/6.62  thf('12', plain,
% 6.41/6.62      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 6.41/6.62         != (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 6.41/6.62      inference('demod', [status(thm)], ['0', '11'])).
% 6.41/6.62  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 6.41/6.62  
% 6.41/6.62  % SZS output end Refutation
% 6.41/6.62  
% 6.41/6.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
