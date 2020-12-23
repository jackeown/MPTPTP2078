%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2ECejXGEOX

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:52 EST 2020

% Result     : Theorem 11.62s
% Output     : Refutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 350 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','14','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2ECejXGEOX
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 11.62/11.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.62/11.86  % Solved by: fo/fo7.sh
% 11.62/11.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.62/11.86  % done 4492 iterations in 11.395s
% 11.62/11.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.62/11.86  % SZS output start Refutation
% 11.62/11.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.62/11.86  thf(sk_A_type, type, sk_A: $i).
% 11.62/11.86  thf(sk_C_type, type, sk_C: $i).
% 11.62/11.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.62/11.86  thf(sk_B_type, type, sk_B: $i).
% 11.62/11.86  thf(t24_xboole_1, conjecture,
% 11.62/11.86    (![A:$i,B:$i,C:$i]:
% 11.62/11.86     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 11.62/11.86       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 11.62/11.86  thf(zf_stmt_0, negated_conjecture,
% 11.62/11.86    (~( ![A:$i,B:$i,C:$i]:
% 11.62/11.86        ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 11.62/11.86          ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )),
% 11.62/11.86    inference('cnf.neg', [status(esa)], [t24_xboole_1])).
% 11.62/11.86  thf('0', plain,
% 11.62/11.86      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 11.62/11.86         != (k3_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 11.62/11.86             (k2_xboole_0 @ sk_A @ sk_C)))),
% 11.62/11.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.62/11.86  thf(commutativity_k3_xboole_0, axiom,
% 11.62/11.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 11.62/11.86  thf('1', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.62/11.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.62/11.86  thf('2', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.62/11.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.62/11.86  thf(t23_xboole_1, axiom,
% 11.62/11.86    (![A:$i,B:$i,C:$i]:
% 11.62/11.86     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 11.62/11.86       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 11.62/11.86  thf('3', plain,
% 11.62/11.86      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.62/11.86         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 11.62/11.86           = (k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X8)))),
% 11.62/11.86      inference('cnf', [status(esa)], [t23_xboole_1])).
% 11.62/11.86  thf('4', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.62/11.86         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 11.62/11.86           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 11.62/11.86      inference('sup+', [status(thm)], ['2', '3'])).
% 11.62/11.86  thf('5', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.62/11.86         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 11.62/11.86           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 11.62/11.86      inference('sup+', [status(thm)], ['1', '4'])).
% 11.62/11.86  thf('6', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.62/11.86         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 11.62/11.86           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 11.62/11.86      inference('sup+', [status(thm)], ['2', '3'])).
% 11.62/11.86  thf('7', plain,
% 11.62/11.86      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.62/11.86         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 11.62/11.86           = (k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X8)))),
% 11.62/11.86      inference('cnf', [status(esa)], [t23_xboole_1])).
% 11.62/11.86  thf(t4_xboole_1, axiom,
% 11.62/11.86    (![A:$i,B:$i,C:$i]:
% 11.62/11.86     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 11.62/11.86       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 11.62/11.86  thf('8', plain,
% 11.62/11.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 11.62/11.86         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 11.62/11.86           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 11.62/11.86      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.62/11.86  thf('9', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.62/11.86         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 11.62/11.86           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 11.62/11.86              (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X3)))),
% 11.62/11.86      inference('sup+', [status(thm)], ['7', '8'])).
% 11.62/11.86  thf('10', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.62/11.86         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X3 @ X2)) @ 
% 11.62/11.86           (k3_xboole_0 @ X2 @ X0))
% 11.62/11.86           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X3) @ 
% 11.62/11.86              (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 11.62/11.86      inference('sup+', [status(thm)], ['6', '9'])).
% 11.62/11.86  thf('11', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.62/11.86         ((k2_xboole_0 @ 
% 11.62/11.86           (k3_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0)) @ 
% 11.62/11.86           (k3_xboole_0 @ X0 @ X2))
% 11.62/11.86           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 11.62/11.86      inference('sup+', [status(thm)], ['5', '10'])).
% 11.62/11.86  thf('12', plain,
% 11.62/11.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 11.62/11.86         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 11.62/11.86           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 11.62/11.86      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.62/11.86  thf(t21_xboole_1, axiom,
% 11.62/11.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 11.62/11.86  thf('13', plain,
% 11.62/11.86      (![X2 : $i, X3 : $i]:
% 11.62/11.86         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 11.62/11.86      inference('cnf', [status(esa)], [t21_xboole_1])).
% 11.62/11.86  thf('14', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.62/11.86         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))
% 11.62/11.86           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 11.62/11.86      inference('demod', [status(thm)], ['11', '12', '13'])).
% 11.62/11.86  thf('15', plain,
% 11.62/11.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.62/11.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.62/11.86  thf('16', plain,
% 11.62/11.86      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 11.62/11.86         != (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 11.62/11.86      inference('demod', [status(thm)], ['0', '14', '15'])).
% 11.62/11.86  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 11.62/11.86  
% 11.62/11.86  % SZS output end Refutation
% 11.62/11.86  
% 11.69/11.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
