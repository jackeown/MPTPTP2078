%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3a5pOeLSfK

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:34 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  224 ( 239 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t73_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) ),
    inference('cnf.neg',[status(esa)],[t73_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3a5pOeLSfK
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 181 iterations in 0.137s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(t73_enumset1, conjecture,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.58     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.40/0.58       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.58        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.40/0.58          ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t73_enumset1])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (((k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.40/0.58         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t47_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.58     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.40/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.58         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.40/0.58              (k2_enumset1 @ X5 @ X6 @ X7 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.40/0.58  thf(idempotence_k2_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.58  thf('2', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.40/0.58  thf(t4_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.58       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 0.40/0.58           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X3)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ X0 @ X1)
% 0.40/0.58           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k1_tarski @ X4) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.40/0.58              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['1', '4'])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.58         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.40/0.58              (k2_enumset1 @ X5 @ X6 @ X7 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.40/0.58              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf(t51_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.58     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.40/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.58         ((k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X9) @ 
% 0.40/0.58              (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.58           = (k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.40/0.58         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.40/0.58      inference('demod', [status(thm)], ['0', '9'])).
% 0.40/0.58  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
