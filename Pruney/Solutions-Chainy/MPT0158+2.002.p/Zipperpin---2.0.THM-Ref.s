%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pizo2Aih9h

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  248 ( 265 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t74_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ),
    inference('cnf.neg',[status(esa)],[t74_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pizo2Aih9h
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 144 iterations in 0.090s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(t74_enumset1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.55     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.55       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.55        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.55          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t74_enumset1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (((k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.20/0.55         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t51_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.55     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.55              (k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.20/0.55  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.55  thf('2', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.55  thf(t4_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.55       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 0.20/0.55           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X3)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ X0 @ X1)
% 0.20/0.55           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.20/0.55           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.20/0.55              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.55           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.55              (k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.55           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.20/0.55              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf(t56_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.55     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.55       ( k2_xboole_0 @
% 0.20/0.55         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         ((k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.55           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 0.20/0.55              (k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.55           = (k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.20/0.55         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '9'])).
% 0.20/0.55  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
