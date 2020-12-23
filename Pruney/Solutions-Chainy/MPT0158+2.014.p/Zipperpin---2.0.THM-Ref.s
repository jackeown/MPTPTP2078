%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XweU18qimY

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  225 ( 242 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XweU18qimY
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 49 iterations in 0.032s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.50  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.50  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.50  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.50  thf(t74_enumset1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.50     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.50       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.50        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.50          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t74_enumset1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (((k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.22/0.50         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t51_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.50     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.22/0.50           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.50              (k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.22/0.50  thf(t6_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.22/0.50           = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.50           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.22/0.50           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.50              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.22/0.50           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.22/0.50              (k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.50           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.22/0.50           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(t56_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.50     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.50       ( k2_xboole_0 @
% 0.22/0.50         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.22/0.50           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 0.22/0.50              (k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         ((k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.50           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.22/0.50         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.50  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
