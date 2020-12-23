%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p86E38qdNl

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:06 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  240 ( 240 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t57_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p86E38qdNl
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:45:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 50 iterations in 0.080s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.35/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.35/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.35/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.35/0.54  thf(t57_enumset1, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.35/0.54     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.35/0.54       ( k2_xboole_0 @
% 0.35/0.54         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.35/0.54        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.35/0.54          ( k2_xboole_0 @
% 0.35/0.54            ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t57_enumset1])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.35/0.54         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.35/0.54             (k3_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t51_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.54     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.35/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.35/0.54           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.35/0.54              (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.35/0.54  thf(t41_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( k2_tarski @ A @ B ) =
% 0.35/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i]:
% 0.35/0.54         ((k2_tarski @ X10 @ X11)
% 0.35/0.54           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.35/0.54  thf(t4_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.35/0.54       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.35/0.54           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.35/0.54           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.35/0.54              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.35/0.54           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.35/0.54           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.35/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['1', '4'])).
% 0.35/0.54  thf(t56_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.35/0.54     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.35/0.54       ( k2_xboole_0 @
% 0.35/0.54         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.54         ((k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.35/0.54           = (k2_xboole_0 @ (k1_tarski @ X18) @ 
% 0.35/0.54              (k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.35/0.54           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.35/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.35/0.54         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.35/0.54      inference('demod', [status(thm)], ['0', '7'])).
% 0.35/0.54  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.40/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
