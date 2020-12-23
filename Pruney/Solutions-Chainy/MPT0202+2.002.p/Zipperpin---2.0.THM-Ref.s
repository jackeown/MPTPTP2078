%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PrGv6jpPtU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :  280 ( 280 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t128_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X8 @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t127_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k7_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t127_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PrGv6jpPtU
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 27 iterations in 0.044s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_I_type, type, sk_I: $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.50                                           $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.50                                           $i > $i).
% 0.21/0.50  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(t128_enumset1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.50     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.21/0.50       ( k2_xboole_0 @
% 0.21/0.50         ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.50        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.21/0.50          ( k2_xboole_0 @
% 0.21/0.50            ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t128_enumset1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.21/0.50         sk_I)
% 0.21/0.50         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50             (k5_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t62_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.50     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.50       ( k2_xboole_0 @
% 0.21/0.50         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.21/0.50         X21 : $i]:
% 0.21/0.50         ((k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.21/0.50           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 0.21/0.50              (k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.21/0.50  thf(t41_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k2_tarski @ A @ B ) =
% 0.21/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         ((k2_tarski @ X12 @ X13)
% 0.21/0.50           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.50  thf(t4_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.50       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.50           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.50           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.50              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.21/0.50         X7 : $i, X8 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k2_tarski @ X8 @ X7) @ 
% 0.21/0.50           (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50           = (k2_xboole_0 @ (k1_tarski @ X8) @ 
% 0.21/0.50              (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf(t127_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.50     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.21/0.50       ( k2_xboole_0 @
% 0.21/0.50         ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, 
% 0.21/0.50         X10 : $i, X11 : $i]:
% 0.21/0.50         ((k7_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.50           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.21/0.50              (k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t127_enumset1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.21/0.50         X7 : $i, X8 : $i]:
% 0.21/0.50         ((k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.50           = (k2_xboole_0 @ (k2_tarski @ X8 @ X7) @ 
% 0.21/0.50              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.21/0.50         sk_I)
% 0.21/0.50         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.21/0.50             sk_H @ sk_I))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
