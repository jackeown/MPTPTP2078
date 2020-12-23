%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AEYVTAN9WX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  354 ( 384 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t67_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k2_tarski @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t113_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X5 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k6_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AEYVTAN9WX
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 21 iterations in 0.090s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.55  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.55                                           $i > $i).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.55  thf(t67_enumset1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.55     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.55       ( k2_xboole_0 @
% 0.21/0.55         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.55        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.55          ( k2_xboole_0 @
% 0.21/0.55            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t67_enumset1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.55         != (k2_xboole_0 @ 
% 0.21/0.55             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.21/0.55             (k2_tarski @ sk_G @ sk_H)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t54_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.55     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         ((k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.55           = (k2_xboole_0 @ (k2_enumset1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.21/0.55              (k2_tarski @ X14 @ X15)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.21/0.55  thf(l53_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.55  thf(t113_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) =
% 0.21/0.55       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.21/0.55           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t113_xboole_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ 
% 0.21/0.55           (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5) @ X4)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.21/0.55              (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X5) @ X4)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ 
% 0.21/0.55           (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X3 @ X2) @ 
% 0.21/0.55            (k2_tarski @ X1 @ X0)) @ 
% 0.21/0.55           X4)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.21/0.55              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         ((k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.55           = (k2_xboole_0 @ (k2_enumset1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.21/0.55              (k2_tarski @ X14 @ X15)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.21/0.55              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.55           (k2_tarski @ X1 @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.55              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '8'])).
% 0.21/0.55  thf(t63_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.55     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.55       ( k2_xboole_0 @
% 0.21/0.55         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.55         X23 : $i]:
% 0.21/0.55         ((k6_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ 
% 0.21/0.55              (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.55           (k2_tarski @ X1 @ X0))
% 0.21/0.55           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.55         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.21/0.55             sk_H))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '11'])).
% 0.21/0.55  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
