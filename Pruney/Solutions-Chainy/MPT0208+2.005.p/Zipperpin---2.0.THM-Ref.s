%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t50k000lmd

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:29 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :  401 ( 795 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :   22 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(t134_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) @ ( k1_tarski @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_I ) @ ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t127_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k7_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k6_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t127_enumset1])).

thf('4',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_I @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t128_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k7_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t128_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X8 @ X7 ) )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t133_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k7_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ ( k2_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t133_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('13',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['4','9','10','11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t50k000lmd
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 202 iterations in 0.254s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(sk_F_type, type, sk_F: $i).
% 0.52/0.71  thf(sk_G_type, type, sk_G: $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.52/0.71  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.52/0.71                                           $i > $i > $i).
% 0.52/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.71  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.71  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.52/0.71                                           $i > $i).
% 0.52/0.71  thf(sk_H_type, type, sk_H: $i).
% 0.52/0.71  thf(sk_I_type, type, sk_I: $i).
% 0.52/0.71  thf(t134_enumset1, conjecture,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.52/0.71     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.52/0.71       ( k2_xboole_0 @
% 0.52/0.71         ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.52/0.71        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.52/0.71          ( k2_xboole_0 @
% 0.52/0.71            ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t134_enumset1])).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.52/0.71         sk_I)
% 0.52/0.71         != (k2_xboole_0 @ 
% 0.52/0.71             (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.52/0.71              sk_H) @ 
% 0.52/0.71             (k1_tarski @ sk_I)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(commutativity_k2_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.52/0.71         sk_I)
% 0.52/0.71         != (k2_xboole_0 @ (k1_tarski @ sk_I) @ 
% 0.52/0.71             (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.52/0.71              sk_H)))),
% 0.52/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.71  thf(t127_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.52/0.71     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.52/0.71       ( k2_xboole_0 @
% 0.52/0.71         ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 0.52/0.71         X11 : $i, X12 : $i]:
% 0.52/0.71         ((k7_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.52/0.71           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.52/0.71              (k6_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t127_enumset1])).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.52/0.71         sk_I)
% 0.52/0.71         != (k7_enumset1 @ sk_I @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ 
% 0.52/0.71             sk_G @ sk_H))),
% 0.52/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf(t128_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.52/0.71     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.52/0.71       ( k2_xboole_0 @
% 0.52/0.71         ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.52/0.71         X20 : $i, X21 : $i]:
% 0.52/0.71         ((k7_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.52/0.71           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ 
% 0.52/0.71              (k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t128_enumset1])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.52/0.71         X7 : $i, X8 : $i]:
% 0.52/0.71         ((k2_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.52/0.71           (k2_tarski @ X8 @ X7))
% 0.52/0.71           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['5', '6'])).
% 0.52/0.71  thf(t133_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.52/0.71     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.52/0.71       ( k2_xboole_0 @
% 0.52/0.71         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ))).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, 
% 0.52/0.71         X29 : $i, X30 : $i]:
% 0.52/0.71         ((k7_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.52/0.71           = (k2_xboole_0 @ 
% 0.52/0.71              (k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28) @ 
% 0.52/0.71              (k2_tarski @ X29 @ X30)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t133_enumset1])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.52/0.71         X7 : $i, X8 : $i]:
% 0.52/0.71         ((k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7)
% 0.52/0.71           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.52/0.71         X7 : $i, X8 : $i]:
% 0.52/0.71         ((k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7)
% 0.52/0.71           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.52/0.71         X7 : $i, X8 : $i]:
% 0.52/0.71         ((k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7)
% 0.52/0.71           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.52/0.71         X7 : $i, X8 : $i]:
% 0.52/0.71         ((k7_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7)
% 0.52/0.71           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.52/0.71         sk_I)
% 0.52/0.71         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.52/0.71             sk_H @ sk_I))),
% 0.52/0.71      inference('demod', [status(thm)], ['4', '9', '10', '11', '12'])).
% 0.52/0.71  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
