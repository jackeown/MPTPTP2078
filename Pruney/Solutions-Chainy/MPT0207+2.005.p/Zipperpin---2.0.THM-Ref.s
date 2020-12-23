%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bXjU6M4Ylm

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :  310 ( 310 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t133_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t133_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) @ ( k2_tarski @ sk_H @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) @ ( k2_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X7 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t127_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k7_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t127_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bXjU6M4Ylm
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:52:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 26 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.49                                           $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.49                                           $i > $i).
% 0.20/0.49  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.49  thf(sk_I_type, type, sk_I: $i).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.49  thf(t133_enumset1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.49     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.20/0.49       ( k2_xboole_0 @
% 0.20/0.49         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.49        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.20/0.49          ( k2_xboole_0 @
% 0.20/0.49            ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k2_tarski @ H @ I ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t133_enumset1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.20/0.49         sk_I)
% 0.20/0.49         != (k2_xboole_0 @ 
% 0.20/0.49             (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G) @ 
% 0.20/0.49             (k2_tarski @ sk_H @ sk_I)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t67_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.49     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.49       ( k2_xboole_0 @
% 0.20/0.49         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.20/0.49         X35 : $i]:
% 0.20/0.49         ((k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.20/0.49           = (k2_xboole_0 @ 
% 0.20/0.49              (k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33) @ 
% 0.20/0.49              (k2_tarski @ X34 @ X35)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.20/0.49  thf(t56_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.49     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.49       ( k2_xboole_0 @
% 0.20/0.49         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.49         ((k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X21) @ 
% 0.20/0.49              (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.20/0.49  thf(t4_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.49       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.49           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X7)
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.20/0.49              (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X7)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.20/0.49         X7 : $i, X8 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ (k5_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.49           (k2_tarski @ X1 @ X0))
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X8) @ 
% 0.20/0.49              (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.49  thf(t127_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.20/0.49     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.20/0.49       ( k2_xboole_0 @
% 0.20/0.49         ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 0.20/0.49         X19 : $i, X20 : $i]:
% 0.20/0.49         ((k7_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.20/0.49              (k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t127_enumset1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.20/0.49         X7 : $i, X8 : $i]:
% 0.20/0.49         ((k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.49           = (k2_xboole_0 @ (k5_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.49              (k2_tarski @ X1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.20/0.49         sk_I)
% 0.20/0.49         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.20/0.49             sk_H @ sk_I))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.49  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
