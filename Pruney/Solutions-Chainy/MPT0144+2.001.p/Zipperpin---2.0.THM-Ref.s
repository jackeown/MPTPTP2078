%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lrLPnF24WX

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  350 ( 575 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t60_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k2_tarski @ sk_F @ sk_G ) ) ),
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
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_F @ sk_G ) @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k5_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k2_tarski @ X19 @ X20 ) @ ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('4',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_F @ sk_G @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X26 @ X27 @ X28 ) @ ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lrLPnF24WX
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:39:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 57 iterations in 0.061s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(t60_enumset1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52          ( k2_xboole_0 @
% 0.21/0.52            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t60_enumset1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.52         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52             (k2_tarski @ sk_F @ sk_G)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.52         != (k2_xboole_0 @ (k2_tarski @ sk_F @ sk_G) @ 
% 0.21/0.52             (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t57_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X19 @ X20) @ 
% 0.21/0.52              (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t57_enumset1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.52         != (k5_enumset1 @ sk_F @ sk_G @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(l68_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.21/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.21/0.52              (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.21/0.52           (k2_enumset1 @ X6 @ X5 @ X4 @ X3))
% 0.21/0.52           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t58_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.21/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X26 @ X27 @ X28) @ 
% 0.21/0.52              (k2_enumset1 @ X29 @ X30 @ X31 @ X32)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.21/0.52           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.52         != (k5_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.21/0.52           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.21/0.52           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.52           = (k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.52         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.52  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
