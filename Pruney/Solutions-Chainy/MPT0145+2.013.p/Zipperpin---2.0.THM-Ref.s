%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1njY7iQbyO

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  264 ( 264 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t61_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tarski @ sk_G ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1njY7iQbyO
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:43:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 8 iterations in 0.012s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.47  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.47  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.47  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(t61_enumset1, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.47     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.47       ( k2_xboole_0 @
% 0.22/0.47         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.47        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.47          ( k2_xboole_0 @
% 0.22/0.47            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t61_enumset1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.22/0.47         != (k2_xboole_0 @ 
% 0.22/0.47             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.22/0.47             (k1_tarski @ sk_G)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t55_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.47     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.47       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.47         ((k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.22/0.47           = (k2_xboole_0 @ (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18) @ 
% 0.22/0.47              (k1_tarski @ X19)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.22/0.47  thf(t51_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.47     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.47         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.22/0.47           = (k2_xboole_0 @ (k1_tarski @ X8) @ 
% 0.22/0.47              (k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.22/0.47  thf(t4_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.47       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.22/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.22/0.47           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.22/0.47              (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)))),
% 0.22/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.47           (k1_tarski @ X0))
% 0.22/0.47           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.22/0.47              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.22/0.47      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.47  thf(t56_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.47     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.47       ( k2_xboole_0 @
% 0.22/0.47         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.47         ((k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.22/0.47           = (k2_xboole_0 @ (k1_tarski @ X20) @ 
% 0.22/0.47              (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.47           (k1_tarski @ X0)) = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.22/0.47         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.47  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
