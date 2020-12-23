%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9SHWvTgIed

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  277 ( 390 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t93_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t93_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X20 @ X20 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t65_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) @ ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t65_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('12',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','9','10','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9SHWvTgIed
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 19:24:50 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 8 iterations in 0.011s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.23/0.49  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.23/0.49                                           $i > $i).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.49  thf(t93_enumset1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C ) =
% 0.23/0.49       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.49        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C ) =
% 0.23/0.49          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t93_enumset1])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.23/0.49         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t84_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X20 @ X20 @ X20 @ X20 @ X21 @ X22)
% 0.23/0.49           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.23/0.49      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.23/0.49  thf(t79_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.23/0.49       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.23/0.49           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.23/0.49      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.50         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.23/0.50           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.23/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.50         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.23/0.50           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.23/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf(t65_enumset1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.23/0.50     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.23/0.50       ( k2_xboole_0 @
% 0.23/0.50         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.23/0.50         X15 : $i]:
% 0.23/0.50         ((k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.23/0.50           = (k2_xboole_0 @ (k2_enumset1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.23/0.50              (k2_enumset1 @ X12 @ X13 @ X14 @ X15)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t65_enumset1])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.50         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.23/0.50           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.23/0.50              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.50         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.23/0.50           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.23/0.50              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['3', '6'])).
% 0.23/0.50  thf(l62_enumset1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.50     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.23/0.50       ( k2_xboole_0 @
% 0.23/0.50         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.50         ((k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.23/0.50           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.23/0.50              (k1_enumset1 @ X5 @ X6 @ X7)))),
% 0.23/0.50      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.50         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.23/0.50           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.50         ((k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.23/0.50           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.23/0.50      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.50         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.23/0.50           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.23/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.23/0.50         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '9', '10', '11'])).
% 0.23/0.50  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
