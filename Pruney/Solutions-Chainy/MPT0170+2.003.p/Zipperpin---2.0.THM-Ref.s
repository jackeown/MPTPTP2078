%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uDOzTLwKlk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :  158 ( 158 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t86_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E )
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) ),
    inference('cnf.neg',[status(esa)],[t86_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k6_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k5_enumset1 @ X5 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k4_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('4',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uDOzTLwKlk
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 3 iterations in 0.007s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.47  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.22/0.47                                           $i > $i).
% 0.22/0.47  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.47  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.47  thf(t86_enumset1, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.47     ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E ) =
% 0.22/0.47       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.47        ( ( k6_enumset1 @ A @ A @ A @ A @ B @ C @ D @ E ) =
% 0.22/0.47          ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t86_enumset1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.22/0.47         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t75_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.47     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.47       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.47         ((k6_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.22/0.47           = (k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.22/0.47      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.22/0.47  thf(t74_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.47     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.47       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.47         ((k5_enumset1 @ X5 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.22/0.47           = (k4_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 0.22/0.47      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.22/0.47  thf(t73_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.47     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.22/0.47       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.47         ((k4_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.22/0.47           = (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.22/0.47         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.22/0.47  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
