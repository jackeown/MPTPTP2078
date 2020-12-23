%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kfjzMjtrTr

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  212 ( 232 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

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

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','5','6','7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kfjzMjtrTr
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 38 iterations in 0.022s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.48                                           $i > $i).
% 0.20/0.48  thf(t93_enumset1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C ) =
% 0.20/0.48       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ B @ C ) =
% 0.20/0.48          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t93_enumset1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.20/0.48         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t76_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X21 : $i]: ((k1_enumset1 @ X21 @ X21 @ X21) = (k1_tarski @ X21))),
% 0.20/0.48      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.20/0.48  thf(t71_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.20/0.48           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.48  thf(l75_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.48     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.48       ( k2_xboole_0 @
% 0.20/0.48         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.20/0.48           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.20/0.48              (k2_enumset1 @ X6 @ X7 @ X8 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.20/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.20/0.48              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         ((k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.20/0.48              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.20/0.48           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.48  thf(t44_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.20/0.48           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.48         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '5', '6', '7', '8'])).
% 0.20/0.48  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
