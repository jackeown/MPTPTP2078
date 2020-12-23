%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C8r0rWS0zB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  180 ( 180 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t45_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C8r0rWS0zB
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 9 iterations in 0.021s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(t45_enumset1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.48       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.48          ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t45_enumset1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48             (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t42_enumset1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         ((k1_enumset1 @ X7 @ X8 @ X9)
% 0.21/0.48           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.48  thf(t41_enumset1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_tarski @ A @ B ) =
% 0.21/0.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((k2_tarski @ X5 @ X6)
% 0.21/0.48           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.48  thf(t4_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.48       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.48           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.48           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.48              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.48           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.48  thf(t44_enumset1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.48           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.48           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.48  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
