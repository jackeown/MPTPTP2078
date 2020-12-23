%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wZnevkQ93R

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  204 ( 204 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t50_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_enumset1 @ A @ B @ C @ D @ E )
        = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_tarski @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t49_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X14 @ X15 @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t49_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wZnevkQ93R
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:57:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 15 iterations in 0.018s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.48  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(t50_enumset1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.48     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.22/0.48       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.48        ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.22/0.48          ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t50_enumset1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.22/0.48         != (k2_xboole_0 @ (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.22/0.48             (k1_tarski @ sk_E)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t41_enumset1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k2_tarski @ A @ B ) =
% 0.22/0.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         ((k2_tarski @ X5 @ X6)
% 0.22/0.48           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.22/0.48  thf(t46_enumset1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.48       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.48         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.22/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.22/0.48  thf(t4_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.48       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.22/0.48           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.22/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.22/0.48              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.22/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.22/0.48              (k2_tarski @ X1 @ X0)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.48  thf(t49_enumset1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.48     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.22/0.48       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.48         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.22/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X14 @ X15 @ X16) @ 
% 0.22/0.48              (k2_tarski @ X17 @ X18)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t49_enumset1])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.22/0.48           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.22/0.48         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.48  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
