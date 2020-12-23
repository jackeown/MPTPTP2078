%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x2I4HnwMTk

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  263 ( 325 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t48_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_enumset1 @ A @ B @ C @ D @ E )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_enumset1 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
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

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x2I4HnwMTk
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 23 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t48_enumset1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47        ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47          ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t48_enumset1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (((k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.47         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.47             (k1_enumset1 @ sk_C_1 @ sk_D @ sk_E)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t42_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k2_tarski @ X16 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.47  thf(t41_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k2_tarski @ A @ B ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         ((k2_tarski @ X13 @ X14)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.47  thf(t4_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.47       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k2_tarski @ X16 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.20/0.47              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['5', '8'])).
% 0.20/0.47  thf(l57_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 0.20/0.47              (k2_tarski @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.47           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.20/0.47              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.47         != (k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '12'])).
% 0.20/0.47  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
