%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGFPZELiKy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:21 EST 2020

% Result     : Theorem 5.31s
% Output     : Refutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  261 ( 279 expanded)
%              Number of equality atoms :   28 (  30 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t53_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
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

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGFPZELiKy
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 5.31/5.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.31/5.50  % Solved by: fo/fo7.sh
% 5.31/5.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.31/5.50  % done 4628 iterations in 5.045s
% 5.31/5.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.31/5.50  % SZS output start Refutation
% 5.31/5.50  thf(sk_B_type, type, sk_B: $i).
% 5.31/5.50  thf(sk_C_type, type, sk_C: $i).
% 5.31/5.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.31/5.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.31/5.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.31/5.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.31/5.50  thf(sk_A_type, type, sk_A: $i).
% 5.31/5.50  thf(t53_xboole_1, conjecture,
% 5.31/5.50    (![A:$i,B:$i,C:$i]:
% 5.31/5.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 5.31/5.50       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 5.31/5.50  thf(zf_stmt_0, negated_conjecture,
% 5.31/5.50    (~( ![A:$i,B:$i,C:$i]:
% 5.31/5.50        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 5.31/5.50          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 5.31/5.50    inference('cnf.neg', [status(esa)], [t53_xboole_1])).
% 5.31/5.50  thf('0', plain,
% 5.31/5.50      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 5.31/5.50         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 5.31/5.50             (k4_xboole_0 @ sk_A @ sk_C)))),
% 5.31/5.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.31/5.50  thf(commutativity_k2_xboole_0, axiom,
% 5.31/5.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.31/5.50  thf('1', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.31/5.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.31/5.50  thf(t46_xboole_1, axiom,
% 5.31/5.50    (![A:$i,B:$i]:
% 5.31/5.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 5.31/5.50  thf('2', plain,
% 5.31/5.50      (![X16 : $i, X17 : $i]:
% 5.31/5.50         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 5.31/5.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 5.31/5.50  thf('3', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i]:
% 5.31/5.50         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 5.31/5.50      inference('sup+', [status(thm)], ['1', '2'])).
% 5.31/5.50  thf(t41_xboole_1, axiom,
% 5.31/5.50    (![A:$i,B:$i,C:$i]:
% 5.31/5.50     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 5.31/5.50       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.31/5.50  thf('4', plain,
% 5.31/5.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.31/5.50         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.31/5.50           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.31/5.50      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.31/5.50  thf(t39_xboole_1, axiom,
% 5.31/5.50    (![A:$i,B:$i]:
% 5.31/5.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 5.31/5.50  thf('5', plain,
% 5.31/5.50      (![X11 : $i, X12 : $i]:
% 5.31/5.50         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 5.31/5.50           = (k2_xboole_0 @ X11 @ X12))),
% 5.31/5.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 5.31/5.50  thf('6', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.31/5.50         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 5.31/5.50           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 5.31/5.50      inference('sup+', [status(thm)], ['4', '5'])).
% 5.31/5.50  thf('7', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i]:
% 5.31/5.50         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 5.31/5.50           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.31/5.50      inference('sup+', [status(thm)], ['3', '6'])).
% 5.31/5.50  thf(t1_boole, axiom,
% 5.31/5.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.31/5.50  thf('8', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 5.31/5.50      inference('cnf', [status(esa)], [t1_boole])).
% 5.31/5.50  thf('9', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i]:
% 5.31/5.50         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.31/5.50      inference('demod', [status(thm)], ['7', '8'])).
% 5.31/5.50  thf('10', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.31/5.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.31/5.50  thf(t21_xboole_1, axiom,
% 5.31/5.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 5.31/5.50  thf('11', plain,
% 5.31/5.50      (![X3 : $i, X4 : $i]:
% 5.31/5.50         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 5.31/5.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 5.31/5.50  thf('12', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i]:
% 5.31/5.50         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 5.31/5.50      inference('sup+', [status(thm)], ['10', '11'])).
% 5.31/5.50  thf('13', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i]:
% 5.31/5.50         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 5.31/5.50           = (k4_xboole_0 @ X0 @ X1))),
% 5.31/5.50      inference('sup+', [status(thm)], ['9', '12'])).
% 5.31/5.50  thf(t49_xboole_1, axiom,
% 5.31/5.50    (![A:$i,B:$i,C:$i]:
% 5.31/5.50     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 5.31/5.50       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 5.31/5.50  thf('14', plain,
% 5.31/5.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.31/5.50         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 5.31/5.50           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 5.31/5.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 5.31/5.50  thf('15', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.31/5.50         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 5.31/5.50           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 5.31/5.50      inference('sup+', [status(thm)], ['13', '14'])).
% 5.31/5.50  thf('16', plain,
% 5.31/5.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.31/5.50         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.31/5.50           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.31/5.50      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.31/5.50  thf('17', plain,
% 5.31/5.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.31/5.50         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 5.31/5.50           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 5.31/5.50      inference('demod', [status(thm)], ['15', '16'])).
% 5.31/5.50  thf('18', plain,
% 5.31/5.50      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 5.31/5.50         != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 5.31/5.50      inference('demod', [status(thm)], ['0', '17'])).
% 5.31/5.50  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 5.31/5.50  
% 5.31/5.50  % SZS output end Refutation
% 5.31/5.50  
% 5.31/5.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
