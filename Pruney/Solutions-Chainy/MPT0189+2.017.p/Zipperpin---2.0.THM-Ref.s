%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T6UagyYn7W

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:08 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :  212 ( 234 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X5 @ X4 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X5 @ X4 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X5 @ X4 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('11',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','5','6','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T6UagyYn7W
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:22:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 930 iterations in 0.455s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.71/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.71/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.71/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.90  thf(t108_enumset1, conjecture,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.71/0.90         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t44_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.71/0.90       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.71/0.90           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.71/0.90  thf(commutativity_k2_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.71/0.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['1', '2'])).
% 0.71/0.90  thf(t46_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.71/0.90       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X14 @ X15 @ X16 @ X17)
% 0.71/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X14 @ X15 @ X16) @ (k1_tarski @ X17)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['3', '4'])).
% 0.71/0.90  thf(t103_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X2 @ X3 @ X5 @ X4) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 0.71/0.90      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.71/0.90  thf(t107_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X6 @ X9 @ X8 @ X7) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.71/0.90      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X2 @ X3 @ X5 @ X4) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 0.71/0.90      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['7', '8'])).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X2 @ X3 @ X5 @ X4) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 0.71/0.90      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.71/0.90         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.71/0.90      inference('demod', [status(thm)], ['0', '5', '6', '9', '10'])).
% 0.71/0.90  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
