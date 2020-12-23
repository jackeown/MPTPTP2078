%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.owyym1LArY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:01 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  197 ( 197 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t99_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ B @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t99_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X6 @ X7 ) @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X19 @ X21 @ X20 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('11',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.owyym1LArY
% 0.15/0.38  % Computer   : n001.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:17:30 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 187 iterations in 0.092s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(t99_enumset1, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.58        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t99_enumset1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.39/0.58         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t70_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.58  thf(t46_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.39/0.58       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.58         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.39/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X6 @ X7) @ (k1_tarski @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.39/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1))
% 0.39/0.58           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.39/0.58           = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 0.39/0.58      inference('sup+', [status(thm)], ['1', '4'])).
% 0.39/0.58  thf(t42_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.39/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.39/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X4)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 0.39/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.58  thf(t71_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.58         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.39/0.58           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.39/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf(t98_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X19 @ X21 @ X20) = (k1_enumset1 @ X19 @ X20 @ X21))),
% 0.39/0.58      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.39/0.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['0', '9', '10'])).
% 0.39/0.58  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
