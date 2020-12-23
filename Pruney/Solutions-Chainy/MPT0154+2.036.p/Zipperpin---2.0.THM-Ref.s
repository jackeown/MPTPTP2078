%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fMIB0t09A3

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :  129 ( 138 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    8 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fMIB0t09A3
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 5 iterations in 0.010s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.46  thf(t70_enumset1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t41_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_tarski @ A @ B ) =
% 0.20/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         ((k2_tarski @ X4 @ X5)
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.46  thf(t6_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.20/0.46           = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         ((k2_tarski @ X4 @ X5)
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.20/0.46           = (k2_tarski @ X1 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf(t42_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.46         ((k1_enumset1 @ X6 @ X7 @ X8)
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k2_tarski @ X7 @ X8)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.46  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
