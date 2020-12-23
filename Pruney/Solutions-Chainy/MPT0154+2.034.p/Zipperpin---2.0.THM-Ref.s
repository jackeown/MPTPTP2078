%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EaZqsB0GzF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  122 ( 122 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EaZqsB0GzF
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 27 iterations in 0.019s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.50  thf(t70_enumset1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t41_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k2_tarski @ A @ B ) =
% 0.19/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         ((k2_tarski @ X4 @ X5)
% 0.19/0.50           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.19/0.50  thf(t7_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf(t12_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.19/0.50           = (k2_tarski @ X1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf(t42_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.19/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X6 @ X7 @ X8)
% 0.19/0.50           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k2_tarski @ X7 @ X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf('8', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.19/0.50  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
