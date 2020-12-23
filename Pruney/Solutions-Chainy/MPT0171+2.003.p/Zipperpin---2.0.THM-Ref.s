%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.byr6UJOXqb

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  131 ( 131 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t87_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_enumset1 @ A @ A @ A @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t87_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.byr6UJOXqb
% 0.16/0.38  % Computer   : n006.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 11:29:23 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.45  % Solved by: fo/fo7.sh
% 0.23/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.45  % done 15 iterations in 0.007s
% 0.23/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.45  % SZS output start Refutation
% 0.23/0.45  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.23/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.45  thf(t87_enumset1, conjecture,
% 0.23/0.45    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.45    (~( ![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.23/0.45    inference('cnf.neg', [status(esa)], [t87_enumset1])).
% 0.23/0.45  thf('0', plain,
% 0.23/0.45      (((k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_tarski @ sk_A))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(t82_enumset1, axiom,
% 0.23/0.45    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.45  thf('1', plain,
% 0.23/0.45      (![X15 : $i]: ((k2_enumset1 @ X15 @ X15 @ X15 @ X15) = (k1_tarski @ X15))),
% 0.23/0.45      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.23/0.45  thf(t50_enumset1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.45     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.23/0.45       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.23/0.45  thf('2', plain,
% 0.23/0.45      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.45         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.23/0.45           = (k2_xboole_0 @ (k2_enumset1 @ X9 @ X10 @ X11 @ X12) @ 
% 0.23/0.45              (k1_tarski @ X13)))),
% 0.23/0.45      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.23/0.45  thf('3', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.23/0.45           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.23/0.45      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.45  thf(t41_enumset1, axiom,
% 0.23/0.45    (![A:$i,B:$i]:
% 0.23/0.45     ( ( k2_tarski @ A @ B ) =
% 0.23/0.45       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.23/0.45  thf('4', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         ((k2_tarski @ X0 @ X1)
% 0.23/0.45           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.23/0.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.23/0.45  thf('5', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i]:
% 0.23/0.45         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.23/0.45      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.45  thf(t69_enumset1, axiom,
% 0.23/0.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.45  thf('6', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.23/0.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.45  thf('7', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.23/0.45      inference('demod', [status(thm)], ['0', '5', '6'])).
% 0.23/0.45  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.23/0.45  
% 0.23/0.45  % SZS output end Refutation
% 0.23/0.45  
% 0.23/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
