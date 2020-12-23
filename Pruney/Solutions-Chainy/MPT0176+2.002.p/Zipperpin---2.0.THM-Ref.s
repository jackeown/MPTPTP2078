%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fr6Z0XUyqa

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  170 ( 170 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t92_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t92_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k5_enumset1 @ X14 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf('2',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fr6Z0XUyqa
% 0.11/0.33  % Computer   : n017.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:03:17 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.33  % Number of cores: 8
% 0.17/0.33  % Python version: Python 3.6.8
% 0.17/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 7 iterations in 0.010s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.45  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(t92_enumset1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t92_enumset1])).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (((k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.19/0.45         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t80_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.45     ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E ) =
% 0.19/0.45       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.45         ((k5_enumset1 @ X14 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.19/0.45           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.19/0.45      inference('cnf', [status(esa)], [t80_enumset1])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (((k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.19/0.45         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf(t82_enumset1, axiom,
% 0.19/0.45    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X19 : $i]: ((k2_enumset1 @ X19 @ X19 @ X19 @ X19) = (k1_tarski @ X19))),
% 0.19/0.45      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.19/0.45  thf(t50_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.45     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.19/0.45       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.45         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.45           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.19/0.45              (k1_tarski @ X6)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.19/0.45           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.45      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.45  thf(t41_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k2_tarski @ A @ B ) =
% 0.19/0.45       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         ((k2_tarski @ X0 @ X1)
% 0.19/0.45           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.19/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf('8', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['2', '7'])).
% 0.19/0.45  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
