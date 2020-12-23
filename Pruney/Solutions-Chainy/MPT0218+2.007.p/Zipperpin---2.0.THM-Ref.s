%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HigNjs39wt

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:01 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  126 ( 135 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t12_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_tarski @ X3 @ X2 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HigNjs39wt
% 0.17/0.39  % Computer   : n023.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 09:28:36 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.40  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 12 iterations in 0.012s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.25/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.51  thf(t12_zfmisc_1, conjecture,
% 0.25/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t12_zfmisc_1])).
% 0.25/0.51  thf('0', plain,
% 0.25/0.51      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(t77_enumset1, axiom,
% 0.25/0.51    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      (![X7 : $i, X8 : $i]:
% 0.25/0.51         ((k2_enumset1 @ X7 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.25/0.51      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.25/0.51  thf(t45_enumset1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.25/0.51       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.25/0.51         ((k2_enumset1 @ X3 @ X4 @ X5 @ X6)
% 0.25/0.51           = (k2_xboole_0 @ (k2_tarski @ X3 @ X4) @ (k2_tarski @ X5 @ X6)))),
% 0.25/0.51      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.25/0.51  thf(t7_xboole_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      (![X1 : $i, X2 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X2))),
% 0.25/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.51         (r1_tarski @ (k2_tarski @ X3 @ X2) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.25/0.51      inference('sup+', [status(thm)], ['1', '4'])).
% 0.25/0.51  thf(t82_enumset1, axiom,
% 0.25/0.51    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.51  thf('6', plain,
% 0.25/0.51      (![X9 : $i]: ((k2_enumset1 @ X9 @ X9 @ X9 @ X9) = (k1_tarski @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.25/0.51  thf('7', plain,
% 0.25/0.51      (![X7 : $i, X8 : $i]:
% 0.25/0.51         ((k2_enumset1 @ X7 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.25/0.51      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.25/0.51  thf('8', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.25/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.51  thf('9', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.25/0.51      inference('demod', [status(thm)], ['5', '8'])).
% 0.25/0.51  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
