%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YKmmMsKIIv

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:47 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  135 ( 135 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t88_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t88_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k3_enumset1 @ X8 @ X8 @ X8 @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 )
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
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YKmmMsKIIv
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 15:23:36 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.26/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.26/0.50  % Solved by: fo/fo7.sh
% 0.26/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.26/0.50  % done 4 iterations in 0.009s
% 0.26/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.26/0.50  % SZS output start Refutation
% 0.26/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.26/0.50  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.26/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.26/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.26/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.26/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.26/0.50  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.26/0.50  thf(t88_enumset1, conjecture,
% 0.26/0.50    (![A:$i,B:$i]:
% 0.26/0.50     ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.26/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.26/0.50    (~( ![A:$i,B:$i]:
% 0.26/0.50        ( ( k4_enumset1 @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.26/0.50    inference('cnf.neg', [status(esa)], [t88_enumset1])).
% 0.26/0.50  thf('0', plain,
% 0.26/0.50      (((k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.26/0.50         != (k2_tarski @ sk_A @ sk_B))),
% 0.26/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.50  thf(t87_enumset1, axiom,
% 0.26/0.50    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.26/0.50  thf('1', plain,
% 0.26/0.50      (![X8 : $i]: ((k3_enumset1 @ X8 @ X8 @ X8 @ X8 @ X8) = (k1_tarski @ X8))),
% 0.26/0.50      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.26/0.50  thf(t55_enumset1, axiom,
% 0.26/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.26/0.50     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.26/0.50       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.26/0.50  thf('2', plain,
% 0.26/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.26/0.50         ((k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.26/0.50           = (k2_xboole_0 @ (k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6) @ 
% 0.26/0.50              (k1_tarski @ X7)))),
% 0.26/0.50      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.26/0.50  thf('3', plain,
% 0.26/0.50      (![X0 : $i, X1 : $i]:
% 0.26/0.50         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.26/0.50           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.26/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.26/0.50  thf(t41_enumset1, axiom,
% 0.26/0.50    (![A:$i,B:$i]:
% 0.26/0.50     ( ( k2_tarski @ A @ B ) =
% 0.26/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.26/0.50  thf('4', plain,
% 0.26/0.50      (![X0 : $i, X1 : $i]:
% 0.26/0.50         ((k2_tarski @ X0 @ X1)
% 0.26/0.50           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.26/0.50      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.26/0.50  thf('5', plain,
% 0.26/0.50      (![X0 : $i, X1 : $i]:
% 0.26/0.50         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.26/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.26/0.50  thf('6', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.26/0.50      inference('demod', [status(thm)], ['0', '5'])).
% 0.26/0.50  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.26/0.50  
% 0.26/0.50  % SZS output end Refutation
% 0.26/0.50  
% 0.26/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
