%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MeULkTyJUl

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  151 ( 160 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t43_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MeULkTyJUl
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 5 iterations in 0.010s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(t43_enumset1, conjecture,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.43       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.43        ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.43          ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t43_enumset1])).
% 0.20/0.43  thf('0', plain,
% 0.20/0.43      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.43         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(t41_enumset1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( k2_tarski @ A @ B ) =
% 0.20/0.43       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X3 : $i, X4 : $i]:
% 0.20/0.43         ((k2_tarski @ X3 @ X4)
% 0.20/0.43           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X3 : $i, X4 : $i]:
% 0.20/0.43         ((k2_tarski @ X3 @ X4)
% 0.20/0.43           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.43  thf(t4_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.43       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.43           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.43           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.43              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.43      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.43           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.43      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.43  thf(t42_enumset1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.43       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.20/0.43           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.43           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.43      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.43         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.43      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.43  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
