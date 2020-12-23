%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xQUzvGlQTB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  164 ( 175 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xQUzvGlQTB
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 22 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(t71_enumset1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.21/0.47         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t42_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X4 @ X5 @ X6)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k2_tarski @ X5 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.47  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.47  thf('2', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.47  thf(t4_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.47       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 0.21/0.47           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ X0 @ X1)
% 0.21/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X4 @ X5 @ X6)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k2_tarski @ X5 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.47  thf(t44_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k1_enumset1 @ X8 @ X9 @ X10)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.21/0.47         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '8'])).
% 0.21/0.47  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
