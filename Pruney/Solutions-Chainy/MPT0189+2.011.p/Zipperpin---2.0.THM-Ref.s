%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FAjEB4bJrj

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:08 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   27 (  33 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  210 ( 278 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

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
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X12 @ X15 @ X14 @ X13 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X11 @ X10 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X11 @ X10 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('12',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','9','10','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FAjEB4bJrj
% 0.13/0.36  % Computer   : n006.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 16:07:38 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 3.36/3.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.36/3.55  % Solved by: fo/fo7.sh
% 3.36/3.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.36/3.55  % done 1726 iterations in 3.081s
% 3.36/3.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.36/3.55  % SZS output start Refutation
% 3.36/3.55  thf(sk_D_type, type, sk_D: $i).
% 3.36/3.55  thf(sk_C_type, type, sk_C: $i).
% 3.36/3.55  thf(sk_B_type, type, sk_B: $i).
% 3.36/3.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.36/3.55  thf(sk_A_type, type, sk_A: $i).
% 3.36/3.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.36/3.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.36/3.55  thf(t108_enumset1, conjecture,
% 3.36/3.55    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.55     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 3.36/3.55  thf(zf_stmt_0, negated_conjecture,
% 3.36/3.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.55        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 3.36/3.55    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 3.36/3.55  thf('0', plain,
% 3.36/3.55      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.36/3.55         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 3.36/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.55  thf(l53_enumset1, axiom,
% 3.36/3.55    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.36/3.55       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.36/3.55  thf('1', plain,
% 3.36/3.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 3.36/3.55           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 3.36/3.55      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.36/3.55  thf(commutativity_k2_xboole_0, axiom,
% 3.36/3.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.36/3.55  thf('2', plain,
% 3.36/3.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.36/3.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.36/3.55  thf('3', plain,
% 3.36/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.36/3.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2))
% 3.36/3.55           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.36/3.55      inference('sup+', [status(thm)], ['1', '2'])).
% 3.36/3.55  thf('4', plain,
% 3.36/3.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 3.36/3.55           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 3.36/3.55      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.36/3.55  thf('5', plain,
% 3.36/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.36/3.55      inference('sup+', [status(thm)], ['3', '4'])).
% 3.36/3.55  thf(t107_enumset1, axiom,
% 3.36/3.55    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.55     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 3.36/3.55  thf('6', plain,
% 3.36/3.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X12 @ X15 @ X14 @ X13)
% 3.36/3.55           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 3.36/3.55      inference('cnf', [status(esa)], [t107_enumset1])).
% 3.36/3.55  thf(t103_enumset1, axiom,
% 3.36/3.55    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.55     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 3.36/3.55  thf('7', plain,
% 3.36/3.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X8 @ X9 @ X11 @ X10)
% 3.36/3.55           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 3.36/3.55      inference('cnf', [status(esa)], [t103_enumset1])).
% 3.36/3.55  thf('8', plain,
% 3.36/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.36/3.55      inference('sup+', [status(thm)], ['6', '7'])).
% 3.36/3.55  thf('9', plain,
% 3.36/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 3.36/3.55      inference('sup+', [status(thm)], ['5', '8'])).
% 3.36/3.55  thf('10', plain,
% 3.36/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.36/3.55      inference('sup+', [status(thm)], ['6', '7'])).
% 3.36/3.55  thf('11', plain,
% 3.36/3.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.36/3.55         ((k2_enumset1 @ X8 @ X9 @ X11 @ X10)
% 3.36/3.55           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 3.36/3.55      inference('cnf', [status(esa)], [t103_enumset1])).
% 3.36/3.55  thf('12', plain,
% 3.36/3.55      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.36/3.55         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 3.36/3.55      inference('demod', [status(thm)], ['0', '9', '10', '11'])).
% 3.36/3.55  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 3.36/3.55  
% 3.36/3.55  % SZS output end Refutation
% 3.36/3.55  
% 3.41/3.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
