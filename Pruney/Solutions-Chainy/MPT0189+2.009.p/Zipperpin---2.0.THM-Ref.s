%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WP16TkD0tH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:07 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  199 ( 223 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X17 @ X15 @ X16 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X17 @ X15 @ X16 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X13 @ X12 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','7','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WP16TkD0tH
% 0.16/0.36  % Computer   : n020.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 20:07:52 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 753 iterations in 0.382s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(t108_enumset1, conjecture,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.68/0.86  thf('0', plain,
% 0.68/0.86      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.86         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(l53_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.68/0.86       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.68/0.86  thf('1', plain,
% 0.68/0.86      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.68/0.86           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.68/0.86      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.68/0.86  thf(commutativity_k2_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.86      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2))
% 0.68/0.86           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.68/0.86           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.68/0.86      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.68/0.86  thf('5', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['3', '4'])).
% 0.68/0.86  thf(t105_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X14 @ X17 @ X15 @ X16)
% 0.68/0.86           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 0.68/0.86      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X14 @ X17 @ X15 @ X16)
% 0.68/0.86           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 0.68/0.86      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.68/0.86  thf(t103_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.68/0.86  thf('9', plain,
% 0.68/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X10 @ X11 @ X13 @ X12)
% 0.68/0.86           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.68/0.86      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['8', '9'])).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.86         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.68/0.86      inference('demod', [status(thm)], ['0', '7', '10'])).
% 0.68/0.86  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
