%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nkGxpnrB3N

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:31 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 100 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  450 ( 876 expanded)
%              Number of equality atoms :   46 (  91 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('2',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('9',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['9','18','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nkGxpnrB3N
% 0.17/0.36  % Computer   : n024.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 20:33:51 EST 2020
% 0.17/0.36  % CPUTime    : 
% 0.17/0.36  % Running portfolio for 600 s
% 0.17/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.36  % Number of cores: 8
% 0.17/0.36  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.62/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.86  % Solved by: fo/fo7.sh
% 0.62/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.86  % done 676 iterations in 0.387s
% 0.62/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.86  % SZS output start Refutation
% 0.62/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.62/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.86  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.62/0.86  thf(t137_enumset1, conjecture,
% 0.62/0.86    (![A:$i,B:$i,C:$i]:
% 0.62/0.86     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.62/0.86       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.62/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.86    (~( ![A:$i,B:$i,C:$i]:
% 0.62/0.86        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.62/0.86          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.62/0.86    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.62/0.86  thf('0', plain,
% 0.62/0.86      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.62/0.86         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.62/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.86  thf(l53_enumset1, axiom,
% 0.62/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.62/0.86       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.62/0.86  thf('1', plain,
% 0.62/0.86      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.62/0.86         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 0.62/0.86           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.62/0.86      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.62/0.86  thf('2', plain,
% 0.62/0.86      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.62/0.86         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.62/0.86      inference('demod', [status(thm)], ['0', '1'])).
% 0.62/0.86  thf(t42_enumset1, axiom,
% 0.62/0.86    (![A:$i,B:$i,C:$i]:
% 0.62/0.86     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.62/0.86       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.62/0.86  thf('3', plain,
% 0.62/0.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k2_tarski @ X9 @ X10)))),
% 0.62/0.86      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.62/0.86  thf(commutativity_k2_xboole_0, axiom,
% 0.62/0.86    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.62/0.86  thf('4', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.86      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.86  thf('5', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.62/0.86           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['3', '4'])).
% 0.62/0.86  thf(t43_enumset1, axiom,
% 0.62/0.86    (![A:$i,B:$i,C:$i]:
% 0.62/0.86     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.62/0.86       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.62/0.86  thf('6', plain,
% 0.62/0.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X11 @ X12 @ X13)
% 0.62/0.86           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 0.62/0.86      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.62/0.86  thf('7', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.62/0.86  thf('8', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.62/0.86  thf('9', plain,
% 0.62/0.86      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.62/0.86         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.62/0.86      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.62/0.86  thf('10', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.62/0.86  thf(t70_enumset1, axiom,
% 0.62/0.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.62/0.86  thf('11', plain,
% 0.62/0.86      (![X19 : $i, X20 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.62/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.62/0.86  thf('12', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.62/0.86      inference('sup+', [status(thm)], ['10', '11'])).
% 0.62/0.86  thf('13', plain,
% 0.62/0.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X11 @ X12 @ X13)
% 0.62/0.86           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 0.62/0.86      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.62/0.86  thf('14', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X0 @ X1 @ X2)
% 0.62/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.62/0.86      inference('sup+', [status(thm)], ['12', '13'])).
% 0.62/0.86  thf(t44_enumset1, axiom,
% 0.62/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.62/0.86       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.62/0.86  thf('15', plain,
% 0.62/0.86      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.62/0.86         ((k2_enumset1 @ X14 @ X15 @ X16 @ X17)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_enumset1 @ X15 @ X16 @ X17)))),
% 0.62/0.86      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.62/0.86  thf('16', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.86      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.86  thf('17', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.62/0.86         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.62/0.86           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.86  thf('18', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X0 @ X1 @ X0))),
% 0.62/0.86      inference('demod', [status(thm)], ['14', '17'])).
% 0.62/0.86  thf('19', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.62/0.86  thf('20', plain,
% 0.62/0.86      (![X19 : $i, X20 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.62/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.62/0.86  thf('21', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.62/0.86      inference('sup+', [status(thm)], ['19', '20'])).
% 0.62/0.86  thf(t69_enumset1, axiom,
% 0.62/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.62/0.86  thf('22', plain,
% 0.62/0.86      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.62/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.86  thf('23', plain,
% 0.62/0.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k2_tarski @ X9 @ X10)))),
% 0.62/0.86      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.62/0.86  thf('24', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.62/0.86      inference('sup+', [status(thm)], ['22', '23'])).
% 0.62/0.86  thf('25', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]:
% 0.62/0.86         ((k2_tarski @ X1 @ X0)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.62/0.86      inference('sup+', [status(thm)], ['21', '24'])).
% 0.62/0.86  thf('26', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.86      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.86  thf('27', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]:
% 0.62/0.86         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.62/0.86           = (k2_tarski @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.86  thf('28', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]:
% 0.62/0.86         ((k2_tarski @ X1 @ X0)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.62/0.86      inference('sup+', [status(thm)], ['21', '24'])).
% 0.62/0.86  thf('29', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['27', '28'])).
% 0.62/0.86  thf('30', plain,
% 0.62/0.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k2_tarski @ X9 @ X10)))),
% 0.62/0.86      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.62/0.86  thf('31', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X2 @ X0 @ X1)
% 0.62/0.86           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.62/0.86      inference('sup+', [status(thm)], ['29', '30'])).
% 0.62/0.86  thf('32', plain,
% 0.62/0.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X11 @ X12 @ X13)
% 0.62/0.86           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 0.62/0.86      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.62/0.86  thf('33', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.86      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.86  thf('34', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 0.62/0.86           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.62/0.86      inference('sup+', [status(thm)], ['32', '33'])).
% 0.62/0.86  thf('35', plain,
% 0.62/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.86         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.62/0.86      inference('sup+', [status(thm)], ['31', '34'])).
% 0.62/0.86  thf('36', plain,
% 0.62/0.86      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.62/0.86         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.62/0.86      inference('demod', [status(thm)], ['9', '18', '35'])).
% 0.62/0.86  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.62/0.86  
% 0.62/0.86  % SZS output end Refutation
% 0.62/0.86  
% 0.62/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
