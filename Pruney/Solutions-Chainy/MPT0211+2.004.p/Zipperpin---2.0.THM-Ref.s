%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pgC08tAmvJ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:30 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  318 ( 399 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   10 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ A @ D ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X4 @ X2 @ X3 @ X5 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X4 @ X2 @ X3 @ X5 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X4 @ X2 @ X3 @ X5 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['10','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pgC08tAmvJ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 159 iterations in 0.131s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(t137_enumset1, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.41/0.59       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.59        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.41/0.59          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.41/0.59         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t45_enumset1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.41/0.59       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.41/0.59           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.41/0.59         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf(commutativity_k2_tarski, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.41/0.59           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2)
% 0.41/0.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.41/0.59           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['5', '6'])).
% 0.41/0.59  thf(l123_enumset1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ))).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X4 @ X2 @ X3 @ X5) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 0.41/0.59         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '9'])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.41/0.59           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1)
% 0.41/0.59           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.41/0.59           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X4 @ X2 @ X3 @ X5) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.41/0.59  thf(t71_enumset1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.41/0.59           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['15', '18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.59         ((k2_enumset1 @ X4 @ X2 @ X3 @ X5) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X2 @ X2))),
% 0.41/0.59      inference('sup+', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.41/0.59         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['10', '21'])).
% 0.41/0.59  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
