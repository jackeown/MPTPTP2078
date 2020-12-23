%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.POtaj3GNPw

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:29 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  421 ( 588 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t52_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.POtaj3GNPw
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.55/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.72  % Solved by: fo/fo7.sh
% 0.55/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.72  % done 244 iterations in 0.231s
% 0.55/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.72  % SZS output start Refutation
% 0.55/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.72  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.72  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.55/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.72  thf(t71_enumset1, conjecture,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.55/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.72        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.55/0.72    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.55/0.72  thf('0', plain,
% 0.55/0.72      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.55/0.72         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(t70_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.72  thf('1', plain,
% 0.55/0.72      (![X34 : $i, X35 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.55/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.72  thf(t69_enumset1, axiom,
% 0.55/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.55/0.72  thf('2', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf(t42_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.55/0.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.55/0.72  thf('3', plain,
% 0.55/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k2_tarski @ X9 @ X10)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.55/0.72  thf('4', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['2', '3'])).
% 0.55/0.72  thf('5', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((k2_tarski @ X0 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['1', '4'])).
% 0.55/0.72  thf('6', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf('7', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((k1_tarski @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.55/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.55/0.72  thf('8', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['2', '3'])).
% 0.55/0.72  thf(l62_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.72     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.55/0.72       ( k2_xboole_0 @
% 0.55/0.72         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.55/0.72  thf('9', plain,
% 0.55/0.72      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.55/0.72         ((k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.55/0.72           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.55/0.72              (k1_enumset1 @ X5 @ X6 @ X7)))),
% 0.55/0.72      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.55/0.72  thf('10', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.72         ((k4_enumset1 @ X1 @ X0 @ X0 @ X4 @ X3 @ X2)
% 0.55/0.72           = (k2_xboole_0 @ 
% 0.55/0.72              (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 0.55/0.72              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.72  thf('11', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.72         ((k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['7', '10'])).
% 0.55/0.72  thf(t44_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.72     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.55/0.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.55/0.72  thf('12', plain,
% 0.55/0.72      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.55/0.72  thf('13', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.72         ((k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.55/0.72           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.55/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.72  thf('14', plain,
% 0.55/0.72      (![X34 : $i, X35 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.55/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.72  thf('15', plain,
% 0.55/0.72      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.55/0.72  thf('16', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.72  thf('17', plain,
% 0.55/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k2_tarski @ X9 @ X10)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.55/0.72  thf('18', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.55/0.72      inference('demod', [status(thm)], ['16', '17'])).
% 0.55/0.72  thf('19', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X1 @ X0)
% 0.55/0.72           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.55/0.72      inference('sup+', [status(thm)], ['13', '18'])).
% 0.55/0.72  thf('20', plain,
% 0.55/0.72      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf(t52_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.72     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.55/0.72       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ))).
% 0.55/0.72  thf('21', plain,
% 0.55/0.72      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.55/0.72         ((k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.55/0.72           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ 
% 0.55/0.72              (k2_enumset1 @ X22 @ X23 @ X24 @ X25)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t52_enumset1])).
% 0.55/0.72  thf('22', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.72         ((k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.55/0.72              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['20', '21'])).
% 0.55/0.72  thf('23', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.55/0.72              (k2_enumset1 @ X2 @ X1 @ X1 @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['19', '22'])).
% 0.55/0.72  thf('24', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.55/0.72      inference('demod', [status(thm)], ['16', '17'])).
% 0.55/0.72  thf('25', plain,
% 0.55/0.72      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.55/0.72  thf('26', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.55/0.72              (k2_enumset1 @ X2 @ X1 @ X1 @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['24', '25'])).
% 0.55/0.72  thf('27', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.55/0.72      inference('demod', [status(thm)], ['23', '26'])).
% 0.55/0.72  thf('28', plain,
% 0.55/0.72      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.55/0.72         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.55/0.72      inference('demod', [status(thm)], ['0', '27'])).
% 0.55/0.72  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.55/0.72  
% 0.55/0.72  % SZS output end Refutation
% 0.55/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
