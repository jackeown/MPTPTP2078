%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wa5QTLJAVt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 103 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  476 ( 991 expanded)
%              Number of equality atoms :   43 (  93 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X53: $i] :
      ( ( k2_tarski @ X53 @ X53 )
      = ( k1_tarski @ X53 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X54 @ X55 )
      = ( k2_tarski @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X53: $i] :
      ( ( k2_tarski @ X53 @ X53 )
      = ( k1_tarski @ X53 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X54 @ X55 )
      = ( k2_tarski @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X54 @ X55 )
      = ( k2_tarski @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X53: $i] :
      ( ( k2_tarski @ X53 @ X53 )
      = ( k1_tarski @ X53 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X53: $i] :
      ( ( k2_tarski @ X53 @ X53 )
      = ( k1_tarski @ X53 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('34',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','32','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wa5QTLJAVt
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 175 iterations in 0.137s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.59  thf(t71_enumset1, conjecture,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.59        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.21/0.59         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t69_enumset1, axiom,
% 0.21/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.59  thf('1', plain, (![X53 : $i]: ((k2_tarski @ X53 @ X53) = (k1_tarski @ X53))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf(t70_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      (![X54 : $i, X55 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X54 @ X54 @ X55) = (k2_tarski @ X54 @ X55))),
% 0.21/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.59  thf(t44_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.59  thf('6', plain, (![X53 : $i]: ((k2_tarski @ X53 @ X53) = (k1_tarski @ X53))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf(t43_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.59       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.21/0.59           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X54 : $i, X55 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X54 @ X54 @ X55) = (k2_tarski @ X54 @ X55))),
% 0.21/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k2_tarski @ X0 @ X1)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.21/0.59              (k2_enumset1 @ X1 @ X0 @ X0 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.59  thf(t47_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.59     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.21/0.59  thf('14', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.59         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X15) @ 
% 0.21/0.59              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.21/0.59           = (k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      (![X54 : $i, X55 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X54 @ X54 @ X55) = (k2_tarski @ X54 @ X55))),
% 0.21/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.59  thf(t48_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.59     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.59       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.59         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.21/0.59           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ 
% 0.21/0.59              (k1_enumset1 @ X22 @ X23 @ X24)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.59         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.21/0.59           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.21/0.59           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['15', '18'])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      (![X53 : $i]: ((k2_tarski @ X53 @ X53) = (k1_tarski @ X53))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.21/0.59           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.59  thf('22', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.21/0.59              (k2_enumset1 @ X2 @ X1 @ X1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.59         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X15) @ 
% 0.21/0.59              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.59           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.59  thf('27', plain,
% 0.21/0.59      (![X53 : $i]: ((k2_tarski @ X53 @ X53) = (k1_tarski @ X53))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf('28', plain,
% 0.21/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.59         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.21/0.59           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ 
% 0.21/0.59              (k1_enumset1 @ X22 @ X23 @ X24)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.21/0.59  thf('29', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.59         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.59  thf('30', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.59         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.21/0.59           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.21/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['26', '31'])).
% 0.21/0.59  thf('33', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.21/0.59         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.59      inference('demod', [status(thm)], ['0', '32', '33'])).
% 0.21/0.59  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
