%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpWSzKMTK8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  365 ( 494 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_enumset1 @ X49 @ X49 @ X50 )
      = ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_enumset1 @ X49 @ X49 @ X50 )
      = ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpWSzKMTK8
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 112 iterations in 0.087s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(t71_enumset1, conjecture,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.55        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.22/0.55         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t70_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X49 : $i, X50 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X49 @ X49 @ X50) = (k2_tarski @ X49 @ X50))),
% 0.22/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.55  thf(t48_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.55     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.22/0.55       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.55         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.22/0.55           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ 
% 0.22/0.55              (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.22/0.55           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf(t69_enumset1, axiom,
% 0.22/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.55  thf('4', plain, (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 0.22/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.55  thf(t43_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.22/0.55       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.22/0.55           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.22/0.55           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X2 @ X1 @ X0) = (k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X49 : $i, X50 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X49 @ X49 @ X50) = (k2_tarski @ X49 @ X50))),
% 0.22/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.55  thf(l62_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.55     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.55       ( k2_xboole_0 @
% 0.22/0.55         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.55         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.22/0.55           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 0.22/0.55              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.22/0.55      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.55         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.22/0.55           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.22/0.55              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.55         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.22/0.55           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ 
% 0.22/0.55              (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.55         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.22/0.55           = (k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.22/0.55           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['7', '12'])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X2 @ X1 @ X0) = (k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.55  thf(t51_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.55     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.55         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.22/0.55           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.22/0.55              (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.22/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf(t44_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.55         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.22/0.55           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.22/0.55           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['13', '18'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.22/0.55         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['0', '19'])).
% 0.22/0.55  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
