%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WoWCBvIbjh

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  365 ( 408 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t90_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t90_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X20 @ X20 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf(t53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X3 @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X3 @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WoWCBvIbjh
% 0.15/0.36  % Computer   : n003.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:35:27 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 12 iterations in 0.017s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.49  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.23/0.49                                           $i > $i).
% 0.23/0.49  thf(t90_enumset1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D ) =
% 0.23/0.49       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ B @ C @ D ) =
% 0.23/0.49          ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t90_enumset1])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.49         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t84_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X20 @ X20 @ X20 @ X20 @ X21 @ X22)
% 0.23/0.49           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.23/0.49      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.23/0.49  thf(t79_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.23/0.49       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.23/0.49           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.23/0.49      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 0.23/0.49           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.23/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf(l75_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.23/0.49     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.23/0.49       ( k2_xboole_0 @
% 0.23/0.49         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.49         ((k6_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.23/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.23/0.49              (k2_enumset1 @ X6 @ X7 @ X8 @ X9)))),
% 0.23/0.49      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.49         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.23/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.23/0.49              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.23/0.49           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.23/0.49      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.23/0.49  thf(t53_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.49     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.23/0.49       ( k2_xboole_0 @
% 0.23/0.49         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.23/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ 
% 0.23/0.49              (k1_enumset1 @ X13 @ X14 @ X15)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t53_enumset1])).
% 0.23/0.49  thf(t6_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.23/0.49           = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.23/0.49           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.23/0.49              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.23/0.49           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ 
% 0.23/0.49              (k1_enumset1 @ X13 @ X14 @ X15)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t53_enumset1])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.23/0.49           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.49           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X3 @ X3) @ 
% 0.23/0.49           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.49           = (k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['6', '11'])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.49         ((k4_enumset1 @ X16 @ X16 @ X16 @ X17 @ X18 @ X19)
% 0.23/0.49           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 0.23/0.49      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X3 @ X3) @ 
% 0.23/0.49           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.49           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.23/0.49           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['5', '14'])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.49         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.23/0.49      inference('demod', [status(thm)], ['0', '15'])).
% 0.23/0.49  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
