%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6KhSx4mgdb

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  421 ( 478 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(t66_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_enumset1 @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
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

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t64_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k6_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6KhSx4mgdb
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 69 iterations in 0.071s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.52                                           $i > $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.52  thf(t66_enumset1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.52        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.52          ( k2_xboole_0 @
% 0.21/0.52            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t66_enumset1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.52         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52             (k1_enumset1 @ sk_F @ sk_G @ sk_H)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t41_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k2_tarski @ A @ B ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((k2_tarski @ X12 @ X13)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((k2_tarski @ X12 @ X13)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.52  thf(t4_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.52       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.52  thf(t43_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.21/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.21/0.52              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.52  thf(l57_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.21/0.52              (k2_tarski @ X10 @ X11)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.21/0.52              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.21/0.52              (k2_tarski @ X10 @ X11)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.21/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.21/0.52              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X5)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.21/0.52           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.21/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.52              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.52  thf(t64_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 0.21/0.52         X43 : $i]:
% 0.21/0.52         ((k6_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.21/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ 
% 0.21/0.52              (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t64_enumset1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.21/0.52           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.21/0.52           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.52         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.21/0.52             sk_H))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.52  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
