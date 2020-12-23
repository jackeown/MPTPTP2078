%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R21oj72rwE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:07 EST 2020

% Result     : Theorem 3.38s
% Output     : Refutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  348 ( 516 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X8 @ X6 @ X7 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X12 @ X10 @ X11 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X12 @ X10 @ X11 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R21oj72rwE
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:00:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 3.38/3.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.38/3.56  % Solved by: fo/fo7.sh
% 3.38/3.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.38/3.56  % done 4383 iterations in 3.091s
% 3.38/3.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.38/3.56  % SZS output start Refutation
% 3.38/3.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.38/3.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.38/3.56  thf(sk_B_type, type, sk_B: $i).
% 3.38/3.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.38/3.56  thf(sk_A_type, type, sk_A: $i).
% 3.38/3.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.38/3.56  thf(sk_C_type, type, sk_C: $i).
% 3.38/3.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.38/3.56  thf(sk_D_type, type, sk_D: $i).
% 3.38/3.56  thf(t108_enumset1, conjecture,
% 3.38/3.56    (![A:$i,B:$i,C:$i,D:$i]:
% 3.38/3.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 3.38/3.56  thf(zf_stmt_0, negated_conjecture,
% 3.38/3.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.38/3.56        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 3.38/3.56    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 3.38/3.56  thf('0', plain,
% 3.38/3.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.38/3.56         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 3.38/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.38/3.56  thf(t100_enumset1, axiom,
% 3.38/3.56    (![A:$i,B:$i,C:$i]:
% 3.38/3.56     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 3.38/3.56  thf('1', plain,
% 3.38/3.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.38/3.56         ((k1_enumset1 @ X8 @ X6 @ X7) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 3.38/3.56      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.38/3.56  thf(t46_enumset1, axiom,
% 3.38/3.56    (![A:$i,B:$i,C:$i,D:$i]:
% 3.38/3.56     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.38/3.56       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 3.38/3.56  thf('2', plain,
% 3.38/3.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 3.38/3.56           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ (k1_tarski @ X16)))),
% 3.38/3.56      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.38/3.56  thf('3', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3)
% 3.38/3.56           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.38/3.56      inference('sup+', [status(thm)], ['1', '2'])).
% 3.38/3.56  thf('4', plain,
% 3.38/3.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 3.38/3.56           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ (k1_tarski @ X16)))),
% 3.38/3.56      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.38/3.56  thf('5', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.38/3.56      inference('sup+', [status(thm)], ['3', '4'])).
% 3.38/3.56  thf(t105_enumset1, axiom,
% 3.38/3.56    (![A:$i,B:$i,C:$i,D:$i]:
% 3.38/3.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 3.38/3.56  thf('6', plain,
% 3.38/3.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X9 @ X12 @ X10 @ X11)
% 3.38/3.56           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 3.38/3.56      inference('cnf', [status(esa)], [t105_enumset1])).
% 3.38/3.56  thf('7', plain,
% 3.38/3.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.38/3.56         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 3.38/3.56      inference('demod', [status(thm)], ['0', '5', '6'])).
% 3.38/3.56  thf(commutativity_k2_tarski, axiom,
% 3.38/3.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.38/3.56  thf('8', plain,
% 3.38/3.56      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 3.38/3.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.38/3.56  thf(t70_enumset1, axiom,
% 3.38/3.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.38/3.56  thf('9', plain,
% 3.38/3.56      (![X41 : $i, X42 : $i]:
% 3.38/3.56         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.38/3.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.38/3.56  thf('10', plain,
% 3.38/3.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 3.38/3.56           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ (k1_tarski @ X16)))),
% 3.38/3.56      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.38/3.56  thf('11', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.38/3.56           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.38/3.56      inference('sup+', [status(thm)], ['9', '10'])).
% 3.38/3.56  thf(t71_enumset1, axiom,
% 3.38/3.56    (![A:$i,B:$i,C:$i]:
% 3.38/3.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.38/3.56  thf('12', plain,
% 3.38/3.56      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.38/3.56           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.38/3.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.38/3.56  thf('13', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.38/3.56         ((k1_enumset1 @ X1 @ X0 @ X2)
% 3.38/3.56           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.38/3.56      inference('demod', [status(thm)], ['11', '12'])).
% 3.38/3.56  thf('14', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.38/3.56         ((k1_enumset1 @ X0 @ X1 @ X2)
% 3.38/3.56           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.38/3.56      inference('sup+', [status(thm)], ['8', '13'])).
% 3.38/3.56  thf('15', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.38/3.56         ((k1_enumset1 @ X1 @ X0 @ X2)
% 3.38/3.56           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.38/3.56      inference('demod', [status(thm)], ['11', '12'])).
% 3.38/3.56  thf('16', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.38/3.56         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.38/3.56      inference('sup+', [status(thm)], ['14', '15'])).
% 3.38/3.56  thf('17', plain,
% 3.38/3.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 3.38/3.56           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ (k1_tarski @ X16)))),
% 3.38/3.56      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.38/3.56  thf('18', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 3.38/3.56           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.38/3.56      inference('sup+', [status(thm)], ['16', '17'])).
% 3.38/3.56  thf('19', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3)
% 3.38/3.56           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.38/3.56      inference('sup+', [status(thm)], ['1', '2'])).
% 3.38/3.56  thf('20', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.38/3.56      inference('sup+', [status(thm)], ['18', '19'])).
% 3.38/3.56  thf('21', plain,
% 3.38/3.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X9 @ X12 @ X10 @ X11)
% 3.38/3.56           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 3.38/3.56      inference('cnf', [status(esa)], [t105_enumset1])).
% 3.38/3.56  thf('22', plain,
% 3.38/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.38/3.56         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 3.38/3.56      inference('sup+', [status(thm)], ['20', '21'])).
% 3.38/3.56  thf('23', plain,
% 3.38/3.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.38/3.56         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 3.38/3.56      inference('demod', [status(thm)], ['7', '22'])).
% 3.38/3.56  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 3.38/3.56  
% 3.38/3.56  % SZS output end Refutation
% 3.38/3.56  
% 3.38/3.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
